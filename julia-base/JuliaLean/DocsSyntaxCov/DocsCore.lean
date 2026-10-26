import JuliaLean.DocsSyntaxCov.Ast

/-!
# `base/docs/core.jl`, `base/docs/utils.jl`, `base/docs/bindings.jl`, `base/docs/basedocs.jl`

Models of the bootstrap docsystem (`Core.CoreDocs`), the `HTML`/`Text` wrappers,
`Docs.Binding` and the `kw"..."` keyword literal, master `bbfa0ce4150`.
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `base/docs/core.jl` -/

/-- The `Core.svec(mod, ex, str, file, line)` record that `CoreDocs.doc!` stores. -/
structure DocRec where
  mod : String
  ex : JV
  str : JV
  file : String
  line : Int
  deriving Repr

/-- `CoreDocs.DocLinkedList`, `base/docs/core.jl:7-12`: `DocLinkedList()` leaves `doc`
and `next` undefined (`empty`); `DocLinkedList(doc, next)` is a cons cell. -/
inductive DocLinkedList where
  | empty
  | cons (doc : DocRec) (next : DocLinkedList)
  deriving Repr

/-- `DocLinkedList()`, `base/docs/core.jl:10`. -/
def docLinkedList0 : DocLinkedList := .empty

/-- `DocLinkedList(doc, next)`, `base/docs/core.jl:11`. -/
def docLinkedList2 (doc : DocRec) (next : DocLinkedList) : DocLinkedList := .cons doc next

/-- `isdefined(docs, :doc)`. -/
def DocLinkedList.hasDoc : DocLinkedList → Bool
  | .empty => false
  | .cons _ _ => true

/-- `CoreDocs.doc!(source, mod, str, ex)`, `base/docs/core.jl:15-19`: the new global
`DOCS` and the return value `nothing`. `source` is `LineNumberNode(line, file)`. -/
def coreDocBang (docs : DocLinkedList) (line : Int) (file mod : String) (str ex : JV) :
    DocLinkedList × JV :=
  (.cons ⟨mod, ex, str, file, line⟩ docs, .nothing)

/-- `CoreDocs.isexpr(x, h)`, `base/docs/core.jl:21`. -/
def coreIsexpr (x : JV) (h : String) : Bool :=
  match x with
  | .expr h' _ => h' == h
  | _ => false

/-- The function object `Core.svec` inside generated expressions. -/
def svecFn : JV := .val "Core.svec"

/-- `lazy_iterpolate(s::AbstractString)` and `lazy_iterpolate(x)`,
`base/docs/core.jl:23-24`. -/
def lazyIterpolate (x : JV) : JV :=
  match x with
  | .str s => .expr "call" [svecFn, .str s]
  | _ => if coreIsexpr x "string" then .expr "call" (svecFn :: x.args) else x

/-- The function object `CoreDocs.doc!`. -/
def coreDocFn : JV := .val "Core.CoreDocs.doc!"

/-- `CoreDocs.docm(source, mod, str, x)`, `base/docs/core.jl:26-35`. -/
def coreDocm4 (source : JV) (mod : String) (str x : JV) : JV :=
  let out := JV.expr "call" [coreDocFn, .qn source, .val mod, lazyIterpolate str, .qn x]
  let out :=
    if coreIsexpr x "module" then JV.expr "toplevel" [out, x]
    else if coreIsexpr x "call" then out
    else JV.expr "block" [x, out]
  .expr "escape" [out]

/-- `CoreDocs.docm(source, mod, x)`, `base/docs/core.jl:36-37`: `x` must be
`str -> body`, whose lowered form is `Expr(:->, str, Expr(:block, line, body))`. -/
def coreDocm3 (source : JV) (mod : String) (x : JV) : DJ JV :=
  match x with
  | .expr "->" (a :: b :: _) =>
    match b.arg? 2 with
    | some body => pure (coreDocm4 source mod a body)
    | none => .error .boundsError
  | _ => .error (DErr.errorException "invalid '@doc'.")

/-! ## `base/docs/basedocs.jl` -/

/-- `kw"text"`, `base/docs/basedocs.jl:11-13`: `Keyword(Symbol(text))`. -/
def kwStr (text : String) : JV := .keyword text

/-! ## `base/docs/utils.jl` -/

/-- The content of an `HTML{T}` or `Text{T}`: a value printed with `print`, or a
function (`T <: Function`) that writes the given strings to the stream. -/
inductive Content (C : Type) where
  | value (c : C)
  | fn (out : List String)

/-- `HTML(xs...)`, `base/docs/utils.jl:33-39`: an `HTML` whose content function prints
each argument in turn. `printC` is `print` of one argument. -/
def htmlVarargs {C : Type} (printC : C → String) (xs : List C) : Content C :=
  .fn (xs.map printC)

/-- `show(io, MIME"text/html"(), h::HTML)` and `show(io, MIME"text/html"(), h::HTML{<:Function})`,
`base/docs/utils.jl:41-42`: the bytes written. -/
def showHtml {C : Type} (printC : C → String) : Content C → String
  | .value c => printC c
  | .fn out => String.join out

/-- `html"s"`, `base/docs/utils.jl:55-57`: `HTML(s)` of the string literal. -/
def htmlStr (s : String) : Content String := .value s

/-- `catdoc(xs::HTML...)`, `base/docs/utils.jl:59-65`: an `HTML` whose function shows
each part as `text/html`. -/
def catdocHtml {C : Type} (printC : C → String) (xs : List (Content C)) : Content C :=
  .fn (xs.map (showHtml printC))

/-- `print(io, t::Text)` and `print(io, t::Text{<:Function})`, `base/docs/utils.jl:91-92`. -/
def printText {C : Type} (printC : C → String) : Content C → String
  | .value c => printC c
  | .fn out => String.join out

/-- `show(io, t::Text) = print(io, t)`, `base/docs/utils.jl:93`. -/
def showText {C : Type} (printC : C → String) (t : Content C) : String := printText printC t

/-- `text"s"`, `base/docs/utils.jl:109-111`. -/
def textStr (s : String) : Content String := .value s

/-- `catdoc(xs::Text...)`, `base/docs/utils.jl:113-119`: each part is shown as
`text/plain`, which for `Text` falls back to `show(io, x)`. -/
def catdocText {C : Type} (printC : C → String) (xs : List (Content C)) : Content C :=
  .fn (xs.map (showText printC))

/-- Julia's `==`, `isequal` and `hash` of a content type `T` (`hash` on `UInt64`). -/
structure ContentOps (C : Type) where
  eq : C → C → Bool
  isequal : C → C → Bool
  hash : C → Nat → Nat
  /-- `hash(T, h)` of the wrapper type `HTML{T}`/`Text{T}`. -/
  hashType : Nat → Nat

/-- `==(t1::T, t2::T) where {T<:Union{HTML,Text}}`, `base/docs/utils.jl:95`, on value
contents of the same type. -/
def wrapperEq {C : Type} (ops : ContentOps C) (a b : C) : Bool := ops.eq a b

/-- `hash(t::T, h) where {T<:Union{HTML,Text}} = hash(T, hash(t.content, h))`,
`base/docs/utils.jl:96`. -/
def wrapperHash {C : Type} (ops : ContentOps C) (a : C) (h : Nat) : Nat :=
  ops.hashType (ops.hash a h)

/-- `isequal(t1, t2)` for `HTML`/`Text`: no method is defined, so Base's fallback
`isequal(x, y) = x == y` (`base/operators.jl`) applies. -/
def wrapperIsequal {C : Type} (ops : ContentOps C) (a b : C) : Bool := wrapperEq ops a b

/-! ## `base/docs/bindings.jl` -/

/-- The module system as `Binding` sees it. Modules are named by strings. -/
structure ModEnv where
  /-- `nameof(m)`. -/
  nameof : String → String
  /-- `parentmodule(m)`. -/
  parent : String → String
  /-- `isdefinedglobal(m, v)` in the current world. -/
  isdefined : String → String → Bool
  /-- The target of an explicit by-name import binding `(m, v)`, if it is one:
  `partition_restriction(bpart).globalref`. -/
  imported : String → String → Option (String × String)
  /-- `Base.binding_module(m, v)`. -/
  bindingModule : String → String → String
  /-- `getglobal(m, v)`. -/
  value : String → String → JV
  /-- `Base.active_module()`. -/
  active : String

/-- `Docs.Binding`: a module and a variable name. -/
structure Binding where
  mod : String
  var : String
  deriving Repr, DecidableEq

/-- The import-following loop of `Binding(m, v)`, `base/docs/bindings.jl:16-23`. -/
def bindingLoop (env : ModEnv) : Nat → String → String → String × String
  | 0, m, v => (m, v)
  | n + 1, m, v =>
    if env.isdefined m v then
      match env.imported m v with
      | none => (m, v)
      | some (m', v') => if m' == m && v' == v then (m, v) else bindingLoop env n m' v'
    else (m, v)

/-- `Binding(m, v)`, `base/docs/bindings.jl:7-25`; `fuel` bounds the import chain. -/
def mkBinding (env : ModEnv) (fuel : Nat) (m v : String) : Binding :=
  let m := if env.nameof m == v then env.parent m else m
  let (m, v) := bindingLoop env fuel m v
  ⟨env.bindingModule m v, v⟩

/-- The function object `Docs.Binding` inside generated expressions. -/
def bindingFn : JV := .val "Base.Docs.Binding"

/-- `:($Base.@__MODULE__)`: a macro call of `Base.@__MODULE__`. -/
def atModuleExpr : JV :=
  .expr "macrocall" [.expr "." [.val "Base", .qn (.sym "@__MODULE__")], .lnn 0 ""]

/-- `splitexpr(x)` for all four methods, `base/docs/bindings.jl:33-38`. -/
def splitexpr (x : JV) : DJ (JV × JV) :=
  match x with
  | .expr h as =>
    if h == "." then
      match as with
      | a :: b :: _ => pure (a, b)
      | _ => .error .boundsError
    else .error (DErr.errorException "Could not find something to document")
  | .sym s => pure (atModuleExpr, quot (.sym s))
  | .gref m n => pure (.val m, quot (.sym n))
  | _ => .error (DErr.errorException "Could not find something to document")

/-- `bindingexpr(x) = Expr(:call, Binding, splitexpr(x)...)`, `base/docs/bindings.jl:28`. -/
def bindingexpr (x : JV) : DJ JV := do
  let (a, b) ← splitexpr x
  pure (.expr "call" [bindingFn, a, b])

/-- `defined(b)`, `base/docs/bindings.jl:30`. -/
def defined (env : ModEnv) (b : Binding) : Bool := env.isdefined b.mod b.var

/-- `resolve(b)`, `base/docs/bindings.jl:31`. -/
def resolve (env : ModEnv) (b : Binding) : DJ JV :=
  if env.isdefined b.mod b.var then pure (env.value b.mod b.var)
  else .error (.undefVarError b.var)

/-- `show(io, b::Binding)`, `base/docs/bindings.jl:40-53`. `isoperator` is
`Base.isoperator` and `showSym` is `show(io, ::Symbol)`. -/
def showBinding (env : ModEnv) (isoperator : String → Bool) (showSym : String → String)
    (b : Binding) : String :=
  if b.mod == env.active then b.var
  else b.mod ++ "." ++ (if isoperator b.var then showSym b.var else b.var)

/-- What `aliasof` dispatches on: a resolved value's type. -/
inductive ValKind where
  | dataType (parent name : String)
  | function (parent name : String)
  | module (name : String)
  | other

/-- `aliasof(d::DataType, b)`, `aliasof(λ::Function, b)`, `aliasof(m::Module, b)` and
`aliasof(other, b)`, `base/docs/bindings.jl:56-59`. -/
def aliasofVal (env : ModEnv) (fuel : Nat) (k : ValKind) (b : Binding) : Binding :=
  match k with
  | .dataType p n => mkBinding env fuel p n
  | .function p n => mkBinding env fuel p n
  | .module m => mkBinding env fuel m (env.nameof m)
  | .other => b

/-- `aliasof(b::Binding)`, `base/docs/bindings.jl:55`. `kind` classifies `resolve(b)`. -/
def aliasof (env : ModEnv) (fuel : Nat) (kind : JV → ValKind) (b : Binding) : Binding :=
  if defined env b then
    let a := aliasofVal env fuel (kind (env.value b.mod b.var)) b
    if defined env a then a else b
  else b

end JuliaLean.DocsSyntaxCov
