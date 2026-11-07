import JuliaLean.Core
import JuliaLean.base.expr


section

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

end JuliaLean.DocsSyntaxCov

end


/-!
# Model of `base/docs/core.jl`

CoreDocs expression values use the source-mirrored `Value` type. Its mutable documentation list is
passed explicitly, so each method returns the updated head while preserving the Julia call order.
-/

namespace JuliaLean.base.docs.core

open JuliaLean JuliaLean.base.expr

abbrev JInt64 := JInt .i64

/-- The source location carried by Julia's `LineNumberNode`. -/
structure DocSource (L : Type) where
  file : Value L
  line : JInt64

/--
Julia source: base/docs/core.jl:7-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DocLinkedList
    doc::SimpleVector
    next::DocLinkedList
```
-/
structure DocLinkedList (L : Type) where
  doc : Option (List (Value L))
  next : Option (DocLinkedList L)

/--
Julia source: base/docs/core.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    DocLinkedList() = new()
```
-/
def docLinkedListEmpty {L : Type} : DocLinkedList L := ⟨none, none⟩

/--
Julia source: base/docs/core.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    DocLinkedList(doc::SimpleVector, next::DocLinkedList) = new(doc, next)
```
-/
def docLinkedListCons {L : Type} (doc : List (Value L)) (next : DocLinkedList L) : DocLinkedList L :=
  ⟨some doc, some next⟩

/--
Julia source: base/docs/core.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
global DOCS = DocLinkedList()
```
-/
def initialDocs {L : Type} : DocLinkedList L := docLinkedListEmpty

/--
Julia source: base/docs/core.jl:15-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function doc!(source::LineNumberNode, mod::Module, str, ex)
    global DOCS
    DOCS = DocLinkedList(Core.svec(mod, ex, str, source.file, source.line), DOCS)
    nothing
end
```
-/
def doc! {L : Type} (ops : LeafOps L) (docs : DocLinkedList L) (source : DocSource L)
    (mod : L) (str ex : Value L) : DocLinkedList L × Unit :=
  (docLinkedListCons [.leaf mod, ex, str, source.file, .leaf (ops.ofInt source.line)] docs, ())

/--
Julia source: base/docs/core.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isexpr(x, h::Symbol) = isa(x, Expr) && x.head === h
```
-/
def isexpr {L : Type} (x : Value L) (h : String) : Bool :=
  match x with
  | .expr head _ => head == h
  | _ => false

/-- `Core.svec` as the function expression used in lazily interpolated documentation strings. -/
def coreSvec {L : Type} (coreModule : L) : Value L := .globalRef coreModule "svec"

/--
Julia source: base/docs/core.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lazy_iterpolate(s::AbstractString) = Expr(:call, Core.svec, s)
```
-/
def lazyIterpolateString {L : Type} (coreModule : L) (s : Value L) : Value L :=
  .expr "call" [coreSvec coreModule, s]

/--
Julia source: base/docs/core.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lazy_iterpolate(x) = isexpr(x, :string) ? Expr(:call, Core.svec, x.args...) : x
```
-/
def lazyIterpolate {L : Type} (coreModule : L) (x : Value L) : Value L :=
  match x with
  | .expr "string" args => .expr "call" (coreSvec coreModule :: args)
  | _ => x

/--
Julia source: base/docs/core.jl:26-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function docm(source::LineNumberNode, mod::Module, str, x)
    out = Expr(:call, doc!, QuoteNode(source), mod, lazy_iterpolate(str), QuoteNode(x))
    if isexpr(x, :module)
        out = Expr(:toplevel, out, x)
    elseif isexpr(x, :call)
    else
        out = Expr(:block, x, out)
    end
    return Expr(:escape, out)
end
```
-/
def docm {L : Type} (coreModule docsModule : L) (source : DocSource L) (mod : L)
    (str x : Value L) : Value L :=
  let call := .expr "call" [
    .globalRef docsModule "doc!",
    .quoteNode (.lineNumberNode source.line source.file),
    .leaf mod,
    lazyIterpolate coreModule str,
    .quoteNode x
  ]
  let out :=
    if isexpr x "module" then .expr "toplevel" [call, x]
    else if isexpr x "call" then call
    else .expr "block" [x, call]
  .expr "escape" [out]

/--
Julia source: base/docs/core.jl:36-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
docm(source::LineNumberNode, mod::Module, x) =
    (isa(x, Expr) && x.head === :->) ? docm(source, mod, x.args[1], x.args[2].args[2]) : error("invalid '@doc'.")
```
-/
def docmArrow {L : Type} (coreModule docsModule : L) (source : DocSource L) (mod : L)
    (x : Value L) : ExprResult (Value L) :=
  match x with
  | .expr "->" args => do
      let str ← argAt args 1
      let body ← argAt args 2
      let (_, bodyArgs) ← asExpr body
      let expression ← argAt bodyArgs 2
      pure (docm coreModule docsModule source mod str expression)
  | _ => .error (.errorException "invalid '@doc'.")

end JuliaLean.base.docs.core
