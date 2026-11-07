import JuliaLean.base.docs.core
import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.base.meta
import JuliaLean.base.docs.bindings


section

/-!
# `base/docs/Docs.jl`: the docsystem

Model of `Base.Docs` at master `bbfa0ce4150`. Expressions are `JV` trees; the
function objects and constants that the `@doc` expansions splice in (`doc!`,
`docstr`, `Binding`, `Dict{Symbol,Any}`, ...) are `JV.val` atoms named after
them. Type signatures are expressions too (`Union{Tuple{...}}`), and the subtype
test `sig <: msig` of documentation lookup is a parameter.

`macroexpand(mod, ex)` (`Base.macroexpand`, another file) is a parameter of the
functions that call it. Mutable state (each module's `META` dictionary, the list
`Docs.modules`) is a `DocsState` value threaded through `doc!`.
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-- A `Docs.DocStr`, `base/docs/Docs.jl:164-168`. -/
structure DocStr where
  text : List JV
  object : Option JV
  data : List (String × JV)
  deriving Inhabited

/-- A `Docs.MultiDoc`, `base/docs/Docs.jl:219-226`: signatures in definition order and the
docstring of each signature (an `IdDict`, listed in its iteration order). -/
structure MultiDoc where
  order : List JV
  docs : List (JV × DocStr)
  deriving Inhabited

/-- `MultiDoc()`, `base/docs/Docs.jl:225`. -/
def MultiDoc.new : MultiDoc := ⟨[], []⟩

/-- The docsystem state: `Docs.modules` and each module's `META` dictionary (keyed by
`Binding`), if defined. -/
structure DocsState where
  modules : List String
  metas : List (String × List (Binding × MultiDoc))
  deriving Inhabited

def assocGet {κ α : Type} [BEq κ] (d : List (κ × α)) (k : κ) : Option α := (d.find? (·.1 == k)).map (·.2)

def assocSet {κ α : Type} [BEq κ] (d : List (κ × α)) (k : κ) (v : α) : List (κ × α) :=
  if d.any (·.1 == k) then d.map (fun p => if p.1 == k then (k, v) else p) else d ++ [(k, v)]

/-- `meta(m; autoinit)`, `base/docs/Docs.jl:80-88`: the `META` dictionary, created by
`initmeta` when absent and `autoinit`. -/
def metaDict (st : DocsState) (m : String) (autoinit : Bool := true) :
    DocsState × Option (List (Binding × MultiDoc)) :=
  match assocGet st.metas m with
  | some d => (st, some d)
  | none => if autoinit then (⟨st.modules ++ [m], st.metas ++ [(m, [])]⟩, some []) else (st, none)

/-- `initmeta(m)`, `base/docs/Docs.jl:90-98`: define `META` in `m` (and record `m` in
`Docs.modules`) unless it exists. -/
def initmeta (st : DocsState) (m : String) : DocsState × List (Binding × MultiDoc) :=
  match assocGet st.metas m with
  | some d => (st, d)
  | none => (⟨st.modules ++ [m], st.metas ++ [(m, [])]⟩, [])

/-! ## Signatures, `base/docs/Docs.jl:100-147` -/

def curly (f : String) (as : List JV) : JV := .expr "curly" (.sym f :: as)

/-- `tvar(x::Expr) = x` and `tvar(s::Symbol) = :($s <: Any)`, lines 146-147. -/
def tvar (x : JV) : DJ JV :=
  match x with
  | .expr _ _ => pure x
  | .sym s => pure (.expr "<:" [.sym s, .sym "Any"])
  | _ => .error (.methodError "tvar")

/-- `argtype(expr::Expr)` and `argtype(other)`, lines 133-144. -/
def argtype : JV → DJ JV
  | .expr "::" as => match as.getLast? with
    | some t => pure t
    | none => .error .boundsError
  | .expr "..." (a :: _) => do pure (curly "Vararg" [← argtype a])
  | .expr "meta" [a1, a2] =>
    if a1.isSym && (match a1 with | .sym n => n == "nospecialize" || n == "specialize" | _ => false)
    then argtype a2 else argtype a1
  | .expr _ (a :: _) => argtype a
  | .expr _ [] => .error .boundsError
  | _ => pure (.sym "Any")

/-- The argument loop of `signature!` for a call, lines 105-111: the tuples of the `Union`,
the last one being extended. -/
def sigTuples : List (List JV) → List JV → DJ (List (List JV))
  | ts, [] => pure ts
  | ts, arg :: rest => do
    if arg.isExpr "parameters" then sigTuples ts rest
    else
      let ts := if arg.isExpr "kw" then ts ++ [ts.getLastD []] else ts
      let t ← argtype arg
      sigTuples (ts.dropLast ++ [ts.getLastD [] ++ [t]]) rest

/-- `mapany(tvar, xs)`. -/
def tvars : List JV → DJ (List JV)
  | [] => pure []
  | x :: xs => do pure ((← tvar x) :: (← tvars xs))

/-- `Expr(:where, sig, tv[i])` for `i = length(tv):-1:1`: `tv[1]` outermost. -/
def wrapWhere (sig : JV) (tv : List JV) : JV := tv.reverse.foldl (fun s t => .expr "where" [s, t]) sig

/-- `signature!(tv, expr::Expr)` and `signature!(tv, other)`, lines 100-129. -/
def signatureBang : List JV → JV → DJ JV
  | tv, .expr h as =>
    if h == "macrocall" || h == "call" then do
      let firstArg := if h == "macrocall" then 3 else 2
      let ts ← sigTuples [[]] (as.drop (firstArg - 1))
      let tv ← match as with
        | f :: _ => if f.isExpr "curly" && tv.isEmpty then do pure (tv ++ (← tvars f.args.tail)) else pure tv
        | [] => .error .boundsError
      let ts := ts ++ tv.reverse.map (fun t => [t.arg 1])
      pure (wrapWhere (curly "Union" (ts.map (curly "Tuple"))) tv)
    else match as with
      | a :: rest =>
        if h == "where" then do signatureBang (tv ++ (← tvars rest)) a
        else signatureBang tv a
      | [] => .error .boundsError
  | _, _ => pure (curly "Union" [])

/-- `signature(expr)`, lines 130-131. -/
def signature (x : JV) : DJ JV := signatureBang [] x

/-! ## `DocStr` construction, lines 170-198 -/

/-- The object passed to `docstr`/`_docstr`: a `SimpleVector` of parts, a string, a
`DocStr`, or any other object. -/
inductive DocObj where
  | svec (parts : List JV)
  | str (s : String)
  | docstr (d : DocStr)
  | other (v : JV)

/-- `merge(data, doc.data)`: entries of the second dictionary win. -/
def mergeData (a b : List (String × JV)) : List (String × JV) :=
  b.foldl (fun acc (k, v) => assocSet acc k v) a

/-- `_docstr` for all four methods and `docstr(object, data)`, lines 184-190. -/
def docstrObj (o : DocObj) (data : List (String × JV)) : DocStr :=
  match o with
  | .svec parts => ⟨parts, none, data⟩
  | .str s => ⟨[.str s], none, data⟩
  | .other v => ⟨[], some v, data⟩
  | .docstr d => { d with data := mergeData data d.data }

/-- `docstr(binding, typesig)`, lines 170-183: the docstring of `binding` for exactly
`typesig` in the first module that has one. -/
def docstrLookup (st : DocsState) (b : Binding) (typesig : JV) : DJ DocStr :=
  let found := st.modules.findSome? fun m =>
    match (metaDict st m false).2 with
    | none => none
    | some dict => match assocGet dict b with
      | none => none
      | some md => assocGet md.docs typesig
  match found with
  | some d => pure d
  | none => .error (.errorException "could not find matching docstring")

def docstrFn : JV := .val "Base.Docs.docstr"

/-- `docexpr(__source__, __module__, args...) = Expr(:call, docstr, args...)`, line 198. -/
def docexpr (args : List JV) : JV := call docstrFn args

/-! ## Names, lines 297-338 -/

/-- `macroname(s::Symbol)` and `macroname(x::Expr)`, lines 333-334. -/
def macroname : JV → DJ JV
  | .sym s => pure (.sym ("@" ++ s))
  | .expr h as => match as.head?, as.getLast? with
    | some a1, some (.qn (.sym s)) => pure (.expr h [a1, .sym ("@" ++ s)])
    | _, _ => .error (.methodError "macroname")
  | _ => .error (.methodError "macroname")

/-- The argument index `astname` descends into, lines 312-324 (`none`: return `x`). -/
def astnameIndex (x : JV) : Option Nat :=
  if x.isExpr "module" then some (if (x.arg 1).isBool then 2 else 3)
  else if x.isExpr "struct" then some 2
  else if x.isExprIn ["call", "macrocall", "function", "=", "macro", "where", "curly", "::", "<:", ">:",
      "local", "global", "const", "atomic", "copyast", "quote", "inert", "primitive", "abstract",
      "escape", "hygienic-scope"] then some 1
  else none

/-- `astname(x::Expr, ismacro)`, `astname(q::QuoteNode, ...)`, `astname(s::Symbol, ...)` and
`astname(other, ...)`, lines 299-331. Each recursive call descends into a strict
sub-expression; `fuel` (at least the size of `x`) bounds the descent. -/
def astnameF (ismacro : Bool) : Nat → JV → DJ JV
  | 0, x => pure x
  | n + 1, .expr h as =>
    if h == "." then if ismacro then macroname (.expr h as) else pure (.expr h as)
    else if h == "call" && (match as with | a :: _ => a.isExpr "::" | [] => false) then
      match (as.headD .nothing).args.getLast? with
      | some y => astnameF ismacro n y
      | none => .error .boundsError
    else if h == "overlay" then
      match as.getLast? with
      | some y => astnameF ismacro n y
      | none => .error .boundsError
    else
      match astnameIndex (.expr h as) with
      | none => pure (.expr h as)
      | some k => if as.length < k then pure (.expr h as) else astnameF ismacro n (as.getD (k - 1) .nothing)
  | n + 1, .qn v => astnameF ismacro n v
  | _ + 1, .sym s => if ismacro then macroname (.sym s) else pure (.sym s)
  | _ + 1, other => pure other

def astname (ismacro : Bool) (x : JV) : DJ JV := astnameF ismacro (x.size + 1) x

/-- `namify(x) = astname(x, isexpr(x, :macro))`, line 297. -/
def namify (x : JV) : DJ JV := astname (x.isExpr "macro") x

/-- `isfield(x)`, lines 336-338. -/
def isfield : JV → Bool
  | .expr "." (a :: b :: _) => (a.isSym || isfield a) && (b.isQn || b.isExpr "quote")
  | _ => false

/-! ## `metadata`, lines 355-392 -/

/-- The name a field declaration declares, for the forms `metadata` recognises (a `Symbol` or
`x::T`). -/
def fieldDeclName : JV → Option String
  | .sym s => some s
  | .expr "::" (.sym s :: _) => some s
  | _ => none

/-- A statement `metadata` takes for a docstring, line 382-383. -/
def isDocForm (x : JV) : Bool :=
  x.isStr || x.isExpr "string" || x.isExpr "call" ||
    (x.isExpr "macrocall" && (match x.args with | .sym "@doc_str" :: _ => true | _ => false))

/-- The field-docstring loop of `metadata`, lines 371-387: `(field name, docstring)` pairs. -/
def fieldDocs : Option JV → List JV → DJ (List (String × JV))
  | _, [] => pure []
  | last, each :: rest =>
    let eachex := unescape each
    if eachex.isSym || eachex.isExpr "::" then
      match last with
      | some d => do
        let n ← namify eachex
        match n with
        | .sym name => do pure ((name, d) :: (← fieldDocs none rest))
        | _ => .error .typeError
      | none => fieldDocs none rest
    else if eachex.isExpr "function" || eachex.isExpr "=" then pure []
    else if isDocForm eachex then fieldDocs (some each) rest
    else fieldDocs last rest

/-- What `metadata(__source__, __module__, expr, ismodule)` builds (the arguments of the
`Dict{Symbol,Any}(...)` expression): `path` (the source file if it is a `Symbol`, else `""`),
`linenumber`, `module` (the module expression for a module docstring) and, for a `struct`,
`fields`. -/
structure Metadata where
  path : String
  linenumber : Int
  module : JV
  moduleIsExpr : Bool
  fields : Option (List (String × JV))

/-- `metadata(__source__, __module__, expr, ismodule)`. `file` is `none` when `__source__.file`
is not a `Symbol`. -/
def metadata (file : Option String) (line : Int) (mod : String) (expr : JV) (ismodule : Bool) :
    DJ Metadata := do
  let path := file.getD ""
  let fields ← if expr.isExpr "struct" then
      match expr.arg? 3 with
      | some (.expr _ body) => do pure (some (← fieldDocs none body))
      | _ => .error .typeError
    else pure none
  pure ⟨path, line, if ismodule then expr else .val mod, ismodule, fields⟩

def dictFn : JV := .val "Dict{Symbol,Any}"

/-- The `Dict{Symbol,Any}(...)` expression `metadata` returns. -/
def Metadata.toExpr (m : Metadata) : JV :=
  call dictFn ([.expr "Pair" [.sym "path", .str m.path], .expr "Pair" [.sym "linenumber", .int m.linenumber],
      .expr "Pair" [.sym "module", m.module]] ++
    (match m.fields with
      | none => []
      | some fs => [.expr "Pair" [.sym "fields", call dictFn (fs.map fun (f, d) => .expr "Pair" [quot (.sym f), d])]]))

/-! ## `@doc` expression builders, lines 394-483 -/

def docFn : JV := .val "Base.Docs.doc!"
def keywordsDict : JV := .val "Base.Docs.keywords"

/-- Where a docstring is attached: the source file (if a `Symbol`), line and module. -/
structure Src where
  file : Option String
  line : Int
  mod : String

/-- `keyworddoc(__source__, __module__, str, def::Keyword)`, lines 394-398. -/
def keyworddoc (src : Src) (str : JV) (name : String) : DJ JV := do
  let md ← metadata src.file src.line src.mod (.keyword name) false
  let ds := esc (docexpr [lazyIterpolate str, md.toExpr])
  pure (.expr "block" [call (.val "setindex!") [keywordsDict, ds, esc (quot (.sym name))], .nothing])

/-- `objectdoc(__source__, __module__, str, def, expr, sig)`, lines 400-426. -/
def objectdoc (src : Src) (str def_ expr : JV) (sig : JV := curly "Union" []) : DJ JV := do
  let b ← bindingexpr (← namify expr)
  let binding := esc b
  let md ← metadata src.file src.line src.mod expr false
  let ds := esc (docexpr [lazyIterpolate str, md.toExpr])
  let docex := call docFn [.val src.mod, binding, ds, esc sig]
  match def_ with
  | .nothing => pure (.expr "block" [docex])
  | _ =>
    let exdef := esc def_
    if def_.isExprN "global" 1 && (match def_.arg 1 with | .sym _ | .gref _ _ => true | _ => false) then
      pure (.expr "block" [exdef, docex, .expr "if" [.bool true, .nothing]])
    else
      let exdef := if def_.isExprN "=" 2 && (def_.arg 1).isExpr "curly" then JV.expr "block" [exdef] else exdef
      let exdef := JV.expr "if" [.bool true, .expr "=" [.sym "val", exdef]]
      pure (.expr "block" [exdef, docex, .expr "if" [.bool true, .sym "val"]])

/-- `callargs(ex)`, lines 437-438. -/
def callargs : JV → DJ (List JV)
  | .expr "where" (a :: _) => callargs a
  | .expr "call" (_ :: as) => pure as
  | _ => .error (.errorException "Invalid expression to callargs")

/-- `validcall(x)`, line 439. -/
def validcall (x : JV) : Bool := x.isSym || x.isExprIn ["::", "...", "kw", "parameters"]

/-- `docerror(ex)`, lines 792-801: an expression calling `error` with the message. -/
def docerror (ex : JV) : JV :=
  let note := if ex.isExpr "macrocall" then " not documentable. See 'Base.@__doc__' docs for details." else ""
  call (.val "error") [.expr "string" [.str "cannot document the following expression:", ex, .str note], .str "\n"]

/-- `calldoc(__source__, __module__, str, def::Expr)`, lines 428-436. -/
def calldoc (src : Src) (str def_ : JV) : DJ JV := do
  let as ← callargs def_
  if as.isEmpty || as.all validcall then objectdoc src str .nothing def_ (← signature def_)
  else pure (docerror def_)

/-- `moduledoc(__source__, __module__, meta, def, def′::Expr)`, lines 441-458. -/
def moduledoc (src : Src) (meta_ def_ def' : JV) : DJ JV := do
  let name ← namify def'
  let b ← bindingexpr name
  let md ← metadata src.file src.line src.mod name true
  let docex := call docFn [name, b, docexpr [lazyIterpolate meta_, md.toExpr]]
  match def_ with
  | .nothing => pure (esc (call (.val "Core.eval") [name, quot docex]))
  | _ =>
    let hasVersion := !(def_.arg 1).isBool
    let d := unblock def_
    let iBlock := 3 + (if hasVersion then 1 else 0)
    let iBare := 1 + (if hasVersion then 1 else 0)
    match d, d.arg? iBlock with
    | .expr h as, some (.expr bh body) =>
      let body := if d.arg iBare == .bool false then
          .expr "import" [.expr ":" [.expr "." [.sym "Base"], .expr "." [.sym "@doc"]]] :: body else body
      let body := body ++ [docex]
      let as := as.set (iBlock - 1) (.expr bh body)
      pure (esc (.expr "toplevel" [.expr h as]))
    | _, _ => .error .boundsError

/-! ## `@__doc__`, lines 549-601 -/

/-- `replace_meta_doc(each)`, lines 553-556: the `@__doc__` marker becomes an `@doc` call. -/
def replaceMetaDoc (source : JV) (mod : String) (meta_ : JV) (define : Bool) (each : JV) : JV :=
  .expr "macrocall" [.sym "@doc", source, .val mod, .nothing, meta_, each.lastArg, .bool define]

/-- Whether `def` is the expansion of an `@__doc__` marker, line 584. -/
def isMetaDocBlock (d : JV) : Bool :=
  d.isExprN "block" 2 && (d.arg 1).isExprN "meta" 1 && ((d.arg 1).arg 1 == .sym "doc")

/-- `finddoc(λ, mod, def; expand_toplevel)` for both methods, lines 583-601: whether a marker
was found, the updated `def` (`λ` replaces each marker) and the markers found in order.
`macroexpand` (`mx`) may grow the tree, so `fuel` bounds the walk. -/
def finddoc (mx : String → JV → JV) (mod : String) (lam : JV → JV) (expandToplevel : Bool) :
    Nat → JV → Bool × JV × List JV
  | 0, x => (false, x, [])
  | n + 1, .expr h as =>
    if isMetaDocBlock (.expr h as) then (true, lam (.expr h as), [.expr h as])
    else
      let as := if expandToplevel && h == "toplevel" then as.map (mx mod) else as
      let rs := as.map (finddoc mx mod lam expandToplevel n)
      (rs.any (·.1), .expr h (rs.map (·.2.1)), rs.flatMap (·.2.2))
  | _ + 1, other => (false, other, [])

/-- `__doc__!(source, mod, meta, def, define)`, lines 549-580: whether a marker was found
and the rewritten `def`. With `define`, the markers become `@doc` calls (first without
expanding `:toplevel` blocks, then with); without, `def` becomes a `:toplevel` of just the
documented sub-expressions. -/
def docBang (mx : String → JV → JV) (fuel : Nat) (source : JV) (mod : String) (meta_ def_ : JV)
    (define : Bool) : Bool × JV :=
  if define then
    let lam := replaceMetaDoc source mod meta_ define
    let (found, d, _) := finddoc mx mod lam false fuel def_
    if found then (true, d) else
      let (found, d, _) := finddoc mx mod lam true fuel def_
      (found, d)
  else
    let (found, d, marks) := finddoc mx mod id true fuel def_
    if found then
      (true, .expr "toplevel" (marks.map fun each =>
        .expr "macrocall" [.sym "@doc", .lnn 570 "Docs.jl", source, .val mod, meta_, each.lastArg,
          .bool define]))
    else (false, d)

/-! ## Registration and lookup, lines 236-284, 616-642, 864-893 -/

/-- `doc!(__module__, b, str, sig)`, lines 236-262: the new state, whether the "Replacing
docs" warning is printed, and the return value `b`. `resolvedModule` is `resolve(b)` when it
is a module (and `b` is defined). -/
def docRegister (st : DocsState) (active mod : String) (resolvedModule : Option String) (b : Binding)
    (str : DocStr) (sig : JV) : DocsState × Bool × Binding :=
  let mod := resolvedModule.getD mod
  let (st, dict) := initmeta st mod
  let m := (assocGet dict b).getD MultiDoc.new
  let replacing := (assocGet m.docs sig).isSome
  let warn := replacing && mod != active
  let order := if replacing then m.order else m.order ++ [sig]
  let str := { str with data := assocSet (assocSet str.data "binding" (.val (b.mod ++ "." ++ b.var))) "typesig" sig }
  let m := ⟨order, assocSet m.docs sig str⟩
  let dict := assocSet dict b m
  (⟨st.modules, assocSet st.metas mod dict⟩, warn, b)

/-- `getdoc(x, sig) = getdoc(x)` and `getdoc(x) = nothing`, lines 283-284, extended by user
methods (`user`). -/
def getdoc (user : JV → Option DocStr) (x : JV) (_sig : Option JV := none) : Option DocStr := user x

/-- `catdoc()` and `catdoc(xs...) = vcat(xs...)`, lines 292-293, on vectors. -/
def catdoc {α : Type} : List (List α) → Option (List α)
  | [] => none
  | xs => some xs.flatten

/-- The search of `_doc(binding, sig)` through `Docs.modules`, lines 621-635: the first
signature in definition order with `sig <: msig`, else the first docstring in the `IdDict`'s
iteration order. -/
def docLookupModules (st : DocsState) (subtype : JV → JV → Bool) (b : Binding) (sig : JV) :
    Option DocStr :=
  st.modules.findSome? fun m =>
    match (metaDict st m false).2 with
    | none => none
    | some dict => match assocGet dict b with
      | none => none
      | some md =>
        match md.order.find? (subtype sig) with
        | some msig => assocGet md.docs msig
        | none => md.docs.head?.map (·.2)

/-- `_doc(binding::Binding, sig::Type = Union{})`, lines 616-637. -/
def docBinding (env : ModEnv) (st : DocsState) (user : JV → Option DocStr) (subtype : JV → JV → Bool)
    (b : Binding) (sig : JV := curly "Union" []) : Option DocStr :=
  let dyn := if defined env b then getdoc user (env.value b.mod b.var) (some sig) else none
  match dyn with
  | some r => some r
  | none => docLookupModules st subtype b sig

/-- A value passed to `_doc(object, ...)`, with what `aliasof(object, typeof(object))` and
`unwrap_unionall` need. -/
inductive DocTarget where
  | unionAll (body : DocTarget)
  | dataType (parent name : String)
  | function (parent name : String)
  | module (name : String)
  /-- Another object, with its type. -/
  | other (typeParent typeName : String)

/-- `_doc(obj::UnionAll)`, `_doc(object, sig::Type)` and `_doc(object, sig...)`,
lines 640-642: the `Binding` searched for. -/
def docTargetBinding (env : ModEnv) (fuel : Nat) : DocTarget → Binding
  | .unionAll body => docTargetBinding env fuel body
  | .dataType p n => mkBinding env fuel p n
  | .function p n => mkBinding env fuel p n
  | .module m => mkBinding env fuel m (env.nameof m)
  | .other tp tn => mkBinding env fuel tp tn

/-- `_doc(object, sig...) = _doc(object, Tuple{sig...})`. -/
def tupleSig (sigs : List JV) : JV := curly "Tuple" sigs

def docFnObj : JV := .val "Base.Docs._doc"

/-- `simple_lookup_doc(ex)`, lines 644-667: the lookup expression (or the keyword's docstring). -/
def simpleLookupDoc (isoperator : String → Bool) (keywords : List (String × DocStr)) (ex : JV) :
    DJ (Sum DocStr JV) := do
  let ex := match ex with
    | .expr h _ => if h != "." && isoperator h then JV.sym h else ex
    | _ => ex
  match ex with
  | .sym s => if let some d := assocGet keywords s then return .inl d
  | _ => pure ()
  match ex with
  | .expr _ _ | .sym _ => pure ()
  | _ => return .inr (call docFnObj [call (.val "typeof") [esc ex]])
  let name ← namify ex
  if (match name with | .expr h _ => h != "." | _ => false) then
    return .inr (call docFnObj [call (.val "typeof") [esc ex]])
  let binding := esc (← bindingexpr name)
  if ex.isExpr "call" || ex.isExpr "macrocall" || ex.isExpr "where" then
    return .inr (call docFnObj [binding, esc (← signature ex)])
  else return .inr (call docFnObj [binding])

/-- `iscallexpr(ex)`, lines 686-687. -/
def iscallexpr : JV → Bool
  | .expr "where" (a :: _) => iscallexpr a
  | x => x.isExpr "call"

/-- `isquotedmacrocall(x)`, lines 608-611. -/
def isquotedmacrocall (x : JV) : Bool :=
  x.isExprN "copyast" 1 && (match x.arg 1 with | .qn v => v.isExprN "macrocall" 2 | _ => false)

/-- `isbasicdoc(x)`, line 613. -/
def isbasicdoc (x : JV) : Bool := x.isExpr "." || x.isQn || x.isSym

/-- `is_signature(x)`, line 614. -/
def isSignature (x : JV) : Bool :=
  x.isExpr "call" || (x.isExprN "::" 2 && (x.arg 1).isExpr "call") || x.isExpr "where"

def FUNC_HEADS : List String := ["function", "macro", "="]
def BINDING_HEADS : List String := ["const", "global", "="]

/-- The environment of `@doc` expansion: `macroexpand`. -/
structure DocmEnv where
  macroexpand : String → JV → JV

/-- The index of the only documentable argument of a `:block`, lines 705-716 (`0`: none or
several). -/
def blockDocarg (as : List JV) : Nat :=
  let idx := ((List.range as.length).zip as).filter (fun (_, a) => !a.isLnn)
  match idx with
  | [(i, _)] => i + 1
  | _ => 0

mutual
/-- `docm(source, mod, meta, ex, define)`, lines 689-695. -/
def docm (env : DocmEnv) (src : Src) (source : JV) : Nat → JV → JV → Bool → DJ JV
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | n + 1, meta_, ex, define => docmInner env src source n meta_ (env.macroexpand src.mod ex) define

/-- `_docm(source, mod, meta, x, define)`, lines 697-790. -/
def docmInner (env : DocmEnv) (src : Src) (source : JV) : Nat → JV → JV → Bool → DJ JV
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | n + 1, meta_, x, define => do
    if x.isExpr "hygienic-scope" || x.isExpr "escape" then
      match x with
      | .expr h (a :: rest) => return .expr h ((← docmInner env src source n meta_ a true) :: rest)
      | _ => .error .boundsError
    if x.isExpr "block" then
      let k := blockDocarg x.args
      if k != 0 then
        let a ← docmInner env src source n meta_ (x.arg k) define
        return .expr "block" (x.args.set (k - 1) a)
    let def_ := if define then x else .nothing
    let x := match x with
      | .gref m nm => if m == src.mod then JV.sym nm else x
      | _ => x
    match x with
    | .keyword name => keyworddoc src meta_ name
    | _ =>
    if x.isExprIn FUNC_HEADS && isSignature (x.arg 1) then
      objectdoc src meta_ def_ x (← signature x)
    else if (x.isExpr "function" || x.isExpr "macro") && !(x.arg 1).isExpr "call" then
      objectdoc src meta_ def_ x
    else if iscallexpr x then calldoc src meta_ x
    else if x.isExprIn ["struct", "abstract", "primitive"] then objectdoc src meta_ def_ x
    else if x.isExprIn BINDING_HEADS && !(x.arg 1).isExpr "call" then objectdoc src meta_ def_ x
    else if isquotedmacrocall x then objectdoc src meta_ .nothing x
    else if x.isExpr "module" then moduledoc src meta_ def_ x
    else if x.isExpr "tuple" then multidoc env src source n meta_ x define
    else if x.isExpr "error" then pure (esc x)
    else
      let (found, x') := docBang env.macroexpand (x.size + 1) source src.mod meta_ x define
      if found then pure (esc x')
      else if isbasicdoc x then objectdoc src meta_ .nothing x
      else pure (docerror x)

/-- `multidoc(__source__, __module__, meta, ex, define)`, lines 463-483. -/
def multidoc (env : DocmEnv) (src : Src) (source : JV) : Nat → JV → JV → Bool → DJ JV
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | n + 1, meta_, ex, define => do
    let md ← metadata src.file src.line src.mod ex false
    let str := docexpr [lazyIterpolate meta_, md.toExpr]
    let ref := JV.val "ref"
    let docstrs := ex.args.mapIdx fun i _ =>
      if i == 0 then call (.val "getindex") [call (.val "setindex!") [ref, str]]
      else call (.val "getindex") [ref]
    let outs ← multidocArgs env src source n (docstrs.zip ex.args) define
    pure (.expr "block" outs)

def multidocArgs (env : DocmEnv) (src : Src) (source : JV) : Nat → List (JV × JV) → Bool → DJ (List JV)
  | 0, _, _ => .error (.errorException "out of fuel")
  | _ + 1, [], _ => pure []
  | n + 1, (d, arg) :: rest, define => do
    let o ← docm env src source n d arg define
    pure (o :: (← multidocArgs env src source n rest define))
end

mutual
/-- `docm(source, mod, ex)`, lines 669-679: `@doc ex` with one argument. `replLookup` is
`REPL.lookup_doc` when the REPL is loaded. -/
def docm1 (env : DocmEnv) (src : Src) (source : JV) (isoperator : String → Bool)
    (keywords : List (String × DocStr)) (replLookup : Option (JV → JV)) : Nat → JV → DJ (Sum DocStr JV)
  | 0, _ => .error (.errorException "out of fuel")
  | n + 1, ex =>
    if ex.isExpr "->" && ex.args.length > 1 then docmArgs env src source isoperator keywords replLookup n ex.args
    else match replLookup with
      | some f => pure (.inr (f ex))
      | none => simpleLookupDoc isoperator keywords ex

/-- `docm(source, mod, args...)` for the arguments of a `->`: two arguments document (the
four-argument `docm`), more drop the first two (`docm(source, mod, _, _, x...)`, line 681),
and one is looked up. -/
def docmArgs (env : DocmEnv) (src : Src) (source : JV) (isoperator : String → Bool)
    (keywords : List (String × DocStr)) (replLookup : Option (JV → JV)) : Nat → List JV → DJ (Sum DocStr JV)
  | 0, _ => .error (.errorException "out of fuel")
  | n + 1, [ex] => docm1 env src source isoperator keywords replLookup n ex
  | n + 1, [meta_, x] => do pure (.inr (← docm env src source n meta_ x true))
  | n + 1, _ :: _ :: rest => docmArgs env src source isoperator keywords replLookup n rest
  | _ + 1, [] => .error (.methodError "docm")
end

/-- `CoreDocs.docm`'s records, replayed by `loaddocs(docs)`, lines 808-819: each record, from
the head of `DOCS` (the most recent `doc!`) to the tail, is expanded (a `SimpleVector`
string is the value `Expr(:svec, parts...)`) with `define = false`
and evaluated in its module. The list of `(module, expansion)` in evaluation order. -/
def loaddocs (env : DocmEnv) (fuel : Nat) : DocLinkedList → List (String × DJ JV)
  | .empty => []
  | .cons d next =>
    let data : List (String × JV) := [("path", .str d.file), ("linenumber", .int d.line)]
    let doc := docstrObj (match d.str with
      | .str s => .str s
      | .expr "svec" parts => .svec parts
      | v => .other v) data
    let src : Src := ⟨some d.file, d.line, d.mod⟩
    let docExpr := JV.expr "DocStr" doc.text
    (d.mod, docm env src (.lnn d.line d.file) fuel docExpr d.ex false) :: loaddocs env fuel next

/-- `hasdoc(binding, sig)`, lines 865-875, with `fuel` bounding the alias chain, and
`hasdoc(mod, sym) = hasdoc(Binding(mod, sym))`, line 864. -/
def hasdocB (env : ModEnv) (st : DocsState) (user : JV → Option DocStr) (kind : JV → ValKind)
    (bfuel : Nat) : Nat → Binding → Bool
  | 0, _ => false
  | n + 1, b =>
    if defined env b && (getdoc user (env.value b.mod b.var)).isSome then true
    else if st.modules.any (fun m => match (metaDict st m false).2 with
        | none => false
        | some dict => (assocGet dict b).isSome) then true
    else
      let alias := aliasof env bfuel kind b
      if alias == b then false else hasdocB env st user kind bfuel n alias

def hasdoc (env : ModEnv) (st : DocsState) (user : JV → Option DocStr) (kind : JV → ValKind)
    (fuel : Nat) (mod sym : String) : Bool :=
  hasdocB env st user kind fuel fuel (mkBinding env fuel mod sym)

/-- `undocumented_names(mod; private)`, lines 888-893: `names(mod; all=true)` without a
docstring, not starting with `#`, and public unless `private`. -/
def undocumentedNames (env : ModEnv) (st : DocsState) (user : JV → Option DocStr) (kind : JV → ValKind)
    (fuel : Nat) (mod : String) (names : List String) (ispublic : String → Bool) (private_ : Bool) :
    List String :=
  names.filter fun sym =>
    !hasdoc env st user kind fuel mod sym && !sym.startsWith "#" && (private_ || ispublic sym)

/-- `@ref x`, lines 192-196: `esc(docexpr(__source__, __module__, bindingexpr(namify(x)), signature(x)))`. -/
def refMacro (x : JV) : DJ JV := do
  let b ← bindingexpr (← namify x)
  pure (esc (docexpr [b, ← signature x]))

end JuliaLean.DocsSyntaxCov

end


/-!
# Model of `base/docs/Docs.jl`

Typed model of the module `Base.Docs` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. Each modelled method is a Lean definition whose docstring carries the
method's verbatim source; its body follows the Julia body call by call.

* The docsystem's runtime state is a `World`: the `modules` vector, the `META` global of each
  module that defines one (an `IdDict` from `Binding`s to `MultiDoc`s), and heaps of the mutable
  `MultiDoc` and `DocStr` objects, addressed by index, so that mutation through shared
  references is visible as in Julia. Methods run in a monad `m` with that state and the
  `DocError` exceptions; reading or writing the world beyond these globals (`isdefinedglobal`,
  `getglobal`, `Core.eval`, logging) goes through the callees of `DocsOps`.
* `Binding` (`base/docs/bindings.jl`), Julia types, modules and arbitrary values are type
  parameters with the operations the methods use.
* Expressions are the `Value L` ASTs of the `base/expr.jl` model. The expression builders of the
  `@doc` macro, which produce code containing function objects and escapes, and its macro
  expansion stay visible as untranslated source.
-/

namespace JuliaLean.base.docs.Docs
open JuliaLean
open JuliaLean.base.expr (Value LeafOps isexpr isexpr_n isexpr_heads)

abbrev Sym := String
abbrev JInt64 := JInt .i64

/-- Exceptions thrown by the modelled methods. -/
inductive DocError where
  /-- `error(msg)`: an `ErrorException`. -/
  | errorException (msg : String)
  | boundsError
  | keyError
  /-- A failed type assertion `x::T`. -/
  | typeError
  | methodError (fn : String)
  /-- `FieldError` of reading a field the value's type does not have. -/
  | fieldError (field : String)
  deriving Repr, DecidableEq

abbrev DocResult (α : Type) := Except DocError α

section ast
variable {L : Type}

/-- `args[i]` (1-based) of a `Vector{Any}`. -/
def argAt (args : List (Value L)) (i : Nat) : DocResult (Value L) :=
  if i = 0 then .error .boundsError
  else match args[i - 1]? with
    | some x => .ok x
    | none => .error .boundsError

/-- `args[end]`. -/
def argLast (args : List (Value L)) : DocResult (Value L) :=
  match args.getLast? with
  | some x => .ok x
  | none => .error .boundsError

/-- `x::Expr`. -/
def asExpr : Value L → DocResult (Sym × List (Value L))
  | .expr h a => .ok (h, a)
  | _ => .error .typeError

/-- `x isa Symbol`. -/
def isSymbol : Value L → Bool
  | .symbol _ => true
  | _ => false

/-- `x isa QuoteNode`. -/
def isQuoteNode : Value L → Bool
  | .quoteNode _ => true
  | _ => false

/-- `:(Union{})`. -/
def unionEmptyExpr : Value L := .expr "curly" [.symbol "Union"]

end ast

-- UNTRANSLATED
-- license header, module docstring, `module Docs`, `@nospecialize`, the `Core.@doc` documentation expression, `include("bindings.jl")` (modelled with its own file), imports and exports: no method
-- Source: base/docs/Docs.jl:1-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     Docs
-- 
-- The `Docs` module provides the [`@doc`](@ref) macro which can be used to set and retrieve
-- documentation metadata for Julia objects.
-- 
-- Please see the manual section on [documentation](@ref man-documentation) for more
-- information.
-- """
-- module Docs
-- 
-- @nospecialize # don't specialize on any arguments of the methods declared herein
-- 
-- """
-- # Documentation
-- 
-- Functions, methods and types can be documented by placing a string before the definition:
-- 
--     \"\"\"
--         foo(x)
-- 
--     Return a fooified version of `x`.
--     \"\"\"
--     foo(x) = ...
-- 
-- The `@doc` macro can be used directly to both set and retrieve documentation / metadata.
-- The macro has special parsing so that the documented object may occur on the next line:
-- 
--     @doc "blah"
--     function foo() ...
-- 
-- By default, documentation is written as Markdown, but any object can be used as
-- the first argument.
-- 
-- ## Documenting objects separately from their definitions
-- You can document an object before or after its definition with
-- 
--     @doc "foo" function_to_doc
--     @doc "bar" TypeToDoc
-- 
-- For macros, the syntax is `@doc "macro doc" :(Module.@macro)` or `@doc "macro doc"
-- :(string_macro"")` for string macros. Without the quote `:()` the expansion of the macro
-- will be documented.
-- 
-- ## Retrieving Documentation
-- You can retrieve docs for functions, macros and other objects as follows:
-- 
--     @doc foo
--     @doc @time
--     @doc md""
-- 
-- !!! compat "Julia 1.11"
--     In Julia 1.11 and newer, retrieving documentation with the `@doc` macro requires that
--     the `REPL` stdlib is loaded.
-- 
-- ## Functions & Methods
-- Placing documentation before a method definition (e.g. `function foo() ...` or `foo() = ...`)
-- will cause that specific method to be documented, as opposed to the whole function. Method
-- docs are concatenated together in the order they were defined to provide docs for the
-- function.
-- """
-- :(Core.@doc)
-- 
-- include("bindings.jl")
-- 
-- import .Base.Meta: quot, isexpr, unblock, unescape
-- using .Base: RefValue, mapany
-- import ..CoreDocs: lazy_iterpolate
-- 
-- export doc, hasdoc, undocumented_names
-- 
-- # Basic API / Storage
-- 
-- /Source

/--
Julia source: base/docs/Docs.jl:76-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const modules = Module[]
const META    = gensym(:meta)
const METAType = IdDict{Any,Any}

```
-/
/- A `DocStr` object: `text::Core.SimpleVector`, `object::Any` (`none` is `nothing`) and
`data::Dict{Symbol,Any}` (an association list with unique keys). -/
structure DocStr (X O A : Type) where
  text : List X
  object : Option O
  data : List (Sym × A)

/-- A `MultiDoc` object: `order::Vector{Type}` and `docs::METAType` from signatures to `DocStr`
references, in insertion order. -/
structure MultiDocObj (Ty : Type) where
  order : List Ty
  docs : List (Ty × Nat)

/-- The docsystem's global state. `metas` holds the `META` global of each module that defines one:
an `IdDict` from `Binding`s to `MultiDoc` references. -/
structure World (Mod B Ty X O A : Type) where
  modules : List Mod
  metas : List (Mod × List (B × Nat))
  multidocs : List (MultiDocObj Ty)
  docstrs : List (DocStr X O A)
  /-- `const keywords = Dict{Symbol, DocStr}()`: keyword names and `DocStr` references. -/
  keywords : List (Sym × Nat)

/-- The initial state: no module has documentation. -/
def World.initial {Mod B Ty X O A : Type} : World Mod B Ty X O A := ⟨[], [], [], [], []⟩

/-- Callees of the docsystem over a monad `n`. -/
structure DocsOps (n : Type → Type) (Mod B Ty X O A Obj R S : Type) where
  /-- `===` on modules, on `Binding`s (an immutable struct of a module and a symbol), and on types. -/
  egalMod : Mod → Mod → Bool
  egalB : B → B → Bool
  egalTy : Ty → Ty → Bool
  /-- `<:` on types, `Union{}`, `Tuple{ts...}`. -/
  subtype : Ty → Ty → Bool
  unionEmpty : Ty
  tupleOf : List Ty → Ty
  /-- `Core.eval(m, :(const $META = $val))`: the effects of defining the global outside the
  docsystem state (which `initmeta` records), including its errors. -/
  evalConstMeta : Mod → n Unit
  /-- `defined(b)` and `resolve(b)` (`base/docs/bindings.jl`), `obj isa Module`. -/
  defined : B → n Bool
  resolve : B → n Obj
  asModule : Obj → Option Mod
  /-- `Base.active_module()`. -/
  active_module : n Mod
  /-- `@warn msg` and the string interpolations `"$b"`, `"$sig"`, `"$mod"`. -/
  warn : String → n Unit
  bindingString : B → n String
  tyString : Ty → n String
  modString : Mod → n String
  /-- `getdoc(obj, sig)`: Julia dispatch over every method, which packages extend; the Base
  methods are `getdoc_2`/`getdoc_1` below. -/
  getdoc : Obj → Ty → n (Option R)
  /-- The `Any` values stored in a docstring's `data`: a `Binding` and a type. -/
  ofBinding : B → A
  ofTy : Ty → A
  /-- `Core.svec(str)` of an `AbstractString`. -/
  ofString : S → X
  /-- `first(values(d))` of a nonempty `IdDict`: its iteration order follows the table's
  object-id hashing. -/
  idDictFirst : List (Ty × Nat) → Option Nat
  /-- `aliasof(b::Binding)`, `aliasof(object, typeof(object))`, `Docs.Binding(mod, sym)`
  (`base/docs/bindings.jl`), `Base.unwrap_unionall`. -/
  aliasof : B → n B
  aliasofObj : Obj → n B
  mkBinding : Mod → Sym → n B
  unwrap_unionall : Obj → Obj
  /-- `names(mod; all=true)` and `Base.ispublic(mod, sym)`. -/
  names : Mod → n (List Sym)
  ispublic : Mod → Sym → n Bool

section runtime
variable {m : Type → Type} [Monad m] [MonadExceptOf DocError m] {Mod B Ty X O A Obj R S : Type}
variable [MonadStateOf (World Mod B Ty X O A) m]

def throwDoc {α : Type} (e : DocError) : m α := throwThe DocError e

def getWorld (_o : DocsOps m Mod B Ty X O A Obj R S) : m (World Mod B Ty X O A) := getThe (World Mod B Ty X O A)
def setWorld (_o : DocsOps m Mod B Ty X O A Obj R S) (w : World Mod B Ty X O A) : m Unit := set w

/-- `IdDict` lookup of a `Binding` key. -/
def lookupB {V : Type} (o : DocsOps m Mod B Ty X O A Obj R S) (d : List (B × V)) (k : B) : Option V :=
  (d.find? fun e => o.egalB e.1 k).map (·.2)

/-- `IdDict` lookup of a type key. -/
def lookupTy {V : Type} (o : DocsOps m Mod B Ty X O A Obj R S) (d : List (Ty × V)) (k : Ty) : Option V :=
  (d.find? fun e => o.egalTy e.1 k).map (·.2)

/-- `d[k] = v` of an `IdDict` keyed by types: replaces the value of an existing key. -/
def setTy {V : Type} (o : DocsOps m Mod B Ty X O A Obj R S) (d : List (Ty × V)) (k : Ty) (v : V) :
    List (Ty × V) :=
  if d.any (fun e => o.egalTy e.1 k) then d.map fun e => if o.egalTy e.1 k then (e.1, v) else e
  else d ++ [(k, v)]

/-- `d[k] = v` of a `Dict{Symbol,Any}`. -/
def setSym {V : Type} (d : List (Sym × V)) (k : Sym) (v : V) : List (Sym × V) :=
  if d.any (·.1 == k) then d.map fun e => if e.1 == k then (e.1, v) else e
  else d ++ [(k, v)]

/-- The `META` dictionary of a module, when the global is defined. -/
def metaOf (o : DocsOps m Mod B Ty X O A Obj R S) (w : World Mod B Ty X O A) (md : Mod) :
    Option (List (B × Nat)) :=
  (w.metas.find? fun e => o.egalMod e.1 md).map (·.2)

def multidocAt (o : DocsOps m Mod B Ty X O A Obj R S) (r : Nat) : m (MultiDocObj Ty) := do
  match (← getWorld o).multidocs[r]? with
  | some d => pure d
  | none => throwDoc .typeError

def docstrAt (o : DocsOps m Mod B Ty X O A Obj R S) (r : Nat) : m (DocStr X O A) := do
  match (← getWorld o).docstrs[r]? with
  | some d => pure d
  | none => throwDoc .typeError

/--
Julia source: base/docs/Docs.jl:90-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function initmeta(m::Module)
    if !invokelatest(isdefinedglobal, m, META)
        val = METAType()
        Core.eval(m, :(const $META = $val))
        push!(modules, m)
        return val
    end
    return invokelatest(getglobal, m, META)
end

```
-/
/- `initmeta(m)`: the `META` dictionary is identified by its module. -/
def initmeta (o : DocsOps m Mod B Ty X O A Obj R S) (md : Mod) : m Mod := do
  let w ← getWorld o
  if (metaOf o w md).isNone then
    -- `val = METAType()`; `Core.eval(m, :(const $META = $val))`
    o.evalConstMeta md
    let w ← getWorld o
    setWorld o { w with metas := w.metas ++ [(md, [])], modules := w.modules ++ [md] }
    return md
  return md

/--
Julia source: base/docs/Docs.jl:80-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function meta(m::Module; autoinit::Bool=true)
    if !invokelatest(isdefinedglobal, m, META)
        return autoinit ? initmeta(m) : nothing
    end
    # TODO: This `invokelatest` is not technically required, but because
    # of the automatic constant backdating is currently required to avoid
    # a warning.
    return invokelatest(getglobal, m, META)::METAType
end

```
-/
/- `meta(m; autoinit)`: `none` is `nothing`; a dictionary is identified by its module. -/
def «meta» (o : DocsOps m Mod B Ty X O A Obj R S) (md : Mod) (autoinit : Bool := true) : m (Option Mod) := do
  let w ← getWorld o
  if (metaOf o w md).isNone then
    if autoinit then return some (← initmeta o md) else return none
  -- `getglobal(m, META)::METAType`: the global holds the dictionary `initmeta` stored
  return some md

/--
Julia source: base/docs/Docs.jl:132-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function argtype(expr::Expr)
    isexpr(expr, :(::))  && return expr.args[end]
    isexpr(expr, :(...)) && return :(Vararg{$(argtype(expr.args[1]))})
    if isexpr(expr, :meta) && length(expr.args) == 2
        a1 = expr.args[1]
        if a1 === :nospecialize || a1 === :specialize
            return argtype(expr.args[2])
        end
    end
    return argtype(expr.args[1])
end
argtype(@nospecialize other) = :Any

tvar(x::Expr)   = x
tvar(s::Symbol) = :($s <: Any)

```
-/
/- `argtype(expr)`. -/
def argtype {L : Type} : Value L → DocResult (Value L)
  | .expr head args =>
    if head == "::" then argLast args
    else if head == "..." then
      match args with
      | a1 :: _ => do return .expr "curly" [.symbol "Vararg", ← argtype a1]
      | [] => .error .boundsError
    else
      match args with
      | [a1, a2] =>
        if head == "meta" && (a1 matches .symbol "nospecialize" || a1 matches .symbol "specialize") then
          argtype a2
        else argtype a1
      | a1 :: _ => argtype a1
      | [] => .error .boundsError
  | _ => .ok (.symbol "Any")

/-- `tvar(x)`. -/
def tvar {L : Type} : Value L → DocResult (Value L)
  | .expr h a => .ok (.expr h a)
  | .symbol s => .ok (.expr "<:" [.symbol s, .symbol "Any"])
  | _ => .error (.methodError "tvar")

/--
Julia source: base/docs/Docs.jl:100-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function signature!(tv::Vector{Any}, expr::Expr)
    is_macrocall = isexpr(expr, :macrocall)
    if is_macrocall || isexpr(expr, :call)
        sig = :(Union{Tuple{}})
        first_arg = is_macrocall ? 3 : 2 # skip function arguments
        for arg in expr.args[first_arg:end]
            isexpr(arg, :parameters) && continue
            if isexpr(arg, :kw) # optional arg
                push!(sig.args, :(Tuple{$((sig.args[end]::Expr).args[2:end]...)}))
            end
            push!((sig.args[end]::Expr).args, argtype(arg))
        end
        if isexpr(expr.args[1], :curly) && isempty(tv)
            append!(tv, mapany(tvar, (expr.args[1]::Expr).args[2:end]))
        end
        for i = length(tv):-1:1
            push!(sig.args, :(Tuple{$((tv[i]::Expr).args[1])}))
        end
        for i = length(tv):-1:1
            sig = Expr(:where, sig, tv[i])
        end
        return sig
    elseif isexpr(expr, :where)
        append!(tv, mapany(tvar, expr.args[2:end]))
        return signature!(tv, expr.args[1])
    else
        return signature!(tv, expr.args[1])
    end
end
signature!(tv::Vector{Any}, @nospecialize(other)) = :(Union{})
signature(expr::Expr) = signature!([], expr)
signature(@nospecialize other) = signature!([], other)
```
-/
/- `push!((sig.args[end]::Expr).args, x)`. -/
def pushLast {L : Type} (sigArgs : List (Value L)) (x : Value L) : DocResult (List (Value L)) :=
  match sigArgs.getLast? with
  | some (.expr h a) => .ok (sigArgs.dropLast ++ [.expr h (a ++ [x])])
  | some _ => .error .typeError
  | none => .error .boundsError

/-- `(tv[i]::Expr).args[1]`. -/
def tvArg1 {L : Type} (t : Value L) : DocResult (Value L) := do
  let (_, a) ← asExpr t
  argAt a 1

/-- `signature!(tv, expr)`: returns the updated `tv` with the signature. -/
def signature_bang {L : Type} (tv : List (Value L)) : Value L → DocResult (List (Value L) × Value L)
  | .expr head args => do
    let is_macrocall := head == "macrocall"
    if is_macrocall || head == "call" then
      -- `sig = :(Union{Tuple{}})`: the arguments of the `:curly` expression
      let mut sigArgs : List (Value L) := [.symbol "Union", .expr "curly" [.symbol "Tuple"]]
      let first_arg := if is_macrocall then 3 else 2 -- skip function arguments
      for arg in args.drop (first_arg - 1) do
        if isexpr arg "parameters" then continue
        if isexpr arg "kw" then -- optional arg
          match sigArgs.getLast? with
          | some (.expr _ a) => sigArgs := sigArgs ++ [.expr "curly" (.symbol "Tuple" :: a.drop 1)]
          | some _ => throw .typeError
          | none => throw .boundsError
        sigArgs ← pushLast sigArgs (← argtype arg)
      let mut tv := tv
      if isexpr (← argAt args 1) "curly" && tv.isEmpty then
        let (_, ca) ← asExpr (← argAt args 1)
        tv := tv ++ (← (ca.drop 1).mapM tvar)
      for t in tv.reverse do
        sigArgs := sigArgs ++ [.expr "curly" [.symbol "Tuple", ← tvArg1 t]]
      let mut sig : Value L := .expr "curly" sigArgs
      for t in tv.reverse do
        sig := .expr "where" [sig, t]
      return (tv, sig)
    else if head == "where" then
      let tv := tv ++ (← (args.drop 1).mapM tvar)
      match args with
      | a1 :: _ => signature_bang tv a1
      | [] => throw .boundsError
    else
      match args with
      | a1 :: _ => signature_bang tv a1
      | [] => throw .boundsError
  | _ => .ok (tv, unionEmptyExpr)

/-- `signature(expr) = signature!([], expr)`. -/
def signature {L : Type} (x : Value L) : DocResult (Value L) := do
  return (← signature_bang [] x).2

/--
Julia source: base/docs/Docs.jl:149-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Docsystem types.
# ================

"""
    Docs.DocStr

Stores the contents of a single docstring as well as related metadata.

Both the raw text, `.text`, and the parsed markdown, `.object`, are tracked by this type.
Parsing of the raw text is done lazily when a request is made to render the docstring,
which helps to reduce total precompiled image size.

The `.data` field stores several values related to the docstring, such as: path,
linenumber, source code, and fielddocs.
"""
mutable struct DocStr
    text   :: Core.SimpleVector
    object :: Any
    data   :: Dict{Symbol, Any}
end

```
-/
/- `DocStr(text, object, data)`: allocates a `DocStr` and returns its reference. -/
def newDocStr (o : DocsOps m Mod B Ty X O A Obj R S) (text : List X) (object : Option O)
    (data : List (Sym × A)) : m Nat := do
  let w ← getWorld o
  setWorld o { w with docstrs := w.docstrs ++ [⟨text, object, data⟩] }
  return w.docstrs.length

/--
Julia source: base/docs/Docs.jl:185-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

_docstr(vec::Core.SimpleVector, data::Dict{Symbol,Any}) = DocStr(vec,            nothing, data)
_docstr(str::AbstractString,    data::Dict{Symbol,Any}) = DocStr(Core.svec(str), nothing, data)
_docstr(object,                 data::Dict{Symbol,Any}) = DocStr(Core.svec(),     object, data)

_docstr(doc::DocStr, data::Dict{Symbol,Any}) = (doc.data = merge(data, doc.data); doc)

```
-/
/- The arguments `docstr(object, data)` dispatches on. -/
inductive DocInput (X O S : Type) where
  | svec (vec : List X)
  | string (str : S)
  | docStr (ref : Nat)
  | other (object : O)

/-- `_docstr(object, data)`. -/
def _docstr (o : DocsOps m Mod B Ty X O A Obj R S) (object : DocInput X O S) (data : List (Sym × A)) :
    m Nat := do
  match object with
  | .svec vec => newDocStr o vec none data
  | .string str => newDocStr o [o.ofString str] none data
  | .other obj => newDocStr o [] (some obj) data
  | .docStr r =>
    -- `doc.data = merge(data, doc.data)`
    let doc ← docstrAt o r
    let merged := doc.data.foldl (fun d e => setSym d e.1 e.2) data
    let w ← getWorld o
    setWorld o { w with docstrs := w.docstrs.set r { doc with data := merged } }
    return r

/--
Julia source: base/docs/Docs.jl:170-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function docstr(binding::Binding, typesig = Union{})
    @nospecialize typesig
    for m in modules
        dict = meta(m; autoinit=false)
        isnothing(dict) && continue
        if haskey(dict, binding)
            docs = dict[binding].docs
            if haskey(docs, typesig)
                return docs[typesig]
            end
        end
    end
    error("could not find matching docstring for '$binding :: $typesig'.")
end
docstr(object, data = Dict{Symbol,Any}()) = _docstr(object, data)
```
-/
/- `docstr(binding, typesig)`. -/
def docstr_Binding (o : DocsOps m Mod B Ty X O A Obj R S) (binding : B) (typesig : Ty) : m Nat := do
  for md in (← getWorld o).modules do
    let some dict ← «meta» o md (autoinit := false) | continue
    let w ← getWorld o
    let entries := (metaOf o w dict).getD []
    if let some mdref := lookupB o entries binding then
      let docs := (← multidocAt o mdref).docs
      if let some r := lookupTy o docs typesig then
        return r
  throwDoc (.errorException ("could not find matching docstring for '" ++ (← o.bindingString binding) ++
    " :: " ++ (← o.tyString typesig) ++ "'."))

/-- `docstr(object, data = Dict{Symbol,Any}())`. -/
def docstr (o : DocsOps m Mod B Ty X O A Obj R S) (object : DocInput X O S) (data : List (Sym × A) := []) :
    m Nat :=
  _docstr o object data


/--
Julia source: base/docs/Docs.jl:200-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    MultiDoc

Stores a collection of docstrings for related objects, ie. a `Function`/`DataType` and
associated `Method` objects.

Each documented object in a `MultiDoc` is referred to by its signature which is represented
by a `Union` of `Tuple` types. For example, the following `Method` definition

    f(x, y) = ...

is stored as `Tuple{Any, Any}` in the `MultiDoc` while

    f(x::T, y = ?) where {T} = ...

is stored as `Union{Tuple{T, Any}, Tuple{T}} where T`.

Note: The `Function`/`DataType` object's signature is always `Union{}`.
"""
mutable struct MultiDoc
    "Ordered (via definition order) vector of object signatures."
    order::Vector{Type}
    "Documentation for each object. Keys are signatures."
    docs::METAType

    MultiDoc() = new(Type[], METAType())
end

```
-/
/- `MultiDoc()`: allocates an empty `MultiDoc` and returns its reference. -/
def newMultiDoc (o : DocsOps m Mod B Ty X O A Obj R S) : m Nat := do
  let w ← getWorld o
  setWorld o { w with multidocs := w.multidocs ++ [(⟨[], []⟩ : MultiDocObj Ty)] }
  return w.multidocs.length

/--
Julia source: base/docs/Docs.jl:228-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Docstring registration.
# =======================

"""
    Docs.doc!(__module__, binding, str, sig)

Adds a new docstring `str` to the docsystem of `__module__` for `binding` and signature `sig`.
"""
function doc!(__module__::Module, b::Binding, str::DocStr, @nospecialize sig = Union{})
    # Module docstrings are in the module itself
    if defined(b)
        obj = resolve(b)
        if isa(obj, Module)
            __module__ = obj
        end
    end
    initmeta(__module__)
    m = get!(meta(__module__), b, MultiDoc())
    if haskey(m.docs, sig)
        # We allow for docstrings to be updated, but print a warning since it is possible
        # that over-writing a docstring *may* have been accidental.  The warning
        # is suppressed for symbols in Main (or current active module),
        # for interactive use (#23011).
        __module__ === Base.active_module() ||
            @warn "Replacing docs for `$b :: $sig` in module `$(__module__)`"
    else
        # The ordering of docstrings for each Binding is defined by the order in which they
        # are initially added. Replacing a specific docstring does not change its ordering.
        push!(m.order, sig)
    end
    m.docs[sig] = str
    str.data[:binding] = b
    str.data[:typesig] = sig
    return b
end

```
-/
def doc_bang (o : DocsOps m Mod B Ty X O A Obj R S) (mod : Mod) (b : B) (str : Nat) (sig : Ty) : m B := do
  let mut mod := mod
  -- Module docstrings are in the module itself
  if ← o.defined b then
    let obj ← o.resolve b
    if let some objm := o.asModule obj then
      mod := objm
  let _ ← initmeta o mod
  -- `get!(meta(__module__), b, MultiDoc())`
  let some dict ← «meta» o mod | throwDoc .typeError
  let fresh ← newMultiDoc o
  let w ← getWorld o
  let entries := (metaOf o w dict).getD []
  let mref ← match lookupB o entries b with
    | some r => pure r
    | none => do
      setWorld o { w with metas := w.metas.map fun e => if o.egalMod e.1 dict then (e.1, e.2 ++ [(b, fresh)]) else e }
      pure fresh
  let md ← multidocAt o mref
  let md ← if (lookupTy o md.docs sig).isSome then do
      -- We allow for docstrings to be updated, but print a warning since it is possible
      -- that over-writing a docstring *may* have been accidental.
      if !o.egalMod mod (← o.active_module) then
        o.warn ("Replacing docs for `" ++ (← o.bindingString b) ++ " :: " ++ (← o.tyString sig) ++
          "` in module `" ++ (← o.modString mod) ++ "`")
      pure md
    else
      -- The ordering of docstrings for each Binding is defined by the order in which they
      -- are initially added. Replacing a specific docstring does not change its ordering.
      pure { md with order := md.order ++ [sig] }
  let md := { md with docs := setTy o md.docs sig str }
  let w ← getWorld o
  setWorld o { w with multidocs := w.multidocs.set mref md }
  let d ← docstrAt o str
  let data := setSym (setSym d.data "binding" (o.ofBinding b)) "typesig" (o.ofTy sig)
  let w ← getWorld o
  setWorld o { w with docstrs := w.docstrs.set str { d with data := data } }
  return b

/--
Julia source: base/docs/Docs.jl:264-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Docstring lookup.
# =================

"""
    getdoc(obj)
    getdoc(obj, sig)

Return a custom docstring object associated with the object `obj` and, optionally, the tuple
type signature `sig`. See `MultiDoc` docs for an explanation of the possible values of `sig`.

The returned object can either be a markdown object generated by `Markdown.parse` or some
other custom type used to display non-markdown formatted documentation.

A return value of `nothing` can be used to signify to the docsystem that no documentation
was found for `obj`, in which case the docsystem will fall back to searching for the
`Binding` associated with `obj` instead.
"""
function getdoc end

getdoc(@nospecialize(x), @nospecialize(sig)) = getdoc(x)
getdoc(@nospecialize(x)) = nothing

```
-/
/- `getdoc(x, sig) = getdoc(x)`. -/
def getdoc_2 (getdoc1 : Obj → m (Option R)) (x : Obj) (_sig : Ty) : m (Option R) := getdoc1 x

/-- `getdoc(x) = nothing`. -/
def getdoc_1 (_x : Obj) : m (Option R) := pure none

/--
Julia source: base/docs/Docs.jl:286-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Utilities.
# ==========

"""
`catdoc(xs...)`: Combine the documentation metadata `xs` into a single meta object.
"""
catdoc() = nothing
catdoc(xs...) = vcat(xs...)

```
-/
/- `catdoc()` is `nothing`; `catdoc(xs...) = vcat(xs...)` over the `vcat` method the arguments
select. -/
def catdoc {Y Z : Type} (vcat : List Y → m Z) : List Y → m (Option Z)
  | [] => pure none
  | xs => some <$> vcat xs

/--
Julia source: base/docs/Docs.jl:295-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const keywords = Dict{Symbol, DocStr}()

```
-/
/- The initial `keywords` dictionary, `World.keywords`. -/
def keywords_initial : List (Sym × Nat) := []

end runtime

section ast2
variable {L : Type}

/--
Julia source: base/docs/Docs.jl:297-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
namify(@nospecialize x) = astname(x, isexpr(x, :macro))

function astname(x::Expr, ismacro::Bool)
    head = x.head
    if head === :.
        ismacro ? macroname(x) : x
elseif head === :call && length(x.args) >= 1 && isexpr(x.args[1], :(::))
        # for documenting (x::y)(args...), extract the name from y
        # otherwise, for documenting `x::y`, it will be extracted from x
        astname((x.args[1]::Expr).args[end], ismacro)
    elseif head === :overlay
        # for documenting `Base.Experimental.@overlay mt f(args...)`, the callee is
        # `Expr(:overlay, mt, f)`: extract the name from f
        astname(x.args[end], ismacro)
    else
        n = if isexpr(x, :module)
            isa(x.args[1], Bool) ? 2 : 3
        elseif isexpr(x, :struct)
            2
        elseif isexpr(x, (:call, :macrocall, :function, :(=), :macro, :where, :curly,
                          :(::), :(<:), :(>:), :local, :global, :const, :atomic,
                          :copyast, :quote, :inert, :primitive, :abstract,
                          :escape, :var"hygienic-scope"))
            # similar to is_function_def, but without -> and with various assignments, quoted statements, and miscellaneous that might be encountered in struct definitions also
            1
        else
            return x # nothing to see here--bindingexpr will convert this to an error if defining a doc
        end
        length(x.args) < n && return x
        astname(x.args[n], ismacro)
    end
end
astname(q::QuoteNode, ismacro::Bool) = astname(q.value, ismacro)
astname(s::Symbol, ismacro::Bool)    = ismacro ? macroname(s) : s
astname(@nospecialize(other), ismacro::Bool) = other

macroname(s::Symbol) = Symbol('@', s)
macroname(x::Expr)   = Expr(x.head, x.args[1], macroname(x.args[end].value))

```
-/
-- `Symbol('@', s)`
def macroname_Symbol (s : Sym) : Value L := .symbol ("@" ++ s)

mutual
/-- `macroname(x)`. -/
def macroname (leafMacroname : L → DocResult (Value L)) : Value L → DocResult (Value L)
  | .symbol s => .ok (macroname_Symbol s)
  | .expr h args => do
    let a1 ← argAt args 1
    return .expr h [a1, ← macroname_last leafMacroname args]
  | _ => .error (.methodError "macroname")

/-- `macroname(args[end].value)`. -/
def macroname_last (leafMacroname : L → DocResult (Value L)) : List (Value L) → DocResult (Value L)
  | [] => .error .boundsError
  | [.quoteNode v] => macroname leafMacroname v
  | [.leaf x] => leafMacroname x
  | [_] => .error (.fieldError "value")
  | _ :: rest => macroname_last leafMacroname rest
end

/-- The heads `astname` descends through at argument 1. -/
def astnameHeads : List Sym :=
  ["call", "macrocall", "function", "=", "macro", "where", "curly", "::", "<:", ">:", "local",
   "global", "const", "atomic", "copyast", "quote", "inert", "primitive", "abstract", "escape",
   "hygienic-scope"]

mutual
/-- `astname(x, ismacro)`. `leafMacroname x` is `macroname(x.value)` for a non-AST object `x`,
whose `value` property is read by the object's own `getproperty`. -/
def astname (lo : LeafOps L) (leafMacroname : L → DocResult (Value L)) (ismacro : Bool) :
    Value L → DocResult (Value L)
  | .expr head args =>
    if head == "." then
      if ismacro then macroname leafMacroname (.expr head args) else .ok (.expr head args)
    else if head == "call" && args.length ≥ 1 && isexpr (args.headD (.symbol "")) "::" then
      -- for documenting (x::y)(args...), extract the name from y
      astname_firstLast lo leafMacroname ismacro args
    else if head == "overlay" then
      -- for documenting `Base.Experimental.@overlay mt f(args...)`: extract the name from f
      astname_last lo leafMacroname ismacro args
    else do
      let n ← if head == "module" then do
          let a1 ← argAt args 1
          pure (match a1 with
            | .leaf x => if (lo.asBool x).isSome then 2 else 3
            | _ => 3)
        else if head == "struct" then pure 2
        else if astnameHeads.contains head then pure 1
        else return .expr head args -- nothing to see here
      if args.length < n then return .expr head args
      astname_nth lo leafMacroname ismacro args n
  | .quoteNode v => astname lo leafMacroname ismacro v
  | .symbol s => if ismacro then macroname leafMacroname (.symbol s) else .ok (.symbol s)
  | other => .ok other

/-- `astname(args[n], ismacro)` with `1 ≤ n ≤ length(args)`. -/
def astname_nth (lo : LeafOps L) (leafMacroname : L → DocResult (Value L)) (ismacro : Bool) :
    List (Value L) → Nat → DocResult (Value L)
  | [], _ => .error .boundsError
  | a :: _, 1 => astname lo leafMacroname ismacro a
  | _ :: rest, n => astname_nth lo leafMacroname ismacro rest (n - 1)

/-- `astname(args[end], ismacro)`. -/
def astname_last (lo : LeafOps L) (leafMacroname : L → DocResult (Value L)) (ismacro : Bool) :
    List (Value L) → DocResult (Value L)
  | [] => .error .boundsError
  | [a] => astname lo leafMacroname ismacro a
  | _ :: rest => astname_last lo leafMacroname ismacro rest

/-- `astname((args[1]::Expr).args[end], ismacro)`. -/
def astname_firstLast (lo : LeafOps L) (leafMacroname : L → DocResult (Value L)) (ismacro : Bool) :
    List (Value L) → DocResult (Value L)
  | .expr _ a :: _ => astname_last lo leafMacroname ismacro a
  | _ :: _ => .error .typeError
  | [] => .error .boundsError
end

/-- `namify(x) = astname(x, isexpr(x, :macro))`. -/
def namify (lo : LeafOps L) (leafMacroname : L → DocResult (Value L)) (x : Value L) : DocResult (Value L) :=
  astname lo leafMacroname (isexpr x "macro") x

/--
Julia source: base/docs/Docs.jl:336-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfield(@nospecialize x) = isexpr(x, :.) &&
    (isa(x.args[1], Symbol) || isfield(x.args[1])) &&
    (isa(x.args[2], QuoteNode) || isexpr(x.args[2], :quote))

```
-/
-- `isexpr(x, :.)`
def isDotExpr (x : Value L) : Bool := isexpr x "."

mutual
/-- `isfield(x)`. -/
def isfield : Value L → DocResult Bool
  | .expr "." args => isfield_args args
  | _ => .ok false

/-- `(isa(args[1], Symbol) || isfield(args[1])) && (isa(args[2], QuoteNode) || isexpr(args[2], :quote))`. -/
def isfield_args : List (Value L) → DocResult Bool
  | [] => .error .boundsError
  | a1 :: rest => do
    let c1 ← if isSymbol a1 then pure true else isfield a1
    if !c1 then return false
    match rest with
    | a2 :: _ => return isQuoteNode a2 || isexpr a2 "quote"
    | [] => throw .boundsError
end


/--
Julia source: base/docs/Docs.jl:437-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
callargs(ex::Expr) = isexpr(ex, :where) ? callargs(ex.args[1]) :
    isexpr(ex, :call) ? ex.args[2:end] : error("Invalid expression to callargs: $ex")
validcall(x) = isa(x, Symbol) || isexpr(x, (:(::), :..., :kw, :parameters))

```
-/
/- `callargs(ex::Expr)`; `str` is the string interpolation `"$ex"`. -/
def callargs (str : Value L → String) : Value L → DocResult (List (Value L))
  | .expr "where" (a1 :: _) => callargs str a1
  | .expr "where" [] => .error .boundsError
  | .expr "call" args => .ok (args.drop 1)
  | .expr h args => .error (.errorException ("Invalid expression to callargs: " ++ str (.expr h args)))
  | _ => .error (.methodError "callargs")

/-- `validcall(x)`. -/
def validcall (x : Value L) : Bool :=
  isSymbol x || isexpr_heads x ["::", "...", "kw", "parameters"]


/--
Julia source: base/docs/Docs.jl:605-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const FUNC_HEADS    = [:function, :macro, :(=)]
const BINDING_HEADS = [:const, :global, :(=)]
# For the special `:@mac` / `:(Base.@mac)` syntax for documenting a macro after definition.
isquotedmacrocall(@nospecialize x) =
    isexpr(x, :copyast, 1) &&
    isa(x.args[1], QuoteNode) &&
    isexpr(x.args[1].value, :macrocall, 2)
# Simple expressions / atoms the may be documented.
isbasicdoc(@nospecialize x) = isexpr(x, :.) || isa(x, Union{QuoteNode, Symbol})
is_signature(@nospecialize x) = isexpr(x, :call) || (isexpr(x, :(::), 2) && isexpr(x.args[1], :call)) || isexpr(x, :where)

```
-/
def FUNC_HEADS : List Sym := ["function", "macro", "="]
def BINDING_HEADS : List Sym := ["const", "global", "="]

/-- `isquotedmacrocall(x)`. -/
def isquotedmacrocall (x : Value L) : DocResult Bool := do
  if !isexpr_n x "copyast" (JInt.wrap .i64 1) then return false
  let (_, args) ← asExpr x
  match ← argAt args 1 with
  | .quoteNode v => return isexpr_n v "macrocall" (JInt.wrap .i64 2)
  | _ => return false

/-- `isbasicdoc(x)`. -/
def isbasicdoc (x : Value L) : Bool := isexpr x "." || isQuoteNode x || isSymbol x

/-- `is_signature(x)`. -/
def is_signature (x : Value L) : DocResult Bool := do
  if isexpr x "call" then return true
  if isexpr_n x "::" (JInt.wrap .i64 2) then
    let (_, args) ← asExpr x
    if isexpr (← argAt args 1) "call" then return true
  return isexpr x "where"

end ast2

section runtime2
variable {m : Type → Type} [Monad m] [MonadExceptOf DocError m] {Mod B Ty X O A Obj R S : Type}
variable [MonadStateOf (World Mod B Ty X O A) m]

/--
Julia source: base/docs/Docs.jl:616-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _doc(binding::Binding, sig::Type = Union{})
    if defined(binding)
        result = getdoc(resolve(binding), sig)
        result === nothing || return result
    end
    # Lookup first match for `binding` and `sig` in all modules of the docsystem.
    for mod in modules
        dict = meta(mod; autoinit=false)
        isnothing(dict) && continue
        if haskey(dict, binding)
            multidoc = dict[binding]
            for msig in multidoc.order
                sig <: msig && return multidoc.docs[msig]
            end
            # if no matching signatures, return first
            if !isempty(multidoc.docs)
                return first(values(multidoc.docs))
            end
        end
    end
    return nothing
end

```
-/
/- The result of a lookup: a `getdoc` object, a `DocStr` reference, or `nothing`. -/
inductive Found (R : Type) where
  | custom (r : R)
  | docStr (ref : Nat)
  | nothing

/-- `_doc(binding, sig)`. -/
def _doc (o : DocsOps m Mod B Ty X O A Obj R S) (binding : B) (sig : Ty) : m (Found R) := do
  if ← o.defined binding then
    let result ← o.getdoc (← o.resolve binding) sig
    if let some r := result then return .custom r
  -- Lookup first match for `binding` and `sig` in all modules of the docsystem.
  for mod in (← getWorld o).modules do
    let some dict ← «meta» o mod (autoinit := false) | continue
    let w ← getWorld o
    if let some mref := lookupB o ((metaOf o w dict).getD []) binding then
      let multidoc ← multidocAt o mref
      for msig in multidoc.order do
        if o.subtype sig msig then
          match lookupTy o multidoc.docs msig with
          | some r => return .docStr r
          | none => throwDoc .keyError
      -- if no matching signatures, return first
      if !multidoc.docs.isEmpty then
        match o.idDictFirst multidoc.docs with
        | some r => return .docStr r
        | none => throwDoc .boundsError
  return .nothing

/--
Julia source: base/docs/Docs.jl:639-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Some additional convenience `doc` methods that take objects rather than `Binding`s.
_doc(obj::UnionAll) = _doc(Base.unwrap_unionall(obj))
_doc(object, sig::Type = Union{}) = _doc(aliasof(object, typeof(object)), sig)
_doc(object, sig...)              = _doc(object, Tuple{sig...})

```
-/
/- `_doc(obj::UnionAll) = _doc(Base.unwrap_unionall(obj))`, through `_doc(object, sig)`. -/
def _doc_object (o : DocsOps m Mod B Ty X O A Obj R S) (object : Obj) (sig : Ty) : m (Found R) := do
  _doc o (← o.aliasofObj object) sig

def _doc_UnionAll (o : DocsOps m Mod B Ty X O A Obj R S) (obj : Obj) : m (Found R) :=
  _doc_object o (o.unwrap_unionall obj) o.unionEmpty

/-- `_doc(object, sig...) = _doc(object, Tuple{sig...})`. -/
def _doc_vararg (o : DocsOps m Mod B Ty X O A Obj R S) (object : Obj) (sig : List Ty) : m (Found R) :=
  _doc_object o object (o.tupleOf sig)


end runtime2

/--
Julia source: base/docs/Docs.jl:686-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iscallexpr(ex::Expr) = isexpr(ex, :where) ? iscallexpr(ex.args[1]) : isexpr(ex, :call)
iscallexpr(@nospecialize ex) = false

```
-/
/- `iscallexpr(ex)`. -/
def iscallexpr {L : Type} : Value L → DocResult Bool
  | .expr "where" (a1 :: _) => iscallexpr a1
  | .expr "where" [] => .error .boundsError
  | .expr h _ => .ok (h == "call")
  | _ => .ok false


-- UNTRANSLATED
-- `formatdoc`, `parsedoc`, `apropos` and `doc` are declared without methods (implemented in the REPL stdlib)
-- Source: base/docs/Docs.jl:826-858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function formatdoc end
-- function parsedoc end
-- 
-- """
--     apropos([io::IO=stdout], pattern::Union{AbstractString,Regex})
-- 
-- Search available docstrings for entries containing `pattern`.
-- 
-- When `pattern` is a string, case is ignored. Results are printed to `io`.
-- 
-- `apropos` can be called from the help mode in the REPL by wrapping the query in double quotes:
-- ```
-- help?> "pattern"
-- ```
-- 
-- !!! compat "Julia 1.11"
--     In Julia 1.11 and newer, `apropos` requires that the `REPL` stdlib is loaded.
-- """
-- function apropos end
-- 
-- """
--     Docs.doc(binding, sig)
-- 
-- Return all documentation that matches both `binding` and `sig`.
-- 
-- If `getdoc` returns a non-`nothing` result on the value of the binding, then a
-- dynamic docstring is returned instead of one based on the binding itself.
-- 
-- !!! compat "Julia 1.11"
--     In Julia 1.11 and newer, `Docs.doc` requires that the `REPL` stdlib is loaded.
-- """
-- function doc end
-- 
-- /Source

section runtime3
variable {m : Type → Type} [Monad m] [MonadExceptOf DocError m] {Mod B Ty X O A Obj R S : Type}
variable [MonadStateOf (World Mod B Ty X O A) m]

/--
Julia source: base/docs/Docs.jl:859-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Docs.hasdoc(mod::Module, sym::Symbol)::Bool

Return `true` if `sym` in `mod` has a docstring and `false` otherwise.
"""
hasdoc(mod::Module, sym::Symbol) = hasdoc(Docs.Binding(mod, sym))
function hasdoc(binding::Docs.Binding, sig::Type = Union{})
    # this function is based on the Base.Docs.doc method implemented
    # in REPL/src/docview.jl.  TODO: refactor and unify these methods.
    defined(binding) && !isnothing(getdoc(resolve(binding), sig)) && return true
    for mod in modules
        dict = meta(mod; autoinit=false)
        !isnothing(dict) && haskey(dict, binding) && return true
    end
    alias = aliasof(binding)
    return alias == binding ? false : hasdoc(alias, sig)
end


```
-/
/- `for mod in modules; dict = meta(mod; autoinit=false); !isnothing(dict) && haskey(dict, binding) && return true; end`. -/
def hasdoc_modules (o : DocsOps m Mod B Ty X O A Obj R S) (binding : B) : List Mod → m Bool
  | [] => pure false
  | md :: rest => do
    match ← «meta» o md (autoinit := false) with
    | some dict =>
      if (lookupB o ((metaOf o (← getWorld o) dict).getD []) binding).isSome then return true
      hasdoc_modules o binding rest
    | none => hasdoc_modules o binding rest

/-- `hasdoc(binding, sig)`. -/
def hasdoc [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : DocsOps m Mod B Ty X O A Obj R S)
    (binding : B) (sig : Ty) : m Bool := do
  let d ← o.defined binding
  if d then
    if (← o.getdoc (← o.resolve binding) sig).isSome then return true
  let found ← hasdoc_modules o binding (← getWorld o).modules
  if found then return true
  let alias ← o.aliasof binding
  if o.egalB alias binding then return false else hasdoc o alias sig
partial_fixpoint

/-- `hasdoc(mod::Module, sym::Symbol) = hasdoc(Docs.Binding(mod, sym))`. -/
def hasdoc_Module [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : DocsOps m Mod B Ty X O A Obj R S)
    (mod : Mod) (sym : Sym) : m Bool := do
  hasdoc o (← o.mkBinding mod sym) o.unionEmpty

/--
Julia source: base/docs/Docs.jl:878-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    undocumented_names(mod::Module; private=false)

Return a sorted vector of undocumented symbols in `module` (that is, lacking docstrings).
`private=false` (the default) returns only identifiers declared with `public` and/or
`export`, whereas `private=true` returns all symbols in the module (excluding
compiler-generated hidden symbols starting with `#`).

See also [`names`](@ref), [`Docs.hasdoc`](@ref), [`Base.ispublic`](@ref).
"""
function undocumented_names(mod::Module; private::Bool=false)
    filter!(names(mod; all=true)) do sym
        !hasdoc(mod, sym) && !startswith(string(sym), '#') &&
            (private || Base.ispublic(mod, sym))
    end
end
```
-/
def undocumented_names [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : DocsOps m Mod B Ty X O A Obj R S)
    (mod : Mod) (priv : Bool := false) : m (List Sym) := do
  let mut out := []
  for sym in ← o.names mod do
    let keep ← do
      if ← hasdoc_Module o mod sym then pure false
      else if sym.startsWith "#" then pure false
      else if priv then pure true
      else o.ispublic mod sym
    if keep then out := out ++ [sym]
  return out

end runtime3

-- UNTRANSLATED
-- end of `module Docs`; no method
-- Source: base/docs/Docs.jl:894-895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end
-- /Source

/-! ## The `@doc` macro expansion

The expansion builders below take the macro's `__source__` and `__module__` and return the
expansion as a `Value L` AST. `Expr` values are their contents: a method that mutates an
argument `Expr` in place (`_docm`, `moduledoc`, `__doc__!`, `finddoc`) returns the mutated
expression, and the caller continues with it; sharing of one `Expr` object between two places
of a tree is not represented. The objects that the expansions interpolate (the functions
`docstr`, `doc!`, `_doc`, `getindex`, `setindex!`, `error`, `typeof`, `Pair`, the types
`Dict{Symbol,Any}`, `Pair{Symbol,Any}` and `Binding`, the `keywords` dictionary and the module
`Docs`) are leaves given by name. -/

/-- The callees of the expansion builders over a monad `n`. -/
structure ExpandOps (n : Type → Type) (L : Type) where
  lo : LeafOps L
  /-- The interpolated object of the given name. -/
  obj : String → L
  /-- A `String` value. -/
  str : String → L
  /-- `x isa String`, `x isa AbstractString`. -/
  isString : L → Bool
  isAbstractString : L → Bool
  /-- `Pair(a, b)`: the immutable pair of two values. -/
  pair : Value L → Value L → L
  /-- `x isa Base.BaseDocs.Keyword`: its `name`. -/
  keywordName : L → Option Sym
  /-- `Base.isoperator(s)`. -/
  isoperator : Sym → Bool
  /-- `macroname(x.value)` of a non-AST object (`namify`). -/
  leafMacroname : L → DocResult (Value L)
  /-- The string interpolation `"$x"`, used by `bindingexpr` and `callargs`. -/
  exprString : Value L → String
  /-- `string(x)` and `repr(x)`, run as printing at the call. -/
  string : Value L → n String
  repr : Value L → n String
  /-- `lazy_iterpolate(s)` (`base/docs/core.jl`). -/
  lazy_iterpolate : Value L → n (Value L)
  /-- `RefValue{DocStr}()`: a fresh reference with no value. -/
  newDocStrRef : n L
  /-- `macroexpand(mod, x)`. -/
  macroexpand : L → Value L → n (Value L)
  /-- `haskey(keywords, ex) ? keywords[ex] : nothing`, on the `keywords` dictionary. -/
  keywordLookup : Value L → n (Option L)
  /-- `Base.REPL_MODULE_REF[]` when it is not `Base`, and `invokelatest(REPL.lookup_doc, ex)`. -/
  replModule : n (Option L)
  lookupDocREPL : L → Value L → n (Value L)
  /-- The computations of `base/meta.jl` (`unblock`, `unescape`) and `base/docs/bindings.jl`
  (`bindingexpr`): their errors, and divergence, as computations of `n`. -/
  liftMeta : {α : Type} → ExceptT (JuliaLean.base.meta.MetaError L) Option α → n α
  liftBinding : {α : Type} → Except JuliaLean.base.docs.bindings.BindingError α → n α

section expand
variable {n : Type → Type} [Monad n] [MonadExceptOf DocError n] {L : Type}
variable [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n]
variable (eo : ExpandOps n L)

/-- A `DocResult` computation in `n`. -/
def liftD {α : Type} (r : DocResult α) : n α :=
  match r with
  | .ok a => pure a
  | .error e => throwThe DocError e

/-- The interpolated object `name`. -/
def objV (name : String) : Value L := .leaf (eo.obj name)

/-- `true`, `false` and `nothing` as AST values. -/
def boolV (b : Bool) : Value L := .leaf (eo.lo.ofBool b)
def nothingV : Value L := .leaf eo.lo.nothing

/-- `x === nothing`. -/
def isNothingV (x : Value L) : Bool :=
  match x with
  | .leaf l => eo.lo.isNothing l
  | _ => false

/-- A line node of the quoted code of `base/docs/Docs.jl` or `base/docs/bindings.jl`. -/
def docsLine (line : Int) : Value L := .lineNumberNode (JInt.wrap .i64 line) (.symbol "docs/Docs.jl")
def bindingsLine : Value L := .lineNumberNode (JInt.wrap .i64 36) (.symbol "docs/bindings.jl")

/-- `bindingexpr(x)` (`base/docs/bindings.jl`). -/
def bindingexprN (x : Value L) : n (Value L) :=
  eo.liftBinding (JuliaLean.base.docs.bindings.bindingexpr eo.lo eo.exprString bindingsLine
    (eo.obj "Binding") x)

/-- `namify(x)`. -/
def namifyN (x : Value L) : n (Value L) := liftD (namify eo.lo eo.leafMacroname x)

/-- `x isa Base.BaseDocs.Keyword`: its `name`. -/
def keywordOf (x : Value L) : Option Sym :=
  match x with
  | .leaf l => eo.keywordName l
  | _ => none

/--
Julia source: base/docs/Docs.jl:192-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro ref(x)
    binding = bindingexpr(namify(x))
    typesig = signature(x)
    return esc(docexpr(__source__, __module__, binding, typesig))
end

docexpr(__source__, __module__, args...) = Expr(:call, docstr, args...)

```
-/
def docexpr (args : List (Value L)) : Value L := .expr "call" (objV eo "docstr" :: args)

/-- `@ref(x)`: the expansion, for the macro arguments `__source__` and `__module__`. -/
def macro_ref (x : Value L) : n (Value L) := do
  let binding ← bindingexprN eo (← namifyN eo x)
  let typesig ← liftD (signature x)
  pure (JuliaLean.base.expr.esc (docexpr eo [binding, typesig]))

/--
Julia source: base/docs/Docs.jl:791-802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function docerror(@nospecialize ex)
    txt = """
    cannot document the following expression:

    $(isa(ex, AbstractString) ? repr(ex) : ex)"""
    if isexpr(ex, :macrocall)
        txt *= "\n\n'$(ex.args[1])' not documentable. See 'Base.@__doc__' docs for details."
    end
    return :($(error)($txt, "\n"))
end

```
-/
def docerror (ex : Value L) : n (Value L) := do
  let shown ← match ex with
    | .leaf l => if eo.isAbstractString l then eo.repr ex else eo.string ex
    | _ => eo.string ex
  let mut txt := "cannot document the following expression:\n\n" ++ shown
  if isexpr ex "macrocall" then
    let (_, args) ← liftD (asExpr ex)
    txt := txt ++ "\n\n'" ++ (← eo.string (← liftD (argAt args 1))) ++
      "' not documentable. See 'Base.@__doc__' docs for details."
  pure (.expr "call" [objV eo "error", .leaf (eo.str txt), .leaf (eo.str "\n")])

-- Reason: A section comment.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:340-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # @doc expression builders.
-- # =========================
-- 
-- /Source

/--
Julia source: base/docs/Docs.jl:343-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Docs.metadata(source, module, expr, ismodule)

Build a `Dict` expression containing metadata captured from the expression `expr`.

Fields that may be included in the returned `Dict`:

- `:path`:       Symbol representing the file where `expr` is defined.
- `:linenumber`: Linenumber where `expr` is defined.
- `:module`:     Module where the docstring is defined.
- `:fields`:     `Dict` of all field docs found in `expr`. Only for concrete types.
"""
function metadata(__source__, __module__, expr, ismodule)
    args = []
    # Filename and linenumber of the docstring.
    __file__ = isa(__source__.file, Symbol) ? String(__source__.file) : ""
    push!(args, Pair(:path, __file__))
    push!(args, Pair(:linenumber, __source__.line))
    # Module in which the docstring is defined.
    if ismodule # Module docs go inside the module with name `expr`
        push!(args, :($Pair(:module, $expr)))
    else
        push!(args, Pair(:module, __module__))
    end
    if isexpr(expr, :struct)
        # Field docs for concrete types.
        P = Pair{Symbol,Any}
        fields = P[]
        last_docstr = nothing
        for each in (expr.args[3]::Expr).args
            eachex = unescape(each)
            if isa(eachex, Symbol) || isexpr(eachex, :(::))
                # a field declaration
                if last_docstr !== nothing
                    push!(fields, P(namify(eachex)::Symbol, last_docstr))
                    last_docstr = nothing
                end
            elseif isexpr(eachex, :function) || isexpr(eachex, :(=))
                break
            elseif isa(eachex, String) || isexpr(eachex, :string) || isexpr(eachex, :call) ||
                (isexpr(eachex, :macrocall) && eachex.args[1] === Symbol("@doc_str"))
                # forms that might be doc strings
                last_docstr = each
            end
        end
        dict = :($(Dict{Symbol,Any})($([(:($(P)($(quot(f)), $d)))::Expr for (f, d) in fields]...)))
        push!(args, :($(Pair)(:fields, $dict)))
    end
    return :($(Dict{Symbol,Any})($(args...)))
end
```
-/
-- The `for each in (expr.args[3]::Expr).args` loop: the field docs found, in order.
def metadataFields (fields : List (Sym × Value L)) (last_docstr : Option (Value L)) :
    List (Value L) → n (List (Sym × Value L))
  | [] => pure fields
  | each :: rest => do
    let eachex ← eo.liftMeta (JuliaLean.base.meta.unescape each)
    if isSymbol eachex || isexpr eachex "::" then
      match last_docstr with
      | some d =>
        match ← namifyN eo eachex with
        | .symbol f => metadataFields (fields ++ [(f, d)]) none rest
        | _ => throwThe DocError .typeError
      | none => metadataFields fields last_docstr rest
    else if isexpr eachex "function" || isexpr eachex "=" then pure fields
    else
      let docLike ← match eachex with
        | .leaf l => pure (eo.isString l)
        | .expr "string" _ | .expr "call" _ => pure true
        | .expr "macrocall" args => do
          pure (match ← liftD (argAt args 1) with
            | .symbol "@doc_str" => true
            | _ => false)
        | _ => pure false
      metadataFields fields (if docLike then some each else last_docstr) rest

def metadata (source : Value L) (mod : L) (expr : Value L) (ismodule : Bool) : n (Value L) := do
  let (line, file) ← match source with
    | .lineNumberNode line file => pure (line, file)
    | _ => throwThe DocError (.fieldError "file")
  let file : Value L := .leaf (eo.str (match file with | .symbol s => s | _ => ""))
  let mut args : List (Value L) := [.leaf (eo.pair (.symbol "path") file),
    .leaf (eo.pair (.symbol "linenumber") (.leaf (eo.lo.ofInt line)))]
  if ismodule then
    args := args ++ [.expr "call" [objV eo "Pair", .quoteNode (.symbol "module"), expr]]
  else
    args := args ++ [.leaf (eo.pair (.symbol "module") (.leaf mod))]
  if isexpr expr "struct" then
    let (_, sargs) ← liftD (asExpr expr)
    let (_, body) ← liftD (asExpr (← liftD (argAt sargs 3)))
    let fields ← metadataFields eo [] none body
    let dict : Value L := .expr "call" (objV eo "Dict{Symbol,Any}" :: fields.map fun (f, d) =>
      .expr "call" [objV eo "Pair{Symbol,Any}", JuliaLean.base.meta.quot (.symbol f), d])
    args := args ++ [.expr "call" [objV eo "Pair", .quoteNode (.symbol "fields"), dict]]
  pure (.expr "call" (objV eo "Dict{Symbol,Any}" :: args))

/--
Julia source: base/docs/Docs.jl:393-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function keyworddoc(__source__, __module__, str, def::Base.BaseDocs.Keyword)
    @nospecialize str
    docstr = esc(docexpr(__source__, __module__, lazy_iterpolate(str), metadata(__source__, __module__, def, false)))
    return :($setindex!($(keywords), $docstr, $(esc(quot(def.name)))); nothing)
end
```
-/
-- `def` is the `Keyword`, with name `name`.
def keyworddoc (source : Value L) (mod : L) (str dfn : Value L) (name : Sym) : n (Value L) := do
  let docstr := JuliaLean.base.expr.esc (docexpr eo
    [← eo.lazy_iterpolate str, ← metadata eo source mod dfn false])
  pure (.expr "block" [docsLine 397, .expr "call" [objV eo "setindex!", objV eo "keywords", docstr,
    JuliaLean.base.expr.esc (JuliaLean.base.meta.quot (.symbol name))], docsLine 397,
    .symbol "nothing"])

/--
Julia source: base/docs/Docs.jl:399-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function objectdoc(__source__, __module__, str, def, expr, sig = :(Union{}))
    @nospecialize str def expr sig
    binding = esc(bindingexpr(namify(expr)))
    docstr  = esc(docexpr(__source__, __module__, lazy_iterpolate(str), metadata(__source__, __module__, expr, false)))
    # Store the result of the definition and return it after documenting
    docex = :($(doc!)($__module__, $binding, $docstr, $(esc(sig))))
    if def === nothing
        return Expr(:block, docex)
    else
        exdef = esc(def)
        if isexpr(def, :global, 1) && def.args[1] isa Union{Symbol,GlobalRef}
            # Special case: `global x` should return nothing to avoid syntax errors with assigning to a value
            val = nothing
        else
            if isexpr(def, :(=), 2) && isexpr(def.args[1], :curly)
                # workaround for lowering bug #60001
                exdef = Expr(:block, exdef)
            end
            val = :val
            # if-true hack: val should not be recognized as a struct field,
            # including by @kwdef
            exdef = Expr(:if, true, Expr(:(=), val, exdef))
        end
        # Note: we want to avoid introducing line number nodes here (issue #24468) for def
        return Expr(:block, exdef, docex, Expr(:if, true, val))
    end
end

```
-/
def objectdoc (source : Value L) (mod : L) (str dfn expr : Value L) (sig : Value L := unionEmptyExpr) :
    n (Value L) := do
  let binding := JuliaLean.base.expr.esc (← bindingexprN eo (← namifyN eo expr))
  let docstr := JuliaLean.base.expr.esc (docexpr eo
    [← eo.lazy_iterpolate str, ← metadata eo source mod expr false])
  let docex : Value L :=
    .expr "call" [objV eo "doc!", .leaf mod, binding, docstr, JuliaLean.base.expr.esc sig]
  if isNothingV eo dfn then
    return .expr "block" [docex]
  let mut exdef := JuliaLean.base.expr.esc dfn
  let globalName := match dfn with
    | .expr "global" [.symbol _] | .expr "global" [.globalRef ..] => true
    | _ => false
  let val ← if globalName then pure (nothingV eo)
    else do
      match dfn with
      | .expr "=" [a1, _] => if isexpr a1 "curly" then exdef := .expr "block" [exdef]
      | _ => pure ()
      exdef := .expr "if" [boolV eo true, .expr "=" [.symbol "val", exdef]]
      pure (.symbol "val")
  return .expr "block" [exdef, docex, .expr "if" [boolV eo true, val]]

/--
Julia source: base/docs/Docs.jl:428-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function calldoc(__source__, __module__, str, def::Expr)
    @nospecialize str
    args = callargs(def)
    if isempty(args) || all(validcall, args)
        objectdoc(__source__, __module__, str, nothing, def, signature(def))
    else
        docerror(def)
    end
end
```
-/
def calldoc (source : Value L) (mod : L) (str dfn : Value L) : n (Value L) := do
  let args ← liftD (callargs eo.exprString dfn)
  if args.isEmpty || args.all validcall then
    objectdoc eo source mod str (nothingV eo) dfn (← liftD (signature dfn))
  else
    docerror eo dfn

/--
Julia source: base/docs/Docs.jl:441-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function moduledoc(__source__, __module__, meta, def, def′::Expr)
    @nospecialize meta def
    name  = namify(def′)
    docex = Expr(:call, doc!, name, bindingexpr(name),
        docexpr(__source__, name, lazy_iterpolate(meta), metadata(__source__, __module__, name, true)))
    if def === nothing
        esc(:(Core.eval($name, $(quot(docex)))))
    else
        has_version = !isa(def.args[1], Bool)
        def = unblock(def)
        block = def.args[3 + has_version].args
        if !def.args[1 + has_version]
            pushfirst!(block, :(import Base: @doc))
        end
        push!(block, docex)
        esc(Expr(:toplevel, def))
    end
end

```
-/
def moduledoc (source : Value L) (mod : L) (meta_ dfn dfn' : Value L) : n (Value L) := do
  let name ← namifyN eo dfn'
  let binding ← bindingexprN eo name
  let docex : Value L := .expr "call" [objV eo "doc!", name, binding,
    docexpr eo [← eo.lazy_iterpolate meta_, ← metadata eo source mod name true]]
  if isNothingV eo dfn then
    return JuliaLean.base.expr.esc (.expr "call" [.expr "." [.symbol "Core", .quoteNode (.symbol "eval")],
      name, JuliaLean.base.meta.quot docex])
  let (_, args) ← liftD (asExpr dfn)
  let has_version : Nat := match ← liftD (argAt args 1) with
    | .leaf l => if (eo.lo.asBool l).isSome then 0 else 1
    | _ => 1
  let (h, args) ← liftD (asExpr (← eo.liftMeta (JuliaLean.base.meta.unblock dfn)))
  let (bh, block) ← match ← liftD (argAt args (3 + has_version)) with
    | .expr bh block => pure (bh, block)
    | _ => throwThe DocError (.fieldError "args")
  let std ← match ← liftD (argAt args (1 + has_version)) with
    | .leaf l => match eo.lo.asBool l with
      | some b => pure b
      | none => throwThe DocError (.methodError "!")
    | _ => throwThe DocError (.methodError "!")
  let importDoc : Value L :=
    .expr "import" [.expr ":" [.expr "." [.symbol "Base"], .expr "." [.symbol "@doc"]]]
  let block := (if !std then importDoc :: block else block) ++ [docex]
  return JuliaLean.base.expr.esc
    (.expr "toplevel" [.expr h (args.set (2 + has_version) (.expr bh block))])

/--
Julia source: base/docs/Docs.jl:581-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Walk expression tree `def` and call `λ` when any `@__doc__` markers are found. Returns
# `true` to signify that at least one `@__doc__` has been found, and `false` otherwise.
function finddoc(λ, mod::Module, def::Expr; expand_toplevel::Bool=false)
    if isexpr(def, :block, 2) && isexpr(def.args[1], :meta, 1) && (def.args[1]::Expr).args[1] === :doc
        # Found the macroexpansion of an `@__doc__` expression.
        λ(def)
        true
    else
        if expand_toplevel && isexpr(def, :toplevel)
            for i = 1:length(def.args)
                def.args[i] = macroexpand(mod, def.args[i])
            end
        end
        found = false
        for each in def.args
            found |= finddoc(λ, mod, each; expand_toplevel)
        end
        found
    end
end
finddoc(λ, mod::Module, @nospecialize def; expand_toplevel::Bool=false) = false

```
-/
-- `finddoc(λ, mod, def; expand_toplevel)`: whether a marker was found, the expression after the
-- mutations of `λ` and of the expansion of `:toplevel` arguments, and the marked expressions `λ`
-- was called on, in order. `λ` returns the marked expression after its mutation.
def finddoc [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n] (lam : Value L → Value L) (mod : L) (dfn : Value L) (expand_toplevel : Bool) :
    n (Bool × Value L × List (Value L)) := do
  match dfn with
  | .expr "block" [.expr "meta" [.symbol "doc"], b] =>
    pure (true, lam (.expr "block" [.expr "meta" [.symbol "doc"], b]),
      [.expr "block" [.expr "meta" [.symbol "doc"], b]])
  | .expr h args => do
    let args ← if expand_toplevel && h == "toplevel" then args.mapM (eo.macroexpand mod)
      else pure args
    let mut found := false
    let mut out : List (Value L) := []
    let mut hits : List (Value L) := []
    for each in args do
      let (f, each', hs) ← finddoc lam mod each expand_toplevel
      found := found || f
      out := out ++ [each']
      hits := hits ++ hs
    pure (found, .expr h out, hits)
  | _ => pure (false, dfn, [])
partial_fixpoint

/--
Julia source: base/docs/Docs.jl:549-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __doc__!(source, mod, meta, def, define::Bool)
    @nospecialize source mod meta def
    # Two cases must be handled here to avoid redefining all definitions contained in `def`:
    if define
        function replace_meta_doc(each)
            each.head = :macrocall
            each.args = Any[Symbol("@doc"), source, mod, nothing, meta, each.args[end], define]
        end

        # `def` has not been defined yet (this is the common case, i.e. when not generating
        # the Base image). We just need to convert each `@__doc__` marker to an `@doc`.
        found = finddoc(replace_meta_doc, mod, def; expand_toplevel = false)

        if !found
            found = finddoc(replace_meta_doc, mod, def; expand_toplevel = true)
        end
    else
        # `def` has already been defined during Base image gen so we just need to find and
        # document any subexpressions marked with `@__doc__`.
        docs  = []
        found = finddoc(mod, def; expand_toplevel = true) do each
            push!(docs, :(@doc($source, $mod, $meta, $(each.args[end]), $define)))
        end
        # If any subexpressions have been documented then replace the entire expression with
        # just those documented subexpressions to avoid redefining any definitions.
        if found
            def.head = :toplevel
            def.args = docs
        end
    end
    return found
end
```
-/
-- `replace_meta_doc(each)`: the marked expression after its mutation.
def replace_meta_doc (source : Value L) (mod : L) (meta_ : Value L) (define : Bool)
    (each : Value L) : Value L :=
  let last := match each with
    | .expr _ args => args.getLastD (nothingV eo)
    | _ => nothingV eo
  .expr "macrocall" [.symbol "@doc", source, .leaf mod, nothingV eo, meta_, last, boolV eo define]

/-- `__doc__!(source, mod, meta, def, define)`: whether a marker was found, and `def` after its
mutations. -/
def __doc__! (source : Value L) (mod : L) (meta_ dfn : Value L) (define : Bool) :
    n (Bool × Value L) := do
  if define then
    let rep := replace_meta_doc eo source mod meta_ define
    let (found, dfn, _) ← finddoc eo rep mod dfn false
    if !found then
      let (found, dfn, _) ← finddoc eo rep mod dfn true
      return (found, dfn)
    return (found, dfn)
  else
    let (found, dfn, marked) ← finddoc eo id mod dfn true
    let docs := marked.map fun each =>
      .expr "macrocall" [.symbol "@doc", docsLine 570, source, .leaf mod, meta_,
        (match each with | .expr _ args => args.getLastD (nothingV eo) | _ => nothingV eo),
        boolV eo define]
    return if found then (true, .expr "toplevel" docs) else (false, dfn)

/--
Julia source: base/docs/Docs.jl:644-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function simple_lookup_doc(ex)
    if isa(ex, Expr) && ex.head !== :(.) && Base.isoperator(ex.head)
        # handle syntactic operators, e.g. +=, ::, .=
        ex = ex.head
    end
    if haskey(keywords, ex)
        return keywords[ex]
    elseif !isa(ex, Expr) && !isa(ex, Symbol)
        return :($(_doc)($(typeof)($(esc(ex)))))
    end
    name = namify(ex)
    # If namify couldn't extract a meaningful name and returned an Expr
    # that can't be converted to a binding, treat it like a value
    if isa(name, Expr) && !isexpr(name, :(.))
        return :($(_doc)($(typeof)($(esc(ex)))))
    end
    binding = esc(bindingexpr(name))
    if isexpr(ex, :call) || isexpr(ex, :macrocall) || isexpr(ex, :where)
        sig = esc(signature(ex))
        :($(_doc)($binding, $sig))
    else
        :($(_doc)($binding))
    end
end

```
-/
def simple_lookup_doc (ex : Value L) : n (Value L) := do
  let ex := match ex with
    | .expr h _ => if h != "." && eo.isoperator h then .symbol h else ex
    | _ => ex
  if let some d ← eo.keywordLookup ex then
    return .leaf d
  let typeofDoc : Value L := .expr "call" [objV eo "_doc",
    .expr "call" [objV eo "typeof", JuliaLean.base.expr.esc ex]]
  match ex with
  | .expr .. | .symbol _ => pure ()
  | _ => return typeofDoc
  let name ← namifyN eo ex
  match name with
  | .expr h _ => if h != "." then return typeofDoc
  | _ => pure ()
  let binding := JuliaLean.base.expr.esc (← bindingexprN eo name)
  if isexpr ex "call" || isexpr ex "macrocall" || isexpr ex "where" then
    let sig := JuliaLean.base.expr.esc (← liftD (signature ex))
    pure (.expr "call" [objV eo "_doc", binding, sig])
  else
    pure (.expr "call" [objV eo "_doc", binding])

-- Reason: A comment on `iscallexpr`, which is modelled with its methods.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:683-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # iscallexpr checks if an expression is a :call expression. The call expression may be
-- # also part of a :where expression, so it unwraps the :where layers until it reaches the
-- # "actual" expression
-- /Source

mutual
/--
Julia source: base/docs/Docs.jl:460-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Shares a single doc, `meta`, between several expressions from the tuple expression `ex`
# (but don't actually create the tuple for the result and just return the final one,
# as if this was a C++ comma operator or a block separated by `;` instead of `,`).
function multidoc(__source__, __module__, meta, ex::Expr, define::Bool)
    @nospecialize meta
    out = Expr(:block)
    str = docexpr(__source__, __module__, lazy_iterpolate(meta), metadata(__source__, __module__, ex, false))
    ref = RefValue{DocStr}()
    first = true
    for arg in ex.args
        # The first `arg` to be documented needs to also create the docstring for the group
        # (after doing the action defined by the argument).
        # Subsequent `arg`s just need `ref` to be able to find the docstring without having
        # to create an entirely new one each.
        if first
            first = false
            docstr = :($getindex($setindex!($(ref), $str)))
        else
            docstr = :($getindex($(ref)))
        end
        push!(out.args, docm(__source__, __module__, docstr, arg, define))
    end
    return out
end

```
-/
-- `multidoc(__source__, __module__, meta, ex, define)`.
def multidoc [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n] (source : Value L) (mod : L) (meta_ ex : Value L) (define : Bool) : n (Value L) := do
  let (_, args) ← liftD (asExpr ex)
  let str := docexpr eo [← eo.lazy_iterpolate meta_, ← metadata eo source mod ex false]
  let ref ← eo.newDocStrRef
  let mut out : List (Value L) := []
  let mut first := true
  for arg in args do
    let docstr : Value L := if first then
        .expr "call" [objV eo "getindex", .expr "call" [objV eo "setindex!", .leaf ref, str]]
      else .expr "call" [objV eo "getindex", .leaf ref]
    first := false
    out := out ++ [← docm_meta source mod docstr arg define]
  pure (.expr "block" out)
partial_fixpoint

/--
Julia source: base/docs/Docs.jl:669-682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function docm(source::LineNumberNode, mod::Module, ex)
    @nospecialize ex
    if isexpr(ex, :->) && length(ex.args) > 1
        return docm(source, mod, ex.args...)
    elseif (REPL = Base.REPL_MODULE_REF[]) !== Base
        # TODO: this is a shim to continue to allow `@doc` for looking up docstrings
        return invokelatest(REPL.lookup_doc, ex)
    else
        return simple_lookup_doc(ex)
    end
end
# Drop incorrect line numbers produced by nested macro calls.
docm(source::LineNumberNode, mod::Module, _, _, x...) = docm(source, mod, x...)

```
-/
-- `docm(source, mod, ex)`.
def docm1 [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n] (source : Value L) (mod : L) (ex : Value L) : n (Value L) := do
  match ex with
  | .expr "->" args =>
    if args.length > 1 then return ← docmArgs source mod args
  | _ => pure ()
  match ← eo.replModule with
  | some repl => eo.lookupDocREPL repl ex
  | none => simple_lookup_doc eo ex
partial_fixpoint

/-- `docm(source, mod, args...)`: the method dispatch over the number of arguments and the type
of `define`; `docm(source, mod, _, _, x...)` drops two arguments. -/
def docmArgs [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n] (source : Value L) (mod : L) (args : List (Value L)) : n (Value L) := do
  match args with
  | [] => throwThe DocError (.methodError "docm")
  | [ex] => docm1 source mod ex
  | [meta_, ex] => docm_meta source mod meta_ ex true
  | [meta_, ex, c] =>
    match c with
    | .leaf l => match eo.lo.asBool l with
      | some b => docm_meta source mod meta_ ex b
      | none => docmArgs source mod [c]
    | _ => docmArgs source mod [c]
  | _ :: _ :: rest => docmArgs source mod rest
partial_fixpoint

/--
Julia source: base/docs/Docs.jl:689-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function docm(source::LineNumberNode, mod::Module, meta, ex, define::Bool = true)
    @nospecialize meta ex
    # Some documented expressions may be decorated with macro calls which obscure the actual
    # expression. Expand the macro calls.
    x = macroexpand(mod, ex)
    return _docm(source, mod, meta, x, define)
end

```
-/
-- `docm(source, mod, meta, ex, define)`.
def docm_meta [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n] (source : Value L) (mod : L) (meta_ ex : Value L) (define : Bool) : n (Value L) := do
  let x ← eo.macroexpand mod ex
  _docm source mod meta_ x define
partial_fixpoint

/--
Julia source: base/docs/Docs.jl:697-790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _docm(source::LineNumberNode, mod::Module, meta, x, define::Bool = true)
    if isexpr(x, :var"hygienic-scope")
        x.args[1] = _docm(source, mod, meta, x.args[1])
        return x
    elseif isexpr(x, :escape)
        x.args[1] = _docm(source, mod, meta, x.args[1])
        return x
    elseif isexpr(x, :block)
        docarg = 0
        for i = 1:length(x.args)
            isa(x.args[i], LineNumberNode) && continue
            if docarg == 0
                docarg = i
                continue
            end
            # More than one documentable expression in the block, treat it as a whole
            # expression, which will fall through and look for (Expr(:meta, doc))
            docarg = 0
            break
        end
        if docarg != 0
            x.args[docarg] = _docm(source, mod, meta, x.args[docarg], define)
            return x
        end
    end

    # Don't try to redefine expressions. This is only needed for `Base` img gen since
    # otherwise calling `loaddocs` would redefine all documented functions and types.
    def = define ? x : nothing
    if isa(x, GlobalRef) && (x::GlobalRef).mod == mod
        x = (x::GlobalRef).name
    end

    # Keywords using the `@kw_str` macro in `base/docs/basedocs.jl`.
    #
    #   "..."
    #   kw"if", kw"else"
    #
    doc =
    isa(x, Base.BaseDocs.Keyword) ? keyworddoc(source, mod, meta, x) :

    # Method / macro definitions and "call" syntax.
    #
    #   function f(...) ... end
    #   f(...) = ...
    #   macro m(...) end
    #   function f end
    #   f(...)
    #
    # Including if the "call" expression is wrapped in "where" expression(s) (#32960), i.e.
    #
    #   f(::T) where T
    #   f(::T, ::U) where T where U
    #
    isexpr(x, FUNC_HEADS) && is_signature((x::Expr).args[1]) ? objectdoc(source, mod, meta, def, x::Expr, signature(x::Expr)) :
    (isexpr(x, :function) || isexpr(x, :macro)) && !isexpr((x::Expr).args[1], :call) ? objectdoc(source, mod, meta, def, x::Expr) :
    iscallexpr(x) ? calldoc(source, mod, meta, x::Expr) :

    # Type definitions.
    #
    #   struct T ... end
    #   abstract type T end
    #   primitive type T N end
    #
    isexpr(x, [:struct, :abstract, :primitive]) ? objectdoc(source, mod, meta, def, x::Expr) :

    # "Bindings". Names that resolve to objects with different names, ie.
    #
    #   const T = S
    #   T = S
    #   global T = S
    #
    isexpr(x, BINDING_HEADS) && !isexpr((x::Expr).args[1], :call) ? objectdoc(source, mod, meta, def, x::Expr) :

    # Quoted macrocall syntax. `:@time` / `:(Base.@time)`.
    isquotedmacrocall(x) ? objectdoc(source, mod, meta, nothing, x) :
    # Modules and baremodules.
    isexpr(x, :module) ? moduledoc(source, mod, meta, def, x::Expr) :
    # Document several expressions with the same docstring. `a, b, c`.
    isexpr(x, :tuple) ? multidoc(source, mod, meta, x::Expr, define) :
    # Errors generated by calling `macroexpand` are passed back to the call site.
    isexpr(x, :error) ? esc(x) :
    # When documenting macro-generated code we look for embedded `@__doc__` calls.
    __doc__!(source, mod, meta, x, define) ? esc(x) :
    # Any "basic" expression such as a bare function or module name or numeric literal.
    isbasicdoc(x) ? objectdoc(source, mod, meta, nothing, x) :

    # All other expressions are undocumentable and should be handled on a case-by-case basis
    # with `@__doc__`. Unbound string literals are also undocumentable since they cannot be
    # retrieved from the module's metadata `IdDict` without a reference to the string.
    docerror(x)

    return doc
end
```
-/
def _docm [∀ α, Lean.Order.CCPO (n α)] [Lean.Order.MonoBind n] (source : Value L) (mod : L) (meta_ x : Value L) (define : Bool) : n (Value L) := do
  match x with
  | .expr h args =>
    if h == "hygienic-scope" || h == "escape" then
      let a1 ← liftD (argAt args 1)
      return .expr h (args.set 0 (← _docm source mod meta_ a1 true))
    if h == "block" then
      -- `docarg`: the index of the only argument that is not a `LineNumberNode`, otherwise 0
      let nonLines := (args.zipIdx 1).filterMap fun (a, i) =>
        match a with
        | .lineNumberNode .. => none
        | _ => some i
      let docarg := match nonLines with
        | [i] => i
        | _ => 0
      if docarg != 0 then
        let a ← liftD (argAt args docarg)
        return .expr h (args.set (docarg - 1) (← _docm source mod meta_ a define))
  | _ => pure ()
  let dfn := if define then x else nothingV eo
  let x := match x with
    | .globalRef m name => if eo.lo.egal m mod then .symbol name else x
    | _ => x
  let kw := keywordOf eo x
  if h : kw.isSome then
    return ← keyworddoc eo source mod meta_ x (kw.get h)
  if isexpr_heads x FUNC_HEADS then
    let (_, args) ← liftD (asExpr x)
    if ← liftD (is_signature (← liftD (argAt args 1))) then
      return ← objectdoc eo source mod meta_ dfn x (← liftD (signature x))
  if isexpr x "function" || isexpr x "macro" then
    let (_, args) ← liftD (asExpr x)
    if !isexpr (← liftD (argAt args 1)) "call" then
      return ← objectdoc eo source mod meta_ dfn x
  if ← liftD (iscallexpr x) then
    return ← calldoc eo source mod meta_ x
  if isexpr_heads x ["struct", "abstract", "primitive"] then
    return ← objectdoc eo source mod meta_ dfn x
  if isexpr_heads x BINDING_HEADS then
    let (_, args) ← liftD (asExpr x)
    if !isexpr (← liftD (argAt args 1)) "call" then
      return ← objectdoc eo source mod meta_ dfn x
  if ← liftD (isquotedmacrocall x) then
    return ← objectdoc eo source mod meta_ (nothingV eo) x
  if isexpr x "module" then
    return ← moduledoc eo source mod meta_ dfn x
  if isexpr x "tuple" then
    return ← multidoc source mod meta_ x define
  if isexpr x "error" then
    return JuliaLean.base.expr.esc x
  let (found, x) ← __doc__! eo source mod meta_ x define
  if found then
    return JuliaLean.base.expr.esc x
  if isbasicdoc x then
    return ← objectdoc eo source mod meta_ (nothingV eo) x
  docerror eo x
partial_fixpoint
end

-- Reason: The docstring of `Core.@__doc__`, attached to the expression `:(Core.@__doc__)`: no method.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:485-548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @__doc__(ex)
-- 
-- Low-level macro used to mark expressions returned by a macro that should be documented. If
-- more than one expression is marked then the same docstring is applied to each expression.
-- 
--     macro example(f)
--         quote
--             \$(f)() = 0
--             @__doc__ \$(f)(x) = 1
--             \$(f)(x, y) = 2
--         end |> esc
--     end
-- 
-- `@__doc__` has no effect when a macro that uses it is not documented.
-- 
-- !!! compat "Julia 1.12"
-- 
--     This section documents a very subtle corner case that is only relevant to
--     macros which themselves both define other macros and then attempt to use them
--     within the same expansion. Such macros were impossible to write prior to
--     Julia 1.12 and are still quite rare. If you are not writing such a macro,
--     you may ignore this note.
-- 
--     In versions prior to Julia 1.12, macroexpansion would recursively expand through
--     `Expr(:toplevel)` blocks. This behavior was changed in Julia 1.12 to allow
--     macros to recursively define other macros and use them in the same returned
--     expression. However, to preserve backwards compatibility with existing uses of
--     `@__doc__`, the doc system will still expand through `Expr(:toplevel)` blocks
--     when looking for `@__doc__` markers. As a result, macro-defining-macros will
--     have an observable behavior difference when annotated with a docstring:
-- 
--     ```julia
--     julia> macro macroception()
--         Expr(:toplevel, :(macro foo() 1 end), :(@foo))
--     end
-- 
--     julia> @macroception
--     1
-- 
--     julia> "Docstring" @macroception
--     ERROR: LoadError: UndefVarError: `@foo` not defined in `Main`
--     ```
-- 
--     The supported workaround is to manually expand the `@__doc__` macro in the
--     defining macro, which the docsystem will recognize and suppress the recursive
--     expansion:
-- 
--     ```julia
--     julia> macro macroception()
--         Expr(:toplevel,
--             macroexpand(__module__, :(@__doc__ macro foo() 1 end); recursive=false),
--             :(@foo))
--     end
-- 
--     julia> @macroception
--     1
-- 
--     julia> "Docstring" @macroception
--     1
--     ```
-- """
-- :(Core.@__doc__)
-- 
-- /Source

-- Reason: A comment.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:603-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Predicates and helpers for `docm` expression selection:
-- 
-- /Source

-- Reason: `include("utils.jl")`: the included file is modelled on its own.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:803-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include("utils.jl")
-- 
-- /Source

-- Reason: A load-time call `Core.atdoc!(docm)` that installs `docm` as the `@doc` macro: no method.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:805-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Swap out the bootstrap macro with the real one.
-- Core.atdoc!(docm)
-- 
-- /Source

-- Reason: A comment.
-- UNTRANSLATED
-- Source: base/docs/Docs.jl:821-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # FIXME: formatdoc, parsedoc, apropos, and doc are defined here (but only doc is exported)
-- # for historical reasons (#25738), but are *implemented* in REPL/src/docview.jl, while
-- # apropos is *exported* by InteractiveUtils and doc is exported by Docs.  Seems
-- # like a more sensible refactoring should be possible.
-- 
-- /Source

end expand
/-- The callees of `loaddocs` beyond the docsystem and the expansion. -/
structure LoaddocsOps (m : Type → Type) (L D X O S A : Type) where
  /-- `isdefined(docs, :doc)`; when defined, `(mod, ex, str, file, line) = docs.doc` (with the
  method `docstr` selects for `str`) and `docs.next`. -/
  entry : D → m (Option (L × Value L × DocInput X O S × Value L × JInt64 × D))
  /-- `string(file)`. -/
  fileString : Value L → m String
  /-- The `Any` values `string(file)` and `line` stored in a docstring's `data`. -/
  dataString : String → A
  dataLine : JInt64 → A
  /-- The `DocStr` object of a docsystem reference, as a value. -/
  docStrObject : Nat → L
  /-- `Core.eval(mod, ex)`. -/
  coreEval : L → Value L → m Unit

section runtime4
variable {m : Type → Type} [Monad m] [MonadExceptOf DocError m] {Mod B Ty X O A Obj R S : Type}
variable [MonadStateOf (World Mod B Ty X O A) m]
variable [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]

/--
Julia source: base/docs/Docs.jl:808-820 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function loaddocs(docs::Base.CoreDocs.DocLinkedList)
    while isdefined(docs, :doc)
        (mod, ex, str, file, line) = docs.doc
        data = Dict{Symbol,Any}(:path => string(file), :linenumber => line)
        doc = docstr(str, data)
        lno = LineNumberNode(line, file)
        docstring = docm(lno, mod, doc, ex, false) # expand the real @doc macro now
        Core.eval(mod, Expr(:var"hygienic-scope", docstring, Docs, lno))
        docs = docs.next
    end
    nothing
end

```
-/
def loaddocs [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {L D : Type} (o : DocsOps m Mod B Ty X O A Obj R S) (eo : ExpandOps m L)
    (lo : LoaddocsOps m L D X O S A) (docs : D) : m Unit := do
  match ← lo.entry docs with
  | none => pure ()
  | some (mod, ex, str, file, line, next) =>
    let data := [("path", lo.dataString (← lo.fileString file)), ("linenumber", lo.dataLine line)]
    let doc ← docstr o str data
    let lno : Value L := .lineNumberNode line file
    let docstring ← docm_meta eo lno mod (.leaf (lo.docStrObject doc)) ex false
    lo.coreEval mod (.expr "hygienic-scope" [docstring, objV eo "Docs", lno])
    loaddocs o eo lo next
partial_fixpoint

end runtime4


end JuliaLean.base.docs.Docs
