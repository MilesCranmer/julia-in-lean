import JuliaLean.DocsSyntaxCov.DocsCore

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
