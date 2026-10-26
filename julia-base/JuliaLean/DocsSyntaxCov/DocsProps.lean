import JuliaLean.DocsSyntaxCov.Docs

/-!
# Properties of `base/docs/Docs.jl`
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## Refuted: field docstrings and method signatures -/

/-- The field a statement of a struct body declares: `x`, `x::T`, `const x::T` or an atomic
field. -/
def declaredField : JV → Option String
  | .sym s => some s
  | .expr "::" (.sym s :: _) => some s
  | .expr "const" [x] => declaredField x
  | .expr "atomic" [x] => declaredField x
  | _ => none

/-- Every field docstring `metadata` records documents the field declared right after it in
the struct body (the manual's field-docstring syntax). -/
def FieldDocsAttach : Prop :=
  ∀ (body : List JV) (fs : List (String × JV)), fieldDocs none body = .ok fs →
    ∀ f d, (f, d) ∈ fs → ∃ i, i < body.length ∧ (body[i]? == some d) = true ∧
      (body[i + 1]?.bind declaredField) = some f

/-- `"doc for a"; const a::Int; b::Int`. -/
def constBody : List JV :=
  [.str "doc for a", .expr "const" [.expr "::" [.sym "a", .sym "Int"]], .expr "::" [.sym "b", .sym "Int"]]

theorem constBody_fields : fieldDocs none constBody = .ok [("b", .str "doc for a")] := by rfl

theorem fieldDocsAttach_refuted : ¬ FieldDocsAttach := by
  intro h
  have := h constBody _ constBody_fields "b" (.str "doc for a") (by simp)
  revert this
  decide +kernel

/-- Fields declared as `x` or `x::T` get the docstring right before them. -/
def FieldDocsPlain : Prop :=
  ∀ (d : String) (x : String) (T : JV),
    fieldDocs none [.str d, .expr "::" [.sym x, T]] = .ok [(x, .str d)] ∧
    fieldDocs none [.str d, .sym x] = .ok [(x, .str d)] ∧
    fieldDocs none [.sym x] = .ok [] ∧
    fieldDocs none [.str d, .expr "function" [], .sym x] = .ok []

theorem fieldDocsPlain : FieldDocsPlain := by
  intro d x T
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- The stored signature of a one-argument method `f(x::U) where T` is `Union{Tuple{U}} where T`:
one tuple per accepted argument count, as the `MultiDoc` docstring describes. -/
def DocSignatureTypevar : Prop :=
  ∀ (f x T : String) (U : JV),
    signature (.expr "where" [call (.sym f) [.expr "::" [.sym x, U]], .sym T]) =
      .ok (wrapWhere (curly "Union" [curly "Tuple" [U]]) [.expr "<:" [.sym T, .sym "Any"]])

def vectorT : JV := curly "Vector" [.sym "T"]

theorem sig_vectorT :
    signature (.expr "where" [call (.sym "g") [.expr "::" [.sym "x", vectorT]], .sym "T"]) =
      .ok (wrapWhere (curly "Union" [curly "Tuple" [vectorT], curly "Tuple" [.sym "T"]])
        [.expr "<:" [.sym "T", .sym "Any"]]) := by
  rfl

theorem docSignatureTypevar_refuted : ¬ DocSignatureTypevar := by
  intro h
  have h2 := h "g" "x" "T" vectorT
  rw [sig_vectorT] at h2
  have := congrArg (fun r => match r with | .ok v => JV.size v | .error _ => 0) h2
  revert this
  decide +kernel

/-- Positional arguments without a `where` clause: `f(x)`, `f(x::T)`, `f(x...)` and an optional
argument `f(x, y=v)`, which stores one tuple per argument count. -/
def SignatureForms : Prop :=
  ∀ (f x y : String) (T v : JV),
    signature (call (.sym f) [.sym x]) = .ok (curly "Union" [curly "Tuple" [.sym "Any"]]) ∧
    signature (call (.sym f) [.expr "::" [.sym x, T]]) = .ok (curly "Union" [curly "Tuple" [T]]) ∧
    signature (call (.sym f) [.expr "..." [.sym x]]) =
      .ok (curly "Union" [curly "Tuple" [curly "Vararg" [.sym "Any"]]]) ∧
    signature (call (.sym f) [.sym x, .expr "kw" [.sym y, v]]) =
      .ok (curly "Union" [curly "Tuple" [.sym "Any"], curly "Tuple" [.sym "Any", .sym "Any"]]) ∧
    signature (call (.sym f) [.sym x, .expr "parameters" [.sym y]]) =
      .ok (curly "Union" [curly "Tuple" [.sym "Any"]]) ∧
    signature (.expr "macrocall" [.sym f, .lnn 0 "", .sym x]) = .ok (curly "Union" [curly "Tuple" [.sym "Any"]]) ∧
    signature (.expr "function" [call (.sym f) [], .expr "block" []]) = .ok (curly "Union" [curly "Tuple" []]) ∧
    signature (.sym f) = .ok (curly "Union" []) ∧
    tvar (.sym x) = .ok (.expr "<:" [.sym x, .sym "Any"]) ∧
    argtype (.expr "::" [.sym x, T]) = .ok T ∧
    argtype (.expr "meta" [.sym "nospecialize", .expr "::" [.sym x, T]]) = .ok T ∧
    argtype (.int 1) = .ok (.sym "Any")

theorem signatureForms : SignatureForms := by
  intro f x y T v
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-! ## State and docstrings -/

/-- `meta(m)` creates (and registers) an empty dictionary for a module without one, `meta(m;
autoinit=false)` returns `nothing` then, and both return an existing dictionary unchanged;
`initmeta` is the same as `meta` with `autoinit`. -/
def MetaForms : Prop :=
  ∀ (st : DocsState) (m : String),
    (assocGet st.metas m = none →
      metaDict st m true = (⟨st.modules ++ [m], st.metas ++ [(m, [])]⟩, some []) ∧
      metaDict st m false = (st, none) ∧
      initmeta st m = (⟨st.modules ++ [m], st.metas ++ [(m, [])]⟩, [])) ∧
    (∀ d, assocGet st.metas m = some d → metaDict st m true = (st, some d) ∧ metaDict st m false = (st, some d) ∧
      initmeta st m = (st, d))

theorem metaForms : MetaForms := by
  intro st m
  refine ⟨fun h => ⟨by simp [metaDict, h], by simp [metaDict, h], by simp [initmeta, h]⟩,
    fun d h => ⟨by simp [metaDict, h], by simp [metaDict, h], by simp [initmeta, h]⟩⟩

/-- `docstr`/`_docstr` keep a `SimpleVector` as the text, wrap a string, store any other object
as `object`, and merge the metadata of an existing `DocStr` (its own entries win); `docexpr`
is the call `docstr(args...)`; `MultiDoc()` is empty. -/
def DocstrForms : Prop :=
  (∀ parts data, docstrObj (.svec parts) data = ⟨parts, none, data⟩) ∧
  (∀ s data, docstrObj (.str s) data = ⟨[.str s], none, data⟩) ∧
  (∀ v data, docstrObj (.other v) data = ⟨[], some v, data⟩) ∧
  (∀ d data, (docstrObj (.docstr d) data).text = d.text ∧ (docstrObj (.docstr d) data).object = d.object ∧
    (docstrObj (.docstr d) data).data = mergeData data d.data) ∧
  (∀ args, docexpr args = call docstrFn args) ∧
  MultiDoc.new.order = [] ∧ MultiDoc.new.docs.length = 0

theorem docstrForms : DocstrForms :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, rfl, rfl⟩

/-- After `doc!(mod, b, str, sig)`, the dictionary of the documented module maps `b` to a
`MultiDoc` whose docs for `sig` are `str` (with `:binding` and `:typesig` recorded); a new
signature is appended to `order`, a replaced one keeps its place and warns outside the
active module; `doc!` returns `b`. -/
def DocRegisterStores : Prop :=
  ∀ (st : DocsState) (active mod : String) (rm : Option String) (b : Binding) (str : DocStr) (sig : JV),
    let (st', warn, r) := docRegister st active mod rm b str sig
    let m := rm.getD mod
    let old := ((assocGet (initmeta st m).2 b).getD MultiDoc.new)
    r = b ∧
    (assocGet old.docs sig = none → warn = false ∧
      (assocGet st'.metas m).bind (fun d => (assocGet d b).map (·.order)) = some (old.order ++ [sig])) ∧
    (∀ d, assocGet old.docs sig = some d → warn = (m != active) ∧
      (assocGet st'.metas m).bind (fun d => (assocGet d b).map (·.order)) = some old.order)

theorem assocGet_map_set {κ α : Type} [BEq κ] [LawfulBEq κ] (k : κ) (v : α) :
    ∀ d : List (κ × α), assocGet (d.map (fun p => if p.1 == k then (k, v) else p)) k =
      if d.any (·.1 == k) then some v else none
  | [] => rfl
  | p :: ps => by
    by_cases hp : p.1 = k
    · simp [assocGet, hp]
    · have ih := assocGet_map_set k v ps
      have hb : (p.1 == k) = false := by simpa using hp
      simp only [assocGet, List.map_cons, hb, List.find?_cons, List.any_cons, Bool.false_or, Bool.false_eq_true,
        ↓reduceIte] at ih ⊢
      exact ih

theorem assocGet_append_new {κ α : Type} [BEq κ] [LawfulBEq κ] (k : κ) (v : α) :
    ∀ d : List (κ × α), d.any (·.1 == k) = false → assocGet (d ++ [(k, v)]) k = some v
  | [], _ => by simp [assocGet]
  | p :: ps, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have ih := assocGet_append_new k v ps h.2
    simp only [assocGet, List.cons_append, List.find?_cons, h.1] at ih ⊢
    exact ih

theorem assocGet_assocSet {κ α : Type} [BEq κ] [LawfulBEq κ] (d : List (κ × α)) (k : κ) (v : α) :
    assocGet (assocSet d k v) k = some v := by
  unfold assocSet
  split
  · rename_i h
    rw [assocGet_map_set, if_pos h]
  · rename_i h
    exact assocGet_append_new k v d (by revert h; cases d.any (·.1 == k) <;> simp)

theorem docRegisterStores : DocRegisterStores := by
  intro st active mod rm b str sig
  simp only [docRegister]
  refine ⟨by trivial, fun h => ?_, fun d h => ?_⟩
  · simp only [h, Option.isSome_none, Bool.false_and, true_and]
    simp [assocGet_assocSet]
  · simp only [h, Option.isSome_some, Bool.true_and, if_true]
    simp [assocGet_assocSet]

/-! ## Names -/

/-- `namify` extracts the documented name: a symbol itself, `f` from `f(args...)`, a function
or `=` definition, `where` and `::` forms, `S` from `struct S`, `@m` from `macro m(...)`, the
value of a `QuoteNode`, and leaves dotted names alone. -/
def NamifyForms : Prop :=
  ∀ (f : String) (args : List JV) (body T : JV) (isMut : Bool),
    namify (.sym f) = .ok (.sym f) ∧
    namify (call (.sym f) args) = .ok (.sym f) ∧
    namify (.expr "function" [call (.sym f) args, body]) = .ok (.sym f) ∧
    namify (.expr "=" [call (.sym f) args, body]) = .ok (.sym f) ∧
    namify (.expr "where" [call (.sym f) args, T]) = .ok (.sym f) ∧
    namify (.expr "struct" [.bool isMut, .sym f, body]) = .ok (.sym f) ∧
    namify (.expr "macro" [call (.sym f) args, body]) = .ok (.sym ("@" ++ f)) ∧
    namify (.qn (.sym f)) = .ok (.sym f) ∧
    namify (.expr "." [.sym f, .qn (.sym f)]) = .ok (.expr "." [.sym f, .qn (.sym f)]) ∧
    namify (.int 1) = .ok (.int 1) ∧
    macroname (.sym f) = .ok (.sym ("@" ++ f)) ∧
    macroname (.expr "." [.sym f, .qn (.sym f)]) = .ok (.expr "." [.sym f, .sym ("@" ++ f)])

theorem astnameF_sym (m : Bool) (n : Nat) (s : String) (h : n ≠ 0) :
    astnameF m n (.sym s) = if m then macroname (.sym s) else pure (.sym s) := by
  cases n with
  | zero => exact absurd rfl h
  | succ n => rfl

theorem astnameF_callSym (m : Bool) (n : Nat) (f : String) (args : List JV) (h : 2 ≤ n) :
    astnameF m n (call (.sym f) args) = if m then macroname (.sym f) else pure (.sym f) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  cases m <;> rfl

theorem astnameF_wrap (m : Bool) (n : Nat) (hd f : String) (args : List JV) (x : JV)
    (hh : hd = "function" ∨ hd = "=" ∨ hd = "where" ∨ hd = "macro") (h : 3 ≤ n) :
    astnameF m n (.expr hd [call (.sym f) args, x]) = if m then macroname (.sym f) else pure (.sym f) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rcases hh with rfl | rfl | rfl | rfl <;> cases m <;> rfl

theorem astnameF_struct (m : Bool) (n : Nat) (b : Bool) (f : String) (x : JV) (h : 2 ≤ n) :
    astnameF m n (.expr "struct" [.bool b, .sym f, x]) = if m then macroname (.sym f) else pure (.sym f) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  cases m <;> rfl

theorem astnameF_eqSym (m : Bool) (n : Nat) (f : String) (rhs : JV) (h : 2 ≤ n) :
    astnameF m n (.expr "=" [.sym f, rhs]) = if m then macroname (.sym f) else pure (.sym f) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  cases m <;> rfl

theorem namifyForms : NamifyForms := by
  intro f args body T isMut
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [namify, astname]
    rw [astnameF_callSym]
    · rfl
    · simp [call, JV.size, JV.size.sizeList] <;> omega
  · simp only [namify, astname]
    rw [astnameF_wrap]
    · rfl
    · decide
    · simp [call, JV.size, JV.size.sizeList] <;> omega
  · simp only [namify, astname]
    rw [astnameF_wrap]
    · rfl
    · decide
    · simp [call, JV.size, JV.size.sizeList] <;> omega
  · simp only [namify, astname]
    rw [astnameF_wrap]
    · rfl
    · decide
    · simp [call, JV.size, JV.size.sizeList] <;> omega
  · simp only [namify, astname]
    rw [astnameF_struct]
    · rfl
    · simp [JV.size, JV.size.sizeList] <;> omega
  · simp only [namify, astname]
    rw [astnameF_wrap]
    · rfl
    · decide
    · simp [call, JV.size, JV.size.sizeList] <;> omega

/-- `isfield` recognises `a.b` and `a.b.c` field accesses (symbol or field on the left, quoted
name on the right). -/
def IsfieldForms : Prop :=
  ∀ (a b c : String),
    isfield (.expr "." [.sym a, .qn (.sym b)]) = true ∧
    isfield (.expr "." [.expr "." [.sym a, .qn (.sym b)], .qn (.sym c)]) = true ∧
    isfield (.expr "." [.sym a, .expr "tuple" [.sym b]]) = false ∧
    isfield (.sym a) = false

theorem isfieldForms : IsfieldForms := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-! ## Expression builders -/

/-- `metadata` records the source file (or `""` when the file is not a `Symbol`), the line, the
documenting module (or the module expression of a module docstring), and the field docs of a
`struct`. -/
def MetadataForms : Prop :=
  ∀ (file : Option String) (line : Int) (mod : String) (expr : JV) (ismod : Bool),
    expr.isExpr "struct" = false →
    metadata file line mod expr ismod =
      .ok ⟨file.getD "", line, if ismod then expr else .val mod, ismod, none⟩

theorem metadataForms : MetadataForms := by
  intro file line mod expr ismod h
  simp [metadata, h]

/-- The builders: `keyworddoc` stores into `Docs.keywords`; `objectdoc` without a definition is
just the `doc!` call, and with one evaluates it first, keeping its value (`nothing` for a
`global x` declaration); `callargs` lists the arguments of a (`where`-wrapped) call;
`validcall` accepts symbols, `::`, `...`, `kw` and `parameters`; `calldoc` documents a call
signature or reports `docerror`. -/
def BuilderForms : Prop :=
  (∀ (src : Src) (str : JV) (name : String), ∃ ds,
    keyworddoc src str name = .ok (.expr "block" [call (.val "setindex!") [keywordsDict, ds, esc (quot (.sym name))], .nothing])) ∧
  (∀ (src : Src) (str : JV) (f : String), ∃ docex,
    objectdoc src str .nothing (.sym f) = .ok (.expr "block" [docex])) ∧
  (∀ (src : Src) (str : JV) (f : String) (rhs : JV), ∃ docex,
    objectdoc src str (.expr "=" [.sym f, rhs]) (.expr "=" [.sym f, rhs]) =
      .ok (.expr "block" [.expr "if" [.bool true, .expr "=" [.sym "val", esc (.expr "=" [.sym f, rhs])]], docex,
        .expr "if" [.bool true, .sym "val"]])) ∧
  (∀ (src : Src) (str : JV) (f : String), ∃ docex,
    objectdoc src str (.expr "global" [.sym f]) (.expr "global" [.sym f]) =
      .ok (.expr "block" [esc (.expr "global" [.sym f]), docex, .expr "if" [.bool true, .nothing]])) ∧
  (∀ f args T, callargs (.expr "where" [call f args, T]) = .ok args) ∧
  (∀ f args, callargs (call f args) = .ok args) ∧
  (∀ s, ∃ m, callargs (.sym s) = .error (.errorException m)) ∧
  (∀ s, validcall (.sym s) = true) ∧
  (∀ h args, h ∈ ["::", "...", "kw", "parameters"] → validcall (.expr h args) = true) ∧
  (∀ n, validcall (.int n) = false) ∧
  (∀ (src : Src) (str : JV) (f : String), calldoc src str (call (.sym f) [.int 1]) =
    .ok (docerror (call (.sym f) [.int 1])))

theorem builderForms : BuilderForms := by
  refine ⟨fun src str name => ⟨_, rfl⟩, fun src str f => ⟨_, rfl⟩, fun src str f rhs => ?_,
    fun src str f => ⟨_, rfl⟩, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => ⟨_, rfl⟩, fun _ => rfl,
    fun h args hh => ?_, fun _ => rfl, fun _ _ _ => rfl⟩
  · simp only [objectdoc, namify, astname]
    rw [astnameF_eqSym]
    · exact ⟨_, rfl⟩
    · simp [JV.size, JV.size.sizeList] <;> omega
  · simp at hh
    rcases hh with rfl | rfl | rfl | rfl <;> rfl

/-- `docerror(ex)` builds a call of `error` naming the expression, with a hint for macro calls. -/
def DocerrorForm : Prop :=
  ∀ ex : JV, ∃ note, docerror ex =
    call (.val "error") [.expr "string" [.str "cannot document the following expression:", ex, .str note], .str "\n"] ∧
    (ex.isExpr "macrocall" = false → note = "")

theorem docerrorForm : DocerrorForm := fun ex => ⟨_, rfl, fun h => by simp [h]⟩

/-! ## `@__doc__` -/

/-- `finddoc` reports an `@__doc__` marker (the block `Expr(:meta, :doc); ex`) and applies `λ`
to it; non-expressions contain none; `__doc__!` with `define` turns each marker into an
`@doc` macro call. -/
def FinddocForms : Prop :=
  ∀ (mx : String → JV → JV) (mod : String) (lam : JV → JV) (et : Bool) (n : Nat) (ex : JV),
    let marker := JV.expr "block" [.expr "meta" [.sym "doc"], ex]
    finddoc mx mod lam et (n + 1) marker = (true, lam marker, [marker]) ∧
    (∀ s, finddoc mx mod lam et (n + 1) (.sym s) = (false, .sym s, [])) ∧
    finddoc mx mod lam false (n + 2) (.expr "toplevel" [marker]) = (true, .expr "toplevel" [lam marker], [marker]) ∧
    ∀ (source meta_ : JV) (define : Bool),
      replaceMetaDoc source mod meta_ define marker =
        .expr "macrocall" [.sym "@doc", source, .val mod, .nothing, meta_, ex, .bool define] ∧
      docBang mx (n + 2) source mod meta_ (.expr "toplevel" [marker]) true =
        (true, .expr "toplevel" [replaceMetaDoc source mod meta_ true marker])

theorem finddocForms : FinddocForms := by
  intro mx mod lam et n ex
  refine ⟨rfl, fun _ => rfl, rfl, fun source meta_ define => ⟨rfl, rfl⟩⟩

/-- Predicates of `docm`: quoted macro calls `:@m`, basic documentable atoms, call signatures
(also under `::` and `where`), and `iscallexpr` through `where` layers. -/
def DocmPredicates : Prop :=
  (∀ m l, isquotedmacrocall (.expr "copyast" [.qn (.expr "macrocall" [m, l])]) = true) ∧
  (∀ s, isbasicdoc (.sym s) = true ∧ isbasicdoc (.qn (.sym s)) = true) ∧
  (∀ a b, isbasicdoc (.expr "." [a, b]) = true) ∧
  (∀ n, isbasicdoc (.int n) = false) ∧
  (∀ f args, isSignature (call f args) = true ∧ iscallexpr (call f args) = true) ∧
  (∀ f args T, isSignature (.expr "::" [call f args, T]) = true) ∧
  (∀ f args T U, iscallexpr (.expr "where" [.expr "where" [call f args, T], U]) = true) ∧
  (∀ s, iscallexpr (.sym s) = false)

theorem docmPredicates : DocmPredicates :=
  ⟨fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩

/-! ## Lookup -/

/-- `_doc(binding, sig)` returns a user `getdoc` result for a defined binding first; otherwise the
docstring of the first signature in definition order that `sig` is a subtype of; `getdoc`
without user methods is `nothing`; `catdoc()` is `nothing` and `catdoc(xs...)` concatenates. -/
def DocLookupForms : Prop :=
  ∀ (env : ModEnv) (st : DocsState) (subtype : JV → JV → Bool) (b : Binding) (sig : JV),
    (∀ user d, defined env b = true → user (env.value b.mod b.var) = some d →
      docBinding env st user subtype b sig = some d) ∧
    (docBinding env st (fun _ => none) subtype b sig = docLookupModules st subtype b sig) ∧
    (∀ x, getdoc (fun _ => none) x = none) ∧
    catdoc ([] : List (List Nat)) = none ∧
    (∀ (x : List Nat) xs, catdoc (x :: xs) = some (x ++ xs.flatten))

theorem docLookupForms : DocLookupForms := by
  intro env st subtype b sig
  refine ⟨fun user d hd hu => by simp [docBinding, hd, getdoc, hu], ?_, fun _ => rfl, rfl, fun _ _ => rfl⟩
  simp [docBinding, getdoc]

/-- `_doc` of an object looks up the binding of its own name (through `UnionAll`s), and
`_doc(object, sig...)` uses the tuple of the signatures. -/
def DocTargetForms : Prop :=
  ∀ (env : ModEnv) (fuel : Nat) (t : DocTarget) (sigs : List JV),
    docTargetBinding env fuel (.unionAll t) = docTargetBinding env fuel t ∧
    (∀ p n, docTargetBinding env fuel (.dataType p n) = mkBinding env fuel p n) ∧
    (∀ m, docTargetBinding env fuel (.module m) = mkBinding env fuel m (env.nameof m)) ∧
    tupleSig sigs = curly "Tuple" sigs

theorem docTargetForms : DocTargetForms := fun _ _ _ _ => ⟨rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

/-- `@doc x` with one argument: a keyword returns its docstring; a value that is no symbol or
expression looks up the docs of its type; a plain name looks up its binding. -/
def SimpleLookupForms : Prop :=
  ∀ (isop : String → Bool) (kws : List (String × DocStr)) (s : String),
    (∀ d, assocGet kws s = some d → simpleLookupDoc isop kws (.sym s) = .ok (.inl d)) ∧
    (assocGet kws s = none → simpleLookupDoc isop kws (.sym s) =
      .ok (.inr (call docFnObj [esc (.expr "call" [bindingFn, atModuleExpr, quot (.sym s)])]))) ∧
    (∀ n, simpleLookupDoc isop kws (.int n) = .ok (.inr (call docFnObj [call (.val "typeof") [esc (.int n)]])))

theorem simpleLookupForms : SimpleLookupForms := by
  intro isop kws s
  refine ⟨fun d h => by simp [simpleLookupDoc, h], fun h => ?_, fun _ => rfl⟩
  simp [simpleLookupDoc, h, namify, astname, astnameF, JV.size, JV.isExpr, bindingexpr, splitexpr]

/-- `@doc` dispatch (`_docm` after `macroexpand`): a keyword becomes a `keyworddoc`, a
`function` definition with a call signature an `objectdoc` with that signature, a tuple a
`multidoc` of its elements, a `:error` from `macroexpand` is passed through escaped, and
`-> (meta, x)` documents `x` with `meta`. -/
def DocmDispatch : Prop :=
  ∀ (env : DocmEnv) (src : Src) (source meta_ : JV) (n : Nat),
    (∀ name, docmInner env src source (n + 1) meta_ (.keyword name) true = keyworddoc src meta_ name) ∧
    (∀ f args body, docmInner env src source (n + 1) meta_ (.expr "function" [call (.sym f) args, body]) true =
      (signature (.expr "function" [call (.sym f) args, body]) >>= fun sig =>
        objectdoc src meta_ (.expr "function" [call (.sym f) args, body]) (.expr "function" [call (.sym f) args, body])
          sig)) ∧
    (∀ args, docmInner env src source (n + 1) meta_ (.expr "error" args) true = .ok (esc (.expr "error" args))) ∧
    (∀ ex, docm env src source (n + 1) meta_ ex true = docmInner env src source n meta_ (env.macroexpand src.mod ex) true)

theorem docmDispatch : DocmDispatch := by
  intro env src source meta_ n
  refine ⟨fun name => ?_, fun f args body => ?_, fun args => ?_, fun ex => rfl⟩
  · first | rfl | simp [docmInner, JV.isExpr]
  · first | rfl | simp [docmInner, JV.isExpr, JV.isExprIn, FUNC_HEADS, isSignature, JV.arg, JV.arg?, JV.args, call]
  · first | rfl | simp [docmInner, JV.isExpr, JV.isExprIn, FUNC_HEADS, BINDING_HEADS, isSignature, iscallexpr, isquotedmacrocall,
      JV.isExprN, JV.arg, JV.arg?, JV.args]

/-- `loaddocs` replays the bootstrap records from the head of `DOCS` (the most recent) to the
tail, in that order, each in its own module. -/
def LoaddocsOrder : Prop :=
  ∀ (env : DocmEnv) (fuel : Nat) (docs : List DocRec),
    (loaddocs env fuel (docs.foldr .cons .empty)).map (·.1) = docs.map (·.mod)

theorem loaddocsOrder : LoaddocsOrder := by
  intro env fuel docs
  induction docs with
  | nil => rfl
  | cons d ds ih => simp [loaddocs, ih]

/-- `undocumented_names` returns exactly the listed names without docs that do not start with
`#` and are public (or all of them with `private=true`). -/
def UndocumentedNamesSpec : Prop :=
  ∀ (env : ModEnv) (st : DocsState) (user : JV → Option DocStr) (kind : JV → ValKind) (fuel : Nat)
    (mod : String) (names : List String) (ispublic : String → Bool) (priv : Bool) (sym : String),
    sym ∈ undocumentedNames env st user kind fuel mod names ispublic priv ↔
      sym ∈ names ∧ hasdoc env st user kind fuel mod sym = false ∧ ¬ sym.startsWith "#" = true ∧
        (priv = true ∨ ispublic sym = true)

theorem undocumentedNamesSpec : UndocumentedNamesSpec := by
  intro env st user kind fuel mod names ispublic priv sym
  simp [undocumentedNames, and_assoc]

/-- `hasdoc` is `true` for a binding listed in some module's `META`, and follows aliases;
`@ref x` builds the `docstr(binding, signature)` call. -/
def HasdocForms : Prop :=
  ∀ (env : ModEnv) (st : DocsState) (user : JV → Option DocStr) (kind : JV → ValKind) (bf n : Nat) (b : Binding),
    (∀ m d md, m ∈ st.modules → assocGet st.metas m = some d → assocGet d b = some md →
      hasdocB env st user kind bf (n + 1) b = true) ∧
    hasdocB env st user kind bf 0 b = false

theorem hasdocForms : HasdocForms := by
  intro env st user kind bf n b
  refine ⟨fun m d md hm hd hb => ?_, rfl⟩
  unfold hasdocB
  by_cases h1 : (defined env b && (getdoc user (env.value b.mod b.var)).isSome) = true
  · rw [if_pos h1]
  · rw [if_neg h1, if_pos]
    rw [List.any_eq_true]
    exact ⟨m, hm, by simp [metaDict, hd, hb]⟩

end JuliaLean.DocsSyntaxCov
