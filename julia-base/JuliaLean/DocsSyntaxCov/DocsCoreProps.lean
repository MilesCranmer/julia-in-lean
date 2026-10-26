import JuliaLean.DocsSyntaxCov.DocsCore

/-!
# Properties of `base/docs/core.jl`, `utils.jl`, `bindings.jl` and `basedocs.jl`
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `Core.CoreDocs` -/

/-- `DocLinkedList()` has no record; `DocLinkedList(doc, next)` holds `doc` before `next`;
`CoreDocs.doc!` puts the new record `(mod, ex, str, file, line)` in front of `DOCS` and
returns `nothing`. -/
def CoreDocsRecords : Prop :=
  docLinkedList0.hasDoc = false ∧
  (∀ d n, docLinkedList2 d n = .cons d n ∧ (docLinkedList2 d n).hasDoc = true) ∧
  ∀ (docs : DocLinkedList) (line : Int) (file mod : String) (str ex : JV),
    coreDocBang docs line file mod str ex = (.cons ⟨mod, ex, str, file, line⟩ docs, .nothing)

theorem coreDocsRecords : CoreDocsRecords := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ _ _ => rfl⟩

/-- `isexpr(x, h)` holds exactly for an `Expr` with head `h`; `lazy_iterpolate` turns a string
literal or a `:string` interpolation into a `Core.svec` call of its parts and leaves other
values alone. -/
def CoreExprHelpers : Prop :=
  (∀ h args h', coreIsexpr (.expr h args) h' = (h == h')) ∧
  (∀ x h', (∀ h args, x ≠ .expr h args) → coreIsexpr x h' = false) ∧
  (∀ s, lazyIterpolate (.str s) = .expr "call" [svecFn, .str s]) ∧
  (∀ args, lazyIterpolate (.expr "string" args) = .expr "call" (svecFn :: args)) ∧
  (∀ x, (∀ s, x ≠ .str s) → coreIsexpr x "string" = false → lazyIterpolate x = x)

theorem coreExprHelpers : CoreExprHelpers := by
  refine ⟨fun _ _ _ => rfl, fun x h' hx => ?_, fun _ => rfl, fun _ => rfl, fun x hs hx => ?_⟩
  · cases x <;> simp [coreIsexpr] <;> exact (hx _ _ rfl).elim
  · cases x <;> simp_all [lazyIterpolate]

/-- The bootstrap `@doc` expansion stores the docstring with `CoreDocs.doc!` and evaluates
the documented expression: after it for most forms, around it for a `module` (`:toplevel`),
and not at all for a bare call signature. `@doc` with one argument requires `str -> ex`. -/
def CoreDocmExpansion : Prop :=
  ∀ (source : JV) (mod : String) (str x : JV),
    let out := JV.expr "call" [coreDocFn, .qn source, .val mod, lazyIterpolate str, .qn x]
    (coreIsexpr x "module" = true → coreDocm4 source mod str x = .expr "escape" [.expr "toplevel" [out, x]]) ∧
    (coreIsexpr x "call" = true → coreDocm4 source mod str x = .expr "escape" [out]) ∧
    (coreIsexpr x "module" = false → coreIsexpr x "call" = false →
      coreDocm4 source mod str x = .expr "escape" [.expr "block" [x, out]]) ∧
    (∀ l rest, coreDocm3 source mod (.expr "->" [str, .expr "block" (l :: x :: rest)]) =
      .ok (coreDocm4 source mod str x)) ∧
    (∀ (y : JV), (∀ a b rest, y ≠ .expr "->" (a :: b :: rest)) →
      coreDocm3 source mod y = .error (.errorException "invalid '@doc'."))

theorem coreDocmExpansion : CoreDocmExpansion := by
  intro source mod str x
  refine ⟨fun h => by simp [coreDocm4, h], fun h => ?_, fun h1 h2 => by simp [coreDocm4, h1, h2], fun _ _ => rfl, ?_⟩
  · have : coreIsexpr x "module" = false := by
      cases x <;> simp_all [coreIsexpr]
    simp [coreDocm4, this, h]
  · intro y hy
    unfold coreDocm3
    split
    · rename_i a b rest; exact (hy a b rest rfl).elim
    · rfl

/-- `kw"text"` is the keyword `Keyword(Symbol(text))`. -/
def KwStrKeyword : Prop := ∀ t : String, kwStr t = .keyword t

theorem kwStrKeyword : KwStrKeyword := fun _ => rfl

/-! ## `HTML` and `Text` -/

/-- `HTML(xs...)` shows as the concatenation of `print`ed arguments, `html"s"` as `s`, the
`catdoc` of several `HTML`s as the concatenation of their `text/html` shows; `Text` prints and
shows its content, and `catdoc` of `Text`s concatenates them. -/
def HtmlTextRendering : Prop :=
  ∀ {C : Type} (printC : C → String),
    (∀ xs, showHtml printC (htmlVarargs printC xs) = String.join (xs.map printC)) ∧
    (∀ c, showHtml printC (.value c) = printC c) ∧
    (∀ s, showHtml id (htmlStr s) = s) ∧
    (∀ hs, showHtml printC (catdocHtml printC hs) = String.join (hs.map (showHtml printC))) ∧
    (∀ t, showText printC t = printText printC t) ∧
    (∀ c, printText printC (.value c) = printC c) ∧
    (∀ out, printText printC (.fn out) = String.join out) ∧
    (∀ s, printText id (textStr s) = s) ∧
    (∀ ts, printText printC (catdocText printC ts) = String.join (ts.map (printText printC)))

theorem htmlTextRendering : HtmlTextRendering := by
  intro C printC
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `isequal(x, y)` implies `hash(x) == hash(y)` (the `hash` contract), for `HTML` and `Text`
whose content type obeys it. -/
def TextHashIsequal : Prop :=
  ∀ {C : Type} (ops : ContentOps C), (∀ a b, ops.isequal a b = true → ops.hash a = ops.hash b) →
    ∀ a b h, wrapperIsequal ops a b = true → wrapperHash ops a h = wrapperHash ops b h

/-- `Float64` contents `-0.0` (`true`) and `0.0` (`false`): equal under `==`, not under
`isequal`, with different hashes. -/
def signedZeroOps : ContentOps Bool :=
  { eq := fun _ _ => true, isequal := fun a b => a == b,
    hash := fun a h => if a then h + 1 else h, hashType := id }

theorem textHashIsequal_refuted : ¬ TextHashIsequal := by
  intro h
  have := h signedZeroOps (by intro a b hab; simp [signedZeroOps] at hab; subst hab; rfl) true false 0 rfl
  simp [wrapperHash, signedZeroOps] at this

/-- `==` of two `HTML`/`Text` of the same type compares their contents with `==`. -/
def WrapperEqContent : Prop :=
  ∀ {C : Type} (ops : ContentOps C) (a b : C), wrapperEq ops a b = ops.eq a b ∧
    wrapperHash ops a 0 = ops.hashType (ops.hash a 0)

theorem wrapperEqContent : WrapperEqContent := fun _ _ _ => ⟨rfl, rfl⟩

/-! ## `Binding` -/

/-- With no import bindings, `Binding(m, v)` is `(binding_module(m', v), v)` where `m'` is the
parent of `m` when `v` names `m` itself (so `Binding(Base, :Base) === Binding(Main, :Base)`). -/
def BindingNormalise : Prop :=
  ∀ (env : ModEnv) (fuel : Nat) (m v : String), (∀ m v, env.imported m v = none) →
    mkBinding env fuel m v = ⟨env.bindingModule (if env.nameof m == v then env.parent m else m) v, v⟩

theorem bindingLoop_noimports (env : ModEnv) (h : ∀ m v, env.imported m v = none) :
    ∀ fuel m v, bindingLoop env fuel m v = (m, v)
  | 0, _, _ => rfl
  | n + 1, m, v => by
    simp only [bindingLoop, h]
    split <;> rfl

theorem bindingNormalise : BindingNormalise := by
  intro env fuel m v h
  simp only [mkBinding, bindingLoop_noimports env h]

/-- An explicit by-name import `v` of `(m2, v2)` is followed: the binding is that of `v2` in
`m2` (with renames threaded through). -/
def BindingFollowsImport : Prop :=
  ∀ (env : ModEnv) (fuel : Nat) (m v m2 v2 : String),
    (env.nameof m == v) = false → env.isdefined m v = true → env.imported m v = some (m2, v2) →
    ¬ (m2 = m ∧ v2 = v) → env.isdefined m2 v2 = false →
    mkBinding env (fuel + 2) m v = ⟨env.bindingModule m2 v2, v2⟩

theorem bindingFollowsImport : BindingFollowsImport := by
  intro env fuel m v m2 v2 hn hd hi hne hd2
  have hb : (m2 == m && v2 == v) = false := by
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    by_cases h1 : m2 = m
    · right; intro h2; exact hne ⟨h1, h2⟩
    · left; exact h1
  simp [mkBinding, hn, bindingLoop, hd, hi, hb, hd2]

/-- `splitexpr` splits `a.b` into `(a, b)`, a symbol into `(@__MODULE__, :s)` and a `GlobalRef`
into `(mod, :name)`, and throws for anything else; `bindingexpr` is the `Binding(...)` call. -/
def SplitexprForms : Prop :=
  (∀ a b rest, splitexpr (.expr "." (a :: b :: rest)) = .ok (a, b)) ∧
  (∀ s, splitexpr (.sym s) = .ok (atModuleExpr, quot (.sym s))) ∧
  (∀ m n, splitexpr (.gref m n) = .ok (.val m, quot (.sym n))) ∧
  (∀ h as, h ≠ "." → ∃ msg, splitexpr (.expr h as) = .error (.errorException msg)) ∧
  (∀ n, ∃ msg, splitexpr (.int n) = .error (.errorException msg)) ∧
  (∀ x a b, splitexpr x = .ok (a, b) → bindingexpr x = .ok (.expr "call" [bindingFn, a, b]))

theorem splitexprForms : SplitexprForms := by
  refine ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun h as hh => ⟨"Could not find something to document", ?_⟩,
    fun _ => ⟨_, rfl⟩, fun x a b hx => by simp [bindingexpr, hx]⟩
  simp [splitexpr, hh]

/-- `defined(b)` is `isdefinedglobal(b.mod, b.var)`; `resolve(b)` returns the global's value or
throws `UndefVarError`; `show(b)` prints the bare name in the active module and `mod.name`
elsewhere, quoting operators. -/
def BindingAccessors : Prop :=
  ∀ (env : ModEnv) (b : Binding),
    defined env b = env.isdefined b.mod b.var ∧
    (env.isdefined b.mod b.var = true → resolve env b = .ok (env.value b.mod b.var)) ∧
    (env.isdefined b.mod b.var = false → resolve env b = .error (.undefVarError b.var)) ∧
    ∀ (isop : String → Bool) (showSym : String → String),
      (b.mod = env.active → showBinding env isop showSym b = b.var) ∧
      (b.mod ≠ env.active → showBinding env isop showSym b =
        b.mod ++ "." ++ (if isop b.var then showSym b.var else b.var))

theorem bindingAccessors : BindingAccessors := by
  intro env b
  refine ⟨rfl, fun h => by simp [resolve, h], fun h => by simp [resolve, h], fun isop showSym => ⟨?_, ?_⟩⟩
  · intro h; simp [showBinding, h]
  · intro h; simp [showBinding, h]

/-- `aliasof(b)` is `b` for an undefined binding or a value that is not a type, function or
module, and otherwise the binding of the value's own name when that binding is defined. -/
def AliasofForms : Prop :=
  ∀ (env : ModEnv) (fuel : Nat) (kind : JV → ValKind) (b : Binding),
    (defined env b = false → aliasof env fuel kind b = b) ∧
    (defined env b = true → kind (env.value b.mod b.var) = .other → aliasof env fuel kind b = b) ∧
    (∀ p n, defined env b = true → kind (env.value b.mod b.var) = .dataType p n →
      defined env (mkBinding env fuel p n) = true → aliasof env fuel kind b = mkBinding env fuel p n) ∧
    (∀ p n, defined env b = true → kind (env.value b.mod b.var) = .function p n →
      defined env (mkBinding env fuel p n) = true → aliasof env fuel kind b = mkBinding env fuel p n) ∧
    (∀ m, aliasofVal env fuel (.module m) b = mkBinding env fuel m (env.nameof m))

theorem aliasofForms : AliasofForms := by
  intro env fuel kind b
  refine ⟨fun h => by simp [aliasof, h], fun h hk => ?_, fun p n h hk hd => ?_, fun p n h hk hd => ?_, fun _ => rfl⟩
  · simp [aliasof, h, hk, aliasofVal]
  · simp [aliasof, h, hk, aliasofVal, hd]
  · simp [aliasof, h, hk, aliasofVal, hd]

end JuliaLean.DocsSyntaxCov
