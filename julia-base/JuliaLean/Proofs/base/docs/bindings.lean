import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.docs.basedocs
import JuliaLean.base.docs.bindings
import JuliaLean.base.docs.core
import JuliaLean.base.docs.utils
import JuliaLean.base.expr
import JuliaLean.base.meta


section

/-!
# Properties of `base/docs/core.jl`, `utils.jl`, `bindings.jl` and `basedocs.jl`
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

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

end

namespace JuliaLean.Proofs.base.docs.bindings

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-bindings-normalise" "base/docs/bindings.jl" ["Binding"]
    "Binding normalizes self names and binding modules."
    "base/docs/bindings.jl:7-25" ``BindingNormalise ``bindingNormalise,
  proven "docssyntaxcov-bindings-import" "base/docs/bindings.jl" ["Binding"]
    "Binding follows explicit import chains."
    "base/docs/bindings.jl:7-25" ``BindingFollowsImport ``bindingFollowsImport,
  proven "docssyntaxcov-bindings-split" "base/docs/bindings.jl" ["bindingexpr", "splitexpr"]
    "Binding expressions split dotted names, symbols and GlobalRefs."
    "base/docs/bindings.jl:28-38" ``SplitexprForms ``splitexprForms,
  proven "docssyntaxcov-bindings-accessors" "base/docs/bindings.jl" ["defined", "resolve", "show"]
    "Binding accessors check definition, resolve values and display qualified names."
    "base/docs/bindings.jl:30-53" ``BindingAccessors ``bindingAccessors,
  proven "docssyntaxcov-bindings-alias" "base/docs/bindings.jl" ["aliasof"]
    "aliasof follows type, function and module aliases and preserves other bindings."
    "base/docs/bindings.jl:55-59" ``AliasofForms ``aliasofForms,
]

end JuliaLean.Proofs.base.docs.bindings
