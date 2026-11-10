import JuliaLean.Proofs.Compiler.src.typelattice.Common

/-!
Properties of the layered `⊑` of `Compiler/src/typelattice.jl:401-567`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelattice

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## Transitivity -/

/-- `⊑(𝕃, ·, ·)` is transitive: `a ⊑ b` and `b ⊑ c` imply `a ⊑ c`. Inference relies on this
when it compares a new state with an old one that was itself merged from earlier states
(`⊑` is "the lattice ordering (i.e. less-than-or-equal)", docstring at
`Compiler/src/abstractlattice.jl:144-150`). -/
def SqsubTransitive (L : Lattice) : Prop :=
  ∀ n₁ n₂ n₃ E a b c s₁ s₁' s₂ s₂',
    (sqsub n₁ E L a b).run s₁ = .ok (true, s₁') →
    (sqsub n₂ E L b c).run s₂ = .ok (true, s₂') →
    Returns (sqsub n₃ E L a c) (· = true)

/-- Transitivity on `typeinf_lattice(NativeInterpreter())`. -/
def SqsubTransitiveTypeinf : Prop := SqsubTransitive typeinfLattice

/-- `Conditional(1, 0, Any, Union{})`, `Conditional(1, 0, Any, Int)`. -/
def condAnyBot : LElt := .conditional 1 0 (.ty anyType) (.ty .bottom) false
def condAnyInt : LElt := .conditional 1 0 (.ty anyType) (.ty longType) false

/-- Counterexample: `Const(true) ⊑ Conditional(1, 0, Any, Union{})` and
`Conditional(1, 0, Any, Union{}) ⊑ Conditional(1, 0, Any, Int)`, but
`Const(true) ⋢ Conditional(1, 0, Any, Int)`: the `Const(Bool)` case of
`⊑(::AnyConditionalsLattice, ...)` (`Compiler/src/typelattice.jl:434-442`) requires the branch
that cannot be taken to have type `Union{}`, which `issubconditional` does not preserve. -/
theorem sqsubTransitiveTypeinf_refuted : ¬ SqsubTransitiveTypeinf := by
  intro h
  have h₃ := h 10 10 10 default (.const (boolVal true)) condAnyBot condAnyInt 0 0 0 0
    (by rfl) (by rfl) 0 false 0 (by rfl)
  exact Bool.false_ne_true h₃

/-! ## `Any` is the top element -/

/-- Every lattice element is `⊑ Any` (`Any` is the top of the native type lattice, and every
layer's element widens to a type). -/
def SqsubAnyTop (L : Lattice) : Prop :=
  ∀ n E x, Returns (sqsub n E L x (.ty anyType)) (· = true)

/-- `PartialTypeVar(T, true, true)` for the `TypeVar` with id 1. -/
def ptvT : LElt := .partialTypeVar (.typevar 1 "T" .bottom anyType) true true

/-- Counterexample on `optimizer_lattice(NativeInterpreter())`: `PartialTypeVar(T) ⋢ Any`. The
`ConstsLattice` method accepts a `PartialTypeVar` only below `TypeVar` itself
(`b === TypeVar || a === b`, `Compiler/src/typelattice.jl:561-562`), and the optimizer lattice
has no conditional layer whose `b === Any` fast path would hide it. -/
def SqsubAnyTopOptimizer : Prop := SqsubAnyTop optimizerLattice
def SqsubAnyTopTypeinf : Prop := SqsubAnyTop typeinfLattice

theorem sqsubAnyTopOptimizer_refuted : ¬ SqsubAnyTopOptimizer := by
  intro h
  exact Bool.false_ne_true (h 10 default ptvT 0 false 0 (by rfl))

theorem sqsubAnyTopTypeinf_proven : SqsubAnyTopTypeinf := by
  intro n E x s r s' h
  cases x
  case limitedAccuracy t cs cid =>
    cases t <;> (rcases n with _ | _ | _ | k) <;> (cases h; try rfl)
  all_goals ((rcases n with _ | _ | _ | k) <;> (cases h; try rfl))

/-! ## `Union{}` is the bottom element -/

/-- `Union{}` is `⊑` every lattice element. -/
def SqsubBottomLeast (L : Lattice) : Prop :=
  ∀ n E x, Returns (sqsub n E L (.ty .bottom) x) (· = true)

/-- Counterexample on `optimizer_lattice(NativeInterpreter())`: `Union{} ⋢ Const(1)`. The
`Union{}` fast path is only in `⊑(::AnyConditionalsLattice, ...)`
(`Compiler/src/typelattice.jl:421-425`); the `ConstsLattice` method asks
`issingletontype(Union{})`, which is false. -/
def SqsubBottomLeastOptimizer : Prop := SqsubBottomLeast optimizerLattice

theorem sqsubBottomLeastOptimizer_refuted : ¬ SqsubBottomLeastOptimizer := by
  intro h
  exact Bool.false_ne_true (h 10 default (.const (.long 1)) 0 false 0 (by rfl))

theorem sqsub_cond_bottom {m : Nat} {E : CEnv} {p : Lattice} {b : LElt} {s r s'}
    (h : (sqsub m E (.conditionals p) (.ty .bottom) b).run s = .ok (r, s')) : r = true := by
  rcases m with _ | k
  · cases h
  · rw [sqsub.eq_def] at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h; rfl

theorem sqsub_ma_bottom {m : Nat} {E : CEnv} {p : Lattice} {b : LElt} {s r s'}
    (h : (sqsub m E (.mustAliases (.conditionals p)) (.ty .bottom) b).run s = .ok (r, s')) :
    r = true := by
  rcases m with _ | k
  · cases h
  · rw [sqsub.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hc; simp [isMustAliasT, LElt.isMustAlias] at hc
    · split at h
      · cases h; rfl
      · exact sqsub_cond_bottom h

/-- On `typeinf_lattice`, `Union{}` is `⊑` every element that is not a `LimitedAccuracy` (a
`LimitedAccuracy(T)` is "ε smaller" than `T`, `Compiler/src/typelattice.jl:416 and 181`, so
`LimitedAccuracy(Union{})` is below `Union{}` by design). -/
def SqsubBottomLeastTypeinf : Prop :=
  ∀ n E x, x.isLimited = false → Returns (sqsub n E typeinfLattice (.ty .bottom) x) (· = true)

theorem sqsubBottomLeastTypeinf_proven : SqsubBottomLeastTypeinf := by
  intro n E x hx s r s' h
  rcases n with _ | k
  · cases h
  · rw [sqsub.eq_def] at h
    dsimp only [typeinfLattice, baseInferenceLattice, simpleInferenceLattice] at h
    obtain ⟨c, s₁, hle, hk⟩ := run_bind_inv h
    have hix : ignorelimited x = x := by cases x <;> first | rfl | simp [LElt.isLimited] at hx
    have hib : ignorelimited (LElt.ty .bottom) = .ty .bottom := rfl
    rw [hix, hib] at hle
    have hc : c = true := sqsub_ma_bottom hle
    subst hc
    cases x <;> first | (cases hk; rfl) | (simp [LElt.isLimited] at hx)

/-! ## `⊑` against native upper bounds -/

/-- `⊑` agrees with `widenconst` on native upper bounds: if `widenconst(a) <: T`, then
`a ⊑ T`. Every layer's element is described by its widened type (`widenconst` "widens extended
lattice element `x` to native `Type` representation", `Compiler/src/typelattice.jl:730-734`), so
an element is below every supertype of its widening. -/
def SqsubWidenconstUpper (L : Lattice) : Prop :=
  ∀ n₁ n₂ n₃ E a w T s₁ s₁' s₂ s₂', (widenconst n₁ E a).run s₁ = .ok (w, s₁') →
    (issub n₂ E w T).run s₂ = .ok (true, s₂') → Returns (sqsub n₃ E L a (.ty T)) (· = true)

/-- The universe of `Any`, `TypeVar` and `Nothing`. -/
def tvE : CEnv where
  types := { names := [
    { name := "Core.Any", abstract := true, mutable := false, wrapper := anyType, super := none },
    { name := "Core.TypeVar", abstract := false, mutable := true, wrapper := tvarType,
      super := some anyType },
    { name := "Core.Nothing", abstract := false, mutable := false,
      wrapper := .datatype "Core.Nothing" [], super := some anyType } ], layouts := [] }

/-- `Union{Nothing, TypeVar}`. -/
def nothingOrTypeVar : Val := .union (.datatype "Core.Nothing" []) tvarType

/-- Counterexample on `typeinf_lattice`: `widenconst(PartialTypeVar(T)) = TypeVar` and
`TypeVar <: Union{Nothing, TypeVar}`, but `PartialTypeVar(T) ⋢ Union{Nothing, TypeVar}`: the
`ConstsLattice` method accepts a `PartialTypeVar` only below `TypeVar` itself
(`b === TypeVar || a === b`, `Compiler/src/typelattice.jl:561-562`). -/
theorem tvarType_sub_nothingOrTypeVar :
    ∃ s', (issub 40 tvE tvarType nothingOrTypeVar).run 0 = .ok (true, s') := by
  have hb : (match (issub 40 tvE tvarType nothingOrTypeVar).run 0 with
      | .ok (true, _) => true | _ => false) = true := by decide +kernel
  split at hb
  · rename_i s' heq; exact ⟨s', heq⟩
  · cases hb

def SqsubWidenconstUpperTypeinf : Prop := SqsubWidenconstUpper typeinfLattice

theorem sqsubWidenconstUpperTypeinf_refuted : ¬ SqsubWidenconstUpperTypeinf := by
  intro h
  obtain ⟨s', hs⟩ := tvarType_sub_nothingOrTypeVar
  exact Bool.false_ne_true (h 10 40 10 tvE ptvT tvarType nothingOrTypeVar 0 0 0 s' rfl
    hs 0 false 0 (by rfl))

/-! ## `⊑(::InferenceLattice, ...)`: `LimitedAccuracy(T)` is ε below `T` -/

theorem sqsub_inference_eq (n : Nat) (E : CEnv) (p : Lattice) (a b : LElt) :
    sqsub (n + 1) E (.inference p) a b = (do
      if !(← sqsub n E p (ignorelimited a) (ignorelimited b)) then return false
      let .limitedAccuracy btyp bcauses _ := b | return true
      let abEq ← sqsub n E p btyp (ignorelimited a)
      if !abEq then
        return true
      let .limitedAccuracy _ acauses _ := a | return false
      return bcauses.all acauses.contains : CM Bool) := by
  first | rfl | (rw [sqsub.eq_def]; rfl) | rw [sqsub.eq_def]

/-- The `LimitedAccuracy` docstring (`Compiler/src/typelattice.jl:180-183`): "As a lattice
element, `LimitedAccuracy(T)` is considered ε smaller than the corresponding lattice element `T`,
but in particular, all lattice elements that are `⊑ T` (but not equal `T`) are also
`⊑ LimitedAccuracy(T)`." Stated for every parent layer `p` and every element `T` with `T ⊑ T` in
`p` (reflexivity is a hypothesis, not proven, see the coverage notes), and every non-limited `a`:

* elements that are not limited are compared by the parent layer;
* `LimitedAccuracy(T) ⊑ T`, and `T ⋢ LimitedAccuracy(T)` (ε smaller, not equal);
* `a ⊑ LimitedAccuracy(T)` when `a ⊑ T` and `T ⋢ a` in `p` (strictly below `T`);
* `LimitedAccuracy(T, ca) ⊑ LimitedAccuracy(T, cb)` exactly when `cb ⊆ ca` (a result limited by
  more causes is less precise). -/
def SqsubLimitedEpsilon : Prop :=
  ∀ n E p,
    (∀ a b s, a.isLimited = false → b.isLimited = false →
      (sqsub (n + 1) E (.inference p) a b).run s = (sqsub n E p a b).run s) ∧
    (∀ T cs cid, T.isLimited = false → AlwaysReturns (sqsub n E p T T) true →
      AlwaysReturns (sqsub (n + 1) E (.inference p) (.limitedAccuracy T cs cid) T) true ∧
      AlwaysReturns (sqsub (n + 1) E (.inference p) T (.limitedAccuracy T cs cid)) false) ∧
    (∀ a T cs cid, a.isLimited = false → AlwaysReturns (sqsub n E p a T) true →
      AlwaysReturns (sqsub n E p T a) false →
      AlwaysReturns (sqsub (n + 1) E (.inference p) a (.limitedAccuracy T cs cid)) true) ∧
    (∀ T ca ia cb ib, AlwaysReturns (sqsub n E p T T) true → ∀ s, ∃ r s',
      (sqsub (n + 1) E (.inference p) (.limitedAccuracy T ca ia) (.limitedAccuracy T cb ib)).run s =
        .ok (r, s') ∧ (r = true ↔ ∀ c ∈ cb, c ∈ ca))

theorem sqsubLimitedEpsilon_proven : SqsubLimitedEpsilon := by
  intro n E p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b s ha hb
    rw [sqsub_inference_eq, ignorelimited_of_not_limited ha, ignorelimited_of_not_limited hb]
    cases h : (sqsub n E p a b).run s with
    | error e => exact run_bind_error h
    | ok q =>
      obtain ⟨c, s₁⟩ := q
      rw [run_bind_ok h]
      cases c
      · rfl
      · cases b <;> first | rfl | (simp [LElt.isLimited] at hb)
  · intro T cs cid hTl hT
    refine ⟨fun s => ?_, fun s => ?_⟩
    · obtain ⟨s₁, h₁⟩ := hT s
      refine ⟨s₁, ?_⟩
      rw [sqsub_inference_eq, ignorelimited_la, ignorelimited_of_not_limited hTl, run_bind_ok h₁]
      cases T <;> first | rfl | (simp [LElt.isLimited] at hTl)
    · obtain ⟨s₁, h₁⟩ := hT s
      obtain ⟨s₂, h₂⟩ := hT s₁
      refine ⟨s₂, ?_⟩
      rw [sqsub_inference_eq, ignorelimited_la, ignorelimited_of_not_limited hTl, run_bind_ok h₁]
      refine (run_bind_ok h₂).trans ?_
      cases T <;> first | rfl | (simp [LElt.isLimited] at hTl)
  · intro a T cs cid ha h1 h2 s
    obtain ⟨s₁, k₁⟩ := h1 s
    obtain ⟨s₂, k₂⟩ := h2 s₁
    refine ⟨s₂, ?_⟩
    rw [sqsub_inference_eq, ignorelimited_la, ignorelimited_of_not_limited ha, run_bind_ok k₁]
    refine (run_bind_ok k₂).trans ?_
    rfl
  · intro T ca ia cb ib hT s
    obtain ⟨s₁, h₁⟩ := hT s
    obtain ⟨s₂, h₂⟩ := hT s₁
    refine ⟨cb.all ca.contains, s₂, ?_, ?_⟩
    · rw [sqsub_inference_eq, ignorelimited_la, ignorelimited_la, run_bind_ok h₁]
      refine (run_bind_ok h₂).trans ?_
      rfl
    · rw [List.all_eq_true]
      exact ⟨fun h c hc => List.mem_of_elem_eq_true (h c hc),
        fun h c hc => List.elem_eq_true_of_mem (h c hc)⟩

/-! ## `⊑(::AnyMustAliasesLattice, ...)` -/

/-- `⊑` on the must-alias layers (`Compiler/src/typelattice.jl:447-458`), for every parent layer:
an alias stands for its field (`MustAlias` docstring), so

* only `Union{}` is below an alias among the elements that are not aliases;
* two aliases of different fields (not `is_same_alias`) are incomparable;
* an alias is compared with a non-alias through its field type `fldtyp`, in the parent layer. -/
def SqsubMustAliasSpec : Prop :=
  ∀ n E p s,
    (∀ a slot d v i f, a.isMustAlias = false →
      (sqsub (n + 1) E (.mustAliases p) a (.mustAlias slot d v i f)).run s = .ok (a.isBottom, s)) ∧
    (∀ s1 d1 v1 i1 f1 s2 d2 v2 i2 f2,
      isSameAlias (.mustAlias s1 d1 v1 i1 f1) (.mustAlias s2 d2 v2 i2 f2) = false →
      (sqsub (n + 1) E (.mustAliases p) (.mustAlias s1 d1 v1 i1 f1)
        (.mustAlias s2 d2 v2 i2 f2)).run s = .ok (false, s)) ∧
    (∀ slot d v i f b, b.isMustAlias = false →
      (sqsub (n + 1) E (.mustAliases p) (.mustAlias slot d v i f) b).run s =
        (sqsub n E p f b).run s) ∧
    (∀ a slot v i f, a.isInterMustAlias = false →
      (sqsub (n + 1) E (.interMustAliases p) a (.interMustAlias slot v i f)).run s =
        .ok (a.isBottom, s)) ∧
    (∀ s1 v1 i1 f1 s2 v2 i2 f2,
      isSameAlias (.interMustAlias s1 v1 i1 f1) (.interMustAlias s2 v2 i2 f2) = false →
      (sqsub (n + 1) E (.interMustAliases p) (.interMustAlias s1 v1 i1 f1)
        (.interMustAlias s2 v2 i2 f2)).run s = .ok (false, s)) ∧
    (∀ slot v i f b, b.isInterMustAlias = false →
      (sqsub (n + 1) E (.interMustAliases p) (.interMustAlias slot v i f) b).run s =
        (sqsub n E p f b).run s)

theorem sqsubMustAliasSpec_proven : SqsubMustAliasSpec := by
  intro n E p s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a slot d v i f ha
    cases a <;> first | rfl | (simp [LElt.isMustAlias] at ha)
  · intro s1 d1 v1 i1 f1 s2 d2 v2 i2 f2 h
    rw [sqsub.eq_def]; dsimp only
    unfold issubalias
    rw [h]
    rfl
  · intro slot d v i f b hb
    cases b <;> first | rfl | (simp [LElt.isMustAlias] at hb)
  · intro a slot v i f ha
    cases a <;> first | rfl | (simp [LElt.isInterMustAlias] at ha)
  · intro s1 v1 i1 f1 s2 v2 i2 f2 h
    rw [sqsub.eq_def]; dsimp only
    unfold issubalias
    rw [h]
    rfl
  · intro slot v i f b hb
    cases b <;> first | rfl | (simp [LElt.isInterMustAlias] at hb)

/-! ## `⊑(::PartialsLattice, ...)` outside the field loops -/

/-- `⊑` on the partials layer (`Compiler/src/typelattice.jl:460-545`), for every parent layer,
on the branches that do not run the field-by-field loops:

* a `PartialStruct` is below a type `T` exactly when its `typ <: T` (it is described by `typ`);
* a `PartialStruct` is not below another whose `typ` is not a supertype of its own, nor below one
  with a different number of fields;
* a `PartialOpaque` is below another exactly when they come from the same method and source,
  `typ <: typ'` and the environments are ordered; against any element that is not partial it is
  compared through its `typ` in the parent layer;
* a `PartialTask` is below another exactly when the fetch types are ordered; against any element
  that is not partial it is compared as `Task` in the parent layer.

The two field loops (`PartialStruct` against `PartialStruct`, and `Const` against
`PartialStruct`) are not stated. -/
def SqsubPartialsSpec : Prop :=
  ∀ n E p,
    (∀ typ u fs ui fi T s r s', T.isType = true → (issub n E typ T).run s = .ok (r, s') →
      (sqsub (n + 1) E (.partials p) (.partialStruct typ u fs ui fi) (.ty T)).run s =
        .ok (r, s')) ∧
    (∀ ta ua fa uia fia tb ub fb uib fib s s₁, (issub n E ta tb).run s = .ok (false, s₁) →
      (sqsub (n + 1) E (.partials p) (.partialStruct ta ua fa uia fia)
        (.partialStruct tb ub fb uib fib)).run s = .ok (false, s₁)) ∧
    (∀ ta ua fa uia fia tb ub fb uib fib s s₁, (issub n E ta tb).run s = .ok (true, s₁) →
      fa.length ≠ fb.length →
      (sqsub (n + 1) E (.partials p) (.partialStruct ta ua fa uia fia)
        (.partialStruct tb ub fb uib fib)).run s = .ok (false, s₁)) ∧
    (∀ ta ea pa sa tb eb pb sb s, (pa == pb && sa == sb) = false →
      (sqsub (n + 1) E (.partials p) (.partialOpaque ta ea pa sa)
        (.partialOpaque tb eb pb sb)).run s = .ok (false, s)) ∧
    (∀ ta ea pa sa tb eb pb sb s s₁, (pa == pb && sa == sb) = true →
      (issub n E ta tb).run s = .ok (false, s₁) →
      (sqsub (n + 1) E (.partials p) (.partialOpaque ta ea pa sa)
        (.partialOpaque tb eb pb sb)).run s = .ok (false, s₁)) ∧
    (∀ ta ea pa sa tb eb pb sb s s₁ r s₂, (pa == pb && sa == sb) = true →
      (issub n E ta tb).run s = .ok (true, s₁) →
      (sqsub n E (.partials p) ea eb).run s₁ = .ok (r, s₂) →
      (sqsub (n + 1) E (.partials p) (.partialOpaque ta ea pa sa)
        (.partialOpaque tb eb pb sb)).run s = .ok (r, s₂)) ∧
    (∀ ta ea pa sa b s r s', b.isPartialStruct = false → b.isPartialOpaque = false →
      (sqsub n E p (.ty ta) b).run s = .ok (r, s') →
      (sqsub (n + 1) E (.partials p) (.partialOpaque ta ea pa sa) b).run s = .ok (r, s')) ∧
    (∀ fa fb s r s', (sqsub n E (.partials p) fa fb).run s = .ok (r, s') →
      (sqsub (n + 1) E (.partials p) (.partialTask fa) (.partialTask fb)).run s = .ok (r, s')) ∧
    (∀ fa b s r s', b.isPartialStruct = false → b.isPartialOpaque = false →
      b.isPartialTask = false → (sqsub n E p (.ty taskType) b).run s = .ok (r, s') →
      (sqsub (n + 1) E (.partials p) (.partialTask fa) b).run s = .ok (r, s'))

theorem sqsubPartialsSpec_proven : SqsubPartialsSpec := by
  intro n E p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro typ u fs ui fi T s r s' hT h
    rw [sqsub.eq_def]; dsimp only
    rw [hT]
    exact h
  · intro ta ua fa uia fia tb ub fb uib fib s s₁ h
    rw [sqsub.eq_def]; dsimp only
    refine (run_bind_ok h).trans ?_
    rfl
  · intro ta ua fa uia fia tb ub fb uib fib s s₁ h hlen
    have hne : (fa.length != fb.length) = true := by simpa using hlen
    rw [sqsub.eq_def]; dsimp only
    rw [run_bind_ok h]
    simp only [hne, Bool.not_true, Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    try rfl
  · intro ta ea pa sa tb eb pb sb s h
    rw [sqsub.eq_def]; dsimp only
    rw [h]
    rfl
  · intro ta ea pa sa tb eb pb sb s s₁ hps h
    rw [sqsub.eq_def]; dsimp only
    rw [hps]
    refine (run_bind_ok h).trans ?_
    rfl
  · intro ta ea pa sa tb eb pb sb s s₁ r s₂ hps h₁ h₂
    rw [sqsub.eq_def]; dsimp only
    rw [hps]
    refine (run_bind_ok h₁).trans ?_
    exact h₂
  · intro ta ea pa sa b s r s' hb1 hb2 h
    cases b <;>
      first
      | (rw [sqsub.eq_def]; dsimp only; exact h)
      | (simp [LElt.isPartialStruct, LElt.isPartialOpaque] at hb1 hb2)
  · intro fa fb s r s' h
    rw [sqsub.eq_def]; dsimp only
    exact h
  · intro fa b s r s' hb1 hb2 hb3 h
    cases b <;>
      first
      | (rw [sqsub.eq_def]; dsimp only; exact h)
      | (simp [LElt.isPartialStruct, LElt.isPartialOpaque, LElt.isPartialTask] at hb1 hb2 hb3)

end JuliaLean.Proofs.Compiler.src.typelattice
