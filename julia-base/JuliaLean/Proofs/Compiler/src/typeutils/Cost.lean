import JuliaLean.Proofs.Compiler.src.typeutils.CostArith
import JuliaLean.Proofs.Compiler.src.typeutils.Loops

/-!
`unionsplitcost` (`Compiler/src/typeutils.jl:285-316`) and `is_union_split_eligible`
(`Compiler/src/abstractinterpretation.jl:395-397`) without alias groups: the model's loop computes
`costLoop` of the union lengths, which is twice the product of the lengths divided by the largest
(or by 2), capped at `typemax(Int)`.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- `unionlen(ti)` when the argument `ti` is a `Union`, read the way `unionsplitcost` reads it. -/
def unionLenOf : LElt → Option Nat
  | .ty (.union a b) => some (unionlen (.union a b))
  | _ => none

theorem unionlen_pos : ∀ v : Val, 1 ≤ unionlen v
  | .union a b => by have := unionlen_pos a; simp only [unionlen]; omega
  | .datatype .. | .intersect .. | .typeeq .. | .typeegal .. | .unionall .. | .typevar ..
  | .vararg .. | .bottom | .typeapp .. | .long .. | .symbol .. | .bits .. | .imm ..
  | .mutableRef .. | .module .. => Nat.le_refl 1

theorem unionLenOf_pos (argtypes : List LElt) :
    ∀ x, some x ∈ argtypes.map unionLenOf → 1 ≤ x := by
  intro x hx
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hx
  cases a with
  | ty t =>
    cases t with
    | union a b => cases ha; exact unionlen_pos _
    | _ => cases ha
  | _ => cases ha

/-- What the loop body does for one argument. -/
def costStepR (p : Int × Nat) : Option Nat → ForInStep (Option Int × Int × Nat)
  | none => .yield (none, p.1, p.2)
  | some x =>
    let q := costStep p x
    if q.1 > typemaxInt then .done (some typemaxInt, q.1, q.2) else .yield (none, q.1, q.2)

/-- What the code after the loop returns. -/
def costFinish (r : Option Int × Int × Nat) : Int :=
  match r.1 with
  | some v => v
  | none => r.2.1

theorem forIn_cost (lens : List (Option Nat)) : ∀ (k m : Nat), lens.length = m →
    ∀ (f : Nat → Option Int × Int × Nat → CM (ForInStep (Option Int × Int × Nat))),
    (∀ j (hj : j < lens.length) nu mx s r s', (f (k + j) (none, nu, mx)).run s = .ok (r, s') →
      r = costStepR (nu, mx) lens[j]) →
    ∀ nu mx s r s', (forIn (List.range' k m) (none, nu, mx) f).run s = .ok (r, s') →
      costFinish r = costLoop (nu, mx) lens := by
  induction lens with
  | nil =>
    intro k m hm f _ nu mx s r s' h
    subst hm
    cases h; rfl
  | cons o os ih =>
    intro k m hm f hf nu mx s r s' h
    subst hm
    rw [List.length_cons, List.range'_succ] at h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    have hst := hf 0 (by simp) nu mx s st s₁ (by simpa using h1)
    simp only [List.getElem_cons_zero] at hst
    subst hst
    have hf' : ∀ j (hj : j < os.length) nu mx s r s',
        (f (k + 1 + j) (none, nu, mx)).run s = .ok (r, s') → r = costStepR (nu, mx) os[j] := by
      intro j hj nu mx s r s' h
      have := hf (j + 1) (by simp; omega) nu mx s r s' (by rw [show k + (j + 1) = k + 1 + j by omega]; exact h)
      simpa using this
    cases o with
    | none =>
      simp only [costStepR] at h2
      exact ih (k + 1) os.length rfl f hf' nu mx s₁ r s' h2
    | some x =>
      simp only [costStepR] at h2
      simp only [costLoop]
      split
      · rename_i hq
        simp only [hq, if_true] at h2
        obtain ⟨rfl, -⟩ := h2
        rfl
      · rename_i hq
        simp only [hq, if_false] at h2
        exact ih (k + 1) os.length rfl f hf' _ _ s₁ r s' h2

/-- The arguments `unionsplitcost` reads without widening them first: on a lattice with extended
union splitting (`MustAliasesLattice`, so `typeinf_lattice`), plain types and `Vararg`s. -/
def PlainArgs (L : Lattice) (argtypes : List LElt) : Prop :=
  hasExtendedUnionsplit L = true → ∀ a ∈ argtypes, a.isTypeElt = true ∨ a.isVarargElt = true

theorem widenconstSplit_ty_run (n : Nat) (E : CEnv) (t : Val) (ht : t.isType = true) (s : Nat) :
    (widenconstSplit n E (.ty t)).run s = .ok (t, s) := by
  simp only [widenconstSplit, ht, if_true]; rfl

/-- The body of the loop of `unionsplitcost` after reading (and maybe widening) the argument. -/
def costBody (nu : Int) (mx : Nat) (a : LElt) : CM (ForInStep (Option Int × Int × Nat)) :=
  match a with
  | .ty u@(.union _ _) =>
    if unionlen u > mx then
      if nu * ↑mx > typemaxInt then pure (.done (some typemaxInt, nu * ↑mx, unionlen u))
      else pure (.yield (none, nu * ↑mx, unionlen u))
    else
      if nu * ↑(unionlen u) > typemaxInt then pure (.done (some typemaxInt, nu * ↑(unionlen u), mx))
      else pure (.yield (none, nu * ↑(unionlen u), mx))
  | _ => pure (.yield (none, nu, mx))

theorem costBody_spec (nu : Int) (mx : Nat) (a : LElt) (s r s') :
    (costBody nu mx a).run s = .ok (r, s') → r = costStepR (nu, mx) (unionLenOf a) := by
  intro h
  cases a with
  | ty t =>
    cases t with
    | union x y =>
      simp only [costBody] at h
      simp only [unionLenOf, costStepR, costStep]
      by_cases hl : unionlen (.union x y) > mx
      · simp only [hl, if_true] at h ⊢
        split at h <;> cases h <;> simp_all
      · simp only [hl, if_false] at h ⊢
        split at h <;> cases h <;> simp_all
    | _ => cases h; rfl
  | _ => cases h; rfl

/-- The loop of `unionsplitcost` computes `costLoop` of the union lengths. -/
theorem unionsplitcost_loop (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt)
    (isVector : Bool) (hma : NoMustAlias argtypes) (hplain : PlainArgs L argtypes) :
    Returns (unionsplitcost n E L argtypes isVector none)
      (· = costLoop (1, 2) (argtypes.map unionLenOf)) := by
  intro s r s' h
  unfold unionsplitcost at h
  obtain ⟨g, s₁, hg, h⟩ := run_bind_inv h
  have hg' := computeAliasGroups_none argtypes _ (by cases isVector <;> simp) hma s g s₁ hg
  subst hg'
  obtain ⟨st, s₂, hst, h⟩ := run_bind_inv h
  have hfin := forIn_cost (argtypes.map unionLenOf) 1 argtypes.length (by simp) _ ?_ 1 2 s₁ st s₂ hst
  · rw [← hfin]
    unfold costFinish
    cases hs1 : st.1 with
    | some v => simp only [hs1] at h; cases h; rfl
    | none => simp only [hs1] at h; cases h; rfl
  · intro j hj nu mx s₃ r₃ s₃' h3
    simp only [List.length_map] at hj
    simp only [List.getElem_map]
    rw [Nat.add_comm 1 j] at h3
    obtain ⟨ti, s₄, hti, h3⟩ := run_bind_inv h3
    rw [eltAt_run argtypes j hj] at hti
    cases hti
    have hmem : argtypes[j] ∈ argtypes := List.getElem_mem hj
    generalize argtypes[j] = a at h3 hmem ⊢
    simp only at h3
    have h3' : ((if (hasExtendedUnionsplit L && !a.isVarargElt) = true then do
          let w ← widenconstSplit n E a
          costBody nu mx (.ty w)
        else costBody nu mx a) : CM _).run s₃ = .ok (r₃, s₃') := h3
    clear h3
    split at h3'
    · rename_i hc
      have hext : hasExtendedUnionsplit L = true := by simp_all
      have hnv : a.isVarargElt = false := by simp_all
      rcases hplain hext a hmem with ht | ht
      · cases a with
        | ty t =>
          simp only [LElt.isTypeElt] at ht
          obtain ⟨w, s₅, hw, h3'⟩ := run_bind_inv h3'
          rw [widenconstSplit_ty_run n E t ht] at hw
          cases hw
          exact costBody_spec nu mx _ _ _ _ h3'
        | _ => simp [LElt.isTypeElt] at ht
      · rw [hnv] at ht; cases ht
    · exact costBody_spec nu mx _ _ _ _ h3'

/-! ## Registry statements -/

/-- The union lengths `unionsplitcost` multiplies, 1 for an argument that is not a `Union`. -/
def costLens (argtypes : List LElt) : List Nat := argtypes.map fun a => lenOrOne (unionLenOf a)

theorem costLens_eq (argtypes : List LElt) :
    (argtypes.map unionLenOf).map lenOrOne = costLens argtypes := by
  simp [costLens, List.map_map, Function.comp_def]

theorem costF_eq_div (l : List Nat) : costF l = 2 * costP l / costM l := by
  have h := costF_mul_costM l
  have hM : 0 < costM l := by have := costM_ge_two l; omega
  rw [← h, Nat.mul_div_cancel _ hM]

theorem unionsplitcost_capped (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt)
    (isVector : Bool) (hma : NoMustAlias argtypes) (hplain : PlainArgs L argtypes) :
    Returns (unionsplitcost n E L argtypes isVector none) (· = costCapped (costLens argtypes)) := by
  intro s r s' h
  rw [unionsplitcost_loop n E L argtypes isVector hma hplain s r s' h,
    costLoop_one_two _ (unionLenOf_pos argtypes), costLens_eq]

/-- `unionsplitcost` "gives a cost function over the effort to switch a tuple-union
representation as a cartesian product, relative to the size of the original representation",
counting "the longest element as being roughly invariant"
(`Compiler/src/typeutils.jl:285-290`). Without alias groups (no `fargs`, no `MustAlias`
argument) and for arguments it reads unwidened, the result is exactly twice the product of the
union lengths divided by the largest length (or by 2 when no length is larger), capped at
`typemax(Int)`. -/
def UnionsplitcostSpec : Prop :=
  ∀ n E L argtypes isVector, NoMustAlias argtypes → PlainArgs L argtypes →
    Returns (unionsplitcost n E L argtypes isVector none) (fun c =>
      c = min typemaxInt ((2 * costP (costLens argtypes) / costM (costLens argtypes) : Nat) : Int))

theorem unionsplitcostSpec_proven : UnionsplitcostSpec := by
  intro n E L argtypes isVector hma hplain s r s' h
  rw [unionsplitcost_capped n E L argtypes isVector hma hplain s r s' h, costCapped,
    ← costF_eq_div]
  split <;> omega

/-- The cost does not depend on the order of the arguments (so neither does
`is_union_split_eligible`): permuting the arguments gives the same cost. -/
def UnionsplitcostOrderIndependent : Prop :=
  ∀ n E L (a a' : List LElt) isVector, a.Perm a' → NoMustAlias a → PlainArgs L a →
    ∀ s c s₁ s' c' s₁', (unionsplitcost n E L a isVector none).run s = .ok (c, s₁) →
      (unionsplitcost n E L a' isVector none).run s' = .ok (c', s₁') → c = c'

theorem unionsplitcostOrderIndependent_proven : UnionsplitcostOrderIndependent := by
  intro n E L a a' isVector hp hma hplain s c s₁ s' c' s₁' h h'
  have hma' : NoMustAlias a' := fun x hx => hma x (hp.symm.mem_iff.mp hx)
  have hplain' : PlainArgs L a' := fun he x hx => hplain he x (hp.symm.mem_iff.mp hx)
  rw [unionsplitcost_capped n E L a isVector hma hplain s c s₁ h,
    unionsplitcost_capped n E L a' isVector hma' hplain' s' c' s₁' h']
  exact costCapped_perm (hp.map _)

/-- Shrinking unions never raises the cost: if each argument of `a'` is a `Union` with at most
as many members as the matching argument of `a` (a non-`Union` counting as 1), the cost of `a'`
is at most that of `a`. So `is_union_split_eligible` stays true for `a'` whenever it is true for
`a` and `a'` still has a `Union` argument (`Compiler/src/abstractinterpretation.jl:395-397`). -/
def UnionsplitcostMonotone : Prop :=
  ∀ n E L (a a' : List LElt) isVector, NoMustAlias a → PlainArgs L a → NoMustAlias a' →
    PlainArgs L a' → PwLe (costLens a') (costLens a) →
    ∀ s c s₁ s' c' s₁', (unionsplitcost n E L a isVector none).run s = .ok (c, s₁) →
      (unionsplitcost n E L a' isVector none).run s' = .ok (c', s₁') → c' ≤ c

theorem unionsplitcostMonotone_proven : UnionsplitcostMonotone := by
  intro n E L a a' isVector hma hplain hma' hplain' hle s c s₁ s' c' s₁' h h'
  rw [unionsplitcost_capped n E L a isVector hma hplain s c s₁ h,
    unionsplitcost_capped n E L a' isVector hma' hplain' s' c' s₁' h']
  exact costCapped_mono hle

end JuliaLean.Proofs.Compiler.src.typeutils
