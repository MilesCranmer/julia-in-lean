import JuliaLean.Proofs.Compiler.src.typeutils.Full

/-!
`unionsplitcost` (`Compiler/src/typeutils.jl:285-316`) with alias groups and with the arguments it
widens first.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- Position `i` (1-based) leads its alias group: `groups === nothing || groups[i] == i`. -/
def isLeader (g : Option (Array Nat)) (i : Nat) : Bool :=
  match g with
  | some g => g[i - 1]! == i
  | none => true

/-- What the loop of `unionsplitcost` reads at position `j + 1`: nothing for a follower
(`Compiler/src/typeutils.jl:298-301`); for a leader, the `unionlen` of the argument, after
`widenconst_split` on a lattice with extended union splitting unless it is a `Vararg`
(lines 302-307); `none` for a non-`Union`. -/
def CostOptAt (n : Nat) (E : CEnv) (L : Lattice) (g : Option (Array Nat)) (argtypes : List LElt)
    (j : Nat) (o : Option Nat) : Prop :=
  ∃ a, argtypes[j]? = some a ∧
    (isLeader g (j + 1) = false → o = none) ∧
    (isLeader g (j + 1) = true → (hasExtendedUnionsplit L && !a.isVarargElt) = true →
      ∃ w s₁ s₂, (widenconstSplit n E a).run s₁ = .ok (w, s₂) ∧ o = unionLenOf (.ty w)) ∧
    (isLeader g (j + 1) = true → (hasExtendedUnionsplit L && !a.isVarargElt) = false →
      o = unionLenOf a)

theorem costLoop_none_cons (p : Int × Nat) (xs : List (Option Nat)) :
    costLoop p (none :: xs) = costLoop p xs := rfl

/-- The loop of `unionsplitcost`, when each step reads some `o` with `P`: it computes `costLoop` of
the values read, and stops early (with `typemax(Int)`) only on overflow. -/
theorem forIn_cost_ex (P : Nat → Option Nat → Prop) :
    ∀ (m k : Nat) (f : Nat → Option Int × Int × Nat → CM (ForInStep (Option Int × Int × Nat))),
    (∀ j, j < m → ∀ nu mx s r s', (f (k + j) (none, nu, mx)).run s = .ok (r, s') →
      ∃ o, P (k + j) o ∧ r = costStepR (nu, mx) o) →
    ∀ nu mx s r s', (forIn (List.range' k m) (none, nu, mx) f).run s = .ok (r, s') →
      ∃ lens : List (Option Nat), lens.length ≤ m ∧ (∀ j (hj : j < lens.length), P (k + j) lens[j]) ∧
        costFinish r = costLoop (nu, mx) lens ∧ (lens.length < m → costFinish r = typemaxInt) := by
  intro m
  induction m with
  | zero =>
    intro k f _ nu mx s r s' h
    cases h
    exact ⟨[], Nat.le_refl 0, fun j hj => absurd hj (Nat.not_lt_zero j), rfl,
      fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ m ih =>
    intro k f hf nu mx s r s' h
    rw [List.range'_succ] at h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    obtain ⟨o, hP, rfl⟩ := hf 0 (Nat.zero_lt_succ m) nu mx s st s₁ (by simpa using h1)
    have hf' : ∀ j, j < m → ∀ nu mx s r s', (f (k + 1 + j) (none, nu, mx)).run s = .ok (r, s') →
        ∃ o, P (k + 1 + j) o ∧ r = costStepR (nu, mx) o := by
      intro j hj nu mx s r s' h
      have := hf (j + 1) (by omega) nu mx s r s' (by rw [show k + (j + 1) = k + 1 + j by omega]; exact h)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    have hP0 : P k o := by simpa using hP
    cases o with
    | none =>
      simp only [costStepR] at h2
      obtain ⟨lens, hl, hP', hc, hlt⟩ := ih (k + 1) f hf' nu mx s₁ r s' h2
      refine ⟨none :: lens, by simp; omega, fun j hj => ?_, by rw [hc]; rfl,
        fun h => hlt (by simp at h; omega)⟩
      cases j with
      | zero => simpa using hP0
      | succ j =>
        have := hP' j (by simp at hj; omega)
        simpa [show k + (j + 1) = k + 1 + j by omega] using this
    | some x =>
      simp only [costStepR] at h2
      by_cases hq : (costStep (nu, mx) x).1 > typemaxInt
      · simp only [hq, if_true] at h2
        obtain ⟨rfl, -⟩ := h2
        refine ⟨[some x], by simp, fun j hj => ?_, ?_, fun _ => rfl⟩
        · have : j = 0 := by simp at hj; omega
          subst this; simpa using hP0
        · simp only [costFinish, costLoop, hq, if_true]
      · simp only [hq, if_false] at h2
        obtain ⟨lens, hl, hP', hc, hlt⟩ := ih (k + 1) f hf' _ _ s₁ r s' h2
        refine ⟨some x :: lens, by simp; omega, fun j hj => ?_, ?_,
          fun h => hlt (by simp at h; omega)⟩
        · cases j with
          | zero => simpa using hP0
          | succ j =>
            have := hP' j (by simp at hj; omega)
            simpa [show k + (j + 1) = k + 1 + j by omega] using this
        · simp only [costLoop, hq, if_false]; exact hc

theorem unionsplitcost_groups (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt)
    (isVector : Bool) (fargs : Option (List FArg)) :
    Returns (unionsplitcost n E L argtypes isVector fargs) (fun c =>
      ∃ g, (∃ s₁ s₂, (computeAliasGroups argtypes.length fargs
          (if isVector then some argtypes else none)).run s₁ = .ok (g, s₂)) ∧
        ∃ lens : List (Option Nat), lens.length ≤ argtypes.length ∧
          (∀ j (hj : j < lens.length), CostOptAt n E L g argtypes j lens[j]) ∧
          c = costLoop (1, 2) lens ∧ (lens.length < argtypes.length → c = typemaxInt)) := by
  intro s r s' h
  unfold unionsplitcost at h
  obtain ⟨g, s₁, hg, h⟩ := run_bind_inv h
  refine ⟨g, ⟨_, _, hg⟩, ?_⟩
  obtain ⟨st, s₂, hst, h⟩ := run_bind_inv h
  have hr : r = costFinish st := by
    unfold costFinish
    cases hs1 : st.1 with
    | some v => simp only [hs1] at h; cases h; rfl
    | none => simp only [hs1] at h; cases h; rfl
  subst hr
  refine forIn_cost_ex (fun i o => CostOptAt n E L g argtypes (i - 1) o) argtypes.length 1 _ ?_ 1 2
    s₁ st s₂ hst |>.imp fun lens ⟨hl, hP, hc, hlt⟩ =>
      ⟨hl, fun j hj => by simpa [Nat.add_comm] using hP j hj, hc, hlt⟩
  intro j hj nu mx s₃ r₃ s₃' h3
  rw [show 1 + j - 1 = j by omega]
  have ha : argtypes[j]? = some argtypes[j] := List.getElem?_eq_getElem hj
  -- The leader's body: read the argument, maybe widen it, and count it.
  have leader : isLeader g (j + 1) = true → ∀ s₄,
      (do
        let ti ← eltAt argtypes (1 + j)
        if (hasExtendedUnionsplit L && !ti.isVarargElt) = true then do
          let w ← widenconstSplit n E ti
          costBody nu mx (.ty w)
        else costBody nu mx ti : CM _).run s₄ = .ok (r₃, s₃') →
      ∃ o, CostOptAt n E L g argtypes j o ∧ r₃ = costStepR (nu, mx) o := by
    intro hlead s₄ h4
    obtain ⟨ti, s₅, hti, h4⟩ := run_bind_inv h4
    rw [Nat.add_comm 1 j, eltAt_run argtypes j hj] at hti
    cases hti
    split at h4
    · rename_i hc
      obtain ⟨w, s₆, hw, h4⟩ := run_bind_inv h4
      exact ⟨_, ⟨_, ha, (fun h => by rw [hlead] at h; cases h),
        (fun _ _ => ⟨w, _, _, hw, rfl⟩), (fun _ h => by rw [hc] at h; cases h)⟩,
        costBody_spec nu mx _ _ _ _ h4⟩
    · rename_i hc
      have hc' : (hasExtendedUnionsplit L && !argtypes[j].isVarargElt) = false := by simpa using hc
      exact ⟨_, ⟨_, ha, (fun h => by rw [hlead] at h; cases h),
        (fun _ h => by rw [hc'] at h; cases h), (fun _ _ => rfl)⟩,
        costBody_spec nu mx _ _ _ _ h4⟩
  cases g with
  | none => exact leader rfl s₃ h3
  | some g' =>
    simp only at h3
    split at h3
    · rename_i hf
      cases h3
      have hl : isLeader (some g') (j + 1) = false := by
        simp only [isLeader, Nat.add_sub_cancel]
        simpa [Nat.add_comm] using hf
      exact ⟨none, ⟨_, ha, (fun _ => rfl), (fun h => by rw [hl] at h; cases h),
        (fun h => by rw [hl] at h; cases h)⟩, rfl⟩
    · rename_i hf
      have hl : isLeader (some g') (j + 1) = true := by
        simp only [isLeader, Nat.add_sub_cancel]
        simpa [Nat.add_comm] using hf
      exact leader hl s₃ h3

end JuliaLean.Proofs.Compiler.src.typeutils
