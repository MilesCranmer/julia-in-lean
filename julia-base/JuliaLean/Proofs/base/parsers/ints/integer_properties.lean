import JuliaLean.base.parsers.ints

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.IntArith.Checked

theorem wrap_base_val {u : IntTy} (hu : u = .u64 ∨ u = .u128) {base : Int}
    (hb : 2 ≤ base) (hb2 : base ≤ 62) : (JInt.wrap u base).val = base := by
  rcases hu with rfl | rfl <;>
    simp only [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true, ite_false] <;>
    omega

theorem mulWithOverflow_ok {u : IntTy} (hu : u = .u64 ∨ u = .u128) (x y : JInt u)
    (hy : 0 < y.val) : ∃ r, mulWithOverflow x y = .ok r := by
  rcases hu with rfl | rfl
  · exact ⟨_, rfl⟩
  · have hy0 : y.val ≠ 0 := by omega
    simp [mulWithOverflow, hy, JInt.fld, JInt.div, hy0, IntTy.signed, bind, Except.bind,
      pure, Except.pure]

theorem checkedLoop_ok {u : IntTy} (hu : u = .u64 ∨ u = .u128) (t : IntTy) (buf : Bytes)
    (j base : Int) (hb : 2 ≤ base) (hb2 : base ≤ 62) :
    ∀ (f : Nat) (s : JInt u × Int), ∃ r, checkedLoop t buf j base f s = .ok r
  | 0, (n, _) => ⟨_, rfl⟩
  | f+1, (n, i) => by
    simp only [checkedLoop]
    split
    · split
      · exact ⟨_, rfl⟩
      · obtain ⟨⟨n', ov⟩, hm⟩ := mulWithOverflow_ok hu n (JInt.wrap u base)
          (by rw [wrap_base_val hu hb hb2]; omega)
        simp only [hm, bind, Except.bind]
        split
        · exact ⟨_, rfl⟩
        · exact checkedLoop_ok hu t buf j base hb hb2 f _
    · exact ⟨_, rfl⟩

theorem uTy_cases (t : IntTy) : uTy t = .u64 ∨ uTy t = .u128 := by
  unfold uTy; split <;> simp

theorem parseint_ok (t : IntTy) (buf : Bytes) (i j base : Int) (neg : Bool)
    (hb : 2 ≤ base) (hb2 : base ≤ 62) : ∃ r, parseint t buf i j base neg = .ok r := by
  unfold parseint
  by_cases hij : i ≤ j
  · simp only [hij, not_true_eq_false, ite_false]
    cases safePrefix t buf i j base with
    | none => exact ⟨_, rfl⟩
    | some s =>
      obtain ⟨r, hr⟩ := checkedLoop_ok (uTy_cases t) t buf j base hb hb2 (buf.length + 1) s
      simp only [hr, bind, Except.bind]
      cases r with
      | inr r => exact ⟨_, rfl⟩
      | inl n =>
        by_cases hc : n.val ≤ (JInt.rem (uTy t) (JInt.typemax t) + ofBool (uTy t) neg).val
        · exact ⟨_, by dsimp only; rw [if_pos hc]; rfl⟩
        · exact ⟨_, by dsimp only; rw [if_neg hc]; rfl⟩
  · simp only [hij, not_false_eq_true, ite_true]
    exact ⟨_, rfl⟩

end JuliaLean.ParsePrint.IntParse
