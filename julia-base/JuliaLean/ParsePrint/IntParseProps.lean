import JuliaLean.ParsePrint.IntParse

/-!
Properties of integer parsing (`base/parse.jl`, `base/parsers/ints.jl`).
-/

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

theorem map_ok {α β ε : Type} (f : α → β) {e : Except ε α} (h : ∃ r, e = .ok r) :
    ∃ r, e.map f = .ok r := by
  obtain ⟨r, hr⟩ := h
  exact ⟨f r, by rw [hr]; rfl⟩

theorem slowPath_ok (t : IntTy) (s : Bytes) (j : Int) :
    ∀ pre, ∃ r, slowPath t s j pre = .ok r
  | (sgn, b, d) => by
    simp only [slowPath]
    by_cases hc : sgn ≠ 0 ∧ 2 ≤ b ∧ b ≤ 62 ∧ d ≠ 0
    · rw [if_pos hc]
      exact map_ok _ (parseint_ok _ _ _ _ _ _ hc.2.1 hc.2.2.1)
    · rw [if_neg hc]
      exact ⟨_, rfl⟩

theorem parseintUtf8Core_ok (t : IntTy) (s : Bytes) (i j base : Int) :
    ∃ r, parseintUtf8Core t s i j base = .ok r := by
  unfold parseintUtf8Core
  by_cases hf : fastCond t s i j base
  · rw [if_pos hf]
    exact map_ok _ (parseint_ok _ _ _ _ _ _ (by decide) (by decide))
  · rw [if_neg hf]
    exact slowPath_ok t s j _

/-- `tryparse(T, s; base)` returns `nothing` exactly when `parse(T, s; base)` throws,
and otherwise both return the same value (`base/parse.jl:241-254`), for every
`BitInteger` type, every byte string and every valid `base` (or none). -/
def TryparseNothingIffParseThrows : Prop := ∀ (t : IntTy) (s : Bytes) (base : Option Int),
  (∀ b, base = some b → 2 ≤ b ∧ b ≤ 62) →
  (tryparse t s base = .ok none ∧ ∃ e, parse t s base = .error e) ∨
    ∃ v, tryparse t s base = .ok (some v) ∧ parse t s base = .ok v

theorem tryparseNothingIffParseThrows : TryparseNothingIffParseThrows := by
  intro t s base hbase
  have hvb : ∃ b, validBase base = .ok b := by
    cases base with
    | none => exact ⟨0, rfl⟩
    | some b =>
      obtain ⟨h1, h2⟩ := hbase b rfl
      exact ⟨b, by simp [validBase, h1, h2]; rfl⟩
  obtain ⟨b, hb⟩ := hvb
  obtain ⟨r, hr⟩ := parseintUtf8Core_ok t s 1 (ncu s) b
  cases r with
  | inl v =>
    right
    refine ⟨v, ?_, ?_⟩ <;>
      simp [tryparse, parse, parseintUtf8, hb, hr, bind, Except.bind, pure, Except.pure]
  | inr f =>
    left
    refine ⟨?_, ?_⟩
    · simp [tryparse, parseintUtf8, hb, hr, bind, Except.bind, pure, Except.pure]
    · simp only [parse, parseintUtf8, hb, hr, bind, Except.bind, if_true]
      cases throwParseintError t s (ncu s) f.sgn f.base f.d with
      | error e => exact ⟨e, rfl⟩
      | ok e => exact ⟨e, rfl⟩

end JuliaLean.ParsePrint.IntParse
