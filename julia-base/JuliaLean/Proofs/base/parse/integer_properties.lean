import JuliaLean.base.parse
import JuliaLean.Proofs.base.parsers.ints.integer_properties

/-!
Properties of integer parsing (`base/parse.jl`, `base/parsers/ints.jl`).
-/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.IntArith.Checked


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
