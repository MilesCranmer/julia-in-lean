import JuliaLean.ParsePrint.IntBoundary1
import JuliaLean.ParsePrint.IntBoundary2
import JuliaLean.ParsePrint.IntBoundary3
import JuliaLean.ParsePrint.IntBoundary4
import JuliaLean.ParsePrint.IntBoundary5
import JuliaLean.ParsePrint.IntBoundary6

/-! Overflow detection in integer parsing near every wrap-around point. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

/-- `parse(T, s; base=b)` of the spelling of `m` returns `m` when it fits in `T` and
throws otherwise; in particular it never returns a wrapped value.
`base/parsers/ints.jl:150-173` checks every multiply-add for overflow of the
accumulator and the final magnitude against `typemax(T) + neg`. -/
def ParseSpecHolds (t : IntTy) (b : Nat) (m : Int) : Prop :=
  (t.min ≤ m ∧ m ≤ t.max → parse t (intStr b m) (some b) = .ok (JInt.lit t m)) ∧
  (¬ (t.min ≤ m ∧ m ≤ t.max) → ∃ e, parse t (intStr b m) (some b) = .error e)

/-- For every `BitInteger` type `T`, base 10 or 16, and every integer within 16 of
`typemin(T)`, `typemax(T)`, `±2^64` or `±2^128`, overflow is detected exactly. -/
def ParseOverflowDetected : Prop := ∀ (t : IntTy) (b : Nat), (b = 10 ∨ b = 16) →
  ∀ c ∈ centers t, ∀ k : Nat, k ≤ 32 → ParseSpecHolds t b (c + k - 16)

theorem parseSpec_sound (t : IntTy) (b : Nat) (m : Int) (h : parseSpec t b m = true) :
    ParseSpecHolds t b m := by
  unfold parseSpec at h
  cases hp : parse t (intStr b m) (some b) with
  | error e =>
    simp only [hp, Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact ⟨fun hr => absurd hr h, fun _ => ⟨e, hp⟩⟩
  | ok v =>
    simp only [hp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hr, hv⟩ := h
    refine ⟨fun _ => ?_, fun hn => absurd hr hn⟩
    rw [hp]
    congr 1
    apply Subtype.ext
    rw [hv]
    simp only [JInt.lit, JInt.wrap]
    exact (wrapInt_of_inRange t m hr).symm

theorem parseOverflowDetected : ParseOverflowDetected := by
  intro t b hb c hc k hk
  apply parseSpec_sound
  have := fun (h : ∀ c ∈ centers t, ∀ k : Fin 33, nearOK t b c k = true) => h c hc ⟨k, by omega⟩
  apply this
  rcases hb with rfl | rfl <;> cases t <;>
    first | exact near_u8_10 | exact near_i8_10 | exact near_u16_10 | exact near_i16_10 | exact near_u32_10 | exact near_i32_10 | exact near_u64_10 | exact near_i64_10 | exact near_u128_10 | exact near_i128_10 | exact near_u8_16 | exact near_i8_16 | exact near_u16_16 | exact near_i16_16 | exact near_u32_16 | exact near_i32_16 | exact near_u64_16 | exact near_i64_16 | exact near_u128_16 | exact near_i128_16

end JuliaLean.ParsePrint.IntParse
