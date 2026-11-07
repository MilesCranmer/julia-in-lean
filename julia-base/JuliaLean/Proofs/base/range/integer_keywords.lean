import JuliaLean.base.range
import JuliaLean.base.broadcast
import JuliaLean.Registry.Types

namespace JuliaLean.Ranges




/-- Every length-taking `range` form respects a requested nonnegative length
whenever construction succeeds. -/
def KeywordLengthPreserved : Prop :=
  ∀ (a s b : Option Num) (n : Num) (r : ResultRng), 0 ≤ n.val →
    rangeKw a s b (some n) = some (.ok r) →
      match resultLength r with
      | .ok m => m.val = n.val
      | .error _ => False

/-- Dotted scalar addition preserves the number of elements. -/
def BroadcastAddLengthPreserved : Prop :=
  ∀ (a b x : Num) (r : Rng) (s : ResultRng),
    colon2 a b = .ok r → broadcastAdd r x = .ok s →
      (resultLength s).map Num.val = (length r).map Num.val

/-- A negative requested element count is invalid. -/
def NegativeKeywordLengthRejected : Prop :=
  ∀ (a n : Num), n.val < 0 →
    ∃ e, rangeStartLength a n = .error e

/-- The documented modulus result is congruent to its input modulo the range count. -/
def ModRangeCongruence : Prop :=
  ∀ (a b i : Num) (r : Rng), colon2 a b = .ok r →
    0 < trueCount r →
      match modRange i r with
      | .ok y => (i.val - y.val) % trueCount r = 0
      | .error _ => False

/-- Broadcast `r .* x` has the elements `r[i] * x` of the elementwise broadcast. -/
def BroadcastMulElementwise : Prop :=
  ∀ (a b x i : Num) (r : Rng) (s : ResultRng),
    colon2 a b = .ok r → broadcastMul r x = .ok s →
    i.ty = .bit .i64 → 1 ≤ i.val → i.val ≤ trueCount r →
      (resultGetindex s i).map Num.val = (getindex r i).map (fun y => (Num.mul y x).val)

/-- The `range_error` hint never names an argument the caller supplied as missing. -/
def RangeErrorHintAccurate : Prop :=
  ∀ (a s b n : Option Num) (msg : String),
    rangeKw a s b n = some (.error (.argumentError msg)) →
      (msg = "At least one of `length` or `stop` must be specified." → b = none ∧ n = none) ∧
      (msg = "At least one of `length` or `step` must be specified." → s = none ∧ n = none) ∧
      (msg = "At least one of `start` or `stop` must be specified." → a = none ∧ b = none)

/-- `range` docstring, base/range.jl:159-161: integer `stop` and `length` alone
produce a `UnitRange`. -/
def StopLengthGivesUnitRange : Prop :=
  ∀ (b n : Num) (r : ResultRng), b.ty ≠ .bool → n.ty ≠ .bool →
    rangeKw none none (some b) (some n) = some (.ok r) →
      ∃ u : Rng, r = .ordinal u ∧ u.kind = .unit

private def i8 (x : Int) : Num := Num.lit (.bit .i8) x
private def i64 (x : Int) : Num := Num.lit (.bit .i64) x
private def empty127 : Rng := ⟨.unit, i8 127, i8 1, i8 126⟩
private def pair126 : Rng := ⟨.unit, i8 126, i8 1, i8 127⟩

set_option maxRecDepth 4096 in
theorem keywordLength_refuted : ¬ KeywordLengthPreserved := by
  intro h
  have bad := h (some (i64 9223372036854775806)) none none (i64 5)
    (.ordinal ⟨.unit, i64 9223372036854775806, i64 1, i64 9223372036854775805⟩)
    (by decide) rfl
  change (0 : Int) = 5 at bad
  omega

set_option maxRecDepth 4096 in
theorem broadcastAddLength_refuted : ¬ BroadcastAddLengthPreserved := by
  intro h
  have bad := h (i8 126) (i8 127) (i8 1) pair126 (.ordinal empty127)
    (by decide) (by decide)
  change (Except.ok (0 : Int) : Jl Int) = .ok 2 at bad
  cases bad

set_option maxRecDepth 4096 in
theorem negativeKeywordLength_refuted : ¬ NegativeKeywordLengthRejected := by
  intro h
  obtain ⟨e, bad⟩ := h (i64 1) (i64 (-1)) (by decide)
  have actual : rangeStartLength (i64 1) (i64 (-1)) =
      .ok (.ordinal ⟨.unit, i64 1, i64 1, i64 0⟩) := by decide
  rw [actual] at bad
  cases bad

set_option maxRecDepth 4096 in
theorem modRangeCongruence_refuted : ¬ ModRangeCongruence := by
  intro h
  have bad := h (i64 1) (i64 3) (i64 (-9223372036854775808))
    ⟨.unit, i64 1, i64 1, i64 3⟩ (by decide) (by decide)
  change ((-9223372036854775808 : Int) - 2) % 3 = 0 at bad
  have : ((-9223372036854775808 : Int) - 2) % 3 ≠ 0 := by decide
  exact this bad

set_option maxRecDepth 4096 in
theorem broadcastMulElementwise_refuted : ¬ BroadcastMulElementwise := by
  intro h
  have bad := h (i8 1) (i8 3) (i8 64) (i64 2) ⟨.unit, i8 1, i8 1, i8 3⟩
    (.counted ⟨i8 64, i8 64, i64 3, i64 1, .bit .i8⟩) rfl rfl rfl (by decide) (by decide)
  change (Except.error (JlError.inexactError "Int8") : Jl Int) = .ok (-128) at bad
  cases bad

theorem rangeErrorHintAccurate_refuted : ¬ RangeErrorHintAccurate := by
  intro h
  have bad := ((h none (some (i64 1)) none (some (i64 3))
    "At least one of `length` or `stop` must be specified." rfl).1 rfl).2
  cases bad

theorem stopLengthGivesUnitRange_refuted : ¬ StopLengthGivesUnitRange := by
  intro h
  obtain ⟨u, hu, _⟩ := h (Num.lit (.bit .u64) 10) (i64 5)
    (.counted ⟨Num.lit (.bit .u64) 6, Num.lit (.bit .u64) 1, i64 5, i64 1, .bit .u64⟩)
    (by decide) (by decide) rfl
  cases hu

open JuliaLean.Registry

def keywordEntries : List Entry := []

end JuliaLean.Ranges
