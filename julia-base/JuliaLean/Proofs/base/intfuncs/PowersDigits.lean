import JuliaLean.base.intfuncs
import JuliaLean.Registry.Types
import JuliaLean.base.float
import JuliaLean.base.checked

namespace JuliaLean.IntArith.PowersDigits

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)









def NextpowLowerBound : Prop := ∀ (t : IntTy) (x r : JInt t),
  0 < x.val → nextpow x = .ok r → x.val ≤ r.val

theorem nextpowLowerBound_refuted : ¬ NextpowLowerBound := by
  intro h
  have bad := h .i8 (JInt.lit .i8 65) (JInt.lit .i8 (-128)) (by decide) (by decide)
  have : ¬ ((JInt.lit .i8 65).val ≤ (JInt.lit .i8 (-128)).val) := by decide
  exact this bad

def NegativeBaseSingleDigit : Prop := ∀ (bty : IntTy) (b : JInt bty) (x : JInt .u8),
  b.val < -1 → 0 < x.val → x.val < -b.val →
  ndigits0z x b = .ok (JInt.lit .i64 1)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem negativeBaseSingleDigit_refuted : ¬ NegativeBaseSingleDigit := by
  intro h
  have bad := h .i8 (JInt.lit .i8 (-128)) (JInt.lit .u8 1)
    (by decide) (by decide) (by decide)
  have : ndigits0z (JInt.lit .u8 1) (JInt.lit .i8 (-128)) ≠ .ok (JInt.lit .i64 1) := by decide
  exact this bad

def LargeBaseSingleDigit : Prop := ∀ (t bty : IntTy) (x : JInt t) (b : JInt bty),
  b.val > 1 → 0 < x.val → x.val < b.val →
  ndigits0z x b = .ok (JInt.lit .i64 1)

theorem largeBaseSingleDigit_refuted : ¬ LargeBaseSingleDigit := by
  intro h
  have bad := h .i64 .i128 (JInt.lit .i64 1) (JInt.lit .i128 9223372036854775808)
    (by decide) (by decide) (by decide)
  have : ndigits0z (JInt.lit .i64 1) (JInt.lit .i128 9223372036854775808) ≠
      .ok (JInt.lit .i64 1) := by decide
  exact this bad

/-- The documented square-root inequality uses exact mathematical products,
so it cannot be satisfied accidentally by wrapping integer multiplication. -/
def IsqrtUInt8 : Prop := ∀ n : Fin 256,
  (match isqrt (JInt.lit .u8 n.val) with
  | .error _ => false
  | .ok r => decide (r.val * r.val ≤ (n.val : Int) ∧
      (n.val : Int) < (r.val + 1) * (r.val + 1))) = true

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 2048 in
theorem isqrtUInt8 : IsqrtUInt8 := by unfold IsqrtUInt8; decide

/-- The integer correction must recover the mathematically smallest power
from a seed at most one exponent away, provided its three computed powers
have not wrapped. The numerical log implementation is an external input. -/
def NextpowSeedCorrection : Prop :=
  ∀ (aty xty : IntTy) (a : JInt aty) (x : JInt xty)
    (n : JInt64) (k : Nat) (p wp wwp : JInt aty),
  a.val > 2 → x.val > 1 → x.val ≤ aty.max → 0 < n.val →
  (n.val + 1 = (k : Int) ∨ n.val = (k : Int) ∨ n.val = (k : Int) + 1) →
  powerBySquaring a (n - JInt.lit .i64 1) = .ok p →
  powerBySquaring a n = .ok wp →
  powerBySquaring a (n + JInt.lit .i64 1) = .ok wwp →
  p.val = a.val ^ (n.val - 1).toNat →
  wp.val = a.val ^ n.val.toNat →
  wwp.val = a.val ^ (n.val + 1).toNat →
  p.val < wp.val → wp.val < wwp.val →
  (∀ j : Nat, j < k → a.val ^ j < x.val) →
  x.val ≤ a.val ^ k →
  ∃ r : JInt aty, nextpowFromLog a x n = .ok ⟨aty,r⟩ ∧ r.val = a.val ^ k

theorem nextpowSeedCorrection : NextpowSeedCorrection := by
  intro aty xty a x n k p wp wwp ha hx hr hn hoff hp hw hww ep ew eww hlt hlt' hmin hupper
  have ha2 : a.val ≠ 2 := by omega
  have ha1 : ¬ a.val ≤ 1 := by omega
  have hx0 : ¬ x.val ≤ 0 := by omega
  have hx1 : ¬ x.val ≤ 1 := by omega
  have hr' : ¬ x.val > aty.max := by omega
  have hwp : ¬ wp.val ≤ p.val := by omega
  have hwwp : ¬ wwp.val ≤ wp.val := by omega
  rcases hoff with hoff | hoff | hoff
  · have ei : n.val.toNat < k := by omega
    have ej : (n.val + 1).toNat = k := by omega
    have below : wp.val < x.val := by rw [ew]; exact hmin _ ei
    have belowp : ¬ x.val ≤ p.val := by omega
    have belowwp : ¬ x.val ≤ wp.val := by omega
    have target : wwp.val = a.val ^ k := by simpa [ej] using eww
    refine ⟨wwp, ?_, target⟩
    simp [nextpowFromLog, ha2, ha1, hx0, hx1, hr', hp, hw, hww,
      belowp, belowwp, hwp, hwwp, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have ei : (n.val - 1).toNat < k := by omega
    have ej : n.val.toNat = k := by omega
    have below : p.val < x.val := by rw [ep]; exact hmin _ ei
    have belowp : ¬ x.val ≤ p.val := by omega
    have target : wp.val = a.val ^ k := by simpa [ej] using ew
    have upper : x.val ≤ wp.val := by simpa [target] using hupper
    refine ⟨wp, ?_, target⟩
    simp [nextpowFromLog, ha2, ha1, hx0, hx1, hr', hp, hw,
      belowp, upper, hwp, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have ej : (n.val - 1).toNat = k := by omega
    have target : p.val = a.val ^ k := by simpa [ej] using ep
    have upper : x.val ≤ p.val := by simpa [target] using hupper
    refine ⟨p, ?_, target⟩
    simp [nextpowFromLog, ha2, ha1, hx0, hx1, hr', hp, upper,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Settled documentation claims and the exact three-candidate correction
contract. The numerical log seed remains an explicit external dependency. -/
def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.PowersDigits
