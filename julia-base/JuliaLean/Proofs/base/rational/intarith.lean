import JuliaLean.base.rational
import JuliaLean.Registry.Types

namespace JuliaLean.IntArith.Rational

open JuliaLean
open JuliaLean.IntArith.Checked

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- Normalized representation: nonnegative denominator and coprime components. -/
def Normalized {t} (x : Rat t) : Prop :=
  0 ≤ x.den.val ∧ Nat.gcd x.num.val.natAbs x.den.val.natAbs = 1

instance {t} (x : Rat t) : Decidable (Normalized x) :=
  inferInstanceAs (Decidable (0 ≤ x.den.val ∧ Nat.gcd x.num.val.natAbs x.den.val.natAbs = 1))

/-- Infinity minus a finite unsigned rational preserves infinity. -/
def InfinitySub : Prop := ∀ (t : IntTy) (x y : Rat t),
  Normalized x → Normalized y → x.num.val > 0 → x.den.val = 0 → y.den.val > 0 →
  sub x y = .ok x

private def unsignedInf : Rat .u8 := ⟨JInt.lit .u8 1, JInt.lit .u8 0⟩
private def unsignedOne : Rat .u8 := ofInt (JInt.lit .u8 1)

theorem infinitySub_refuted : ¬ InfinitySub := by
  intro h
  have bad := h .u8 unsignedInf unsignedOne (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have actual : sub unsignedInf unsignedOne = .error (.overflowError "") := by decide
  rw [actual] at bad
  cases bad

/-- If the reduced, positive-denominator representation fits T, constructing
from wider integer components succeeds. -/
def NormalizeBeforeConvert : Prop := ∀ (t s : IntTy) (n d : JInt s) (x : Rat t),
  Normalized x → x.den.val > 0 → d.val ≠ 0 →
  n.val * x.den.val = x.num.val * d.val → construct t n d = .ok x

theorem normalizeBeforeConvert_refuted : ¬ NormalizeBeforeConvert := by
  intro h
  have bad := h .i8 .i16 (JInt.lit .i16 128) (JInt.lit .i16 (-1))
    (ofInt (JInt.lit .i8 (-128))) (by decide) (by decide) (by decide) (by decide)
  have actual : construct .i8 (JInt.lit .i16 128) (JInt.lit .i16 (-1)) =
      .error (.inexactError "Int8") := by decide +kernel
  rw [actual] at bad
  cases bad

/-- Every integer-target rounding mode rejects zero-denominator rationals. -/
def InfiniteRoundingRejected : Prop := ∀ (t target : IntTy) (x : Rat t) (mode : Rounding),
  x.den.val = 0 → round target x mode = .error .divideError

theorem infiniteRoundingRejected_proven : InfiniteRoundingRejected := by
  intro t target x mode h
  cases mode <;> simp [round, roundedDiv, JInt.div, JInt.fld, JInt.cld, h,
    Bind.bind, Except.bind]

/-- Truncation of every finite normalized rational is the mathematical
truncating quotient, without overflow, for all ten component types. -/
def TruncExact : Prop := ∀ (t : IntTy) (x : Rat t),
  0 < x.den.val → ∃ z, trunc t x = .ok z ∧ z.val = x.num.val.tdiv x.den.val

theorem truncExact_proven : TruncExact := by
  intro t x hd
  have hz : t.min ≤ 0 ∧ 0 ≤ t.max := by cases t <;> decide
  have hb : t.min ≤ x.num.val.tdiv x.den.val ∧ x.num.val.tdiv x.den.val ≤ t.max := by
    have hn := x.num.property
    by_cases hs : 0 ≤ x.num.val
    · have hlo := Int.tdiv_le_tdiv hd hs
      have hhi := Int.tdiv_le_self x.den.val hs
      simp only [Int.zero_tdiv] at hlo
      omega
    · have hlo := Int.tdiv_le_self x.den.val (by omega : 0 ≤ -x.num.val)
      rw [Int.neg_tdiv] at hlo
      have hhi := Int.tdiv_le_tdiv hd (by omega : x.num.val ≤ 0)
      simp only [Int.zero_tdiv] at hhi
      omega
  let z : JInt t := ⟨x.num.val.tdiv x.den.val, hb⟩
  refine ⟨z, ?_, rfl⟩
  have hw : JInt.wrap t (x.num.val.tdiv x.den.val) = z := by
    apply Subtype.ext
    exact wrapInt_of_inRange t _ hb
  have he : ¬ (t.signed = true ∧ x.num.val = t.min ∧ x.den.val = -1) := by omega
  simp [trunc, round, roundedDiv, JInt.div, Int.ne_of_gt hd, he, hw, JInt.convert, hb, z,
    Bind.bind, Except.bind]

/-- A successful arithmetic result is normalized and represents the specified
exact ratio. Infinite results must carry the numerator's sign. -/
private def exactResult (r : Jl (Rat .i8)) (n d : Int) : Bool :=
  match r with
  | .error _ => false
  | .ok z => decide (Normalized z ∧ z.num.val * d = n * z.den.val ∧
      (d = 0 → z.den.val = 0 ∧ 0 < z.num.val * n))

/-- Finite input grid includes negative and zero numerators and nontrivial
cross gcds. The reference calculations use mathematical integers only. -/
private def smallArithmeticCase (a b c d : Fin 4) : Bool :=
  match ofInts (JInt.lit .i8 ((a.val : Int) - 2)) (JInt.lit .i8 ((b.val : Int) + 1)),
      ofInts (JInt.lit .i8 ((c.val : Int) - 2)) (JInt.lit .i8 ((d.val : Int) + 1)) with
  | .ok x, .ok y =>
    let crossX := x.num.val * y.den.val
    let crossY := y.num.val * x.den.val
    exactResult (add x y) (crossX + crossY) (x.den.val * y.den.val) &&
    exactResult (sub x y) (crossX - crossY) (x.den.val * y.den.val) &&
    exactResult (mul x y) (x.num.val * y.num.val) (x.den.val * y.den.val) &&
    (if x.num.val = 0 ∧ y.num.val = 0 then decide (div x y = .error .divideError)
     else exactResult (div x y) crossX (x.den.val * y.num.val)) &&
    decide (lt x y = decide (crossX < crossY)) &&
    decide (eq x y = decide (crossX = crossY))
  | _, _ => false

/-- Exact arithmetic and order for all 256 pairs of finite rationals generated
by numerators -2..1 and denominators 1..4, including unreduced inputs. -/
def SmallArithmetic : Prop := ∀ a b c d : Fin 4, smallArithmeticCase a b c d = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem smallArithmetic_proven : SmallArithmetic := by
  unfold SmallArithmetic
  decide +kernel

/-- Whole-rational conversion errors occur before addition or subtraction
arithmetic, including the infinity shortcuts. -/
def MixedConversionFirst : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s) (e : JlError),
  convertRat (t.promote s) x = .error e →
  addMixed x y = .error e ∧ subMixed x y = .error e

theorem mixedConversionFirst_proven : MixedConversionFirst := by
  intro t s x y e h
  simp [addMixed, subMixed, h, Bind.bind, Except.bind]

def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.Rational
