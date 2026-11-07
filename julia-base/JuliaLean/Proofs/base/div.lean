import JuliaLean.Proofs.base.div.IntArithDivision
import JuliaLean.base.math
import JuliaLean.base.floatfuncs
import JuliaLean.base.number
import JuliaLean.base.operators
import JuliaLean.base.div
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.int

/-!
# Properties of `base/div.jl`

These statements give the documented integer quotient, remainder, division-error, and wrapper
contracts for every `BitInteger` width. The expected quotient uses exact mathematical integers,
while the tested methods are the source models in `JuliaLean.base.div` instantiated with
`JuliaLean.base.int` operations.
-/

namespace JuliaLean.Proofs.base.div

open JuliaLean
open JuliaLean.base.div
open JuliaLean.base.float
open JuliaLean.Registry
open JuliaLean.JInt

private def absInt (x : Int) : Int := if x < 0 then -x else x

private def sameSign (x y : Int) : Bool := (x < 0) = (y < 0)

private def awayFromZero (x y q : Int) : Int :=
  q + if sameSign x y then 1 else -1

/-- Exact mathematical quotient rounding for integer inputs; division by zero is excluded by the
specifications below. -/
def roundedIntegerQuotient (x y : Int) (mode : RoundingMode) : Int :=
  if y = 0 then 0 else
    let q := x.tdiv y
    let r := x.tmod y
    match mode with
    | .ToZero => q
    | .Down => x.fdiv y
    | .Up => -((-x).fdiv y)
    | .FromZero => if sameSign x y then -((-x).fdiv y) else x.fdiv y
    | .Nearest | .NearestTiesAway | .NearestTiesUp =>
        let twiceRemainder := 2 * absInt r
        let divisorMagnitude := absInt y
        if twiceRemainder > divisorMagnitude then awayFromZero x y q
        else if twiceRemainder < divisorMagnitude then q
        else if mode = .Nearest then
          if q.tmod 2 = 0 then q else awayFromZero x y q
        else if mode = .NearestTiesAway then awayFromZero x y q
        else if sameSign x y then awayFromZero x y q else q

private def divisionError {t : IntTy} (x y : JInt t) : Prop :=
  y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1)

private def remainderError {t : IntTy} (x y : JInt t) (mode : RoundingMode) : Prop :=
  y.val = 0 ∨
    (t.signed = true ∧ x.val = t.min ∧ y.val = -1 ∧
      (mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp))

/-- `div` returns the mathematical quotient rounded in the requested mode, or `DivideError` for
zero divisors and signed `typemin / -1`, for every `BitInteger` type. -/
def BitIntegerDivisionCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    (divisionError x y → divBitIntegerMode x y mode = .error .divideError) ∧
    (¬ divisionError x y →
      ∃ q : JInt t,
        divBitIntegerMode x y mode = .ok q ∧
        q.val = roundedIntegerQuotient x.val y.val mode)

/-- `rem` is the exact dividend minus divisor times the quotient rounded in the selected mode;
zero divisors and nearest-mode signed `typemin / -1` raise `DivideError`. -/
def BitIntegerRemainderCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    (remainderError x y mode → remBitIntegerMode x y mode = .error .divideError) ∧
    (¬ remainderError x y mode →
      ∃ r : JInt t,
        remBitIntegerMode x y mode = .ok r ∧
        r.val = x.val - y.val * roundedIntegerQuotient x.val y.val mode)

/-- The documented `divrem` pair agrees with separate `div` and `rem` calls for all seven Julia
rounding modes, with errors preserved. -/
def BitIntegerDivremProjection : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    divremBitIntegerMode x y mode = do
      let q ← divBitIntegerMode x y mode
      let r ← remBitIntegerMode x y mode
      pure (q, r)

/-- `divrem` returns the correctly rounded quotient and exact remainder at every fixed-width
integer width, or preserves `DivideError` for invalid divisions. -/
def BitIntegerDivremCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    (divisionError x y →
      divremBitIntegerMode x y mode = .error .divideError) ∧
    (¬ divisionError x y →
      ∃ q r : JInt t,
        divremBitIntegerMode x y mode = .ok (q, r) ∧
        q.val = roundedIntegerQuotient x.val y.val mode ∧
        r.val = x.val - y.val * q.val)

/-- Truncating, floored, ceiled, and nearest integer division return the exact rounded quotient at
every `BitInteger` width; `fld1` retains its documented `cld` result. -/
def BitIntegerFloorCeilingCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    (divisionError x y →
      fldBitInteger x y = .error .divideError ∧
      cldBitInteger x y = .error .divideError ∧
      fld1BitInteger x y = .error .divideError) ∧
    (¬ divisionError x y →
      ∃ f c : JInt t,
        fldBitInteger x y = .ok f ∧ f.val = x.val.fdiv y.val ∧
        cldBitInteger x y = .ok c ∧ c.val = -((-x.val).fdiv y.val) ∧
        fld1BitInteger x y = .ok c)

/-- `fldmod` returns the same floored quotient and modulo as its documented `(fld, mod)` pair,
including `DivideError` at zero and signed `typemin / -1`. -/
def BitIntegerFldmodCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    fldmodBitInteger x y = do
      let q ← fldBitInteger x y
      let r ← (if t.signed then JuliaLean.base.int.mod_BitSigned fldBitInteger x y
               else JuliaLean.base.int.mod_Unsigned x y)
      pure (q, r)

/-- Division and `divrem` raise `DivideError` for every zero divisor and for signed
`typemin / -1`; truncating, floored, ceiled, and directed remainder retain their documented
zero-remainder behavior at `typemin / -1`. -/
def BitIntegerDivisionErrorCases : Prop :=
  (∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    y.val = 0 →
      divBitIntegerMode x y mode = .error .divideError ∧
      remBitIntegerMode x y mode = .error .divideError ∧
      divremBitIntegerMode x y mode = .error .divideError ∧
      fldBitInteger x y = .error .divideError ∧
      cldBitInteger x y = .error .divideError ∧
      fldmodBitInteger x y = .error .divideError) ∧
  (∀ (t : IntTy) (x y : JInt t),
    t.signed = true → x.val = t.min → y.val = -1 →
      (∀ mode, divBitIntegerMode x y mode = .error .divideError ∧
        divremBitIntegerMode x y mode = .error .divideError) ∧
      fldBitInteger x y = .error .divideError ∧
      cldBitInteger x y = .error .divideError ∧
      fldmodBitInteger x y = .error .divideError ∧
      remBitIntegerMode x y .ToZero = .ok (JuliaLean.base.int.lit t 0) ∧
      remBitIntegerMode x y .Down = .ok (JuliaLean.base.int.lit t 0) ∧
      remBitIntegerMode x y .Up = .ok (JuliaLean.base.int.lit t 0) ∧
      remBitIntegerMode x y .FromZero = .ok (JuliaLean.base.int.lit t 0) ∧
      (∀ mode, mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp →
        remBitIntegerMode x y mode = .error .divideError))

private def remainderValuesAgree {q r m : IntTy}
    (pair : JuliaLean.Jl (JInt q × JInt r)) (modValue : JuliaLean.Jl (JInt m)) : Prop :=
  ∀ (quotient : JInt q) (remainder : JInt r) (modulus : JInt m),
    pair = .ok (quotient, remainder) → modValue = .ok modulus →
    remainder.val = modulus.val

/-- The source `fldmod` result and the source `base/int.jl` `mod` result have the same mathematical
remainder for every pair of distinct same-signedness types and every mixed signed/unsigned pair. -/
def BitIntegerMixedFldmodConsistency : Prop :=
  (∀ (s u : IntTy) (x : JInt s) (y : JInt u),
    s.signed = u.signed → s ≠ u →
    remainderValuesAgree (fldmodMixedSameSign x y) (modMixedSameSign x y)) ∧
  (∀ (s u : IntTy) (x : JInt s) (y : JInt u),
    s.signed = true → u.signed = false →
    remainderValuesAgree (fldmodMixedSignedUnsigned x y) (modMixedSignedUnsigned x y)) ∧
  (∀ (u s : IntTy) (x : JInt u) (y : JInt s),
    u.signed = false → s.signed = true →
    remainderValuesAgree (fldmodMixedUnsignedSigned x y) (modMixedUnsignedSigned x y))

/-! Nothing to promise: div(::Bool,::Bool,::RoundingMode)@422: forwards to ordinary Bool division.
Nothing to promise: generated div(::Bool,::Bool,::RoundingMode)@424-426: forwards to ordinary Bool division.
Nothing to promise: div(::Bool,::Bool,nearest mode)@427: forwards to ordinary Bool division. -/

/-- The float `mod` method returns a value without throwing; this adapter supplies the `Jl` result
expected by the source `rem` model. -/
def floatModJl {T : FTy} (x y : FV T) : JuliaLean.Jl (FV T) :=
  .ok (JuliaLean.base.float.mod_AbstractFloat x y)

/-- For finite `Float64` `x` and positive finite `y`, the documented RoundDown remainder lies in
`[0,y)`. This retains the existing runtime counterexample for the later proof worker. -/
def RoundDownFloatRemainderBound : Prop :=
  ∀ (x y : JuliaLean.base.float.FV .f64),
    JuliaLean.base.float.isfinite_callee x = true →
    JuliaLean.base.float.isfinite_callee y = true →
    JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float .f64) y = true →
    ∃ r : JuliaLean.base.float.FV .f64,
      JuliaLean.base.div.rem_Down floatModJl x y = .ok r ∧
      JuliaLean.base.float.le_float (JuliaLean.base.float.zero_float .f64) r = true ∧
      JuliaLean.base.float.lt_float r y = true

private theorem quotient_zero {t : IntTy} (x y : JInt t) (hy : y.val = 0) :
    divBitIntegerToZero x y = .error .divideError := by
  simp [divBitIntegerToZero, div_BitInteger_ToZero,
    JuliaLean.Proofs.base.int.divSame_eq, hy]

private theorem div_zero {t : IntTy} (x y : JInt t) (hy : y.val = 0) :
    ∀ mode, divBitIntegerMode x y mode = .error .divideError := by
  intro mode
  cases mode <;>
    simp [divBitIntegerMode, divBitIntegerDown, divBitIntegerUp,
      div_Integer_Down, div_Unsigned_Down, div_Integer_Up, div_Unsigned_Up,
      div_Integer_FromZero, div_Integer_Nearest, divBitIntegerUpDown,
      divremBitIntegerNearestModes, divremBitIntegerNearest, divremBitIntegerTiesAway,
      divremBitIntegerTiesUp, divremBitIntegerToZero,
      divrem_Integer_Nearest, divrem_Integer_NearestTiesAway, divrem_Integer_NearestTiesUp,
      divrem_BitSigned_Directed, divrem_Integer_Directed, quotient_zero x y hy,
      JuliaLean.Proofs.base.int.divSame_eq, hy, Functor.map, Except.map, Bind.bind, Except.bind]

private theorem quotient_error {t : IntTy} (x y : JInt t) (he : divisionError x y) :
    divBitIntegerToZero x y = .error .divideError := by
  simp [divBitIntegerToZero, div_BitInteger_ToZero,
    JuliaLean.Proofs.base.int.divSame_eq, divisionError] at he ⊢
  intro h
  exact he.resolve_left h

private theorem div_error {t : IntTy} (x y : JInt t) (he : divisionError x y) :
    ∀ mode, divBitIntegerMode x y mode = .error .divideError := by
  intro mode
  have hq := quotient_error x y he
  have hd : JuliaLean.base.int.divSame x y = .error .divideError := by
    simpa [divBitIntegerToZero, div_BitInteger_ToZero] using hq
  cases mode <;>
    simp [divBitIntegerMode, divBitIntegerDown, divBitIntegerUp,
      div_Integer_Down, div_Unsigned_Down, div_Integer_Up, div_Unsigned_Up,
      div_Integer_FromZero, div_Integer_Nearest, divBitIntegerUpDown,
      divremBitIntegerNearestModes, divremBitIntegerNearest, divremBitIntegerTiesAway,
      divremBitIntegerTiesUp, divremBitIntegerToZero,
      divrem_Integer_Nearest, divrem_Integer_NearestTiesAway, divrem_Integer_NearestTiesUp,
      divrem_BitSigned_Directed, divrem_Integer_Directed, hq, hd, Bind.bind, Except.bind]

private theorem divrem_error {t : IntTy} (x y : JInt t) (he : divisionError x y) :
    ∀ mode, divremBitIntegerMode x y mode = .error .divideError := by
  intro mode
  have hq := quotient_error x y he
  have hd := div_error x y he
  cases mode <;>
    simp [divremBitIntegerMode, divremBitIntegerDirected, divremBitIntegerUpDown,
      divremBitIntegerNearestModes, divremBitIntegerNearest, divremBitIntegerTiesAway,
      divremBitIntegerTiesUp, divremBitIntegerToZero, fldBitInteger, fld_same_numeric,
      divrem_Integer_Nearest, divrem_Integer_NearestTiesAway, divrem_Integer_NearestTiesUp,
      divrem_BitSigned_Directed, divrem_Integer_Directed, divrem_FromZero,
      hq, hd, Bind.bind, Except.bind]

private theorem mod_zero {t : IntTy} (x y : JInt t) (hy : y.val = 0) :
    modBitInteger x y = .error .divideError := by
  have hm1 : (JuliaLean.base.int.lit .i64 (-1)).val = -1 := by decide
  unfold modBitInteger
  split
  · unfold JuliaLean.base.int.mod_BitSigned
    rw [JuliaLean.Proofs.base.int.eq_eq, hm1]
    simp [hy, fldBitInteger, fld_same_numeric, div_zero x y hy, Bind.bind, Except.bind]
  · simp [JuliaLean.base.int.mod_Unsigned, JuliaLean.base.int.Generic.mod_Unsigned,
      JuliaLean.Proofs.base.int.remSame_eq, hy]

private theorem rem_zero {t : IntTy} (x y : JInt t) (hy : y.val = 0) :
    ∀ mode, remBitIntegerMode x y mode = .error .divideError := by
  have hn : (JuliaLean.base.int.neg y).val = 0 := by
    rw [JuliaLean.base.int.neg, JuliaLean.Proofs.base.int.neg_int_val, hy]
    cases t <;> rfl
  intro mode
  cases mode <;>
    simp [remBitIntegerMode, rem_ToZero, rem_Down, rem_Up, rem_FromZero,
      rem_Integer_Nearest, rem_Integer_Ties, remBitIntegerUpDown,
      divremBitIntegerNearestModes, divremBitIntegerNearest, divremBitIntegerTiesAway,
      divremBitIntegerTiesUp, divrem_Integer_Nearest, divrem_Integer_NearestTiesAway,
      divrem_Integer_NearestTiesUp, quotient_zero x y hy, divremBitIntegerToZero,
      divrem_BitSigned_Directed, divrem_Integer_Directed, mod_zero x y hy,
      mod_zero x (JuliaLean.base.int.neg y) hn, JuliaLean.Proofs.base.int.remSame_eq,
      fldBitInteger, fld_same_numeric, div_zero x y hy, hy, Bind.bind, Except.bind]

private theorem rem_overflow {t : IntTy} (x y : JInt t)
    (hs : t.signed = true) (hx : x.val = t.min) (hy : y.val = -1) :
    remBitIntegerMode x y .ToZero = .ok (JuliaLean.base.int.lit t 0) ∧
    remBitIntegerMode x y .Down = .ok (JuliaLean.base.int.lit t 0) ∧
    remBitIntegerMode x y .Up = .ok (JuliaLean.base.int.lit t 0) ∧
    remBitIntegerMode x y .FromZero = .ok (JuliaLean.base.int.lit t 0) := by
  have hxl : x = JuliaLean.base.int.lit t t.min := by
    apply Subtype.ext
    rw [JuliaLean.Proofs.base.int.lit_val, hx]
    cases t <;> rfl
  have hyl : y = JuliaLean.base.int.lit t (-1) := by
    apply Subtype.ext
    rw [JuliaLean.Proofs.base.int.lit_val, hy]
    cases t <;> simp_all [IntTy.signed] <;> decide
  rw [hxl, hyl]
  cases t <;> simp_all [IntTy.signed] <;> (repeat' constructor) <;> rfl

theorem bitIntegerDivisionErrorCases_proven : BitIntegerDivisionErrorCases := by
  constructor
  · intro t x y mode hy
    have he : divisionError x y := Or.inl hy
    exact ⟨div_zero x y hy mode, rem_zero x y hy mode, divrem_error x y he mode,
      by simpa [fldBitInteger, fld_same_numeric] using div_zero x y hy .Down,
      by simpa [cldBitInteger, cld_same_numeric] using div_zero x y hy .Up,
      by simpa [fldmodBitInteger, fldmod] using divrem_error x y he .Down⟩
  · intro t x y hs hx hy
    have he : divisionError x y := Or.inr ⟨hs, hx, hy⟩
    obtain ⟨hz, hd, hu, hf⟩ := rem_overflow x y hs hx hy
    refine ⟨fun mode => ⟨div_error x y he mode, divrem_error x y he mode⟩,
      ?_, ?_, ?_, hz, hd, hu, hf, ?_⟩
    · simpa [fldBitInteger, fld_same_numeric] using div_error x y he .Down
    · simpa [cldBitInteger, cld_same_numeric] using div_error x y he .Up
    · simpa [fldmodBitInteger, fldmod] using divrem_error x y he .Down
    · intro mode hm
      have hq := quotient_error x y he
      rcases hm with rfl | rfl | rfl <;>
        simp [remBitIntegerMode, rem_Integer_Nearest, rem_Integer_Ties,
          divremBitIntegerNearestModes, divremBitIntegerNearest,
          divremBitIntegerTiesAway, divremBitIntegerTiesUp, divrem_Integer_Nearest,
          divrem_Integer_NearestTiesAway, divrem_Integer_NearestTiesUp,
          divremBitIntegerToZero, divrem_BitSigned_Directed,
          divrem_Integer_Directed, hq, Bind.bind, Except.bind]

private theorem ty_range (t : IntTy) :
    (t.min = -(t.max + 1) ∧ 127 ≤ t.max) ∨ (t.min = 0 ∧ 255 ≤ t.max) := by
  cases t <;> simp [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits]

private theorem signed_of_min_neg (t : IntTy) (h : t.min < 0) : t.signed = true := by
  cases t <;> simp_all [IntTy.signed, IntTy.min]

private theorem unsigned_nonneg {t : IntTy} (x : JInt t) (h : t.signed = false) :
    0 ≤ x.val := by
  have hx := x.property.1
  cases t <;> simp_all [IntTy.signed, IntTy.min]

theorem fdiv_fmod_tdiv (a b : Int) (hb : b ≠ 0) :
    a.fdiv b = (if ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tdiv b - 1 else a.tdiv b) ∧
    a.fmod b = (if ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tmod b + b else a.tmod b) := by
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt a hb
  have h4 : a = 0 → a % b = 0 := by intro h; subst h; simp
  have htm0 : (a.tmod b = 0) = (a % b = 0) := by
    rw [Int.tmod_eq_emod]
    simp only [Int.dvd_iff_emod_eq_zero]
    apply propext
    split <;> omega
  simp only [ne_eq, htm0]
  rw [Int.fdiv_eq_ediv, Int.fmod_eq_emod, Int.tdiv_eq_ediv, Int.tmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  generalize a / b = e
  generalize a % b = m at h0 h1 h4 ⊢
  rcases Int.lt_or_gt_of_ne hb with hs | hs
  · rw [Int.sign_eq_neg_one_of_neg hs]
    constructor <;> (repeat' split) <;> omega
  · rw [Int.sign_eq_one_of_pos hs]
    constructor <;> (repeat' split) <;> omega

private theorem cdiv_tdiv (a b : Int) (hb : b ≠ 0) :
    -((-a).fdiv b) = (if ((0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tdiv b + 1 else a.tdiv b) := by
  rw [(fdiv_fmod_tdiv (-a) b hb).1, Int.neg_tdiv, Int.neg_tmod]
  split <;> split <;> omega

private theorem fdiv_mul_add_fmod (a b : Int) (hb : b ≠ 0) :
    a.fdiv b * b + a.fmod b = a := by
  obtain ⟨hfd, hfm⟩ := fdiv_fmod_tdiv a b hb
  have := Int.tdiv_mul_add_tmod a b
  rw [hfd, hfm]
  split
  · rw [Int.sub_mul, Int.one_mul]
    omega
  · omega

private theorem fmod_neg_one (a : Int) : a.fmod (-1) = 0 := by
  rw [(fdiv_fmod_tdiv a (-1) (by decide)).2, Int.tmod_neg, Int.tmod_one]
  simp

private theorem quot_facts (a b : Int) (hb : b ≠ 0) :
    a.tdiv b * b + a.tmod b = a ∧
    (0 ≤ a → 0 ≤ a.tmod b ∧ a.tmod b ≤ a) ∧ (a < 0 → a ≤ a.tmod b ∧ a.tmod b ≤ 0) ∧
    (0 < b → -b < a.tmod b ∧ a.tmod b < b) ∧ (b < 0 → b < a.tmod b ∧ a.tmod b < -b) ∧
    (0 ≤ a → (2 ≤ b ∨ b ≤ -2) → -a ≤ 2 * a.tdiv b ∧ 2 * a.tdiv b ≤ a) ∧
    (a < 0 → (2 ≤ b ∨ b ≤ -2) → a ≤ 2 * a.tdiv b ∧ 2 * a.tdiv b ≤ -a) ∧
    (b = 1 → a.tdiv b = a) ∧ (b = -1 → a.tdiv b = -a) ∧
    (0 ≤ a → 0 < b → 0 ≤ a.tdiv b) := by
  have hra : (a.tmod b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
  have hq2 : 2 ≤ b.natAbs → 2 * (a.tdiv b).natAbs ≤ a.natAbs := by
    intro h2
    rw [Int.natAbs_tdiv]
    have := @Nat.div_le_div_left 2 b.natAbs a.natAbs h2 (by omega)
    show 2 * (a.natAbs / b.natAbs) ≤ a.natAbs
    omega
  refine ⟨Int.tdiv_mul_add_tmod a b, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h h2 => ?_, fun h h2 => ?_, fun h => by subst h; exact Int.tdiv_one a,
    fun h => by subst h; rw [Int.tdiv_neg, Int.tdiv_one], fun ha hb' => ?_⟩
  · have := Int.tmod_nonneg b h
    omega
  · have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
    rw [Int.neg_tmod] at this
    omega
  · exact ⟨Int.lt_tmod_of_pos a h, Int.tmod_lt_of_pos a h⟩
  · have h1 := Int.lt_tmod_of_pos a (show 0 < -b by omega)
    have h2 := Int.tmod_lt_of_pos a (show 0 < -b by omega)
    rw [Int.tmod_neg] at h1 h2
    omega
  · have := hq2 (by omega)
    omega
  · have := hq2 (by omega)
    omega
  · rw [Int.tdiv_eq_ediv_of_nonneg ha]; exact Int.ediv_nonneg ha (by omega)

private theorem ranges_int (x y q r lo hi : Int) (hy : y ≠ 0)
    (hx : lo ≤ x ∧ x ≤ hi) (hyr : lo ≤ y ∧ y ≤ hi)
    (hty : (lo = -(hi + 1) ∧ 127 ≤ hi) ∨ (lo = 0 ∧ 255 ≤ hi))
    (hqr : q * y + r = x)
    (hra0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hra1 : x < 0 → x ≤ r ∧ r ≤ 0)
    (hrb0 : 0 < y → -y < r ∧ r < y) (hrb1 : y < 0 → y < r ∧ r < -y)
    (hq20 : 0 ≤ x → (2 ≤ y ∨ y ≤ -2) → -x ≤ 2 * q ∧ 2 * q ≤ x)
    (hq21 : x < 0 → (2 ≤ y ∨ y ≤ -2) → x ≤ 2 * q ∧ 2 * q ≤ -x)
    (hq1 : y = 1 → q = x) (hqm1 : y = -1 → q = -x) (hqpos : 0 ≤ x → 0 < y → 0 ≤ q) :
    (lo ≤ r ∧ r ≤ hi) ∧
    (lo ≤ (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then r + y else r) ∧
      (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then r + y else r) ≤ hi) ∧
    (lo ≤ q * y ∧ q * y ≤ hi) ∧
    (¬(lo < 0 ∧ x = lo ∧ y = -1) →
      (lo ≤ q ∧ q ≤ hi) ∧
      (lo ≤ (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) ∧
        (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) ≤ hi) ∧
      (lo ≤ (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) ∧
        (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) ≤ hi)) := by
  rcases hty with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;>
  by_cases hx0 : 0 ≤ x <;>
  rcases Int.lt_or_gt_of_ne hy with hy0 | hy0 <;>
  refine ⟨by omega, by split <;> omega, by omega,
    fun hn => ⟨by omega, by split <;> omega, by split <;> omega⟩⟩

private theorem div_ranges {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0) :
    (t.min ≤ a.val.tmod b.val ∧ a.val.tmod b.val ≤ t.max) ∧
    (t.min ≤ a.val.fmod b.val ∧ a.val.fmod b.val ≤ t.max) ∧
    (t.min ≤ a.val.tdiv b.val * b.val ∧ a.val.tdiv b.val * b.val ≤ t.max) ∧
    (¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) →
      (t.min ≤ a.val.tdiv b.val ∧ a.val.tdiv b.val ≤ t.max) ∧
      (t.min ≤ a.val.fdiv b.val ∧ a.val.fdiv b.val ≤ t.max) ∧
      (t.min ≤ -((-a.val).fdiv b.val) ∧ -((-a.val).fdiv b.val) ≤ t.max)) := by
  obtain ⟨hqr, hr0, hr1, hrb, hra, hqa, hq2, hq1, hqm1, hqpos⟩ := quot_facts a.val b.val hb0
  obtain ⟨hfd, hfm⟩ := fdiv_fmod_tdiv a.val b.val hb0
  have key := ranges_int a.val b.val _ _ t.min t.max hb0 a.property b.property (ty_range t)
    hqr hr0 hr1 hrb hra hqa hq2 hq1 hqm1 hqpos
  rw [hfd, hfm, cdiv_tdiv a.val b.val hb0]
  exact ⟨key.1, key.2.1, key.2.2.1,
    fun hn => key.2.2.2 fun h => hn ⟨signed_of_min_neg t h.1, h.2⟩⟩

private theorem pos_of_unsigned {t : IntTy} (x : JInt t) (h : t.signed = false)
    (hx : x.val ≠ 0) : 0 < x.val := by
  have := unsigned_nonneg x h
  omega

private theorem sub_of_add (p m x : Int) (h : p + m = x) : x - p = m := by
  omega

private theorem fld_cond (x y q r : Int) (hy : y ≠ 0) (hqr : q * y + r = x)
    (hr0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hr1 : x < 0 → x ≤ r ∧ r ≤ 0) :
    q - (if ((x < 0 ∧ 0 ≤ y) ∨ (0 ≤ x ∧ y < 0)) ∧ q * y ≠ x then 1 else 0) =
      (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) := by
  split <;> split <;> omega

private theorem cld_cond (s : Bool) (x y q r : Int) (hy : y ≠ 0) (hqr : q * y + r = x)
    (hr0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hr1 : x < 0 → x ≤ r ∧ r ≤ 0)
    (hs : s = false → 0 ≤ x ∧ 0 < y) :
    q + (if (¬ s = true ∨ (x > 0 ↔ y > 0)) ∧ q * y ≠ x then 1 else 0) =
      (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) := by
  cases s
  · have := hs rfl
    simp only [Bool.false_eq_true, not_false_eq_true, true_or, true_and]
    split <;> split <;> omega
  · simp only [not_true_eq_false, false_or]
    split <;> split <;> omega


private theorem div_success {t : IntTy} (a b : JInt t) (h : ¬ divisionError a b) :
    divBitIntegerToZero a b = .ok (lit t (a.val.tdiv b.val)) := by
  rw [divBitIntegerToZero, div_BitInteger_ToZero, JuliaLean.Proofs.base.int.divSame_eq]
  exact if_neg h

private theorem ofBool_val (t : IntTy) (b : Bool) :
    (JuliaLean.base.int.ofBool t b).val = if b then 1 else 0 := by
  cases b <;> cases t <;> decide

private theorem bit_add_bool_val {t : IntTy} (a : JInt t) (b : Bool) :
    (bitAddBool a b).val = wrapInt t (a.val + if b then 1 else 0) := by
  change wrapInt t (a.val + (JuliaLean.base.int.ofBool t b).val) = _
  rw [ofBool_val]

private theorem bit_sub_bool_val {t : IntTy} (a : JInt t) (b : Bool) :
    (bitSubBool a b).val = wrapInt t (a.val - if b then 1 else 0) := by
  change wrapInt t (a.val - (JuliaLean.base.int.ofBool t b).val) = _
  rw [ofBool_val]

private theorem down_success {t : IntTy} (a b : JInt t) (h : ¬ divisionError a b) :
    divBitIntegerDown a b = .ok (lit t (a.val.fdiv b.val)) := by
  have hb : b.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ a.val = t.min ∧ b.val = -1) := fun hz => h (Or.inr hz)
  have ranges := div_ranges a b hb
  have qfit := (ranges.2.2.2 ho).1
  have qv : (lit t (a.val.tdiv b.val)).val = a.val.tdiv b.val :=
    JuliaLean.Proofs.base.int.lit_of_fits qfit
  have mv : (bitMul (lit t (a.val.tdiv b.val)) b).val = a.val.tdiv b.val * b.val := by
    rw [bitMul, JuliaLean.Proofs.base.int.mulSame_val, qv]
    exact JuliaLean.Proofs.base.int.lit_of_fits ranges.2.2.1
  unfold divBitIntegerDown
  split
  · rename_i hs
    rw [div_Integer_Down, div_success a b h]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    congr 1
    apply JuliaLean.Proofs.base.int.jint_eq
    rw [bit_sub_bool_val, qv]
    have sx : bitSignbit (bitXor a b) = decide (¬ (a.val < 0 ↔ b.val < 0)) := by
      rw [bitSignbit, JuliaLean.base.int.signbit, if_pos hs]
      rw [(JuliaLean.Proofs.base.int.signPredicates_proven t _).1]
      congr 1
      exact propext (JuliaLean.Proofs.base.int.bxor_neg_iff hs a b)
    rw [sx]
    simp only [bitNeq, mv, Bool.and_eq_true, decide_eq_true_eq]
    change wrapInt t _ = wrapInt t _
    congr 1
    rw [(fdiv_fmod_tdiv a.val b.val hb).1]
    have facts := quot_facts a.val b.val hb
    have sign : (¬ (a.val < 0 ↔ b.val < 0)) ↔
        ((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) := by omega
    simpa only [sign] using fld_cond a.val b.val _ _ hb facts.1 facts.2.1 facts.2.2.1
  · rename_i hs
    have hu : t.signed = false := Bool.eq_false_iff.mpr hs
    have ha := unsigned_nonneg a hu
    have hy := pos_of_unsigned b hu hb
    rw [div_Unsigned_Down, JuliaLean.Proofs.base.int.divSame_eq]
    rw [if_neg (show ¬ (b.val = 0 ∨ t.signed = true ∧ a.val = t.min ∧ b.val = -1) from h)]
    congr 2
    rw [Int.fdiv_eq_ediv_of_nonneg a.val (by omega), Int.tdiv_eq_ediv_of_nonneg ha]

private theorem up_success {t : IntTy} (a b : JInt t) (h : ¬ divisionError a b) :
    divBitIntegerUp a b = .ok (lit t (-((-a.val).fdiv b.val))) := by
  have hb : b.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ a.val = t.min ∧ b.val = -1) := fun hz => h (Or.inr hz)
  have ranges := div_ranges a b hb
  have qfit := (ranges.2.2.2 ho).1
  have qv : (lit t (a.val.tdiv b.val)).val = a.val.tdiv b.val :=
    JuliaLean.Proofs.base.int.lit_of_fits qfit
  have mv : (bitMul (lit t (a.val.tdiv b.val)) b).val = a.val.tdiv b.val * b.val := by
    rw [bitMul, JuliaLean.Proofs.base.int.mulSame_val, qv]
    exact JuliaLean.Proofs.base.int.lit_of_fits ranges.2.2.1
  have facts := quot_facts a.val b.val hb
  have hs : t.signed = false → 0 ≤ a.val ∧ 0 < b.val := by
    intro hu
    exact ⟨unsigned_nonneg a hu, pos_of_unsigned b hu hb⟩
  unfold divBitIntegerUp
  split
  · rename_i ht
    rw [div_Integer_Up, div_success a b h]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    congr 1
    apply JuliaLean.Proofs.base.int.jint_eq
    rw [bit_add_bool_val, qv]
    simp only [bitGtZero, bitNeq, mv, Bool.and_eq_true, decide_eq_true_eq, decide_eq_decide]
    change wrapInt t _ = wrapInt t _
    congr 1
    rw [cdiv_tdiv a.val b.val hb]
    simpa using
      cld_cond true a.val b.val _ _ hb facts.1 facts.2.1 facts.2.2.1 (by simp)
  · rename_i ht
    have hu : t.signed = false := Bool.eq_false_iff.mpr ht
    rw [div_Unsigned_Up, div_success a b h]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    congr 1
    apply JuliaLean.Proofs.base.int.jint_eq
    rw [bit_add_bool_val, qv]
    simp only [bitNeq, mv, decide_eq_true_eq]
    change wrapInt t _ = wrapInt t _
    congr 1
    rw [cdiv_tdiv a.val b.val hb]
    simpa using cld_cond false a.val b.val _ _ hb facts.1 facts.2.1 facts.2.2.1 (by
      intro _
      exact hs hu)
private def nearestRaw (x y q r : Int) (mode : RoundingMode) : Int :=
  let odd := y.tmod 2 ≠ 0
  let tie := if mode = .Nearest then odd ∨ q.tmod 2 = 0 else odd
  if 0 ≤ x then
    if 0 ≤ y then
      if r ≥ y.tdiv 2 + (if tie then 1 else 0) then q + 1 else q
    else
      if r ≥ -(y.tdiv 2) + (if mode = .NearestTiesUp then 1 else if tie then 1 else 0)
        then q - 1 else q
  else if 0 ≤ y then
    if r ≤ -(y.tdiv 2) - (if mode = .NearestTiesUp then 1 else if tie then 1 else 0)
      then q - 1 else q
  else
    if r ≤ y.tdiv 2 - (if tie then 1 else 0) then q + 1 else q

set_option maxHeartbeats 4000000 in
private theorem nearest_raw_correct (x y : Int) (mode : RoundingMode)
    (hm : mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp)
    (hy : y ≠ 0) :
    nearestRaw x y (x.tdiv y) (x.tmod y) mode = roundedIntegerQuotient x y mode ∧
    (nearestRaw x y (x.tdiv y) (x.tmod y) mode = x.tdiv y ∨
      nearestRaw x y (x.tdiv y) (x.tmod y) mode = x.fdiv y ∨
      nearestRaw x y (x.tdiv y) (x.tmod y) mode = -((-x).fdiv y)) := by
  rcases quot_facts x y hy with ⟨he, hp, hn, hyp, hyn, hqp, hqn, hq1, hqm1, hqs⟩
  have hhalf := Int.tdiv_mul_add_tmod y 2
  have hhalflo := Int.lt_tmod_of_pos y (by decide : (0 : Int) < 2)
  have hhalfhi := Int.tmod_lt_of_pos y (by decide : (0 : Int) < 2)
  have hhalfpos : 0 ≤ y → 0 ≤ y.tmod 2 := fun h => Int.tmod_nonneg 2 h
  have hhalfneg : y < 0 → y.tmod 2 ≤ 0 := by
    intro h
    have hh := Int.tmod_nonneg 2 (show 0 ≤ -y by omega)
    rw [Int.neg_tmod] at hh
    omega
  rw [(fdiv_fmod_tdiv x y hy).1, cdiv_tdiv x y hy]
  rcases hm with rfl | rfl | rfl <;>
    simp only [nearestRaw, roundedIntegerQuotient, if_neg hy, absInt, awayFromZero,
      sameSign, reduceCtorEq, ↓reduceIte, Bool.decide_coe] <;>
    (repeat' split) <;> simp_all <;> omega

private theorem divrem_zero_success {t : IntTy} (x y : JInt t)
    (h : ¬ divisionError x y) :
    divremBitIntegerToZero x y = .ok (lit t (x.val.tdiv y.val), lit t (x.val.tmod y.val)) := by
  have hy : y.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun hz => h (Or.inr hz)
  have ranges := div_ranges x y hy
  have qv : (lit t (x.val.tdiv y.val)).val = x.val.tdiv y.val :=
    JuliaLean.Proofs.base.int.lit_of_fits ((ranges.2.2.2 ho).1)
  have hv : bitSub x (bitMul (lit t (x.val.tdiv y.val)) y) = lit t (x.val.tmod y.val) := by
    apply JuliaLean.Proofs.base.int.jint_eq
    change wrapInt t (x.val - (bitMul (lit t (x.val.tdiv y.val)) y).val) = _
    rw [bitMul, JuliaLean.Proofs.base.int.mulSame_val, qv,
      JuliaLean.Proofs.base.int.wrapInt_sub_right]
    congr 1
    have he := Int.tdiv_mul_add_tmod x.val y.val
    omega
  unfold divremBitIntegerToZero
  split <;> simp [divrem_BitSigned_Directed, divrem_Integer_Directed,
    div_success x y h, Bind.bind, Except.bind, pure, Except.pure, hv]

private theorem add_lit_true (t : IntTy) (q : Int) :
    bitAddBool (lit t q) true = lit t (q + 1) := by
  apply JuliaLean.Proofs.base.int.jint_eq
  rw [bit_add_bool_val]
  exact JuliaLean.Proofs.base.int.wrapInt_add_left t q 1

private theorem sub_lit_true (t : IntTy) (q : Int) :
    bitSubBool (lit t q) true = lit t (q - 1) := by
  apply JuliaLean.Proofs.base.int.jint_eq
  rw [bit_sub_bool_val]
  exact JuliaLean.Proofs.base.int.wrapInt_sub_left t q 1

private theorem except_bind_ite {E A B : Type} (p : Prop) [Decidable p]
    (a b : Except E A) (k : A → Except E B) :
    Except.bind (if p then a else b) k =
      if p then Except.bind a k else Except.bind b k := by
  by_cases h : p <;> simp [h]

private theorem except_bind_ok {E A B : Type} (a : A) (k : A → Except E B) :
    Except.bind (.ok a) k = k a := rfl

set_option maxHeartbeats 4000000 in
private theorem nearest_source {t : IntTy} (x y : JInt t) (mode : RoundingMode)
    (hm : mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp)
    (h : ¬ divisionError x y) :
    divBitIntegerMode x y mode =
      .ok (lit t (nearestRaw x.val y.val (x.val.tdiv y.val) (x.val.tmod y.val) mode)) := by
  have hy : y.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun hz => h (Or.inr hz)
  have ranges := div_ranges x y hy
  have qv : (lit t (x.val.tdiv y.val)).val = x.val.tdiv y.val :=
    JuliaLean.Proofs.base.int.lit_of_fits ((ranges.2.2.2 ho).1)
  have rv : (lit t (x.val.tmod y.val)).val = x.val.tmod y.val :=
    JuliaLean.Proofs.base.int.lit_of_fits ranges.1
  rcases hm with rfl | rfl | rfl <;>
    simp only [divBitIntegerMode, div_Integer_Nearest, divremBitIntegerNearestModes,
      divremBitIntegerNearest, divremBitIntegerTiesAway, divremBitIntegerTiesUp,
      divrem_Integer_Nearest, divrem_Integer_NearestTiesAway, divrem_Integer_NearestTiesUp,
      divrem_zero_success x y h, reduceCtorEq, ↓reduceIte, eq_self_iff_true, if_true, boolInt,
      Bind.bind, pure, Except.pure, except_bind_ite, except_bind_ok] <;>
    simp only [nearestRaw, bitVal, bitHalf, bitIsOdd, bitIsEven, qv, rv, add_lit_true,
      sub_lit_true, Bool.or_eq_true, Bool.decide_eq_true, reduceCtorEq, ↓reduceIte,
      eq_self_iff_true, if_true, except_bind_ite, except_bind_ok] <;>
    (repeat' split) <;> simp_all <;> (repeat' split) <;> simp_all

private theorem bit_signbit_eq {t : IntTy} (x : JInt t) :
    bitSignbit x = decide (x.val < 0) := by
  unfold bitSignbit JuliaLean.base.int.signbit
  split
  · exact (JuliaLean.Proofs.base.int.signPredicates_proven t x).1
  · rename_i ht
    exact ((JuliaLean.Proofs.base.int.signPredicates_proven t x).2
      (Bool.eq_false_iff.mpr ht)).1

private theorem fromzero_success {t : IntTy} (x y : JInt t)
    (h : ¬ divisionError x y) :
    divBitIntegerMode x y .FromZero = .ok (lit t
      (if sameSign x.val y.val then -((-x.val).fdiv y.val) else x.val.fdiv y.val)) := by
  simp only [divBitIntegerMode, reduceCtorEq, ↓reduceIte, div_Integer_FromZero,
    bit_signbit_eq, divBitIntegerUpDown]
  by_cases hs : x.val < 0 ↔ y.val < 0
  · have he : decide (x.val < 0) = decide (y.val < 0) := by simp [hs]
    simp [he, sameSign, hs, up_success x y h]
  · have he : decide (x.val < 0) ≠ decide (y.val < 0) := by simpa using hs
    simp [he, sameSign, hs, down_success x y h]

private theorem nearest_success {t : IntTy} (x y : JInt t) (mode : RoundingMode)
    (hm : mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp)
    (h : ¬ divisionError x y) :
    ∃ q : JInt t, divBitIntegerMode x y mode = .ok q ∧
      q.val = roundedIntegerQuotient x.val y.val mode := by
  have hy : y.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun hz => h (Or.inr hz)
  have ranges := (div_ranges x y hy).2.2.2 ho
  have hc := nearest_raw_correct x.val y.val mode hm hy
  refine ⟨lit t (nearestRaw x.val y.val (x.val.tdiv y.val) (x.val.tmod y.val) mode),
    nearest_source x y mode hm h, ?_⟩
  have hf : t.min ≤ nearestRaw x.val y.val (x.val.tdiv y.val) (x.val.tmod y.val) mode ∧
      nearestRaw x.val y.val (x.val.tdiv y.val) (x.val.tmod y.val) mode ≤ t.max := by
    rcases hc.2 with he | he | he
    · rw [he]; exact ranges.1
    · rw [he]; exact ranges.2.1
    · rw [he]; exact ranges.2.2
  exact (JuliaLean.Proofs.base.int.lit_of_fits (t := t) hf).trans hc.1

theorem BitIntegerDivisionCorrect_proven : BitIntegerDivisionCorrect := by
  intro t x y mode
  refine ⟨fun he => div_error x y he mode, ?_⟩
  intro h
  have hy : y.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun hz => h (Or.inr hz)
  have ranges := (div_ranges x y hy).2.2.2 ho
  cases mode with
  | ToZero =>
    refine ⟨lit t (x.val.tdiv y.val), ?_, ?_⟩
    · simpa [divBitIntegerMode] using div_success x y h
    · simp only [roundedIntegerQuotient, if_neg hy]
      exact JuliaLean.Proofs.base.int.lit_of_fits (t := t) ranges.1
  | Down =>
    refine ⟨lit t (x.val.fdiv y.val), ?_, ?_⟩
    · simpa [divBitIntegerMode] using down_success x y h
    · simp only [roundedIntegerQuotient, if_neg hy]
      exact JuliaLean.Proofs.base.int.lit_of_fits (t := t) ranges.2.1
  | Up =>
    refine ⟨lit t (-((-x.val).fdiv y.val)), ?_, ?_⟩
    · simpa [divBitIntegerMode] using up_success x y h
    · simp only [roundedIntegerQuotient, if_neg hy]
      exact JuliaLean.Proofs.base.int.lit_of_fits (t := t) ranges.2.2
  | FromZero =>
    refine ⟨lit t (if sameSign x.val y.val then -((-x.val).fdiv y.val)
      else x.val.fdiv y.val), fromzero_success x y h, ?_⟩
    simp only [roundedIntegerQuotient, if_neg hy]
    split
    · exact JuliaLean.Proofs.base.int.lit_of_fits ranges.2.2
    · exact JuliaLean.Proofs.base.int.lit_of_fits ranges.2.1
  | Nearest => exact nearest_success x y .Nearest (Or.inl rfl) h
  | NearestTiesAway => exact nearest_success x y .NearestTiesAway (Or.inr (Or.inl rfl)) h
  | NearestTiesUp => exact nearest_success x y .NearestTiesUp (Or.inr (Or.inr rfl)) h


private theorem fld_success {t : IntTy} (x y : JInt t) (h : ¬ divisionError x y) :
    fldBitInteger x y = .ok (lit t (x.val.fdiv y.val)) := by
  simpa [fldBitInteger, fld_same_numeric, divBitIntegerMode] using down_success x y h

private theorem cld_success {t : IntTy} (x y : JInt t) (h : ¬ divisionError x y) :
    cldBitInteger x y = .ok (lit t (-((-x.val).fdiv y.val))) := by
  simpa [cldBitInteger, cld_same_numeric, divBitIntegerMode] using up_success x y h

theorem BitIntegerFloorCeilingCorrect_proven : BitIntegerFloorCeilingCorrect := by
  intro t x y
  constructor
  · intro h
    have hf := div_error x y h .Down
    have hc := div_error x y h .Up
    simpa [fldBitInteger, cldBitInteger, fld1BitInteger, fld_same_numeric,
      cld_same_numeric, fld1] using And.intro hf (And.intro hc hc)
  · intro h
    have hy : y.val ≠ 0 := fun hz => h (Or.inl hz)
    have ho : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun hz => h (Or.inr hz)
    have ranges := (div_ranges x y hy).2.2.2 ho
    refine ⟨lit t (x.val.fdiv y.val), lit t (-((-x.val).fdiv y.val)),
      fld_success x y h, ?_, cld_success x y h, ?_, ?_⟩
    · exact JuliaLean.Proofs.base.int.lit_of_fits ranges.2.1
    · exact JuliaLean.Proofs.base.int.lit_of_fits ranges.2.2
    · exact cld_success x y h

theorem fldBitInteger_spec (t : IntTy) :
    JuliaLean.Proofs.base.int.FldSpec (@fldBitInteger t) := by
  intro x y hy1
  by_cases hy0 : y.val = 0
  · simpa [hy0, fldBitInteger, fld_same_numeric] using div_zero x y hy0 .Down
  · simpa [hy0, JuliaLean.base.int.lit, JInt.lit] using fld_success x y (by
      intro h
      rcases h with h | ⟨_, _, h⟩
      · exact hy0 h
      · exact hy1 h)

theorem modBitInteger_eq {t : IntTy} (x y : JInt t) :
    modBitInteger x y =
      if y.val = 0 then .error .divideError else .ok (lit t (x.val.fmod y.val)) := by
  by_cases hy : y.val = 0
  · simpa [hy] using mod_zero x y hy
  · rw [if_neg hy]
    have hv := JuliaLean.Proofs.base.int.lit_of_fits
      (JuliaLean.Proofs.base.int.fmod_fits x y hy)
    unfold modBitInteger
    split
    · rename_i ht
      exact ((JuliaLean.Proofs.base.int.modSigned_proven.1 t ht _ (fldBitInteger_spec t) x y).2
        (lit t (x.val.fmod y.val))).mpr ⟨hy, hv⟩
    · rename_i ht
      exact ((JuliaLean.Proofs.base.int.modUnsigned_proven t (Bool.eq_false_iff.mpr ht) x y).2
        (lit t (x.val.fmod y.val))).mpr ⟨hy, hv⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem bitIntegerMixedFldmodConsistency_refuted : ¬ BitIntegerMixedFldmodConsistency := by
  intro h
  have bad := h.2.2 .u8 .i8 (JuliaLean.base.int.lit .u8 1)
    (JuliaLean.base.int.lit .i8 (-2)) (by decide) (by decide)
    (JuliaLean.base.int.lit .u8 255) (JuliaLean.base.int.lit .u8 255)
    (JuliaLean.base.int.lit .i8 (-1)) (by rfl) (by rfl)
  exact (by decide : ¬ ((JuliaLean.base.int.lit .u8 255).val =
    (JuliaLean.base.int.lit .i8 (-1)).val)) bad

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem roundDownFloatRemainderBound_refuted : ¬ RoundDownFloatRemainderBound := by
  intro h
  obtain ⟨r, hr, _, hlt⟩ := h
    (JuliaLean.Promotion.Fl.ofBits 0x8000000000000001)
    (one_float .f64) (by decide) (by decide) (by decide)
  have result : rem_Down floatModJl
      (JuliaLean.Promotion.Fl.ofBits 0x8000000000000001 : FV .f64)
      (one_float .f64) = .ok (one_float .f64) := by rfl
  rw [result] at hr
  cases hr
  exact (by decide : ¬ (lt_float (one_float .f64) (one_float .f64) = true)) hlt

theorem bitIntegerDivremProjection_refuted : ¬ BitIntegerDivremProjection := by
  intro h
  have hp := h .i8 (lit .i8 (-127)) (lit .i8 (-128)) .Up
  have hleft : divremBitIntegerMode (lit .i8 (-127)) (lit .i8 (-128)) .Up =
      .ok (lit .i8 1, lit .i8 1) := rfl
  have hright : (do
      let q ← divBitIntegerMode (lit .i8 (-127)) (lit .i8 (-128)) .Up
      let r ← remBitIntegerMode (lit .i8 (-127)) (lit .i8 (-128)) .Up
      pure (q, r)) = .ok (lit .i8 1, lit .i8 (-127)) := rfl
  rw [hleft, hright] at hp
  have hv := congrArg (fun qr : JInt .i8 × JInt .i8 => qr.2.val) (Except.ok.inj hp)
  change (1 : Int) = -127 at hv
  omega

theorem bitIntegerRemainderCorrect_refuted : ¬ BitIntegerRemainderCorrect := by
  intro h
  obtain ⟨r, hr, hv⟩ := (h .i8 (lit .i8 (-127)) (lit .i8 (-128)) .Up).2 (by
    unfold remainderError
    decide)
  have actual : remBitIntegerMode (lit .i8 (-127)) (lit .i8 (-128)) .Up =
      .ok (lit .i8 (-127)) := rfl
  rw [actual] at hr
  cases hr
  exact (by decide : ¬ ((lit .i8 (-127)).val =
    (lit .i8 (-127)).val - (lit .i8 (-128)).val *
      roundedIntegerQuotient (lit .i8 (-127)).val (lit .i8 (-128)).val .Up)) hv

private theorem fldmod_success {t : IntTy} (x y : JInt t) (h : ¬ divisionError x y) :
    fldmodBitInteger x y = .ok (lit t (x.val.fdiv y.val), lit t (x.val.fmod y.val)) := by
  have hy : y.val ≠ 0 := fun hz => h (Or.inl hz)
  have ho : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun hz => h (Or.inr hz)
  have qfit := ((div_ranges x y hy).2.2.2 ho).2.1
  have qv : (lit t (x.val.fdiv y.val)).val = x.val.fdiv y.val :=
    JuliaLean.Proofs.base.int.lit_of_fits qfit
  have hv : bitSub x (bitMul (lit t (x.val.fdiv y.val)) y) = lit t (x.val.fmod y.val) := by
    apply JuliaLean.Proofs.base.int.jint_eq
    change wrapInt t (x.val - (bitMul (lit t (x.val.fdiv y.val)) y).val) = _
    rw [bitMul, JuliaLean.Proofs.base.int.mulSame_val]
    rw [qv, JuliaLean.Proofs.base.int.wrapInt_sub_right]
    congr 1
    have he := fdiv_mul_add_fmod x.val y.val hy
    omega
  unfold fldmodBitInteger fldmod divremBitIntegerMode divremBitIntegerDirected
  simp only [RoundingMode.noConfusion, reduceCtorEq, ↓reduceIte]
  split <;> simp [divrem_BitSigned_Directed, divrem_Integer_Directed,
    fld_success x y h, Bind.bind, Except.bind, pure, Except.pure, hv]

theorem BitIntegerFldmodCorrect_proven : BitIntegerFldmodCorrect := by
  intro t x y
  by_cases he : divisionError x y
  · have hq := div_error x y he .Down
    have hp := divrem_error x y he .Down
    simpa [fldmodBitInteger, fldmod, fldBitInteger, fld_same_numeric,
      hq, Bind.bind, Except.bind] using hp
  · have hy : y.val ≠ 0 := fun hz => he (Or.inl hz)
    have hm : (if t.signed then JuliaLean.base.int.mod_BitSigned fldBitInteger x y
        else JuliaLean.base.int.mod_Unsigned x y) =
        .ok (lit t (x.val.fmod y.val)) := by
      simpa [modBitInteger, hy] using modBitInteger_eq x y
    rw [fldmod_success x y he, fld_success x y he, hm]
    rfl

end JuliaLean.Proofs.base.div

namespace JuliaLean.Proofs.base.div.Round1

open JuliaLean JuliaLean.base.div JuliaLean.base.float JuliaLean.Proofs.base.div

/-- Observe each actual integer type and mathematical value without changing an exception. -/
def pairTypedIntegerValues {q r : IntTy} (result : Jl (JInt q × JInt r)) :
    Jl ((IntTy × Int) × (IntTy × Int)) :=
  result.map (fun pair => ((q, pair.1.val), (r, pair.2.val)))

/-- The two documented exceptional divisions for a same-typed fixed-width pair. -/
def invalidSameTypeDivision {t : IntTy} (x y : JInt t) : Prop :=
  y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1)

/-- For each IEEE format, finite x and positive finite y have RoundDown remainder in [0,y).
Julia source: base/div.jl:79-129, specifically :128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:95-97; doc/src/base/math.md:20-23; doc/src/manual/mathematical-operations.md:618-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RoundDownIEEEFloatRemainderBound : Prop :=
  ∀ (T : FTy) (x y : FV T),
    isfinite_IEEEFloat x = true →
    isfinite_IEEEFloat y = true →
    lt_IEEEFloat (zero_float T) y = true →
    ∃ r : FV T,
      rem_Down (fun a b => .ok (mod_AbstractFloat a b)) x y = .ok r ∧
      le_IEEEFloat (zero_float T) r = true ∧
      lt_IEEEFloat r y = true

/-- For all different-width same-sign and all mixed-sign fixed-width inputs, fldmod agrees with separate fld and mod calls in types, values, and exceptions.
Julia source: base/div.jl:290-306,381-406,437-442; base/int.jl:281-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:379-389; doc/src/base/math.md:18,23,27; doc/src/manual/mathematical-operations.md:616,619,623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def MixedFldmodMatchesSeparateCalls : Prop :=
  (∀ (s u : IntTy) (x : JInt s) (y : JInt u),
    s.signed = u.signed → s ≠ u →
    pairTypedIntegerValues (fldmodMixedSameSign x y) = pairTypedIntegerValues (do
      let q ← fld_Real_Real JuliaLean.base.int.promoteSameSign divBitIntegerMode x y
      let r ← modMixedSameSign x y
      pure (q, r))) ∧
  (∀ (s u : IntTy) (x : JInt s) (y : JInt u),
    s.signed = true → u.signed = false →
    pairTypedIntegerValues (fldmodMixedSignedUnsigned x y) = pairTypedIntegerValues (do
      let q ← fld_Signed_Unsigned mixedDivSignedUnsigned x y
      let r ← modMixedSignedUnsigned x y
      pure (q, r))) ∧
  (∀ (u s : IntTy) (x : JInt u) (y : JInt s),
    u.signed = false → s.signed = true →
    pairTypedIntegerValues (fldmodMixedUnsignedSigned x y) = pairTypedIntegerValues (do
      let q ← fld_Unsigned_Signed mixedDivUnsignedSigned x y
      let r ← modMixedUnsignedSigned x y
      pure (q, r)))

/-- For every fixed-width type, same-typed divrem equals separate div and rem calls for all values and seven rounding modes, with the same first exception.
Julia source: base/div.jl:273-377,409-421,459-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:254-271; doc/src/base/math.md:16-21,26; doc/src/manual/mathematical-operations.md:622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SameTypeDivremMatchesSeparateCalls : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    divremBitIntegerMode x y mode = do
      let q ← divBitIntegerMode x y mode
      let r ← remBitIntegerMode x y mode
      pure (q, r)

/-- For every fixed-width type, same-typed divrem returns the exactly rounded quotient and mathematical remainder, or exactly the documented DivideError cases.
Julia source: base/div.jl:290-377,409-421,459-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-13,79-105,254-271; doc/src/base/math.md:16-21,26; doc/src/manual/mathematical-operations.md:615-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SameTypeDivremReconstruction : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    match divremBitIntegerMode x y mode with
    | .error error => error = .divideError ∧ invalidSameTypeDivision x y
    | .ok (q, r) =>
      ¬ invalidSameTypeDivision x y ∧
      q.val = roundedIntegerQuotient x.val y.val mode ∧
      r.val = x.val - q.val * y.val

open JuliaLean JuliaLean.base.div JuliaLean.base.float

/-- Observe a native integer result as its mathematical value, preserving errors. -/
def BitValueResult {t : IntTy} (result : Jl (JInt t)) : Jl Int :=
  result.map (fun value => value.val)

/-- Observe both native result values without identifying different error outcomes. -/
def BitPairValueResult {q r : IntTy} (result : Jl (JInt q × JInt r)) : Jl (Int × Int) :=
  result.map (fun value => (value.1.val, value.2.val))

/-- Division's exceptional input classes after same-signedness promotion. -/
def BitDivisionInvalid {a b : IntTy} (x : JInt a) (y : JInt b) : Prop :=
  y.val = 0 ∨
    (a.signed = true ∧ b.signed = true ∧
      x.val = (a.promote b).min ∧ y.val = -1)

/-- The three nearest modes obtain their remainder through division. -/
def BitNearestMode (mode : RoundingMode) : Prop :=
  mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp

/-- Directed and truncating remainder permit the signed minimum divided by -1. -/
def BitRemainderInvalid {a b : IntTy} (x : JInt a) (y : JInt b)
    (mode : RoundingMode) : Prop :=
  y.val = 0 ∨
    (a.signed = true ∧ b.signed = true ∧
      x.val = (a.promote b).min ∧ y.val = -1 ∧ BitNearestMode mode)

/-- Bind the actual same-type, promoted and mixed-signedness fld methods. -/
def BitFloorValues {a b : IntTy} (x : JInt a) (y : JInt b) : Jl Int :=
  if h : a = b then BitValueResult (fldBitInteger (h ▸ x) y)
  else if a.signed = b.signed then
    BitValueResult (fld_Real_Real JuliaLean.base.int.promoteSameSign divBitIntegerMode x y)
  else if a.signed then BitValueResult (fld_Signed_Unsigned mixedDivSignedUnsigned x y)
  else BitValueResult (fld_Unsigned_Signed mixedDivUnsignedSigned x y)

/-- Bind the actual same-type, promoted and mixed-signedness cld methods. -/
def BitCeilingValues {a b : IntTy} (x : JInt a) (y : JInt b) : Jl Int :=
  if h : a = b then BitValueResult (cldBitInteger (h ▸ x) y)
  else if a.signed = b.signed then
    BitValueResult (cld_Real_Real JuliaLean.base.int.promoteSameSign divBitIntegerMode x y)
  else if a.signed then BitValueResult (cld_Signed_Unsigned mixedDivSignedUnsigned x y)
  else BitValueResult (cld_Unsigned_Signed mixedDivUnsignedSigned x y)

/-- Bind the actual integer mod methods used in fldmod's documented comparison. -/
def BitModValues {a b : IntTy} (x : JInt a) (y : JInt b) : Jl Int :=
  if h : a = b then BitValueResult (modBitInteger (h ▸ x) y)
  else if a.signed = b.signed then BitValueResult (modMixedSameSign x y)
  else if a.signed then BitValueResult (modMixedSignedUnsigned x y)
  else BitValueResult (modMixedUnsignedSigned x y)

/-- Bind every fixed-width fldmod route, retaining both observed result values. -/
def BitFldmodValues {a b : IntTy} (x : JInt a) (y : JInt b) : Jl (Int × Int) :=
  if h : a = b then BitPairValueResult (fldmodBitInteger (h ▸ x) y)
  else if a.signed = b.signed then BitPairValueResult (fldmodMixedSameSign x y)
  else if a.signed then BitPairValueResult (fldmodMixedSignedUnsigned x y)
  else BitPairValueResult (fldmodMixedUnsignedSigned x y)


/-- Independent exact integer interval promised for each remainder rounding mode.
The nearest-ties variants use the same half-divisor magnitude bound. -/
def BitRemainderInterval (x y r : Int) (mode : RoundingMode) : Prop :=
  let magnitude := if y < 0 then -y else y
  match mode with
  | .ToZero => if 0 < x then 0 ≤ r ∧ r < magnitude else -magnitude < r ∧ r ≤ 0
  | .Down => if 0 < y then 0 ≤ r ∧ r < magnitude else -magnitude < r ∧ r ≤ 0
  | .Up => if 0 < y then -magnitude < r ∧ r ≤ 0 else 0 ≤ r ∧ r < magnitude
  | .FromZero => if 0 < x then -magnitude < r ∧ r ≤ 0 else 0 ≤ r ∧ r < magnitude
  | .Nearest | .NearestTiesAway | .NearestTiesUp => -magnitude ≤ 2 * r ∧ 2 * r ≤ magnitude

/-- A complete exception classification: the run fails exactly on the specified
input condition, and the only possible exception is DivideError. -/
def BitDivideErrorPolicy {A : Type} (run : Jl A) (invalid : Prop) : Prop :=
  ∀ error, run = .error error ↔ error = .divideError ∧ invalid

/-- For every fixed-width type and rounding mode, same-typed div returns the
exact rounded mathematical quotient or exactly the documented DivideError cases.
Julia source: base/div.jl:409-421,459-473; base/int.jl:353-358,1085-1089
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-21; base/rounding.jl:50-110;
doc/src/base/math.md:16-17; doc/src/manual/integers-and-floating-point-numbers.md:261-266
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SameTypeBitIntegerRoundedQuotients : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    match divBitIntegerMode x y mode with
    | .error error => error = .divideError ∧ BitDivisionInvalid x y
    | .ok q => ¬ BitDivisionInvalid x y ∧
        q.val = JuliaLean.Proofs.base.div.roundedIntegerQuotient x.val y.val mode

/-- For every fixed-width type and rounding mode, same-typed rem returns the
exact mathematical remainder in its documented interval, with its complete
zero-divisor and nearest-mode signed-overflow exception behavior.
Julia source: base/div.jl:127-138,326-377; base/int.jl:331-352
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:79-108; base/rounding.jl:50-110;
doc/src/base/math.md:20-21; doc/src/manual/integers-and-floating-point-numbers.md:263-266
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SameTypeBitIntegerRemainderEquation : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    match remBitIntegerMode x y mode with
    | .error error => error = .divideError ∧ BitRemainderInvalid x y mode
    | .ok r => ¬ BitRemainderInvalid x y mode ∧
        r.val = x.val - y.val *
          JuliaLean.Proofs.base.div.roundedIntegerQuotient x.val y.val mode ∧
        BitRemainderInterval x.val y.val r.val mode

/-- For every same-typed or mixed fixed-width pair, fld and cld return the exact
floor and ceiling quotients with division errors preserved; same-typed fld1
returns that exact ceiling under its documented legacy contract.
Julia source: base/div.jl:196,243,252,391-406,432-445,459-473
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:151-156,198-203,245-250;
doc/src/base/math.md:18-19; doc/src/manual/mathematical-operations.md:616-617;
doc/src/manual/integers-and-floating-point-numbers.md:263-264
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AllBitIntegerDirectedWrappers : Prop :=
  (∀ (a b : IntTy) (x : JInt a) (y : JInt b),
    (BitDivisionInvalid x y →
      BitFloorValues x y = .error .divideError ∧
      BitCeilingValues x y = .error .divideError) ∧
    (¬ BitDivisionInvalid x y →
      ∃ floor ceiling : Int,
        BitFloorValues x y = .ok floor ∧
        BitCeilingValues x y = .ok ceiling ∧
        floor = x.val.fdiv y.val ∧
        ceiling = -((-x.val).fdiv y.val))) ∧
  (∀ (t : IntTy) (x y : JInt t),
    match fld1BitInteger x y with
    | .error error => error = .divideError ∧ BitDivisionInvalid x y
    | .ok ceiling => ¬ BitDivisionInvalid x y ∧
        ceiling.val = -((-x.val).fdiv y.val))

/-- For all same-typed and mixed fixed-width pairs, fldmod has the same numerical
success/error outcome as the separate public fld/mod calls and returns the mathematical floored quotient and
modulus, including every error and the modulus sign/magnitude bound.
Julia source: base/div.jl:290-325,379-387,438-443; base/int.jl:331-352
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:379-385; base/int.jl:292-306;
doc/src/base/math.md:18,23,27; doc/src/manual/mathematical-operations.md:616,619,623
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AllBitIntegerFldmodContract : Prop :=
  ∀ (a b : IntTy) (x : JInt a) (y : JInt b),
    (BitFldmodValues x y = do
      let q ← BitFloorValues x y
      let r ← BitModValues x y
      pure (q, r)) ∧
    (match BitFldmodValues x y with
      | .error error => error = .divideError ∧ BitDivisionInvalid x y
      | .ok (q, r) => ¬ BitDivisionInvalid x y ∧
          q = x.val.fdiv y.val ∧ r = x.val - y.val * q ∧
          (if 0 < y.val then 0 ≤ r ∧ r < y.val else y.val < r ∧ r ≤ 0))

/-- For all same-typed fixed-width inputs, every public division wrapper has its
complete DivideError classification, while directed/truncating rem at the signed
minimum divided by -1 returns zero and nearest rem retains DivideError.
Julia source: base/div.jl:77,127-138,196,243,252,273-377,387,409-421,432-473;
base/int.jl:331-358,1085-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:261-266;
base/div.jl:5-21,79-108,151-156,198-203,245-250,254-271,379-385
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SameTypeBitIntegerDivisionErrorCases : Prop :=
  (∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    BitDivideErrorPolicy (divBitIntegerMode x y mode) (BitDivisionInvalid x y) ∧
    BitDivideErrorPolicy (remBitIntegerMode x y mode) (BitRemainderInvalid x y mode) ∧
    BitDivideErrorPolicy (divremBitIntegerMode x y mode) (BitDivisionInvalid x y) ∧
    BitDivideErrorPolicy (divDefaultBitInteger x y) (BitDivisionInvalid x y) ∧
    BitDivideErrorPolicy (fldBitInteger x y) (BitDivisionInvalid x y) ∧
    BitDivideErrorPolicy (cldBitInteger x y) (BitDivisionInvalid x y) ∧
    BitDivideErrorPolicy (fld1BitInteger x y) (BitDivisionInvalid x y) ∧
    BitDivideErrorPolicy (fldmodBitInteger x y) (BitDivisionInvalid x y)) ∧
  (∀ (t : IntTy) (x y : JInt t),
    t.signed = true → x.val = t.min → y.val = -1 →
    remBitIntegerMode x y .ToZero = .ok (JInt.lit t 0) ∧
    remBitIntegerMode x y .Down = .ok (JInt.lit t 0) ∧
    remBitIntegerMode x y .Up = .ok (JInt.lit t 0) ∧
    remBitIntegerMode x y .FromZero = .ok (JInt.lit t 0))

open JuliaLean JuliaLean.base.div JuliaLean.base.float

/-- Independent exceptional inputs after actual same-signedness promotion. -/
def AwayDivisionInvalid {a b : IntTy} (x : JInt a) (y : JInt b) : Prop :=
  y.val = 0 ∨
    (a.signed = true ∧ b.signed = true ∧
      x.val = (a.promote b).min ∧ y.val = -1)

/-- For all same-typed and mixed fixed-width inputs, division away from zero returns
the exact mathematical rounded quotient, or exactly the documented DivideError cases.
Julia source: base/div.jl:391-406,415-417,448-456,460-474;
base/int.jl:275-289,355-358,1085-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-21; base/rounding.jl:79-94;
doc/src/base/math.md:16-17; doc/src/manual/integers-and-floating-point-numbers.md:261-266
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AllBitIntegerAwayQuotient : Prop :=
  ∀ (a b : IntTy) (x : JInt a) (y : JInt b),
    match div_Integer_FromZero bitSignbit bitSignbit divBitIntegerMixedMode x y with
    | .error error => error = .divideError ∧ AwayDivisionInvalid x y
    | .ok q =>
      ¬ AwayDivisionInvalid x y ∧
      q.val = JuliaLean.Proofs.base.div.roundedIntegerQuotient x.val y.val .FromZero

end JuliaLean.Proofs.base.div.Round1

namespace JuliaLean.Proofs.base.div

open JuliaLean.base.div
open JuliaLean.base.float
open JuliaLean.Registry


namespace Archive20261102Round1

open JuliaLean JuliaLean.base.div JuliaLean.Proofs.base.div
open JuliaLean.Proofs.base.div.Round1

open JuliaLean JuliaLean.base.div JuliaLean.base.float JuliaLean.Proofs.base.div

/-- Concrete same-type IEEE binding of the public two nearest-ties remainder
method. Every operation is an existing source/runtime model, with no supplied
expected answer or callee-correctness hypothesis. -/
def IEEETiesRemainder {T : FTy} (x y : FV T) (mode : TiesMode) : FV T :=
  rem_AbstractFloat_Ties mod_AbstractFloat isnan_callee iszero_float
    lt_float floatmax_val abs_IEEEFloat (floatOfInt T (JInt.lit .i64 2))
    mul_float div_IEEEFloat neg_float signbit_float
    (mode = .NearestTiesUp) x y

/-- Independent rational-value observation for the exact mathematical
remainder, using finite IEEE numerator/denominator observations. -/
def ExactIEEERemainder {T : FTy} (x y r : FV T) (mode : RoundingMode) : Prop :=
  let xn := x.toRat.1
  let xd : Int := x.toRat.2
  let yn := y.toRat.1
  let yd : Int := y.toRat.2
  let rn := r.toRat.1
  let rd : Int := r.toRat.2
  let q := roundedIntegerQuotient (xn * yd) (yn * xd) mode
  r.isfinite = true ∧ rn * xd * yd = (xn * yd - q * yn * xd) * rd

/-- For same-type Float16/32/64 operands, both nearest-ties remainder modes
return the exact mathematical remainder for their stated tie rule, return the
finite dividend for an infinite divisor, and propagate invalid IEEE inputs as NaN.
Julia source: base/div.jl:139-149; base/float.jl:590-613
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:80-87; base/rounding.jl:97-108;
doc/src/base/math.md:20-21; doc/src/manual/integers-and-floating-point-numbers.md:355-386
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IEEEFloatTiesRemainderContract : Prop :=
  ∀ (T : FTy) (x y : FV T) (mode : TiesMode),
    let r := IEEETiesRemainder x y mode
    ((x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) →
      r.isnan = true) ∧
    (x.isfinite = true → y.isinf = true → r.toBits = x.toBits) ∧
    (x.isfinite = true → y.isfinite = true → y.iszero = false →
      ExactIEEERemainder x y r
        (match mode with
         | .NearestTiesAway => .NearestTiesAway
         | .NearestTiesUp => .NearestTiesUp))

/-- The concrete IEEE flipsign dispatch used by the nearest-even remainder
callee. The Float16 fallback executes the existing generic Real source model;
its three callees always return `.ok`, so its error arm is unreachable. -/
def IEEEFlipSign : (T : FTy) → FV T → FV T → FV T
  | .f16, x, y =>
    match JuliaLean.base.number.flipsign
        (fun z => .ok (JuliaLean.base.floatfuncs.signbit_Float16 z))
        (fun z => .ok (neg_IEEEFloat z))
        (fun z => .ok (JuliaLean.base.operators.unaryPlusNumber z))
        JuliaLean.base.operators.ifelseValue x y with
    | .ok value => value
    | .error _ => nan_float .f16
  | .f32, x, y => JuliaLean.base.floatfuncs.flipsign_Float32 x y
  | .f64, x, y => JuliaLean.base.floatfuncs.flipsign_Float64 x y

/-- `math.remNearest` reads only `floatmin`, `rem`, and `flipsign` from this
large shared record; those three fields are bound to their existing models.
All other fields are fixed inert padding and are never called by this subject.
They are not assumptions or expected numerical answers. -/
def IEEENearestRemainderOps (T : FTy) : JuliaLean.base.math.IEEEOps T where
  sqrtLlvm := fun _ => zero_float T
  eps := zero_float T
  floatmin := floatmin_float T
  floatmax := zero_float T
  invFloatmin := zero_float T
  pi := zero_float T
  fma := fun _ _ _ => zero_float T
  twoMul := fun _ _ => (zero_float T, zero_float T)
  trunc := fun _ => zero_float T
  rem := rem_IEEEFloat
  flipsign := IEEEFlipSign T
  minFloat := fun _ _ => zero_float T
  maxFloat := fun _ _ => zero_float T
  clampUnsigned := fun _ _ _ => 0
  addFast := fun _ _ => zero_float T
  oneunit := fun _ => zero_float T
  inverse := fun _ => zero_float T
  greater := fun _ _ => false
  muladd := fun _ _ _ => zero_float T
  abs2 := fun _ => zero_float T
  haveFma := false

/-- Existing source dispatch for all seven same-type IEEE remainder modes.
The nearest-even specialization is in math.jl, rather than the generic
non-Integer nearest method in div.jl. Every branch is nonthrowing IEEE code. -/
def IEEERemainderBound {T : FTy} (x y : FV T) (mode : RoundingMode) : Jl (FV T) :=
  match mode with
  | .ToZero => rem_ToZero (fun a b => .ok (rem_IEEEFloat a b)) x y
  | .Down => rem_Down (fun a b => .ok (mod_AbstractFloat a b)) x y
  | .Up => rem_Up (fun a b => .ok (mod_AbstractFloat a b)) neg_IEEEFloat x y
  | .Nearest => .ok (JuliaLean.base.math.remNearest (IEEENearestRemainderOps T) x y)
  | .NearestTiesAway => .ok (IEEETiesRemainder x y .NearestTiesAway)
  | .NearestTiesUp => .ok (IEEETiesRemainder x y .NearestTiesUp)
  | .FromZero => rem_FromZero signbit_float signbit_float
      (fun a b r => if r = .Up then
        rem_Up (fun c d => .ok (mod_AbstractFloat c d)) neg_IEEEFloat a b
       else rem_Down (fun c d => .ok (mod_AbstractFloat c d)) a b) x y

/-- Eliminate the unreachable exception arm of the nonthrowing IEEE dispatch
so it fits the existing pure AbstractFloat division mirror. -/
def IEEERemainderValue {T : FTy} (x y : FV T) (mode : RoundingMode) : FV T :=
  match IEEERemainderBound x y mode with
  | .ok value => value
  | .error _ => nan_float T

/-- Unqualified round dispatches through the modeled keyword wrapper to the
existing IEEE nearest-even rounding primitive. -/
def IEEERoundDefault {T : FTy} (x : FV T) : FV T :=
  JuliaLean.base.rounding.roundKeyword
    (fun value _ (_ : Unit) => round_Nearest_llvm value) x ()

def IEEEQuotientBound {T : FTy} (x y : FV T) (mode : RoundingMode) : FV T :=
  div_AbstractFloat div_IEEEFloat IEEERemainderValue sub_IEEEFloat IEEERoundDefault x y mode

/-- Exact rational quotient rounded mathematically, independent of the source
floating-point division and remainder calculations. -/
def ExactIEEEQuotient {T : FTy} (x y : FV T) (mode : RoundingMode) : Int :=
  roundedIntegerQuotient (x.toRat.1 * (y.toRat.2 : Int))
    (y.toRat.1 * (x.toRat.2 : Int)) mode

/-- The documented finite exact-integer region and IEEE exceptional cases.
The accuracy precondition is the literal input condition `eps(x/y) ≤ 1`, using
the existing `/`, `eps`, comparison and one models; it never inspects the
rounded-division implementation's output. Values outside the documented
accuracy region are not assigned an unsupported exactness promise. -/
def IEEEQuotientBehavior {T : FTy} (x y : FV T) (mode : RoundingMode)
    (result : Jl (FV T)) : Prop :=
  ((x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) →
    ∃ value, result = .ok value ∧ value.isnan = true) ∧
  (x.isfinite = true → y.isinf = true →
    ∃ value, result = .ok value ∧ value.iszero = true) ∧
  (x.isfinite = true → y.isfinite = true → y.iszero = false →
    le_IEEEFloat (eps_IEEEFloat (div_IEEEFloat x y)) (one_float T) = true →
    ∃ value, result = .ok value ∧ value.isfinite = true ∧
      value.toRat.1 = ExactIEEEQuotient x y mode * (value.toRat.2 : Int))

/-- Same-type Float16/32/64 division in every rounding mode, together with fld
and cld and the default truncating division call, returns the exact rounded quotient throughout the documented safe
integer region and has the IEEE NaN/zero results on exceptional operands.
Julia source: base/div.jl:77,432-433,480; base/float.jl:458-461,487-490,590-613,987-995;
base/math.jl:1122-1145; base/rounding.jl:483
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:6-13,46-50,152-154,167-171,199-201,214-218;
doc/src/base/math.md:16-19; doc/src/manual/integers-and-floating-point-numbers.md:355-386
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IEEEFloatDivisionContract : Prop :=
  ∀ (T : FTy) (x y : FV T),
    (∀ mode, IEEEQuotientBehavior x y mode (.ok (IEEEQuotientBound x y mode))) ∧
    IEEEQuotientBehavior x y .ToZero
      (div_default (fun a b mode => .ok (IEEEQuotientBound a b mode)) x y) ∧
    IEEEQuotientBehavior x y .Down
      (fld_same_numeric (fun a b mode => .ok (IEEEQuotientBound a b mode)) x y) ∧
    IEEEQuotientBehavior x y .Up
      (cld_same_numeric (fun a b mode => .ok (IEEEQuotientBound a b mode)) x y)

end Archive20261102Round1

end JuliaLean.Proofs.base.div

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean JuliaLean.base.div JuliaLean.base.float
open JuliaLean.Proofs.base.div JuliaLean.Proofs.base.div.Round1

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

theorem FloatRemDownBoundV2_refuted : ¬ JuliaLean.Proofs.base.div.Round1.RoundDownIEEEFloatRemainderBound := by
  intro h
  obtain ⟨r, hr, _, hlt⟩ := h .f64
    (JuliaLean.Promotion.Fl.ofBits 0x8000000000000001)
    (one_float .f64) (by decide) (by decide) (by decide)
  have result : rem_Down (fun a b => .ok (mod_AbstractFloat a b))
      (JuliaLean.Promotion.Fl.ofBits 0x8000000000000001 : FV .f64)
      (one_float .f64) = .ok (one_float .f64) := by rfl
  rw [result] at hr
  cases hr
  exact (by decide : ¬ (lt_IEEEFloat (one_float .f64) (one_float .f64) = true)) hlt

theorem IntarithDivisionFldmodConsistencyV2_refuted : ¬ JuliaLean.Proofs.base.div.Round1.MixedFldmodMatchesSeparateCalls := by
  intro h
  have bad := h.2.2 .u8 .i8 (JInt.lit .u8 1) (JInt.lit .i8 (-2))
    (by decide) (by decide)
  change (Except.ok ((IntTy.u8, (255 : Int)), (IntTy.u8, (255 : Int))) :
    Jl ((IntTy × Int) × (IntTy × Int))) =
    .ok ((IntTy.u8, (255 : Int)), (IntTy.i8, (-1 : Int))) at bad
  cases bad

theorem FloatintcovDivremRoundupTypeminV2_refuted : ¬ JuliaLean.Proofs.base.div.Round1.SameTypeDivremMatchesSeparateCalls := by
  exact bitIntegerDivremProjection_refuted

theorem DivBitintegerDivremReconstruction_refuted : ¬ JuliaLean.Proofs.base.div.Round1.SameTypeDivremReconstruction := by
  intro h
  have bad := h .u8 (JInt.lit .u8 1) (JInt.lit .u8 2) .Up
  change ¬ invalidSameTypeDivision (JInt.lit .u8 1) (JInt.lit .u8 2) ∧
    (1 : Int) = roundedIntegerQuotient 1 2 .Up ∧
    (255 : Int) = 1 - 1 * 2 at bad
  have impossible := bad.2.2
  omega

theorem divPromoteSelf (t : IntTy) : t.promote t = t := by
  cases t <;> rfl

theorem divInvalidSameType {t : IntTy} (x y : JInt t) :
    BitDivisionInvalid x y ↔ invalidSameTypeDivision x y := by
  simp only [BitDivisionInvalid, invalidSameTypeDivision, divPromoteSelf,
    and_self_left]

theorem DivBitintegerRoundedQuotientV2_proven : JuliaLean.Proofs.base.div.Round1.SameTypeBitIntegerRoundedQuotients := by
  intro t x y mode
  have contract := BitIntegerDivisionCorrect_proven t x y mode
  change (invalidSameTypeDivision x y → divBitIntegerMode x y mode = .error .divideError) ∧
    (¬ invalidSameTypeDivision x y → ∃ q : JInt t,
      divBitIntegerMode x y mode = .ok q ∧
      q.val = roundedIntegerQuotient x.val y.val mode) at contract
  by_cases invalid : invalidSameTypeDivision x y
  · rw [contract.1 invalid]
    exact ⟨rfl, (divInvalidSameType x y).mpr invalid⟩
  · obtain ⟨q, run, value⟩ := contract.2 invalid
    rw [run]
    exact ⟨fun h => invalid ((divInvalidSameType x y).mp h), value⟩

theorem DivBitintegerRemainderEquationV2_refuted : ¬ JuliaLean.Proofs.base.div.Round1.SameTypeBitIntegerRemainderEquation := by
  intro h
  have bad := h .i8 (JInt.lit .i8 (-127)) (JInt.lit .i8 (-128)) .Up
  change ¬ BitRemainderInvalid (JInt.lit .i8 (-127)) (JInt.lit .i8 (-128)) .Up ∧
    (-127 : Int) = -127 - (-128) * roundedIntegerQuotient (-127) (-128) .Up ∧
    BitRemainderInterval (-127) (-128) (-127) .Up at bad
  have quotient : roundedIntegerQuotient (-127) (-128) .Up = 1 := by decide
  rw [quotient] at bad
  have impossible := bad.2.1
  omega

theorem DivBitintegerDirectedWrapperCorrectV2_refuted : ¬ JuliaLean.Proofs.base.div.Round1.AllBitIntegerDirectedWrappers := by
  intro h
  have valid : ¬ BitDivisionInvalid (JInt.lit .u8 1) (JInt.lit .i8 (-2)) := by
    unfold BitDivisionInvalid
    decide
  obtain ⟨floor, ceiling, run, _, exactFloor, _⟩ :=
    (h.1 .u8 .i8 (JInt.lit .u8 1) (JInt.lit .i8 (-2))).2 valid
  have actual : BitFloorValues (JInt.lit .u8 1) (JInt.lit .i8 (-2)) = .ok 255 := by rfl
  rw [actual] at run
  cases run
  change (255 : Int) = -1 at exactFloor
  omega

theorem DivBitintegerFldmodContractV2_refuted : ¬ JuliaLean.Proofs.base.div.Round1.AllBitIntegerFldmodContract := by
  intro h
  have bad := (h .u8 .i8 (JInt.lit .u8 1) (JInt.lit .i8 (-2))).1
  change (Except.ok ((255 : Int), (255 : Int)) : Jl (Int × Int)) = .ok (255, -1) at bad
  cases bad

theorem DivBitintegerAwayQuotient_refuted : ¬ JuliaLean.Proofs.base.div.Round1.AllBitIntegerAwayQuotient := by
  intro h
  have bad := h .u8 .i8 (JInt.lit .u8 1) (JInt.lit .i8 (-2))
  change ¬ AwayDivisionInvalid (JInt.lit .u8 1) (JInt.lit .i8 (-2)) ∧
    (255 : Int) = roundedIntegerQuotient 1 (-2) .FromZero at bad
  have actual : roundedIntegerQuotient 1 (-2) .FromZero = -1 := by decide
  rw [actual] at bad
  have impossible := bad.2
  omega

def divAbsValue (z : Int) : Int := if z < 0 then -z else z

def divSignsAgree (x y : Int) : Bool := (x < 0) = (y < 0)

theorem divNearestTiesViaFloor (x y : Int) (hy : y ≠ 0) (tiesUp : Bool) :
    roundedIntegerQuotient x y (if tiesUp then .NearestTiesUp else .NearestTiesAway) =
      x.fdiv y +
        (if divAbsValue y < 2 * divAbsValue (x.fmod y) ∨
          (2 * divAbsValue (x.fmod y) = divAbsValue y ∧
            (tiesUp = true ∨ (x < 0 ↔ y < 0))) then 1 else 0) := by
  have magnitudeBound : (x.tmod y).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_le _ _
  have nonnegative : 0 ≤ x → 0 ≤ x.tmod y ∧ x.tmod y ≤ x := by
    intro h
    have lower := Int.tmod_nonneg y h
    have upper : ((x.tmod y).natAbs : Int) ≤ (x.natAbs : Int) :=
      Int.ofNat_le.mpr magnitudeBound
    rw [Int.natAbs_of_nonneg lower, Int.natAbs_of_nonneg h] at upper
    exact ⟨lower, upper⟩
  have nonpositive : x < 0 → x ≤ x.tmod y ∧ x.tmod y ≤ 0 := by
    intro h
    have bound := Int.tmod_nonneg y (show 0 ≤ -x by omega)
    rw [Int.neg_tmod] at bound
    have remainderNonpositive : x.tmod y ≤ 0 := by omega
    have absoluteBound : ((x.tmod y).natAbs : Int) ≤ (x.natAbs : Int) :=
      Int.ofNat_le.mpr magnitudeBound
    rw [Int.ofNat_natAbs_of_nonpos remainderNonpositive,
      Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)] at absoluteBound
    exact ⟨by omega, remainderNonpositive⟩
  have positiveBounds : 0 < y → -y < x.tmod y ∧ x.tmod y < y := by
    intro h
    exact ⟨Int.lt_tmod_of_pos x h, Int.tmod_lt_of_pos x h⟩
  have negativeBounds : y < 0 → y < x.tmod y ∧ x.tmod y < -y := by
    intro h
    have lo := Int.lt_tmod_of_pos x (show 0 < -y by omega)
    have hi := Int.tmod_lt_of_pos x (show 0 < -y by omega)
    rw [Int.tmod_neg] at lo hi
    exact ⟨by omega, hi⟩
  obtain ⟨floorRule, modulusRule⟩ := fdiv_fmod_tdiv x y hy
  have formula : roundedIntegerQuotient x y
      (if tiesUp then .NearestTiesUp else .NearestTiesAway) =
      (if y = 0 then 0 else
        if 2 * divAbsValue (x.tmod y) > divAbsValue y then
          x.tdiv y + if divSignsAgree x y then 1 else -1
        else if 2 * divAbsValue (x.tmod y) < divAbsValue y then x.tdiv y
        else if tiesUp then
          if divSignsAgree x y then
            x.tdiv y + if divSignsAgree x y then 1 else -1
          else x.tdiv y
        else x.tdiv y + if divSignsAgree x y then 1 else -1) := by
    cases tiesUp <;> rfl
  rw [formula, if_neg hy, floorRule, modulusRule]
  simp only [divAbsValue, divSignsAgree, Bool.decide_coe]
  cases tiesUp <;>
    by_cases hx : 0 ≤ x <;>
    rcases Int.lt_or_gt_of_ne hy with hyNeg | hyPos <;>
    simp_all <;> (repeat' (split <;> simp_all)) <;> omega

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.ChatGPT.Batch8.Group7
open JuliaLean JuliaLean.base.div JuliaLean.base.float
open JuliaLean.Proofs.base.div JuliaLean.Proofs.base.div.Round1

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-- Same-type promotion is the identity. -/
theorem g7DivDivPromoteSelf (t : IntTy) : t.promote t = t := by
  cases t <;> rfl

/-- The expanded v2 exceptional-input predicate agrees with its predecessor. -/
theorem g7DivDivInvalidSameType {t : IntTy} (x y : JInt t) :
    BitDivisionInvalid x y ↔ invalidSameTypeDivision x y := by
  simp only [BitDivisionInvalid, invalidSameTypeDivision, g7DivDivPromoteSelf,
    and_self_left]

theorem g7DivDivremQuotientProjection {t : IntTy} (x y : JInt t) (mode : RoundingMode) :
    (divremBitIntegerMode x y mode).map Prod.fst = divBitIntegerMode x y mode := by
  cases mode with
  | ToZero =>
    simp only [divremBitIntegerMode, divBitIntegerMode, reduceCtorEq, ↓reduceIte]
    unfold divremBitIntegerToZero
    split <;> simp only [divrem_BitSigned_Directed, divrem_Integer_Directed,
      reduceCtorEq, ↓reduceIte] <;>
      cases divBitIntegerToZero x y <;> rfl
  | Down =>
    simp only [divremBitIntegerMode, divBitIntegerMode, reduceCtorEq, ↓reduceIte]
    unfold divremBitIntegerDirected
    split <;> simp only [divrem_BitSigned_Directed, divrem_Integer_Directed,
      fldBitInteger, fld_same_numeric, divBitIntegerMode, reduceCtorEq, ↓reduceIte] <;>
      cases divBitIntegerDown x y <;> rfl
  | Up =>
    simp only [divremBitIntegerMode, divBitIntegerMode, reduceCtorEq, ↓reduceIte]
    unfold divremBitIntegerDirected
    split <;> simp only [divrem_BitSigned_Directed, divrem_Integer_Directed,
      divBitIntegerMode, reduceCtorEq, ↓reduceIte] <;>
      cases divBitIntegerUp x y <;> rfl
  | Nearest =>
    simp only [divremBitIntegerMode, divBitIntegerMode, div_Integer_Nearest,
      divremBitIntegerNearestModes, reduceCtorEq, ↓reduceIte]
    cases divremBitIntegerNearest x y <;> rfl
  | NearestTiesAway =>
    simp only [divremBitIntegerMode, divBitIntegerMode, div_Integer_Nearest,
      divremBitIntegerNearestModes, reduceCtorEq, ↓reduceIte]
    cases divremBitIntegerTiesAway x y <;> rfl
  | NearestTiesUp =>
    simp only [divremBitIntegerMode, divBitIntegerMode, div_Integer_Nearest,
      divremBitIntegerNearestModes, reduceCtorEq, ↓reduceIte]
    cases divremBitIntegerTiesUp x y <;> rfl
  | FromZero =>
    simp only [divremBitIntegerMode, divBitIntegerMode, divrem_FromZero,
      div_Integer_FromZero, reduceCtorEq, ↓reduceIte]
    by_cases signs : bitSignbit x = bitSignbit y
    · simp only [if_pos signs, divremBitIntegerUpDown, divBitIntegerUpDown,
        reduceCtorEq, ↓reduceIte]
      unfold divremBitIntegerDirected
      split <;> simp only [divrem_BitSigned_Directed, divrem_Integer_Directed,
        divBitIntegerMode, reduceCtorEq, ↓reduceIte] <;>
        cases divBitIntegerUp x y <;> rfl
    · simp only [if_neg signs, divremBitIntegerUpDown, divBitIntegerUpDown,
        reduceCtorEq, ↓reduceIte]
      unfold divremBitIntegerDirected
      split <;> simp only [divrem_BitSigned_Directed, divrem_Integer_Directed,
        fldBitInteger, fld_same_numeric, divBitIntegerMode, reduceCtorEq, ↓reduceIte] <;>
        cases divBitIntegerDown x y <;> rfl

/-- Mapping a successful value cannot introduce or erase an exception. -/
theorem g7DivDivMapError {A B : Type} (run : Jl A) (f : A → B) (error : JlError) :
    run.map f = .error error ↔ run = .error error := by
  cases run <;> simp only [Except.map, Except.error.injEq, reduceCtorEq]

theorem g7DivDivOperationErrorPolicy {t : IntTy} (x y : JInt t) (mode : RoundingMode) :
    BitDivideErrorPolicy (divBitIntegerMode x y mode) (BitDivisionInvalid x y) := by
  intro error
  have contract := BitIntegerDivisionCorrect_proven t x y mode
  constructor
  · intro run
    by_cases invalid : invalidSameTypeDivision x y
    · have errorRun := contract.1 invalid
      rw [run] at errorRun
      exact ⟨Except.error.inj errorRun, (g7DivDivInvalidSameType x y).mpr invalid⟩
    · obtain ⟨value, valueRun, _⟩ := contract.2 invalid
      rw [run] at valueRun
      cases valueRun
  · rintro ⟨rfl, invalid⟩
    exact contract.1 ((g7DivDivInvalidSameType x y).mp invalid)

theorem g7DivDivremOperationErrorPolicy {t : IntTy} (x y : JInt t) (mode : RoundingMode) :
    BitDivideErrorPolicy (divremBitIntegerMode x y mode) (BitDivisionInvalid x y) := by
  intro error
  rw [← g7DivDivMapError (divremBitIntegerMode x y mode) Prod.fst error,
    g7DivDivremQuotientProjection]
  exact g7DivDivOperationErrorPolicy x y mode error

theorem g7DivDivLitZeroValue (t : IntTy) : (JInt.lit t 0).val = 0 := by
  cases t <;> rfl

/-- Negation preserves the zero/nonzero test, including signed minima. -/
theorem g7DivDivNegZero {t : IntTy} (x : JInt t) :
    (JuliaLean.base.int.neg x).val = 0 ↔ x.val = 0 := by
  constructor
  · intro hz
    have ring := (JuliaLean.Proofs.base.int.primitiveRingLaws_proven t x x x).2.2.1
    have values := congrArg (fun n : JInt t => n.val) ring
    rw [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val, hz,
      Int.zero_add, JuliaLean.Proofs.base.int.wrapInt_val] at values
    exact values.trans (g7DivDivLitZeroValue t)
  · intro hz
    rw [JuliaLean.base.int.neg, JuliaLean.Proofs.base.int.neg_int_val, hz, Int.neg_zero]
    exact g7DivDivLitZeroValue t

theorem g7DivDivModError {t : IntTy} (x y : JInt t) (error : JlError) :
    modBitInteger x y = .error error ↔ error = .divideError ∧ y.val = 0 := by
  rw [modBitInteger_eq]
  by_cases hy : y.val = 0 <;> simp only [hy, ↓reduceIte, reduceCtorEq,
    Except.error.injEq, and_true, and_false, eq_comm]

theorem g7DivDivNearestRemainderProjection {t : IntTy} (x y : JInt t)
    (mode : RoundingMode) (nearest : BitNearestMode mode) :
    remBitIntegerMode x y mode = (divremBitIntegerMode x y mode).map Prod.snd := by
  rcases nearest with rfl | rfl | rfl <;>
    simp only [remBitIntegerMode, divremBitIntegerMode, rem_Integer_Nearest,
      rem_Integer_Ties, divremBitIntegerNearestModes, reduceCtorEq, ↓reduceIte]
  · cases divremBitIntegerNearest x y <;> rfl
  · cases divremBitIntegerTiesAway x y <;> rfl
  · cases divremBitIntegerTiesUp x y <;> rfl

theorem g7DivDivNearestInvalid {t : IntTy} (x y : JInt t) (mode : RoundingMode)
    (nearest : BitNearestMode mode) :
    BitRemainderInvalid x y mode ↔ BitDivisionInvalid x y := by
  simp only [BitRemainderInvalid, BitDivisionInvalid, nearest, and_true]

theorem g7DivDivRemainderOperationErrorPolicy {t : IntTy} (x y : JInt t) (mode : RoundingMode) :
    BitDivideErrorPolicy (remBitIntegerMode x y mode) (BitRemainderInvalid x y mode) := by
  intro error
  by_cases nearest : BitNearestMode mode
  · rw [g7DivDivNearestRemainderProjection x y mode nearest,
      g7DivDivMapError, g7DivDivNearestInvalid x y mode nearest]
    exact g7DivDivremOperationErrorPolicy x y mode error
  · have hn : mode ≠ .Nearest ∧ mode ≠ .NearestTiesAway ∧ mode ≠ .NearestTiesUp := by
      unfold BitNearestMode at nearest
      exact ⟨fun h => nearest (Or.inl h),
        fun h => nearest (Or.inr (Or.inl h)),
        fun h => nearest (Or.inr (Or.inr h))⟩
    have invalid : BitRemainderInvalid x y mode ↔ y.val = 0 := by
      simp only [BitRemainderInvalid, nearest, and_false, or_false]
    rw [invalid]
    cases mode with
    | ToZero =>
      simp only [remBitIntegerMode, rem_ToZero, reduceCtorEq, ↓reduceIte,
        JuliaLean.Proofs.base.int.remSame_eq]
      by_cases hz : y.val = 0 <;> simp only [hz, ↓reduceIte, reduceCtorEq,
        Except.error.injEq, and_true, and_false, eq_comm]
    | Down =>
      simpa only [remBitIntegerMode, rem_Down, reduceCtorEq, ↓reduceIte] using
        g7DivDivModError x y error
    | Up =>
      simpa only [remBitIntegerMode, rem_Up, reduceCtorEq, ↓reduceIte,
        g7DivDivNegZero] using g7DivDivModError x (JuliaLean.base.int.neg y) error
    | FromZero =>
      simp only [remBitIntegerMode, rem_FromZero, reduceCtorEq, ↓reduceIte]
      split
      · simpa only [remBitIntegerUpDown, rem_Up, reduceCtorEq, ↓reduceIte,
          g7DivDivNegZero] using g7DivDivModError x (JuliaLean.base.int.neg y) error
      · simpa only [remBitIntegerUpDown, rem_Down, reduceCtorEq, ↓reduceIte] using
          g7DivDivModError x y error
    | Nearest => exact False.elim (hn.1 rfl)
    | NearestTiesAway => exact False.elim (hn.2.1 rfl)
    | NearestTiesUp => exact False.elim (hn.2.2 rfl)

/-- Every exposed same-type wrapper has exactly the specified exceptions. -/
theorem DivBitintegerDivisionErrorCasesV2_proven : JuliaLean.Proofs.base.div.Round1.SameTypeBitIntegerDivisionErrorCases := by
  constructor
  · intro t x y mode
    refine ⟨g7DivDivOperationErrorPolicy x y mode, g7DivDivRemainderOperationErrorPolicy x y mode,
      g7DivDivremOperationErrorPolicy x y mode, ?_, ?_, ?_, ?_, ?_⟩
    · exact g7DivDivOperationErrorPolicy x y .ToZero
    · exact g7DivDivOperationErrorPolicy x y .Down
    · exact g7DivDivOperationErrorPolicy x y .Up
    · exact g7DivDivOperationErrorPolicy x y .Up
    · exact g7DivDivremOperationErrorPolicy x y .Down
  · intro t x y signed minValue minusOne
    have existing := (bitIntegerDivisionErrorCases_proven.2 t x y signed minValue minusOne).2.2.2.2
    exact ⟨existing.1, existing.2.1, existing.2.2.1, existing.2.2.2.1⟩




open JuliaLean.Proofs.base.div.Archive20261102Round1

/-- All modeled IEEE remainder dispatches are total; this isolates the numerical obligation. -/
theorem g7DivDivIEEERemainderTotal {T : FTy} (x y : FV T) (mode : RoundingMode) :
    ∃ value : FV T, IEEERemainderBound x y mode = .ok value := by
  cases mode with
  | ToZero => exact ⟨rem_IEEEFloat x y, rfl⟩
  | Down => exact ⟨mod_AbstractFloat x y, rfl⟩
  | Up => exact ⟨mod_AbstractFloat x (neg_IEEEFloat y), rfl⟩
  | Nearest => exact ⟨JuliaLean.base.math.remNearest (IEEENearestRemainderOps T) x y, rfl⟩
  | NearestTiesAway => exact ⟨IEEETiesRemainder x y .NearestTiesAway, rfl⟩
  | NearestTiesUp => exact ⟨IEEETiesRemainder x y .NearestTiesUp, rfl⟩
  | FromZero =>
    by_cases sameSign : signbit_float x = signbit_float y
    · refine ⟨mod_AbstractFloat x (neg_IEEEFloat y), ?_⟩
      simp only [IEEERemainderBound, rem_FromZero, if_pos sameSign,
        reduceCtorEq, ↓reduceIte, rem_Up]
    · refine ⟨mod_AbstractFloat x y, ?_⟩
      simp only [IEEERemainderBound, rem_FromZero, if_neg sameSign,
        reduceCtorEq, ↓reduceIte, rem_Down]

/-- Extracting the remainder value never takes the exception fallback. -/
theorem g7DivDivIEEERemainderValueRun {T : FTy} (x y : FV T) (mode : RoundingMode) :
    IEEERemainderBound x y mode = .ok (IEEERemainderValue x y mode) := by
  obtain ⟨value, run⟩ := g7DivDivIEEERemainderTotal x y mode
  simp only [IEEERemainderValue, run]

/-- The source NaN callee agrees with the bit-level IEEE observation. -/
theorem g7DivDivIEEENaNCallee {T : FTy} (x : FV T) : isnan_callee x = x.isnan := by
  unfold isnan_callee eq_float JuliaLean.C.jlEqFloat JuliaLean.Promotion.Fl.eq
  cases hx : x.isnan <;> simp [hx]

/-- The first NaN branch of the ties algorithm preserves the modulo result. -/
theorem g7DivDivIEEETiesNaNBranch {T : FTy} (x y : FV T) (mode : TiesMode)
    (nanResult : isnan_callee (mod_AbstractFloat x y) = true) :
    IEEETiesRemainder x y mode = mod_AbstractFloat x y := by
  simp [IEEETiesRemainder, rem_AbstractFloat_Ties, nanResult]

/-- A NaN modulo result makes both nearest-tie remainders NaN. -/
theorem g7DivDivIEEETiesPreservesNaNModulo {T : FTy} (x y : FV T) (mode : TiesMode)
    (nanResult : (mod_AbstractFloat x y).isnan = true) :
    (IEEETiesRemainder x y mode).isnan = true := by
  rw [g7DivDivIEEETiesNaNBranch x y mode (by rw [g7DivDivIEEENaNCallee]; exact nanResult)]
  exact nanResult

/-- If both modulo signs return the same value, the ties algorithm returns it as well. -/
theorem g7DivDivIEEETiesEqualModuloResults {T : FTy} (x y value : FV T) (mode : TiesMode)
    (positive : mod_AbstractFloat x y = value)
    (negative : mod_AbstractFloat x (neg_float y) = value) :
    IEEETiesRemainder x y mode = value := by
  simp [IEEETiesRemainder, rem_AbstractFloat_Ties, positive, negative]

/-- Default div, fld and cld introduce no new numerical obligations beyond the seven modes. -/
theorem g7DivDivIEEEContractOfModeBehavior
    (modes : ∀ (T : FTy) (x y : FV T) (mode : RoundingMode),
      IEEEQuotientBehavior x y mode (.ok (IEEEQuotientBound x y mode))) :
    IEEEFloatDivisionContract := by
  intro T x y
  exact ⟨modes T x y, modes T x y .ToZero, modes T x y .Down, modes T x y .Up⟩

/-- Conversely, the full contract includes the modewise numerical obligation. -/
theorem g7DivDivIEEEModeBehaviorOfContract (contract : IEEEFloatDivisionContract)
    (T : FTy) (x y : FV T) (mode : RoundingMode) :
    IEEEQuotientBehavior x y mode (.ok (IEEEQuotientBound x y mode)) :=
  (contract T x y).1 mode

def g7DivDivAbsValue (z : Int) : Int := if z < 0 then -z else z

def g7DivDivSignsAgree (x y : Int) : Bool := (x < 0) = (y < 0)

/-- Exact nearest-tie quotients can be selected from the mathematical floor and modulus. -/
theorem g7DivDivNearestTiesViaFloor (x y : Int) (hy : y ≠ 0) (tiesUp : Bool) :
    roundedIntegerQuotient x y (if tiesUp then .NearestTiesUp else .NearestTiesAway) =
      x.fdiv y +
        (if g7DivDivAbsValue y < 2 * g7DivDivAbsValue (x.fmod y) ∨
          (2 * g7DivDivAbsValue (x.fmod y) = g7DivDivAbsValue y ∧
            (tiesUp = true ∨ (x < 0 ↔ y < 0))) then 1 else 0) := by
  have magnitudeBound : (x.tmod y).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_le _ _
  have nonnegative : 0 ≤ x → 0 ≤ x.tmod y ∧ x.tmod y ≤ x := by
    intro h
    have lower := Int.tmod_nonneg y h
    have upper : ((x.tmod y).natAbs : Int) ≤ (x.natAbs : Int) :=
      Int.ofNat_le.mpr magnitudeBound
    rw [Int.natAbs_of_nonneg lower, Int.natAbs_of_nonneg h] at upper
    exact ⟨lower, upper⟩
  have nonpositive : x < 0 → x ≤ x.tmod y ∧ x.tmod y ≤ 0 := by
    intro h
    have bound := Int.tmod_nonneg y (show 0 ≤ -x by omega)
    rw [Int.neg_tmod] at bound
    have remainderNonpositive : x.tmod y ≤ 0 := by omega
    have absoluteBound : ((x.tmod y).natAbs : Int) ≤ (x.natAbs : Int) :=
      Int.ofNat_le.mpr magnitudeBound
    rw [Int.ofNat_natAbs_of_nonpos remainderNonpositive,
      Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)] at absoluteBound
    exact ⟨by omega, remainderNonpositive⟩
  have positiveBounds : 0 < y → -y < x.tmod y ∧ x.tmod y < y := by
    intro h
    exact ⟨Int.lt_tmod_of_pos x h, Int.tmod_lt_of_pos x h⟩
  have negativeBounds : y < 0 → y < x.tmod y ∧ x.tmod y < -y := by
    intro h
    have lo := Int.lt_tmod_of_pos x (show 0 < -y by omega)
    have hi := Int.tmod_lt_of_pos x (show 0 < -y by omega)
    rw [Int.tmod_neg] at lo hi
    exact ⟨by omega, hi⟩
  obtain ⟨floorRule, modulusRule⟩ := fdiv_fmod_tdiv x y hy
  have formula : roundedIntegerQuotient x y
      (if tiesUp then .NearestTiesUp else .NearestTiesAway) =
      (if y = 0 then 0 else
        if 2 * g7DivDivAbsValue (x.tmod y) > g7DivDivAbsValue y then
          x.tdiv y + if g7DivDivSignsAgree x y then 1 else -1
        else if 2 * g7DivDivAbsValue (x.tmod y) < g7DivDivAbsValue y then x.tdiv y
        else if tiesUp then
          if g7DivDivSignsAgree x y then
            x.tdiv y + if g7DivDivSignsAgree x y then 1 else -1
          else x.tdiv y
        else x.tdiv y + if g7DivDivSignsAgree x y then 1 else -1) := by
    cases tiesUp <;> rfl
  rw [formula, if_neg hy, floorRule, modulusRule]
  simp only [g7DivDivAbsValue, g7DivDivSignsAgree, Bool.decide_coe]
  cases tiesUp <;>
    by_cases hx : 0 ≤ x <;>
    rcases Int.lt_or_gt_of_ne hy with hyNeg | hyPos <;>
    simp_all <;> (repeat' (split <;> simp_all)) <;> omega



open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64


theorem g7DivDivFloatWidthPow (f : Fmt) :
    2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem g7DivDivFloatToBitsOfBits {f : Fmt} (v : Nat) :
    (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem g7DivDivFloatBitsSplit {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := g7DivDivFloatWidthPow f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold Fl.signbit Fl.magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ↓reduceIte]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]

theorem g7DivDivFloatExpFromMagnitude {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem g7DivDivFloatFracFromMagnitude {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem g7DivDivFloatNegParts {T : FTy} (x : FV T) :
    (Fl.neg x).magnitude = x.magnitude ∧ (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hbx, hmx⟩ := g7DivDivFloatBitsSplit x
  have h2 := g7DivDivFloatWidthPow T.fmt
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  unfold Fl.neg
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hs] at hbx
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hbx
    have hlt : x.toBits + 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    unfold Fl.magnitude Fl.signbit
    rw [g7DivDivFloatToBitsOfBits, Nat.mod_eq_of_lt hlt]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mod_left]
    · rw [decide_eq_true_iff]
      omega
  · simp only [↓reduceIte, Bool.not_true]
    rw [hs] at hbx
    simp only [↓reduceIte] at hbx
    have hlt : x.toBits - 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    have hsub : x.toBits - 2 ^ (T.fmt.eb + T.fmt.sb) = x.magnitude := by omega
    unfold Fl.magnitude Fl.signbit
    rw [g7DivDivFloatToBitsOfBits, Nat.mod_eq_of_lt hlt, hsub]
    refine ⟨Nat.mod_eq_of_lt hmx, ?_⟩
    rw [decide_eq_false_iff_not]
    omega

theorem g7DivDivFloatNegMetadata {T : FTy} (x : FV T) :
    (Fl.neg x).expField = x.expField ∧ (Fl.neg x).frac = x.frac ∧
    (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hm, hs⟩ := g7DivDivFloatNegParts x
  refine ⟨?_, ?_, hs⟩
  · rw [g7DivDivFloatExpFromMagnitude, hm, ← g7DivDivFloatExpFromMagnitude]
  · rw [g7DivDivFloatFracFromMagnitude, hm, ← g7DivDivFloatFracFromMagnitude]

theorem g7DivDivFloatNegClassifiers {T : FTy} (x : FV T) :
    (Fl.neg x).isfinite = x.isfinite ∧ (Fl.neg x).isnan = x.isnan ∧
    (Fl.neg x).isinf = x.isinf := by
  obtain ⟨he, hf, _⟩ := g7DivDivFloatNegMetadata x
  simp only [Fl.isfinite, Fl.isnan, Fl.isinf, he, hf, and_self]

theorem g7DivDivFloatNegRat {T : FTy} (x : FV T) :
    (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
  obtain ⟨he, hfr, hs⟩ := g7DivDivFloatNegMetadata x
  have hf := (g7DivDivFloatNegClassifiers x).1
  unfold Fl.toRat
  rw [hf, he, hfr, hs]
  dsimp only
  generalize x.frac + (if (x.expField == 0) = true then 0 else 2 ^ T.fmt.sb) = m
  generalize (if (x.expField == 0) = true then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
    else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) = p
  cases x.isfinite
  · simp only [Bool.not_false, ↓reduceIte, Int.neg_zero]
  · cases x.signbit <;>
      simp only [Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;>
      split <;> simp only [Int.neg_mul, Int.neg_neg]


open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.C

/-- Equality of the represented bits determines an IEEE value. -/
theorem g7DivDivFloatBitsExt {T : FTy} (x y : FV T) (bits : x.toBits = y.toBits) : x = y := by
  cases x with
  | mk xb =>
    cases y with
    | mk yb =>
      have equal : xb = yb := Fin.ext bits
      cases equal
      rfl

/-- Finite formats exclude the NaN exponent field. -/
theorem g7DivDivFloatFiniteNotNaN {T : FTy} {x : FV T} (finite : x.isfinite = true) :
    x.isnan = false := by
  simp_all [Fl.isfinite, Fl.isnan]

/-- Finite formats exclude the infinity exponent field. -/
theorem g7DivDivFloatFiniteNotInf {T : FTy} {x : FV T} (finite : x.isfinite = true) :
    x.isinf = false := by
  simp_all [Fl.isfinite, Fl.isinf]

/-- Finite rational observations always have a strictly positive denominator. -/
theorem g7DivDivFloatFiniteDenominator {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    0 < x.toRat.2 := by
  simp only [Fl.toRat, finite, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> split <;> first
    | exact Nat.zero_lt_one
    | exact Nat.two_pow_pos _

/-- The final runtime conversion is the identity on the three supported IEEE formats. -/
theorem g7DivDivFloatFinish {T : FTy} (x : FV T) : finishFloat x = x := by
  unfold finishFloat
  have format : (T.fmt == bfloat) = false := by cases T <;> decide
  rw [format] <;> rfl

/-- Subtracting a finite value from itself gives positive zero in the source runtime. -/
theorem g7DivDivFloatSelfSubtract {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    sub_float x x = Fl.zero false := by
  have metadata := g7DivDivFloatNegMetadata x
  have nan := g7DivDivFloatFiniteNotNaN finite
  have inf := g7DivDivFloatFiniteNotInf finite
  have negativeNan : (Fl.neg x).isnan = false := by
    unfold Fl.isnan
    rw [metadata.1, metadata.2.1]
    exact nan
  have negativeInf : (Fl.neg x).isinf = false := by
    unfold Fl.isinf
    rw [metadata.1, metadata.2.1]
    exact inf
  unfold sub_float jlSubFloat
  rw [g7DivDivFloatFinish]
  simp only [floatSub, floatAdd, nan, inf, negativeNan, negativeInf,
    Bool.false_eq_true, ↓reduceIte, g7DivDivFloatNegRat, metadata.2.2]
  have numerator : x.toRat.1 * (x.toRat.2 : Int) +
      -x.toRat.1 * (x.toRat.2 : Int) = 0 := by
    rw [Int.neg_mul, Int.add_right_neg]
  have denominator : (x.toRat.2 * x.toRat.2 == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    have positive := Nat.mul_pos (g7DivDivFloatFiniteDenominator x finite)
      (g7DivDivFloatFiniteDenominator x finite)
    omega
  have sign : (x.signbit && !x.signbit) = false := by cases x.signbit <;> rfl
  rw [numerator, sign]
  simp only [Fl.roundRat, denominator, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]

/-- The source finiteness callee accepts every finite bit pattern. -/
theorem g7DivDivFloatFiniteCallee {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    isfinite_callee x = true := by
  simp only [isfinite_callee, g7DivDivFloatSelfSubtract x finite]
  cases T <;> rfl

/-- Every infinite bit pattern is the signed infinity constructor. -/
theorem g7DivDivFloatInfinityForm {T : FTy} (x : FV T) (infinite : x.isinf = true) :
    x = Fl.inf x.signbit := by
  apply g7DivDivFloatBitsExt
  have bounded := x.bits.isLt
  change x.toBits < 2 ^ T.fmt.width at bounded
  cases T <;> cases sign : x.signbit <;>
    simp [Fl.isinf, Fl.expField, Fl.frac, Fl.inf, Fl.ofBits, Fl.toBits,
      Fl.signbit, FTy.fmt, half, single, double, Fmt.width, Fmt.emax] at infinite bounded sign ⊢ <;> omega

/-- The source infinity callee recognizes both signed infinities. -/
theorem g7DivDivFloatInfinityCallee (T : FTy) (negative : Bool) :
    isinf_callee (Fl.inf negative : FV T) = true := by
  cases T <;> cases negative <;> decide

/-- Source negation changes only the sign of infinity. -/
theorem g7DivDivFloatNegInfinity (T : FTy) (negative : Bool) :
    neg_float (Fl.inf negative : FV T) = Fl.inf (!negative) := by
  cases T <;> cases negative <;> rfl

/-- The source infinity callee accepts every infinite bit pattern. -/
theorem g7DivDivFloatInfCallee {T : FTy} (x : FV T) (infinite : x.isinf = true) :
    isinf_callee x = true := by
  rw [g7DivDivFloatInfinityForm x infinite]
  exact g7DivDivFloatInfinityCallee T x.signbit

/-- A finite dividend modulo either signed infinite divisor is unchanged. -/
theorem g7DivDivFloatModuloInfinity {T : FTy} (x y : FV T)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    mod_AbstractFloat x y = x := by
  simp only [mod_AbstractFloat, mod_generic, g7DivDivFloatInfCallee y infinite,
    g7DivDivFloatFiniteCallee x finite, Bool.true_and, ↓reduceIte]

/-- Both nearest-tie remainders preserve a finite dividend for an infinite divisor. -/
theorem g7DivDivIEEETiesInfinityValue {T : FTy} (x y : FV T) (mode : TiesMode)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    IEEETiesRemainder x y mode = x := by
  have positive := g7DivDivFloatModuloInfinity x y finite infinite
  have negativeInf : isinf_callee (neg_float y) = true := by
    rw [g7DivDivFloatInfinityForm y infinite, g7DivDivFloatNegInfinity]
    exact g7DivDivFloatInfinityCallee T (!y.signbit)
  have negative : mod_AbstractFloat x (neg_float y) = x := by
    simp only [mod_AbstractFloat, mod_generic, negativeInf,
      g7DivDivFloatFiniteCallee x finite, Bool.true_and, ↓reduceIte]
  exact g7DivDivIEEETiesEqualModuloResults x y x mode positive negative

/-- The complete infinite-divisor conjunct of the frozen IEEE ties-remainder target. -/
theorem g7DivDivIEEETiesInfinityBits {T : FTy} (x y : FV T) (mode : TiesMode)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    (IEEETiesRemainder x y mode).toBits = x.toBits := by
  rw [g7DivDivIEEETiesInfinityValue x y mode finite infinite]


/-- The source infinity callee rejects every finite dividend. -/
theorem g7DivDivFloatFiniteNoInfCallee {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    isinf_callee x = false := by
  have nan := g7DivDivFloatFiniteNotNaN finite
  have magnitudeBound : x.magnitude < 2 ^ T.fmt.width := by
    have bounded := (g7DivDivFloatBitsSplit x).2
    rw [g7DivDivFloatWidthPow]
    omega
  have infinityBits : (inf_float T).toBits = T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> rfl
  unfold isinf_callee egal_float abs_float jlAbsFloat unaryFloat
  rw [g7DivDivFloatFinish]
  simp only [nan, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    g7DivDivFloatToBitsOfBits, Nat.mod_eq_of_lt magnitudeBound, infinityBits]
  apply beq_eq_false_iff_ne.mpr
  intro equal
  have exponent := g7DivDivFloatExpFromMagnitude x
  rw [equal, Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at exponent
  have different : x.expField ≠ T.fmt.emax := by
    simpa only [Fl.isfinite, bne_iff_ne] using finite
  exact different exponent

/-- Source observations on either infinity are independent of its sign. -/
theorem g7DivDivFloatInfinitySourceClassifiers (T : FTy) (negative : Bool) :
    isfinite_callee (Fl.inf negative : FV T) = false ∧
    isnan_callee (Fl.inf negative : FV T) = false ∧
    iszero_float (Fl.inf negative : FV T) = false := by
  cases T <;> cases negative <;> decide

/-- Bit observations on either infinity are independent of its sign. -/
theorem g7DivDivFloatInfinityBitClassifiers (T : FTy) (negative : Bool) :
    (Fl.inf negative : FV T).isfinite = false ∧
    (Fl.inf negative : FV T).isnan = false ∧
    (Fl.inf negative : FV T).iszero = false := by
  cases T <;> cases negative <;> decide

/-- Ordinary IEEE remainder also preserves a finite dividend modulo infinity. -/
theorem g7DivDivFloatRemainderInfinity {T : FTy} (x y : FV T)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    rem_IEEEFloat x y = x := by
  rw [g7DivDivFloatInfinityForm y infinite]
  obtain ⟨infinityFinite, infinityNan, infinityZero⟩ :=
    g7DivDivFloatInfinitySourceClassifiers T y.signbit
  simp only [rem_IEEEFloat, g7DivDivFloatFiniteCallee x finite,
    g7DivDivFloatFiniteNoInfCallee x finite, infinityFinite, infinityNan, infinityZero,
    Bool.and_false, Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

/-- Source negation preserves the infinity classification. -/
theorem g7DivDivFloatNegIsInf {T : FTy} (y : FV T) (infinite : y.isinf = true) :
    (neg_float y).isinf = true := by
  rw [g7DivDivFloatInfinityForm y infinite, g7DivDivFloatNegInfinity]
  cases T <;> cases y.signbit <;> rfl

/-- Every remainder mode except the distinct nearest-even algorithm returns x modulo infinity. -/
theorem g7DivDivIEEERemainderInfinityExceptNearest {T : FTy} (x y : FV T)
    (mode : RoundingMode) (different : mode ≠ .Nearest)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    IEEERemainderValue x y mode = x := by
  have positive := g7DivDivFloatModuloInfinity x y finite infinite
  have negative : mod_AbstractFloat x (neg_IEEEFloat y) = x :=
    g7DivDivFloatModuloInfinity x (neg_float y) finite (g7DivDivFloatNegIsInf y infinite)
  cases mode with
  | ToZero =>
    exact g7DivDivFloatRemainderInfinity x y finite infinite
  | Down => exact positive
  | Up => exact negative
  | Nearest => exact False.elim (different rfl)
  | NearestTiesAway => exact g7DivDivIEEETiesInfinityValue x y .NearestTiesAway finite infinite
  | NearestTiesUp => exact g7DivDivIEEETiesInfinityValue x y .NearestTiesUp finite infinite
  | FromZero =>
    by_cases signs : signbit_float x = signbit_float y
    · simpa only [IEEERemainderValue, IEEERemainderBound, rem_FromZero,
        if_pos signs, reduceCtorEq, ↓reduceIte, rem_Up] using negative
    · simpa only [IEEERemainderValue, IEEERemainderBound, rem_FromZero,
        if_neg signs, reduceCtorEq, ↓reduceIte, rem_Down] using positive

/-- A finite number divided by infinity is the correctly signed IEEE zero. -/
theorem g7DivDivFloatDivideInfinity {T : FTy} (x y : FV T)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    div_IEEEFloat x y = Fl.zero (x.signbit != y.signbit) := by
  have xNan := g7DivDivFloatFiniteNotNaN finite
  have xInf := g7DivDivFloatFiniteNotInf finite
  have yNan : y.isnan = false := by
    rw [g7DivDivFloatInfinityForm y infinite]
    exact (g7DivDivFloatInfinityBitClassifiers T y.signbit).2.1
  have yZero : y.iszero = false := by
    rw [g7DivDivFloatInfinityForm y infinite]
    exact (g7DivDivFloatInfinityBitClassifiers T y.signbit).2.2
  unfold div_IEEEFloat div_float jlDivFloat
  rw [g7DivDivFloatFinish]
  simp only [floatDiv, xNan, xInf, yNan, yZero, infinite,
    Bool.false_and, Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

/-- Every signed IEEE zero is finite. -/
theorem g7DivDivFloatZeroFinite (T : FTy) (negative : Bool) :
    (Fl.zero negative : FV T).isfinite = true := by
  cases T <;> cases negative <;> rfl

/-- Equal floating quotients cancel to positive zero before the final rounding call. -/
theorem g7DivDivIEEEQuotientOfRemainderDividend {T : FTy} (x y : FV T) (mode : RoundingMode)
    (finite : (div_IEEEFloat x y).isfinite = true)
    (remainder : IEEERemainderValue x y mode = x) :
    IEEEQuotientBound x y mode = Fl.zero false := by
  unfold IEEEQuotientBound div_AbstractFloat
  rw [remainder]
  have subtraction : sub_IEEEFloat (div_IEEEFloat x y) (div_IEEEFloat x y) =
      (Fl.zero false : FV T) := g7DivDivFloatSelfSubtract (div_IEEEFloat x y) finite
  rw [subtraction]
  cases T <;> rfl

/-- Six rounding modes satisfy the complete infinite-divisor quotient conclusion. -/
theorem g7DivDivIEEEQuotientInfinityExceptNearest {T : FTy} (x y : FV T)
    (mode : RoundingMode) (different : mode ≠ .Nearest)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    IEEEQuotientBound x y mode = Fl.zero false := by
  have quotientFinite : (div_IEEEFloat x y).isfinite = true := by
    rw [g7DivDivFloatDivideInfinity x y finite infinite]
    exact g7DivDivFloatZeroFinite T (x.signbit != y.signbit)
  exact g7DivDivIEEEQuotientOfRemainderDividend x y mode quotientFinite
    (g7DivDivIEEERemainderInfinityExceptNearest x y mode different finite infinite)


/-- The five shape facts used by the exact rational representation proof. -/
structure g7DivDivFloatFormatGood (format : Fmt) : Prop where
  emax_eq : format.emax = 2 * format.bias + 1
  emax_succ : format.emax + 1 = 2 ^ format.eb
  bias_pos : 1 ≤ format.bias
  sb_pos : 1 ≤ format.sb
  sb_le : format.sb ≤ format.bias

/-- Each supported IEEE format satisfies the rational representation shape facts. -/
theorem g7DivDivFloatGoodFormat (T : FTy) : g7DivDivFloatFormatGood T.fmt := by
  cases T <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A fixed positive denominator common to every finite value of a format. -/
def g7DivDivFloatFormatDen (format : Fmt) : Nat := 2 ^ (format.bias + format.sb - 1)

theorem g7DivDivFloatFormatDenPos (format : Fmt) : 0 < g7DivDivFloatFormatDen format :=
  Nat.two_pow_pos _

theorem g7DivDivFloatPowerProduct (m a b c d : Nat) (equal : a + b = c + d) :
    m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, equal]

/-- Unsigned magnitude in units of the least positive subnormal. -/
def g7DivDivFloatMagnitudeKey (format : Fmt) (magnitude : Nat) : Nat :=
  (magnitude % 2 ^ format.sb +
      if magnitude / 2 ^ format.sb = 0 then 0 else 2 ^ format.sb) *
    2 ^ (magnitude / 2 ^ format.sb - 1)

/-- Signed integer value in units of the least positive subnormal. -/
def g7DivDivFloatKey {format : Fmt} (x : Fl format) : Int :=
  if x.signbit then -(g7DivDivFloatMagnitudeKey format x.magnitude : Int)
  else (g7DivDivFloatMagnitudeKey format x.magnitude : Int)

theorem g7DivDivFloatRationalCases {f : Fmt} (hf : g7DivDivFloatFormatGood f) (x : Fl f) (hx : x.isfinite = true) : ∃ m i j : Nat,
    x.toRat = ((if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int)),
      2 ^ j) ∧
    g7DivDivFloatMagnitudeKey f x.magnitude * 2 ^ j = m * 2 ^ i * (g7DivDivFloatFormatDen f) ∧ m < 2 ^ (f.sb + 1) ∧
    (m ≠ 0 → j + 1 ≤ m.log2 + i + f.bias + f.sb ∧ m.log2 + i ≤ j + f.bias) := by
  have hP := Nat.two_pow_pos f.sb
  have hb := hf.bias_pos
  have hs := hf.sb_pos
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hM := (g7DivDivFloatBitsSplit x).2
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx
    simp only [Fl.isfinite, bne_iff_ne, ne_eq] at this
    rw [g7DivDivFloatExpFromMagnitude] at this
    exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hr := Nat.mod_lt x.magnitude hP
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold Fl.toRat g7DivDivFloatMagnitudeKey g7DivDivFloatFormatDen
  rw [g7DivDivFloatExpFromMagnitude, g7DivDivFloatFracFromMagnitude]
  simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  generalize x.signbit = s
  generalize x.magnitude / 2 ^ f.sb = e at *
  generalize x.magnitude % 2 ^ f.sb = r at *
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨r, 0, f.bias + f.sb - 1, ?_, ?_, by omega, ?_⟩
    · simp only [↓reduceIte, Nat.add_zero]
      split
      · exfalso; omega
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
    · simp
    · intro hr0
      have : r.log2 < f.sb := (Nat.log2_lt hr0).2 hr
      omega
  · have he0 : e ≠ 0 := by omega
    have hne : r + 2 ^ f.sb ≠ 0 := by omega
    have hl1 : (r + 2 ^ f.sb).log2 < f.sb + 1 := (Nat.log2_lt hne).2 (by omega)
    have hl2 : f.sb ≤ (r + 2 ^ f.sb).log2 := (Nat.le_log2 hne).2 (by omega)
    simp only [he0, ↓reduceIte]
    split
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, e - f.bias - f.sb, 0, ?_, ?_, by omega, fun _ => by omega⟩
      · have ht : ((e : Int) - f.bias - f.sb).toNat = e - f.bias - f.sb := by omega
        rw [ht]
        refine Prod.ext ?_ rfl
        cases s <;> simp [Int.natCast_mul, Int.neg_mul]
      · rw [Nat.mul_one]
        conv => lhs; rw [← Nat.mul_one ((r + 2 ^ f.sb) * 2 ^ (e - 1))]
        rw [show (1 : Nat) = 2 ^ 0 from rfl]
        exact g7DivDivFloatPowerProduct _ _ _ _ _ (by omega)
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, 0, f.bias + f.sb - e, ?_, ?_, by omega, fun _ => by omega⟩
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
      · exact g7DivDivFloatPowerProduct _ _ _ _ _ (by omega)

theorem g7DivDivFloatRationalKey {f : Fmt} (hf : g7DivDivFloatFormatGood f) (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧ x.toRat.1 * ((g7DivDivFloatFormatDen f) : Int) = (g7DivDivFloatKey x) * (x.toRat.2 : Int) := by
  obtain ⟨m, i, j, hr, hk, -, -⟩ := g7DivDivFloatRationalCases hf x hx
  rw [hr]
  refine ⟨Nat.two_pow_pos j, ?_⟩
  unfold g7DivDivFloatKey
  dsimp only
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul, ← Int.natCast_mul, hk]

theorem g7DivDivFloatRationalRatioToTrunc {T : FTy} (x y : FV T) (hx : x.isfinite = true) (hy : y.isfinite = true) :
    (x.toRat.1 * (y.toRat.2 : Int)).tdiv (y.toRat.1 * (x.toRat.2 : Int)) = (g7DivDivFloatKey x).tdiv (g7DivDivFloatKey y) := by
  have hrx := g7DivDivFloatRationalKey (g7DivDivFloatGoodFormat T) x hx
  have hry := g7DivDivFloatRationalKey (g7DivDivFloatGoodFormat T) y hy
  let P := (x.toRat.2 : Int) * (y.toRat.2 : Int)
  have hp : 0 < P := Int.mul_pos (Int.natCast_pos.mpr hrx.1) (Int.natCast_pos.mpr hry.1)
  have hd : 0 < ((g7DivDivFloatFormatDen T.fmt) : Int) := Int.natCast_pos.mpr (g7DivDivFloatFormatDenPos _)
  have hsx : (x.toRat.1 * (y.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int) = (g7DivDivFloatKey x) * P := by
    rw [Int.mul_right_comm, hrx.2, Int.mul_assoc]
  have hsy : (y.toRat.1 * (x.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int) = (g7DivDivFloatKey y) * P := by
    rw [Int.mul_right_comm, hry.2, Int.mul_assoc, Int.mul_comm (y.toRat.2 : Int) (x.toRat.2 : Int)]
  calc
    _ = ((x.toRat.1 * (y.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int)).tdiv
        ((y.toRat.1 * (x.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int)) := (Int.mul_tdiv_mul_of_pos_left _ _ hd).symm
    _ = ((g7DivDivFloatKey x) * P).tdiv ((g7DivDivFloatKey y) * P) := by rw [hsx, hsy]
    _ = _ := Int.mul_tdiv_mul_of_pos_left _ _ hp

theorem g7DivDivFloatRationalRemainderIdentity {T : FTy} (x y r : FV T) (q : Int)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hr : r.isfinite = true)
    (hk : (g7DivDivFloatKey r) = (g7DivDivFloatKey x) - (g7DivDivFloatKey y) * q) :
    r.toRat.1 * ((x.toRat.2 : Int) * (y.toRat.2 : Int)) =
      (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int) * q) * (r.toRat.2 : Int) := by
  have hrx := (g7DivDivFloatRationalKey (g7DivDivFloatGoodFormat T) x hx).2
  have hry := (g7DivDivFloatRationalKey (g7DivDivFloatGoodFormat T) y hy).2
  have hrr := (g7DivDivFloatRationalKey (g7DivDivFloatGoodFormat T) r hr).2
  let P := (x.toRat.2 : Int) * (y.toRat.2 : Int)
  let N := x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int) * q
  have hsx : (x.toRat.1 * (y.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int) = (g7DivDivFloatKey x) * P := by
    rw [Int.mul_right_comm, hrx, Int.mul_assoc]
  have hsy : (y.toRat.1 * (x.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int) = (g7DivDivFloatKey y) * P := by
    rw [Int.mul_right_comm, hry, Int.mul_assoc, Int.mul_comm (y.toRat.2 : Int) (x.toRat.2 : Int)]
  have hscale : N * ((g7DivDivFloatFormatDen T.fmt) : Int) = ((g7DivDivFloatKey x) - (g7DivDivFloatKey y) * q) * P := by
    dsimp only [N]
    rw [Int.sub_mul, Int.mul_right_comm (y.toRat.1 * (x.toRat.2 : Int)) q ((g7DivDivFloatFormatDen T.fmt) : Int), hsx, hsy,
      Int.sub_mul, Int.mul_right_comm (g7DivDivFloatKey y) P q]
  apply Int.eq_of_mul_eq_mul_right (show ((g7DivDivFloatFormatDen T.fmt) : Int) ≠ 0 by
    have hp := Int.natCast_pos.mpr (g7DivDivFloatFormatDenPos T.fmt)
    omega)
  change (r.toRat.1 * P) * ((g7DivDivFloatFormatDen T.fmt) : Int) = (N * (r.toRat.2 : Int)) * ((g7DivDivFloatFormatDen T.fmt) : Int)
  calc
    _ = (r.toRat.1 * ((g7DivDivFloatFormatDen T.fmt) : Int)) * P := Int.mul_right_comm _ _ _
    _ = (((g7DivDivFloatKey x) - (g7DivDivFloatKey y) * q) * (r.toRat.2 : Int)) * P := by rw [hrr, hk]
    _ = (((g7DivDivFloatKey x) - (g7DivDivFloatKey y) * q) * P) * (r.toRat.2 : Int) := Int.mul_right_comm _ _ _
    _ = (N * ((g7DivDivFloatFormatDen T.fmt) : Int)) * (r.toRat.2 : Int) := by rw [hscale]
    _ = _ := Int.mul_right_comm _ _ _



/-- Setting the quiet bit preserves the exponent and sets only a fraction bit. -/
theorem g7DivDivFloatQuietMetadata {T : FTy} (x : FV T) :
    (quietFloat x).expField = x.expField ∧
    (quietFloat x).frac = (x.frac ||| 2 ^ (T.fmt.sb - 1)) := by
  have fractionBound : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.sb := by cases T <;> decide
  have widthBound : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.width := by cases T <;> decide
  have rawBits : (quietFloat x).toBits = x.toBits ||| 2 ^ (T.fmt.sb - 1) := by
    unfold quietFloat
    rw [g7DivDivFloatToBitsOfBits]
    exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (show x.toBits < 2 ^ T.fmt.width from x.bits.isLt) widthBound)
  constructor
  · unfold Fl.expField
    rw [rawBits, Nat.or_div_two_pow, Nat.div_eq_of_lt fractionBound, Nat.or_zero]
  · unfold Fl.frac
    rw [rawBits, Nat.or_mod_two_pow, Nat.mod_eq_of_lt fractionBound]

/-- Quieting a NaN keeps its NaN classification. -/
theorem g7DivDivFloatQuietNaN {T : FTy} (x : FV T) (nan : x.isnan = true) :
    (quietFloat x).isnan = true := by
  have fields : x.expField = T.fmt.emax ∧ x.frac ≠ 0 := by
    simpa only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using nan
  have metadata := g7DivDivFloatQuietMetadata x
  have fractionNonzero : (x.frac ||| 2 ^ (T.fmt.sb - 1)) ≠ 0 := by
    intro zero
    exact fields.2 (Nat.or_eq_zero_iff.mp zero).1
  simpa only [Fl.isnan, metadata.1, metadata.2, fields.1, beq_self_eq_true,
    Bool.true_and, bne_iff_ne] using fractionNonzero

/-- A nonfinite bit pattern is either a NaN or an infinity. -/
theorem g7DivDivFloatNonfiniteCases {T : FTy} (x : FV T) (nonfinite : x.isfinite = false) :
    x.isnan = true ∨ x.isinf = true := by
  have exponent : x.expField = T.fmt.emax := by
    simpa only [Fl.isfinite, bne_eq_false_iff_eq] using nonfinite
  by_cases fraction : x.frac = 0
  · right
    simp only [Fl.isinf, exponent, fraction, beq_self_eq_true, Bool.and_self]
  · left
    simp only [Fl.isnan, exponent, beq_self_eq_true, Bool.true_and, bne_iff_ne]
    exact fraction

theorem g7DivDivFloatNaNNotFinite {T : FTy} (x : FV T) (nan : x.isnan = true) :
    x.isfinite = false := by
  cases finite : x.isfinite
  · rfl
  · have impossible := g7DivDivFloatFiniteNotNaN finite
    rw [nan] at impossible
    cases impossible

theorem g7DivDivFloatInfNotFinite {T : FTy} (x : FV T) (infinite : x.isinf = true) :
    x.isfinite = false := by
  rw [g7DivDivFloatInfinityForm x infinite]
  exact (g7DivDivFloatInfinityBitClassifiers T x.signbit).1

theorem g7DivDivFloatNaNNotInf {T : FTy} (x : FV T) (nan : x.isnan = true) :
    x.isinf = false := by
  have fields : x.expField = T.fmt.emax ∧ x.frac ≠ 0 := by
    simpa only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using nan
  simpa only [Fl.isinf, fields.1, beq_self_eq_true, Bool.true_and,
    beq_eq_false_iff_ne] using fields.2

theorem g7DivDivFloatInfNotNaN {T : FTy} (x : FV T) (infinite : x.isinf = true) :
    x.isnan = false := by
  rw [g7DivDivFloatInfinityForm x infinite]
  exact (g7DivDivFloatInfinityBitClassifiers T x.signbit).2.1

theorem g7DivDivFloatInfNotZero {T : FTy} (x : FV T) (infinite : x.isinf = true) :
    x.iszero = false := by
  rw [g7DivDivFloatInfinityForm x infinite]
  exact (g7DivDivFloatInfinityBitClassifiers T x.signbit).2.2

/-- The finite test built from source self-subtraction matches the bit classifier. -/
theorem g7DivDivFloatFiniteCalleeEq {T : FTy} (x : FV T) :
    isfinite_callee x = x.isfinite := by
  cases finite : x.isfinite
  · change (!(isnan_callee (sub_float x x))) = false
    rcases g7DivDivFloatNonfiniteCases x finite with nan | infinite
    · have subtraction : sub_float x x = quietFloat x := by
        unfold sub_float jlSubFloat
        rw [g7DivDivFloatFinish]
        simp only [floatSub, nan, ↓reduceIte]
      rw [subtraction, g7DivDivIEEENaNCallee, g7DivDivFloatQuietNaN x nan, Bool.not_true]
    · have subtraction : sub_float x x = invalidFloat T.fmt := by
        rw [g7DivDivFloatInfinityForm x infinite]
        cases T <;> cases x.signbit <;> rfl
      have invalidNaN : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
      rw [subtraction, g7DivDivIEEENaNCallee, invalidNaN, Bool.not_true]
  · exact g7DivDivFloatFiniteCallee x finite

/-- The source infinity test rejects every NaN, including quieted Float16 inputs. -/
theorem g7DivDivFloatNaNNoInfCallee {T : FTy} (x : FV T) (nan : x.isnan = true) :
    isinf_callee x = false := by
  let q : FV T := if T.fmt == half && x.isnan then quietFloat x else x
  have qNaN : q.isnan = true := by
    dsimp only [q]
    split
    · exact g7DivDivFloatQuietNaN x nan
    · exact nan
  have magnitudeBound : q.magnitude < 2 ^ T.fmt.width := by
    have bounded := (g7DivDivFloatBitsSplit q).2
    rw [g7DivDivFloatWidthPow]
    omega
  have infinityBits : (inf_float T).toBits = T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> rfl
  change ((finishFloat (Fl.ofBits q.magnitude : FV T)).toBits == (inf_float T).toBits) = false
  rw [g7DivDivFloatFinish, g7DivDivFloatToBitsOfBits, Nat.mod_eq_of_lt magnitudeBound, infinityBits]
  apply beq_eq_false_iff_ne.mpr
  intro equal
  have fraction := g7DivDivFloatFracFromMagnitude q
  rw [equal, Nat.mul_mod_left] at fraction
  have nonzero : q.frac ≠ 0 := by
    have fields : q.expField = T.fmt.emax ∧ q.frac ≠ 0 := by
      simpa only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using qNaN
    exact fields.2
  exact nonzero fraction

/-- The source infinity callee matches its IEEE bit classifier. -/
theorem g7DivDivFloatInfCalleeEq {T : FTy} (x : FV T) : isinf_callee x = x.isinf := by
  cases finite : x.isfinite
  · rcases g7DivDivFloatNonfiniteCases x finite with nan | infinite
    · rw [g7DivDivFloatNaNNoInfCallee x nan, g7DivDivFloatNaNNotInf x nan]
    · rw [g7DivDivFloatInfCallee x infinite, infinite]
  · rw [g7DivDivFloatFiniteNoInfCallee x finite, g7DivDivFloatFiniteNotInf finite]

/-- Every zero bit pattern is its signed zero constructor. -/
theorem g7DivDivFloatZeroForm {T : FTy} (x : FV T) (zero : x.iszero = true) :
    x = Fl.zero x.signbit := by
  apply g7DivDivFloatBitsExt
  have magnitude : x.magnitude = 0 := by
    simpa only [Fl.iszero, beq_iff_eq] using zero
  rw [(g7DivDivFloatBitsSplit x).1, magnitude, Nat.add_zero]
  cases T <;> cases x.signbit <;> rfl

theorem g7DivDivFloatZeroCallee {T : FTy} (x : FV T) (zero : x.iszero = true) :
    iszero_float x = true := by
  rw [g7DivDivFloatZeroForm x zero]
  cases T <;> cases x.signbit <;> decide

/-- Every invalid IEEE remainder input produces NaN in ordinary remainder and modulo. -/
theorem g7DivDivFloatExceptionalRemainderAndModulo {T : FTy} (x y : FV T)
    (invalid : x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) :
    (rem_IEEEFloat x y).isnan = true ∧ (mod_AbstractFloat x y).isnan = true := by
  have nanConstant : (nan_float T : FV T).isnan = true := by cases T <;> decide
  have remainderNaN : (rem_IEEEFloat x y).isnan = true := by
    unfold rem_IEEEFloat
    rw [g7DivDivFloatFiniteCalleeEq x, g7DivDivFloatFiniteCalleeEq y,
      g7DivDivFloatInfCalleeEq x, g7DivDivIEEENaNCallee y]
    rcases invalid with xNaN | yNaN | xInf | yZero
    · simp only [g7DivDivFloatNaNNotFinite x xNaN, g7DivDivFloatNaNNotInf x xNaN,
        Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      split <;> simp only [nanConstant, xNaN]
    · simp only [g7DivDivFloatNaNNotFinite y yNaN, yNaN, Bool.and_false,
        Bool.false_and, Bool.or_true, Bool.true_or, Bool.false_eq_true,
        ↓reduceIte, nanConstant]
    · simp only [g7DivDivFloatInfNotFinite x xInf, xInf, Bool.false_and,
        Bool.true_or, Bool.false_eq_true, ↓reduceIte, nanConstant]
    · simp only [g7DivDivFloatZeroCallee y yZero, Bool.not_true, Bool.and_false,
        Bool.or_true, Bool.false_eq_true, ↓reduceIte, nanConstant]
  refine ⟨remainderNaN, ?_⟩
  unfold mod_AbstractFloat mod_generic
  rw [g7DivDivFloatInfCalleeEq y, g7DivDivFloatFiniteCalleeEq x]
  by_cases shortcut : (y.isinf && x.isfinite) = true
  · have operands : y.isinf = true ∧ x.isfinite = true := by simpa only [Bool.and_eq_true] using shortcut
    rcases invalid with xNaN | yNaN | xInf | yZero
    · have impossible := g7DivDivFloatFiniteNotNaN operands.2
      rw [xNaN] at impossible
      cases impossible
    · have impossible := g7DivDivFloatInfNotNaN y operands.1
      rw [yNaN] at impossible
      cases impossible
    · have impossible := g7DivDivFloatFiniteNotInf operands.2
      rw [xInf] at impossible
      cases impossible
    · have impossible := g7DivDivFloatInfNotZero y operands.1
      rw [yZero] at impossible
      cases impossible
  · simp only [shortcut, Bool.false_eq_true, ↓reduceIte]
    have zeroTest : eq_float (rem_IEEEFloat x y) (zero_float T) = false := by
      unfold eq_float jlEqFloat Fl.eq
      simp only [remainderNaN, Bool.not_true, Bool.false_and]
    rw [zeroTest]
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [add_float, jlAddFloat, g7DivDivFloatFinish, floatAdd, remainderNaN,
        ↓reduceIte, g7DivDivFloatQuietNaN (rem_IEEEFloat x y) remainderNaN]
    · exact remainderNaN

/-- The complete invalid-input conjunct of the frozen nearest-ties remainder target. -/
theorem g7DivDivIEEETiesExceptionalNaN {T : FTy} (x y : FV T) (mode : TiesMode)
    (invalid : x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) :
    (IEEETiesRemainder x y mode).isnan = true :=
  g7DivDivIEEETiesPreservesNaNModulo x y mode
    (g7DivDivFloatExceptionalRemainderAndModulo x y invalid).2

/-- Both nonfinite branches of the frozen nearest-ties remainder contract. -/
theorem g7DivDivIEEETiesExceptionalBehavior {T : FTy} (x y : FV T) (mode : TiesMode) :
    ((x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) →
      (IEEETiesRemainder x y mode).isnan = true) ∧
    (x.isfinite = true → y.isinf = true →
      (IEEETiesRemainder x y mode).toBits = x.toBits) := by
  exact ⟨g7DivDivIEEETiesExceptionalNaN x y mode, g7DivDivIEEETiesInfinityBits x y mode⟩


/-- NaN in the dividend propagates through the modeled IEEE division primitive. -/
theorem g7DivDivFloatDivideLeftNaN {T : FTy} (x y : FV T) (nan : x.isnan = true) :
    (div_IEEEFloat x y).isnan = true := by
  unfold div_IEEEFloat div_float jlDivFloat
  rw [g7DivDivFloatFinish]
  simp only [floatDiv, nan, ↓reduceIte, g7DivDivFloatQuietNaN x nan]

/-- A NaN subtrahend propagates even when the minuend is independently NaN. -/
theorem g7DivDivFloatSubtractRightNaN {T : FTy} (x y : FV T) (nan : y.isnan = true) :
    (sub_IEEEFloat x y).isnan = true := by
  unfold sub_IEEEFloat sub_float jlSubFloat
  rw [g7DivDivFloatFinish]
  cases xNaN : x.isnan
  · simp only [floatSub, xNaN, nan, Bool.false_eq_true, ↓reduceIte,
      g7DivDivFloatQuietNaN y nan]
  · simp only [floatSub, xNaN, ↓reduceIte, g7DivDivFloatQuietNaN x xNaN]

/-- Nearest-integer rounding preserves NaN after the Float16 quieting conversion. -/
theorem g7DivDivFloatRoundNearestNaN {T : FTy} (x : FV T) (nan : x.isnan = true) :
    (round_Nearest_llvm x).isnan = true := by
  let q : FV T := if T.fmt == half && x.isnan then quietFloat x else x
  have qNaN : q.isnan = true := by
    dsimp only [q]
    split
    · exact g7DivDivFloatQuietNaN x nan
    · exact nan
  change (finishFloat (roundFloat 3 q)).isnan = true
  rw [g7DivDivFloatFinish]
  simp only [roundFloat, qNaN, ↓reduceIte, g7DivDivFloatQuietNaN q qNaN]

/-- A NaN selected remainder forces the complete source quotient expression to NaN. -/
theorem g7DivDivIEEEQuotientNaNOfRemainder {T : FTy} (x y : FV T) (mode : RoundingMode)
    (nan : (IEEERemainderValue x y mode).isnan = true) :
    (IEEEQuotientBound x y mode).isnan = true := by
  unfold IEEEQuotientBound div_AbstractFloat
  apply g7DivDivFloatRoundNearestNaN
  exact g7DivDivFloatSubtractRightNaN (div_IEEEFloat x y)
    (div_IEEEFloat (IEEERemainderValue x y mode) y)
    (g7DivDivFloatDivideLeftNaN (IEEERemainderValue x y mode) y nan)

/-- Source negation preserves NaN, including Float16's quieting branch. -/
theorem g7DivDivFloatNegNaN {T : FTy} (y : FV T) (nan : y.isnan = true) :
    (neg_float y).isnan = true := by
  let q : FV T := if T.fmt == half && y.isnan then quietFloat y else y
  have qNaN : q.isnan = true := by
    dsimp only [q]
    split
    · exact g7DivDivFloatQuietNaN y nan
    · exact nan
  change (finishFloat (Fl.neg q)).isnan = true
  rw [g7DivDivFloatFinish, (g7DivDivFloatNegClassifiers q).2.1]
  exact qNaN

/-- Source negation preserves both IEEE zero signs as zero. -/
theorem g7DivDivFloatNegIsZero {T : FTy} (y : FV T) (zero : y.iszero = true) :
    (neg_float y).iszero = true := by
  rw [g7DivDivFloatZeroForm y zero]
  cases T <;> cases y.signbit <;> rfl

/-- Flipping the divisor sign preserves every exceptional remainder-input class. -/
theorem g7DivDivFloatExceptionalInputsNegated {T : FTy} (x y : FV T)
    (invalid : x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) :
    x.isnan = true ∨ (neg_float y).isnan = true ∨ x.isinf = true ∨
      (neg_float y).iszero = true := by
  rcases invalid with xNaN | yNaN | xInf | yZero
  · exact Or.inl xNaN
  · exact Or.inr (Or.inl (g7DivDivFloatNegNaN y yNaN))
  · exact Or.inr (Or.inr (Or.inl xInf))
  · exact Or.inr (Or.inr (Or.inr (g7DivDivFloatNegIsZero y yZero)))

/-- The nearest-even source specialization rejects invalid operands before numerical work. -/
theorem g7DivDivIEEENearestExceptionalValue {T : FTy} (operations : JuliaLean.base.math.IEEEOps T)
    (x y : FV T)
    (invalid : x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) :
    JuliaLean.base.math.remNearest operations x y = nan_float T := by
  have guard : (JuliaLean.base.math.fiszero y || !JuliaLean.base.math.fisfinite x ||
      JuliaLean.base.math.fisnan y) = true := by
    change (iszero_float y || !isfinite_callee x || isnan_callee y) = true
    rw [g7DivDivFloatFiniteCalleeEq x, g7DivDivIEEENaNCallee y]
    rcases invalid with xNaN | yNaN | xInf | yZero
    · simp only [g7DivDivFloatNaNNotFinite x xNaN, Bool.not_false, Bool.or_true, Bool.true_or]
    · simp only [yNaN, Bool.or_true]
    · simp only [g7DivDivFloatInfNotFinite x xInf, Bool.not_false, Bool.or_true, Bool.true_or]
    · simp only [g7DivDivFloatZeroCallee y yZero, Bool.true_or]
  simp only [JuliaLean.base.math.remNearest, JuliaLean.base.math.remNearestSource, guard,
    ↓reduceIte] <;> rfl

/-- All seven selected IEEE remainders are NaN on the frozen invalid-input disjunction. -/
theorem g7DivDivIEEERemainderExceptionalNaN {T : FTy} (x y : FV T) (mode : RoundingMode)
    (invalid : x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) :
    (IEEERemainderValue x y mode).isnan = true := by
  have ordinary := (g7DivDivFloatExceptionalRemainderAndModulo x y invalid).1
  have down := (g7DivDivFloatExceptionalRemainderAndModulo x y invalid).2
  have up : (mod_AbstractFloat x (neg_IEEEFloat y)).isnan = true :=
    (g7DivDivFloatExceptionalRemainderAndModulo x (neg_float y)
      (g7DivDivFloatExceptionalInputsNegated x y invalid)).2
  cases mode with
  | ToZero => exact ordinary
  | Down => exact down
  | Up => exact up
  | NearestTiesAway => exact g7DivDivIEEETiesExceptionalNaN x y .NearestTiesAway invalid
  | NearestTiesUp => exact g7DivDivIEEETiesExceptionalNaN x y .NearestTiesUp invalid
  | Nearest =>
    change (JuliaLean.base.math.remNearest (IEEENearestRemainderOps T) x y).isnan = true
    rw [g7DivDivIEEENearestExceptionalValue (IEEENearestRemainderOps T) x y invalid]
    cases T <;> decide
  | FromZero =>
    by_cases signs : signbit_float x = signbit_float y
    · simpa only [IEEERemainderValue, IEEERemainderBound, rem_FromZero,
        if_pos signs, reduceCtorEq, ↓reduceIte, rem_Up] using up
    · simpa only [IEEERemainderValue, IEEERemainderBound, rem_FromZero,
        if_neg signs, reduceCtorEq, ↓reduceIte, rem_Down] using down

/-- The complete invalid-input conjunct of every mode in the frozen quotient contract. -/
theorem g7DivDivIEEEQuotientExceptionalNaN {T : FTy} (x y : FV T) (mode : RoundingMode)
    (invalid : x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) :
    (IEEEQuotientBound x y mode).isnan = true :=
  g7DivDivIEEEQuotientNaNOfRemainder x y mode (g7DivDivIEEERemainderExceptionalNaN x y mode invalid)


open JuliaLean JuliaLean.C
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.base.float JuliaLean.base.int
open JuliaLean.Proofs.base.int JuliaLean.Proofs.base.div

theorem g7DivDivIntXorPattern {t : IntTy} (x y : JInt t) :
    pattern (xor_int x y) = pattern x ^^^ pattern y := by
  simp only [xor_int, jlXorInt, pattern_toJInt, BitVec.toNat_xor, ← pattern_fromJInt]

theorem g7DivDivIntAndPattern {t : IntTy} (x y : JInt t) :
    pattern (and_int x y) = pattern x &&& pattern y := by
  simp only [and_int, jlAndInt, pattern_toJInt, BitVec.toNat_and, ← pattern_fromJInt]

theorem g7DivDivFloatBitcastPattern (t : IntTy) {T : FTy} (x : FV T)
    (width : t.bits = T.fmt.width) : pattern (bitcast_from_float t x) = x.toBits := by
  simp only [bitcast_from_float, JuliaLean.base.int.bitcastFloat, jlBitcast,
    pattern_toJInt, BitVec.toNat_ofNat, width]
  exact Nat.mod_eq_of_lt x.bits.isLt

theorem g7DivDivFloatBitcastMagnitude (T : FTy) {t : IntTy} (x : JInt t) :
    (bitcast_to_float T x).magnitude = pattern x % 2 ^ (T.fmt.eb + T.fmt.sb) := by
  unfold bitcast_to_float Fl.magnitude
  rw [g7DivDivFloatToBitsOfBits]
  change (fromJInt x).toNat % 2 ^ T.fmt.width % 2 ^ (T.fmt.eb + T.fmt.sb) = _
  rw [← pattern_fromJInt]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by cases T <;> decide))

theorem g7DivDivFlipSign32Magnitude (x y : FV .f32) :
    (JuliaLean.base.floatfuncs.flipsign_Float32 x y).magnitude = x.magnitude := by
  unfold JuliaLean.base.floatfuncs.flipsign_Float32
  rw [g7DivDivFloatBitcastMagnitude, g7DivDivIntXorPattern, g7DivDivIntAndPattern,
    g7DivDivFloatBitcastPattern .u32 x rfl, g7DivDivFloatBitcastPattern .u32 y rfl]
  have mask : pattern (JuliaLean.base.int.lit .u32 0x80000000) = 2 ^ 31 := by decide
  change (x.toBits ^^^ (y.toBits &&& pattern (JuliaLean.base.int.lit .u32 0x80000000))) % 2 ^ 31 =
    x.toBits % 2 ^ 31
  rw [mask, Nat.xor_mod_two_pow, Nat.and_mod_two_pow,
    Nat.mod_self, Nat.and_zero, Nat.xor_zero]

theorem g7DivDivFlipSign64Magnitude (x y : FV .f64) :
    (JuliaLean.base.floatfuncs.flipsign_Float64 x y).magnitude = x.magnitude := by
  unfold JuliaLean.base.floatfuncs.flipsign_Float64
  rw [g7DivDivFloatBitcastMagnitude, g7DivDivIntXorPattern, g7DivDivIntAndPattern,
    g7DivDivFloatBitcastPattern .u64 x rfl, g7DivDivFloatBitcastPattern .u64 y rfl]
  have mask : pattern (JuliaLean.base.int.lit .u64 0x8000000000000000) = 2 ^ 63 := by decide
  change (x.toBits ^^^ (y.toBits &&& pattern (JuliaLean.base.int.lit .u64 0x8000000000000000))) % 2 ^ 63 =
    x.toBits % 2 ^ 63
  rw [mask, Nat.xor_mod_two_pow, Nat.and_mod_two_pow,
    Nat.mod_self, Nat.and_zero, Nat.xor_zero]

theorem g7DivDivFloatFiniteOfMagnitude {T : FTy} (x y : FV T)
    (magnitude : x.magnitude = y.magnitude) : x.isfinite = y.isfinite := by
  unfold Fl.isfinite
  rw [g7DivDivFloatExpFromMagnitude, g7DivDivFloatExpFromMagnitude, magnitude]

theorem g7DivDivFloatFlipSign32Finite (x y : FV .f32) :
    (JuliaLean.base.floatfuncs.flipsign_Float32 x y).isfinite = x.isfinite :=
  g7DivDivFloatFiniteOfMagnitude _ _ (g7DivDivFlipSign32Magnitude x y)

theorem g7DivDivFloatFlipSign64Finite (x y : FV .f64) :
    (JuliaLean.base.floatfuncs.flipsign_Float64 x y).isfinite = x.isfinite :=
  g7DivDivFloatFiniteOfMagnitude _ _ (g7DivDivFlipSign64Magnitude x y)


/-- Finite source negation preserves finite classification. -/
theorem g7DivDivFloatNegFinite {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    (neg_float x).isfinite = true := by
  unfold neg_float jlNegFloat unaryFloat
  rw [g7DivDivFloatFinish]
  simp only [g7DivDivFloatFiniteNotNaN finite, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, (g7DivDivFloatNegClassifiers x).1, finite]

/-- Source absolute value removes only the sign of a finite bit pattern. -/
theorem g7DivDivFloatAbsFiniteForm {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    abs_float x = Fl.ofBits x.magnitude := by
  unfold abs_float jlAbsFloat unaryFloat
  rw [g7DivDivFloatFinish]
  simp only [g7DivDivFloatFiniteNotNaN finite, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Source absolute value preserves every finite magnitude. -/
theorem g7DivDivFloatAbsMagnitude {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    (abs_float x).magnitude = x.magnitude := by
  have magnitudeBound := (g7DivDivFloatBitsSplit x).2
  have widthBound : x.magnitude < 2 ^ T.fmt.width := by
    rw [g7DivDivFloatWidthPow]
    omega
  rw [g7DivDivFloatAbsFiniteForm x finite]
  change (Fl.ofBits x.magnitude : FV T).toBits % 2 ^ (T.fmt.eb + T.fmt.sb) = x.magnitude
  rw [g7DivDivFloatToBitsOfBits, Nat.mod_eq_of_lt widthBound,
    Nat.mod_eq_of_lt magnitudeBound]

theorem g7DivDivFloatAbsFinite {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    (abs_float x).isfinite = true :=
  (g7DivDivFloatFiniteOfMagnitude (abs_float x) x (g7DivDivFloatAbsMagnitude x finite)).trans finite

/-- Every source flipsign branch preserves the first operand's finite classification. -/
theorem g7DivDivIEEEFlipSignFinite {T : FTy} (x y : FV T) (finite : x.isfinite = true) :
    (IEEEFlipSign T x y).isfinite = true := by
  cases T with
  | f16 =>
    cases sign : JuliaLean.base.floatfuncs.signbit_Float16 y
    · simpa only [IEEEFlipSign, JuliaLean.base.number.flipsign, sign,
        Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.operators.ifelseValue,
        JuliaLean.base.operators.unaryPlusNumber] using finite
    · simpa only [IEEEFlipSign, JuliaLean.base.number.flipsign, sign,
        Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.operators.ifelseValue,
        JuliaLean.base.operators.unaryPlusNumber, neg_IEEEFloat] using g7DivDivFloatNegFinite x finite
  | f32 => exact (g7DivDivFloatFlipSign32Finite x y).trans finite
  | f64 => exact (g7DivDivFloatFlipSign64Finite x y).trans finite

/-- A finite magnitude lies strictly below the infinity magnitude. -/
theorem g7DivDivFloatFiniteMagnitudeBound {T : FTy} (x : FV T) (finite : x.isfinite = true) :
    x.magnitude < T.fmt.emax * 2 ^ T.fmt.sb := by
  have unequal : x.expField ≠ T.fmt.emax := by
    simpa only [Fl.isfinite, bne_iff_ne] using finite
  have exponentBound : x.expField < 2 ^ T.fmt.eb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have maximum : T.fmt.emax + 1 = 2 ^ T.fmt.eb := by cases T <;> decide
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos T.fmt.sb)).mp
  rw [← g7DivDivFloatExpFromMagnitude]
  omega

/-- Positive infinity is never less than a finite operand in source comparison. -/
theorem g7DivDivFloatPositiveInfinityNotLessFinite {T : FTy} (x : FV T)
    (finite : x.isfinite = true) :
    lt_float (Fl.inf false : FV T) x = false := by
  have infMetadata : (Fl.inf false : FV T).isnan = false ∧
      (Fl.inf false : FV T).iszero = false ∧
      (Fl.inf false : FV T).signbit = false ∧
      (Fl.inf false : FV T).toBits = T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> decide
  unfold lt_float jlLtFloat Fl.lt
  simp only [infMetadata.1, g7DivDivFloatFiniteNotNaN finite, infMetadata.2.1,
    infMetadata.2.2.1, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases sign : x.signbit
  · simp only [sign, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply decide_eq_false_iff_not.mpr
    have bits := (g7DivDivFloatBitsSplit x).1
    simp only [sign, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at bits
    rw [infMetadata.2.2.2, bits]
    have bounded := g7DivDivFloatFiniteMagnitudeBound x finite
    omega
  · rfl

/-- A finite operand is unequal to either signed infinity in source comparison. -/
theorem g7DivDivFloatFiniteNotEqualInfinity {T : FTy} (x y : FV T)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    eq_float x y = false := by
  unfold eq_float jlEqFloat Fl.eq
  simp only [g7DivDivFloatFiniteNotNaN finite, g7DivDivFloatInfNotNaN y infinite,
    g7DivDivFloatInfNotZero y infinite, Bool.not_false, Bool.true_and,
    Bool.and_false, Bool.or_false]
  apply beq_eq_false_iff_ne.mpr
  intro bits
  have equal := g7DivDivFloatBitsExt x y bits
  have impossible := g7DivDivFloatFiniteNotInf finite
  rw [equal, infinite] at impossible
  cases impossible

theorem g7DivDivFloatAbsInfinity {T : FTy} (y : FV T) (infinite : y.isinf = true) :
    abs_float y = (Fl.inf false : FV T) := by
  rw [g7DivDivFloatInfinityForm y infinite]
  cases T <;> cases y.signbit <;> rfl

theorem g7DivDivFloatTwoTimesInfinity {T : FTy} (y : FV T) (infinite : y.isinf = true) :
    mul_float (Fl.ofInt 2) y = y := by
  rw [g7DivDivFloatInfinityForm y infinite]
  cases T <;> cases y.signbit <;> rfl

theorem g7DivDivFloatPositiveInfinityHalf (T : FTy) :
    div_float (Fl.inf false : FV T) (Fl.ofInt 2) = Fl.inf false := by
  cases T <;> rfl

set_option exponentiation.threshold 4096 in
/-- The source's tiny-divisor guard is false at an infinite divisor. -/
theorem g7DivDivFloatInfinityMinimumGuard (T : FTy) :
    lt_float (Fl.inf false : FV T) (mul_float (Fl.ofInt 2) (floatmin_float T)) = false := by
  cases T <;> decide

/-- At infinity, nearest-even remainder reaches only abs and flipsign of the dividend. -/
theorem g7DivDivIEEENearestInfinityValue {T : FTy} (x y : FV T)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    JuliaLean.base.math.remNearest (IEEENearestRemainderOps T) x y =
      IEEEFlipSign T (abs_float x) x := by
  have yZero : iszero_float y = false := by
    rw [g7DivDivFloatInfinityForm y infinite]
    exact (g7DivDivFloatInfinitySourceClassifiers T y.signbit).2.2
  have firstGuard : (JuliaLean.base.math.fiszero y || !JuliaLean.base.math.fisfinite x ||
      JuliaLean.base.math.fisnan y) = false := by
    change (iszero_float y || !isfinite_callee x || isnan_callee y) = false
    rw [yZero, g7DivDivFloatFiniteCallee x finite, g7DivDivIEEENaNCallee y,
      g7DivDivFloatInfNotNaN y infinite] <;> rfl
  have compare := g7DivDivFloatPositiveInfinityNotLessFinite (abs_float x) (g7DivDivFloatAbsFinite x finite)
  simp only [JuliaLean.base.math.remNearest, JuliaLean.base.math.remNearestSource, firstGuard,
    g7DivDivFloatFiniteNotEqualInfinity x y finite infinite, Bool.false_eq_true, ↓reduceIte,
    IEEENearestRemainderOps, g7DivDivFloatTwoTimesInfinity y infinite,
    g7DivDivFloatRemainderInfinity x y finite infinite, g7DivDivFloatAbsInfinity y infinite,
    g7DivDivFloatInfinityMinimumGuard, g7DivDivFloatPositiveInfinityHalf, compare] <;> rfl

/-- The seventh remainder mode also remains finite for a finite dividend and infinite divisor. -/
theorem g7DivDivIEEENearestInfinityFinite {T : FTy} (x y : FV T)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    (IEEERemainderValue x y .Nearest).isfinite = true := by
  change (JuliaLean.base.math.remNearest (IEEENearestRemainderOps T) x y).isfinite = true
  rw [g7DivDivIEEENearestInfinityValue x y finite infinite]
  exact g7DivDivIEEEFlipSignFinite (abs_float x) x (g7DivDivFloatAbsFinite x finite)

set_option exponentiation.threshold 4096 in
/-- The difference of signed zero quotients rounds to an IEEE zero. -/
theorem g7DivDivFloatRoundedDifferenceOfZeros (T : FTy) (left right : Bool) :
    (round_Nearest_llvm (sub_IEEEFloat (Fl.zero left : FV T) (Fl.zero right))).iszero = true := by
  cases T <;> cases left <;> cases right <;> decide

/-- A finite selected remainder suffices for the infinite-divisor quotient conclusion. -/
theorem g7DivDivIEEEQuotientZeroOfFiniteRemainder {T : FTy} (x y : FV T) (mode : RoundingMode)
    (finite : x.isfinite = true) (infinite : y.isinf = true)
    (remainderFinite : (IEEERemainderValue x y mode).isfinite = true) :
    (IEEEQuotientBound x y mode).iszero = true := by
  unfold IEEEQuotientBound div_AbstractFloat
  rw [g7DivDivFloatDivideInfinity x y finite infinite,
    g7DivDivFloatDivideInfinity (IEEERemainderValue x y mode) y remainderFinite infinite]
  exact g7DivDivFloatRoundedDifferenceOfZeros T (x.signbit != y.signbit)
    ((IEEERemainderValue x y mode).signbit != y.signbit)

/-- The complete infinite-divisor quotient conclusion holds in all seven modes. -/
theorem g7DivDivIEEEQuotientInfinityZero {T : FTy} (x y : FV T) (mode : RoundingMode)
    (finite : x.isfinite = true) (infinite : y.isinf = true) :
    (IEEEQuotientBound x y mode).iszero = true := by
  apply g7DivDivIEEEQuotientZeroOfFiniteRemainder x y mode finite infinite
  by_cases nearest : mode = .Nearest
  · rw [nearest]
    exact g7DivDivIEEENearestInfinityFinite x y finite infinite
  · rw [g7DivDivIEEERemainderInfinityExceptNearest x y mode nearest finite infinite]
    exact finite


/-- Both nonfinite clauses of every modewise frozen IEEE quotient behavior. -/
theorem g7DivDivIEEEQuotientExceptionalBehavior {T : FTy} (x y : FV T) (mode : RoundingMode) :
    ((x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ y.iszero = true) →
      ∃ value, (.ok (IEEEQuotientBound x y mode) : Jl (FV T)) = .ok value ∧
        value.isnan = true) ∧
    (x.isfinite = true → y.isinf = true →
      ∃ value, (.ok (IEEEQuotientBound x y mode) : Jl (FV T)) = .ok value ∧
        value.iszero = true) := by
  constructor
  · intro invalid
    exact ⟨IEEEQuotientBound x y mode, rfl, g7DivDivIEEEQuotientExceptionalNaN x y mode invalid⟩
  · intro finite infinite
    exact ⟨IEEEQuotientBound x y mode, rfl, g7DivDivIEEEQuotientInfinityZero x y mode finite infinite⟩


end JuliaLean.ChatGPT.Batch8.Group7

namespace JuliaLean.ChatGPT.Batch8.Group7
open JuliaLean JuliaLean.base.div JuliaLean.Proofs.base.div

set_option maxHeartbeats 1000000

def g7ScaleAbsValue (z : Int) : Int := if z < 0 then -z else z
def g7ScaleSignsAgree (x y : Int) : Bool := (x < 0) = (y < 0)

theorem g7DivScaledLT {c : Int} (hc : 0 < c) (a b : Int) :
    a * c < b * c ↔ a < b := by
  constructor
  · intro h
    exact Int.lt_of_mul_lt_mul_right h (Int.le_of_lt hc)
  · intro h
    exact Int.mul_lt_mul_of_pos_right h hc

theorem g7DivScaledNeg {c : Int} (hc : 0 < c) (a : Int) :
    a * c < 0 ↔ a < 0 := by
  simpa only [Int.zero_mul] using g7DivScaledLT hc a 0

theorem g7DivAbsScale {c : Int} (hc : 0 < c) (a : Int) :
    g7ScaleAbsValue (a * c) = g7ScaleAbsValue a * c := by
  by_cases ha : a < 0 <;>
    simp only [g7ScaleAbsValue, g7DivScaledNeg hc, ha, ↓reduceIte, Int.neg_mul]

theorem g7DivSignsScale {c : Int} (hc : 0 < c) (a b : Int) :
    g7ScaleSignsAgree (a * c) (b * c) = g7ScaleSignsAgree a b := by
  simp only [g7ScaleSignsAgree, g7DivScaledNeg hc]

/-- An explicit formula using local magnitude and sign helpers. -/
theorem g7DivRoundedFormula (x y : Int) (mode : JuliaLean.base.float.RoundingMode) :
    roundedIntegerQuotient x y mode =
    (if y = 0 then 0 else
      let q := x.tdiv y
      let r := x.tmod y
      match mode with
      | .ToZero => q
      | .Down => x.fdiv y
      | .Up => -((-x).fdiv y)
      | .FromZero => if g7ScaleSignsAgree x y then -((-x).fdiv y) else x.fdiv y
      | .Nearest | .NearestTiesAway | .NearestTiesUp =>
        if 2 * g7ScaleAbsValue r > g7ScaleAbsValue y then
          q + if g7ScaleSignsAgree x y then 1 else -1
        else if 2 * g7ScaleAbsValue r < g7ScaleAbsValue y then q
        else if mode = .Nearest then
          if q.tmod 2 = 0 then q else q + if g7ScaleSignsAgree x y then 1 else -1
        else if mode = .NearestTiesAway then q + if g7ScaleSignsAgree x y then 1 else -1
        else if g7ScaleSignsAgree x y then q + if g7ScaleSignsAgree x y then 1 else -1
        else q) := by
  rfl

/-- A common positive scale changes no mathematical quotient rounding mode. -/
theorem g7DivRoundedScale (x y c : Int) (hc : 0 < c) (mode : JuliaLean.base.float.RoundingMode) :
    roundedIntegerQuotient (x * c) (y * c) mode = roundedIntegerQuotient x y mode := by
  have hzero : y * c = 0 ↔ y = 0 := by
    simp only [Int.mul_eq_zero, Int.ne_of_gt hc, or_false]
  have htrunc : (x * c).tdiv (y * c) = x.tdiv y := Int.mul_tdiv_mul_of_pos_left x y hc
  have hfloor : (x * c).fdiv (y * c) = x.fdiv y := Int.mul_fdiv_mul_of_pos_left x y hc
  have hceil : (-(x * c)).fdiv (y * c) = (-x).fdiv y := by
    rw [← Int.neg_mul]
    exact Int.mul_fdiv_mul_of_pos_left (-x) y hc
  have hrem : (x * c).tmod (y * c) = x.tmod y * c := by
    rw [Int.mul_comm x c, Int.mul_comm y c, Int.mul_tmod_mul_of_pos x y hc,
      Int.mul_comm c]
  rw [g7DivRoundedFormula, g7DivRoundedFormula]
  cases mode <;> simp only [hzero, htrunc, hfloor, hceil, hrem,
    g7DivAbsScale hc, ← Int.mul_assoc, g7DivScaledLT hc, g7DivSignsScale hc]

end JuliaLean.ChatGPT.Batch8.Group7
namespace JuliaLean.Proofs.base.div

open JuliaLean.Registry

def entries : List Entry := [
  { id := "float-rem-down-bound", juliaFile := "base/div.jl",
    juliaFns := ["rem(::Float64,::Float64,RoundDown)"],
    statement := "For finite x and positive finite y, RoundDown remainder lies in [0,y).",
    source := "rem docstring; base/div.jl:95-97", status := .refuted,
    prop := ``RoundDownFloatRemainderBound, thm := some ``roundDownFloatRemainderBound_refuted,
    issue := "#8831 (closed, related); no exact duplicate found (issues and PRs: rem RoundDown rounding)" },
  { id := "intarith-division-fldmod-consistency", juliaFile := "base/div.jl",
    juliaFns := ["fldmod", "mod", "divrem(::Integer,::Integer,::typeof(RoundDown))"],
    statement := "The remainder from fldmod equals mod for all mixed fixed-width integer inputs.",
    source := "fldmod docstring and mixed mod methods; base/div.jl:379-387; base/int.jl:342-352",
    status := .refuted, prop := ``BitIntegerMixedFldmodConsistency,
    thm := some ``bitIntegerMixedFldmodConsistency_refuted,
    issue := "#57855, #62319, #63557 (open, related); no exact duplicate found (issues and PRs: fldmod unsigned negative)" },
  { id := "floatintcov-divrem-roundup-typemin", juliaFile := "base/div.jl",
    juliaFns := ["divrem(::Integer,::Integer,RoundUp)", "div(::Integer,::Integer,RoundUp)",
      "rem(::Integer,::Integer,RoundUp)"],
    statement := "For every BitInteger width and rounding mode, divrem agrees with the pair of separate div and rem calls, including typemin and zero-divisor errors.",
    source := "divrem docstring; base/div.jl:255-262", status := .refuted,
    prop := ``BitIntegerDivremProjection, thm := some ``bitIntegerDivremProjection_refuted,
    issue := "#62283 (open, duplicate); #62319 (open, related); searched issues and PRs: rem typemin RoundUp" },
  { id := "div-bitinteger-rounded-quotient", juliaFile := "base/div.jl",
    juliaFns := ["div(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width, div returns x/y rounded by the requested mode; zero divisors and signed typemin / -1 raise DivideError.",
    source := "div docstring; base/div.jl:5-21", status := .proven,
    prop := ``BitIntegerDivisionCorrect, thm := some ``BitIntegerDivisionCorrect_proven },
  { id := "div-bitinteger-remainder-equation", juliaFile := "base/div.jl",
    juliaFns := ["rem(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width, rem is the exact x - y*q remainder for the quotient rounded by the selected mode, with DivideError for zero divisors and nearest-mode signed typemin / -1.",
    source := "rem docstring; base/div.jl:79-108", status := .refuted,
    prop := ``BitIntegerRemainderCorrect, thm := some ``bitIntegerRemainderCorrect_refuted,
    issue := "#62283 (open, duplicate); #62319 (open, related); searched issues and PRs: rem typemin RoundUp" },
  { id := "div-bitinteger-directed-wrapper-correct", juliaFile := "base/div.jl",
    juliaFns := ["fld", "cld", "fld1", "div(::BitInteger,::BitInteger,RoundDown)",
      "div(::BitInteger,::BitInteger,RoundUp)"],
    statement := "For every BitInteger width, fld and cld return the exact floor and ceiling quotients, fld1 returns cld, and signed typemin / -1 raises DivideError.",
    source := "fld and cld docstrings; base/div.jl:151-156,198-203,245-250,458-474", status := .proven,
    prop := ``BitIntegerFloorCeilingCorrect, thm := some ``BitIntegerFloorCeilingCorrect_proven },
  { id := "div-bitinteger-fldmod-contract", juliaFile := "base/div.jl",
    juliaFns := ["fldmod(::BitInteger,::BitInteger)", "fld(::BitInteger,::BitInteger)",
      "mod(::BitInteger,::BitInteger)"],
    statement := "For every BitInteger width, fldmod equals the pair (fld(x,y), mod(x,y)), preserving division errors.",
    source := "fldmod docstring; base/div.jl:379-385", status := .proven,
    prop := ``BitIntegerFldmodCorrect, thm := some ``BitIntegerFldmodCorrect_proven },
  { id := "div-bitinteger-division-error-cases", juliaFile := "base/div.jl",
    juliaFns := ["div", "rem", "divrem", "fld", "cld", "fldmod"],
    statement := "All rounding-mode divisions, divrem, fld, cld, and fldmod raise DivideError on zero divisors and on signed typemin / -1; truncating and directed remainders at typemin / -1 remain zero.",
    source := "checked BitInteger division contract; base/div.jl:127-138,273-325,391-474", status := .proven,
    prop := ``BitIntegerDivisionErrorCases, thm := some ``bitIntegerDivisionErrorCases_proven },
  { id := "float-rem-down-bound-v2", juliaFile := "base/div.jl",
    juliaFns := ["rem(::Float64,::Float64,RoundDown)"],
    statement := "For finite x and positive finite y, RoundDown remainder lies in [0,y).",
    source := "rem docstring; base/div.jl:95-97", status := .refuted,
    prop := ``Round1.RoundDownIEEEFloatRemainderBound, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.FloatRemDownBoundV2_refuted,
    issue := "#8831 (closed, related, PR); keyword searches returned no matches; known related records inspected" },
  { id := "intarith-division-fldmod-consistency-v2", juliaFile := "base/div.jl",
    juliaFns := ["fldmod", "mod", "divrem(::Integer,::Integer,::typeof(RoundDown))"],
    statement := "The remainder from fldmod equals mod for all mixed fixed-width integer inputs.",
    source := "fldmod docstring and mixed mod methods; base/div.jl:379-387; base/int.jl:342-352",
    status := .refuted, prop := ``Round1.MixedFldmodMatchesSeparateCalls, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.IntarithDivisionFldmodConsistencyV2_refuted,
    issue := "#57855 (open, related, issue); #62319 (open, related, PR); #63557 (open, related, PR); keyword searches returned no matches; known related records inspected" },
  { id := "floatintcov-divrem-roundup-typemin-v2", juliaFile := "base/div.jl",
    juliaFns := ["divrem(::Integer,::Integer,RoundUp)", "div(::Integer,::Integer,RoundUp)",
      "rem(::Integer,::Integer,RoundUp)"],
    statement := "For every BitInteger width and rounding mode, divrem agrees with the pair of separate div and rem calls, including typemin and zero-divisor errors.",
    source := "divrem docstring; base/div.jl:255-262", status := .refuted,
    prop := ``Round1.SameTypeDivremMatchesSeparateCalls, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.FloatintcovDivremRoundupTypeminV2_refuted,
    issue := "#62283 (open, duplicate, PR); #62319 (open, related, PR); keyword searches returned no matches; known related records inspected" },
  { id := "div-bitinteger-divrem-reconstruction", juliaFile := "base/div.jl",
    juliaFns := ["divrem(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width and rounding mode, divrem returns the rounded integer quotient and exact x - q*y remainder, or DivideError for zero divisors and signed typemin / -1.",
    source := "divrem docstring; base/div.jl:255-262,290-373", status := .refuted,
    prop := ``Round1.SameTypeDivremReconstruction, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.DivBitintegerDivremReconstruction_refuted,
    issue := "#34325 (open, related, issue); #39318 (open, related, PR); #62319 (open, related, PR); keyword searches returned no matches; known related records inspected" },
  { id := "div-bitinteger-rounded-quotient-v2", juliaFile := "base/div.jl",
    juliaFns := ["div(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width, div returns x/y rounded by the requested mode; zero divisors and signed typemin / -1 raise DivideError.",
    source := "div docstring; base/div.jl:5-21", status := .proven,
    prop := ``Round1.SameTypeBitIntegerRoundedQuotients, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.DivBitintegerRoundedQuotientV2_proven },
  { id := "div-bitinteger-remainder-equation-v2", juliaFile := "base/div.jl",
    juliaFns := ["rem(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width, rem is the exact x - y*q remainder for the quotient rounded by the selected mode, with DivideError for zero divisors and nearest-mode signed typemin / -1.",
    source := "rem docstring; base/div.jl:79-108", status := .refuted,
    prop := ``Round1.SameTypeBitIntegerRemainderEquation, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.DivBitintegerRemainderEquationV2_refuted,
    issue := "#62283 (open, duplicate, PR); #62319 (open, related, PR); keyword searches returned no matches; known related records inspected" },
  { id := "div-bitinteger-directed-wrapper-correct-v2", juliaFile := "base/div.jl",
    juliaFns := ["fld", "cld", "fld1", "div(::BitInteger,::BitInteger,RoundDown)",
      "div(::BitInteger,::BitInteger,RoundUp)"],
    statement := "For every BitInteger width, fld and cld return the exact floor and ceiling quotients, fld1 returns cld, and signed typemin / -1 raises DivideError.",
    source := "fld and cld docstrings; base/div.jl:151-156,198-203,245-250,458-474", status := .refuted,
    prop := ``Round1.AllBitIntegerDirectedWrappers, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.DivBitintegerDirectedWrapperCorrectV2_refuted,
    issue := "#57855 (open, duplicate, issue); #64440 (open, related, issue); #63557 (open, related, PR); #64418 (merged, related, PR); successful keyword retries and match inspection completed" },
  { id := "div-bitinteger-fldmod-contract-v2", juliaFile := "base/div.jl",
    juliaFns := ["fldmod(::BitInteger,::BitInteger)", "fld(::BitInteger,::BitInteger)",
      "mod(::BitInteger,::BitInteger)"],
    statement := "For every BitInteger width, fldmod equals the pair (fld(x,y), mod(x,y)), preserving division errors.",
    source := "fldmod docstring; base/div.jl:379-385", status := .refuted,
    prop := ``Round1.AllBitIntegerFldmodContract, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.DivBitintegerFldmodContractV2_refuted,
    issue := "#57855 (open, related, issue); #19181 (closed, related, issue); #64440 (open, related, issue); #62319 (open, related, PR); #63557 (open, related, PR); successful keyword retries and match inspection completed" },
  { id := "div-bitinteger-division-error-cases-v2", juliaFile := "base/div.jl",
    juliaFns := ["div", "rem", "divrem", "fld", "cld", "fldmod"],
    statement := "All rounding-mode divisions, divrem, fld, cld, and fldmod raise DivideError on zero divisors and on signed typemin / -1; truncating and directed remainders at typemin / -1 remain zero.",
    source := "checked BitInteger division contract; base/div.jl:127-138,273-325,391-474", status := .proven,
    prop := ``Round1.SameTypeBitIntegerDivisionErrorCases, thm := some ``JuliaLean.ChatGPT.Batch8.Group7.DivBitintegerDivisionErrorCasesV2_proven },
  { id := "div-bitinteger-away-quotient", juliaFile := "base/div.jl",
    juliaFns := ["div(::Integer,::Integer,::typeof(RoundFromZero))"],
    statement := "div(x, y, RoundFromZero) returns the exact quotient rounded away from zero for every pair of fixed-width integer types, or DivideError exactly for a zero divisor and for signed typemin / -1 after promotion.",
    source := "div docstring; base/div.jl:5-21,391-417,448-474", status := .refuted,
    prop := ``Round1.AllBitIntegerAwayQuotient, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.DivBitintegerAwayQuotient_refuted,
    issue := "#57855 (open, duplicate, issue); #34519 (closed, related, issue); #63557 (open, related, PR); successful keyword retries and match inspection completed" },
{ id := "div-ieee-ties-remainder", juliaFile := "base/div.jl",
    juliaFns := ["rem(::AbstractFloat, ::AbstractFloat, ::RoundingMode)"],
    statement := "For same-type Float16/32/64 operands, both nearest-ties remainder modes return the exact mathematical remainder for their stated tie rule, return the finite dividend for an infinite divisor, and propagate invalid IEEE inputs as NaN.",
    source := "base/div.jl:139-149; base/float.jl:590-613", status := .todo,
    prop := ``Archive20261102Round1.IEEEFloatTiesRemainderContract, thm := none, notes := "No complete exact proof returned. reached g11TiesContractOfFiniteKeys (with g11RatioToRoundedKeys and g11ExactRemainderOfKeys); remaining goal is finiteness and exact integer-key remainder accounting for finite operands with a nonzero divisor in both ties modes; target theorem omitted." },
  { id := "div-ieee-rounded-quotient", juliaFile := "base/div.jl",
    juliaFns := ["div(::AbstractFloat, ::AbstractFloat, ::RoundingMode)", "fld", "cld"],
    statement := "Same-type Float16/32/64 division in every rounding mode, together with fld and cld and the default truncating division call, returns the exact rounded quotient throughout the documented safe integer region and has the IEEE NaN/zero results on exceptional operands.",
    source := "base/div.jl:77,432-433,480; base/float.jl:458-461,487-490,590-613,987-995;\nbase/math.jl:1122-1145; base/rounding.jl:483", status := .todo,
    prop := ``Archive20261102Round1.IEEEFloatDivisionContract, thm := none, notes := "No complete exact proof returned. reached g11DivisionContractOfFiniteKeys (with g11ExactIntegerOfKey); remaining goal is finiteness and equality of the result key to the exact rounded integer quotient times the format denominator under the documented eps(x/y) <= 1 condition; target theorem omitted." }
]

end JuliaLean.Proofs.base.div
