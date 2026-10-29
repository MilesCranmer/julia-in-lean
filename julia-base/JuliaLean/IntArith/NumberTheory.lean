import JuliaLean.Core
import JuliaLean.IntArith.Checked
import JuliaLean.Registry.Types

namespace JuliaLean.IntArith.NumberTheory

/-- `abs`, `base/int.jl:233-234`; the negation wraps at signed typemin. -/
def abs {t : IntTy} (a : JInt t) : JInt t := if a.val < 0 then -a else a

/-- `uabs`, `base/float.jl:235-236`, as used by `base/intfuncs.jl:544`.
Reinterpretation follows the wrapping absolute value, including signed typemin. -/
def uabs {t : IntTy} (a : JInt t) : JInt t.toUnsigned :=
  JInt.rem t.toUnsigned (abs a)

/-- `checked_abs`, used by `base/intfuncs.jl:54-55,142,152`. -/
def checkedAbs {t : IntTy} (a : JInt t) : Jl (JInt t) := Checked.checkedAbs a

/-- Working type for the explicit `widen(Int128) == BigInt` branches in
`base/intfuncs.jl:328-332,587`. `none` denotes Julia BigInt. -/
abbrev WorkTy := Option IntTy

/-- Integer remainder-to-type conversion, `base/int.jl:618-634,695-698`.
Finite work types always use Core's JInt two's-complement conversion. -/
def norm : WorkTy → Int → Int
  | some t, x => (JInt.wrap t x).val
  | none, x => x

/-- Wrapping addition, `base/int.jl:88,93`; BigInt addition is exact. -/
def add (t : WorkTy) (a b : Int) : Int := match t with
  | some t => ((JInt.wrap t a) + (JInt.wrap t b)).val
  | none => a + b

/-- Wrapping subtraction, `base/int.jl:87,92`; BigInt subtraction is exact. -/
def sub (t : WorkTy) (a b : Int) : Int := match t with
  | some t => ((JInt.wrap t a) - (JInt.wrap t b)).val
  | none => a - b

/-- Wrapping multiplication, `base/int.jl:89,94`; BigInt multiplication is exact. -/
def mul (t : WorkTy) (a b : Int) : Int := match t with
  | some t => ((JInt.wrap t a) * (JInt.wrap t b)).val
  | none => a * b

/-- Wrapping unary negation, `base/int.jl:86,91`. -/
def neg (t : WorkTy) (a : Int) : Int := match t with
  | some t => (-(JInt.wrap t a)).val
  | none => -a

/-- `abs` on a work type, `base/int.jl:233-234`. -/
def absVal (t : WorkTy) (a : Int) : Int := if a < 0 then neg t a else a

/-- `widen`, `base/int.jl:911-918`, and `base/gmp.jl:298-299`. -/
def widen : IntTy → WorkTy
  | .i8 => some .i16 | .i16 => some .i32 | .i32 => some .i64
  | .i64 => some .i128 | .u8 => some .u16 | .u16 => some .u32
  | .u32 => some .u64 | .u64 => some .u128 | .i128 | .u128 => none

/-- `divrem`'s exception check, `base/int.jl:355-358,1085-1089`.
The Euclidean state below stores remainders without a second conversion:
`natAbs_tmod` ensures each nonzero remainder is smaller than the divisor,
so the checked intrinsic's final conversion cannot change it. -/
def divOverflow (t : WorkTy) (a b : Int) : Bool := match t with
  | some t => t.signed && a == t.min && b == -1
  | none => false

/-- Extended Euclidean loop, `base/intfuncs.jl:245-259`.
Only coefficients and quotients need wrapping: the truncating remainder
is already representable. Termination follows strictly decreasing
`natAbs b`, including negative divisors and signed typemin. -/
def gcdxLoop (t : WorkTy) (a b s0 s1 t0 t1 : Int) : Jl (Int × Int × Int) :=
  if _h : b = 0 then
    if a < 0 && absVal t a < 0 then
      .error (.domainError "")
    else .ok (if a < 0 then (absVal t a, neg t s0, neg t t0) else (a, s0, t0))
  else if divOverflow t a b then .error .divideError
  else
    let q := norm t (a.tdiv b)
    gcdxLoop t b (a.tmod b) s1 (sub t s0 (mul t q s1))
      t1 (sub t t0 (mul t q t1))
termination_by b.natAbs
decreasing_by
  simpa only [Int.natAbs_tmod] using Nat.mod_lt a.natAbs (by omega : 0 < b.natAbs)

/-- Same-type `gcdx`, `base/intfuncs.jl:235-260`, including the ordered
zero and unit fast paths before the checked Euclidean loop. -/
def gcdxVal (t : WorkTy) (a b : Int) : Jl (Int × Int × Int) :=
  if a = 0 ∧ b = 0 then .ok (0, 0, 0)
  else if absVal t b = 1 then .ok (1, 0, b)
  else if absVal t a = 1 then .ok (1, a, 0)
  else gcdxLoop t a b 1 0 0 1

/-- BitInteger `gcdx`, `base/intfuncs.jl:235-260`. -/
def gcdx {t : IntTy} (a b : JInt t) : Jl (JInt t × JInt t × JInt t) := do
  let (d, x, y) ← gcdxVal (some t) a.val b.val
  pure (JInt.wrap t d, JInt.wrap t x, JInt.wrap t y)

/-- `_gcdx_update`, `base/intfuncs.jl:189-190`. -/
def gcdxUpdate {t : IntTy} (s0 q s1 : JInt t) : JInt t := s0 - q * s1

/-- Semantic primitive boundary for `MPZ.gcdext`,
`base/gmp.jl:255-260,676-677`. GMP's documented centered coefficients,
including `abs(a)=abs(b)` and the half-period tie, are selected from an
exact Euclidean witness. This models the external primitive's result,
not GMP's internal implementation. Specification:
https://gmplib.org/manual/Number-Theoretic-Functions#index-mpz_005fgcdext -/
def gmpGcdext (a b : Int) : Jl (Int × Int × Int) := do
  let (g, s, _) ← gcdxVal none a b
  if a.natAbs = b.natAbs then pure (g, 0, b.sign)
  else if b = 0 then pure (g, a.sign, 0)
  else
    let period := ((b.tdiv g).natAbs : Int)
    let u := s % period
    let u := if 2 * u > period then u - period
      else if 2 * u = period ∧ a < 0 then -u else u
    pure (g, u, (g - a * u).tdiv b)

/-- Julia's BigInt coefficient normalization after the GMP primitive,
`base/gmp.jl:676-687`. -/
def gmpGcdx (a b : Int) : Jl (Int × Int × Int) := do
  let (g, s, t) ← gmpGcdext a b
  if t = 0 then
    if a = b then pure (g, t, s)
    else if a.natAbs = b.natAbs then pure (g, t, -s)
    else pure (g, s, t)
  else pure (g, s, t)

/-- `_bezout_coef`, `base/intfuncs.jl:337-341`. -/
def bezoutCoef (t : WorkTy) (n m : Int) : Jl Int := do
  let (g, x, _) ← match t with
    | none => gmpGcdx n m
    | some _ => gcdxVal t n m
  if g ≠ 1 then .error (.domainError "") else pure x

/-- Truncating remainder magnitude lemma used to justify the loop's
unwrapped remainder state, `base/intfuncs.jl:249-250`. -/
theorem remainder_magnitude (a b : Int) (hb : b ≠ 0) :
    (a.tmod b).natAbs < b.natAbs := by
  rw [Int.natAbs_tmod]
  exact Nat.mod_lt _ (by omega)

/-- Removing factors of two implements the right shift by `trailing_zeros`
in `base/intfuncs.jl:81-89`. Zero remains zero. -/
def stripTwos (n : Nat) : Nat :=
  if h : 0 < n ∧ n % 2 = 0 then stripTwos (n / 2) else n
termination_by n
decreasing_by omega

theorem stripTwos_le (n : Nat) : stripTwos n ≤ n := by
  unfold stripTwos
  split
  · exact Nat.le_trans (stripTwos_le _) (Nat.div_le_self _ _)
  · exact Nat.le_refl _
termination_by n
decreasing_by omega

theorem stripTwos_pos (n : Nat) (hn : 0 < n) : 0 < stripTwos n := by
  unfold stripTwos
  split
  · apply stripTwos_pos
    omega
  · exact hn
termination_by n
decreasing_by omega

/-- Count trailing zero bits, `base/int.jl:501`.
For zero the intrinsic returns the full bit width. -/
def trailingZeros (t : IntTy) (x : Int) : Nat :=
  ((List.range t.bits).find? (fun k => (x / (2 ^ k : Int)) % 2 != 0)).getD t.bits

/-- Arithmetic right shift, `base/int.jl:604-605,611-612`. -/
def shiftRight {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  JInt.wrap t (x.val / (2 ^ k : Int))

/-- Left shift, `base/int.jl:606,613-614`. -/
def shiftLeft {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  JInt.wrap t (x.val * (2 ^ k : Int))

private theorem min_nonpos (t : IntTy) : t.min ≤ 0 := by
  cases t <;> decide

private theorem max_nonneg (t : IntTy) : 0 ≤ t.max := by
  cases t <;> decide

private theorem neg_max_min (t : IntTy) (h : t.signed = true) : t.min ≤ -t.max := by
  cases t <;> first | contradiction | decide

/-- Nonnegative loop-state integers, `base/intfuncs.jl:83-91`.
The stored bound permits direct construction of the same JInt value. -/
def boundedNat (t : IntTy) (n : Nat) (h : (n : Int) ≤ t.max) : JInt t :=
  ⟨n, by have := min_nonpos t; omega⟩

/-- `absdiff`, `base/intfuncs.jl:68-75`; subtraction and abs wrap. -/
def absdiff {t : IntTy} (x y : JInt t) : JInt t × JInt t :=
  if t.signed then
    let d := x - y
    (abs d, d)
  else
    let d := if x ≤ y then y - x else x - y
    (d, d)

private theorem absdiff_bounded (t : IntTy) (a b : Nat)
    (ha : (a : Int) ≤ t.max) (hb : (b : Int) ≤ t.max) :
    (absdiff (boundedNat t a ha) (boundedNat t b hb)).1.val =
      (if a ≤ b then (b - a : Nat) else a - b) := by
  have hlo := min_nonpos t
  by_cases hs : t.signed = true
  · have hneg := neg_max_min t hs
    have hd : t.min ≤ (a : Int) - b ∧ (a : Int) - b ≤ t.max := by omega
    have hn : t.min ≤ -((a : Int) - b) ∧ -((a : Int) - b) ≤ t.max := by omega
    simp only [absdiff, hs, ↓reduceIte, boundedNat]
    change (abs (JInt.wrap t ((a : Int) - b))).val = _
    simp only [abs, JInt.wrap, wrapInt_of_inRange t _ hd]
    split
    · change wrapInt t (-((a : Int) - b)) = _
      rw [wrapInt_of_inRange t _ hn]
      split <;> omega
    · change (a : Int) - b = _
      split <;> omega
  · have hs' : t.signed = false := by cases h : t.signed <;> simp_all
    simp only [absdiff, hs', Bool.false_eq_true, ↓reduceIte, boundedNat]
    change (if (a : Int) ≤ b then JInt.wrap t ((b : Int) - a)
      else JInt.wrap t ((a : Int) - b)).val = _
    split
    · have hr : t.min ≤ (b : Int) - a ∧ (b : Int) - a ≤ t.max := by omega
      change wrapInt t ((b : Int) - a) = _
      rw [wrapInt_of_inRange t _ hr]
      split <;> omega
    · have hr : t.min ≤ (a : Int) - b ∧ (a : Int) - b ≤ t.max := by omega
      change wrapInt t ((a : Int) - b) = _
      rw [wrapInt_of_inRange t _ hr]
      split <;> omega

/-- Stein's loop, `base/intfuncs.jl:86-92`.
`stripTwos` fuses the `za = trailing_zeros(diff)` calculation with the next
iteration's `a >>= za`; all subtraction and absolute-value intermediates
are JInt operations. The measure is the sum of the nonnegative operands:
after a nonzero iteration the new sum is `max(stripTwos a,b) < a+b`. -/
def steinLoop (t : IntTy) (a b : Nat) (ha : (a : Int) ≤ t.max)
    (hb : (b : Int) ≤ t.max) (hbp : 0 < b) : JInt t :=
  if h : a = 0 then boundedNat t b hb
  else
    let s := stripTwos a
    have hs : (s : Int) ≤ t.max := by have := stripTwos_le a; omega
    let d := (absdiff (boundedNat t s hs) (boundedNat t b hb)).1
    have hd := absdiff_bounded t s b hs hb
    have hdnonneg : 0 ≤ d.val := by dsimp [d]; rw [hd]; split <;> omega
    have hdbound : (d.val.toNat : Int) ≤ t.max := by
      have := d.property.2
      omega
    have hmin : ((min s b : Nat) : Int) ≤ t.max := by omega
    have hminpos : 0 < min s b := by have := stripTwos_pos a (by omega); omega
    steinLoop t d.val.toNat (min s b) hdbound hmin hminpos
termination_by a + b
decreasing_by
  have hsle := stripTwos_le a
  have hspos := stripTwos_pos a (by omega)
  dsimp only [s] at hd
  split at hd <;> omega

private theorem stripped_bound (t : IntTy) (b : JInt t) :
    (stripTwos b.val.natAbs : Int) ≤ t.max := by
  have hle := stripTwos_le b.val.natAbs
  have hr := b.property
  by_cases h : t.signed ∧ b.val = t.min
  · rcases h with ⟨hs, hv⟩
    rw [hv]
    cases t <;> first | contradiction | decide +kernel
  · have hab : (b.val.natAbs : Int) ≤ t.max := by
      by_cases hn : 0 ≤ b.val
      · rw [Int.natAbs_of_nonneg hn]
        exact hr.2
      · rw [Int.ofNat_natAbs_of_nonpos (by omega : b.val ≤ 0)]
        cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
    exact Int.le_trans (Int.ofNat_le.mpr hle) hab

/-- `_gcd`, `base/intfuncs.jl:80-95`, on the internal domain guaranteed by
the public gcd's typemin swap. The second operand's shift-then-abs is
represented by stripping its unsigned magnitude, including typemin. -/
def binaryGcd {t : IntTy} (a b : JInt t) (hb : b.val ≠ 0)
    (_ha : t.signed = true → a.val ≠ t.min) : JInt t :=
  let za := trailingZeros t a.val
  let zb := trailingZeros t b.val
  let aa := abs a
  let r := steinLoop t aa.val.toNat (stripTwos b.val.natAbs)
    (by have := aa.property.2; have := max_nonneg t; omega)
    (stripped_bound t b)
    (stripTwos_pos _ (by omega))
  shiftLeft r (min za zb)

/-- BitInteger `gcd`, `base/intfuncs.jl:53-66`; zero checks precede
typemin overflow and the operand swap. -/
def gcd {t : IntTy} (a b : JInt t) : Jl (JInt t) :=
  if ha : a.val = 0 then checkedAbs b
  else if hb : b.val = 0 then checkedAbs a
  else if hmin : t.signed = true ∧ a.val = t.min then
    if heq : a.val = b.val then .error (.overflowError "")
    else .ok (binaryGcd b a ha (by intro _ h; exact heq (hmin.2.trans h.symm)))
  else .ok (binaryGcd a b hb (by intro hs h; exact hmin ⟨hs, h⟩))

/-- `lcm`, `base/intfuncs.jl:136-144`; checked multiplication follows
the ordered gcd and truncating division calls. -/
def lcm {t : IntTy} (a b : JInt t) : Jl (JInt t) := do
  if a.val = 0 ∨ b.val = 0 then pure (JInt.lit t 0)
  else
    let d ← gcd b a
    let q ← JInt.div b d
    let z ← Checked.checkedMul a q
    checkedAbs z

/-- Unary gcd, `base/intfuncs.jl:152`. -/
def gcdUnary {t : IntTy} (a : JInt t) : Jl (JInt t) := checkedAbs a

/-- Unary lcm, `base/intfuncs.jl:154`. -/
def lcmUnary {t : IntTy} (a : JInt t) : Jl (JInt t) := gcdUnary a

/-- Unary gcdx, `base/intfuncs.jl:263`; the coefficient sign is chosen
after the checked gcd call, so signed typemin still throws. -/
def gcdxUnary {t : IntTy} (a : JInt t) : Jl (JInt t × JInt t) := do
  let d ← gcdUnary a
  pure (d, if a.val < 0 then -(JInt.lit t 1) else JInt.lit t 1)

/-- `_promote_mixed_signs`, `base/intfuncs.jl:146-150`.
Promotion is an exact conversion after signed remainder-to-type and abs. -/
def promoteMixedSigns {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (IntTy.promote s t) × JInt (IntTy.promote s t)) := do
  let r := IntTy.promote s t
  let x := abs (JInt.rem r.toSigned a)
  let x ← JInt.convert r x.val
  let y ← JInt.convert r b.val
  pure (x, y)

/-- Mixed gcd dispatch, `base/intfuncs.jl:155-159`. -/
def mixedGcd {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (IntTy.promote s t)) := do
  let r := IntTy.promote s t
  if s.signed && !t.signed then
    let (x, y) ← promoteMixedSigns a b
    gcd x y
  else if !s.signed && t.signed then
    let x := abs (JInt.rem r.toSigned b)
    let x ← JInt.convert r x.val
    let y ← JInt.convert r a.val
    gcd x y
  else
    let x ← JInt.convert r a.val
    let y ← JInt.convert r b.val
    gcd x y

/-- Mixed lcm dispatch, `base/intfuncs.jl:157-160`.
The unsigned-first method takes abs in the original signed type. -/
def mixedLcm {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (IntTy.promote s t)) := do
  let r := IntTy.promote s t
  if s.signed && !t.signed then
    let (x, y) ← promoteMixedSigns a b
    lcm x y
  else if !s.signed && t.signed then
    let x ← JInt.convert r a.val
    let y ← JInt.convert r (abs b).val
    lcm x y
  else
    let x ← JInt.convert r a.val
    let y ← JInt.convert r b.val
    lcm x y

/-- Mixed gcdx dispatch, `base/intfuncs.jl:276-285`.
The wrapped sign adjustment handles a negative signed input whose
promoted signed representation is typemin. -/
def mixedGcdx {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (IntTy.promote s t) × JInt (IntTy.promote s t) ×
      JInt (IntTy.promote s t)) := do
  let r := IntTy.promote s t
  if s.signed && !t.signed then
    let (x, y) ← promoteMixedSigns a b
    let (d, u, v) ← gcdx x y
    let flip := a.val < 0 ∧ r.signed
    let sign := a - JInt.lit s (if flip then 1 else 0)
    pure (d, if sign.val < 0 then -u else u, v)
  else if !s.signed && t.signed then
    let x := abs (JInt.rem r.toSigned b)
    let x ← JInt.convert r x.val
    let y ← JInt.convert r a.val
    let (d, v, u) ← gcdx x y
    let flip := b.val < 0 ∧ r.signed
    let sign := b - JInt.lit t (if flip then 1 else 0)
    pure (d, u, if sign.val < 0 then -v else v)
  else
    let x ← JInt.convert r a.val
    let y ← JInt.convert r b.val
    gcdx x y

/-- Mixed remainder result type, `base/int.jl:278-279,342-351`:
the modulus supplies signedness, while the wider operand supplies width. -/
def modTy (s t : IntTy) : IntTy :=
  if t.signed then (IntTy.promote s t).toSigned else (IntTy.promote s t).toUnsigned

/-- Mixed `mod`, `base/int.jl:342-351`. Each reinterpretation and correction
is retained; using an exact mathematical remainder here would hide the
signed reinterpretation edge cases. -/
def mixedMod {s t : IntTy} (a : JInt s) (b : JInt t) : Jl (JInt (modTy s t)) := do
  let r := IntTy.promote s t
  if b.val = 0 then .error .divideError
  else if s.signed = t.signed then
    let x := JInt.rem r a
    let y := JInt.rem r b
    let z ← JInt.mod x y
    pure (JInt.rem (modTy s t) z)
  else if s.signed then
    let u := r.toUnsigned
    let remval := JInt.wrap u ((uabs a).val.tmod b.val)
    let signedRem := JInt.wrap r.toSigned remval.val
    let remval := if a.val < 0 then -signedRem else signedRem
    let correction := if remval.val < 0 then b.val else 0
    let corrected := add (some r) remval.val correction
    pure (JInt.wrap (modTy s t) corrected)
  else
    let remval := JInt.wrap r.toUnsigned (a.val.tmod (uabs b).val)
    let remval := JInt.wrap r.toSigned remval.val
    let correction := if remval.val ≠ 0 ∧ b.val < 0 then b.val else 0
    pure (JInt.wrap (modTy s t) (add (some r.toSigned) remval.val correction))

/-- Same working-type `mod`, using Core for BitInteger and exact BigInt
remainder for the explicit widening branches, `base/intfuncs.jl:314,330`. -/
def workMod (t : WorkTy) (a b : Int) : Jl Int := match t with
  | some t => (JInt.mod (JInt.wrap t a) (JInt.wrap t b)).map Subtype.val
  | none => if b = 0 then .error .divideError else
      let r := a.tmod b
      .ok (if r = 0 ∨ (r < 0 ↔ b < 0) then r else r + b)

/-- `invmod(n,m)`, `base/intfuncs.jl:308-335`. All finite branches use
the same coefficient types and mixed-modulus dispatch as the source.
`widen(Int128)` is the exact BigInt Euclidean algorithm, never a gcd oracle. -/
def invmod {s t : IntTy} (n : JInt s) (m : JInt t) :
    Jl (JInt (modTy s t)) := do
  if m.val = 0 then .error (.domainError "")
  else
    let r := IntTy.promote s t
    if r.signed then
      let (g, x, _) ← mixedGcdx n m
      if g.val ≠ 1 then .error (.domainError "")
      else
        let z ← mixedMod x m
        pure (JInt.wrap (modTy s t) z.val)
    else
      let st := r.toSigned
      if n.val ≤ st.max ∧ m.val ≤ st.max then
        let x ← bezoutCoef (some st) (norm (some st) n.val) (norm (some st) m.val)
        let x := if x < 0 then add (some (IntTy.promote st t)) x (abs m).val else x
        let z ← mixedMod (JInt.wrap r x) m
        pure (JInt.wrap (modTy s t) z.val)
      else
        let w := widen st
        let x ← bezoutCoef w (norm w n.val) (norm w m.val)
        let z ← workMod w x (norm w m.val)
        let z := if m.val < 0 then sub w z m.val else z
        let z ← mixedMod (JInt.wrap r z) m
        pure (JInt.wrap (modTy s t) z.val)

/-- The fixed Newton/Hurchalla loop, `base/intfuncs.jl:377-380`.
The iteration count is the source's trailing-zero count of twice sizeof. -/
def inverseNewton {t : IntTy} : Nat → JInt t → JInt t → JInt t
  | 0, x, _ => x
  | n + 1, x, y => inverseNewton n (x * (y + JInt.lit t 1)) (y * y)

/-- `invmod(n::BitInteger)`, `base/intfuncs.jl:373-382`.
The literal 3 and xor 2 use Int64 promotion before remainder-to-T. -/
def invmodRing {t : IntTy} (n : JInt t) : Jl (JInt t) :=
  if n.val % 2 = 0 then .error (.domainError "")
  else
    let p := IntTy.promote .i64 t
    let xn := mul (some p) 3 n.val
    let x := JInt.wrap t (Nat.xor (JInt.wrap p.toUnsigned xn).val.toNat 2)
    let y := JInt.lit t 1 - n * x
    .ok (inverseNewton (trailingZeros .i64 (2 * (t.bits / 8))) x y)

/-- `invmod(n,T)`, `base/intfuncs.jl:370`. -/
def invmodType {s : IntTy} (n : JInt s) (t : IntTy) : Jl (JInt t) :=
  invmodRing (JInt.rem t n)

/-- `_powermod_mi_legal`, `base/intfuncs.jl:581-584`. -/
def powermodMILegal (t : IntTy) (m : JInt t) : Bool :=
  !t.signed && decide (m.val ≤ t.max / (2 ^ (t.bits / 2) : Int))

/-- Unsigned multiplicative inverse fields, `base/multinverses.jl:92-96`. -/
structure UnsignedMI (t : IntTy) where
  divisor : JInt t
  multiplier : JInt t
  add : Bool
  shift : Nat

/-- Unsigned magic-number constructor loop, `base/multinverses.jl:109-132`.
The source explicitly stops at `p == 2*bits`; that test proves termination.
Every recurrence is evaluated in its original wrapping unsigned type. -/
def magicLoop (t : IntTy) (d nc : JInt t) (p : Nat)
    (q1 r1 q2 r2 : JInt t) (addFlag : Bool) : UnsignedMI t :=
  let one := JInt.lit t 1
  let signedmin := JInt.wrap t (2 ^ (t.bits - 1))
  let signedmax := signedmin - one
  let (q1, r1) := if r1 ≥ nc - r1 then
    (q1 + q1 + one, r1 + r1 - nc) else (q1 + q1, r1 + r1)
  let (q2, r2, addFlag) := if r2 + one ≥ d - r2 then
    (q2 + q2 + one, r2 + r2 + one - d, addFlag || decide (q2 ≥ signedmax))
    else (q2 + q2, r2 + r2 + one, addFlag || decide (q2 ≥ signedmin))
  let delta := d - one - r2
  if p + 1 < 2 * t.bits ∧ (q1 < delta ∨ (q1 = delta ∧ r1.val = 0)) then
    magicLoop t d nc (p + 1) q1 r1 q2 r2 addFlag
  else
    ⟨d, q2 + one, addFlag,
      (JInt.wrap .u8 (((p + 1 : Nat) : Int) - (t.bits : Int) - (if addFlag then 1 else 0))).val.toNat⟩
termination_by 2 * t.bits - p
decreasing_by omega

/-- Unsigned magic-number constructor, `base/multinverses.jl:98-108`. -/
def unsignedMI {t : IntTy} (d : JInt t) : Jl (UnsignedMI t) := do
  if d.val = 0 then .error (.argumentError "")
  else
    let one := JInt.lit t 1
    let signedmin := JInt.wrap t (2 ^ (t.bits - 1))
    let signedmax := signedmin - one
    let allones := JInt.lit t 0 - one
    let nc := allones - (← JInt.remInt (allones - d) d)
    let q1 ← JInt.div signedmin nc
    let r1 ← JInt.remInt signedmin nc
    let q2 ← JInt.div signedmax d
    let r2 ← JInt.remInt signedmax d
    pure (magicLoop t d nc (t.bits - 1) q1 r1 q2 r2 false)

/-- Unsigned inverse division and remainder,
`base/multinverses.jl:142-149,156`. `mul_hi` is the high half of the
explicitly widened wrapping product, `base/int.jl:123-124`. -/
def magicMod {t : IntTy} (a : JInt t) (mi : UnsignedMI t) : JInt t :=
  let x := JInt.wrap t (mul (widen t) a.val mi.multiplier.val / (2 ^ t.bits : Int))
  let x := if mi.add then shiftRight (a - x) 1 + x else x
  let q := if mi.divisor.val = 1 then a else shiftRight x mi.shift
  a - q * mi.divisor

/-- Original-width optimized loop, `base/intfuncs.jl:552-562`.
`mod(_,mis)` executes the magic-multiply algorithm rather than division. -/
def powermodMagicLoop {t : IntTy} (mi : UnsignedMI t) (p : Nat)
    (rr bb : JInt t) : JInt t :=
  let rr := if p % 2 ≠ 0 then magicMod (rr * bb) mi else rr
  let p' := p / 2
  if p' = 0 then rr
  else powermodMagicLoop mi p' rr (magicMod (bb * bb) mi)
termination_by p
decreasing_by omega

/-- Widened-product positive exponent loop, `base/intfuncs.jl:568-577`.
Reduction takes place before conversion back to the modulus width. -/
def powermodLoop (t : WorkTy) (productTy : WorkTy) (p : Nat) (m rr bb : Int) :
    Jl Int := do
  let rr ← if p % 2 ≠ 0 then
    (workMod productTy (mul productTy rr bb) m).map (norm t) else pure rr
  let p' := p / 2
  if p' = 0 then pure rr
  else
    let bb ← (workMod productTy (mul productTy bb bb) m).map (norm t)
    powermodLoop t productTy p' m rr bb
termination_by p
decreasing_by omega

/-- Semantic primitive boundary for `MPZ.powm`, `base/gmp.jl:250-253`.
The external GMP API computes modular exponentiation, including inversion
for negative exponents. The executable specification uses exact integers;
it does not claim to model GMP's internal exponentiation implementation.
Zero modulus and a missing negative-power inverse raise DivideError.
Specification: https://gmplib.org/manual/Integer-Exponentiation -/
def gmpPowm (x p m : Int) : Jl Int := do
  if m = 0 then .error .divideError
  else
    let mm := (m.natAbs : Int)
    if p = 0 then pure (1 % mm)
    else
      let bb ← if p < 0 then do
          let (g, s, _) ← gmpGcdext x mm
          if g ≠ 1 then .error .divideError else pure (s % mm)
        else pure (x % mm)
      powermodLoop none none p.natAbs mm 1 bb

/-- BigInt powermod sign normalization, `base/gmp.jl:669-674`. -/
def gmpPowermod (x p m : Int) : Jl Int := do
  let r ← gmpPowm x p m
  pure (if m < 0 ∧ r > 0 then r + m else r)

/-- Nonnegative exponent section of `powermod`, `base/intfuncs.jl:542-578`.
The 128-bit overload uses BigInt once, `base/intfuncs.jl:587`. -/
def powermodPositive {s t : IntTy} (x : JInt s) (p : Nat) (m : JInt t) :
    Jl (JInt t) := do
  if m.val = 1 ∨ m.val = -1 then pure (JInt.lit t 0)
  else
    let mm := uabs m
    let bb ← mixedMod x mm
    let bb := JInt.wrap t.toUnsigned bb.val
    let rr ← if powermodMILegal t.toUnsigned mm && decide (p > 2 * (t.bits / 8)) then
        if bb.val = 0 then pure 0
        else
          let mi ← unsignedMI mm
          pure (powermodMagicLoop mi p (JInt.lit _ 1) bb).val
      else if bb.val = 0 then pure 0
      else powermodLoop (some t.toUnsigned) (widen t.toUnsigned) p mm.val 1 bb.val
    let r ← JInt.convert t rr
    pure (if r.val = 0 ∨ m.val > 0 then r else r + m)

/-- `powermod`, `base/intfuncs.jl:524-541,587`, including the 128-bit
BigInt overload before generic p=0 and sign checks. The external GMP
primitive boundary is specified in `gmpPowm`; all Julia conversions,
negative-modulus adjustment, and generic typemin branches are explicit. -/
def powermod {s e t : IntTy} (x : JInt s) (p : JInt e) (m : JInt t) :
    Jl (JInt t) := do
  if t.bits = 128 then
    let r ← gmpPowermod x.val p.val m.val
    JInt.convert t r
  else if p.val = 0 then JInt.mod (JInt.lit t 1) m
  else if p.val < 0 then
    let imod ← invmod x m
    if p.val = (-p).val then
      let halfTy := IntTy.promote e .i64
      let half ← JInt.div (JInt.rem halfTy p) (JInt.lit halfTy 2)
      let rhalf ← powermodPositive imod (-half).val.toNat m
      let w := widen t
      let r ← workMod w (mul w rhalf.val rhalf.val) m.val
      let r ← JInt.convert t r
      if p.val % 2 ≠ 0 then
        let r ← workMod w (mul w r.val imod.val) m.val
        JInt.convert t r
      else pure r
    else powermodPositive imod (-p).val.toNat m
  else powermodPositive x p.val.toNat m

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- A signed typemin gcd with itself is unrepresentable and must throw. -/
def GcdTypeminOverflow : Prop := ∀ t : IntTy, t.signed = true →
  gcd (JInt.typemin t) (JInt.typemin t) = .error (.overflowError "")

theorem gcdTypeminOverflow : GcdTypeminOverflow := by
  intro t
  cases t <;> decide

/-- The documented lcm exists in the promoted type for these inputs,
regardless of argument order. -/
def MixedLcmRepresentable : Prop := ∀ (a : JInt .u16) (b : JInt .i8),
  Int.lcm a.val b.val ≤ IntTy.max .u16 →
  (mixedLcm a b).map Subtype.val = .ok (Int.lcm a.val b.val)

theorem mixedLcmRepresentable_refuted : ¬ MixedLcmRepresentable := by
  intro h
  have hbad := h (JInt.lit .u16 1) (JInt.lit .i8 (-128)) (by decide)
  have hneq : (mixedLcm (JInt.lit .u16 1) (JInt.lit .i8 (-128))).map Subtype.val ≠
      .ok (Int.lcm (JInt.lit .u16 1).val (JInt.lit .i8 (-128)).val) := by decide
  exact hneq hbad

/-- Exact signed Bézout identity and the strict coefficient inequalities
printed in the gcdx docstring. Both inputs are explicitly nonzero. -/
def GcdxStrictBounds : Prop := ∀ (a b d u v : JInt .i8),
  a.val ≠ 0 → b.val ≠ 0 → gcdx a b = .ok (d, u, v) →
  u.val * a.val + v.val * b.val = d.val ∧
  u.val.natAbs < (b.val.tdiv d.val).natAbs ∧
  v.val.natAbs < (a.val.tdiv d.val).natAbs

theorem gcdxStrictBounds_refuted : ¬ GcdxStrictBounds := by
  intro h
  have hb := h (JInt.lit .i8 2) (JInt.lit .i8 2) (JInt.lit .i8 2)
    (JInt.lit .i8 0) (JInt.lit .i8 1) (by decide) (by decide) (by decide +kernel)
  exact (by decide : ¬ ((JInt.lit .i8 1).val.natAbs <
    ((JInt.lit .i8 2).val.tdiv (JInt.lit .i8 2).val).natAbs)) hb.2.2

/-- Byte edge grid includes zero, signed typemin, and unsigned typemax. -/
def byteEdge (n : Fin 16) : Int :=
  if n.val = 0 then 0 else if n.val = 1 then 128 else n.val * 17

/-- General inverse correctness postcondition, `base/intfuncs.jl:309`. -/
def inversePost {t : IntTy} (a m : Int) (result : Jl (JInt t)) : Prop :=
  match result with
  | .error _ => m = 0 ∨ Nat.gcd a.natAbs m.natAbs ≠ 1
  | .ok y => m ≠ 0 ∧ (y.val * a - 1).tmod m = 0 ∧ y.val.tdiv m = 0

private instance {t : IntTy} (a m : Int) (result : Jl (JInt t)) :
    Decidable (inversePost a m result) := by
  cases result <;> unfold inversePost <;> infer_instance

/-- invmod's documented congruence and truncating-division range on a
signed/unsigned byte edge grid. Errors are permitted exactly when the
modulus is zero or the inputs are not relatively prime. -/
def InvmodByteRange : Prop := ∀ (sn sm : Bool) (n m : Fin 16),
  let a := JInt.lit (if sn then .i8 else .u8) (byteEdge n)
  let b := JInt.lit (if sm then .i8 else .u8) (byteEdge m)
  inversePost a.val b.val (invmod a b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem invmodByteRange : InvmodByteRange := by unfold InvmodByteRange; decide +kernel

/-- Exhaustive ring inverse contract for all 256 UInt8 bit patterns:
even inputs throw and odd inputs multiply to one in the machine ring. -/
def RingInverseUInt8 : Prop := ∀ n : Fin 256,
  let a := JInt.lit .u8 n.val
  if a.val % 2 = 0 then invmodRing a = .error (.domainError "")
  else (invmodRing a).map (fun x => (a * x).val) = .ok 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem ringInverseUInt8 : RingInverseUInt8 := by unfold RingInverseUInt8; decide +kernel

/-- Exhaustive signed Int8 bit patterns, including negative odd inputs. -/
def RingInverseInt8 : Prop := ∀ n : Fin 256,
  let a := JInt.lit .i8 n.val
  if a.val % 2 = 0 then invmodRing a = .error (.domainError "")
  else (invmodRing a).map (fun x => (a * x).val) = .ok 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem ringInverseInt8 : RingInverseInt8 := by unfold RingInverseInt8; decide +kernel

/-- All odd Int8 residues have x^(-128) congruent to one modulo -128;
the returned representative has the modulus's negative sign. -/
def PowermodTypeminNegative : Prop := ∀ n : Fin 128,
  let a := JInt.lit .i8 n.val
  a.val % 2 ≠ 0 →
  (powermod a (JInt.lit .i8 (-128)) (JInt.lit .i8 (-128))).map Subtype.val = .ok (-127)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem powermodTypeminNegative : PowermodTypeminNegative := by unfold PowermodTypeminNegative; decide +kernel

/-- Small nonnegative exponents against exact integer exponentiation.
Negative moduli exercise the final sign correction and the optimized
magic-number branch whenever p > 2*sizeof(Int8). -/
def PowermodNegativeModulus : Prop := ∀ (x : Fin 8) (p : Fin 8) (m : Fin 8),
  m.val ≠ 0 →
  (powermod (JInt.lit .i8 x.val) (JInt.lit .i8 p.val)
    (JInt.lit .i8 (-(m.val : Int)))).map Subtype.val =
    .ok (if ((x.val : Int) ^ p.val) % (m.val : Int) = 0 then 0
      else ((x.val : Int) ^ p.val) % (m.val : Int) - m.val)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem powermodNegativeModulus : PowermodNegativeModulus := by unfold PowermodNegativeModulus; decide +kernel

/-- UInt128 inputs close to typemax exercise the BigInt gcdext widening
and conversion back to UInt128 in the general inverse implementation. -/
def InvmodUInt128Range : Prop := ∀ n : Fin 8,
  let a := JInt.lit .u128 (IntTy.max .u128 - 2 * n.val)
  let m := JInt.typemax .u128
  inversePost a.val m.val (invmod a m)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem invmodUInt128Range : InvmodUInt128Range := by unfold InvmodUInt128Range; decide +kernel

/-- The Int128 overload must send the original negative exponent and
modulus to GMP. Odd residues raised to -2^127 are one modulo 2^127. -/
def PowermodInt128Typemin : Prop := ∀ n : Fin 8,
  (powermod (JInt.lit .i128 (2 * n.val + 1)) (JInt.typemin .i128)
    (JInt.typemin .i128)).map Subtype.val = .ok (IntTy.min .i128 + 1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem powermodInt128Typemin : PowermodInt128Typemin := by unfold PowermodInt128Typemin; decide +kernel

def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.NumberTheory
