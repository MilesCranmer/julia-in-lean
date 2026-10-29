import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Float.Extras
import JuliaLean.IntArith.Checked

/-!
BitInteger coverage of `base/intfuncs.jl` at bbfa0ce4150. `nextpow` and
`prevpow` model the integer fast path `a == 2`. The `FromLog` definitions
model all other integer-base control flow parametrically in the actual
rounded logarithm seed. Julia's `base/special/log.jl` supplies that seed;
the numerical logarithm is outside this module. Literal negative exponents,
Bool, and BigInt dispatch are outside this module.
The source loops are expanded into the maximum number of iterations for
BitInteger inputs. Squaring consumes at least one exponent bit per step,
so the exponent width bounds it. Positive digit reduction halves x on each
division; multiplication grows m by at least two, after x was divided once.
For a negative base, ceiled division sends |x| to at most ceil(|x|/2);
the only nonshrinking case is -1, followed by 1 then 0. Thus 130 steps
cover 128 magnitude bits, including the unsigned first division.
The model preserves intermediate types, including mixed-sign division.
The modelled source algorithms are unchanged in 1.13.2; master adds aggressive
constant propagation to the digit dispatchers and an explicit decimal return.
-/
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

/-- `base/int.jl:488,569`: ctlz on the unsigned bit pattern, including zero. -/
def leadingZeros {t : IntTy} (x : JInt t) : Nat :=
  t.bits - (JInt.rem t.toUnsigned x).val.toNat.log2 -
    (if x.val = 0 then 0 else 1)

/-- `base/int.jl:569`: bit width minus ctlz. -/
def topSetBit {t : IntTy} (x : JInt t) : Nat :=
  t.bits - leadingZeros x

/-- `base/int.jl:501`: cttz returns the type width for zero. -/
def trailingZeros {t : IntTy} (x : JInt t) : Nat :=
  ((List.range t.bits).find? fun k =>
    ((JInt.rem t.toUnsigned x).val.toNat / 2^k) % 2 = 1).getD t.bits

/-- `base/int.jl:475`: ctpop of the complete fixed-width representation. -/
def countOnes {t : IntTy} (x : JInt t) : Nat :=
  ((List.range t.bits).filter fun k =>
    ((JInt.rem t.toUnsigned x).val.toNat / 2^k) % 2 = 1).length

/-- `base/intfuncs.jl:624`: positivity is checked before population count. -/
def ispow2 {t : IntTy} (x : JInt t) : Bool := x.val > 0 && countOnes x == 1

/-- `base/int.jl:606,613-614`: nonnegative wrapping left shift. -/
def shl {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  JInt.wrap t (x.val * (2^k : Int))

/-- `base/intfuncs.jl:589-590`: unsigned subtract/shift, signed reinterpretation. -/
def nextpow2 {t : IntTy} (x : JInt t) : JInt t :=
  let u := JInt.rem t.toUnsigned (if x.val < 0 then -x else x)
  let y := shl (JInt.lit t.toUnsigned 1) (topSetBit (u - JInt.lit _ 1))
  JInt.rem t (if x.val < 0 then -y else y)

/-- `base/intfuncs.jl:591-592`: unsigned shift and signed reinterpretation.
At zero the unsigned shift count is huge, so the result is zero. -/
def prevpow2 {t : IntTy} (x : JInt t) : JInt t :=
  let u := JInt.rem t.toUnsigned (if x.val < 0 then -x else x)
  let y := if u.val = 0 then JInt.lit t.toUnsigned 0 else
    shl (JInt.lit t.toUnsigned 1) (topSetBit u - 1)
  JInt.rem t (if x.val < 0 then -y else y)

/-- `base/intfuncs.jl:649-654`: complete integer branch with base exactly 2.
No logarithmic estimate or general-base fallback is modelled. -/
def nextpow {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  if x.val ≤ 0 then .error (.domainError "x must be positive") else .ok (nextpow2 x)

/-- `base/intfuncs.jl:694-697`: complete integer branch with base exactly 2. -/
def prevpow {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  if x.val < 1 then .error (.domainError "x must be at least one") else .ok (prevpow2 x)

/-- `base/intfuncs.jl:437-441`: one outer squaring-loop iteration. -/
def powerStep {t pty : IntTy} (s : JInt t × JInt t × JInt pty) :=
  let (x, y, p) := s
  if p.val > 0 then
    let k := trailingZeros p + 1
    let p' := JInt.wrap pty (p.val / (2^k : Int))
    let x' := k.repeat (fun a => a * a) x
    (x', y * x', p')
  else s

/-- `base/intfuncs.jl:399-443,450-451`: ordinary BitInteger `^`, including
its eager square, exception branches, and trailing-zero squaring schedule.
For BitInteger multiplication `typeof(x*x) == typeof(x)`. -/
def powerBySquaring {t pty : IntTy} (x : JInt t) (p : JInt pty) : Jl (JInt t) :=
  let square := x*x
  if p.val = 1 then .ok x
  else if p.val = 0 then .ok (JInt.lit t 1)
  else if p.val = 2 then .ok square
  else if p.val < 0 then
    if x.val = 1 then .ok x
    else if (-x).val = 1 then .ok (if p.val % 2 = 0 then JInt.lit t 1 else x)
    else .error (.domainError "negative integer exponent")
  else
    let k := trailingZeros p + 1
    let p' := JInt.wrap pty (p.val / (2^k : Int))
    let x' := if k > 1 then (k-2).repeat (fun a => a*a) square else x
    .ok ((pty.bits.repeat powerStep (x', x', p')).2.1)

/-- `base/intfuncs.jl:725-729`: decimal table estimate and correction.
`10^(nd-1)` is exactly the UInt64 table entry at Julia's one-based index nd. -/
def decimal64 {t : IntTy} (x : JInt t) : JInt64 :=
  let lz := JInt.lit .i64 (topSetBit x)
  let nd := JInt.wrap .i64 (((JInt.lit .i64 1233 * lz).val / 4096) + 1)
  nd - JInt.lit .i64 (if x.val < (10 : Int)^(nd.val.toNat-1) then 1 else 0)

/-- `base/intfuncs.jl:730-737`: UInt128 decimal chunk loop. Each iteration
removes 19 digits; two iterations suffice for UInt128 (at most 39 digits). -/
def decimal128Step (s : JInt .u128 × JInt64) :=
  if s.1.val > 10000000000000000000 then
    (JInt.wrap .u128 (s.1.val / 10000000000000000000), s.2 + JInt.lit .i64 19)
  else s

/-- Runtime-typed intermediate needed when ndigits changes signedness. -/
abbrev Box := Σ t : IntTy, JInt t
/-- `base/intfuncs.jl:649-669`: all integer-base branches after the numerical
seed boundary. `n` must be the actual `ceil(Integer, log(a,x))`, computed by
Julia's floating-point logarithm; this estimate is an explicit input,
not a mathematical logarithm or an assumed exact power. The base-two path
never reads the seed. Other branches preserve each wrapping power and check. -/
def nextpowFromLog {aty xty : IntTy} (a : JInt aty) (x : JInt xty)
    (n : JInt64) : Jl Box := do
  if x.val ≤ 0 then .error (.domainError "x must be positive")
  else if a.val = 2 then pure ⟨xty,nextpow2 x⟩
  else if a.val ≤ 1 then .error (.domainError "base must exceed one")
  else if x.val ≤ 1 then pure ⟨aty,JInt.lit aty 1⟩
  else
    let p ← powerBySquaring a (n - JInt.lit .i64 1)
    if x.val > aty.max then .error (.domainError "argument beyond base type range")
    else if p.val ≥ x.val then pure ⟨aty,p⟩
    else
      let wp ← powerBySquaring a n
      if wp.val ≤ p.val then .error (.overflowError "result beyond base type range")
      else if wp.val ≥ x.val then pure ⟨aty,wp⟩
      else
        let wwp ← powerBySquaring a (n + JInt.lit .i64 1)
        if wwp.val ≤ wp.val then .error (.overflowError "result beyond base type range")
        else pure ⟨aty,wwp⟩

/-- `base/intfuncs.jl:694-713`: all integer-base branches after the numerical
seed boundary. `n` is Julia's actual `floor(Integer, log(a,x))`. The next power
uses the shared source model of `mul_with_overflow`, including its Int128
threshold divisions. The numerical logarithm is intentionally not modelled. -/
def prevpowFromLog {aty xty : IntTy} (a : JInt aty) (x : JInt xty)
    (n : JInt64) : Jl Box := do
  if x.val < 1 then .error (.domainError "x must be at least one")
  else if a.val = 2 then pure ⟨xty,prevpow2 x⟩
  else if a.val ≤ 1 then .error (.domainError "base must exceed one")
  else
    let p ← powerBySquaring a n
    if x.val > aty.max then .error (.domainError "argument beyond base type range")
    else
      let (wp, overflow) ← JuliaLean.IntArith.Checked.mulWithOverflow a p
      if wp.val ≤ x.val ∧ overflow = false then pure ⟨aty,wp⟩
      else if p.val ≤ x.val then pure ⟨aty,p⟩
      else pure ⟨aty,← powerBySquaring a (n - JInt.lit .i64 1)⟩
/-- `base/intfuncs.jl:725-740`: decimal dispatch after unsigned(abs(x)). -/
def decimalDigits {t : IntTy} (x : JInt t) : JInt64 :=
  if t.bits = 128 then
    let (u,n) := (2).repeat decimal128Step (JInt.rem .u128 x, JInt.lit .i64 0)
    n + decimal64 (JInt.rem .u64 u)
  else decimal64 x


/-- `base/int.jl:275-288`, `base/div.jl:391-407,438-443`: mixed-sign division
uses magnitude division followed by wrapping sign/rounding corrections.
Same-sign arguments use promotion and the Core checked quotient. -/
def quotient (roundUp roundDown : Bool) (a b : Box) : Jl Box := do
  let ⟨ta,x⟩ := a
  let ⟨tb,y⟩ := b
  if ta.signed = tb.signed then
    let t := IntTy.promote ta tb
    let x := JInt.rem t x
    let y := JInt.rem t y
    let q ← if roundUp then JInt.cld x y else if roundDown then JInt.fld x y else JInt.div x y
    pure ⟨t,q⟩
  else
    let u := IntTy.promote ta.toUnsigned tb.toUnsigned
    let ax := JInt.rem u (if x.val < 0 then -x else x)
    let ay := JInt.rem u (if y.val < 0 then -y else y)
    let q ← JInt.div ax ay
    let r ← JInt.remInt ax ay
    let s := JInt.rem u.toSigned q
    let s := if (x.val < 0) != (y.val < 0) then -s else s
    let t := if ta.signed then u.toSigned else u
    let q := JInt.rem t s
    let q := if roundDown && ((x.val < 0) != (y.val < 0)) && r.val != 0 then
      q - JInt.lit t 1 else q
    let q := if roundUp && ((x.val < 0) == (y.val < 0)) && r.val != 0 then
      q + JInt.lit t 1 else q
    pure ⟨t,q⟩

/-- `base/intfuncs.jl:753-756`: one ceiled-division negative-base iteration. -/
def negativeStep (b : Box) (s : Box × JInt64) : Jl (Box × JInt64) := do
  if s.1.2.val = 0 then pure s else
    pure (← quotient true false s.1 b, s.2 + JInt.lit .i64 1)

/-- `base/intfuncs.jl:746-758`: unsigned first-division peel, wrapping unary
negation of the base before fld, signed conversion, then repeated cld.
A base of magnitude at least two needs at most 130 iterations for 128 bits. -/
def ndigits0znb {t bty : IntTy} (x : JInt t) (b : JInt bty) : Jl JInt64 := do
  let init : Box × JInt64 ← if t.signed then pure (⟨t,x⟩, JInt.lit .i64 0) else do
    let q ← quotient false true ⟨t,x⟩ ⟨bty,-b⟩
    let n := -(JInt.rem q.1.toSigned q.2)
    pure (⟨q.1.toSigned,n⟩, JInt.lit .i64 (if x.val = 0 then 0 else 1))
  let s ← (130).repeat (fun r => r >>= negativeStep ⟨bty,b⟩) (.ok init)
  pure s.2

/-- `base/intfuncs.jl:781-785`: reduce UInt128 until it fits Int64. -/
def reducePositive (b : JInt64) (s : Box × JInt64) : Jl (Box × JInt64) := do
  if s.1.2.val > IntTy.max .i64 then
    pure (← quotient false false s.1 ⟨.i64,b⟩, s.2 + JInt.lit .i64 1)
  else pure s

/-- `base/intfuncs.jl:789-793`: wrapping Int64 multiplication loop. -/
def positiveStep (b : JInt64) (x : Box) (s : JInt64 × JInt64) :=
  if s.1.val ≤ x.2.val then (s.1 * b, s.2 + JInt.lit .i64 1) else s

/-- `base/intfuncs.jl:764-796`: exact base conversion precedes unsigned(abs),
then all binary/octal/hex/decimal/power-of-two branches and generic loops. -/
def ndigits0zpb {t bty : IntTy} (x : JInt t) (base : JInt bty) : Jl JInt64 := do
  if x.val = 0 then pure (JInt.lit .i64 0) else
    let b ← JInt.convert .i64 base.val
    let u := JInt.rem t.toUnsigned (if x.val < 0 then -x else x)
    let bits := topSetBit u
    if b.val = 2 then pure (JInt.lit .i64 bits)
    else if b.val = 8 then pure (JInt.lit .i64 ((bits+2)/3))
    else if b.val = 16 then
      let sz := shl (JInt.lit .i64 (t.bits / 8)) 1
      let lz := JInt.wrap .i64 ((leadingZeros u : Int) / 4)
      pure (sz - lz)
    else if b.val = 10 then pure (decimalDigits u)
    else if ispow2 b then
      let k := trailingZeros b
      pure (JInt.lit .i64 (bits/k + if bits%k = 0 then 0 else 1))
    else
      let s ← (128).repeat (fun r => r >>= reducePositive b) (.ok (⟨t.toUnsigned,u⟩, JInt.lit .i64 0))
      let q ← quotient false false s.1 ⟨.i64,b⟩
      let r := (64).repeat (positiveStep b q) (JInt.lit .i64 1, s.2 + JInt.lit .i64 1)
      pure r.2

/-- `base/intfuncs.jl:829-838`: validate the documented base restriction. -/
def ndigits0z {t bty : IntTy} (x : JInt t) (b : JInt bty) : Jl JInt64 :=
  if b.val < -1 then ndigits0znb x b else if b.val > 1 then ndigits0zpb x b
  else .error (.domainError "base must not be -1, 0, or 1")

/-- `base/intfuncs.jl:739-740`: unary default-decimal dispatch preserves the
unsigned bit pattern of abs(typemin), which itself wraps. -/
def ndigits0zDecimal {t : IntTy} (x : JInt t) : JInt64 :=
  decimalDigits (JInt.rem t.toUnsigned (if x.val < 0 then -x else x))

/-- `base/intfuncs.jl:874`: keyword padding is applied after digit counting.
The pad is Int64 here; other pad types are outside this signature. -/
def ndigits {t bty : IntTy} (x : JInt t) (b : JInt bty) (pad : JInt64) : Jl JInt64 := do
  let d ← ndigits0z x b
  pure (if pad.val ≥ d.val then pad else d)

/-- `base/intfuncs.jl:1293-1303`: exact binary64 conversion, correctly rounded
sqrt and truncation; wide integers then take the source's wrapping Newton
step and wrapping square correction. -/
def isqrt {t : IntTy} (x : JInt t) : Jl (JInt t) := do
  if (t.bits = 64 ∨ t.bits = 128) ∧ x.val = 0 then pure x else
    let f ← JuliaLean.Float.F64.sqrt (JuliaLean.Float.F64.ofJInt x)
    let s ← JuliaLean.Float.F64.truncInt t f
    if t.bits = 64 ∨ t.bits = 128 then
      let q ← JInt.div x s
      let s := JInt.wrap t ((s + q).val / 2)
      pure (if (s*s).val > x.val then s - JInt.lit t 1 else s)
    else pure s

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
