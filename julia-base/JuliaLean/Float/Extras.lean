import JuliaLean.Float.Basic

/-!
Float64 utilities from Julia master `bbfa0ce4150`. Arithmetic uses the default
nearest-even environment with gradual underflow. Integer inputs represented by
`Int` are mathematical inputs to Julia's generic `Integer` methods; intermediate
machine integers use `JInt`. NaN payloads are retained by bit-only operations.
-/

namespace JuliaLean.Float

/-- `base/rounding.jl:48-102`: the five rounding modes modelled here. -/
inductive Rounding where
  | RoundNearest | RoundNearestTiesAway | RoundUp | RoundDown | RoundToZero
  deriving Repr, DecidableEq, Inhabited

namespace F64

private def extraSign : Nat := 0x8000000000000000
private def extraFrac : Nat := 0x000fffffffffffff
private def extraExp : Nat := 0x7ff0000000000000
private def extraU (n : Nat) : JInt .u64 := JInt.wrap .u64 (Int.ofNat n)
private def extraN (x : JInt .u64) : Nat := x.val.toNat
private def extraShl (x : JInt .u64) (n : Nat) : JInt .u64 :=
  if n ≥ 64 then extraU 0 else extraU (extraN x <<< n)
private def extraShr (x : JInt .u64) (n : Nat) : JInt .u64 := extraU (extraN x >>> n)
private def extraShift (x : JInt .u64) (n : Int) : JInt .u64 :=
  if n < 0 then extraShr x n.natAbs else extraShl x n.toNat
private def extraLz (x : JInt .u64) : Nat :=
  if extraN x == 0 then 64 else 63 - (extraN x).log2
private def extraCountTz : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, u => if u % 2 == 1 then 0 else 1 + extraCountTz n (u >>> 1)
private def extraTz (x : JInt .u64) : Nat := extraCountTz 64 (extraN x)

/-- `base/floatfuncs.jl:5`: sign-copy intrinsic. -/
private def extraCopySign (x y : F64) : F64 :=
  ofBits (Nat.lor (toBits (abs x)) (Nat.land (toBits y) extraSign))

/-- `base/floatfuncs.jl:10`: sign-flip intrinsic. -/
private def extraFlipSign (x y : F64) : F64 := if signbit y then neg x else x

/-- `base/float.jl:810-845`: stepping through sign-magnitude encodings. -/
private def extraNext (x : F64) (dneg : Bool) (da : Nat) : F64 := Id.run do
  if isnan x then return x
  let mut fneg := signbit x
  let mut fu := extraU (toBits (abs x))
  let fumax := extraU extraExp
  if da > 2^64 - 1 then
    fneg := dneg
    fu := fumax
  else
    let du := extraU da
    if fneg != dneg then
      if du.val > fu.val then
        fu := if (du - fu).val < fumax.val then du - fu else fumax
        fneg := !fneg
      else
        fu := fu - du
    else
      if (fumax - fu).val < du.val then fu := fumax else fu := fu + du
  return ofBits (extraN fu + if fneg then extraSign else 0)

/-- `base/float.jl:853,863`: `n` applications of nextfloat, with negative steps reversed. -/
def nextfloat (x : F64) (n : Int := 1) : F64 := extraNext x (decide (n < 0)) n.natAbs

/-- `base/float.jl:871,879`: `n` applications of prevfloat, with negative steps reversed. -/
def prevfloat (x : F64) (n : Int := 1) : F64 := extraNext x (decide (n > 0)) n.natAbs

/-- `base/float.jl:974`: smallest positive normal Float64. -/
def floatmin : F64 := ofBits 0x0010000000000000
/-- `base/float.jl:977`: largest finite Float64. -/
def floatmax : F64 := ofBits 0x7fefffffffffffff

/-- `base/float.jl:981,987-995`: epsilon via the rounded difference after toggling bit zero. -/
def eps (x : F64 := one) : F64 := abs (sub x (ofBits (Nat.xor (toBits x) 1)))

/-- `base/math.jl:854-897`: exponent manipulation, including wrapped Int64 exponent addition. -/
def ldexp (x : F64) (e : Int) : F64 := Id.run do
  let mut xu := toBits x
  let xs := toBits (abs x)
  if xs ≥ extraExp then return x
  let mut k := JInt.wrap .i64 (Int.ofNat (xs >>> 52))
  if k.val == 0 then
    if xs == 0 then return x
    let m := extraLz (extraU xs) - 11
    let ys := extraN (extraShl (extraU xs) m)
    xu := Nat.lor ys (Nat.land xu extraSign)
    k := JInt.wrap .i64 (1 - Int.ofNat m)
    if e < -50000 then return zero (signbit x)
  if e > IntTy.max .i64 then return inf (signbit x)
  if e < IntTy.min .i64 then return zero (signbit x)
  k := k + JInt.wrap .i64 e
  if k.val ≥ 2047 then return inf (signbit x)
  if k.val > 0 then
    return ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) (k.val.toNat <<< 52))
  else
    if k.val ≤ -53 then
      if e > 50000 then return inf (signbit x)
      return zero (signbit x)
    k := k + JInt.wrap .i64 53
    let z := ofBits (970 <<< 52)
    let y := ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) (k.val.toNat <<< 52))
    return mul z y

/-- `base/math.jl:936-950`: exponent errors precede subnormal normalization. -/
def exponent (x : F64) : Jl Int :=
  let xs := toBits (abs x)
  if xs ≥ extraExp then .error (.domainError "Cannot be NaN or Inf.")
  else
    let k := Int.ofNat (xs >>> 52)
    if k == 0 then
      if xs == 0 then .error (.domainError "Cannot be ±0.0.")
      else .ok (1 - Int.ofNat (extraLz (extraU xs) - 11) - 1023)
    else .ok (k - 1023)

/-- `base/math.jl:1026-1038`: normalize subnormals before replacing exponent bits. -/
def significand (x : F64) : F64 := Id.run do
  let mut xu := toBits x
  let xs := toBits (abs x)
  if xs ≥ extraExp then return x
  if xs ≤ extraFrac then
    if xs == 0 then return x
    let m := extraLz (extraU xs) - 11
    xu := Nat.lor (extraN (extraShl (extraU xs) m)) (Nat.land xu extraSign)
  return ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) 0x3ff0000000000000)

/-- `base/math.jl:1060-1077`: preserve nonfinite values and signed zeros with exponent zero. -/
def frexp (x : F64) : F64 × Int := Id.run do
  let mut xu := toBits x
  let xs := toBits (abs x)
  if xs ≥ extraExp then return (x, 0)
  let mut k := Int.ofNat (xs >>> 52)
  if k == 0 then
    if xs == 0 then return (x, 0)
    let m := extraLz (extraU xs) - 11
    xu := Nat.lor (extraN (extraShl (extraU xs) m)) (Nat.land xu extraSign)
    k := 1 - Int.ofNat m
  return (ofBits (Nat.lor (Nat.land xu (extraSign + extraFrac)) 0x3fe0000000000000), k - 1022)

/-- `base/float.jl:502-506`: explicit mantissa of a finite nonzero value. -/
private def extraMantissa (x : F64) : JInt .u64 :=
  let u := toBits x
  extraU (Nat.land u extraFrac + if u >>> 52 == 0 then 0 else 2^52)

/-- `base/float.jl:508-522`: UInt64 mantissa/exponent reconstruction. -/
private def extraToFloat (number ep : JInt .u64) : F64 :=
  let epint := JInt.wrap .i64 ep.val
  let lz := JInt.wrap .i64 (Int.ofNat (extraLz number) - 11)
  let number := extraShift number lz.val
  let epint := epint - lz
  if epint.val ≥ 0 then
    ofBits (Nat.lor (Nat.land (extraN number) extraFrac)
      (Nat.land (extraN (extraShl (JInt.wrap .u64 (epint + JInt.wrap .i64 1).val) 52)) extraExp))
  else ofBits (Nat.land (extraN (extraShift number epint.val)) extraFrac)

/-- `base/float.jl:580-586`: the exact shift/remainder loop; the shift size is positive. -/
private def extraRemLoop (n sideMinusOne : Nat) (mx my : JInt .u64) : JInt .u64 :=
  let side := sideMinusOne + 1
  if _h : side < n then
    let mx := extraU (extraN (extraShl mx side) % extraN my)
    extraRemLoop (n - side) sideMinusOne mx my
  else extraU (extraN (extraShl mx n) % extraN my)
termination_by n
decreasing_by omega

/-- `base/float.jl:524-588`: all three mantissa-reduction branches of rem_internal. -/
private def extraRemInternal (x y : F64) : F64 := Id.run do
  let xuint := extraU (toBits x)
  let yuint := extraU (toBits y)
  if xuint.val ≤ yuint.val then
    if xuint.val < yuint.val then return x
    return zero
  let ex := extraU (toBits x >>> 52)
  let ey := extraU (toBits y >>> 52)
  if ey.val > 52 && (ex - ey).val ≤ 11 then
    let mx := extraMantissa x
    let my := extraMantissa y
    let d := extraU (extraN (extraShl mx (extraN (ex - ey))) % extraN my)
    if d.val == 0 then return zero
    return extraToFloat d (ey - extraU 1)
  if ex.val == 0 && ey.val == 0 then
    return ofBits (Nat.land (extraN xuint % extraN yuint) extraFrac)
  let mut mx := extraMantissa x
  let ex := ex - extraU 1
  let mut my := extraMantissa y
  let mut ey := ey
  let mut lzmy := 11
  if ey.val > 0 then ey := ey - extraU 1
  else
    my := extraU (Nat.land (toBits y) extraFrac)
    lzmy := extraLz my
  let tzmy := extraTz my
  let side := lzmy + tzmy
  let mut diff := ex - ey
  let right := min (extraN diff) tzmy
  my := extraShr my right
  diff := diff - extraU right
  ey := ey + extraU right
  let left := min (extraN diff) 11
  mx := extraShl mx left
  diff := diff - extraU left
  mx := extraU (extraN mx % extraN my)
  if mx.val == 0 then return zero
  if diff.val == 0 then return extraToFloat mx ey
  return extraToFloat (extraRemLoop (extraN diff) (side - 1) mx my) ey

/-- `base/float.jl:590-598`: exceptional cases and dividend-signed exact remainder. -/
def rem (x y : F64) : F64 :=
  if isfinite x && !iszero x && isfinite y && !iszero y then
    extraCopySign (extraRemInternal (abs x) (abs y)) x
  else if isinf x || isnan y || iszero y then nan
  else x

/-- `base/float.jl:600-612`: retain the rounded addition when remainder and divisor differ in sign. -/
def mod (x y : F64) : F64 :=
  if isinf y && isfinite x then x
  else
    let r := rem x y
    if eq r zero then extraCopySign r y
    else if lt zero r != lt zero y then add r y
    else r

/-
This remainder method follows Julia's adaptation of the msun remainder functions.
Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
Developed at SunSoft, a Sun Microsystems, Inc. business.
Permission to use, copy, modify, and distribute this software is freely granted,
provided that this notice is preserved.
-/
/-- `base/math.jl:1122-1145`: IEEE nearest-even remainder, including tiny-divisor branches. -/
private def extraRemNearest (x p : F64) : F64 := Id.run do
  if iszero p || !isfinite x || isnan p then return nan
  if eq x p then return zero (signbit x)
  let oldx := x
  let two := ofInt 2
  let mut x := abs (rem x (mul two p))
  let p := abs p
  if lt p (mul two floatmin) then
    if lt p (mul two x) then
      x := sub x p
      if le p (mul two x) then x := sub x p
  else
    let phalf := div p two
    if lt phalf x then
      x := sub x p
      if le phalf x then x := sub x p
  return extraFlipSign x oldx

/-- `base/div.jl:127-149`, `base/math.jl:1122-1145`: mode-specific remainder dispatch. -/
def remMode (x y : F64) (mode : Rounding) : F64 := Id.run do
  match mode with
  | .RoundToZero => return rem x y
  | .RoundDown => return mod x y
  | .RoundUp => return mod x (neg y)
  | .RoundNearest => return extraRemNearest x y
  | .RoundNearestTiesAway =>
    let r := mod x y
    if isnan r then return r
    if !iszero r then
      let two := ofInt 2
      let (m, n) := if lt (abs r) (div floatmax two) then (abs (mul two r), abs y)
                    else (abs r, abs (div y two))
      if lt m n then return r
      if lt n m then return mod x (neg y)
    return if signbit x == signbit y then mod x (neg y) else r

/-- LLVM integral rounding behind `base/float.jl:458-461`, with exact rational arithmetic. -/
private def extraRoundIntrinsic (x : F64) (mode : Rounding) : F64 :=
  if isnan x then ofBits (Nat.lor (toBits x) 0x0008000000000000)
  else if isinf x then x
  else
    let (num, den) := toRat x
    let q := num.natAbs / den
    let r := num.natAbs % den
    let increment := match mode with
      | .RoundToZero => false
      | .RoundDown => signbit x && r != 0
      | .RoundUp => !signbit x && r != 0
      | .RoundNearest => 2*r > den || (2*r == den && q % 2 == 1)
      | .RoundNearestTiesAway => decide (2*r ≥ den)
    let magnitude := q + if increment then 1 else 0
    if magnitude == 0 then zero (signbit x)
    else ofInt (if signbit x then -Int.ofNat magnitude else Int.ofNat magnitude)

/-- `base/float.jl:458-461`, `base/floatfuncs.jl:151-154`: ties-away retains rounded intermediates. -/
def round (x : F64) (mode : Rounding := .RoundNearest) : F64 :=
  match mode with
  | .RoundNearestTiesAway =>
    let y := extraRoundIntrinsic x .RoundToZero
    if eq x y then y else extraRoundIntrinsic (sub (mul (ofInt 2) x) y) .RoundToZero
  | _ => extraRoundIntrinsic x mode

/-- `base/rounding.jl:480`: truncation wrapper. -/
def trunc (x : F64) : F64 := round x .RoundToZero
/-- `base/rounding.jl:481`: floor wrapper. -/
def floor (x : F64) : F64 := round x .RoundDown
/-- `base/rounding.jl:482`: ceiling wrapper. -/
def ceil (x : F64) : F64 := round x .RoundUp

/-- `base/div.jl:77,480`: each division and subtraction rounds before nearest-even rounding. -/
def divInteger (x y : F64) (mode : Rounding := .RoundToZero) : F64 :=
  round (sub (div x y) (div (remMode x y mode) y))
/-- `base/div.jl:432`: floored quotient wrapper. -/
def fld (x y : F64) : F64 := divInteger x y .RoundDown
/-- `base/div.jl:433`: ceiling quotient wrapper. -/
def cld (x y : F64) : F64 := divInteger x y .RoundUp

/--
Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:111-122` and `base/math.jl:1137-1160`.
The release has no Float64 ties-away remainder method; master adds it at
`base/div.jl:139-149`.
-/
def remModeRelease (x y : F64) (mode : Rounding) : Jl F64 :=
  match mode with
  | .RoundToZero => .ok (rem x y)
  | .RoundDown => .ok (mod x y)
  | .RoundUp => .ok (mod x (neg y))
  | .RoundNearest => .ok (extraRemNearest x y)
  | .RoundNearestTiesAway => .error (.methodError "rem")

/--
Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:383`: subtraction precedes division.
Master `base/div.jl:480` instead divides both terms before subtracting.
-/
def divIntegerRelease (x y : F64) (mode : Rounding := .RoundToZero) : Jl F64 := do
  let r ← remModeRelease x y mode
  pure (round (div (sub x r) y))

/-- Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:336`: release floored quotient. -/
def fldRelease (x y : F64) : Jl F64 := divIntegerRelease x y .RoundDown
/-- Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:337`: release ceiling quotient. -/
def cldRelease (x y : F64) : Jl F64 := divIntegerRelease x y .RoundUp

/-- `base/float.jl:265-305`: two Float64 mantissas and the large UInt128 sticky-bit packing. -/
private def extraOfUInt128 (x : JInt .u128) : F64 :=
  let n := x.val.toNat
  if n < 2^104 then
    let lowExp := ofBits (1075 <<< 52)
    let highExp := ofBits (1127 <<< 52)
    let lowBits := Nat.land (n % 2^64) extraFrac
    let lowValue := sub (ofBits (Nat.lor (toBits lowExp) lowBits)) lowExp
    let highBits := (n >>> 52) % 2^64
    let highValue := sub (ofBits (Nat.lor (toBits highExp) highBits)) highExp
    add lowValue highValue
  else
    let lowExp := ofBits (1099 <<< 52)
    let highExp := ofBits (1151 <<< 52)
    let lowBits := Nat.lor (((n >>> 12) % 2^64) >>> 12) (Nat.land (n % 2^64) 0xffffff)
    let lowValue := sub (ofBits (Nat.lor (toBits lowExp) lowBits)) lowExp
    let highBits := (n >>> 76) % 2^64
    let highValue := sub (ofBits (Nat.lor (toBits highExp) highBits)) highExp
    add lowValue highValue

/-- `base/float.jl:243-305`: fixed-width integer conversion, preserving the Int128 source branches. -/
def ofJInt {t : IntTy} (x : JInt t) : F64 :=
  match t with
  | .u128 => extraOfUInt128 (JInt.wrap .u128 x.val)
  | .i128 =>
    let magnitude := extraOfUInt128 (JInt.wrap .u128 (Int.ofNat x.val.natAbs))
    ofBits (Nat.lor (toBits magnitude) (if x.val < 0 then extraSign else 0))
  | _ => ofInt x.val

/-- `base/floatfuncs.jl:51`: infinity is excluded by the rounded subtraction. -/
def isinteger (x : F64) : Bool := iszero (sub x (trunc x))

/-- Safe call sites of `base/float.jl:408-433`: exact truncation followed by the fixed-width intrinsic. -/
private def extraUnsafeTrunc (t : IntTy) (x : F64) : JInt t :=
  let (n, d) := toRat x
  JInt.wrap t (n.tdiv (Int.ofNat d))

/-- `base/float.jl:881-931`: the unsigned/small-signed and large-signed range-check branches. -/
def truncInt (t : IntTy) (x : F64) : Jl (JInt t) :=
  let lo := ofJInt (JInt.typemin t)
  let hi := ofJInt (JInt.typemax t)
  let valid := if !t.signed || t.bits < 64 then
      lt (sub lo one) x && lt x (add hi one)
    else le lo x && lt x hi
  if valid then .ok (extraUnsafeTrunc t x) else .error (.inexactError "round")

/-- `base/float.jl:895-927`: exact integer conversion checks integrality after the range checks. -/
def int (t : IntTy) (x : F64) : Jl (JInt t) :=
  let lo := ofJInt (JInt.typemin t)
  let hi := ofJInt (JInt.typemax t)
  let upper := if !t.signed || t.bits < 64 then add hi one else hi
  if le lo x && lt x upper && isinteger x then .ok (extraUnsafeTrunc t x)
  else .error (.inexactError t.name)

/-- `base/rounding.jl:485-491`, `base/float.jl:888-919`: direct truncation dispatch; otherwise round then convert. -/
def roundInt (t : IntTy) (x : F64) (mode : Rounding := .RoundNearest) : Jl (JInt t) :=
  match mode with
  | .RoundToZero => truncInt t x
  | _ => int t (round x mode)

/-- `base/rounding.jl:486`: floor to the requested fixed-width integer type. -/
def floorInt (t : IntTy) (x : F64) : Jl (JInt t) := roundInt t x .RoundDown
/-- `base/rounding.jl:487`: ceiling to the requested fixed-width integer type. -/
def ceilInt (t : IntTy) (x : F64) : Jl (JInt t) := roundInt t x .RoundUp

end F64
end JuliaLean.Float
