import JuliaLean.Core
import JuliaLean.Float
import JuliaLean.Float.Extras
import JuliaLean.ParsePrint.Bits

/-!
Float64 shortest printing, `base/ryu/shortest.jl` and `base/ryu/utils.jl` at
master `bbfa0ce4150` (unchanged in behaviour from 1.13.2, which differs only in
spelling `-%`/`*%` as `-`/`*`, with the same wrapping semantics).

`reduceShortest` mirrors `reduce_shortest(::Float64, maxsignif)`
(`base/ryu/shortest.jl:7-226`) branch by branch, with `T == Float64`: the
`Float32`/`Float16` refinements of `b_lastdigit` (lines 51-57, 74-80) are not
taken. Unsigned arithmetic is `JInt .u64`/`.u128`/`.u32`, wrapping exactly where
Julia wraps. The exponent bookkeeping (`e`, `ef`, `e2`, `q`, `k`, `i`, `j`,
`e10`) is `Int` arithmetic on values bounded by a few thousand, so Julia's `Int`
never wraps there; `>>` on these nonnegative `Int`s is floor division.

Each Julia `while true` loop is a fuel-bounded recursion. Every iteration divides
a `UInt64` by ten, so 24 iterations exceed the at most 20 a nonzero `UInt64`
allows; the remaining loops stop once a value's last digit is nonzero.

The lookup tables `pow5invsplit_lookup`/`pow5split_lookup` are the closed
formulas that generate them (`base/ryu/utils.jl:279-326`), evaluated directly.
`writeshortest` mirrors `base/ryu/shortest.jl:228-464` for `Float64`, for which
`typed` has no effect. The output is the list of written bytes.
-/

namespace JuliaLean.ParsePrint.Ryu

open JuliaLean JuliaLean.Float JuliaLean.ParsePrint

abbrev U64 := JInt .u64
abbrev U128 := JInt .u128
abbrev U32 := JInt .u32

/-- `base/ryu/utils.jl:27`: `floor(log10(2^e))`. -/
def log10pow2 (e : Int) : Int := (e * 78913) / 2^18
/-- `base/ryu/utils.jl:35`: `floor(log10(5^e))`. -/
def log10pow5 (e : Int) : Int := (e * 732923) / 2^20
/-- `base/ryu/utils.jl:42`: `ceil(log2(5^e))`, one for zero. -/
def pow5bits (e : Int) : Int := ((e * 1217359) / 2^19) + 1

/-- `ndigits(n, base=2)` for a positive integer. -/
def nbits (n : Nat) : Nat := Nat.log2 n + 1

/-- `base/ryu/utils.jl:279-284` with `pow5_inv_bitcount(Float64) = 122`. -/
def pow5invsplit (i : Int) : U128 :=
  let pow := 5 ^ i.toNat
  JInt.wrap .u128 (2 ^ (nbits pow - 1 + 122) / pow + 1)

/-- `base/ryu/utils.jl:308-312` with `pow5_bitcount(Float64) = 121`; a negative
`BigInt` shift is a left shift. -/
def pow5split (i : Int) : U128 :=
  let pow := 5 ^ i.toNat
  let s : Int := (nbits pow : Int) - 121
  JInt.wrap .u128 (if s ≥ 0 then pow / 2 ^ s.toNat else pow * 2 ^ (-s).toNat)

/-- `base/ryu/utils.jl:49-53`: `(m * mul) >> j` through a 128-bit product; `j ≥ 64`. -/
def mulshift (m : U64) (mul : U128) (j : Int) : U64 :=
  let wm : U128 := JInt.rem .u128 m
  let lo : U128 := JInt.rem .u128 (JInt.rem .u64 mul)
  let hi : U128 := shr mul 64
  JInt.rem .u64 (shrI (shr (wm * lo) 64 + wm * hi) (j - 64))

/-- `base/ryu/utils.jl:64-80`: wrapping `5^p` by squaring is `5^p mod 2^64`, never zero. -/
def pow5 (x : U64) (p : Int) : Bool :=
  x.val % (JInt.wrap .u64 (5 ^ p.toNat)).val == 0

/-- `base/ryu/utils.jl:87`: `(x & ((Int64(1) << p) - 1)) == 0` for `0 ≤ p < 63`. -/
def pow2 (x : U64) (p : Int) : Bool :=
  (band x (JInt.rem .u64 (JInt.lit .i64 (2 ^ p.toNat - 1)))).val == 0

/-- `base/ryu/utils.jl:94-112`. -/
def decimallength (v : U64) : Nat :=
  let v := v.val
  if v ≥ 10000000000000000 then 17 else if v ≥ 1000000000000000 then 16
  else if v ≥ 100000000000000 then 15 else if v ≥ 10000000000000 then 14
  else if v ≥ 1000000000000 then 13 else if v ≥ 100000000000 then 12
  else if v ≥ 10000000000 then 11 else if v ≥ 1000000000 then 10
  else if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/-- `(x % UInt32) -% UInt32(10) *% (xdiv % UInt32)`, the last decimal digit. -/
def mod10 (x xdiv : U64) : U32 :=
  JInt.rem .u32 x - JInt.lit .u32 10 * JInt.rem .u32 xdiv

/-- `(x % UInt32) -% UInt32(100) *% (xdiv % UInt32)`. -/
def mod100 (x xdiv : U64) : U32 :=
  JInt.rem .u32 x - JInt.lit .u32 100 * JInt.rem .u32 xdiv

/-- The mutable locals of step 4 and of the `maxsignif` reduction. -/
structure St where
  a : U64
  b : U64
  c : U64
  e10 : Int
  aAll : Bool
  bAll : Bool
  bLast : JInt .u8
  roundup : Bool

/-- `base/ryu/shortest.jl:96-112`: the slow reduction loop. -/
def slowLoop : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let cd := udivLit s.c 10
    let ad := udivLit s.a 10
    if cd.val ≤ ad.val then s else
      let am := mod10 s.a ad
      let bd := udivLit s.b 10
      let bm := mod10 s.b bd
      slowLoop n { s with
        aAll := s.aAll && am.val == 0, bAll := s.bAll && s.bLast.val == 0,
        bLast := JInt.rem .u8 bm, b := bd, c := cd, a := ad, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:114-129`: remove digits while `a` ends in zero, or while
`b` is not below `maxsignif`. -/
def aZeroLoop (maxsignif : Option Int) : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let ad := udivLit s.a 10
    let am := mod10 s.a ad
    if am.val ≠ 0 && (match maxsignif with | none => true | some M => decide (s.b.val < M)) then s else
      let cd := udivLit s.c 10
      let bd := udivLit s.b 10
      let bm := mod10 s.b bd
      aZeroLoop maxsignif n { s with
        bAll := s.bAll && s.bLast.val == 0,
        bLast := JInt.rem .u8 bm, b := bd, c := cd, a := ad, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:149-162`: the common-case reduction loop. -/
def fastLoop : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let cd := udivLit s.c 10
    let ad := udivLit s.a 10
    if cd.val ≤ ad.val then s else
      let bd := udivLit s.b 10
      let bm := mod10 s.b bd
      fastLoop n { s with
        roundup := decide (bm.val ≥ 5), b := bd, c := cd, a := ad, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:167-177` and `202-212`: reduce to `maxsignif` digits,
remembering whether the removed digits were all zero. -/
def maxLoop (M : Int) : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let bd := udivLit s.b 10
    let bm := mod10 s.b bd
    if s.b.val ≤ M then s else
      maxLoop M n { s with
        b := bd,
        roundup := if s.bAll && bd.val % 2 == 0 then decide (bm.val > 5) else decide (bm.val ≥ 5),
        bAll := s.bAll && bm.val == 0, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:181-189` and `215-223`: remove trailing zeros. -/
def zeroLoop : Nat → U64 × Int → U64 × Int
  | 0, s => s
  | n+1, (b, e10) =>
    let bd := udivLit b 10
    let bm := mod10 b bd
    if bm.val ≠ 0 then (b, e10) else zeroLoop n (bd, e10 + 1)

/-- The fuel for every reduction loop (see the module docstring). -/
def fuel : Nat := 24

/-- `base/ryu/shortest.jl:7-226`: `reduce_shortest(f::Float64, maxsignif)`. -/
def reduceShortest (f : F64) (maxsignif : Option Int) : U64 × Int :=
  let uf : U64 := JInt.wrap .u64 (F64.toBits f)
  let m : U64 := band uf (JInt.lit .u64 0x000fffffffffffff)
  let e : Int := (shr (band uf (JInt.lit .u64 0x7ff0000000000000)) 52).val
  -- Step 1
  let mf : U64 := bor (shl (JInt.lit .u64 1) 52) m
  let ef : Int := e - 1023 - 52
  let fIsInteger := (band mf (shlI (JInt.lit .u64 1) (-ef) - JInt.lit .u64 1)).val == 0
  if ef > 0 ∨ ef < -52 ∨ !fIsInteger then
    -- fixup subnormals
    let (ef, mf) := if e == 0 then ((1 : Int) - 1023 - 52, m) else (ef, mf)
    -- Step 2
    let e2 := ef - 2
    let mfIsEven := mf.val % 2 == 0
    let v : U64 := JInt.lit .u64 4 * mf
    let w : U64 := v + JInt.lit .u64 2
    let uShiftHalf := m.val == 0 && e > 1
    let u : U64 := v - JInt.lit .u64 2 + ofBool .u64 uShiftHalf
    -- Step 3
    let (a, b, c, e10, aAll, bAll) :=
      if e2 ≥ 0 then
        let q := log10pow2 e2 - (if e2 > 3 then 1 else 0)
        let k := 122 + pow5bits q - 1
        let i := -e2 + q + k
        let mul := pow5invsplit q
        let a := mulshift u mul i
        let b := mulshift v mul i
        let c := mulshift w mul i
        if q ≤ 21 then
          -- `(v % UInt32) -% 5 *% div(v, 5)`: `div(v, 5)` stays a UInt64, so the
          -- difference is taken modulo 2^64 (`base/ryu/shortest.jl:59`).
          let vmod5 : U64 := JInt.rem .u64 (JInt.rem .u32 v) -
            JInt.lit .u64 5 * udivLit v 5
          if vmod5.val == 0 then (a, b, c, q, false, pow5 v q)
          else if mfIsEven then (a, b, c, q, pow5 u q, false)
          else (a, b, c - ofBool .u64 (pow5 w q), q, false, false)
        else (a, b, c, q, false, false)
      else
        let q := log10pow5 (-e2) - (if -e2 > 1 then 1 else 0)
        let e10 := q + e2
        let i := -e2 - q
        let k := pow5bits i - 121
        let j := q - k
        let mul := pow5split i
        let a := mulshift u mul j
        let b := mulshift v mul j
        let c := mulshift w mul j
        if q ≤ 1 then
          if mfIsEven then (a, b, c, e10, !uShiftHalf, true)
          else (a, b, c - JInt.lit .u64 1, e10, false, true)
        else if q < 63 then (a, b, c, e10, false, pow2 v q)
        else (a, b, c, e10, false, false)
    let s0 : St := ⟨a, b, c, e10, aAll, bAll, JInt.lit .u8 0, false⟩
    -- Step 4
    let s :=
      if s0.aAll || s0.bAll then
        let s := slowLoop fuel s0
        let s := if s.aAll then aZeroLoop maxsignif fuel s else s
        let s := if s.bAll && s.bLast.val == 5 && s.b.val % 2 == 0 then
          { s with bLast := JInt.lit .u8 4 } else s
        { s with roundup := (s.b.val == s.a.val && (!mfIsEven || !s.aAll)) || decide (s.bLast.val ≥ 5) }
      else
        let s := { s0 with roundup := decide (s0.bLast.val ≥ 5) }
        let cd := udivLit s.c 100
        let ad := udivLit s.a 100
        let s := if cd.val > ad.val then
            let bd := udivLit s.b 100
            let bm := mod100 s.b bd
            { s with roundup := decide (bm.val ≥ 50), b := bd, c := cd, a := ad, e10 := s.e10 + 2 }
          else s
        let s := fastLoop fuel s
        { s with roundup := s.b.val == s.a.val || s.roundup }
    match maxsignif with
    | some M =>
      if s.b.val > M then
        let s := maxLoop M fuel s
        zeroLoop fuel (s.b + ofBool .u64 s.roundup, s.e10)
      else (s.b + ofBool .u64 s.roundup, s.e10)
    | none => (s.b + ofBool .u64 s.roundup, s.e10)
  else
    -- c) an integer < 2^53
    let b := shrI mf (-ef)
    let (b, e10) : U64 × Int := match maxsignif with
      | some M =>
        if b.val > M then
          let s := maxLoop M fuel ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
          (s.b + ofBool .u64 s.roundup, s.e10)
        else (b, 0)
      | none => (b, 0)
    zeroLoop fuel (b, e10)

/-! ### Output bytes -/

def chZero : Nat := 48
def chDot : Nat := 46
def chMinus : Nat := 45
def chPlus : Nat := 43
def chSpace : Nat := 32
def chE : Nat := 101

/-- `base/ryu/utils.jl:208-220`: the sign, suppressed for NaNs. -/
def appendSign (x : F64) (plus space : Bool) : List Nat :=
  if F64.signbit x && !F64.isnan x then [chMinus]
  else if plus then [chPlus] else if space then [chSpace] else []

/-- `append_c_digits(olength, digits, buf, pos)` (`base/intfuncs.jl:938-952`):
two digits per step from the right from the `_dec_d100` table, then a last
single digit. -/
def cDigits : Nat → Nat → List Nat
  | 0, _ => []
  | 1, d => [chZero + d % 10]
  | n+2, d => cDigits n (d / 100) ++ [chZero + (d % 100) / 10, chZero + d % 10]

/-- `n` zero characters. -/
def zeros (n : Nat) : List Nat := List.replicate n chZero

/-- The Float64 literal `0.05`. -/
def c005 : F64 := F64.ofBits 0x3FA999999999999A

/-- The two characters of `_dec_d100[n + 1]` for `0 ≤ n < 100` (`base/intfuncs.jl:923-936`). -/
def d100 (n : Nat) : List Nat := [chZero + n / 10, chZero + n % 10]

/-- `base/ryu/shortest.jl:228-464` for `x::Float64` (`typed` has no effect). -/
def writeshortest (x : F64) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (compact : Bool) : List Nat :=
  if F64.iszero x then
    let pre := appendSign x plus space ++ [chZero] ++ (if hash then [decchar] else [])
    if precision == -1 then pre ++ (if hash then [chZero] else [])
    else pre ++ (if hash then zeros (precision - 1).toNat else [])
  else if F64.isnan x then appendSign x plus space ++ [78, 97, 78]
  else if !F64.isfinite x then appendSign x plus space ++ [73, 110, 102]
  else
    let (output, nexp) := reduceShortest x (if compact then some (999999 : Int) else none)
    let sign := appendSign x plus space
    let olength := decimallength output
    let digits := cDigits olength output.val.toNat
    let pt : Int := nexp + olength
    let fixedForm :=
      -4 < pt ∧ pt ≤ (if precision == -1 then 6 else precision) ∧
      ¬ (pt ≥ olength ∧
        F64.lt c005 (F64.abs (F64.sub
          (F64.mod (F64.add x c005) (F64.ofInt (JInt.wrap .i64 (10 ^ (pt - olength).toNat)).val))
          c005)))
    if fixedForm then
      if pt ≤ 0 then
        let precision := precision - olength
        sign ++ [chZero, decchar] ++ zeros pt.natAbs ++ digits ++
          (if hash then zeros precision.toNat else [])
      else if pt ≥ olength then
        let precision := precision - olength - nexp
        sign ++ digits ++ zeros nexp.toNat ++
          (if hash then [decchar] ++ (if precision < 0 then [chZero] else []) ++ zeros precision.toNat
           else [])
      else
        let pointoff := olength - nexp.natAbs
        let precision := precision - olength
        sign ++ digits.take pointoff ++ [decchar] ++ digits.drop pointoff ++
          (if hash then zeros precision.toNat else [])
    else
      let (mant, precision) :=
        if olength > 1 || hash then (digits.take 1 ++ [decchar] ++ digits.drop 1, precision - olength)
        else (digits.take 1, precision)
      let mant := mant ++
        (if hash then (if olength == 1 then [chZero] else []) ++ zeros precision.toNat else [])
      let exp2 : Int := nexp + olength - 1
      let (esign, exp2) :=
        if exp2 < 0 then ([chMinus], -exp2) else if padexp then ([chPlus], exp2) else ([], exp2)
      let e := exp2.toNat
      let edigits :=
        if exp2 ≥ 100 then d100 (e / 10) ++ [chZero + e % 10]
        else if exp2 ≥ 10 then d100 e
        else (if padexp then [chZero] else []) ++ [chZero + e]
      sign ++ mant ++ [expchar] ++ esign ++ edigits

/-- `base/ryu/Ryu.jl:138-143`: `string(x::Float64)`. -/
def string (x : F64) : List Nat := writeshortest x false false true (-1) chE false chDot false

/-- `base/ryu/Ryu.jl:128-136`: `show(io, x::Float64)`, with `compact = get(io, :compact, false)`. -/
def showFloat (compact : Bool) (x : F64) : List Nat :=
  writeshortest x false false true (-1) chE false chDot compact

end JuliaLean.ParsePrint.Ryu
