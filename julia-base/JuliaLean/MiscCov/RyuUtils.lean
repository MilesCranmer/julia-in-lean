import JuliaLean.Core
import JuliaLean.ParsePrint.Bits
import JuliaLean.MiscCov.Arith
import JuliaLean.MiscCov.Basic

/-!
# `base/ryu/utils.jl` (master `bbfa0ce4150`)

The helpers of the Ryu printing algorithm. Julia integer values are `JInt`
values of the Julia type; unsigned operations wrap exactly where Julia wraps.
`BigInt` computations (`pow5split`, `pow5invsplit`, `generateinversetables`)
are `Nat` arithmetic, which is what `BigInt` arithmetic on these nonnegative
values is. `Base.power_by_squaring(UInt64(5), p; mul = *%)` is wrapping
multiplication in the ring of integers modulo `2^64`, so its value is
`5^p mod 2^64`.
-/

namespace JuliaLean.MiscCov.RyuUtils

open JuliaLean JuliaLean.ParsePrint

/-- `Float16`, `Float32`, `Float64`. -/
inductive FT where
  | f16 | f32 | f64
  deriving DecidableEq, Repr

/-- `uinttype(T)`. -/
def FT.uint : FT → IntTy
  | .f16 => .u16 | .f32 => .u32 | .f64 => .u64

/-- `widen(uinttype(T))`. -/
def FT.wide : FT → IntTy
  | .f16 => .u32 | .f32 => .u64 | .f64 => .u128

/-- `exponent_max(T)`, `precision(T)`, `exponent_bias(T)`, `significand_bits(T)`. -/
def FT.exponentMax : FT → Int | .f16 => 15 | .f32 => 127 | .f64 => 1023
def FT.precision : FT → Int | .f16 => 11 | .f32 => 24 | .f64 => 53
def FT.exponentBias : FT → Int | .f16 => 15 | .f32 => 127 | .f64 => 1023
def FT.significandBits : FT → Int | .f16 => 10 | .f32 => 23 | .f64 => 52

/-- `base/ryu/utils.jl:6-8`. -/
def pow5Bitcount : FT → Nat | .f16 => 30 | .f32 => 61 | .f64 => 121
/-- `base/ryu/utils.jl:10-12`. -/
def pow5InvBitcount : FT → Nat | .f16 => 30 | .f32 => 59 | .f64 => 122
/-- `base/ryu/utils.jl:14-16`. -/
def qinvbound : FT → Nat | .f16 => 4 | .f32 => 9 | .f64 => 21
/-- `base/ryu/utils.jl:18-20`. -/
def qbound : FT → Nat | .f16 => 15 | .f32 => 31 | .f64 => 63

/-- `x >> k` on a signed `Int` (`ashr_int`) for a nonnegative count: floor division. -/
def ashr (x : JInt t) (k : Nat) : JInt t := JInt.wrap t (x.val / 2 ^ k)

/-- `log10pow2(e) = (e * 78913) >> 18`, `base/ryu/utils.jl:27`, on `e::Int`. -/
def log10pow2 (e : JInt .i64) : JInt .i64 := ashr (e * JInt.lit .i64 78913) 18

/-- `log10pow5(e) = (e * 732923) >> 20`, `base/ryu/utils.jl:35`. -/
def log10pow5 (e : JInt .i64) : JInt .i64 := ashr (e * JInt.lit .i64 732923) 20

/-- `pow5bits(e) = ((e * 1217359) >> 19) + 1`, `base/ryu/utils.jl:42`. -/
def pow5bits (e : JInt .i64) : JInt .i64 := ashr (e * JInt.lit .i64 1217359) 19 + JInt.lit .i64 1

/-- `promote_type(U, UInt32)` for the unsigned `U` of `mulshift`. -/
def promU32 : IntTy → IntTy
  | .u8 => .u32 | .u16 => .u32 | t => t

/-- `widen(U)`. -/
def widenTy : IntTy → IntTy
  | .u8 => .u16 | .u16 => .u32 | .u32 => .u64 | .u64 => .u128 | t => t

/-- `mulshift(m::U, mul, j)`, `base/ryu/utils.jl:49-53`, for `mul` of type `widen(U)`
(the type of the lookup tables it is called with):
`((((W(m) * (mul % U)) >> nbits) + W(m) * (mul >> nbits)) >> (j - nbits)) % promote_type(U,UInt32)`. -/
def mulshift (u : IntTy) (m : JInt u) (mul : JInt (widenTy u)) (j : Int) : JInt (promU32 u) :=
  let nbits := u.bits
  let wm : JInt (widenTy u) := JInt.rem (widenTy u) m
  let lo : JInt (widenTy u) := JInt.rem (widenTy u) (JInt.rem u mul)
  let hi : JInt (widenTy u) := shr mul nbits
  JInt.rem (promU32 u) (shrI (shr (wm * lo) nbits + wm * hi) (j - nbits))

/-- `indexforexp(e) = div(e + 15, 16)`, `base/ryu/utils.jl:55` (`e ≥ 0` at every call). -/
def indexforexp (e : JInt .i64) : Jl (JInt .i64) := JInt.div (e + JInt.lit .i64 15) (JInt.lit .i64 16)

/-- `pow10bitsforindex(idx) = 16 * idx + 120`, `base/ryu/utils.jl:56`. -/
def pow10bitsforindex (idx : JInt .i64) : JInt .i64 := JInt.lit .i64 16 * idx + JInt.lit .i64 120

/-- `lengthforindex(idx)`, `base/ryu/utils.jl:57`:
`div(((Int64(16 * idx) * 1292913986) >> 32) + 1 + 16 + 8, 9)`. -/
def lengthforindex (idx : JInt .i64) : Jl (JInt .i64) :=
  JInt.div (ashr (JInt.lit .i64 16 * idx * JInt.lit .i64 1292913986) 32 + JInt.lit .i64 1 +
    JInt.lit .i64 16 + JInt.lit .i64 8) (JInt.lit .i64 9)

/-- `Base.power_by_squaring(UInt64(5), p; mul = *%)`: `5^p mod 2^64` for `p ≥ 0`. -/
def wrappedPow5 (p : JInt .i64) : JInt .u64 := JInt.wrap .u64 (5 ^ p.val.toNat)

/-- `pow5(x, p) = x % wrapped_pow == 0`, `base/ryu/utils.jl:64-80`; `x::UInt64`.
`wrapped_pow` is never zero (it is odd), so `%` does not throw. -/
def pow5 (x : JInt .u64) (p : JInt .i64) : Bool :=
  x.val % (wrappedPow5 p).val == 0

/-- `Int64(1) << p` for `p ≥ 0` (`shl_int`): zero once the count reaches 64. -/
def shlOne64 (p : Nat) : JInt .i64 := JInt.wrap .i64 (if p < 64 then 2 ^ p else 0)

/-- `pow2(x, p) = (x & ((Int64(1) << p) - 1)) == 0`, `base/ryu/utils.jl:87`, for an
unsigned `x` (`UInt64` or `UInt32`) and `p ≥ 0`. `x & mask` reinterprets the `Int64`
mask in the common type, whose low bits are the two's-complement bits of the mask. -/
def pow2 {u : IntTy} (x : JInt u) (p : Nat) : Bool :=
  let mask : JInt .i64 := shlOne64 p - JInt.lit .i64 1
  Nat.land x.val.toNat (mask.val % 2 ^ 64).toNat == 0

/-- `decimallength(v)`, `base/ryu/utils.jl:94-112` (the method for other integers). -/
def decimallength (v : Int) : Nat :=
  if v ≥ 10000000000000000 then 17 else if v ≥ 1000000000000000 then 16
  else if v ≥ 100000000000000 then 15 else if v ≥ 10000000000000 then 14
  else if v ≥ 1000000000000 then 13 else if v ≥ 100000000000 then 12
  else if v ≥ 10000000000 then 11 else if v ≥ 1000000000 then 10
  else if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/-- `decimallength(v::UInt32)`, `base/ryu/utils.jl:113-123`. -/
def decimallength32 (v : JInt .u32) : Nat :=
  let v := v.val
  if v ≥ 100000000 then 9 else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7 else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/-- `decimallength(v::UInt16)`, `base/ryu/utils.jl:124-130`. -/
def decimallength16 (v : JInt .u16) : Nat :=
  let v := v.val
  if v ≥ 10000 then 5 else if v ≥ 1000 then 4
  else if v ≥ 100 then 3 else if v ≥ 10 then 2 else 1

/-- `ndigits(v)` for `v ≥ 0`: the number of decimal digits (one for zero). -/
def ndigits10 (v : Nat) : Nat := (Nat.toDigits 10 v).length

/-! ### 256-bit products and `mod1e9` -/

/-- `umul256(a, bHi, bLo)`, `base/ryu/utils.jl:153-176`. Returns `(pLo, pHi)`. -/
def umul256 (a : JInt .u128) (bHi bLo : JInt .u64) : JInt .u128 × JInt .u128 :=
  let aLo : JInt .u64 := JInt.rem .u64 a
  let aHi : JInt .u64 := JInt.rem .u64 (shr a 64)
  let b00 : JInt .u128 := JInt.rem .u128 aLo * JInt.rem .u128 bLo
  let b01 : JInt .u128 := JInt.rem .u128 aLo * JInt.rem .u128 bHi
  let b10 : JInt .u128 := JInt.rem .u128 aHi * JInt.rem .u128 bLo
  let b11 : JInt .u128 := JInt.rem .u128 aHi * JInt.rem .u128 bHi
  let b00Lo : JInt .u64 := JInt.rem .u64 b00
  let b00Hi : JInt .u64 := JInt.rem .u64 (shr b00 64)
  let mid1 : JInt .u128 := b10 + JInt.rem .u128 b00Hi
  let mid1Lo : JInt .u64 := JInt.rem .u64 mid1
  let mid1Hi : JInt .u64 := JInt.rem .u64 (shr mid1 64)
  let mid2 : JInt .u128 := b01 + JInt.rem .u128 mid1Lo
  let mid2Lo : JInt .u64 := JInt.rem .u64 mid2
  let mid2Hi : JInt .u64 := JInt.rem .u64 (shr mid2 64)
  let pHi : JInt .u128 := b11 + JInt.rem .u128 mid1Hi + JInt.rem .u128 mid2Hi
  let pLo : JInt .u128 := bor (shl (JInt.rem .u128 mid2Lo) 64) (JInt.rem .u128 b00Lo)
  (pLo, pHi)

/-- `umul256_hi(a, bHi, bLo) = umul256(a, bHi, bLo)[2]`, `base/ryu/utils.jl:183`. -/
def umul256Hi (a : JInt .u128) (bHi bLo : JInt .u64) : JInt .u128 := (umul256 a bHi bLo).2

/-- `mod1e9(v::UInt128)`, `base/ryu/utils.jl:185-191`. -/
def mod1e9 (v : JInt .u128) : JInt .u32 :=
  let multiplied := umul256Hi v (JInt.lit .u64 0x89705F4136B4A597) (JInt.lit .u64 0x31680A88F8953031)
  let shifted : JInt .u32 := JInt.rem .u32 (shr multiplied 29)
  JInt.rem .u32 v - JInt.lit .u32 1000000000 * shifted

/-- `mulshiftmod1e9(m, mula, mulb, mulc, j)`, `base/ryu/utils.jl:198-206`, with
`m::UInt64` and `UInt64` limbs (as at every call site, `base/ryu/fixed.jl:60,110`
and `base/ryu/exp.jl:68,108`). -/
def mulshiftmod1e9 (m mula mulb mulc : JInt .u64) (j : Int) : JInt .u32 :=
  let b0 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mula
  let b1 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mulb
  let b2 : JInt .u128 := JInt.rem .u128 m * JInt.rem .u128 mulc
  let mid : JInt .u128 := b1 + JInt.rem .u128 (JInt.rem .u64 (shr b0 64))
  let s1 : JInt .u128 := b2 + JInt.rem .u128 (JInt.rem .u64 (shr mid 64))
  let v := shrI s1 (j - 128)
  mod1e9 v

/-! ### Output helpers -/

/-- The sign bit and NaN test of a float, by its bit pattern of `bits` bits. -/
structure FloatBits where
  signbit : Bool
  isnan : Bool

/-- `append_sign(x, plus, space, buf, pos)`, `base/ryu/utils.jl:208-220`: the
written byte (if any) and the returned position. -/
def appendSign (x : FloatBits) (plus space : Bool) (pos : Int) : Option Nat × Int :=
  if x.signbit && !x.isnan then (some 45, pos + 1)
  else if plus then (some 43, pos + 1)
  else if space then (some 32, pos + 1)
  else (none, pos)

/-- A byte buffer: `buf[k]` for one-based `k`. -/
abbrev Buf := Int → Nat

def Buf.set (b : Buf) (k : Int) (v : Nat) : Buf := fun i => if i = k then v else b i

/-- `Base.append_c_digits_fast(olength, digits, buf, pos)` (`base/intfuncs.jl`):
writes the `olength` low decimal digits of `digits`, most significant first, at
`pos:pos+olength-1` and returns `pos + olength`. -/
def appendCDigits (olength : Nat) (digits : Nat) (buf : Buf) (pos : Int) : Buf × Int :=
  (fun i => if pos ≤ i ∧ i < pos + olength then
      48 + digits / 10 ^ (olength - 1 - (i - pos).toNat) % 10 else buf i, pos + olength)

/-- `append_d_digits(olength, digits, buf, pos, decchar)`, `base/ryu/utils.jl:225-230`. -/
def appendDDigits (olength : Nat) (digits : Nat) (buf : Buf) (pos : Int) (decchar : Nat) : Buf × Int :=
  let r := appendCDigits olength digits buf (pos + 1)
  let buf := r.1.set pos (r.1 (pos + 1))
  let buf := buf.set (pos + 1) decchar
  (buf, r.2)

/-! ### Tables -/

/-- `ndigits(n, base = 2)` for `n > 0`. -/
def nbits (n : Nat) : Nat := Nat.log2 n + 1

/-- `pow5invsplit(T, i)`, `base/ryu/utils.jl:279-284`:
`W(div(big(1) << (ndigits(pow, base=2) - 1 + pow5_inv_bitcount(T)), pow) + 1)`. -/
def pow5invsplit (T : FT) (i : Nat) : Jl (JInt T.wide) :=
  let pow := 5 ^ i
  let inv := 2 ^ (nbits pow - 1 + pow5InvBitcount T) / pow + 1
  JInt.convert T.wide inv

/-- `pow5split(T, i)`, `base/ryu/utils.jl:308-312`: `W(pow >> (ndigits(pow, base=2) -
pow5_bitcount(T)))`; a negative `BigInt` shift count shifts left. -/
def pow5split (T : FT) (i : Nat) : Jl (JInt T.wide) :=
  let pow := 5 ^ i
  let s : Int := (nbits pow : Int) - pow5Bitcount T
  JInt.convert T.wide (if s ≥ 0 then pow / 2 ^ s.toNat else pow * 2 ^ (-s).toNat)

/-- The last table index of `pow5invsplit_lookup(T, ·)`, `base/ryu/utils.jl:294-295`:
`log10pow2(exponent_max(T) - precision(T) - 1)`. -/
def invImax (T : FT) : Int := (log10pow2 (JInt.lit .i64 (T.exponentMax - T.precision - 1))).val

/-- The last table index of `pow5split_lookup(T, ·)`, `base/ryu/utils.jl:322-323`:
`1 - e2_min - log10pow5(-e2_min)` with `e2_min = 1 - exponent_bias(T) - significand_bits(T) - 2`. -/
def splitImax (T : FT) : Int :=
  let e2min := 1 - T.exponentBias - T.significandBits - 2
  1 - e2min - (log10pow5 (JInt.lit .i64 (-e2min))).val

/-- The table `pow5invsplit_table_T`: `Tuple(Any[pow5invsplit(T, i) for i = 0:i_max])`
(every element converts, as the table builds at bootstrap). -/
def invTable (T : FT) : List (Jl (JInt T.wide)) :=
  (List.range ((invImax T).toNat + 1)).map (pow5invsplit T)

def splitTable (T : FT) : List (Jl (JInt T.wide)) :=
  (List.range ((splitImax T).toNat + 1)).map (pow5split T)

/-- `pow5invsplit_lookup(T, i) = @inbounds(table[i+1])`, `base/ryu/utils.jl:297`;
`none` is an access outside the table. -/
def pow5invsplitLookup (T : FT) (i : Int) : Option (Jl (JInt T.wide)) :=
  if 0 ≤ i then (invTable T)[i.toNat]? else none

/-- `pow5split_lookup(T, i)`, `base/ryu/utils.jl:325`. -/
def pow5splitLookup (T : FT) (i : Int) : Option (Jl (JInt T.wide)) :=
  if 0 ≤ i then (splitTable T)[i.toNat]? else none

/-- `mulshiftinvsplit(T, mv, mp, mm, i, j)`, `base/ryu/utils.jl:132-138`, with the
table entry `mul`. -/
def mulshiftinvsplit (u : IntTy) (mul : JInt (widenTy u)) (mv mp mm : JInt u) (j : Int) :
    JInt (promU32 u) × JInt (promU32 u) × JInt (promU32 u) :=
  (mulshift u mv mul j, mulshift u mp mul j, mulshift u mm mul j)

/-- `mulshiftsplit(T, mv, mp, mm, i, j)`, `base/ryu/utils.jl:140-146`. -/
def mulshiftsplit (u : IntTy) (mul : JInt (widenTy u)) (mv mp mm : JInt u) (j : Int) :
    JInt (promU32 u) × JInt (promU32 u) × JInt (promU32 u) :=
  (mulshift u mv mul j, mulshift u mp mul j, mulshift u mm mul j)

/-! ### `generateinversetables()`, `base/ryu/utils.jl:242-268` -/

/-- The state of the `while true` loop for one `idx`: the table so far, `i`, and
`MIN_BLOCK_2[idx + 1]` (`none` while it is `0xff`). -/
structure InvState where
  split : List (Nat × Nat × Nat)
  minBlock : Option Nat
  deriving Repr

def bigMask : Nat := 2 ^ 64 - 1

/-- `v = ((big(10)^(9 * (i + 1)) >> (-(120 - 16 * idx))) % (big(10)^9) << (120 + 16))`;
a negative `BigInt` shift count shifts left. -/
def invV (idx i : Nat) : Nat :=
  let p := 10 ^ (9 * (i + 1))
  let s : Int := -(120 - 16 * (idx : Int))
  let q := if s ≥ 0 then p / 2 ^ s.toNat else p * 2 ^ (-s).toNat
  q % (10 ^ 9 * 2 ^ (120 + 16))

/-- The `while true` loop body, `base/ryu/utils.jl:250-262`, on fuel. -/
def invLoop (idx : Nat) : Nat → Nat → InvState → InvState
  | 0, _, s => s
  | fuel + 1, i, s =>
    let v := invV idx i
    if s.minBlock.isNone && (v * 2 ^ (54 + 8)) / 2 ^ 128 == 0 then invLoop idx fuel (i + 1) s
    else
      let s := if s.minBlock.isNone then { s with minBlock := some i } else s
      if v == 0 then s
      else invLoop idx fuel (i + 1)
        { s with split := s.split ++ [((v &&& bigMask) % 2 ^ 64, ((v >>> 64) &&& bigMask) % 2 ^ 64,
          ((v >>> 128) &&& bigMask) % 2 ^ 64)] }

/-- One iteration `idx` of the `for` loop: push the current length of `POW10_SPLIT_2` to
`POW10_OFFSET_2`, run the `while` loop from `i = 0`, push `MIN_BLOCK_2[idx + 1]`.
`fuel` bounds the `while` loop. -/
def genStep (fuel : Nat) (acc : List Nat × List Nat × List (Nat × Nat × Nat)) (idx : Nat) :
    List Nat × List Nat × List (Nat × Nat × Nat) :=
  let s := invLoop idx fuel 0 ⟨acc.2.2, none⟩
  (acc.1 ++ [acc.2.2.length], acc.2.1 ++ [s.minBlock.getD 0xff], s.split)

/-- The results `(POW10_OFFSET_2, MIN_BLOCK_2, POW10_SPLIT_2)` for `idx = 0:n-1`; Julia
uses `n = 68`. After the loop the final offset and a `MIN_BLOCK_2` of 0 are pushed. -/
def generateinversetables (n fuel : Nat) : List Nat × List Nat × List (Nat × Nat × Nat) :=
  let r := (List.range n).foldl (genStep fuel) ([], [], [])
  (r.1 ++ [r.2.2.length], r.2.1 ++ [0], r.2.2)

end JuliaLean.MiscCov.RyuUtils
