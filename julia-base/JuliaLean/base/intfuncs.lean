import JuliaLean.base.int
import JuliaLean.base.operators
import JuliaLean.base.checked
import JuliaLean.base.float
import JuliaLean.base.div
import JuliaLean.base.number
import JuliaLean.base.promotion
import JuliaLean.base.math
import JuliaLean.base.multinverses
import JuliaLean.base.reduce
import JuliaLean.base.char
import JuliaLean.base.rounding
import JuliaLean.Runtime.IO
import JuliaLean.base.array
import JuliaLean.base.pointer
import JuliaLean.base.strings.string

/-!
# Model of `base/intfuncs.jl`

Typed source models at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
`IntegerOps` keeps generic Integer methods open to BigInt and user-defined integers.
BitInteger specializations use `JuliaLean.base.int` at every width and signedness.
Callees loaded in other Base files remain typed arguments. Loop bounds count source
iterations from the input magnitude, exponent bits, or allocation size.
-/

namespace JuliaLean.base.intfuncs

open JuliaLean

/--
Julia source: base/intfuncs.jl:718-724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const powers_of_ten = [
    0x0000000000000001, 0x000000000000000a, 0x0000000000000064, 0x00000000000003e8,
    0x0000000000002710, 0x00000000000186a0, 0x00000000000f4240, 0x0000000000989680,
    0x0000000005f5e100, 0x000000003b9aca00, 0x00000002540be400, 0x000000174876e800,
    0x000000e8d4a51000, 0x000009184e72a000, 0x00005af3107a4000, 0x00038d7ea4c68000,
    0x002386f26fc10000, 0x016345785d8a0000, 0x0de0b6b3a7640000, 0x8ac7230489e80000,
]
```
-/
def powersOfTen : List (JInt .u64) :=
  [JuliaLean.base.int.lit .u64 0x0000000000000001, JuliaLean.base.int.lit .u64 0x000000000000000a, JuliaLean.base.int.lit .u64 0x0000000000000064, JuliaLean.base.int.lit .u64 0x00000000000003e8, JuliaLean.base.int.lit .u64 0x0000000000002710, JuliaLean.base.int.lit .u64 0x00000000000186a0, JuliaLean.base.int.lit .u64 0x00000000000f4240, JuliaLean.base.int.lit .u64 0x0000000000989680, JuliaLean.base.int.lit .u64 0x0000000005f5e100, JuliaLean.base.int.lit .u64 0x000000003b9aca00, JuliaLean.base.int.lit .u64 0x00000002540be400, JuliaLean.base.int.lit .u64 0x000000174876e800, JuliaLean.base.int.lit .u64 0x000000e8d4a51000, JuliaLean.base.int.lit .u64 0x000009184e72a000, JuliaLean.base.int.lit .u64 0x00005af3107a4000, JuliaLean.base.int.lit .u64 0x00038d7ea4c68000, JuliaLean.base.int.lit .u64 0x002386f26fc10000, JuliaLean.base.int.lit .u64 0x016345785d8a0000, JuliaLean.base.int.lit .u64 0x0de0b6b3a7640000, JuliaLean.base.int.lit .u64 0x8ac7230489e80000]

/--
Julia source: base/intfuncs.jl:923-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _dec_d100 = UInt16[
# generating expression: UInt16[(0x30 + i % 10) << 0x8 + (0x30 + i ÷ 10) for i = 0:99]
#    0 0,    0 1,    0 2,    0 3, and so on in little-endian
  0x3030, 0x3130, 0x3230, 0x3330, 0x3430, 0x3530, 0x3630, 0x3730, 0x3830, 0x3930,
  0x3031, 0x3131, 0x3231, 0x3331, 0x3431, 0x3531, 0x3631, 0x3731, 0x3831, 0x3931,
  0x3032, 0x3132, 0x3232, 0x3332, 0x3432, 0x3532, 0x3632, 0x3732, 0x3832, 0x3932,
  0x3033, 0x3133, 0x3233, 0x3333, 0x3433, 0x3533, 0x3633, 0x3733, 0x3833, 0x3933,
  0x3034, 0x3134, 0x3234, 0x3334, 0x3434, 0x3534, 0x3634, 0x3734, 0x3834, 0x3934,
  0x3035, 0x3135, 0x3235, 0x3335, 0x3435, 0x3535, 0x3635, 0x3735, 0x3835, 0x3935,
  0x3036, 0x3136, 0x3236, 0x3336, 0x3436, 0x3536, 0x3636, 0x3736, 0x3836, 0x3936,
  0x3037, 0x3137, 0x3237, 0x3337, 0x3437, 0x3537, 0x3637, 0x3737, 0x3837, 0x3937,
  0x3038, 0x3138, 0x3238, 0x3338, 0x3438, 0x3538, 0x3638, 0x3738, 0x3838, 0x3938,
  0x3039, 0x3139, 0x3239, 0x3339, 0x3439, 0x3539, 0x3639, 0x3739, 0x3839, 0x3939
]
```
-/
def decimalPairs : List (JInt .u16) :=
  [JuliaLean.base.int.lit .u16 0x3030, JuliaLean.base.int.lit .u16 0x3130, JuliaLean.base.int.lit .u16 0x3230, JuliaLean.base.int.lit .u16 0x3330, JuliaLean.base.int.lit .u16 0x3430, JuliaLean.base.int.lit .u16 0x3530, JuliaLean.base.int.lit .u16 0x3630, JuliaLean.base.int.lit .u16 0x3730, JuliaLean.base.int.lit .u16 0x3830, JuliaLean.base.int.lit .u16 0x3930, JuliaLean.base.int.lit .u16 0x3031, JuliaLean.base.int.lit .u16 0x3131, JuliaLean.base.int.lit .u16 0x3231, JuliaLean.base.int.lit .u16 0x3331, JuliaLean.base.int.lit .u16 0x3431, JuliaLean.base.int.lit .u16 0x3531, JuliaLean.base.int.lit .u16 0x3631, JuliaLean.base.int.lit .u16 0x3731, JuliaLean.base.int.lit .u16 0x3831, JuliaLean.base.int.lit .u16 0x3931, JuliaLean.base.int.lit .u16 0x3032, JuliaLean.base.int.lit .u16 0x3132, JuliaLean.base.int.lit .u16 0x3232, JuliaLean.base.int.lit .u16 0x3332, JuliaLean.base.int.lit .u16 0x3432, JuliaLean.base.int.lit .u16 0x3532, JuliaLean.base.int.lit .u16 0x3632, JuliaLean.base.int.lit .u16 0x3732, JuliaLean.base.int.lit .u16 0x3832, JuliaLean.base.int.lit .u16 0x3932, JuliaLean.base.int.lit .u16 0x3033, JuliaLean.base.int.lit .u16 0x3133, JuliaLean.base.int.lit .u16 0x3233, JuliaLean.base.int.lit .u16 0x3333, JuliaLean.base.int.lit .u16 0x3433, JuliaLean.base.int.lit .u16 0x3533, JuliaLean.base.int.lit .u16 0x3633, JuliaLean.base.int.lit .u16 0x3733, JuliaLean.base.int.lit .u16 0x3833, JuliaLean.base.int.lit .u16 0x3933, JuliaLean.base.int.lit .u16 0x3034, JuliaLean.base.int.lit .u16 0x3134, JuliaLean.base.int.lit .u16 0x3234, JuliaLean.base.int.lit .u16 0x3334, JuliaLean.base.int.lit .u16 0x3434, JuliaLean.base.int.lit .u16 0x3534, JuliaLean.base.int.lit .u16 0x3634, JuliaLean.base.int.lit .u16 0x3734, JuliaLean.base.int.lit .u16 0x3834, JuliaLean.base.int.lit .u16 0x3934, JuliaLean.base.int.lit .u16 0x3035, JuliaLean.base.int.lit .u16 0x3135, JuliaLean.base.int.lit .u16 0x3235, JuliaLean.base.int.lit .u16 0x3335, JuliaLean.base.int.lit .u16 0x3435, JuliaLean.base.int.lit .u16 0x3535, JuliaLean.base.int.lit .u16 0x3635, JuliaLean.base.int.lit .u16 0x3735, JuliaLean.base.int.lit .u16 0x3835, JuliaLean.base.int.lit .u16 0x3935, JuliaLean.base.int.lit .u16 0x3036, JuliaLean.base.int.lit .u16 0x3136, JuliaLean.base.int.lit .u16 0x3236, JuliaLean.base.int.lit .u16 0x3336, JuliaLean.base.int.lit .u16 0x3436, JuliaLean.base.int.lit .u16 0x3536, JuliaLean.base.int.lit .u16 0x3636, JuliaLean.base.int.lit .u16 0x3736, JuliaLean.base.int.lit .u16 0x3836, JuliaLean.base.int.lit .u16 0x3936, JuliaLean.base.int.lit .u16 0x3037, JuliaLean.base.int.lit .u16 0x3137, JuliaLean.base.int.lit .u16 0x3237, JuliaLean.base.int.lit .u16 0x3337, JuliaLean.base.int.lit .u16 0x3437, JuliaLean.base.int.lit .u16 0x3537, JuliaLean.base.int.lit .u16 0x3637, JuliaLean.base.int.lit .u16 0x3737, JuliaLean.base.int.lit .u16 0x3837, JuliaLean.base.int.lit .u16 0x3937, JuliaLean.base.int.lit .u16 0x3038, JuliaLean.base.int.lit .u16 0x3138, JuliaLean.base.int.lit .u16 0x3238, JuliaLean.base.int.lit .u16 0x3338, JuliaLean.base.int.lit .u16 0x3438, JuliaLean.base.int.lit .u16 0x3538, JuliaLean.base.int.lit .u16 0x3638, JuliaLean.base.int.lit .u16 0x3738, JuliaLean.base.int.lit .u16 0x3838, JuliaLean.base.int.lit .u16 0x3938, JuliaLean.base.int.lit .u16 0x3039, JuliaLean.base.int.lit .u16 0x3139, JuliaLean.base.int.lit .u16 0x3239, JuliaLean.base.int.lit .u16 0x3339, JuliaLean.base.int.lit .u16 0x3439, JuliaLean.base.int.lit .u16 0x3539, JuliaLean.base.int.lit .u16 0x3639, JuliaLean.base.int.lit .u16 0x3739, JuliaLean.base.int.lit .u16 0x3839, JuliaLean.base.int.lit .u16 0x3939]

/--
Julia source: base/intfuncs.jl:1044-1044 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const base36digits = UInt8['0':'9';'a':'z']
```
-/
def base36Digits : List Nat :=
  (List.range 10).map (fun i => 48 + i) ++ (List.range 26).map (fun i => 97 + i)

/--
Julia source: base/intfuncs.jl:1045-1045 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const base62digits = UInt8['0':'9';'A':'Z';'a':'z']
```
-/
def base62Digits : List Nat :=
  (List.range 10).map (fun i => 48 + i) ++ (List.range 26).map (fun i => 65 + i) ++
    (List.range 26).map (fun i => 97 + i)

structure IntegerOps (I : Type) where
  value : I → Int
  unsigned : Bool
  ofInt : Int → I
  add : I → I → I
  sub : I → I → I
  mul : I → I → I
  neg : I → I
  abs : I → I
  checkedAbs : I → Jl I
  checkedMul : I → I → Jl I
  div : I → I → Jl I
  rem : I → I → Jl I
  divrem : I → I → Jl (I × I)
  shiftRight : I → Nat → I
  shiftLeft : I → Nat → I
  trailingZeros : I → Nat
  countOnes : I → Nat

def repeatM {S : Type} (n : Nat) (step : S → Jl S) (s : S) : Jl S :=
  (List.range n).foldlM (fun s _ => step s) s

def magnitude {I : Type} (o : IntegerOps I) (x : I) : Nat := (o.value x).natAbs

def bitOps (t : IntTy) (divrem : JInt t → JInt t → Jl (JInt t × JInt t)) :
    IntegerOps (JInt t) where
  value := Subtype.val
  unsigned := !t.signed
  ofInt := JuliaLean.base.int.lit t
  add := JuliaLean.base.int.add
  sub := JuliaLean.base.int.sub
  mul := JuliaLean.base.int.mul
  neg := JuliaLean.base.int.neg
  abs := JuliaLean.base.int.abs
  checkedAbs := JuliaLean.base.checked.checkedAbsBits
  checkedMul := JuliaLean.base.checked.checkedMulBits
  div := JuliaLean.base.int.divSame
  rem := JuliaLean.base.int.remSame
  divrem := divrem
  shiftRight := fun x n => JuliaLean.base.int.shr_Int x (JuliaLean.base.int.lit .i64 n)
  shiftLeft := fun x n => JuliaLean.base.int.shl_int x (JuliaLean.base.int.lit .i64 n)
  trailingZeros := fun x => (JuliaLean.base.int.cttz_int x).val.toNat
  countOnes := fun x => (JuliaLean.base.int.ctpop_int x).val.toNat

structure Buffer where
  bytes : List Nat
  writes : List Int := []
  tableReads : List (Int × Nat) := []
  deriving Repr, DecidableEq

def newBuffer (n : Int) : Jl Buffer := do
  let length ← JInt.convert (IntTy.u64.name) .u64 n
  pure ⟨List.replicate length.val.toNat 0, [], []⟩
def store (b : Buffer) (i : Int) (v : Nat) : Buffer :=
  { b with bytes := b.bytes.set (i - 1).toNat (v % 256), writes := b.writes ++ [i] }
def readTable (b : Buffer) (index : Int) (size : Nat) : Buffer :=
  { b with tableReads := b.tableReads ++ [(index, size)] }
def minusSign (neg : Bool) (b : Buffer) : Buffer := if neg then store b 1 45 else b
def boolInt (b : Bool) : Int := if b then 1 else 0

def topBit {t : IntTy} (x : JInt t) : Nat :=
  (JuliaLean.base.int.top_set_bit x).val.toNat

def minBits {t : IntTy} (a b : JInt t) : JInt t :=
  JuliaLean.base.operators.min JuliaLean.base.int.ltSame JuliaLean.base.int.ifelse a b

def maxBits {t : IntTy} (a b : JInt t) : JInt t :=
  JuliaLean.base.operators.max JuliaLean.base.int.ltSame JuliaLean.base.int.ifelse a b

def unsignedAbs {t : IntTy} (x : JInt t) : JInt t.toUnsigned := JuliaLean.base.int.unsigned (JuliaLean.base.int.abs x)

def gcdEuclidLoop {I : Type} (o : IntegerOps I) : Nat → I → I → Jl (I × I)
  | 0, a, b => pure (a, b)
  | n + 1, a, b => do
      if o.value b = 0 then pure (a, b) else
        let t := b
        let b ← o.rem a b
        gcdEuclidLoop o n t b

def powerSquares {A : Type} (mul : A → A → Jl A) (n : Nat) (x : A) : Jl A :=
  repeatM n (fun x => mul x x) x

def powerLoop {A E : Type} (eo : IntegerOps E) (mul : A → A → Jl A) :
    Nat → A → A → E → Jl A
  | 0, _, y, _ => pure y
  | n + 1, x, y, p => do
      if eo.value p ≤ 0 then pure y else
        let t := eo.trailingZeros p + 1
        let p := eo.shiftRight p t
        let x ← powerSquares mul t x
        let y ← mul y x
        powerLoop eo mul n x y p

def powermodLoop {P U : Type} (po : IntegerOps P) (value : U → Int)
    (mulmod : U → U → Jl U) : Nat → P → U → U → Jl U
  | 0, _, rr, _ => pure rr
  | n + 1, p, rr, bb => do
      let rr ← if po.value p % 2 ≠ 0 then mulmod rr bb else pure rr
      let p := po.shiftRight p 1
      if po.value p = 0 then pure rr else
        let bb ← mulmod bb bb
        powermodLoop po value mulmod n p rr bb

def digitChar (large : Bool) (k : Nat) : Jl Nat :=
  match (if large then base62Digits else base36Digits)[k]? with
  | some ch => pure ch
  | none => .error .boundsError

def hexChar (d : Nat) : Nat := d + if d > 9 then 87 else 48

def binLoop4 {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) :
    Nat → Buffer → U → Int → Buffer × U × Int
  | 0, b, x, i => (b, x, i)
  | n + 1, b, x, i =>
      if i < 4 then (b, x, i) else
        let byte := lowByte x % 256
        let b32 := JuliaLean.base.int.lit .u32 byte
        let packed := JuliaLean.base.int.mulWrap b32 (JuliaLean.base.int.lit .u32 0x08040201)
        let shifted := JuliaLean.base.int.lshr_int packed (JuliaLean.base.int.lit .u8 3)
        let d := (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .u32 0x30303030)
          (JuliaLean.base.int.band shifted (JuliaLean.base.int.lit .u32 0x01010101))).val.toNat
        let b := store b (i - 3) (d % 256)
        let b := store b (i - 2) (d / 2^8 % 256)
        let b := store b (i - 1) (d / 2^16 % 256)
        let b := store b i (d / 2^24 % 256)
        binLoop4 lowByte shr n b (shr x 4) (i - 4)

def binLoop1 {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) (neg : Bool) :
    Nat → Buffer → U → Int → Buffer
  | 0, b, _, _ => b
  | n + 1, b, x, i =>
      if i ≤ boolInt neg then b else
        binLoop1 lowByte shr neg n (store b i (48 + lowByte x % 2)) (shr x 1) (i - 1)

def octLoop {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) (neg : Bool) :
    Nat → Buffer → U → Int → Buffer
  | 0, b, _, _ => b
  | n + 1, b, x, i =>
      if i ≤ boolInt neg then b else
        octLoop lowByte shr neg n (store b i (48 + lowByte x % 8)) (shr x 3) (i - 1)

def hexLoop {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) :
    Nat → Buffer → U → Int → Buffer × U × Int
  | 0, b, x, i => (b, x, i)
  | n + 1, b, x, i =>
      if i < 2 then (b, x, i) else
        let byte := lowByte x % 256
        let b := store b (i - 1) (hexChar (byte / 16))
        let b := store b i (hexChar (byte % 16))
        hexLoop lowByte shr n b (shr x 8) (i - 2)

def decimalPair (d : Nat) : Jl Nat :=
  match decimalPairs[d]? with
  | some pair => pure pair.val.toNat
  | none => .error .boundsError

def appendLoop {U : Type} (value : U → Int) (divrem : U → Nat → Jl (U × Nat)) :
    Nat → Int → U → Buffer → Int → Jl (Int × U × Buffer)
  | 0, i, x, b, _ => pure (i, x, b)
  | n + 1, i, x, b, pos => do
      if i < 2 then pure (i, x, b) else
        let (d, c) ← divrem x 100
        let v ← decimalPair c
        let b := readTable b (c + 1) 100
        let b := store b (wrapInt .i64 (pos + i - 2)) (v % 256)
        let b := store b (wrapInt .i64 (pos + i - 1)) (v / 256 % 256)
        appendLoop value divrem n (i - 2) d b pos

def baseLoop {I : Type} (o : IntegerOps I) (rem : I → Int → Jl Int) (div : I → Int → Jl I)
    (mod : I → Int → Jl Int) (cld : I → Int → Jl I) (base : Int) (large neg : Bool) :
    Nat → I → Int → Buffer → Jl Buffer
  | 0, _, _, b => pure b
  | n + 1, x, i, b => do
      if i ≤ boolInt neg then pure b else
        if 0 < base then
          let r ← rem x base
          let b := readTable b (r + 1) (if large then 62 else 36)
          let ch ← digitChar large r.toNat
          let b := store b i ch
          let q ← div x base
          baseLoop o rem div mod cld base large neg n q (i - 1) b
        else
          let r ← mod x (-base)
          let b := readTable b (r + 1) (if large then 62 else 36)
          let ch ← digitChar large r.toNat
          let b := store b i ch
          let q ← cld x base
          baseLoop o rem div mod cld base large neg n q (i - 1) b
structure Vector (A : Type) where
  first : Int := 1
  values : List A
  writes : List Int := []
  deriving Repr, DecidableEq

def vectorStore {A : Type} (a : Vector A) (i : Int) (x : A) : Vector A :=
  { a with values := a.values.set (i - a.first).toNat x, writes := a.writes ++ [i] }

def factorialLoop {I F : Type} (value : I → Int) (ofInt : Int → Jl F)
    (mul : F → F → Jl F) (n : I) (f : F) : Jl F :=
  (List.range ((value n - 1).toNat)).foldlM (fun f (j : Nat) => do
    let i ← ofInt ((j : Int) + 2)
    mul f i) f

def binomialLoop {I : Type} (o : IntegerOps I) (wideDiv : I → I → I → Jl Int) :
    Nat → I → I → I → I → Jl I
  | 0, x, _, _, _ => pure x
  | f + 1, x, nn, rr, k => do
      if o.value rr > o.value k then pure x else
        let xt ← wideDiv x nn rr
        let x := o.ofInt xt
        if o.value x ≠ xt then .error (.overflowError "") else
          binomialLoop o wideDiv f x (o.add nn (o.ofInt 1)) (o.add rr (o.ofInt 1)) k

/--
Julia source: base/intfuncs.jl:44-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcd(a::T, b::T) where T<:Integer
    while b != 0
        t = b
        b = rem(a, b)
        a = t
    end
    checked_abs(a)
end
```
-/
def gcd_Integer {I : Type} (o : IntegerOps I) (a b : I) : Jl I := do
  let (a, _) ← gcdEuclidLoop o (magnitude o b + 1) a b
  o.checkedAbs a

/--
Julia source: base/intfuncs.jl:65-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline __throw_gcd_overflow(a, b) =
    throw(OverflowError(LazyString("gcd(", a, ", ", b, ") overflows")))
```
-/
def throwGcdOverflow {A B R : Type} (_a : A) (_b : B) : Jl R :=
  .error (.overflowError "")

/--
Julia source: base/intfuncs.jl:68-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function absdiff(x::T,y::T) where {T<:Unsigned}
    d = max(x,y) - min(x,y)
    d, d
end
```
-/
def absdiff_Unsigned {U : Type} (max min sub : U → U → U) (x y : U) : U × U :=
  let d := sub (max x y) (min x y)
  (d, d)

/--
Julia source: base/intfuncs.jl:72-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function absdiff(x::T,y::T) where {T<:Signed}
    d = x - y
    abs(d), d
end
```
-/
def absdiff_Signed {S : Type} (sub : S → S → S) (abs : S → S) (x y : S) : S × S :=
  let d := sub x y
  (abs d, d)

def binaryGcdLoop {t : IntTy} : Nat → JInt t → JInt t → Nat → JInt t
  | 0, _, b, _ => b
  | n + 1, a, b, za =>
      if a.val = 0 then b else
        let a := JuliaLean.base.int.shr_Int a (JuliaLean.base.int.lit .i64 za)
        let (absd, d) := if t.signed then absdiff_Signed JuliaLean.base.int.sub JuliaLean.base.int.abs a b
          else absdiff_Unsigned maxBits minBits JuliaLean.base.int.sub a b
        let za := (JuliaLean.base.int.cttz_int d).val.toNat
        binaryGcdLoop n absd (minBits a b) za

/--
Julia source: base/intfuncs.jl:80-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_locally function _gcd(ain::T, bin::T) where T<:BitInteger
    zb = trailing_zeros(bin)
    za = trailing_zeros(ain)
    a = abs(ain)
    b = abs(bin >> zb)
    k = min(za, zb)
    while a != 0
        a >>= za
        absd, diff = absdiff(a, b)
        za = trailing_zeros(diff)
        b = min(a, b)
        a = absd
    end
    r = b << k
    return r % T
end
```
-/
def binaryGcd {t : IntTy} (ain bin : JInt t)
    (_nonzero : bin.val ≠ 0) (_firstNotMin : t.signed = true → ain.val ≠ t.min) : JInt t :=
  let zb := (JuliaLean.base.int.cttz_int bin).val.toNat
  let za := (JuliaLean.base.int.cttz_int ain).val.toNat
  let a := JuliaLean.base.int.abs ain
  let b := JuliaLean.base.int.abs (JuliaLean.base.int.shr_Int bin (JuliaLean.base.int.lit .i64 zb))
  let k := min za zb
  let b := binaryGcdLoop (ain.val.natAbs + bin.val.natAbs + 1) a b za
  let r := JuliaLean.base.int.shl_int b (JuliaLean.base.int.lit .i64 k)
  JuliaLean.base.int.remT t r

/--
Julia source: base/intfuncs.jl:53-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcd(a::T, b::T) where T<:BitInteger
    a == 0 && return Base.checked_abs(b)
    b == 0 && return Base.checked_abs(a)
    if a isa Signed && a == typemin(T)
        if a == b
            Base.__throw_gcd_overflow(a, b)
        else
            a, b = b, a
        end
    end
    return _gcd(a, b)
end
```
-/
def gcd_BitInteger {t : IntTy} (a b : JInt t) : Jl (JInt t) := do
  if ha : a.val = 0 then JuliaLean.base.checked.checkedAbsBits b
  else if hb : b.val = 0 then JuliaLean.base.checked.checkedAbsBits a
  else if hm : t.signed = true ∧ a.val = t.min then
    if he : a.val = b.val then throwGcdOverflow a b
    else pure (binaryGcd b a ha (by intro _ h; exact he (hm.2.trans h.symm)))
  else pure (binaryGcd a b hb (by intro hs h; exact hm ⟨hs, h⟩))

/--
Julia source: base/intfuncs.jl:136-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lcm(a::T, b::T) where T<:Integer
    # explicit a==0 test is to handle case of lcm(0, 0) correctly
    # explicit b==0 test is to handle case of lcm(typemin(T),0) correctly
    if a == 0 || b == 0
        return zero(a)
    else
        return checked_abs(checked_mul(a, div(b, gcd(b,a))))
    end
end
```
-/
def lcm_Integer {I : Type} (o : IntegerOps I) (gcd : I → I → Jl I) (a b : I) : Jl I := do
  if o.value a = 0 ∨ o.value b = 0 then pure (o.ofInt 0)
  else
    let d ← gcd b a
    let q ← o.div b d
    let product ← o.checkedMul a q
    o.checkedAbs product

/--
Julia source: base/intfuncs.jl:146-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote_mixed_signs(a::Signed, b::Unsigned)
    # handle the case a == typemin(typeof(a)) if R != typeof(a)
    R = promote_typeof(a, b)
    promote(abs(a % signed(R)), b)
end
```
-/
def promoteMixedSigns {S U R SR : Type} (remSigned : S → SR) (abs : SR → SR)
    (promote : SR → U → Jl (R × R)) (a : S) (b : U) : Jl (R × R) :=
  promote (abs (remSigned a)) b

/--
Julia source: base/intfuncs.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::Integer) = checked_abs(a)
```
-/
def gcd_Unary_Integer {I : Type} (checkedAbs : I → Jl I) (a : I) : Jl I := checkedAbs a

/--
Julia source: base/intfuncs.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::Rational) = checked_abs(a.num) // a.den
```
-/
def gcd_Unary_Rational {I R : Type} (num den : R → I) (checkedAbs : I → Jl I)
    (ratio : I → I → Jl R) (a : R) : Jl R := do
  let numerator ← checkedAbs (num a)
  ratio numerator (den a)

/--
Julia source: base/intfuncs.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm(a::Union{Integer,Rational}) = gcd(a)
```
-/
def lcm_Unary {R : Type} (gcd : R → Jl R) (a : R) : Jl R := gcd a

/--
Julia source: base/intfuncs.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::Unsigned, b::Signed) = gcd(b, a)
```
-/
def gcd_Unsigned_Signed {S U R : Type} (gcd : S → U → Jl R) (a : U) (b : S) : Jl R := gcd b a

/--
Julia source: base/intfuncs.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::Signed, b::Unsigned) = gcd(_promote_mixed_signs(a, b)...)
```
-/
def gcd_Signed_Unsigned {S U R : Type} (promote : S → U → Jl (R × R))
    (gcd : R → R → Jl R) (a : S) (b : U) : Jl R := do
  let (a, b) ← promote a b
  gcd a b

/--
Julia source: base/intfuncs.jl:157-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm(a::Unsigned, b::Signed) = lcm(promote(a, abs(b))...)
```
-/
def lcm_Unsigned_Signed {S U R : Type} (abs : S → S) (promote : U → S → Jl (R × R))
    (lcm : R → R → Jl R) (a : U) (b : S) : Jl R := do
  let (a, b) ← promote a (abs b)
  lcm a b

/--
Julia source: base/intfuncs.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm(a::Signed, b::Unsigned) = lcm(_promote_mixed_signs(a, b)...)
```
-/
def lcm_Signed_Unsigned {S U R : Type} (promote : S → U → Jl (R × R))
    (lcm : R → R → Jl R) (a : S) (b : U) : Jl R := do
  let (a, b) ← promote a b
  lcm a b

/--
Julia source: base/intfuncs.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::Real, b::Real) = gcd(promote(a,b)...)
```
-/
def gcd_Real {A B R : Type} (promote : A → B → Jl (R × R))
    (callee : R → R → Jl (R)) (a : A) (b : B) : Jl (R) := do
  let (a, b) ← promote a b
  callee a b

/--
Julia source: base/intfuncs.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm(a::Real, b::Real) = lcm(promote(a,b)...)
```
-/
def lcm_Real {A B R : Type} (promote : A → B → Jl (R × R))
    (callee : R → R → Jl (R)) (a : A) (b : B) : Jl (R) := do
  let (a, b) ← promote a b
  callee a b

/--
Julia source: base/intfuncs.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
```
-/
def gcd_Nary {R : Type} (gcd : R → R → Jl R) (unary : R → Jl R)
    (a b : R) (cs : List R) : Jl R := do
  let tail ← match cs with
    | [] => unary b
    | [c] => gcd b c
    | c :: d :: ds => gcd_Nary gcd unary b c (d :: ds)
  gcd a tail

/--
Julia source: base/intfuncs.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
```
-/
def lcm_Nary {R : Type} (lcm : R → R → Jl R) (unary : R → Jl R)
    (a b : R) (cs : List R) : Jl R := do
  let tail ← match cs with
    | [] => unary b
    | [c] => lcm b c
    | c :: d :: ds => lcm_Nary lcm unary b c (d :: ds)
  lcm a tail

/--
Julia source: base/intfuncs.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(a::T, b::T) where T<:Real = throw(MethodError(gcd, (a,b)))
```
-/
def gcd_NoMethod {R A : Type} (_a _b : R) : Jl A := .error (.methodError "gcd")

/--
Julia source: base/intfuncs.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm(a::T, b::T) where T<:Real = throw(MethodError(lcm, (a,b)))
```
-/
def lcm_NoMethod {R A : Type} (_a _b : R) : Jl A := .error (.methodError "lcm")

structure ArrayReduceCallees (A R : Type) where
  withInit : (R → R → Jl R) → A → R → Jl R
  withoutInit : (R → R → Jl R) → A → Jl R

structure GcdArrayCallees (A R : Type) where
  reduce : ArrayReduceCallees A R
  gcd : R → R → Jl R
  zero : R

structure LcmArrayCallees (A R : Type) where
  length : A → Nat
  isInteger : Bool
  one : R
  elementType : String
  abs : R → Jl R
  only : A → Jl R
  reduce : ArrayReduceCallees A R
  lcm : R → R → Jl R

/--
Julia source: base/intfuncs.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcd(abc::AbstractArray{<:Real}) = reduce(gcd, abc; init=zero(eltype(abc)))
```
-/
def gcd_Array_Real {A R : Type} (c : GcdArrayCallees A R) (abc : A) : Jl R :=
  c.reduce.withInit c.gcd abc c.zero

/--
Julia source: base/intfuncs.jl:167-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lcm(abc::AbstractArray{<:Real})
    # Using reduce with init=one(eltype(abc)) is buggy for Rationals.
    l = length(abc)
    if l == 0
        eltype(abc) <: Integer && return one(eltype(abc))
        throw(ArgumentError("lcm has no identity for $(eltype(abc))"))
    end
    l == 1 && return abs(only(abc))
    return reduce(lcm, abc)
end
```
-/
def lcm_Array_Real {A R : Type} (c : LcmArrayCallees A R) (abc : A) : Jl R := do
  let l := c.length abc
  if l = 0 then
    if c.isInteger then pure c.one else .error (.argumentError ("lcm has no identity for " ++ c.elementType))
  else if l = 1 then c.abs (← c.only abc)
  else c.reduce.withoutInit c.lcm abc

/--
Julia source: base/intfuncs.jl:178-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcd(abc::AbstractArray{<:Integer})
    a = zero(eltype(abc))
    for b in abc
        a = gcd(a, b)
        if a == 1
            return a
        end
    end
    return a
end
```
-/
def gcd_Array_Integer {I : Type} (o : IntegerOps I) (gcd : I → I → Jl I) (abc : List I) : Jl I :=
  let rec loop (a : I) : List I → Jl I
    | [] => pure a
    | b :: bs => do
        let a ← gcd a b
        if o.value a = 1 then pure a else loop a bs
  loop (o.ofInt 0) abc

/--
Julia source: base/intfuncs.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
```
-/
def gcdxUpdate_Unsigned {U : Type} (subWrap mulWrap : U → U → U) (s0 q s1 : U) : U :=
  subWrap s0 (mulWrap q s1)

/--
Julia source: base/intfuncs.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_gcdx_update(s0, q, s1) = s0 - q*s1
```
-/
def gcdxUpdate {I : Type} (sub mul : I → I → I) (s0 q s1 : I) : I := sub s0 (mul q s1)

def gcdxLoop {I : Type} (o : IntegerOps I) : Nat → I → I → I → I → I → I →
    Jl (I × I × I)
  | 0, a, _b, s0, _, t0, _ =>
      if o.value a < 0 ∧ o.value (o.abs a) < 0 then .error (.domainError "")
      else .ok (if o.value a < 0 then (o.abs a, o.neg s0, o.neg t0) else (a, s0, t0))
  | n + 1, a, b, s0, s1, t0, t1 => do
      if o.value b = 0 then
        if o.value a < 0 ∧ o.value (o.abs a) < 0 then .error (.domainError "")
        else pure (if o.value a < 0 then (o.abs a, o.neg s0, o.neg t0) else (a, s0, t0))
      else
        let (q, r) ← o.divrem a b
        let update := if o.unsigned then gcdxUpdate_Unsigned o.sub o.mul else gcdxUpdate o.sub o.mul
        gcdxLoop o n b r s1 (update s0 q s1) t1 (update t0 q t1)

/--
Julia source: base/intfuncs.jl:235-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :terminates_locally function gcdx(a::T, b::T) where {T<:Integer}
    if iszero(a) && iszero(b)
        return (zero(T), zero(T), zero(T))
    elseif isone(abs(b))
        # handles (typemin(::Signed), -1)
        return (one(T), zero(T), b)
    elseif isone(abs(a))
        return (one(T), a, zero(T))
    end
    # a0, b0 = a, b
    s0, s1 = oneunit(T), zero(T)
    t0, t1 = s1, s0
    # The loop invariant is: s0*a0 + t0*b0 == a && s1*a0 + t1*b0 == b
    while !iszero(b)
        q, r = divrem(a, b)
        a, b = b, r
        s0, s1 = s1, _gcdx_update(s0, q, s1)
        t0, t1 = t1, _gcdx_update(t0, q, t1)
    end
    # for cases like abs(Int8(-128))
    if isnegative(a) && isnegative(abs(a))
        throw(DomainError((a, b), LazyString("gcd not representable in ", T)))
    else
        return isnegative(a) ? (abs(a), -s0, -t0) : (a, s0, t0)
    end
end
```
-/
def gcdx_Integer {I : Type} (o : IntegerOps I) (a b : I) : Jl (I × I × I) :=
  if o.value a = 0 ∧ o.value b = 0 then pure (o.ofInt 0, o.ofInt 0, o.ofInt 0)
  else if o.value (o.abs b) = 1 then pure (o.ofInt 1, o.ofInt 0, b)
  else if o.value (o.abs a) = 1 then pure (o.ofInt 1, a, o.ofInt 0)
  else gcdxLoop o (magnitude o b + 1) a b (o.ofInt 1) (o.ofInt 0) (o.ofInt 0) (o.ofInt 1)

/--
Julia source: base/intfuncs.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcdx(a::Real, b::Real) = gcdx(promote(a,b)...)
```
-/
def gcdx_Real {A B R : Type} (promote : A → B → Jl (R × R))
    (callee : R → R → Jl (R × R × R)) (a : A) (b : B) : Jl (R × R × R) := do
  let (a, b) ← promote a b
  callee a b

/--
Julia source: base/intfuncs.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcdx(a::T, b::T) where T<:Real = throw(MethodError(gcdx, (a,b)))
```
-/
def gcdx_NoMethod {R A : Type} (_a _b : R) : Jl A := .error (.methodError "gcdx")

/--
Julia source: base/intfuncs.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gcdx(a::Real) = (gcd(a), signbit(a) ? -one(a) : one(a))
```
-/
def gcdx_Unary {R : Type} (gcd : R → Jl R) (signbit : R → Bool)
    (one : R → R) (neg : R → R) (a : R) : Jl (R × R) := do
  let d ← gcd a
  pure (d, if signbit a then neg (one a) else one a)

def gcdxUnary {R : Type} (gcd : R → Jl R) (signbit : R → Bool)
    (one : R → Jl R) (neg : R → Jl R) (a : R) : Jl (R × R) := do
  let d ← gcd a
  let coefficient ← if signbit a then do neg (← one a) else one a
  pure (d, coefficient)

/--
Julia source: base/intfuncs.jl:264-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcdx(a::Real, b::Real, cs::Real...)
    # a solution to the 3-arg `gcdx(a,b,c)` problem, `u*a + v*b + w*c = gcd(a,b,c)`, can be
    # obtained from the 2-arg problem in three steps:
    #   1. `gcdx(a,b)`: solve `i*a + j*b = d′ = gcd(a,b)` for `(i,j)`
    #   2. `gcdx(d′,c)`: solve `x*gcd(a,b) + yc = gcd(gcd(a,b),c) = gcd(a,b,c)` for `(x,y)`
    #   3. return `d = gcd(a,b,c)`, `u = i*x`, `v = j*x`, and `w = y`
    # the N-arg solution proceeds similarly by recursion
    d, i, j = gcdx(a, b)
    d′, x, ys... = gcdx(d, cs...)
    return d′, i*x, j*x, ys...
end
```
-/
def gcdx_Nary {R : Type} (gcdx : R → R → Jl (R × R × R))
    (unary : R → Jl (R × R)) (mul : R → R → R) (a b : R) (cs : List R) : Jl (R × R × R × List R) := do
  let (d, i, j) ← gcdx a b
  match cs with
  | [] =>
      let (d', x) ← unary d
      pure (d', mul i x, mul j x, [])
  | [c] =>
      let (d', x, y) ← gcdx d c
      pure (d', mul i x, mul j x, [y])
  | c :: next :: ds =>
      let (d', x, y, ys) ← gcdx_Nary gcdx unary mul d c (next :: ds)
      pure (d', mul i x, mul j x, y :: ys)

def gcdxNary {R C : Type} (gcdx : R → R → Jl (R × C × C))
    (unary : R → Jl (R × C)) (mul : C → C → Jl C)
    (a b : R) (cs : List R) : Jl (R × C × C × List C) := do
  let (d, i, j) ← gcdx a b
  match cs with
  | [] =>
      let (d', x) ← unary d
      let u ← mul i x
      let v ← mul j x
      pure (d', u, v, [])
  | [c] =>
      let (d', x, y) ← gcdx d c
      let u ← mul i x
      let v ← mul j x
      pure (d', u, v, [y])
  | c :: next :: ds =>
      let (d', x, y, ys) ← gcdxNary gcdx unary mul d c (next :: ds)
      let u ← mul i x
      let v ← mul j x
      pure (d', u, v, y :: ys)

/--
Julia source: base/intfuncs.jl:276-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcdx(a::Signed, b::Unsigned)
    R = promote_typeof(a, b)
    d, u, v = gcdx(promote(abs(a % signed(R)), b)...)
    flip_typemin = isnegative(a) & (R <: Signed)
    d, flipsign(u, a -% oftype(a, flip_typemin)), v
end
```
-/
def gcdx_Signed_Unsigned {S U R : Type} (promote : S → U → Jl (R × R))
    (gcdx : R → R → Jl (R × R × R)) (isnegative : S → Bool) (resultSigned : Bool)
    (subWrap : S → S → S) (ofBool : Bool → S) (flipsign : R → S → R)
    (a : S) (b : U) : Jl (R × R × R) := do
  let (a', b') ← promote a b
  let (d, u, v) ← gcdx a' b'
  let flipTypemin := isnegative a && resultSigned
  pure (d, flipsign u (subWrap a (ofBool flipTypemin)), v)

/--
Julia source: base/intfuncs.jl:282-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcdx(a::Unsigned, b::Signed)
    d, v, u = gcdx(b, a)
    d, u, v
end
```
-/
def gcdx_Unsigned_Signed {S U R : Type} (gcdx : S → U → Jl (R × R × R))
    (a : U) (b : S) : Jl (R × R × R) := do
  let (d, v, u) ← gcdx b a
  pure (d, u, v)

/--
Julia source: base/intfuncs.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invmod(n::Integer, ::Type{T}) where {T<:BitInteger} = invmod(n % T)
```
-/
def invmod_Type {I : Type} {t : IntTy} (rem : I → JInt t) (invmod : JInt t → Jl (JInt t)) (n : I) :
    Jl (JInt t) := invmod (rem n)

/--
Julia source: base/intfuncs.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invmod(n, ::Type{Union{}}, slurp...) = throw(MethodError(invmod, (n, Union{}, slurp...)))
```
-/
def invmod_Bottom {N Tail R : Type} (_n : N) (_slurp : Tail) : Jl R :=
  .error (.methodError "invmod")

/--
Julia source: base/intfuncs.jl:373-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invmod(n::T) where {T<:BitInteger}
    isodd(n) || throw(DomainError(n, "Argument must be odd."))
    x = (3 *% n ⊻ 2) % T
    y = (one(T) -% n *% x) % T
    for _ = 1:trailing_zeros(2*sizeof(T))
        x = x *% (y +% one(T))
        y = y *% y
    end
    return x
end
```
-/
def invmod_Ring {t : IntTy} (n : JInt t) : Jl (JInt t) :=
  if n.val % 2 = 0 then .error (.domainError "") else
    let promoted := IntTy.promote .i64 t
    let xn := JuliaLean.base.int.mul (JuliaLean.base.int.lit promoted 3) (JuliaLean.base.int.remT promoted n)
    let x := JuliaLean.base.int.remT t (JuliaLean.base.int.xor_int xn (JuliaLean.base.int.lit promoted 2))
    let y := JuliaLean.base.int.sub (JuliaLean.base.int.lit t 1) (JuliaLean.base.int.mul n x)
    let iterations := (JuliaLean.base.int.cttz_int (JuliaLean.base.int.lit .i64 (2 * (t.bits / 8)))).val.toNat
    pure (((List.range iterations).foldl (fun (s : JInt t × JInt t) _ =>
      (JuliaLean.base.int.mul s.1 (JuliaLean.base.int.add s.2 (JuliaLean.base.int.lit t 1)), JuliaLean.base.int.mul s.2 s.2)) (x, y)).1)

/--
Julia source: base/intfuncs.jl:385-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_domerr_powbysq(::Any, p) = throw(DomainError(p, LazyString(
    "Cannot raise an integer x to a negative power ", p, ".",
    "\nConvert input to float.")))
```
-/
def throwPowerDomain_Any {A P R : Type} (_x : A) (_p : P) : Jl R := .error (.domainError "")

/--
Julia source: base/intfuncs.jl:388-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_domerr_powbysq(::Integer, p) = throw(DomainError(p, LazyString(
    "Cannot raise an integer x to a negative power ", p, ".",
    "\nMake x or ", p, " a float by adding a zero decimal ",
    "(e.g., 2.0^", p, " or 2^", float(p), " instead of 2^", p, ") ",
    "or write 1/x^", -p, ", float(x)^", p, ", x^float(", p, ") or (x//1)^", p, ".")))
```
-/
def throwPowerDomain_Integer {A P R : Type} (_x : A) (_p : P) : Jl R := .error (.domainError "")

/--
Julia source: base/intfuncs.jl:393-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_domerr_powbysq(::AbstractMatrix, p) = throw(DomainError(p, LazyString(
    "Cannot raise an integer matrix x to a negative power ", p, ".",
    "\nMake x a float matrix by adding a zero decimal ",
    "(e.g., [2.0 1.0;1.0 0.0]^", p, " instead of [2 1;1 0]^", p, ") ",
    "or write float(x)^", p, " or Rational.(x)^", p, ".")))
```
-/
def throwPowerDomain_Matrix {A P R : Type} (_x : A) (_p : P) : Jl R := .error (.domainError "")

/--
Julia source: base/intfuncs.jl:399-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_locally function power_by_squaring(x_, p::Integer; mul=*)
    x_squared_ = x_ * x_
    x_squared_type = typeof(x_squared_)
    T = if x_ isa Number
        promote_type(typeof(x_), x_squared_type)
    else
        x_squared_type
    end
    x = convert(T, x_)
    square_is_useful = mul === *
    if p == 1
        return copy(x)
    elseif p == 0
        return one(x)
    elseif p == 2
        if square_is_useful  # avoid performing the same multiplication a second time when possible
            return convert(T, x_squared_)
        end
        return mul(x, x)
    elseif p < 0
        isone(x) && return copy(x)
        isone(-x) && return iseven(p) ? one(x) : copy(x)
        throw_domerr_powbysq(x, p)
    end
    t = trailing_zeros(p) + 1
    p >>= t
    if square_is_useful  # avoid performing the same multiplication a second time when possible
        if (t -= 1) > 0
            x = convert(T, x_squared_)
        end
    end
    while (t -= 1) > 0
        x = mul(x, x)
    end
    y = x
    while p > 0
        t = trailing_zeros(p) + 1
        p >>= t
        while (t -= 1) >= 0
            x = mul(x, x)
        end
        y = mul(y, x)
    end
    return y
end
```
-/
def powerBySquaring {A S T E : Type} (eo : IntegerOps E)
    (square : A → A → Jl S) (isNumber : Bool) (convertNumber convertOther : A → Jl T)
    (convertSquare : S → Jl T) (copy : T → T) (one : T → T) (neg : T → Jl T)
    (isone : T → Bool) (mul : T → T → Jl T) (squareUseful : Bool)
    (x_ : A) (p : E) (throwDomerr : T → E → Jl T := throwPowerDomain_Integer) : Jl T := do
  let xSquared ← square x_ x_
  let x ← if isNumber then convertNumber x_ else convertOther x_
  if eo.value p = 1 then pure (copy x)
  else if eo.value p = 0 then pure (one x)
  else if eo.value p = 2 then
    if squareUseful then convertSquare xSquared else mul x x
  else if eo.value p < 0 then
    if isone x then pure (copy x)
    else
      let negX ← neg x
      if isone negX then pure (if eo.value p % 2 = 0 then one x else copy x)
      else throwDomerr x p
  else
    let t := eo.trailingZeros p + 1
    let p := eo.shiftRight p t
    let (x, t) ← if squareUseful then
        if t > 1 then do
          let x ← convertSquare xSquared
          pure (x, t - 1)
        else pure (x, t - 1)
      else pure (x, t)
    let x ← powerSquares mul (t - 1) x
    powerLoop eo mul (eo.value p).natAbs x x p

/--
Julia source: base/intfuncs.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
power_by_squaring(x::Bool, p::Unsigned) = ((p==0) | x)
```
-/
def powerBool_Unsigned {U : Type} (iszero : U → Bool) (x : Bool) (p : U) : Bool := iszero p || x

/--
Julia source: base/intfuncs.jl:445-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function power_by_squaring(x::Bool, p::Integer)
    p < 0 && !x && throw_domerr_powbysq(x, p)
    return (p==0) | x
end
```
-/
def powerBool_Integer {I : Type} (value : I → Int) (x : Bool) (p : I) : Jl Bool := do
  if value p < 0 ∧ !x then throwPowerDomain_Integer x p
  else pure (decide (value p = 0) || x)

/--
Julia source: base/intfuncs.jl:450-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::T, p::T) where {T<:Integer} = power_by_squaring(x,p)
```
-/
def pow_Integer {I : Type} (power : I → I → Jl I) (x p : I) : Jl I := power x p

/--
Julia source: base/intfuncs.jl:451-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::Number, p::Integer)  = power_by_squaring(x,p)
```
-/
def pow_Number {N I R : Type} (power : N → I → Jl R) (x : N) (p : I) : Jl R := power x p

/--
Julia source: base/intfuncs.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(f, x, ::Val{p}) where {p} = f(x,p)
```
-/
def literalPow {A P R : Type} (f : A → P → Jl R) (x : A) (p : P) : Jl R := f x p

/--
Julia source: base/intfuncs.jl:470-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::HWNumber, ::Val{0}) = one(x)
```
-/
def literalPow_Zero {N : Type} (one : N → N) (x : N) : N := one x

/--
Julia source: base/intfuncs.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::HWNumber, ::Val{1}) = x
```
-/
def literalPow_One {N : Type} (x : N) : N := x

/--
Julia source: base/intfuncs.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::HWNumber, ::Val{2}) = x*x
```
-/
def literalPow_Two {N : Type} (mul : N → N → Jl N) (x : N) : Jl N := mul x x

/--
Julia source: base/intfuncs.jl:473-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::HWNumber, ::Val{3}) = x*x*x
```
-/
def literalPow_Three {N : Type} (mul : N → N → Jl N) (x : N) : Jl N := do
  let square ← mul x x
  mul square x

/--
Julia source: base/intfuncs.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::HWNumber, ::Val{-1}) = inv(x)
```
-/
def literalPow_NegOne {N R : Type} (inv : N → Jl R) (x : N) : Jl R := inv x

/--
Julia source: base/intfuncs.jl:475-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::HWNumber, ::Val{-2}) = (i=inv(x); i*i)
```
-/
def literalPow_NegTwo {N R : Type} (inv : N → Jl R) (mul : R → R → Jl R) (x : N) : Jl R := do
  let i ← inv x
  mul i i

/--
Julia source: base/intfuncs.jl:478-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::AbstractFloat, ::Val{p}) where {p} = x^p
```
-/
def literalPow_Float {F R : Type} (pow : F → Int → Jl R) (x : F) (p : Int) : Jl R := pow x p

/--
Julia source: base/intfuncs.jl:479-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline literal_pow(::typeof(^), x::AbstractFloat, ::Val{-1}) = inv(x)
```
-/
def literalPow_Float_NegOne {F : Type} (inv : F → Jl F) (x : F) : Jl F := inv x

/--
Julia source: base/intfuncs.jl:483-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function literal_pow(f::typeof(^), x, ::Val{p}) where {p}
    if p < 0
        if x isa BitInteger64
            f(Float64(x), p) # inv would cause rounding, while Float64^Integer is able to compensate the inverse
        else
            f(inv(x), -p)
        end
    else
        f(x, p)
    end
end
```
-/
def literalPow_Generic {A F V R : Type} (isBitInteger64 : Bool) (toFloat : A → Jl F)
    (inv : A → Jl V) (powA : A → Int → Jl R) (powFloat : F → Int → Jl R)
    (powInverse : V → Int → Jl R) (x : A) (p : Int) : Jl R := do
  if p < 0 then
    if isBitInteger64 then powFloat (← toFloat x) p
    else powInverse (← inv x) (-p)
  else powA x p

/--
Julia source: base/intfuncs.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
powermod(x::Integer, p::Integer, m::Union{Int128,UInt128}) = oftype(m, powermod(x, p, big(m)))
```
-/
def powermod_128 {X P B : Type} {t : IntTy} (big : JInt t → B)
    (powermod : X → P → B → Jl B) (oftype : B → Jl (JInt t))
    (x : X) (p : P) (m : JInt t) : Jl (JInt t) := do
  oftype (← powermod x p (big m))

/--
Julia source: base/intfuncs.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
```
-/
def nextpow2_Unsigned {U : Type} (oneunit : U → U) (sub : U → U → U)
    (topBit : U → Nat) (shl : U → Nat → U) (x : U) : U :=
  shl (oneunit x) (topBit (sub x (oneunit x)))

/--
Julia source: base/intfuncs.jl:590-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
```
-/
def nextpow2_Integer {I U : Type} (value : I → Int) (negI : I → I)
    (unsigned : I → U) (negU : U → U) (nextpow2 : U → U) (reinterpret : U → I) (x : I) : I :=
  reinterpret (if value x < 0 then negU (nextpow2 (unsigned (negI x))) else nextpow2 (unsigned x))

/--
Julia source: base/intfuncs.jl:591-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
```
-/
def prevpow2_Unsigned {U : Type} (one : U → U) (topBit : U → Int)
    (unsigned : Int → Nat) (shl : U → Nat → U) (x : U) : U :=
  shl (one x) (unsigned (topBit x - 1))

/--
Julia source: base/intfuncs.jl:592-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
```
-/
def prevpow2_Integer {I U : Type} (value : I → Int) (negI : I → I)
    (unsigned : I → U) (negU : U → U) (prevpow2 : U → U) (reinterpret : U → I) (x : I) : I :=
  reinterpret (if value x < 0 then negU (prevpow2 (unsigned (negI x))) else prevpow2 (unsigned x))

/--
Julia source: base/intfuncs.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispow2(x::Number) = isreal(x) && ispow2(real(x))
```
-/
def ispow2_Number {N R : Type} (isreal : N → Bool) (real : N → R) (ispow2 : R → Bool) (x : N) : Bool :=
  isreal x && ispow2 (real x)

/--
Julia source: base/intfuncs.jl:624-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispow2(x::Integer) = x > 0 && count_ones(x) == 1
```
-/
def ispow2_Integer {I : Type} (value : I → Int) (countOnes : I → Nat) (x : I) : Bool :=
  decide (value x > 0) && countOnes x == 1

/--
Julia source: base/intfuncs.jl:649-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nextpow(a::Real, x::Real)
    x <= 0 && throw(DomainError(x, "`x` must be positive."))
    # Special case fast path for x::Integer, a == 2.
    # This is a very common case. Constant prop will make sure that a call site
    # specified as `nextpow(2, x)` will get this special case inlined.
    a == 2 && isa(x, Integer) && return _nextpow2(x)
    a <= 1 && throw(DomainError(a, "`a` must be greater than 1."))
    x <= 1 && return one(a)
    n = ceil(Integer,log(a, x))
    # round-off error of log can go either direction, so need some checks
    p = a^(n-1)
    hastypemax(typeof(p)) && x > typemax(p) &&
        throw(DomainError(x,"argument is beyond the range of type of the base"))
    p >= x && return p
    wp = a^n
    wp > p || throw(OverflowError("result is beyond the range of type of the base"))
    wp >= x && return wp
    wwp = a^(n+1)
    wwp > wp || throw(OverflowError("result is beyond the range of type of the base"))
    return wwp
end
```
-/
def nextpow {A X R : Type} (xNonpos : X → Bool) (aTwo : A → Bool) (xInteger : Bool)
    (fast : X → Jl R) (aSmall : A → Bool) (xAtMostOne : X → Bool) (one : A → R)
    (ceilLog : A → X → Jl Int) (pow : A → Int → Jl R) (hasMax : R → Bool)
    (beyondMax : X → R → Bool) (ge : R → X → Bool) (gt : R → R → Bool)
    (a : A) (x : X) : Jl R := do
  if xNonpos x then .error (.domainError "")
  else if aTwo a && xInteger then fast x
  else if aSmall a then .error (.domainError "")
  else if xAtMostOne x then pure (one a)
  else
    let n ← ceilLog a x
    let p ← pow a (n - 1)
    if hasMax p && beyondMax x p then .error (.domainError "")
    else if ge p x then pure p else
      let wp ← pow a n
      if !gt wp p then .error (.overflowError "")
      else if ge wp x then pure wp else
        let wwp ← pow a (n + 1)
        if !gt wwp wp then .error (.overflowError "") else pure wwp

/--
Julia source: base/intfuncs.jl:694-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prevpow(a::T, x::Real) where T <: Real
    x < 1 && throw(DomainError(x, "`x` must be ≥ 1."))
    # See comment in nextpow() for a == special case.
    a == 2 && isa(x, Integer) && return _prevpow2(x)
    a <= 1 && throw(DomainError(a, "`a` must be greater than 1."))
    n = floor(Integer,log(a, x))
    # round-off error of log can go either direction, so need some checks
    p = a^n
    hastypemax(typeof(p)) && x > typemax(p) &&
        throw(DomainError(x,"argument is beyond the range of type of the base"))
    if a isa Integer
        wp, overflow = mul_with_overflow(promote(a, p)...)
        wp <= x && !overflow && return wp
    else
        wp = a^(n+1)
        wp <= x && return wp
    end
    p <= x && return p
    return a^(n-1)
end
```
-/
def prevpow {A X R : Type} (xBelowOne : X → Bool) (aTwo : A → Bool) (xInteger : Bool)
    (fast : X → Jl R) (aSmall : A → Bool) (floorLog : A → X → Jl Int)
    (pow : A → Int → Jl R) (hasMax : R → Bool) (beyondMax : X → R → Bool)
    (aInteger : Bool) (mulWithOverflow : A → R → Jl (R × Bool)) (le : R → X → Bool)
    (a : A) (x : X) : Jl R := do
  if xBelowOne x then .error (.domainError "")
  else if aTwo a && xInteger then fast x
  else if aSmall a then .error (.domainError "") else
    let n ← floorLog a x
    let p ← pow a n
    if hasMax p && beyondMax x p then .error (.domainError "") else
      let wp ← if aInteger then do
          let (wp, overflow) ← mulWithOverflow a p
          pure (wp, le wp x && !overflow)
        else do
          let wp ← pow a (n + 1)
          pure (wp, le wp x)
      if wp.2 then pure wp.1 else if le p x then pure p else pow a (n - 1)

/--
Julia source: base/intfuncs.jl:725-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bit_ndigits0z(x::Base.BitUnsigned64)
    lz = top_set_bit(x)
    nd = (1233*lz)>>12+1
    return nd - (x < powers_of_ten[nd])
end
```
-/
def bitNdigits64 {t : IntTy} (x : JInt t) (_unsigned : t.signed = false) (_width : t.bits ≤ 64) : Jl JInt64 := do
  let lz := JuliaLean.base.int.lit .i64 (topBit x)
  let nd := JuliaLean.base.int.add (JuliaLean.base.int.ashr_int (JuliaLean.base.int.mul (JuliaLean.base.int.lit .i64 1233) lz) (JuliaLean.base.int.lit .i64 12)) (JuliaLean.base.int.lit .i64 1)
  if nd.val < 1 then .error .boundsError else
    match powersOfTen[(nd.val - 1).toNat]? with
    | none => .error .boundsError
    | some power => pure (JuliaLean.base.int.sub nd (JuliaLean.base.int.lit .i64 (if x.val < power.val then 1 else 0)))

/--
Julia source: base/intfuncs.jl:730-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bit_ndigits0z(x::UInt128)
    n = 0
    while x > 0x8ac7230489e80000 # 10e18
        x = div(x,0x8ac7230489e80000)
        n += 19
    end
    return n + ndigits0z(UInt64(x))
end
```
-/
def bitNdigits128 (decimal64 : JInt .u64 → Jl JInt64) (div : JInt .u128 → JInt .u128 → Jl (JInt .u128))
    (x : JInt .u128) : Jl JInt64 := do
  let step := fun (s : JInt .u128 × JInt64) => do
    if s.1.val > 10000000000000000000 then
      pure (← div s.1 (JuliaLean.base.int.lit .u128 10000000000000000000), JuliaLean.base.int.add s.2 (JuliaLean.base.int.lit .i64 19))
    else pure s
  let (x, n) ← repeatM (x.val.natAbs + 1) step (x, JuliaLean.base.int.lit .i64 0)
  pure (JuliaLean.base.int.add n (← decimal64 (JuliaLean.base.int.remT .u64 x)))

/--
Julia source: base/intfuncs.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndigits0z(x::BitSigned) = bit_ndigits0z(unsigned(abs(x)))
```
-/
def ndigitsDecimal_Signed {S U : Type} (abs : S → S) (unsigned : S → U)
    (decimal : U → Jl JInt64) (x : S) : Jl JInt64 := decimal (unsigned (abs x))

/--
Julia source: base/intfuncs.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndigits0z(x::BitUnsigned) = bit_ndigits0z(x)
```
-/
def ndigitsDecimal_Unsigned {U : Type} (decimal : U → Jl JInt64) (x : U) : Jl JInt64 := decimal x

/--
Julia source: base/intfuncs.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndigits0z(x::Integer) = ndigits0zpb(x, 10)
```
-/
def ndigitsDecimal_Integer {I B : Type} (ten : B) (positive : I → B → Jl JInt64) (x : I) :
    Jl JInt64 := positive x ten

/--
Julia source: base/intfuncs.jl:746-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ndigits0znb(x::Integer, b::Integer)
    d = 0
    if x isa Unsigned
        d += (x != 0)::Bool
        x = -signed(fld(x, -b))
    end
    # precondition: b < -1 && !(typeof(x) <: Unsigned)
    while x != 0
        x = cld(x,b)
        d += 1
    end
    return d
end
```
-/
def ndigitsNegative {I B S : Type} (value : I → Int) (isUnsigned : Bool)
    (negBase : B → B) (fld : I → B → Jl I) (signed : I → S) (neg : S → S)
    (lift : I → S) (signedValue : S → Int) (cld : S → B → Jl S) (x : I) (b : B) : Jl JInt64 := do
  let (x, d) ← if isUnsigned then do
      let q ← fld x (negBase b)
      pure (neg (signed q), JuliaLean.base.int.lit .i64 (if value x = 0 then 0 else 1))
    else pure (lift x, JuliaLean.base.int.lit .i64 0)
  let step := fun (s : S × JInt64) => do
    if signedValue s.1 = 0 then pure s else
      pure (← cld s.1 b, JuliaLean.base.int.add s.2 (JuliaLean.base.int.lit .i64 1))
  let (_, d) ← repeatM (2 * (signedValue x).natAbs + 3) step (x, d)
  pure d

/--
Julia source: base/intfuncs.jl:761-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndigits0znb(x::Bool, b::Integer) = x % Int
```
-/
def ndigitsNegative_Bool {B : Type} (x : Bool) (_b : B) : JInt64 := JuliaLean.base.int.ofBool .i64 x

/--
Julia source: base/intfuncs.jl:764-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ndigits0zpb(x::Integer, b::Integer)
    @constprop :aggressive
    # precondition: b > 1
    x == 0 && return 0
    b = Int(b)
    x = abs(x)
    if x isa Base.BitInteger
        x = unsigned(x)::Unsigned
        b == 2  && return top_set_bit(x)
        b == 8  && return (top_set_bit(x) + 2) ÷ 3
        b == 16 && return sizeof(x)<<1 - leading_zeros(x)>>2
        b == 10 && return bit_ndigits0z(x)
        if ispow2(b)
            dv, rm = divrem(top_set_bit(x), trailing_zeros(b))
            return iszero(rm) ? dv : dv + 1
        end
    end

    d = 0
    while x > typemax(Int)
        x = div(x,b)
        d += 1
    end
    x = div(x,b)
    d += 1

    m = 1
    while m <= x
        m *= b
        d += 1
    end
    return d
end
```
-/
def ndigitsPositive {I B X : Type} (value : I → Int) (toInt : B → Jl JInt64)
    (abs : I → I) (isBitInteger : Bool) (unsigned lift : I → X) (xvalue : X → Int)
    (topBit : X → Nat) (leadingZeros : X → Nat) (bytes : X → Nat)
    (decimal : X → Jl JInt64) (div : X → JInt64 → Jl X)
    (ispow2 : JInt64 → Bool) (trailingZeros : JInt64 → Nat) (x : I) (base : B) : Jl JInt64 := do
  if value x = 0 then pure (JuliaLean.base.int.lit .i64 0) else
    let b ← toInt base
    let x := abs x
    let x := if isBitInteger then unsigned x else lift x
    if isBitInteger && decide (b.val = 2) then pure (JuliaLean.base.int.lit .i64 (topBit x))
    else if isBitInteger && decide (b.val = 8) then pure (JuliaLean.base.int.lit .i64 ((topBit x + 2) / 3))
    else if isBitInteger && decide (b.val = 16) then
      pure (JuliaLean.base.int.lit .i64 (2 * (bytes x : Int) - (leadingZeros x / 4 : Nat)))
    else if isBitInteger && decide (b.val = 10) then decimal x
    else if isBitInteger && ispow2 b then
      let dv := topBit x / trailingZeros b
      let rm := topBit x % trailingZeros b
      pure (JuliaLean.base.int.lit .i64 (if rm = 0 then dv else dv + 1))
    else
      let step := fun (s : X × JInt64) => do
        if xvalue s.1 > IntTy.max .i64 then pure (← div s.1 b, JuliaLean.base.int.add s.2 (JuliaLean.base.int.lit .i64 1))
        else pure s
      let (x, d) ← repeatM ((xvalue x).natAbs + 1) step (x, JuliaLean.base.int.lit .i64 0)
      let x ← div x b
      let d := JuliaLean.base.int.add d (JuliaLean.base.int.lit .i64 1)
      let step := fun (s : JInt64 × JInt64) =>
        if s.1.val ≤ xvalue x then (JuliaLean.base.int.mul s.1 b, JuliaLean.base.int.add s.2 (JuliaLean.base.int.lit .i64 1)) else s
      pure ((List.range ((xvalue x).natAbs + 1)).foldl (fun s _ => step s) (JuliaLean.base.int.lit .i64 1, d)).2

/--
Julia source: base/intfuncs.jl:798-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndigits0zpb(x::Bool, b::Integer) = x % Int
```
-/
def ndigitsPositive_Bool {B : Type} (x : Bool) (_b : B) : JInt64 := JuliaLean.base.int.ofBool .i64 x

/--
Julia source: base/intfuncs.jl:829-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ndigits0z(x::Integer, b::Integer)
    @constprop :aggressive
    if b < -1
        ndigits0znb(x, b)
    elseif b > 1
        ndigits0zpb(x, b)
    else
        throw(DomainError(b, "The base must not be in `[-1, 0, 1]`."))
    end
end
```
-/
def ndigitsZero {I B : Type} (value : B → Int)
    (negative positive : I → B → Jl JInt64) (x : I) (b : B) : Jl JInt64 :=
  if value b < -1 then negative x b else if value b > 1 then positive x b
  else .error (.domainError "")

/--
Julia source: base/intfuncs.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
top_set_bit(x::Integer) = iszero(x) ? 0 : exponent(x) + 1
```
-/
def isfiniteReal {R N E D : Type} (decompose : R → N × E × D)
    (zero : D) (equal : D → D → Bool) (x : R) : Bool :=
  !(equal (decompose x).2.2 zero)

def topSetBitIntegerM {M : Type → Type} [Monad M] {I : Type}
    (iszero : I → Bool) (exponent : I → M Int) (x : I) : M Int := do
  if iszero x then pure 0 else pure ((← exponent x) + 1)

def topSetBit_Integer {I : Type} (iszero : I → Bool) (exponent : I → Jl Int) (x : I) : Jl Int :=
  if iszero x then pure 0 else do pure ((← exponent x) + 1)

abbrev FormatRun (A : Type) := ExceptT JlError Option A


def topSetBitBig (ops : JuliaLean.base.math.IntegerExponentOps Int Int) (n : Int) : FormatRun Int :=
  topSetBitIntegerM ops.iszero (JuliaLean.base.math.exponentInteger ops) n
def liftJl {A : Type} (result : Jl A) : FormatRun A := some result

/--
Julia source: base/intfuncs.jl:874-874 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndigits(x::Integer; base::Integer=10, pad::Integer=1) = max(pad, ndigits0z(x, base))
```
-/
def ndigits {I B P R : Type} (ndigitsZero : I → B → Jl JInt64)
    (max : P → JInt64 → Jl R) (x : I) (base : B) (pad : P) : Jl R := do
  max pad (← ndigitsZero x base)

/--
Julia source: base/intfuncs.jl:878-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bin(x::Unsigned, pad::Int, neg::Bool)
    m = top_set_bit(x)
    n = neg + max(pad, m)
    str = _string_n(n)
    GC.@preserve str begin
        p = pointer(str)
        i = n
        while i >= 4
            b = UInt32((x % UInt8)::UInt8)
            d = 0x30303030 +% ((b *% 0x08040201) >> 0x3) & 0x01010101
            unsafe_store!(p, (d >> 0x00) % UInt8, i-3)
            unsafe_store!(p, (d >> 0x08) % UInt8, i-2)
            unsafe_store!(p, (d >> 0x10) % UInt8, i-1)
            unsafe_store!(p, (d >> 0x18) % UInt8, i)
            x >>= 0x4
            i -= 4
        end
        while i > neg
            unsafe_store!(p, 0x30 + ((x % UInt8)::UInt8 & 0x1), i)
            x >>= 0x1
            i -= 1
        end
        neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
    end
    return str
end
```
-/
def bin {U : Type} (topBit : U → Nat) (lowByte : U → Nat) (shr : U → Nat → U)
    (x : U) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  let m : Int := topBit x
  let n := wrapInt .i64 (boolInt neg + max pad.val m)
  let str ← newBuffer n
  let (str, x, i) := binLoop4 lowByte shr (n.toNat / 4 + 1) str x n
  let str := binLoop1 lowByte shr neg (n.toNat + 1) str x i
  pure (minusSign neg str)

def binM {U : Type} (topBit : U → FormatRun Int) (lowByte : U → Nat)
    (shr : U → Nat → U) (x : U) (pad : JInt64) (neg : Bool) : FormatRun Buffer := do
  let m ← topBit x
  let n := wrapInt .i64 (boolInt neg + max pad.val m)
  let str ← liftJl (newBuffer n)
  let (str, x, i) := binLoop4 lowByte shr (n.toNat / 4 + 1) str x n
  let str := binLoop1 lowByte shr neg (n.toNat + 1) str x i
  pure (minusSign neg str)

/--
Julia source: base/intfuncs.jl:905-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function oct(x::Unsigned, pad::Int, neg::Bool)
    m = div(top_set_bit(x) + 2, 3)
    n = neg + max(pad, m)
    str = _string_n(n)
    GC.@preserve str begin
        p = pointer(str)
        i = n
        while i > neg
            unsafe_store!(p, 0x30 + ((x % UInt8)::UInt8 & 0x7), i)
            x >>= 0x3
            i -= 1
        end
        neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
    end
    return str
end
```
-/
def oct {U : Type} (topBit : U → Nat) (lowByte : U → Nat) (shr : U → Nat → U)
    (x : U) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  let m : Int := (topBit x + 2) / 3
  let n := wrapInt .i64 (boolInt neg + max pad.val m)
  let str ← newBuffer n
  pure (minusSign neg (octLoop lowByte shr neg (n.toNat + 1) str x n))

def octM {U : Type} (topBit : U → FormatRun Int) (lowByte : U → Nat)
    (shr : U → Nat → U) (x : U) (pad : JInt64) (neg : Bool) : FormatRun Buffer := do
  let top ← topBit x
  let m := (top + 2).tdiv 3
  let n := wrapInt .i64 (boolInt neg + max pad.val m)
  let str ← liftJl (newBuffer n)
  pure (minusSign neg (octLoop lowByte shr neg (n.toNat + 1) str x n))

/--
Julia source: base/intfuncs.jl:938-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append_c_digits(olength::Int, digits::Unsigned, buf, pos::Int)
    i = olength
    while i >= 2
        d, c = divrem(digits, 0x64)
        digits = oftype(digits, d)
        @inbounds d100 = _dec_d100[(c % Int)::Int + 1]
        @inbounds buf[pos + i - 2] = d100 % UInt8
        @inbounds buf[pos + i - 1] = (d100 >> 0x8) % UInt8
        i -= 2
    end
    if i == 1
        @inbounds buf[pos] = UInt8('0') + rem(digits, 0xa) % UInt8
    end
    return pos + olength
end
```
-/
def appendCDigits {U : Type} (value : U → Int) (divrem : U → Nat → Jl (U × Nat))
    (olength : JInt64) (digits : U) (buf : Buffer) (pos : JInt64) : Jl (Buffer × JInt64) := do
  let (i, digits, buf) ← appendLoop value divrem (olength.val.toNat / 2 + 1) olength.val digits buf pos.val
  let buf := if i = 1 then store buf pos.val (48 + (value digits).toNat % 10) else buf
  pure (buf, JuliaLean.base.int.add pos olength)

/--
Julia source: base/intfuncs.jl:954-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append_nine_digits(digits::Unsigned, buf, pos::Int)
    if digits == 0
        for _ = 1:9
            @inbounds buf[pos] = UInt8('0')
            pos += 1
        end
        return pos
    end
    return @inline append_c_digits(9, digits, buf, pos) # force loop-unrolling on the length
end
```
-/
def appendNineDigits {U : Type} (value : U → Int) (append : JInt64 → U → Buffer → JInt64 → Jl (Buffer × JInt64))
    (digits : U) (buf : Buffer) (pos : JInt64) : Jl (Buffer × JInt64) :=
  if value digits = 0 then
    let (buf, pos) := (List.range 9).foldl (fun (s : Buffer × JInt64) _ =>
      (store s.1 s.2.val 48, JuliaLean.base.int.add s.2 (JuliaLean.base.int.lit .i64 1))) (buf, pos)
    pure (buf, pos)
  else append (JuliaLean.base.int.lit .i64 9) digits buf pos

/--
Julia source: base/intfuncs.jl:965-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append_c_digits_fast(olength::Int, digits::Unsigned, buf, pos::Int)
    i = olength
    # n.b. olength may be larger than required to print all of `digits` (and will be padded
    # with zeros), but the printed number will be undefined if it is smaller, and may include
    # bits of both the high and low bytes.
    maxpow10 = 0x3b9aca00 # 10e9 as UInt32
    while i > 9 && digits > typemax(UInt)
        # do everything in cheap math chunks, using the processor's native math size
        d, c = divrem(digits, maxpow10)
        digits = oftype(digits, d)
        append_nine_digits(c % UInt32, buf, pos + i - 9)
        i -= 9
    end
    append_c_digits(i, digits % UInt, buf, pos)
    return pos + olength
end
```
-/
def appendCDigitsFast {U : Type} (value : U → Int) (divrem : U → Nat → Jl (U × Nat))
    (toUInt : U → JInt .u64) (append : JInt64 → JInt .u64 → Buffer → JInt64 → Jl (Buffer × JInt64))
    (appendNine : JInt .u32 → Buffer → JInt64 → Jl (Buffer × JInt64))
    (olength : JInt64) (digits : U) (buf : Buffer) (pos : JInt64) : Jl (Buffer × JInt64) := do
  let step := fun (s : Int × U × Buffer) => do
    let (i, digits, buf) := s
    if i > 9 ∧ value digits > IntTy.max .u64 then
      let (d, c) ← divrem digits 1000000000
      let (buf, _) ← appendNine (JuliaLean.base.int.lit .u32 c) buf (JuliaLean.base.int.lit .i64 (pos.val + i - 9))
      pure (i - 9, d, buf)
    else pure s
  let (i, digits, buf) ← repeatM (olength.val.toNat / 9 + 1) step (olength.val, digits, buf)
  let (buf, _) ← append (JuliaLean.base.int.lit .i64 i) (toUInt digits) buf pos
  pure (buf, JuliaLean.base.int.add pos olength)

/--
Julia source: base/intfuncs.jl:983-1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dec(x::Unsigned, pad::Int, neg::Bool)
    n = neg + ndigits(x, pad=pad)
    str = _string_n(n)
    GC.@preserve str begin
        p = pointer(str)
        i = n
        while i > 9 && x > typemax(UInt)
            d, r = divrem(x, 0x3b9aca00) # 10^9
            x = oftype(x, d)
            r32 = r % UInt32
            for j in 0:3
                q, s = divrem(r32, 0x64)
                r32 = q
                v = @inbounds _dec_d100[1 + (s % Int)]
                unsafe_store!(p, (v >> 8) % UInt8, i - 2*j)
                unsafe_store!(p, v % UInt8, i - 2*j - 1)
            end
            unsafe_store!(p, 0x30 + (r32 % UInt8), i - 8)
            i -= 9
        end
        y = x % UInt
        while i >= 2
            d, r = divrem(y, 0x64)
            y = d
            v = @inbounds _dec_d100[1 + (r % Int)]
            unsafe_store!(p, (v >> 8) % UInt8, i)
            unsafe_store!(p, v % UInt8, i - 1)
            i -= 2
        end
        if i > neg
            unsafe_store!(p, 0x30 + (rem(y, 0xa) % UInt8), i)
        end
        neg && unsafe_store!(p, 0x2d, 1) # '-'
    end
    return str
end
```
-/
def dec {U : Type} (value : U → Int) (divrem : U → Nat → Jl (U × Nat))
    (ndigits : U → JInt64 → Jl JInt64) (toUInt : U → JInt .u64)
    (x : U) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  let n := wrapInt .i64 (boolInt neg + (← ndigits x pad).val)
  let str ← newBuffer n
  let chunk := fun (s : Buffer × U × Int) => do
    let (str, x, i) := s
    if i > 9 ∧ value x > IntTy.max .u64 then
      let (d, r) ← divrem x 1000000000
      let (str, r32) ← (List.range 4).foldlM (fun (s : Buffer × Nat) (j : Nat) => do
        let q := s.2 / 100
        let rem := s.2 % 100
        let v ← decimalPair rem
        let str := readTable s.1 (rem + 1) 100
        let str := store str (i - 2 * (j : Int)) (v / 256 % 256)
        let str := store str (i - 2 * (j : Int) - 1) (v % 256)
        pure (str, q)) (str, r % 2^32)
      pure (store str (i - 8) (48 + r32 % 256), d, i - 9)
    else pure s
  let (str, x, i) ← repeatM (n.toNat / 9 + 1) chunk (str, x, n)
  let y := toUInt x
  let pair := fun (s : Buffer × JInt .u64 × Int) => do
    let (str, y, i) := s
    if i ≥ 2 then
      let d := JuliaLean.base.int.lit .u64 (y.val / 100)
      let r := (y.val % 100).toNat
      let v ← decimalPair r
      let str := readTable str (r + 1) 100
      pure (store (store str i (v / 256 % 256)) (i - 1) (v % 256), d, i - 2)
    else pure s
  let (str, y, i) ← repeatM (i.toNat / 2 + 1) pair (str, y, i)
  let str := if i > boolInt neg then store str i (48 + (y.val % 10).toNat % 256) else str
  pure (minusSign neg str)

def divremHundred32 (x : JInt .u32) : Jl (JInt .u32 × JInt .u32) :=
  let (a,b) := JuliaLean.base.int.promoteSameSign x (JuliaLean.base.int.lit .u8 100)
  JuliaLean.base.div.divremBitIntegerToZero a b

def divremHundred64 (x : JInt .u64) : Jl (JInt .u64 × JInt .u64) :=
  let (a,b) := JuliaLean.base.int.promoteSameSign x (JuliaLean.base.int.lit .u8 100)
  JuliaLean.base.div.divremBitIntegerToZero a b

def remTen64 (x : JInt .u64) : Jl (JInt .u64) :=
  let (a,b) := JuliaLean.base.int.promoteSameSign x (JuliaLean.base.int.lit .u8 10)
  JuliaLean.base.int.remSame a b

def decSource {U Q R : Type} (value : U → Int)
    (divremChunk : U → Jl (Q × R)) (oftype : U → Q → Jl U)
    (rem32 : R → JInt .u32) (ndigits : U → JInt64 → Jl JInt64)
    (toUInt : U → JInt .u64) (x : U) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  let n := wrapInt .i64 (boolInt neg + (← ndigits x pad).val)
  let str ← newBuffer n
  let chunk := fun (state : Buffer × U × Int) => do
    let (str,x,i) := state
    if i > 9 ∧ value x > IntTy.max .u64 then
      let (d,r) ← divremChunk x
      let x ← oftype x d
      let (str,r32) ← (List.range 4).foldlM
        (fun (state : Buffer × JInt .u32) (j : Nat) => do
          let (q,s) ← divremHundred32 state.2
          let rem := (JuliaLean.base.int.remT .i64 s).val.toNat
          let v ← decimalPair rem
          let str := readTable state.1 (rem + 1) 100
          let str := store str (i - 2 * (j : Int)) (v / 256 % 256)
          let str := store str (i - 2 * (j : Int) - 1) (v % 256)
          pure (str,q)) (str,rem32 r)
      pure (store str (i - 8) (48 + (JuliaLean.base.int.remT .u8 r32).val.toNat),x,i - 9)
    else pure state
  let (str,x,i) ← repeatM (n.toNat / 9 + 1) chunk (str,x,n)
  let y := toUInt x
  let pair := fun (state : Buffer × JInt .u64 × Int) => do
    let (str,y,i) := state
    if i ≥ 2 then
      let (d,r) ← divremHundred64 y
      let rem := (JuliaLean.base.int.remT .i64 r).val.toNat
      let v ← decimalPair rem
      let str := readTable str (rem + 1) 100
      pure (store (store str i (v / 256 % 256)) (i - 1) (v % 256),d,i - 2)
    else pure state
  let (str,y,i) ← repeatM (i.toNat / 2 + 1) pair (str,y,i)
  let str ← if i > boolInt neg then do
    let r ← remTen64 y
    pure (store str i (48 + (JuliaLean.base.int.remT .u8 r).val.toNat))
    else pure str
  pure (minusSign neg str)

/--
Julia source: base/intfuncs.jl:1020-1042 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hex(x::Unsigned, pad::Int, neg::Bool)
    m = (top_set_bit(x) + 3) ÷ 4 # nibbles = ceil(bits / 4)
    n = neg + max(pad, m)
    str = _string_n(n)
    GC.@preserve str begin
        p = pointer(str)
        i = n
        while i >= 2
            b = (x % UInt8)::UInt8
            d1, d2 = b >> 0x4, b & 0xf
            unsafe_store!(p, d1 + ifelse(d1 > 0x9, 0x57, 0x30), i-1)
            unsafe_store!(p, d2 + ifelse(d2 > 0x9, 0x57, 0x30), i)
            x >>= 0x8
            i -= 2
        end
        if i > neg
            d = (x % UInt8)::UInt8 & 0xf
            unsafe_store!(p, d + ifelse(d > 0x9, 0x57, 0x30), i)
        end
        neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
    end
    return str
end
```
-/
def hex {U : Type} (topBit : U → Nat) (lowByte : U → Nat) (shr : U → Nat → U)
    (x : U) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  let m : Int := (topBit x + 3) / 4
  let n := wrapInt .i64 (boolInt neg + max pad.val m)
  let str ← newBuffer n
  let (str, x, i) := hexLoop lowByte shr (n.toNat / 2 + 1) str x n
  let str := if i > boolInt neg then store str i (hexChar (lowByte x % 16)) else str
  pure (minusSign neg str)

def hexM {U : Type} (topBit : U → FormatRun Int) (lowByte : U → Nat)
    (shr : U → Nat → U) (x : U) (pad : JInt64) (neg : Bool) : FormatRun Buffer := do
  let top ← topBit x
  let m := (top + 3).tdiv 4
  let n := wrapInt .i64 (boolInt neg + max pad.val m)
  let str ← liftJl (newBuffer n)
  let (str, x, i) := hexLoop lowByte shr (n.toNat / 2 + 1) str x n
  let str := if i > boolInt neg then store str i (hexChar (lowByte x % 16)) else str
  pure (minusSign neg str)

/--
Julia source: base/intfuncs.jl:1047-1070 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _base(base::Integer, x::Integer, pad::Int, neg::Bool)
    (x >= 0) | (base < 0) || throw(DomainError(x, "For negative `x`, `base` must be negative."))
    2 <= abs(base) <= 62 || throw(DomainError(base, "base must satisfy 2 ≤ abs(base) ≤ 62"))
    b = (base % Int)::Int
    digits = abs(b) <= 36 ? base36digits : base62digits
    n = neg + ndigits(x, base=b, pad=pad)
    str = _string_n(n)
    GC.@preserve str begin
        p = pointer(str)
        i = n
        while i > neg
            if b > 0
                unsafe_store!(p, @inbounds(digits[1 + (rem(x, b) % Int)::Int]), i)
                x = div(x,b)
            else
                unsafe_store!(p, @inbounds(digits[1 + (mod(x, -b) % Int)::Int]), i)
                x = cld(x,b)
            end
            i -= 1
        end
        neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
    end
    return str
end
```
-/
def baseString {I B : Type} (o : IntegerOps I) (bo : IntegerOps B) (remInt : B → JInt64)
    (rem : I → Int → Jl Int) (div : I → Int → Jl I)
    (mod : I → Int → Jl Int) (cld : I → Int → Jl I)
    (ndigits : I → JInt64 → JInt64 → Jl JInt64)
    (base : B) (x : I) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  if ¬ (o.value x ≥ 0 ∨ bo.value base < 0) then .error (.domainError "")
  else if ¬ (2 ≤ bo.value (bo.abs base) ∧ bo.value (bo.abs base) ≤ 62) then .error (.domainError "") else
    let b := remInt base
    let large := decide (b.val.natAbs > 36)
    let n := wrapInt .i64 (boolInt neg + (← ndigits x b pad).val)
    let str ← newBuffer n
    pure (minusSign neg (← baseLoop o rem div mod cld b.val large neg (n.toNat + 1) x n str))

/--
Julia source: base/intfuncs.jl:1072-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
split_sign(n::Integer) = (unsigned(abs(n)), n < 0)
```
-/
def splitSign_Integer {I U : Type} (abs : I → I) (unsigned : I → U) (value : I → Int) (n : I) : U × Bool :=
  (unsigned (abs n), decide (value n < 0))

/--
Julia source: base/intfuncs.jl:1073-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
split_sign(n::Unsigned) = (n, false)
```
-/
def splitSign_Unsigned {U : Type} (n : U) : U × Bool := (n, false)

/--
Julia source: base/intfuncs.jl:1101-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string(n::Integer; base::Integer = 10, pad::Integer = 1)
    @constprop :aggressive
    pad = (min(max(pad, typemin(Int)), typemax(Int)) % Int)::Int
    if base == 2
        (n_positive, neg) = split_sign(n)
        bin(n_positive, pad, neg)
    elseif base == 8
        (n_positive, neg) = split_sign(n)
        oct(n_positive, pad, neg)
    elseif base == 10
        (n_positive, neg) = split_sign(n)
        dec(n_positive, pad, neg)
    elseif base == 16
        (n_positive, neg) = split_sign(n)
        hex(n_positive, pad, neg)
    else
        _base(base, base > 0 ? unsigned(abs(n)) : convert(Signed, n), pad, (base>0) & (n<0))
    end
end
```
-/
def string_Integer {I B P U S : Type} (value : I → Int) (bvalue : B → Int) (pvalue : P → Int)
    (split : I → U × Bool) (unsignedAbs : I → U) (toSigned : I → Jl S)
    (bin oct dec hex : U → JInt64 → Bool → Jl Buffer)
    (baseUnsigned : B → U → JInt64 → Bool → Jl Buffer)
    (baseSigned : B → S → JInt64 → Bool → Jl Buffer)
    (n : I) (base : B) (pad : P) : Jl Buffer := do
  let pad := JuliaLean.base.int.lit .i64 (min (max (pvalue pad) (IntTy.min .i64)) (IntTy.max .i64))
  if bvalue base = 2 then
    let (nPositive, neg) := split n
    bin nPositive pad neg
  else if bvalue base = 8 then
    let (nPositive, neg) := split n
    oct nPositive pad neg
  else if bvalue base = 10 then
    let (nPositive, neg) := split n
    dec nPositive pad neg
  else if bvalue base = 16 then
    let (nPositive, neg) := split n
    hex nPositive pad neg
  else if bvalue base > 0 then baseUnsigned base (unsignedAbs n) pad (decide (value n < 0))
  else baseSigned base (← toSigned n) pad false

/--
Julia source: base/intfuncs.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(b::Bool) = b ? "true" : "false"
```
-/
def string_Bool (b : Bool) : String := if b then "true" else "false"

/--
Julia source: base/intfuncs.jl:1140-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bitstring(x::T) where {T}
    isprimitivetype(T) || throw(ArgumentError(LazyString(T, " not a primitive type")))
    sz = Core.bitsizeof(T)
    onebyte = sz == 8
    subbyte = sz < 8
    str = _string_n(sz)
    GC.@preserve str begin
        p = pointer(str)
        i = sz
        while i >= 4
            b = UInt32(onebyte ? bitcast(UInt8, x) : subbyte ? zext_int(UInt8, x) : trunc_int(UInt8, x))
            d = 0x30303030 +% ((b *% 0x08040201) >> 0x3) & 0x01010101
            unsafe_store!(p, (d >> 0x00) % UInt8, i-3)
            unsafe_store!(p, (d >> 0x08) % UInt8, i-2)
            unsafe_store!(p, (d >> 0x10) % UInt8, i-1)
            unsafe_store!(p, (d >> 0x18) % UInt8, i)
            x = lshr_int(x, 4)
            i -= 4
        end
        while i > 0
            b = UInt8(onebyte ? bitcast(UInt8, x) : subbyte ? zext_int(UInt8, x) : trunc_int(UInt8, x))
            unsafe_store!(p, 0x30 + (b & 0x01), i)
            x = lshr_int(x, 1)
            i -= 1
        end
    end
    return str
end
```
-/
def bitstring {A : Type} (primitive : Bool) (bits : Nat) (bitcastByte zextByte truncByte : A → Nat)
    (lshr : A → Nat → A) (x : A) : Jl Buffer := do
  if !primitive then .error (.argumentError "") else
    let onebyte := bits == 8
    let subbyte := bits < 8
    let lowByte := fun x => if onebyte then bitcastByte x else if subbyte then zextByte x else truncByte x
    let str ← newBuffer bits
    let (str, x, i) := binLoop4 lowByte lshr (bits / 4 + 1) str x bits
    pure (binLoop1 lowByte lshr false (i.toNat + 1) str x i)

/--
Julia source: base/intfuncs.jl:1219-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hastypemax(::Type{T}) where {T} = applicable(typemax, T) && applicable(typemin, T)
```
-/
def hasTypeMax (maxApplicable minApplicable : Bool) : Bool := maxApplicable && minApplicable

/--
Julia source: base/intfuncs.jl:1220-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hastypemax(::Type{Union{}}) = false
```
-/
def hasTypeMax_Bottom : Bool := false

/--
Julia source: base/intfuncs.jl:1221-1221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hastypemax(::Type{Union{}}, slurp...) = throw(MethodError(hastypemax, (Union{}, slurp...)))
```
-/
def hasTypeMax_Bottom_Extra {Tail R : Type} (_slurp : Tail) : Jl R := .error (.methodError "hastypemax")

/--
Julia source: base/intfuncs.jl:1293-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isqrt(x::Integer) = oftype(x, trunc(sqrt(x)))
```
-/
def isqrt_Integer {I F R : Type} (sqrt : I → Jl F) (trunc : F → Jl R)
    (oftype : R → Jl I) (x : I) : Jl I := do
  oftype (← trunc (← sqrt x))

/--
Julia source: base/intfuncs.jl:1295-1302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isqrt(x::Union{Int64,UInt64,Int128,UInt128})
    x==0 && return x
    s = oftype(x, trunc(sqrt(x)))
    # fix with a Newton iteration, since conversion to float discards
    # too many bits.
    s = (s + div(x,s)) >> 1
    s*s > x ? s-1 : s
end
```
-/
def isqrt_Wide {t : IntTy} {F R : Type} (sqrt : JInt t → Jl F) (trunc : F → Jl R)
    (oftype : R → Jl (JInt t)) (div : JInt t → JInt t → Jl (JInt t))
    (x : JInt t) : Jl (JInt t) := do
  if x.val = 0 then pure x else
    let s ← oftype (← trunc (← sqrt x))
    let s := JuliaLean.base.int.shr_Int (JuliaLean.base.int.add s (← div x s)) (JuliaLean.base.int.lit .i64 1)
    pure (if (JuliaLean.base.int.mul s s).val > x.val then JuliaLean.base.int.sub s (JuliaLean.base.int.lit t 1) else s)

/--
The result type `F` is Julia's `typeof(n*n)`, selected by multiplication dispatch.

Julia source: base/intfuncs.jl:1330-1337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function factorial(n::Integer)
    n < 0 && throw(DomainError(n, "`n` must be non-negative."))
    f::typeof(n*n) = 1
    for i::typeof(n*n) = 2:n
        f *= i
    end
    return f
end
```
-/
def factorial_Integer {I F : Type} (value : I → Int) (ofInt : Int → Jl F)
    (mul : F → F → Jl F) (n : I) : Jl F := do
  if value n < 0 then .error (.domainError "") else
    let f ← ofInt 1
    factorialLoop value ofInt mul n f

structure BinomialMixedCallees (N K I : Type) where
  promote : N → K → Jl (I × I)
  binomial : I → I → Jl I

/--
Julia source: base/intfuncs.jl:1373-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
binomial(n::Integer, k::Integer) = binomial(promote(n, k)...)
```
-/
def binomial_Mixed {N K I : Type} (c : BinomialMixedCallees N K I) (n : N) (k : K) : Jl I := do
  let (n, k) ← c.promote n k
  c.binomial n k

/--
Julia source: base/intfuncs.jl:1375-1402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :terminates_locally function binomial(n::T, k::T) where T<:Integer
    n0, k0 = n, k
    k < 0 && return zero(T)
    sgn = one(T)
    if n < 0
        n = -n + k - one(T)
        if isodd(k)
            sgn = -sgn
        end
    end
    k > n && return zero(T)
    (k == 0 || k == n) && return sgn
    k == 1 && return sgn*n
    if k > (n>>1)
        k = (n - k)
    end
    x = nn = n - k + one(T)
    nn += one(T)
    rr = T(2)
    while rr <= k
        xt = div(widemul(x, nn), rr)
        x = xt % T
        x == xt || throw(OverflowError(LazyString("binomial(", n0, ", ", k0, ") overflows")))
        rr += one(T)
        nn += one(T)
    end
    copysign(x, sgn)
end
```
-/
def binomial_Integer {I : Type} (o : IntegerOps I) (wideDiv : I → I → I → Jl Int)
    (copysign : I → I → I) (n0 k0 : I) : Jl I := do
  if o.value k0 < 0 then pure (o.ofInt 0) else
    let sgn := o.ofInt 1
    let (n, sgn) := if o.value n0 < 0 then
        (o.sub (o.add (o.neg n0) k0) (o.ofInt 1), if o.value k0 % 2 ≠ 0 then o.neg sgn else sgn)
      else (n0, sgn)
    if o.value k0 > o.value n then pure (o.ofInt 0)
    else if o.value k0 = 0 ∨ o.value k0 = o.value n then pure sgn
    else if o.value k0 = 1 then pure (o.mul sgn n)
    else
      let k := if o.value k0 > o.value (o.shiftRight n 1) then o.sub n k0 else k0
      let x := o.add (o.sub n k) (o.ofInt 1)
      let nn := o.add x (o.ofInt 1)
      let rr := o.ofInt 2
      let x ← binomialLoop o wideDiv ((o.value k - 1).toNat) x nn rr k
      pure (copysign x sgn)

structure BinomialNumberCallees (N I R : Type) where
  value : I → Int
  zero : N → N
  one : I → I
  oneunit : N → N
  subIndex : N → Int → N
  div : N → I → Jl R
  prod : (I → Jl R) → JuliaLean.base.reduce.JIterator I → R → Jl R
  oneTo : I → JuliaLean.base.reduce.JIterator I

/--
Julia source: base/intfuncs.jl:1428-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function binomial(x::Number, k::Integer)
    k < 0 && return zero(x)/one(k)
    # we don't use prod(i -> (x-i+1), 1:k) / factorial(k),
    # and instead divide each term by i, to avoid spurious overflow.
    return prod(i -> (x-(i-1))/i, OneTo(k), init=oneunit(x)/one(k))
end
```
-/
def binomial_Number {N I R : Type} (c : BinomialNumberCallees N I R)
    (x : N) (k : I) : Jl R := do
  if c.value k < 0 then c.div (c.zero x) (c.one k) else
    let init ← c.div (c.oneunit x) (c.one k)
    c.prod (fun i => c.div (c.subIndex x (c.value i - 1)) i) (c.oneTo k) init

structure BinomialCallees (N I R : Type) where
  value : I → Int
  zero : N → N
  one : I → I
  oneunit : N → N
  subIndex : N → Int → Jl N
  div : N → I → Jl R
  prod : (I → Jl R) → JuliaLean.base.reduce.JIterator I → R → Jl R
  oneTo : I → Except JlError (JuliaLean.base.reduce.JIterator I)

def binomialNumber {N I R : Type} (c : BinomialCallees N I R)
    (x : N) (k : I) : Jl R := do
  if c.value k < 0 then c.div (c.zero x) (c.one k) else
    match c.oneTo k with
    | .error e => .error e
    | .ok itr => do
        let init ← c.div (c.oneunit x) (c.one k)
        c.prod (fun i => do c.div (← c.subIndex x (c.value i - 1)) i) itr init

/--
Julia source: base/intfuncs.jl:1461-1464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function clamp(x::X, lo::L, hi::H) where {X,L,H}
    T = promote_type(X, L, H)
    return (x > hi) ? convert(T, hi) : (x < lo) ? convert(T, lo) : convert(T, x)
end
```
-/
def clamp {X L H T : Type} (gt : X → H → Bool) (lt : X → L → Bool)
    (convertX : X → Jl T) (convertL : L → Jl T) (convertH : H → Jl T)
    (x : X) (lo : L) (hi : H) : Jl T :=
  if gt x hi then convertH hi else if lt x lo then convertL lo else convertX x

/--
Julia source: base/intfuncs.jl:1485-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function clamp(x, ::Type{T}) where {T<:Integer}
    # delegating to clamp(x, typemin(T), typemax(T)) would promote types
    # this way, we avoid unnecessary conversions
    # think of, e.g., clamp(big(2) ^ 200, Int16)
    lo = typemin(T)
    hi = typemax(T)
    return (x > hi) ? hi : (x < lo) ? lo : convert(T, x)
end
```
-/
def clamp_Type {X T : Type} (lo hi : T) (gt lt : X → T → Bool) (convert : X → Jl T) (x : X) : Jl T :=
  if gt x hi then pure hi else if lt x lo then pure lo else convert x

/--
Julia source: base/intfuncs.jl:1493-1493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clamp(x, ::Type{Union{}}, slurp...) = throw(MethodError(clamp, (x, Union{}, slurp...)))
```
-/
def clamp_Bottom {X Tail R : Type} (_x : X) (_slurp : Tail) : Jl R := .error (.methodError "clamp")

/--
Julia source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function clamp!(x::AbstractArray, lo, hi)
    @inbounds for i in eachindex(x)
        x[i] = clamp(x[i], lo, hi)
    end
    x
end
```
-/
def clampBang {A Index V L H : Type} {IndexOps : Type u}
    (index : IndexOps)
    (eachindex : IndexOps → A → Jl (List Index))
    (getindex : A → Index → Jl V)
    (setindex : A → Index → V → Jl A) (clamp : V → L → H → Jl V)
    (x : A) (lo : L) (hi : H) : Jl A := do
  let indices ← eachindex index x
  let x ← indices.foldlM (fun x i => do
    let value ← getindex x i
    setindex x i (← clamp value lo hi)) x
  pure x

/--
Julia source: base/intfuncs.jl:1533-1533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clamp(x::Integer, r::AbstractUnitRange{<:Integer}) = clamp(x, first(r), last(r))
```
-/
def clamp_Range {I R T : Type} (first last : R → I) (clamp : I → I → I → Jl T)
    (x : I) (r : R) : Jl T := clamp x (first r) (last r)

/--
Julia source: base/intfuncs.jl:337-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _bezout_coef(n, m)
    g, x, _ = gcdx(n, m)
    g != 1 && throw(DomainError((n, m), LazyString("Greatest common divisor is ", g, ".")))
    return x
end
```
-/
def bezoutCoef {N M G X Y : Type} (gcdx : N → M → Jl (G × X × Y))
    (isone : G → Bool) (n : N) (m : M) : Jl X := do
  let (g, x, _) ← gcdx n m
  if !isone g then .error (.domainError "") else pure x

/--
Julia source: base/intfuncs.jl:308-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invmod(n::Integer, m::Integer)
    # The postcondition is: mod(widemul(result, n), m) == mod(one(T), m) && iszero(div(result, m))
    iszero(m) && throw(DomainError(m, "`m` must not be 0."))
    R = promote_typeof(n, m)
    if R <: Signed
        x = _bezout_coef(n, m)
        return mod(x, m)
    else
        S = signed(R)
        if !hastypemax(S) || (n <= typemax(S)) && (m <= typemax(S))
            x = _bezout_coef(n % S, m % S)

            # this branch is only hit if R <: Unsigned, so we don't have
            # to worry about abs(typemin(::Signed)) overflow. If `m` is
            # signed then `x` must be unsigned, and thus never negative
            isnegative(x) && (x += abs(m))
            return mod(x % R, m)
        else
            # since gcdx only promises bezout w.r.t overflow for unsigned ints,
            # we have to widen to a signed type
            W = widen(S)
            x = _bezout_coef(n % W, m % W)
            t = mod(x, m % W)
            isnegative(m) && (t -= m)
            return mod(t % R, m)
        end
    end
end
```
-/
def invmod_Integer {N M X S W R : Type}
    (iszero : M → Bool) (resultSigned : Bool) (signedHasMax : Bool)
    (nFits : N → Bool) (mFits : M → Bool)
    (bezout : N → M → Jl X) (modX : X → M → Jl R)
    (toSignedN : N → S) (toSignedM : M → S)
    (bezoutSigned : S → S → Jl S) (isnegative : S → Bool) (addAbsM : S → M → S)
    (toResult : S → R) (modR : R → M → Jl R)
    (toWideN : N → W) (toWideM : M → W) (bezoutWide : W → W → Jl W)
    (modWide : W → W → Jl W) (mNegative : M → Bool) (subtractM : W → M → W)
    (wideResult : W → R) (n : N) (m : M) : Jl R := do
  if iszero m then .error (.domainError "") else
    if resultSigned then
      let x ← bezout n m
      modX x m
    else if !signedHasMax || (nFits n && mFits m) then
      let x ← bezoutSigned (toSignedN n) (toSignedM m)
      let x := if isnegative x then addAbsM x m else x
      modR (toResult x) m
    else
      let x ← bezoutWide (toWideN n) (toWideM m)
      let t ← modWide x (toWideM m)
      let t := if mNegative m then subtractM t m else t
      modR (wideResult t) m

/--
Julia source: base/intfuncs.jl:581-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_powermod_mi_legal(::Integer) = false
```
-/
def powermodMILegal_Integer {I : Type} (_mm : I) : Bool := false

/--
Julia source: base/intfuncs.jl:582-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _powermod_mi_legal(mm::T) where {T<:Unsigned}
    return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
end
```
-/
def powermodMILegal_Unsigned {U : Type} (hasMax : Bool) (max : U) (le : U → U → Bool)
    (shiftRight : U → Nat → U) (bytes : Nat) (mm : U) : Bool :=
  hasMax && le mm (shiftRight max (bytes * 4))

/--
Julia source: base/intfuncs.jl:524-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function powermod(x::Integer, p::Integer, m::T) where T<:Integer
    p == 0 && return mod(one(m),m)
    # When the concrete type of p is signed and has the lowest value,
    # `p < 0 && p == -p` is equivalent to `p == typemin(typeof(p))` for 2's complement representation.
    # but will work for integer types like `BigInt` that don't have `typemin` defined
    # It needs special handling otherwise will cause overflow problem.
    if p < 0
        if p == -p
            imod = invmod(x, m)
            rhalf = powermod(imod, -(p÷2), m)
            r::T = mod(widemul(rhalf, rhalf), m)
            isodd(p) && (r = mod(widemul(r, imod), m))
            #else odd
            return r
        else
            return powermod(invmod(x, m), -p, m)
        end
    end
    (m == 1 || m == -1) && return zero(m)

    mm = uabs(m)
    rr = one(mm)
    bb = oftype(mm, mod(x, mm))

    # legal && profitable
    if _powermod_mi_legal(mm) && (p > 2sizeof(mm))
        if bb == 0
            rr = zero(mm)
        else
            mis = MultiplicativeInverses.multiplicativeinverse(mm)
            Base.@assume_effects :terminates_locally while true
                if (p & 1) != 0
                    rr = mod(rr * bb, mis)
                end
                p >>= 1
                p == 0 && break
                bb = mod(bb * bb, mis)
            end
        end
    else
        if bb == 0
            rr = zero(mm)
        else
            Base.@assume_effects :terminates_locally while true
                if (p & 1) != 0
                    rr = oftype(mm, mod(widemul(rr, bb), mm))
                end
                p >>= 1
                p == 0 && break
                bb = oftype(mm, mod(widemul(bb, bb), mm))
            end
        end
    end
    r = oftype(m, rr)
    return (iszero(r) || (m > 0)) ? r : r + m
end
```
-/
def powermod_Integer {X I P U R MI : Type} (io : IntegerOps I) (po : IntegerOps P)
    (uvalue : U → Int) (uone uzero : U → U) (uabs : I → U)
    (modI : I → I → Jl I) (modX : X → U → Jl U) (modInverse : R → U → Jl U) (toI : U → Jl I)
    (wideSquare : I → I → I → Jl I) (wideLast : I → R → I → Jl I)
    (wideModU : U → U → U → Jl U) (invmod : X → I → Jl R)
    (legal : U → Bool) (bytes : U → Nat) (inverse : U → Jl MI)
    (magicMod : U → U → MI → Jl U) (x : X) (p : P) (m : I) : Jl I := do
  let positive := fun (baseMod : U → Jl U) (p : P) => do
    if io.value m = 1 ∨ io.value m = -1 then pure (io.ofInt 0) else
      let mm := uabs m
      let rr := uone mm
      let bb ← baseMod mm
      let rr ← if legal mm && decide (po.value p > 2 * bytes mm) then
          if uvalue bb = 0 then pure (uzero mm) else do
            let mis ← inverse mm
            powermodLoop po uvalue (fun a b => magicMod a b mis) (po.value p).natAbs p rr bb
        else if uvalue bb = 0 then pure (uzero mm) else
          powermodLoop po uvalue (fun a b => wideModU a b mm) (po.value p).natAbs p rr bb
      let r ← toI rr
      pure (if io.value r = 0 ∨ io.value m > 0 then r else io.add r m)
  if po.value p = 0 then modI (io.ofInt 1) m
  else if po.value p < 0 then
    if po.value p = po.value (po.neg p) then
      let imod ← invmod x m
      let half ← po.div p (po.ofInt 2)
      let rhalf ← positive (modInverse imod) (po.neg half)
      let r ← wideSquare rhalf rhalf m
      if po.value p % 2 ≠ 0 then wideLast r imod m else pure r
    else positive (modInverse (← invmod x m)) (po.neg p)
  else positive (modX x) p

/--
Julia source: base/intfuncs.jl:1249-1281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function digits!(a::AbstractVector{T}, n::Integer; base::Integer = 10) where T<:Integer
    2 <= abs(base) || throw(DomainError(base, "base must be ≥ 2 or ≤ -2"))
    hastypemax(T) && abs(base) - 1 > typemax(T) &&
        throw(ArgumentError(LazyString("type ", T, " too small for base ", base)))
    isempty(a) && return a

    if base > 0
        if ispow2(base) && n >= 0 && n isa Base.BitInteger && base <= typemax(Int)
            base = Int(base)
            k = trailing_zeros(base)
            c = base - 1
            for i in eachindex(a)
                a[i] = (n >> (k * (i - firstindex(a)))) & c
            end
        else
            for i in eachindex(a)
                n, d = divrem(n, base)
                a[i] = d
            end
        end
    else
        # manually peel one loop iteration for type stability
        n, d = fldmod(n, -base)
        a[firstindex(a)] = d
        n = -signed(n)
        for i in firstindex(a)+1:lastindex(a)
            n, d = fldmod(n, -base)
            a[i] = d
            n = -n
        end
    end
    return a
end
```
-/
def digitsBang {N B S D T : Type} (nvalue : N → Int) (bo : IntegerOps B)
    (hasMax : Bool) (elementMax : Int) (isBitInteger : Bool)
    (toIntBase : B → Jl JInt64) (trailingZeros : JInt64 → Nat)
    (shiftMask : N → Nat → Int → D) (divrem : N → B → Jl (N × D))
    (fldmodFirst : N → B → Jl (N × D)) (signed : N → S)
    (neg : S → S) (fldmodRest : S → B → Jl (S × D)) (convert : D → Jl T)
    (a : Vector T) (n : N) (base : B) : Jl (Vector T) := do
  if bo.value (bo.abs base) < 2 then .error (.domainError "")
  else if hasMax && decide (bo.value (bo.sub (bo.abs base) (bo.ofInt 1)) > elementMax) then
    .error (.argumentError "")
  else if a.values.isEmpty then pure a
  else if bo.value base > 0 then
    if ispow2_Integer bo.value bo.countOnes base && decide (nvalue n ≥ 0) && isBitInteger &&
        decide (bo.value base ≤ IntTy.max .i64) then
      let b ← toIntBase base
      let k := trailingZeros b
      let c := b.val - 1
      (List.range a.values.length).foldlM (fun a (j : Nat) => do
        let d ← convert (shiftMask n (k * j) c)
        pure (vectorStore a (a.first + j) d)) a
    else
      let (a, _) ← (List.range a.values.length).foldlM (fun (s : Vector T × N) (j : Nat) => do
        let (n, d) ← divrem s.2 base
        let d ← convert d
        pure (vectorStore s.1 (s.1.first + j) d, n)) (a, n)
      pure a
  else
    let (n, d) ← fldmodFirst n (bo.neg base)
    let d ← convert d
    let a := vectorStore a a.first d
    let n := neg (signed n)
    let (a, _) ← (List.range (a.values.length - 1)).foldlM (fun (s : Vector T × S) (j : Nat) => do
      let (n, d) ← fldmodRest s.2 (bo.neg base)
      let d ← convert d
      pure (vectorStore s.1 (s.1.first + (j + 1)) d, neg n)) (a, n)
    pure a

/--
Julia source: base/intfuncs.jl:1210-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function digits(T::Type{<:Integer}, n::Integer; base::Integer = 10, pad::Integer = 1)
    digits!(zeros(T, ndigits(n, base=base, pad=pad)), n, base=base)
end
```
-/
def digits_Type {N B P T L : Type} (zeros : L → Jl (Vector T))
    (ndigits : N → B → P → Jl L) (digitsBang : Vector T → N → B → Jl (Vector T))
    (n : N) (base : B) (pad : P) : Jl (Vector T) := do
  let length ← ndigits n base pad
  let a ← zeros length
  digitsBang a n base

/--
Julia source: base/intfuncs.jl:1207-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
digits(n::Integer; base::Integer = 10, pad::Integer = 1) =
    digits(typeof(base), n, base = base, pad = pad)
```
-/
def digits_Default {N B P T : Type} (digits : N → B → P → Jl (Vector T))
    (n : N) (base : B) (pad : P) : Jl (Vector T) := digits n base pad

/-! ## Concrete instances and Julia dispatch

These definitions instantiate the generic source methods. They do not count as additional
Julia methods. Division, arbitrary-precision primitives, and logarithms belong to other files.
-/

def bigOps : IntegerOps Int where
  value := id
  unsigned := false
  ofInt := id
  add := Int.add
  sub := Int.sub
  mul := Int.mul
  neg := Int.neg
  abs := fun x => (x.natAbs : Int)
  checkedAbs := fun x => pure (x.natAbs : Int)
  checkedMul := fun x y => pure (x * y)
  div := fun x y => if y = 0 then .error .divideError else pure (x.tdiv y)
  rem := fun x y => if y = 0 then .error .divideError else pure (x.tmod y)
  divrem := fun x y => if y = 0 then .error .divideError else pure (x.tdiv y, x.tmod y)
  shiftRight := fun x n => x / (2 ^ n : Int)
  shiftLeft := fun x n => x * (2 ^ n : Int)
  trailingZeros := fun x => ((List.range (x.natAbs.log2 + 1)).find? (fun n => x.natAbs.testBit n)).getD 0
  countOnes := fun x => (List.range (x.natAbs.log2 + 1)).countP (fun n => x.natAbs.testBit n)

def divremBits {t : IntTy} (a b : JInt t) : Jl (JInt t × JInt t) := do
  let q ← JuliaLean.base.int.divSame a b
  let r ← JuliaLean.base.int.remSame a b
  pure (q, r)

def bitsOps (t : IntTy) : IntegerOps (JInt t) := bitOps t divremBits

def lcmBits {t : IntTy} (a b : JInt t) : Jl (JInt t) :=
  lcm_Integer (bitsOps t) gcd_BitInteger a b

def gcdxBits {t : IntTy} (a b : JInt t) : Jl (JInt t × JInt t × JInt t) :=
  gcdx_Integer (bitsOps t) a b

def promoteBits {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (s.promote t) × JInt (s.promote t)) := do
  let a ← JuliaLean.base.int.convert (s.promote t) a
  let b ← JuliaLean.base.int.convert (s.promote t) b
  pure (a, b)

def promoteMixedTo (r : IntTy) {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt r × JInt r) :=
  promoteMixedSigns (JuliaLean.base.int.remT r.toSigned) JuliaLean.base.int.abs
    (fun a b => do
      let a ← JuliaLean.base.int.convert r a
      let b ← JuliaLean.base.int.convert r b
      pure (a, b)) a b

def promoteMixedBits {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (s.promote t) × JInt (s.promote t)) :=
  promoteMixedTo (s.promote t) a b

def gcdMixedBits {s t : IntTy} (a : JInt s) (b : JInt t) : Jl (JInt (s.promote t)) :=
  if s.signed && !t.signed then gcd_Signed_Unsigned promoteMixedBits gcd_BitInteger a b
  else if !s.signed && t.signed then
    gcd_Unsigned_Signed (gcd_Signed_Unsigned (promoteMixedTo (s.promote t)) gcd_BitInteger) a b
  else gcd_Real promoteBits gcd_BitInteger a b

def lcmMixedBits {s t : IntTy} (a : JInt s) (b : JInt t) : Jl (JInt (s.promote t)) :=
  if s.signed && !t.signed then lcm_Signed_Unsigned promoteMixedBits lcmBits a b
  else if !s.signed && t.signed then lcm_Unsigned_Signed JuliaLean.base.int.abs promoteBits lcmBits a b
  else lcm_Real promoteBits lcmBits a b

def gcdxMixedBits {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (s.promote t) × JInt (s.promote t) × JInt (s.promote t)) := do
  let r := s.promote t
  if s.signed && !t.signed then
    gcdx_Signed_Unsigned promoteMixedBits gcdxBits (fun x => decide (x.val < 0)) r.signed
      JuliaLean.base.int.subWrap (JuliaLean.base.int.ofBool s)
      (fun u sign => if sign.val < 0 then JuliaLean.base.int.neg u else u) a b
  else if !s.signed && t.signed then
    gcdx_Unsigned_Signed
      (gcdx_Signed_Unsigned (promoteMixedTo r) gcdxBits (fun x => decide (x.val < 0)) r.signed
        JuliaLean.base.int.subWrap (JuliaLean.base.int.ofBool t)
        (fun u sign => if sign.val < 0 then JuliaLean.base.int.neg u else u)) a b
  else gcdx_Real promoteBits gcdxBits a b

def powerBits {t e : IntTy} (x : JInt t) (p : JInt e) : Jl (JInt t) :=
  powerBySquaring (bitsOps e) (fun x y => pure (JuliaLean.base.int.mul x y)) true
    (fun x => pure x) (fun x => pure x) (fun x => pure x) id
    (fun _ => JuliaLean.base.int.lit t 1) (fun x => pure (JuliaLean.base.int.neg x))
    (fun x => decide (x.val = 1)) (fun x y => pure (JuliaLean.base.int.mul x y)) true
    x p throwPowerDomain_Integer

def powerBig (x p : Int) : Jl Int :=
  powerBySquaring bigOps (fun x y => pure (x * y)) true pure pure pure id
    (fun _ => 1) (fun x => pure (Int.neg x)) (fun x => decide (x = 1)) (fun x y => pure (x * y)) true
    x p throwPowerDomain_Integer

def nextpow2Bits {t : IntTy} (x : JInt t) : JInt t :=
  nextpow2_Integer Subtype.val JuliaLean.base.int.neg JuliaLean.base.int.unsigned
    JuliaLean.base.int.neg
    (nextpow2_Unsigned (fun _ => JuliaLean.base.int.lit t.toUnsigned 1)
      JuliaLean.base.int.sub topBit (fun x n => JuliaLean.base.int.shl_int x (JuliaLean.base.int.lit .i64 n)))
    (JuliaLean.base.int.remT t) x

def prevpow2Bits {t : IntTy} (x : JInt t) : JInt t :=
  prevpow2_Integer Subtype.val JuliaLean.base.int.neg JuliaLean.base.int.unsigned
    JuliaLean.base.int.neg
    (prevpow2_Unsigned (fun _ => JuliaLean.base.int.lit t.toUnsigned 1) (fun x => (topBit x : Int))
      (fun z => (JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .i64 z)).val.toNat)
      (fun x n => JuliaLean.base.int.shl_int x (JuliaLean.base.int.lit .u64 n)))
    (JuliaLean.base.int.remT t) x

def ispow2Bits {t : IntTy} (x : JInt t) : Bool :=
  ispow2_Integer Subtype.val (fun x => (JuliaLean.base.int.ctpop_int x).val.toNat) x

def nextpowBits {a x : IntTy} (ceilLog : JInt a → JInt x → Jl Int)
    (base : JInt a) (input : JInt x) : Jl Int :=
  nextpow (fun x => decide (x.val ≤ 0)) (fun a => decide (a.val = 2)) true
    (fun x => pure (nextpow2Bits x).val) (fun a => decide (a.val ≤ 1)) (fun x => decide (x.val ≤ 1))
    (fun _ => 1) ceilLog (fun a n => (powerBySquaring bigOps
      (fun a b => pure (JuliaLean.base.int.mul a b)) true pure pure pure id
      (fun _ => JuliaLean.base.int.lit _ 1) (fun x => pure (JuliaLean.base.int.neg x))
      (fun x => decide (x.val = 1)) (fun a b => pure (JuliaLean.base.int.mul a b)) true
      a n throwPowerDomain_Integer).map Subtype.val)
    (fun _ => hasTypeMax true true) (fun x _ => decide (x.val > a.max))
    (fun p x => decide (p ≥ x.val)) (fun p q => decide (p > q)) base input

def prevpowBits {a x : IntTy} (floorLog : JInt a → JInt x → Jl Int)
    (base : JInt a) (input : JInt x) : Jl Int :=
  prevpow (fun x => decide (x.val < 1)) (fun a => decide (a.val = 2)) true
    (fun x => pure (prevpow2Bits x).val) (fun a => decide (a.val ≤ 1)) floorLog
    (fun a n => (powerBySquaring bigOps
      (fun a b => pure (JuliaLean.base.int.mul a b)) true pure pure pure id
      (fun _ => JuliaLean.base.int.lit _ 1) (fun x => pure (JuliaLean.base.int.neg x))
      (fun x => decide (x.val = 1)) (fun a b => pure (JuliaLean.base.int.mul a b)) true
      a n throwPowerDomain_Integer).map Subtype.val)
    (fun _ => hasTypeMax true true) (fun x _ => decide (x.val > a.max)) true
    (fun a p => do
      let (result, overflow) ← JuliaLean.base.checked.mulWithOverflowBits a (JuliaLean.base.int.lit _ p)
      pure (result.val, overflow)) (fun p x => decide (p ≤ x.val)) base input

def decimalBits {t : IntTy} (x : JInt t) : Jl JInt64 :=
  if h : t.bits = 128 then
    bitNdigits128 (ndigitsDecimal_Unsigned (fun x => bitNdigits64 x (by decide) (by decide)))
      JuliaLean.base.int.divSame (JuliaLean.base.int.remT .u128 x)
  else bitNdigits64 (JuliaLean.base.int.remT t.toUnsigned x)
    (by cases t <;> rfl)
    (by cases t <;> simp_all [IntTy.bits, IntTy.toUnsigned])

structure DigitCallees where
  quotient : IntTy → IntTy → Bool → Bool → Int → Int → Jl Int

/-- The divisor operations come from `base/div.jl`; both argument types remain explicit. -/
def ndigitsNegativeBits (c : DigitCallees) {t b : IntTy} (x : JInt t) (base : JInt b) : Jl JInt64 :=
  ndigitsNegative Subtype.val (!t.signed) JuliaLean.base.int.neg
    (fun x base => (c.quotient t b false true x.val base.val).map (JuliaLean.base.int.lit t))
    (fun x => (JuliaLean.base.int.signed x).val) Int.neg Subtype.val id
    (fun x base => c.quotient t.toSigned b true false x base.val) x base

def ndigitsPositiveBits {t b : IntTy} (x : JInt t) (base : JInt b) : Jl JInt64 :=
  ndigitsPositive Subtype.val (JuliaLean.base.int.convert .i64) JuliaLean.base.int.abs true
    JuliaLean.base.int.unsigned JuliaLean.base.int.unsigned Subtype.val topBit
    (fun x => (JuliaLean.base.int.ctlz_int x).val.toNat) (fun _ => t.bits / 8) decimalBits
    (fun x b => if b.val = 0 then .error .divideError
      else pure (JuliaLean.base.int.lit t.toUnsigned (x.val.tdiv b.val)))
    ispow2Bits (fun b => (JuliaLean.base.int.cttz_int b).val.toNat) x base

def ndigitsZeroBits (c : DigitCallees) {t b : IntTy} (x : JInt t) (base : JInt b) : Jl JInt64 :=
  ndigitsZero Subtype.val (ndigitsNegativeBits c) ndigitsPositiveBits x base

def ndigitsBits (c : DigitCallees) {t b p : IntTy} (x : JInt t) (base : JInt b) (pad : JInt p) : Jl Int :=
  ndigits (ndigitsZeroBits c) (fun pad d => pure (max pad.val d.val)) x base pad

def unsignedDivrem {t : IntTy} (x : JInt t) (d : Nat) : Jl (JInt t × Nat) :=
  if d = 0 then .error .divideError
  else pure (JuliaLean.base.int.lit t (x.val.tdiv d), (x.val.tmod d).toNat)

def formatBin {t : IntTy} (x : JInt t) (pad : JInt64) (neg : Bool) : Jl Buffer :=
  bin topBit (fun x => (JuliaLean.base.int.remT .u8 x).val.toNat)
    (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) x pad neg

def formatOct {t : IntTy} (x : JInt t) (pad : JInt64) (neg : Bool) : Jl Buffer :=
  oct topBit (fun x => (JuliaLean.base.int.remT .u8 x).val.toNat)
    (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) x pad neg

def formatHex {t : IntTy} (x : JInt t) (pad : JInt64) (neg : Bool) : Jl Buffer :=
  hex topBit (fun x => (JuliaLean.base.int.remT .u8 x).val.toNat)
    (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) x pad neg

def formatDec (c : DigitCallees) {t : IntTy} (x : JInt t) (pad : JInt64) (neg : Bool) : Jl Buffer :=
  dec Subtype.val unsignedDivrem
    (fun x pad => do pure (JuliaLean.base.int.lit .i64 (← ndigitsBits c x (JuliaLean.base.int.lit .i64 10) pad)))
    (JuliaLean.base.int.remT .u64) x pad neg

def formatBase (c : DigitCallees) {t b : IntTy} (base : JInt b) (x : JInt t)
    (pad : JInt64) (neg : Bool) : Jl Buffer :=
  baseString (bitsOps t) (bitsOps b) (JuliaLean.base.int.remT .i64)
    (fun x b => if b = 0 then .error .divideError else pure (x.val.tmod b))
    (fun x b => if b = 0 then .error .divideError else pure (JuliaLean.base.int.lit t (x.val.tdiv b)))
    (fun x b => if b = 0 then .error .divideError else pure (x.val % b))
    (fun x b => if b = 0 then .error .divideError else pure (JuliaLean.base.int.lit t (-(x.val / (-b)))))
    (fun x base pad => do pure (JuliaLean.base.int.lit .i64 (← ndigitsBits c x base pad)))
    base x pad neg

def sameDivIntfuncs {a b : IntTy} (x : JInt a) (y : JInt b) : Jl (JInt (a.promote b)) :=
  let (x, y) := JuliaLean.base.int.promoteSameSign x y
  JuliaLean.base.div.divDefaultBitInteger x y

def divByUnsigned : (t : IntTy) → JInt t → JInt t.toUnsigned → Jl (JInt t)
  | .i8, x, g => JuliaLean.base.int.div_BitSigned_Unsigned sameDivIntfuncs x g
  | .i16, x, g => JuliaLean.base.int.div_BitSigned_Unsigned sameDivIntfuncs x g
  | .i32, x, g => JuliaLean.base.int.div_BitSigned_Unsigned sameDivIntfuncs x g
  | .i64, x, g => JuliaLean.base.int.div_BitSigned_Unsigned sameDivIntfuncs x g
  | .i128, x, g => JuliaLean.base.int.div_BitSigned_Unsigned sameDivIntfuncs x g
  | .u8, x, g => JuliaLean.base.div.divDefaultBitInteger x g
  | .u16, x, g => JuliaLean.base.div.divDefaultBitInteger x g
  | .u32, x, g => JuliaLean.base.div.divDefaultBitInteger x g
  | .u64, x, g => JuliaLean.base.div.divDefaultBitInteger x g
  | .u128, x, g => JuliaLean.base.div.divDefaultBitInteger x g

def promoteSamePair {A : Type} (x y : A) : A × A :=
  let values := JuliaLean.base.promotion.promoteSameType x y []
  (values[0]'(by simp [values, JuliaLean.base.promotion.promoteSameType]),
   values[1]'(by simp [values, JuliaLean.base.promotion.promoteSameType]))

def bitsIszeroCall {t : IntTy} (x : JInt t) : Jl Bool :=
  JuliaLean.base.number.iszero
    (fun x => .ok (JuliaLean.base.int.zero x))
    (fun x y => .ok (JuliaLean.base.int.eq x y)) x

def stringBits (c : DigitCallees) {t b p : IntTy} (n : JInt t) (base : JInt b) (pad : JInt p) : Jl Buffer :=
  string_Integer Subtype.val Subtype.val Subtype.val
    (splitSign_Integer JuliaLean.base.int.abs JuliaLean.base.int.unsigned Subtype.val)
    unsignedAbs (JuliaLean.base.int.convert t.toSigned) formatBin formatOct (formatDec c) formatHex
    (formatBase c) (formatBase c) n base pad

def bitstringBits {t : IntTy} (x : JInt t) : Jl Buffer :=
  bitstring true t.bits
    (fun x => (JuliaLean.base.int.remT .u8 x).val.toNat)
    (fun x => (JuliaLean.base.int.remT .u8 x).val.toNat)
    (fun x => (JuliaLean.base.int.remT .u8 x).val.toNat)
    (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) x

def digitsBangBits {t b e : IntTy} (a : Vector (JInt e)) (n : JInt t) (base : JInt b) : Jl (Vector (JInt e)) :=
  digitsBang Subtype.val (bitsOps b) (hasTypeMax true true) e.max true (JuliaLean.base.int.convert .i64)
    (fun x => (JuliaLean.base.int.cttz_int x).val.toNat)
    (fun x k mask => (JuliaLean.base.int.band
      (JuliaLean.base.int.shr_Int x (JuliaLean.base.int.lit .i64 k)) (JuliaLean.base.int.lit t mask)).val)
    (fun x base => if base.val = 0 then .error .divideError else
      pure (JuliaLean.base.int.lit t (x.val.tdiv base.val), x.val.tmod base.val))
    (fun x base => if base.val = 0 then .error .divideError else
      pure (JuliaLean.base.int.lit t (x.val / base.val), x.val % base.val))
    (fun x => (JuliaLean.base.int.signed x).val) Int.neg
    (fun x base => if base.val = 0 then .error .divideError else pure (x / base.val, x % base.val))
    (JInt.convert (e.name) e) a n base

def zerosVector {T : Type} (zero : T) (length : Int) : Jl (Vector T) := do
  let length ← JInt.convert (IntTy.i64.name) .i64 length
  if length.val < 0 then .error (.argumentError "")
  else pure ⟨1, List.replicate length.val.toNat zero, []⟩

def digitsBits (c : DigitCallees) {t b p : IntTy} (element : IntTy)
    (n : JInt t) (base : JInt b) (pad : JInt p) : Jl (Vector (JInt element)) :=
  digits_Type (zerosVector (JuliaLean.base.int.lit element 0))
    (fun n base pad => ndigitsBits c n base pad)
    digitsBangBits n base pad

def binomialBits {t : IntTy} (n k : JInt t) : Jl (JInt t) :=
  binomial_Integer (bitsOps t)
    (fun x nn rr => if rr.val = 0 then .error .divideError else pure ((x.val * nn.val).tdiv rr.val))
    (fun x sign => if sign.val < 0 then JuliaLean.base.int.neg x else x) n k

def binomialMixedBits {s k : IntTy} (n : JInt s) (r : JInt k) :
    Jl (JInt (s.promote k)) :=
  binomial_Mixed ⟨promoteBits, binomialBits⟩ n r

/-- Finite-carrier instance of the generic fallback. Julia's public BitInteger dispatch selects
the table methods in `base/combinatorics.jl`. -/
def factorialFallbackBits {t : IntTy} (n : JInt t) : Jl (JInt t) :=
  factorial_Integer Subtype.val (JInt.convert (t.name) t) (fun x y => pure (JuliaLean.base.int.mul x y)) n

def clampBits {t : IntTy} (x lo hi : JInt t) : Jl (JInt t) :=
  clamp (fun x hi => decide (x.val > hi.val)) (fun x lo => decide (x.val < lo.val)) pure pure pure x lo hi

def inverseForBits {t : IntTy} (d : JInt t) :
    Jl (JuliaLean.base.multinverses.BitsMultiplicativeInverse t) :=
  let o := JuliaLean.base.multinverses.bitsCallees divremBits
  if h : t.signed = true then
    match JuliaLean.base.multinverses.multiplicativeinverseSigned
        JuliaLean.base.multinverses.bitDomains o h d with
    | some r => r.map .signed
    | none => .error (.argumentError "nonterminating multiplicativeinverse")
  else
    match JuliaLean.base.multinverses.multiplicativeinverseUnsigned
        JuliaLean.base.multinverses.bitDomains o
        (by cases t <;> simp_all [JuliaLean.base.multinverses.bitDomains, IntTy.signed]) d with
    | some r => r.map .unsigned
    | none => .error (.argumentError "nonterminating multiplicativeinverse")

def magicModBits {t : IntTy} (a b : JInt t)
    (mis : JuliaLean.base.multinverses.BitsMultiplicativeInverse t) :
    Jl (JInt t) := do
  let o := JuliaLean.base.multinverses.bitsCallees divremBits
  let r ← match mis with
    | .signed inverse =>
        JuliaLean.base.multinverses.modSignedInverse o (JuliaLean.base.int.mul a b) inverse
    | .unsigned inverse =>
        JuliaLean.base.multinverses.modUnsignedInverse o (JuliaLean.base.int.mul a b) inverse
  JuliaLean.base.int.convert t r.2

/-! Callees from `base/int.jl`, `base/div.jl`, `base/gmp.jl`, and `base/multinverses.jl`. -/
structure NumberCallees where
  mixedMod : {s t : IntTy} → JInt s → JInt t → Jl Int
  gmpGcdx : Int → Int → Jl (Int × Int × Int)
  gmpPowermod : Int → Int → Int → Jl Int
  magicMod : {t : IntTy} → JInt t → JInt t → JuliaLean.base.multinverses.BitsMultiplicativeInverse t → Jl (JInt t) := magicModBits

def workValue (t : Option IntTy) (n : Int) : Int :=
  match t with
  | some t => (JuliaLean.base.int.lit t n).val
  | none => n

def bezoutWork (c : NumberCallees) (t : Option IntTy) (n m : Int) : Jl Int :=
  match t with
  | some t =>
      (bezoutCoef gcdxBits (fun g => decide (g.val = 1))
        (JuliaLean.base.int.lit t n) (JuliaLean.base.int.lit t m)).map Subtype.val
  | none => bezoutCoef c.gmpGcdx (fun g => decide (g = 1)) n m

def workMod (c : NumberCallees) (t : Option IntTy) (a b : Int) : Jl Int :=
  match t with
  | some t => c.mixedMod (JuliaLean.base.int.lit t a) (JuliaLean.base.int.lit t b)
  | none => if b = 0 then .error .divideError else pure (a % b)
def invmodBits (c : NumberCallees) {s t : IntTy} (n : JInt s) (m : JInt t) : Jl Int :=
  let r := s.promote t
  let st := r.toSigned
  let w := JuliaLean.base.int.widenType st
  invmod_Integer (fun m => decide (m.val = 0)) r.signed (hasTypeMax true true)
    (fun n => decide (n.val ≤ st.max)) (fun m => decide (m.val ≤ st.max))
    (bezoutCoef gcdxMixedBits (fun g => decide (g.val = 1))) c.mixedMod
    (JuliaLean.base.int.remT st) (JuliaLean.base.int.remT st)
    (bezoutCoef gcdxBits (fun g => decide (g.val = 1)))
    (fun x => decide (x.val < 0))
    (fun x m => JuliaLean.base.int.lit st (x.val + (JuliaLean.base.int.abs m).val))
    (fun x => (JuliaLean.base.int.remT r x).val)
    (fun x m => c.mixedMod (JuliaLean.base.int.lit r x) m)
    (fun n => workValue w n.val) (fun m => workValue w m.val)
    (bezoutWork c w) (workMod c w) (fun m => decide (m.val < 0))
    (fun x m => workValue w (x - m.val))
    (fun x => (JuliaLean.base.int.lit r x).val) n m

def powermodBits (c : NumberCallees) {s e t : IntTy}
    (x : JInt s) (p : JInt e) (m : JInt t) : Jl (JInt t) :=
  if t.bits = 128 then
    powermod_128 Subtype.val c.gmpPowermod (JInt.convert (t.name) t) x.val p.val m
  else
    powermod_Integer (bitsOps t) (bitsOps e) Subtype.val
      (fun _ => JuliaLean.base.int.lit t.toUnsigned 1)
      (fun _ => JuliaLean.base.int.lit t.toUnsigned 0) JuliaLean.base.float.uabs
      (fun a b => do JInt.convert (t.name) t (← c.mixedMod a b))
      (fun a mm => do JInt.convert (t.toUnsigned.name) t.toUnsigned (← c.mixedMod a mm))
      (fun a mm => if mm.val = 0 then .error .divideError
        else pure (JuliaLean.base.int.lit t.toUnsigned (a % mm.val)))
      (fun a => JInt.convert (t.name) t a.val)
      (fun a b m => do JInt.convert (t.name) t (← workMod c (JuliaLean.base.int.widenType t) (a.val * b.val) m.val))
      (fun a b m => do JInt.convert (t.name) t (← workMod c (JuliaLean.base.int.widenType t) (a.val * b) m.val))
      (fun a b mm => do
        let productMod ← workMod c (JuliaLean.base.int.widenType t.toUnsigned) (a.val * b.val) mm.val
        JInt.convert (t.toUnsigned.name) t.toUnsigned productMod)
      (invmodBits c)
      (powermodMILegal_Unsigned (hasTypeMax true true) (JuliaLean.base.int.lit t.toUnsigned t.toUnsigned.max)
        (fun a b => decide (a.val ≤ b.val))
        (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) (t.bits / 8))
      (fun _ => t.bits / 8) inverseForBits c.magicMod x p m

def isqrtBits (sqrt : {t : IntTy} → JInt t → Jl (JuliaLean.base.float.FV .f64))
    {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  let trunc := fun f => pure (JuliaLean.base.float.trunc_llvm f)
  let oftype := JuliaLean.base.float.intOfFloat t
  if t.bits = 64 ∨ t.bits = 128 then
    isqrt_Wide sqrt trunc oftype JuliaLean.base.int.divSame x
  else isqrt_Integer sqrt trunc oftype x

def powerFloat (T : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV T) (p : Int) :
    Jl (JuliaLean.base.float.FV T) :=
  powerBySquaring bigOps (fun x y => pure (JuliaLean.base.float.mul_IEEEFloat x y)) true
    pure pure pure id (fun _ => JuliaLean.base.float.one_float T)
    (fun x => pure (JuliaLean.base.float.neg_IEEEFloat x))
    (fun x => JuliaLean.base.float.eq_IEEEFloat x (JuliaLean.base.float.one_float T))
    (fun x y => pure (JuliaLean.base.float.mul_IEEEFloat x y)) true x p throwPowerDomain_Any
def prevpowFloat32 (floorLog : JuliaLean.base.float.FV .f32 → JuliaLean.base.float.FV .f64 → Jl Int)
    (a : JuliaLean.base.float.FV .f32) (x : JuliaLean.base.float.FV .f64) :
    Jl (JuliaLean.base.float.FV .f32) :=
  prevpow
    (fun x => JuliaLean.base.float.lt_IEEEFloat x (JuliaLean.base.float.one_float .f64))
    (fun a => JuliaLean.base.float.eq_IEEEFloat a (JuliaLean.Promotion.Fl.ofInt 2)) false
    (fun _ => .error (.methodError "_prevpow2"))
    (fun a => JuliaLean.base.float.le_IEEEFloat a (JuliaLean.base.float.one_float .f32))
    floorLog (powerFloat .f32) (fun _ => hasTypeMax true true)
    (fun x _ => JuliaLean.base.float.lt_IEEEFloat
      (JuliaLean.base.float.convertFloat .f64 (JuliaLean.base.float.typemax_Float32)) x)
    false (fun a p => pure (JuliaLean.base.float.mul_IEEEFloat a p, false))
    (fun p x => JuliaLean.base.float.le_IEEEFloat (JuliaLean.base.float.convertFloat .f64 p) x) a x

end JuliaLean.base.intfuncs


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-!
Additive, effect-preserving models for the group-16 queue. The installed
`base.io.M` keeps the mutable world on success and failure, and represents
nontermination by outer `none`. Its installed `whileLoop` supplies the actual
recursive language loop; no source algorithm is delegated to an ops field.
Every open operation below is selected on a type not fixed by the source
method. A value carrier may be a tagged union of Julia runtime values, so
assignments and custom methods may change the concrete runtime type.
-/

/-- Open Integer dispatch at `base/intfuncs.jl:44-51`. `notEqualZero` executes
`!=` and the conditional's Bool validation, including TypeError on a non-Bool
result. Those two operations have no intervening source effect. The second
argument is the actual native Int literal zero. `V` includes all intermediate
values, rather than imposing the input method parameter T on assignments. -/
-- Source: base/intfuncs.jl:44-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcd(a::T, b::T) where T<:Integer
--     while b != 0
--         t = b
--         b = rem(a, b)
--         a = t
--     end
--     checked_abs(a)
-- end
-- /Source
structure GcdOps (World V : Type) where
  notEqualZero : V → JInt64 → JuliaLean.base.io.M World Bool
  rem : V → V → JuliaLean.base.io.M World V
  checkedAbs : V → JuliaLean.base.io.M World V

/-- Full generic Euclidean loop, including custom dispatch, exceptions,
state changes and divergence. Julia source: base/intfuncs.jl:44-51. -/
-- Source: base/intfuncs.jl:44-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcd(a::T, b::T) where T<:Integer
--     while b != 0
--         t = b
--         b = rem(a, b)
--         a = t
--     end
--     checked_abs(a)
-- end
-- /Source
def gcdInteger {World V : Type} (ops : GcdOps World V) (a b : V) :
    JuliaLean.base.io.M World V :=
  JuliaLean.base.io.whileLoop (fun (a, b) => do
    if ← ops.notEqualZero b (JuliaLean.base.int.lit .i64 0) then
      let t := b
      let b ← ops.rem a b
      let a := t
      pure (.inr (a, b))
    else
      pure (.inl (← ops.checkedAbs a))) (a, b)

/-- Concrete native-integer instantiation of the open operations in the
generic body, useful also for independent mathematical specifications.
Source reference: base/intfuncs.jl:44-51; base/int.jl's installed primitives
implement the comparison, remainder and checked absolute value. -/
-- Source: base/intfuncs.jl:44-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcd(a::T, b::T) where T<:Integer
--     while b != 0
--         t = b
--         b = rem(a, b)
--         a = t
--     end
--     checked_abs(a)
-- end
-- /Source
def gcdIntegerBitsOps {World : Type} (t : IntTy) : GcdOps World (JInt t) where
  notEqualZero := fun b z => pure (JuliaLean.base.operators.notEqual JuliaLean.base.int.eq Bool.not b z)
  rem := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.int.remSame a b)
  checkedAbs := fun a => JuliaLean.base.io.liftJl (JuliaLean.base.checked.checkedAbsBits a)

/-- Open operations for unsigned absdiff, `base/intfuncs.jl:68-71`.
Different intermediate/result carriers preserve type-changing custom
dispatch; references in D are returned twice without a copy. -/
-- Source: base/intfuncs.jl:68-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function absdiff(x::T,y::T) where {T<:Unsigned}
--     d = max(x,y) - min(x,y)
--     d, d
-- end
-- /Source
structure AbsDiffUnsignedOps (m : Type → Type) (U Max Min D : Type) where
  max : U → U → m Max
  min : U → U → m Min
  sub : Max → Min → m D

/-- Unsigned absdiff with the exact order max, min, subtraction, tuple.
Source reference: base/intfuncs.jl:68-71. -/
-- Source: base/intfuncs.jl:68-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function absdiff(x::T,y::T) where {T<:Unsigned}
--     d = max(x,y) - min(x,y)
--     d, d
-- end
-- /Source
def absdiffUnsigned {m : Type → Type} [Monad m] {U Max Min D : Type}
    (ops : AbsDiffUnsignedOps m U Max Min D) (x y : U) : m (D × D) := do
  let maximum ← ops.max x y
  let minimum ← ops.min x y
  let d ← ops.sub maximum minimum
  pure (d, d)

/-- Open operations for signed absdiff, `base/intfuncs.jl:72-75`.
The original difference reference is retained even if abs changes its type
or mutates aliased state. -/
-- Source: base/intfuncs.jl:72-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function absdiff(x::T,y::T) where {T<:Signed}
--     d = x - y
--     abs(d), d
-- end
-- /Source
structure AbsDiffSignedOps (m : Type → Type) (S D A : Type) where
  sub : S → S → m D
  abs : D → m A

/-- Signed absdiff, including effects/errors of subtraction and absolute
value and heterogeneous custom results. Julia source: base/intfuncs.jl:72-75. -/
-- Source: base/intfuncs.jl:72-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function absdiff(x::T,y::T) where {T<:Signed}
--     d = x - y
--     abs(d), d
-- end
-- /Source
def absdiffSigned {m : Type → Type} [Monad m] {S D A : Type}
    (ops : AbsDiffSignedOps m S D A) (x y : S) : m (A × D) := do
  let d ← ops.sub x y
  let absolute ← ops.abs d
  pure (absolute, d)

/-- Unrestricted source model of the internal binary-GCD method. Every
arithmetic intermediate and shift count keeps its Julia machine type.
The installed fuel-free loop preserves infinite executions on arguments
outside the public gcd caller's established invariants.
Source reference: base/intfuncs.jl:80-95. -/
-- Source: base/intfuncs.jl:80-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :terminates_locally function _gcd(ain::T, bin::T) where T<:BitInteger
--     zb = trailing_zeros(bin)
--     za = trailing_zeros(ain)
--     a = abs(ain)
--     b = abs(bin >> zb)
--     k = min(za, zb)
--     while a != 0
--         a >>= za
--         absd, diff = absdiff(a, b)
--         za = trailing_zeros(diff)
--         b = min(a, b)
--         a = absd
--     end
--     r = b << k
--     return r % T
-- end
-- /Source
def binaryGcd {World : Type} {t : IntTy} (ain bin : JInt t) :
    JuliaLean.base.io.M World (JInt t) := do
  let zb := JuliaLean.base.int.trailing_zeros bin
  let za := JuliaLean.base.int.trailing_zeros ain
  let a := JuliaLean.base.int.abs ain
  let b := JuliaLean.base.int.abs (JuliaLean.base.int.shr_Int bin zb)
  let k := JuliaLean.base.intfuncs.minBits za zb
  let b ← JuliaLean.base.io.whileLoop (fun (a, b, za) => do
    if JuliaLean.base.operators.notEqual JuliaLean.base.int.eq Bool.not a
        (JuliaLean.base.int.lit .i64 0) then
      let a := JuliaLean.base.int.shr_Int a za
      let (absd, diff) := if t.signed then
          JuliaLean.base.intfuncs.absdiff_Signed JuliaLean.base.int.sub JuliaLean.base.int.abs a b
        else
          JuliaLean.base.intfuncs.absdiff_Unsigned JuliaLean.base.intfuncs.maxBits
            JuliaLean.base.intfuncs.minBits JuliaLean.base.int.sub a b
      let za := JuliaLean.base.int.trailing_zeros diff
      let b := JuliaLean.base.intfuncs.minBits a b
      let a := absd
      pure (.inr (a, b, za))
    else
      pure (.inl b)) (a, b, za)
  let r := JuliaLean.base.int.shl_int b k
  pure (JuliaLean.base.int.remT t r)

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Effectful Integer operations selected by base/intfuncs.jl:136-144.
The carrier may contain all dynamically returned values. Conditional
comparison fields retain the adjacent Bool assertion and its errors. -/
-- Source: base/intfuncs.jl:136-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function lcm(a::T, b::T) where T<:Integer
--     # explicit a==0 test is to handle case of lcm(0, 0) correctly
--     # explicit b==0 test is to handle case of lcm(typemin(T),0) correctly
--     if a == 0 || b == 0
--         return zero(a)
--     else
--         return checked_abs(checked_mul(a, div(b, gcd(b,a))))
--     end
-- end
-- /Source
structure LcmOps (m : Type → Type) (V : Type) where
  equalZero : V → JInt64 → m Bool
  zero : V → m V
  gcd : V → V → m V
  div : V → V → m V
  checkedMul : V → V → m V
  checkedAbs : V → m V

/-- Full generic LCM composition with left-to-right short-circuiting and
every open dispatch call in its original position.
Source reference: base/intfuncs.jl:136-144. -/
-- Source: base/intfuncs.jl:136-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function lcm(a::T, b::T) where T<:Integer
--     # explicit a==0 test is to handle case of lcm(0, 0) correctly
--     # explicit b==0 test is to handle case of lcm(typemin(T),0) correctly
--     if a == 0 || b == 0
--         return zero(a)
--     else
--         return checked_abs(checked_mul(a, div(b, gcd(b,a))))
--     end
-- end
-- /Source
def lcmInteger {m : Type → Type} [Monad m] {V : Type}
    (ops : LcmOps m V) (a b : V) : m V := do
  if ← ops.equalZero a (JuliaLean.base.int.lit .i64 0) then
    ops.zero a
  else if ← ops.equalZero b (JuliaLean.base.int.lit .i64 0) then
    ops.zero a
  else
    let d ← ops.gcd b a
    let quotient ← ops.div b d
    let product ← ops.checkedMul a quotient
    ops.checkedAbs product

/-- Concrete native operations for the generic LCM body. The public
BitInteger gcd call uses its installed faithful model.
Source reference: base/intfuncs.jl:136-144. -/
-- Source: base/intfuncs.jl:136-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function lcm(a::T, b::T) where T<:Integer
--     # explicit a==0 test is to handle case of lcm(0, 0) correctly
--     # explicit b==0 test is to handle case of lcm(typemin(T),0) correctly
--     if a == 0 || b == 0
--         return zero(a)
--     else
--         return checked_abs(checked_mul(a, div(b, gcd(b,a))))
--     end
-- end
-- /Source
def lcmIntegerBitsOps {World : Type} (t : IntTy) :
    LcmOps (JuliaLean.base.io.M World) (JInt t) where
  equalZero := fun a z => pure (JuliaLean.base.int.eq a z)
  zero := fun a => pure (JuliaLean.base.int.zero a)
  gcd := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.gcd_BitInteger a b)
  div := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.int.divSame a b)
  checkedMul := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.checked.checkedMulBits a b)
  checkedAbs := fun a => JuliaLean.base.io.liftJl (JuliaLean.base.checked.checkedAbsBits a)

/-- Open checked_abs dispatch for base/intfuncs.jl:152. The result carrier
need not be the same as the Integer input carrier. -/
-- Source: base/intfuncs.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Integer) = checked_abs(a)
-- /Source
structure UnaryGcdOps (m : Type → Type) (I R : Type) where
  checkedAbs : I → m R

/-- Unary Integer gcd, including effects and heterogeneous custom results.
Source reference: base/intfuncs.jl:152. -/
-- Source: base/intfuncs.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Integer) = checked_abs(a)
-- /Source
def gcdUnaryInteger {m : Type → Type} {I R : Type}
    (ops : UnaryGcdOps m I R) (a : I) : m R :=
  ops.checkedAbs a

/-- The fixed immutable field storage of Rational{I}; every raw pair is
retained because unsafe_rational does not normalize or validate it. This is
structurally the same storage as JuliaLean.base.rational.Rational, which is
defined in a downstream module importing intfuncs and cannot be imported
here without a cycle. It is a representation dependency, not a replacement
Rational constructor or an arbitrary field-projection interface.
Source reference: base/rational.jl:9-15. -/
-- Source: base/rational.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Rational{T<:Integer} <: Real
--     num::T
--     den::T
-- 
--     # Unexported inner constructor of Rational that bypasses all checks
--     global unsafe_rational(::Type{T}, num, den) where {T} = new{T}(num, den)
-- end
-- /Source
structure RationalStorage (I : Type) where
  num : I
  den : I

/-- Arithmetic dispatch for base/intfuncs.jl:153. The unspecified component
type I and checked-absolute-value result U choose these methods; the fixed
Rational field accesses are implemented directly. -/
-- Source: base/intfuncs.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Rational) = checked_abs(a.num) // a.den
-- /Source
structure RationalUnaryOps (m : Type → Type) (I U R : Type) where
  checkedAbs : I → m U
  ratio : U → I → m R

/-- Unary Rational gcd with concrete field reads and effectful arithmetic
dispatch. No normalization restriction is added to the input fields.
Source reference: base/intfuncs.jl:153. -/
-- Source: base/intfuncs.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Rational) = checked_abs(a.num) // a.den
-- /Source
def gcdUnaryRational {m : Type → Type} [Monad m] {I U R : Type}
    (ops : RationalUnaryOps m I U R) (a : RationalStorage I) : m R := do
  let numerator ← ops.checkedAbs a.num
  ops.ratio numerator a.den

/-- Open unary gcd dispatch selected on the Integer or Rational argument
of base/intfuncs.jl:154, including user-defined Integer types. -/
-- Source: base/intfuncs.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lcm(a::Union{Integer,Rational}) = gcd(a)
-- /Source
structure UnaryLcmOps (m : Type → Type) (A R : Type) where
  gcd : A → m R

/-- Unary lcm preserves the selected unary gcd's result and effects.
Source reference: base/intfuncs.jl:154. -/
-- Source: base/intfuncs.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lcm(a::Union{Integer,Rational}) = gcd(a)
-- /Source
def lcmUnary {m : Type → Type} {A R : Type}
    (ops : UnaryLcmOps m A R) (a : A) : m R :=
  ops.gcd a

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Fixed function identities in base/intfuncs.jl:159-162. -/
-- Source: base/intfuncs.jl:159-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real) = gcd(promote(a,b)...)
-- lcm(a::Real, b::Real) = lcm(promote(a,b)...)
-- gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
-- lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
-- /Source
inductive NumberTheoryFunction where
  | gcd | lcm
  deriving DecidableEq, BEq

/-- The Base.iterate function passed by source lowering at
base/intfuncs.jl:159-160 to Core._apply_iterate. -/
-- Source: base/intfuncs.jl:159-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real) = gcd(promote(a,b)...)
-- lcm(a::Real, b::Real) = lcm(promote(a,b)...)
-- /Source
inductive IterateToken where
  | baseIterate
  deriving DecidableEq, BEq

/-- Typed projection of the existing Core runtime application boundary
JuliaLean.base.boot.CoreOps.applyIterate. Arguments correspond to the iterate
token and [function, promotedValue] in that interface. Promote can return any
P, including arbitrary tuples, other iterables, or values causing errors.
The established primitive includes iteration and allocation effects/errors,
arity errors, selected method dispatch, and divergence. This parameter is
not an implementation of either surrounding source method, whose body is
explicit below. Julia source: base/intfuncs.jl:159-160. -/
-- Source: base/intfuncs.jl:159-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real) = gcd(promote(a,b)...)
-- lcm(a::Real, b::Real) = lcm(promote(a,b)...)
-- /Source
structure PromoteApplyOps (m : Type → Type) (A B P R : Type) where
  promote : A → B → m P
  applyIterate : IterateToken → NumberTheoryFunction → P → m R

/-- Full promotion then runtime splat/application. A custom promote result
is not restricted to a pair. Julia source: base/intfuncs.jl:159. -/
-- Source: base/intfuncs.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real) = gcd(promote(a,b)...)
-- /Source
def gcdReal {m : Type → Type} [Monad m] {A B P R : Type}
    (ops : PromoteApplyOps m A B P R) (a : A) (b : B) : m R := do
  let promoted ← ops.promote a b
  ops.applyIterate .baseIterate .gcd promoted

/-- Real lcm fixes its actual function identity at the existing Core
application boundary. Julia source: base/intfuncs.jl:160. -/
-- Source: base/intfuncs.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lcm(a::Real, b::Real) = lcm(promote(a,b)...)
-- /Source
def lcmReal {m : Type → Type} [Monad m] {A B P R : Type}
    (ops : PromoteApplyOps m A B P R) (a : A) (b : B) : m R := do
  let promoted ← ops.promote a b
  ops.applyIterate .baseIterate .lcm promoted

/-- Native two-tuples use structural splatting and installed native calls;
this adapter imposes no shape constraint on the generic models above.
Source reference: base/intfuncs.jl:159-160. -/
-- Source: base/intfuncs.jl:159-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real) = gcd(promote(a,b)...)
-- lcm(a::Real, b::Real) = lcm(promote(a,b)...)
-- /Source
def promoteApplyBitsOps {World : Type} (s t : IntTy) :
    PromoteApplyOps (JuliaLean.base.io.M World) (JInt s) (JInt t)
      (JInt (s.promote t) × JInt (s.promote t)) (JInt (s.promote t)) where
  promote := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.promoteBits a b)
  applyIterate := fun .baseIterate fn (a, b) =>
    match fn with
    | .gcd => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.gcd_BitInteger a b)
    | .lcm => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.lcmBits a b)

/-- A constructible rest tuple; the bound includes the two fixed arguments.
Nat describes representation and Lean recursion, not Julia arithmetic.
Source reference: base/intfuncs.jl:161-162. -/
-- Source: base/intfuncs.jl:161-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
-- lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
-- /Source
structure Varargs (V : Type) where
  values : List V
  nativeArity : values.length + 2 ≤ 2 ^ 63 - 1

/-- Runtime selection on unknown Real types. Unary/binary operations remain
open. For at least three arguments, some action denotes an actually selected
custom method; none selects the generic method and the recursion below.
Selection does not execute the action. Tagged V permits type-changing
results and shared reference handles. Julia source: base/intfuncs.jl:161-162. -/
-- Source: base/intfuncs.jl:161-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
-- lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
-- /Source
structure NaryOps (m : Type → Type) (V : Type) where
  unary : NumberTheoryFunction → V → m V
  binary : NumberTheoryFunction → V → V → m V
  customNary : NumberTheoryFunction → V → V → List V → Option (m V)

/-- Actual source recursion, with a separate route only for an actually
selected custom n-ary method. Effects/errors of the tail precede outer calls.
Source reference: base/intfuncs.jl:161-162. -/
-- Source: base/intfuncs.jl:161-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
-- lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
-- /Source
def naryTail {m : Type → Type} [Monad m] {V : Type}
    (ops : NaryOps m V) (fn : NumberTheoryFunction) (a : V) : List V → m V
  | [] => ops.unary fn a
  | [b] => ops.binary fn a b
  | b :: c :: cs =>
      match ops.customNary fn a b (c :: cs) with
      | some selected => selected
      | none => do
          let tail ← naryTail ops fn b (c :: cs)
          ops.binary fn a tail

/-- The selected generic n-ary gcd body, including empty rest arguments
allowed by the signature. Julia source: base/intfuncs.jl:161. -/
-- Source: base/intfuncs.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
-- /Source
def gcdNary {m : Type → Type} [Monad m] {V : Type}
    (ops : NaryOps m V) (a b : V) (cs : Varargs V) : m V := do
  let tail ← naryTail ops .gcd b cs.values
  ops.binary .gcd a tail

/-- Selected generic n-ary lcm with real recursive-tail dispatch.
Source reference: base/intfuncs.jl:162. -/
-- Source: base/intfuncs.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
-- /Source
def lcmNary {m : Type → Type} [Monad m] {V : Type}
    (ops : NaryOps m V) (a b : V) (cs : Varargs V) : m V := do
  let tail ← naryTail ops .lcm b cs.values
  ops.binary .lcm a tail

/-- Native types select the generic n-ary body and installed unary/binary
Base methods; no fake custom implementation is supplied.
Source reference: base/intfuncs.jl:152,154,161-162. -/
-- Source: base/intfuncs.jl:161-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(a::Real, b::Real, c::Real...) = gcd(a, gcd(b, c...))
-- lcm(a::Real, b::Real, c::Real...) = lcm(a, lcm(b, c...))
-- /Source
def naryBitsOps {World : Type} (t : IntTy) :
    NaryOps (JuliaLean.base.io.M World) (JInt t) where
  unary := fun fn a => match fn with
    | .gcd => JuliaLean.base.io.liftJl
        (JuliaLean.base.intfuncs.gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits a)
    | .lcm => JuliaLean.base.io.liftJl
        (JuliaLean.base.intfuncs.lcm_Unary
          (JuliaLean.base.intfuncs.gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits) a)
  binary := fun fn a b => match fn with
    | .gcd => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.gcd_BitInteger a b)
    | .lcm => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.lcmBits a b)
  customNary := fun _ _ _ _ => none

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Open AbstractArray/type operations for base/intfuncs.jl:166. Array
handles retain arbitrary indexing conventions; the reduce method is selected
on the unknown array type. The operator token retains function identity. -/
-- Source: base/intfuncs.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(abc::AbstractArray{<:Real}) = reduce(gcd, abc; init=zero(eltype(abc)))
-- /Source
structure GcdArrayOps (m : Type → Type) (A Ty Init R : Type) where
  eltype : A → m Ty
  zero : Ty → m Init
  reduceWithInit : NumberTheoryFunction → A → Init → m R

/-- Real-array gcd evaluates its keyword initializer before reduction.
Source reference: base/intfuncs.jl:166. -/
-- Source: base/intfuncs.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcd(abc::AbstractArray{<:Real}) = reduce(gcd, abc; init=zero(eltype(abc)))
-- /Source
def gcdArray {m : Type → Type} [Monad m] {A Ty Init R : Type}
    (ops : GcdArrayOps m A Ty Init R) (abc : A) : m R := do
  let elementType ← ops.eltype abc
  let initial ← ops.zero elementType
  ops.reduceWithInit .gcd abc initial

/-- Fixed Integer type identity passed to Core subtype, at
base/intfuncs.jl:171. -/
-- Source: base/intfuncs.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         eltype(abc) <: Integer && return one(eltype(abc))
-- /Source
inductive TypeToken where
  | integer
  deriving BEq, DecidableEq

/-- Effectful dispatch at base/intfuncs.jl:167-176. Length L need not be
native Int. `equal` includes conditional Bool validation. `subtype` projects
the existing Core subtype primitive, including invalid-type errors, with
its Integer argument explicit. `string` retains interpolation effects before
the local throw. No selected user callee has an assumed correctness law. -/
-- Source: base/intfuncs.jl:167-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function lcm(abc::AbstractArray{<:Real})
--     # Using reduce with init=one(eltype(abc)) is buggy for Rationals.
--     l = length(abc)
--     if l == 0
--         eltype(abc) <: Integer && return one(eltype(abc))
--         throw(ArgumentError("lcm has no identity for $(eltype(abc))"))
--     end
--     l == 1 && return abs(only(abc))
--     return reduce(lcm, abc)
-- end
-- /Source
structure LcmArrayOps (m : Type → Type) (A L Ty V R : Type) where
  length : A → m L
  equal : L → JInt64 → m Bool
  eltype : A → m Ty
  subtype : Ty → TypeToken → m Bool
  one : Ty → m R
  string : String → Ty → m String
  only : A → m V
  abs : V → m R
  reduceWithoutInit : NumberTheoryFunction → A → m R

/-- Full real-array lcm. Empty paths have two distinct effectful eltype
calls. Interpolation precedes ArgumentError; a singleton calls only before
abs; longer arrays use reduce without an initializer.
Source reference: base/intfuncs.jl:167-176. -/
-- Source: base/intfuncs.jl:167-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function lcm(abc::AbstractArray{<:Real})
--     # Using reduce with init=one(eltype(abc)) is buggy for Rationals.
--     l = length(abc)
--     if l == 0
--         eltype(abc) <: Integer && return one(eltype(abc))
--         throw(ArgumentError("lcm has no identity for $(eltype(abc))"))
--     end
--     l == 1 && return abs(only(abc))
--     return reduce(lcm, abc)
-- end
-- /Source
def lcmArray {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.io.Error m]
    {A L Ty V R : Type} (ops : LcmArrayOps m A L Ty V R) (abc : A) : m R := do
  let length ← ops.length abc
  if ← ops.equal length (JuliaLean.base.int.lit .i64 0) then
    let firstType ← ops.eltype abc
    if ← ops.subtype firstType .integer then
      let secondType ← ops.eltype abc
      ops.one secondType
    else
      let secondType ← ops.eltype abc
      let message ← ops.string "lcm has no identity for " secondType
      throw (.jl (.argumentError message))
  else if ← ops.equal length (JuliaLean.base.int.lit .i64 1) then
    let value ← ops.only abc
    ops.abs value
  else
    ops.reduceWithoutInit .lcm abc

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Open unsigned coefficient-update leaves. Multiplication may return a
new runtime type, and subtraction may return yet another. The original three
arguments have the same selected Unsigned type.
Source reference: base/intfuncs.jl:189. -/
-- Source: base/intfuncs.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
-- /Source
structure GcdxUnsignedUpdateOps (m : Type → Type) (U Product R : Type) where
  mulWrap : U → U → m Product
  subWrap : U → Product → m R

/-- Unsigned coefficient update with multiplication before subtraction,
retaining all selected-operation effects, errors and result types.
Source reference: base/intfuncs.jl:189. -/
-- Source: base/intfuncs.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
-- /Source
def gcdxUpdateUnsigned {m : Type → Type} [Monad m] {U Product R : Type}
    (ops : GcdxUnsignedUpdateOps m U Product R) (s0 q s1 : U) : m R := do
  let product ← ops.mulWrap q s1
  ops.subWrap s0 product

/-- Open generic coefficient-update leaves. The method imposes no common
argument type, and each selected operation may change the result type.
Source reference: base/intfuncs.jl:190. -/
-- Source: base/intfuncs.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0, q, s1) = s0 - q*s1
-- /Source
structure GcdxGenericUpdateOps (m : Type → Type) (S0 Q S1 Product R : Type) where
  mul : Q → S1 → m Product
  sub : S0 → Product → m R

/-- Generic coefficient update, preserving multiplication/subtraction
order, heterogeneous arguments and arbitrary selected-operation effects.
Source reference: base/intfuncs.jl:190. -/
-- Source: base/intfuncs.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0, q, s1) = s0 - q*s1
-- /Source
def gcdxUpdateGeneric {m : Type → Type} [Monad m] {S0 Q S1 Product R : Type}
    (ops : GcdxGenericUpdateOps m S0 Q S1 Product R)
    (s0 : S0) (q : Q) (s1 : S1) : m R := do
  let product ← ops.mul q s1
  ops.sub s0 product

/-- Runtime-selected update method. Only an actually selected custom
method carries code; the two known source methods are implemented below.
A dynamic V may tag different runtime types and shared references.
Source reference: base/intfuncs.jl:189-190. -/
-- Source: base/intfuncs.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
-- _gcdx_update(s0, q, s1) = s0 - q*s1
-- /Source
inductive GcdxUpdateRoute (m : Type → Type) (V : Type) where
  | generic
  | unsigned
  | custom (callee : V → V → V → m V)

/-- Open operator dispatch and pure method selection for the update call.
Selection inspects runtime argument types but does not execute the method.
Source reference: base/intfuncs.jl:189-190. -/
-- Source: base/intfuncs.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
-- _gcdx_update(s0, q, s1) = s0 - q*s1
-- /Source
structure GcdxUpdateDispatchOps (m : Type → Type) (V : Type) where
  generic : GcdxGenericUpdateOps m V V V V V
  unsigned : GcdxUnsignedUpdateOps m V V V
  select : V → V → V → GcdxUpdateRoute m V

/-- Closed dispatch to the complete generic/unsigned update bodies.
Custom-selected code receives exactly the original three operands.
Source reference: base/intfuncs.jl:189-190,251-252. -/
-- Source: base/intfuncs.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
-- _gcdx_update(s0, q, s1) = s0 - q*s1
-- /Source
def gcdxUpdateSelected {m : Type → Type} [Monad m] {V : Type}
    (ops : GcdxUpdateDispatchOps m V) (s0 q s1 : V) : m V :=
  match ops.select s0 q s1 with
  | .generic => gcdxUpdateGeneric ops.generic s0 q s1
  | .unsigned => gcdxUpdateUnsigned ops.unsigned s0 q s1
  | .custom callee => callee s0 q s1

/-- Use the installed conditional Bool assertion at the source branch.
Non-Bool results retain TypeError, including mutations already performed by
the predicate. Other retains arbitrary non-Bool result identities.
Source reference: base/intfuncs.jl:236-242,248,255-258. -/
-- Source: base/intfuncs.jl:235-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@assume_effects :terminates_locally function gcdx(a::T, b::T) where {T<:Integer}
--     if iszero(a) && iszero(b)
--         return (zero(T), zero(T), zero(T))
--     elseif isone(abs(b))
--         # handles (typemin(::Signed), -1)
--         return (one(T), zero(T), b)
--     elseif isone(abs(a))
--         return (one(T), a, zero(T))
-- /Source
def gcdxAssertBool {World Other : Type} (value : Bool ⊕ Other) :
    JuliaLean.base.io.M World Bool :=
  match JuliaLean.base.reduce.assertBool value with
  | .ok result => pure result
  | .error .typeError => throw (.foreignError "TypeError" "")

/-- The loop's explicit logical negation. Known Bool values call the
installed primitive-backed Bool model. Only a selected non-Bool ! operation
is open; its result is subsequently asserted as Bool by the loop.
Source reference: base/intfuncs.jl:248. -/
-- Source: base/intfuncs.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     while !iszero(b)
-- /Source
def gcdxLogicalNot {World Other : Type}
    (notOther : Other → JuliaLean.base.io.M World (Bool ⊕ Other)) :
    Bool ⊕ Other → JuliaLean.base.io.M World (Bool ⊕ Other)
  | .inl value => pure (.inl
      (JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool value))
  | .inr value => notOther value

/-- Operations selected by the generic Integer method. V contains every
arithmetic intermediate and shared reference, D every divrem result, and
IterState its destructuring state; no divrem pair-shape law is assumed.
Indexed-iterate fields include the required Core field extraction and
propagate malformed-return errors. The first call extracts value and state;
the final call extracts only the value, without requiring an unused second
field. The first call has no state argument, and the next call receives
exactly the state observed from the first.
The nullary type operations close over the method's original T and execute
afresh on every occurrence. Predicate values retain non-Bool alternatives,
including custom ! dispatch before the while condition's Bool assertion.
Source reference: base/intfuncs.jl:235-260. -/
-- Source: base/intfuncs.jl:235-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@assume_effects :terminates_locally function gcdx(a::T, b::T) where {T<:Integer}
--     if iszero(a) && iszero(b)
--         return (zero(T), zero(T), zero(T))
--     elseif isone(abs(b))
--         # handles (typemin(::Signed), -1)
--         return (one(T), zero(T), b)
--     elseif isone(abs(a))
--         return (one(T), a, zero(T))
--     end
--     # a0, b0 = a, b
--     s0, s1 = oneunit(T), zero(T)
--     t0, t1 = s1, s0
--     # The loop invariant is: s0*a0 + t0*b0 == a && s1*a0 + t1*b0 == b
--     while !iszero(b)
--         q, r = divrem(a, b)
--         a, b = b, r
--         s0, s1 = s1, _gcdx_update(s0, q, s1)
--         t0, t1 = t1, _gcdx_update(t0, q, t1)
--     end
--     # for cases like abs(Int8(-128))
--     if isnegative(a) && isnegative(abs(a))
--         throw(DomainError((a, b), LazyString("gcd not representable in ", T)))
--     else
--         return isnegative(a) ? (abs(a), -s0, -t0) : (a, s0, t0)
--     end
-- end
-- /Source
structure GcdxOps (World V D IterState Other : Type) where
  iszero : V → JuliaLean.base.io.M World (Bool ⊕ Other)
  isone : V → JuliaLean.base.io.M World (Bool ⊕ Other)
  abs : V → JuliaLean.base.io.M World V
  isnegative : V → JuliaLean.base.io.M World (Bool ⊕ Other)
  neg : V → JuliaLean.base.io.M World V
  notOther : Other → JuliaLean.base.io.M World (Bool ⊕ Other)
  zeroType : JuliaLean.base.io.M World V
  oneType : JuliaLean.base.io.M World V
  oneunitType : JuliaLean.base.io.M World V
  divrem : V → V → JuliaLean.base.io.M World D
  indexedIterateFirst : D → JInt64 → JuliaLean.base.io.M World (V × IterState)
  indexedIterateNext : D → JInt64 → IterState → JuliaLean.base.io.M World V
  update : GcdxUpdateDispatchOps (JuliaLean.base.io.M World) V

/-- Representation of the six source loop variables, retaining references
without copying their underlying values. Julia source: base/intfuncs.jl:245-253. -/
-- Source: base/intfuncs.jl:245-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     s0, s1 = oneunit(T), zero(T)
--     t0, t1 = s1, s0
--     # The loop invariant is: s0*a0 + t0*b0 == a && s1*a0 + t1*b0 == b
--     while !iszero(b)
--         q, r = divrem(a, b)
--         a, b = b, r
--         s0, s1 = s1, _gcdx_update(s0, q, s1)
--         t0, t1 = t1, _gcdx_update(t0, q, t1)
--     end
-- /Source
structure GcdxState (V : Type) where
  a : V
  b : V
  s0 : V
  s1 : V
  t0 : V
  t1 : V

/-- Complete effectful source method, with genuine fuel-free recursion.
All early return calls, destructuring indices/state, coefficient-update
selection, repeated abs/isnegative calls, error points and tuple evaluation
order remain explicit. DomainError is represented at the established
exception-class boundary; its lazy text and payload are not inspected.
Source reference: base/intfuncs.jl:235-260. -/
-- Source: base/intfuncs.jl:235-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@assume_effects :terminates_locally function gcdx(a::T, b::T) where {T<:Integer}
--     if iszero(a) && iszero(b)
--         return (zero(T), zero(T), zero(T))
--     elseif isone(abs(b))
--         # handles (typemin(::Signed), -1)
--         return (one(T), zero(T), b)
--     elseif isone(abs(a))
--         return (one(T), a, zero(T))
--     end
--     # a0, b0 = a, b
--     s0, s1 = oneunit(T), zero(T)
--     t0, t1 = s1, s0
--     # The loop invariant is: s0*a0 + t0*b0 == a && s1*a0 + t1*b0 == b
--     while !iszero(b)
--         q, r = divrem(a, b)
--         a, b = b, r
--         s0, s1 = s1, _gcdx_update(s0, q, s1)
--         t0, t1 = t1, _gcdx_update(t0, q, t1)
--     end
--     # for cases like abs(Int8(-128))
--     if isnegative(a) && isnegative(abs(a))
--         throw(DomainError((a, b), LazyString("gcd not representable in ", T)))
--     else
--         return isnegative(a) ? (abs(a), -s0, -t0) : (a, s0, t0)
--     end
-- end
-- /Source
def gcdxInteger {World V D IterState Other : Type}
    (ops : GcdxOps World V D IterState Other) (a b : V) :
    JuliaLean.base.io.M World (V × V × V) := do
  let bothZero ← do
    if ← gcdxAssertBool (← ops.iszero a) then
      gcdxAssertBool (← ops.iszero b)
    else pure false
  if bothZero then
    let d ← ops.zeroType
    let u ← ops.zeroType
    let v ← ops.zeroType
    return (d, u, v)
  let absB ← ops.abs b
  if ← gcdxAssertBool (← ops.isone absB) then
    let d ← ops.oneType
    let u ← ops.zeroType
    return (d, u, b)
  let absA ← ops.abs a
  if ← gcdxAssertBool (← ops.isone absA) then
    let d ← ops.oneType
    let v ← ops.zeroType
    return (d, a, v)
  let s0 ← ops.oneunitType
  let s1 ← ops.zeroType
  let t0 := s1
  let t1 := s0
  let final ← JuliaLean.base.io.whileLoop (fun (state : GcdxState V) => do
    let isZero ← ops.iszero state.b
    let notZero ← gcdxLogicalNot ops.notOther isZero
    if ← gcdxAssertBool notZero then
      let divremResult ← ops.divrem state.a state.b
      let (q, iterateState) ← ops.indexedIterateFirst divremResult
        (JuliaLean.base.int.lit .i64 1)
      let r ← ops.indexedIterateNext divremResult
        (JuliaLean.base.int.lit .i64 2) iterateState
      let a := state.b
      let b := r
      let s0 := state.s1
      let s1 ← gcdxUpdateSelected ops.update state.s0 q state.s1
      let t0 := state.t1
      let t1 ← gcdxUpdateSelected ops.update state.t0 q state.t1
      pure (.inr { a, b, s0, s1, t0, t1 })
    else pure (.inl state)) { a, b, s0, s1, t0, t1 }
  let unrepresentable ← do
    if ← gcdxAssertBool (← ops.isnegative final.a) then
      let absolute ← ops.abs final.a
      gcdxAssertBool (← ops.isnegative absolute)
    else pure false
  if unrepresentable then
    throw (.jl (.domainError ""))
  else
    if ← gcdxAssertBool (← ops.isnegative final.a) then
      let d ← ops.abs final.a
      let u ← ops.neg final.s0
      let v ← ops.neg final.t0
      pure (d, u, v)
    else pure (final.a, final.s0, final.t0)

/-- Adapter to the installed zero(T) model for a fixed native T. The
constructor conversion is the installed Int-to-T conversion, not wrapping
an arbitrary mathematical value. Julia dependency: base/number.jl:364;
used by base/intfuncs.jl:237,240,242,245. -/
-- Source: base/number.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zero(::Type{T}) where {T<:Number} = convert(T,0)
-- /Source
def gcdxBitsZero (t : IntTy) : Jl (JInt t) :=
  JuliaLean.base.number.zeroType
    (fun (_ : Unit) value => JuliaLean.base.int.convert t
      (JuliaLean.base.int.lit .i64 value)) ()

/-- Adapter to the installed one(T) model, with the installed native
conversion of the actual Int literal. Julia dependency: base/number.jl:405;
used by base/intfuncs.jl:240,242,245. -/
-- Source: base/number.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- /Source
def gcdxBitsOne (t : IntTy) : Jl (JInt t) :=
  JuliaLean.base.number.oneType
    (fun (_ : Unit) value => JuliaLean.base.int.convert t
      (JuliaLean.base.int.lit .i64 value)) ()

/-- Adapter to installed oneunit(T), retaining its extra T conversion
after one(T). Julia dependency: base/number.jl:431;
used by base/intfuncs.jl:245. -/
-- Source: base/number.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- oneunit(::Type{T}) where {T} = T(one(T))
-- /Source
def gcdxBitsOneunit (t : IntTy) : Jl (JInt t) :=
  JuliaLean.base.number.oneunitType (fun (_ : Unit) => gcdxBitsOne t)
    (fun value => JuliaLean.base.int.convert t value) ()

/-- Exception-class adapter for installed Tuple indexed_iterate. Julia
errors remain Jl errors; additional Tuple runtime error classes retain their
names in the existing IO runtime error interface. No default is substituted.
Julia dependency: base/tuple.jl:161; used by base/intfuncs.jl:249. -/
-- Source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- /Source
def gcdxLiftTuple {World A : Type} : JuliaLean.base.tuple.R A → JuliaLean.base.io.M World A
  | .ok value => pure value
  | .error (.julia error) => throw (.jl error)
  | .error .errorException => throw (.errorException "")
  | .error error => throw (.foreignError error.kind "")

/-- Use the actual installed tuple indexed-iterate model on a constructible
two-element native tuple. Its successful indices are only 1 and 2, so the
returned Int states 2 and 3 fit native Int; the JInt wrapper is a representation
adapter. All bad indices retain the installed BoundsError.
Julia dependency: base/tuple.jl:161; source use base/intfuncs.jl:249. -/
-- Source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- /Source
def gcdxIndexedTuple {World : Type} {t : IntTy} (values : JInt t × JInt t)
    (index : JInt64) (state : Option JInt64) : JuliaLean.base.io.M World (JInt t × JInt64) := do
  let result := match state with
    | none => JuliaLean.base.tuple.indexedIterateTuple [values.1, values.2] index.val
    | some state => JuliaLean.base.tuple.indexedIterateTuple [values.1, values.2] index.val state.val
  let (value, next) ← gcdxLiftTuple result
  pure (value, JuliaLean.base.int.lit .i64 next)

/-- Native update dispatch uses the new complete helper bodies. Every
operator leaf is an installed concrete Base operation; signed multiplication
uses its width-selected model. There is no fictitious custom branch.
Source reference: base/intfuncs.jl:189-190,251-252. -/
-- Source: base/intfuncs.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned} = s0 -% q *% s1
-- _gcdx_update(s0, q, s1) = s0 - q*s1
-- /Source
def gcdxUpdateBitsOps {World : Type} (t : IntTy) :
    GcdxUpdateDispatchOps (JuliaLean.base.io.M World) (JInt t) where
  generic :=
    { mul := fun a b => pure (JuliaLean.base.int.mulSame a b)
      sub := fun a b => pure (JuliaLean.base.int.sub a b) }
  unsigned :=
    { mulWrap := fun a b => pure (JuliaLean.base.int.mulWrap a b)
      subWrap := fun a b => pure (JuliaLean.base.int.subWrap a b) }
  select := fun _ _ _ => if t.signed then .generic else .unsigned

/-- Full native instantiation of the generic Integer body. All numerical
leaves use installed concrete models, divrem is an actual two-element tuple,
and its destructuring runs installed indexedIterateTuple. Empty witnesses
that native predicates return Bool; custom predicate results remain available
in the generic GcdxOps. Native oneunit retains the conversion after one(T).
Source reference: base/intfuncs.jl:235-260. -/
-- Source: base/intfuncs.jl:235-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@assume_effects :terminates_locally function gcdx(a::T, b::T) where {T<:Integer}
--     if iszero(a) && iszero(b)
--         return (zero(T), zero(T), zero(T))
--     elseif isone(abs(b))
--         # handles (typemin(::Signed), -1)
--         return (one(T), zero(T), b)
--     elseif isone(abs(a))
--         return (one(T), a, zero(T))
--     end
--     # a0, b0 = a, b
--     s0, s1 = oneunit(T), zero(T)
--     t0, t1 = s1, s0
--     # The loop invariant is: s0*a0 + t0*b0 == a && s1*a0 + t1*b0 == b
--     while !iszero(b)
--         q, r = divrem(a, b)
--         a, b = b, r
--         s0, s1 = s1, _gcdx_update(s0, q, s1)
--         t0, t1 = t1, _gcdx_update(t0, q, t1)
--     end
--     # for cases like abs(Int8(-128))
--     if isnegative(a) && isnegative(abs(a))
--         throw(DomainError((a, b), LazyString("gcd not representable in ", T)))
--     else
--         return isnegative(a) ? (abs(a), -s0, -t0) : (a, s0, t0)
--     end
-- end
-- /Source
def gcdxIntegerBitsOps {World : Type} (t : IntTy) :
    GcdxOps World (JInt t) (JInt t × JInt t) JInt64 Empty where
  iszero := fun value => do
    let result ← JuliaLean.base.io.liftJl (JuliaLean.base.number.iszero
      (fun value => pure (JuliaLean.base.int.zero value))
      (fun a b => pure (JuliaLean.base.int.eq a b)) value)
    pure (.inl result)
  isone := fun value => do
    let result ← JuliaLean.base.io.liftJl (JuliaLean.base.number.isone
      (fun value => JuliaLean.base.number.oneValue (fun _ => ())
        (fun _ => gcdxBitsOne t) value)
      (fun a b => pure (JuliaLean.base.int.eq a b)) value)
    pure (.inl result)
  abs := fun value => pure (JuliaLean.base.int.abs value)
  isnegative := fun value => do
    let result ← JuliaLean.base.io.liftJl
      (if t.signed then
        JuliaLean.base.number.isnegative (fun value => pure
          (JuliaLean.base.int.lt value (JuliaLean.base.int.lit .i64 0))) value
      else pure (JuliaLean.base.int.isnegative_Unsigned value))
    pure (.inl result)
  neg := fun value => pure (JuliaLean.base.int.neg value)
  notOther := fun impossible => nomatch impossible
  zeroType := JuliaLean.base.io.liftJl (gcdxBitsZero t)
  oneType := JuliaLean.base.io.liftJl (gcdxBitsOne t)
  oneunitType := JuliaLean.base.io.liftJl (gcdxBitsOneunit t)
  divrem := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.divremBits a b)
  indexedIterateFirst := fun values index => gcdxIndexedTuple values index none
  indexedIterateNext := fun values index state => do
    let (value, _) ← gcdxIndexedTuple values index (some state)
    pure value
  update := gcdxUpdateBitsOps t

/-- Convenient concrete Base instantiation for independent mathematical
properties. This calls the complete generic body and its actual new update
helper implementations. Julia source: base/intfuncs.jl:235-260. -/
-- Source: base/intfuncs.jl:235-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@assume_effects :terminates_locally function gcdx(a::T, b::T) where {T<:Integer}
--     if iszero(a) && iszero(b)
--         return (zero(T), zero(T), zero(T))
--     elseif isone(abs(b))
--         # handles (typemin(::Signed), -1)
--         return (one(T), zero(T), b)
--     elseif isone(abs(a))
--         return (one(T), a, zero(T))
--     end
--     # a0, b0 = a, b
--     s0, s1 = oneunit(T), zero(T)
--     t0, t1 = s1, s0
--     # The loop invariant is: s0*a0 + t0*b0 == a && s1*a0 + t1*b0 == b
--     while !iszero(b)
--         q, r = divrem(a, b)
--         a, b = b, r
--         s0, s1 = s1, _gcdx_update(s0, q, s1)
--         t0, t1 = t1, _gcdx_update(t0, q, t1)
--     end
--     # for cases like abs(Int8(-128))
--     if isnegative(a) && isnegative(abs(a))
--         throw(DomainError((a, b), LazyString("gcd not representable in ", T)))
--     else
--         return isnegative(a) ? (abs(a), -s0, -t0) : (a, s0, t0)
--     end
-- end
-- /Source
def gcdxIntegerBits {World : Type} {t : IntTy} (a b : JInt t) :
    JuliaLean.base.io.M World (JInt t × JInt t × JInt t) :=
  gcdxInteger (gcdxIntegerBitsOps t) a b

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- The fixed gcdx function identity in base/intfuncs.jl:261. -/
-- Source: base/intfuncs.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real, b::Real) = gcdx(promote(a,b)...)
-- /Source
inductive GcdxFunction where
  | gcdx
  deriving BEq, DecidableEq

/-- The same established Core._apply_iterate projection used by the Real
gcd/lcm wrappers, now with the fixed gcdx token. Promote returns arbitrary P,
and the runtime primitive handles all splat/iteration/dispatch behavior.
Source reference: base/intfuncs.jl:261. -/
-- Source: base/intfuncs.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real, b::Real) = gcdx(promote(a,b)...)
-- /Source
structure GcdxPromoteOps (m : Type → Type) (A B P R : Type) where
  promote : A → B → m P
  applyIterate : IterateToken → GcdxFunction → P → m R

/-- Full generic Real gcdx promotion and splatting without a pair-only
restriction on custom promotion. Julia source: base/intfuncs.jl:261. -/
-- Source: base/intfuncs.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real, b::Real) = gcdx(promote(a,b)...)
-- /Source
def gcdxReal {m : Type → Type} [Monad m] {A B P R : Type}
    (ops : GcdxPromoteOps m A B P R) (a : A) (b : B) : m R := do
  let promoted ← ops.promote a b
  ops.applyIterate .baseIterate .gcdx promoted

/-- Native tuple specialization of the established application primitive.
The native gcdx callee reuses its installed model; the generic wrapper keeps
the promoted carrier unrestricted. Julia source: base/intfuncs.jl:261. -/
-- Source: base/intfuncs.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real, b::Real) = gcdx(promote(a,b)...)
-- /Source
def gcdxPromoteBitsOps {World : Type} (s t : IntTy) :
    GcdxPromoteOps (JuliaLean.base.io.M World) (JInt s) (JInt t)
      (JInt (s.promote t) × JInt (s.promote t))
      (JInt (s.promote t) × JInt (s.promote t) × JInt (s.promote t)) where
  promote := fun a b => JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.promoteBits a b)
  applyIterate := fun .baseIterate .gcdx (a, b) =>
    JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.gcdxBits a b)

/-- Open unary Real operations. D is independent of the coefficient carrier
C, which may be a tagged union containing all one/negation results. The
signbit operation includes the adjacent conditional Bool validation.
Source reference: base/intfuncs.jl:263. -/
-- Source: base/intfuncs.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real) = (gcd(a), signbit(a) ? -one(a) : one(a))
-- /Source
structure GcdxUnaryOps (m : Type → Type) (A D C : Type) where
  gcd : A → m D
  signbit : A → m Bool
  one : A → m C
  neg : C → m C

/-- Unary gcdx retains left-to-right tuple evaluation and the two distinct
branches of its sign-dependent coefficient. Julia source: base/intfuncs.jl:263. -/
-- Source: base/intfuncs.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real) = (gcd(a), signbit(a) ? -one(a) : one(a))
-- /Source
def gcdxUnary {m : Type → Type} [Monad m] {A D C : Type}
    (ops : GcdxUnaryOps m A D C) (a : A) : m (D × C) := do
  let d ← ops.gcd a
  let coefficient ← if ← ops.signbit a then do
      let one ← ops.one a
      ops.neg one
    else
      ops.one a
  pure (d, coefficient)

/-- Concrete native dispatch for the unary body. one(a) is its installed
number.oneValue/oneType composition with the actual native conversion.
Source reference: base/intfuncs.jl:263. -/
-- Source: base/intfuncs.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdx(a::Real) = (gcd(a), signbit(a) ? -one(a) : one(a))
-- /Source
def gcdxUnaryBitsOps {World : Type} (t : IntTy) :
    GcdxUnaryOps (JuliaLean.base.io.M World) (JInt t) (JInt t) (JInt t) where
  gcd := fun a => JuliaLean.base.io.liftJl
    (JuliaLean.base.intfuncs.gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits a)
  signbit := fun a => pure (JuliaLean.base.int.signbit a)
  one := fun a => JuliaLean.base.io.liftJl
    (JuliaLean.base.number.oneValue (fun (_ : JInt t) => ())
      (JuliaLean.base.number.oneType
        (fun (_ : Unit) z => JInt.convert t.name t z)) a)
  neg := fun a => pure (JuliaLean.base.int.neg a)

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Open gcdx and destructuring leaves for base/intfuncs.jl:337-341.
P is the actual arbitrary gcdx result, not a required triple. The first two
indexed_iterate operations include their required value/state extraction;
the third includes its call and required value extraction but no unused
final state read. Other return-shape errors remain effects of these leaves.
The final inequality includes its adjacent conditional Bool validation. -/
-- Source: base/intfuncs.jl:337-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _bezout_coef(n, m)
--     g, x, _ = gcdx(n, m)
--     g != 1 && throw(DomainError((n, m), LazyString("Greatest common divisor is ", g, ".")))
--     return x
-- end
-- /Source
structure BezoutCoefOps (World V P State : Type) where
  gcdx : V → V → JuliaLean.base.io.M World P
  indexedFirst : P → JInt64 → JuliaLean.base.io.M World (V × State)
  indexedSecond : P → JInt64 → State → JuliaLean.base.io.M World (V × State)
  indexedThird : P → JInt64 → State → JuliaLean.base.io.M World Unit
  notEqual : V → JInt64 → JuliaLean.base.io.M World Bool

/-- The actual _bezout_coef body, including all three destructuring calls.
The third value is discarded only after its effects and errors occur.
The lazy error message is not rendered at the throw; the installed error
boundary retains DomainError class, as in existing source models.
Source reference: base/intfuncs.jl:337-341. -/
-- Source: base/intfuncs.jl:337-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _bezout_coef(n, m)
--     g, x, _ = gcdx(n, m)
--     g != 1 && throw(DomainError((n, m), LazyString("Greatest common divisor is ", g, ".")))
--     return x
-- end
-- /Source
def bezoutCoefGeneric {World V P State : Type}
    (ops : BezoutCoefOps World V P State) (n m : V) : JuliaLean.base.io.M World V := do
  let result ← ops.gcdx n m
  let (g, state1) ← ops.indexedFirst result (JuliaLean.base.int.lit .i64 1)
  let (x, state2) ← ops.indexedSecond result (JuliaLean.base.int.lit .i64 2) state1
  let _ ← ops.indexedThird result (JuliaLean.base.int.lit .i64 3) state2
  if ← ops.notEqual g (JuliaLean.base.int.lit .i64 1) then
    throw (.jl (.domainError ""))
  else
    pure x

/-- Only an actually selected custom _bezout_coef specialization carries
code; the known generic method is always implemented by bezoutCoefGeneric.
Source reference: base/intfuncs.jl:313,318,329,337-341. -/
-- Source: base/intfuncs.jl:337-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _bezout_coef(n, m)
--     g, x, _ = gcdx(n, m)
--     g != 1 && throw(DomainError((n, m), LazyString("Greatest common divisor is ", g, ".")))
--     return x
-- end
-- /Source
inductive BezoutCoefRoute (m : Type → Type) (V : Type) where
  | generic
  | custom (callee : V → V → m V)

/-- Open dispatch selection plus the explicit source generic body.
Source reference: base/intfuncs.jl:313,318,329,337-341. -/
-- Source: base/intfuncs.jl:337-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _bezout_coef(n, m)
--     g, x, _ = gcdx(n, m)
--     g != 1 && throw(DomainError((n, m), LazyString("Greatest common divisor is ", g, ".")))
--     return x
-- end
-- /Source
structure BezoutCoefDispatchOps (World V P State : Type) where
  generic : BezoutCoefOps World V P State
  select : V → V → BezoutCoefRoute (JuliaLean.base.io.M World) V

/-- Dispatch the internal coefficient helper without replacing its own body
with a callback. Julia source: base/intfuncs.jl:313,318,329,337-341. -/
-- Source: base/intfuncs.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         x = _bezout_coef(n, m)
-- /Source
def bezoutCoefSelected {World V P State : Type}
    (ops : BezoutCoefDispatchOps World V P State) (n m : V) : JuliaLean.base.io.M World V :=
  match ops.select n m with
  | .generic => bezoutCoefGeneric ops.generic n m
  | .custom callee => callee n m

/-- Fixed Signed type identity supplied to the established Core subtype
boundary. Julia source: base/intfuncs.jl:312. -/
-- Source: base/intfuncs.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if R <: Signed
-- /Source
inductive InvmodTypeToken where
  | signed
  deriving BEq, DecidableEq

/-- Convert the actual conditional value with the installed Bool assertion.
Mutations made before a non-Bool result are retained on TypeError.
Source reference: base/intfuncs.jl:317. -/
-- Source: base/intfuncs.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if !hastypemax(S) || (n <= typemax(S)) && (m <= typemax(S))
-- /Source
def invmodAssertBool {World Other : Type} (value : Bool ⊕ Other) :
    JuliaLean.base.io.M World Bool :=
  match JuliaLean.base.reduce.assertBool value with
  | .ok result => pure result
  | .error .typeError => throw (.foreignError "TypeError" "")

/-- Preserve custom ! dispatch on a non-Bool hastypemax result. The known
Bool branch calls the installed primitive-backed Bool model.
Source reference: base/intfuncs.jl:317. -/
-- Source: base/intfuncs.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if !hastypemax(S) || (n <= typemax(S)) && (m <= typemax(S))
-- /Source
def invmodLogicalNot {World Other : Type}
    (notOther : Other → JuliaLean.base.io.M World (Bool ⊕ Other)) :
    Bool ⊕ Other → JuliaLean.base.io.M World (Bool ⊕ Other)
  | .inl value => pure (.inl
      (JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool value))
  | .inr value => notOther value

/-- Full dynamic Integer/type interfaces for base/intfuncs.jl:308-335.
V and Ty may be tagged carriers of every intermediate/reference, including
non-type reflection results. subtype projects the existing Core primitive
with an explicit Signed token and its invalid-operand errors. All predicates
except hastypemax include adjacent Bool validation; hastypemax must retain a
non-Bool result until its selected ! call and the subsequent validation.
No array/tuple sizes or arithmetic correctness assumptions are introduced. -/
-- Source: base/intfuncs.jl:308-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function invmod(n::Integer, m::Integer)
--     # The postcondition is: mod(widemul(result, n), m) == mod(one(T), m) && iszero(div(result, m))
--     iszero(m) && throw(DomainError(m, "`m` must not be 0."))
--     R = promote_typeof(n, m)
--     if R <: Signed
--         x = _bezout_coef(n, m)
--         return mod(x, m)
--     else
--         S = signed(R)
--         if !hastypemax(S) || (n <= typemax(S)) && (m <= typemax(S))
--             x = _bezout_coef(n % S, m % S)
-- 
--             # this branch is only hit if R <: Unsigned, so we don't have
--             # to worry about abs(typemin(::Signed)) overflow. If `m` is
--             # signed then `x` must be unsigned, and thus never negative
--             isnegative(x) && (x += abs(m))
--             return mod(x % R, m)
--         else
--             # since gcdx only promises bezout w.r.t overflow for unsigned ints,
--             # we have to widen to a signed type
--             W = widen(S)
--             x = _bezout_coef(n % W, m % W)
--             t = mod(x, m % W)
--             isnegative(m) && (t -= m)
--             return mod(t % R, m)
--         end
--     end
-- end
-- /Source
structure InvmodOps (World V Ty P State Other : Type) where
  iszero : V → JuliaLean.base.io.M World Bool
  promoteTypeof : V → V → JuliaLean.base.io.M World Ty
  subtype : Ty → InvmodTypeToken → JuliaLean.base.io.M World Bool
  signedType : Ty → JuliaLean.base.io.M World Ty
  hasTypeMax : Ty → JuliaLean.base.io.M World (Bool ⊕ Other)
  notOther : Other → JuliaLean.base.io.M World (Bool ⊕ Other)
  typemax : Ty → JuliaLean.base.io.M World V
  lessEqual : V → V → JuliaLean.base.io.M World Bool
  widen : Ty → JuliaLean.base.io.M World Ty
  remType : V → Ty → JuliaLean.base.io.M World V
  isnegative : V → JuliaLean.base.io.M World Bool
  abs : V → JuliaLean.base.io.M World V
  add : V → V → JuliaLean.base.io.M World V
  sub : V → V → JuliaLean.base.io.M World V
  mod : V → V → JuliaLean.base.io.M World V
  bezout : BezoutCoefDispatchOps World V P State

/-- Full invmod(Integer,Integer) source body. Type-bound checks retain their
original short circuit and two separate typemax calls. The wide branch also
retains both distinct conversions of m to W. All arithmetic uses selected
Julia operations, and the known coefficient helper invokes its real body.
Source reference: base/intfuncs.jl:308-335. -/
-- Source: base/intfuncs.jl:308-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function invmod(n::Integer, m::Integer)
--     # The postcondition is: mod(widemul(result, n), m) == mod(one(T), m) && iszero(div(result, m))
--     iszero(m) && throw(DomainError(m, "`m` must not be 0."))
--     R = promote_typeof(n, m)
--     if R <: Signed
--         x = _bezout_coef(n, m)
--         return mod(x, m)
--     else
--         S = signed(R)
--         if !hastypemax(S) || (n <= typemax(S)) && (m <= typemax(S))
--             x = _bezout_coef(n % S, m % S)
-- 
--             # this branch is only hit if R <: Unsigned, so we don't have
--             # to worry about abs(typemin(::Signed)) overflow. If `m` is
--             # signed then `x` must be unsigned, and thus never negative
--             isnegative(x) && (x += abs(m))
--             return mod(x % R, m)
--         else
--             # since gcdx only promises bezout w.r.t overflow for unsigned ints,
--             # we have to widen to a signed type
--             W = widen(S)
--             x = _bezout_coef(n % W, m % W)
--             t = mod(x, m % W)
--             isnegative(m) && (t -= m)
--             return mod(t % R, m)
--         end
--     end
-- end
-- /Source
def invmodInteger {World V Ty P State Other : Type}
    (ops : InvmodOps World V Ty P State Other) (n m : V) : JuliaLean.base.io.M World V := do
  if ← ops.iszero m then
    throw (.jl (.domainError "`m` must not be 0."))
  let resultType ← ops.promoteTypeof n m
  if ← ops.subtype resultType .signed then
    let x ← bezoutCoefSelected ops.bezout n m
    ops.mod x m
  else
    let signedType ← ops.signedType resultType
    let noMaximum ← invmodLogicalNot ops.notOther (← ops.hasTypeMax signedType)
    let fits ← if ← invmodAssertBool noMaximum then pure true else do
      let nMaximum ← ops.typemax signedType
      if ← ops.lessEqual n nMaximum then do
        let mMaximum ← ops.typemax signedType
        ops.lessEqual m mMaximum
      else
        pure false
    if fits then
      let convertedN ← ops.remType n signedType
      let convertedM ← ops.remType m signedType
      let x ← bezoutCoefSelected ops.bezout convertedN convertedM
      let x ← if ← ops.isnegative x then do
          let magnitude ← ops.abs m
          ops.add x magnitude
        else pure x
      let convertedX ← ops.remType x resultType
      ops.mod convertedX m
    else
      let wideType ← ops.widen signedType
      let convertedN ← ops.remType n wideType
      let convertedM ← ops.remType m wideType
      let x ← bezoutCoefSelected ops.bezout convertedN convertedM
      let convertedMForMod ← ops.remType m wideType
      let t ← ops.mod x convertedMForMod
      let t ← if ← ops.isnegative m then ops.sub t m else pure t
      let convertedT ← ops.remType t resultType
      ops.mod convertedT m

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- A dynamic remainder/inverse value. Native values retain their actual
width, which need not equal the requested modulus type after custom remainder
dispatch. Custom tags represent genuinely selected user methods. Unmatched tags
retain every other runtime type/reference for which no unary inverse exists.
Source reference: base/intfuncs.jl:370. -/
-- Source: base/intfuncs.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invmod(n::Integer, ::Type{T}) where {T<:BitInteger} = invmod(n % T)
-- /Source
inductive RingInverseValue (Custom : Type) where
  | native (type : IntTy) (value : JInt type)
  | custom (value : Custom)
  | unmatched (value : Custom)

/-- Open remainder-to-type and genuinely selected custom unary-inverse
operations. The generic source does not constrain a custom remainder result
to T or even to an Integer. Known native inverse dispatch is closed below.
Source reference: base/intfuncs.jl:370. -/
-- Source: base/intfuncs.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invmod(n::Integer, ::Type{T}) where {T<:BitInteger} = invmod(n % T)
-- /Source
structure RingInverseTypeOps (World I Custom : Type) where
  remToType : I → IntTy → JuliaLean.base.io.M World (RingInverseValue Custom)
  customInvmod : Custom → JuliaLean.base.io.M World (RingInverseValue Custom)

/-- Unary inverse dispatch after the remainder call. Every native branch
uses the preserved, source-mirrored ring algorithm; only a genuinely selected
custom method is supplied by the open interface.
Source reference: base/intfuncs.jl:370,373-382. -/
-- Source: base/intfuncs.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invmod(n::Integer, ::Type{T}) where {T<:BitInteger} = invmod(n % T)
-- /Source
def invmodTypeSelected {World Custom : Type}
    (customInvmod : Custom → JuliaLean.base.io.M World (RingInverseValue Custom)) :
    RingInverseValue Custom → JuliaLean.base.io.M World (RingInverseValue Custom)
  | .native type value => do
      let result ← JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.invmod_Ring value)
      pure (.native type result)
  | .custom value => customInvmod value
  | .unmatched _ => throw (.jl (.methodError "invmod"))

/-- Complete typed-modulus wrapper: first execute remainder using the
requested native type, then dispatch inverse on the actual returned value.
Both effects and errors, and type-changing custom results, are retained.
Source reference: base/intfuncs.jl:370. -/
-- Source: base/intfuncs.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invmod(n::Integer, ::Type{T}) where {T<:BitInteger} = invmod(n % T)
-- /Source
def invmodType {World I Custom : Type} (ops : RingInverseTypeOps World I Custom)
    (n : I) (type : IntTy) : JuliaLean.base.io.M World (RingInverseValue Custom) := do
  let reduced ← ops.remToType n type
  invmodTypeSelected ops.customInvmod reduced

/-- Native instantiation uses installed remainder-to-type and closed
native inverse dispatch. There is no fictitious custom fallback: Empty
excludes custom outputs from the installed native remainder operation.
Source reference: base/intfuncs.jl:370. -/
-- Source: base/intfuncs.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invmod(n::Integer, ::Type{T}) where {T<:BitInteger} = invmod(n % T)
-- /Source
def invmodTypeBitsOps {World : Type} (sourceType : IntTy) :
    RingInverseTypeOps World (JInt sourceType) Empty where
  remToType := fun value targetType => pure
    (.native targetType (JuliaLean.base.int.remT targetType value))
  customInvmod := fun impossible => nomatch impossible

/-- The two eager expressions among the Integer helper's LazyString
arguments. The exponent is unrestricted, and float/negation may have different
result types, effects, exceptions or divergence.
Source reference: base/intfuncs.jl:388-392. -/
-- Source: base/intfuncs.jl:388-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline throw_domerr_powbysq(::Integer, p) = throw(DomainError(p, LazyString(
--     "Cannot raise an integer x to a negative power ", p, ".",
--     "\nMake x or ", p, " a float by adding a zero decimal ",
--     "(e.g., 2.0^", p, " or 2^", float(p), " instead of 2^", p, ") ",
--     "or write 1/x^", -p, ", float(x)^", p, ", x^float(", p, ") or (x//1)^", p, ".")))
-- /Source
structure PowerDomainIntegerOps (World P F N : Type) where
  float : P → JuliaLean.base.io.M World F
  neg : P → JuliaLean.base.io.M World N

/-- Full Integer error helper. LazyString delays printing its arguments,
not evaluation of float(p) and -p. Execute those calls in source order before
the final DomainError, preserving any earlier error and mutable state.
The lazy message and DomainError payload are not inspected at the installed
exception-class boundary. Julia source: base/intfuncs.jl:388-392. -/
-- Source: base/intfuncs.jl:388-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline throw_domerr_powbysq(::Integer, p) = throw(DomainError(p, LazyString(
--     "Cannot raise an integer x to a negative power ", p, ".",
--     "\nMake x or ", p, " a float by adding a zero decimal ",
--     "(e.g., 2.0^", p, " or 2^", float(p), " instead of 2^", p, ") ",
--     "or write 1/x^", -p, ", float(x)^", p, ", x^float(", p, ") or (x//1)^", p, ".")))
-- /Source
def throwPowerDomainInteger {World A P F N R : Type}
    (ops : PowerDomainIntegerOps World P F N) (_x : A) (p : P) :
    JuliaLean.base.io.M World R := do
  let _ ← ops.float p
  let _ ← ops.neg p
  throw (.jl (.domainError ""))

/-- Concrete native exponent adapter for the eager diagnostic calls.
Both Float64 conversion and unary negation use installed Base models, including
128-bit inputs and signed-minimum wrapping.
Source reference: base/intfuncs.jl:388-392. -/
-- Source: base/intfuncs.jl:388-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline throw_domerr_powbysq(::Integer, p) = throw(DomainError(p, LazyString(
--     "Cannot raise an integer x to a negative power ", p, ".",
--     "\nMake x or ", p, " a float by adding a zero decimal ",
--     "(e.g., 2.0^", p, " or 2^", float(p), " instead of 2^", p, ") ",
--     "or write 1/x^", -p, ", float(x)^", p, ", x^float(", p, ") or (x//1)^", p, ".")))
-- /Source
def powerDomainIntegerBitsOps {World : Type} (t : IntTy) :
    PowerDomainIntegerOps World (JInt t) (JuliaLean.base.float.FV .f64) (JInt t) where
  float := fun value => pure (JuliaLean.base.float.float_BitInteger value)
  neg := fun value => pure (JuliaLean.base.int.neg value)

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Identity of the keyword callable in base/intfuncs.jl:399-443. The Base
star branch uses the very same selected multiplication as the eager square;
custom is an actually distinct callable, retaining its effects and failures. -/
-- Source: base/intfuncs.jl:399-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :terminates_locally function power_by_squaring(x_, p::Integer; mul=*)
--     x_squared_ = x_ * x_
--     x_squared_type = typeof(x_squared_)
--     T = if x_ isa Number
--         promote_type(typeof(x_), x_squared_type)
--     else
--         x_squared_type
--     end
--     x = convert(T, x_)
--     square_is_useful = mul === *
--     if p == 1
--         return copy(x)
--     elseif p == 0
--         return one(x)
--     elseif p == 2
--         if square_is_useful  # avoid performing the same multiplication a second time when possible
--             return convert(T, x_squared_)
--         end
--         return mul(x, x)
--     elseif p < 0
--         isone(x) && return copy(x)
--         isone(-x) && return iseven(p) ? one(x) : copy(x)
--         throw_domerr_powbysq(x, p)
--     end
--     t = trailing_zeros(p) + 1
--     p >>= t
--     if square_is_useful  # avoid performing the same multiplication a second time when possible
--         if (t -= 1) > 0
--             x = convert(T, x_squared_)
--         end
--     end
--     while (t -= 1) > 0
--         x = mul(x, x)
--     end
--     y = x
--     while p > 0
--         t = trailing_zeros(p) + 1
--         p >>= t
--         while (t -= 1) >= 0
--             x = mul(x, x)
--         end
--         y = mul(y, x)
--     end
--     return y
-- end
-- /Source
inductive PowerMultiplier (World V : Type) where
  | baseStar
  | custom (call : V → V → JuliaLean.base.io.M World V)

/-- Runtime values, types, exponents, and counters are independent tagged
carriers. Each may include changed runtime types and references. typeOf and
isNumber project the established Core typeof/isa boundary; promoteType and
convert are actual dispatch-selected calls. Condition fields include the
adjacent Bool assertion, so a non-Bool result preserves TypeError. Counters
are not natural-number fuel: every +, -, comparison, shift and call is open
dispatch in its original position. Julia source: base/intfuncs.jl:399-443. -/
-- Source: base/intfuncs.jl:399-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :terminates_locally function power_by_squaring(x_, p::Integer; mul=*)
--     x_squared_ = x_ * x_
--     x_squared_type = typeof(x_squared_)
--     T = if x_ isa Number
--         promote_type(typeof(x_), x_squared_type)
--     else
--         x_squared_type
--     end
--     x = convert(T, x_)
--     square_is_useful = mul === *
--     if p == 1
--         return copy(x)
--     elseif p == 0
--         return one(x)
--     elseif p == 2
--         if square_is_useful  # avoid performing the same multiplication a second time when possible
--             return convert(T, x_squared_)
--         end
--         return mul(x, x)
--     elseif p < 0
--         isone(x) && return copy(x)
--         isone(-x) && return iseven(p) ? one(x) : copy(x)
--         throw_domerr_powbysq(x, p)
--     end
--     t = trailing_zeros(p) + 1
--     p >>= t
--     if square_is_useful  # avoid performing the same multiplication a second time when possible
--         if (t -= 1) > 0
--             x = convert(T, x_squared_)
--         end
--     end
--     while (t -= 1) > 0
--         x = mul(x, x)
--     end
--     y = x
--     while p > 0
--         t = trailing_zeros(p) + 1
--         p >>= t
--         while (t -= 1) >= 0
--             x = mul(x, x)
--         end
--         y = mul(y, x)
--     end
--     return y
-- end
-- /Source
structure PowerOps (World V Ty P C : Type) where
  star : V → V → JuliaLean.base.io.M World V
  typeOf : V → Ty
  isNumber : V → Bool
  promoteType : Ty → Ty → JuliaLean.base.io.M World Ty
  convert : Ty → V → JuliaLean.base.io.M World V
  copy : V → JuliaLean.base.io.M World V
  one : V → JuliaLean.base.io.M World V
  neg : V → JuliaLean.base.io.M World V
  isone : V → JuliaLean.base.io.M World Bool
  exponentEqual : P → JInt64 → JuliaLean.base.io.M World Bool
  exponentLess : P → JInt64 → JuliaLean.base.io.M World Bool
  exponentGreater : P → JInt64 → JuliaLean.base.io.M World Bool
  iseven : P → JuliaLean.base.io.M World Bool
  trailingZeros : P → JuliaLean.base.io.M World C
  addCounter : C → JInt64 → JuliaLean.base.io.M World C
  subCounter : C → JInt64 → JuliaLean.base.io.M World C
  counterGreater : C → JInt64 → JuliaLean.base.io.M World Bool
  counterGreaterEqual : C → JInt64 → JuliaLean.base.io.M World Bool
  shiftRight : P → C → JuliaLean.base.io.M World P
  throwDomain : V → P → JuliaLean.base.io.M World V

/-- The keyword's equality to Base.* fixes both square reuse and its actual
callee. Julia source: base/intfuncs.jl:399,408,418,432,437,439. -/
-- Source: base/intfuncs.jl:408-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     square_is_useful = mul === *
-- /Source
def powerMultiply {World V Ty P C : Type} (ops : PowerOps World V Ty P C)
    (mul : PowerMultiplier World V) (a b : V) : JuliaLean.base.io.M World V :=
  match mul with
  | .baseStar => ops.star a b
  | .custom call => call a b

/-- Complete power-by-squaring body with three genuine source while loops.
The eager x_*x_, type promotion and conversion precede every exponent check.
Each decrement occurs before its comparison; changed counter/exponent types,
custom callables, aliases, effects, errors and divergence remain observable.
A normally returning custom diagnostic is ignored, then execution continues.
Source reference: base/intfuncs.jl:399-443. -/
-- Source: base/intfuncs.jl:399-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :terminates_locally function power_by_squaring(x_, p::Integer; mul=*)
--     x_squared_ = x_ * x_
--     x_squared_type = typeof(x_squared_)
--     T = if x_ isa Number
--         promote_type(typeof(x_), x_squared_type)
--     else
--         x_squared_type
--     end
--     x = convert(T, x_)
--     square_is_useful = mul === *
--     if p == 1
--         return copy(x)
--     elseif p == 0
--         return one(x)
--     elseif p == 2
--         if square_is_useful  # avoid performing the same multiplication a second time when possible
--             return convert(T, x_squared_)
--         end
--         return mul(x, x)
--     elseif p < 0
--         isone(x) && return copy(x)
--         isone(-x) && return iseven(p) ? one(x) : copy(x)
--         throw_domerr_powbysq(x, p)
--     end
--     t = trailing_zeros(p) + 1
--     p >>= t
--     if square_is_useful  # avoid performing the same multiplication a second time when possible
--         if (t -= 1) > 0
--             x = convert(T, x_squared_)
--         end
--     end
--     while (t -= 1) > 0
--         x = mul(x, x)
--     end
--     y = x
--     while p > 0
--         t = trailing_zeros(p) + 1
--         p >>= t
--         while (t -= 1) >= 0
--             x = mul(x, x)
--         end
--         y = mul(y, x)
--     end
--     return y
-- end
-- /Source
def powerBySquaring {World V Ty P C : Type} (ops : PowerOps World V Ty P C)
    (x_ : V) (p : P) (mul : PowerMultiplier World V := .baseStar) :
    JuliaLean.base.io.M World V := do
  let xSquared ← ops.star x_ x_
  let xSquaredType := ops.typeOf xSquared
  let target ← if ops.isNumber x_ then
      ops.promoteType (ops.typeOf x_) xSquaredType
    else pure xSquaredType
  let x ← ops.convert target x_
  let squareIsUseful := match mul with | .baseStar => true | .custom _ => false
  if ← ops.exponentEqual p (JuliaLean.base.int.lit .i64 1) then
    return ← ops.copy x
  else if ← ops.exponentEqual p (JuliaLean.base.int.lit .i64 0) then
    return ← ops.one x
  else if ← ops.exponentEqual p (JuliaLean.base.int.lit .i64 2) then
    if squareIsUseful then return ← ops.convert target xSquared
    return ← powerMultiply ops mul x x
  else if ← ops.exponentLess p (JuliaLean.base.int.lit .i64 0) then
    if ← ops.isone x then return ← ops.copy x
    let negative ← ops.neg x
    if ← ops.isone negative then
      if ← ops.iseven p then return ← ops.one x
      else return ← ops.copy x
    let _ ← ops.throwDomain x p
    pure ()
  let count ← ops.trailingZeros p
  let count ← ops.addCounter count (JuliaLean.base.int.lit .i64 1)
  let p ← ops.shiftRight p count
  let (x, count) ← if squareIsUseful then do
      let count ← ops.subCounter count (JuliaLean.base.int.lit .i64 1)
      if ← ops.counterGreater count (JuliaLean.base.int.lit .i64 0) then
        let x ← ops.convert target xSquared
        pure (x, count)
      else pure (x, count)
    else pure (x, count)
  let (x, _) ← JuliaLean.base.io.whileLoop (fun (state : V × C) => do
    let count ← ops.subCounter state.2 (JuliaLean.base.int.lit .i64 1)
    if ← ops.counterGreater count (JuliaLean.base.int.lit .i64 0) then
      let x ← powerMultiply ops mul state.1 state.1
      pure (.inr (x, count))
    else pure (.inl (state.1, count))) (x, count)
  let y := x
  JuliaLean.base.io.whileLoop (fun (state : V × V × P) => do
    let (x, y, p) := state
    if ← ops.exponentGreater p (JuliaLean.base.int.lit .i64 0) then
      let count ← ops.trailingZeros p
      let count ← ops.addCounter count (JuliaLean.base.int.lit .i64 1)
      let p ← ops.shiftRight p count
      let (x, _) ← JuliaLean.base.io.whileLoop (fun (inner : V × C) => do
        let count ← ops.subCounter inner.2 (JuliaLean.base.int.lit .i64 1)
        if ← ops.counterGreaterEqual count (JuliaLean.base.int.lit .i64 0) then
          let x ← powerMultiply ops mul inner.1 inner.1
          pure (.inr (x, count))
        else pure (.inl (inner.1, count))) (x, count)
      let y ← powerMultiply ops mul y x
      pure (.inr (x, y, p))
    else pure (.inl y)) (x, y, p)

/-- Concrete same-sign native remainder adapter used by the installed mixed
signedness remainder method. Both promotion and remainder are installed Base
models, and no machine arithmetic is replaced by Lean arithmetic.
Julia dependency: base/promotion.jl:520; source use base/int.jl:279. -/
-- Source: base/promotion.jl:520-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::Real, y::Real) = rem(promote(x,y)...)
-- /Source
def powerNativeRem {s t : IntTy} (a : JInt s) (b : JInt t) :
    Jl (JInt (s.promote t)) := do
  let (a, b) := JuliaLean.base.int.promoteSameSign a b
  JuliaLean.base.int.remSame a b

/-- Installed iseven composition for native exponents. Integer(n) is the
identity on the concrete native carrier. The selected mixed remainder is
evaluated once and keeps its errors; all surrounding tests/constructors are
pure on these fixed concrete types. Julia dependency: base/int.jl:181;
used by base/intfuncs.jl:420. -/
-- Source: base/int.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iseven(n::Real) = isinteger(n) && iszero(rem(Integer(n), 2))
-- /Source
def powerNativeEven {t : IntTy} (p : JInt t) : Jl Bool := do
  if t.signed then
    let remainder ← powerNativeRem p (JuliaLean.base.int.lit .i64 2)
    pure (JuliaLean.base.int.iseven_Real JuliaLean.base.number.isintegerInteger id
      (fun _ _ => remainder)
      (fun value => JuliaLean.base.int.eq value (JuliaLean.base.int.zero value)) p)
  else
    let remainder ← JuliaLean.base.int.rem_Unsigned_BitSigned
      powerNativeRem p (JuliaLean.base.int.lit .i64 2)
    pure (JuliaLean.base.int.iseven_Real JuliaLean.base.number.isintegerInteger id
      (fun _ _ => remainder)
      (fun value => JuliaLean.base.int.eq value (JuliaLean.base.int.zero value)) p)

/-- Concrete native Base instantiation, retaining the distinct base and
exponent widths. Every numeric leaf uses installed Base behavior; counters
are native Int, one/copy/convert are installed number methods, and the known
Integer negative-power diagnostic invokes the complete effectful helper.
Source reference: base/intfuncs.jl:399-443. -/
-- Source: base/intfuncs.jl:399-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :terminates_locally function power_by_squaring(x_, p::Integer; mul=*)
--     x_squared_ = x_ * x_
--     x_squared_type = typeof(x_squared_)
--     T = if x_ isa Number
--         promote_type(typeof(x_), x_squared_type)
--     else
--         x_squared_type
--     end
--     x = convert(T, x_)
--     square_is_useful = mul === *
--     if p == 1
--         return copy(x)
--     elseif p == 0
--         return one(x)
--     elseif p == 2
--         if square_is_useful  # avoid performing the same multiplication a second time when possible
--             return convert(T, x_squared_)
--         end
--         return mul(x, x)
--     elseif p < 0
--         isone(x) && return copy(x)
--         isone(-x) && return iseven(p) ? one(x) : copy(x)
--         throw_domerr_powbysq(x, p)
--     end
--     t = trailing_zeros(p) + 1
--     p >>= t
--     if square_is_useful  # avoid performing the same multiplication a second time when possible
--         if (t -= 1) > 0
--             x = convert(T, x_squared_)
--         end
--     end
--     while (t -= 1) > 0
--         x = mul(x, x)
--     end
--     y = x
--     while p > 0
--         t = trailing_zeros(p) + 1
--         p >>= t
--         while (t -= 1) >= 0
--             x = mul(x, x)
--         end
--         y = mul(y, x)
--     end
--     return y
-- end
-- /Source
def powerBitsOps {World : Type} (t e : IntTy) :
    PowerOps World (JInt t) Unit (JInt e) JInt64 where
  star := fun a b => pure (JuliaLean.base.int.mulSame a b)
  typeOf := fun _ => ()
  isNumber := fun _ => true
  promoteType := fun _ _ => pure (JuliaLean.base.promotion.promoteTypeSame ())
  convert := fun _ value => pure (JuliaLean.base.number.convertSame value)
  copy := fun value => pure (JuliaLean.base.number.copy value)
  one := fun value => JuliaLean.base.io.liftJl
    (JuliaLean.base.number.oneValue (fun _ => ()) (fun _ => gcdxBitsOne t) value)
  neg := fun value => pure (JuliaLean.base.int.neg value)
  isone := fun value => JuliaLean.base.io.liftJl
    (JuliaLean.base.number.isone
      (fun value => JuliaLean.base.number.oneValue (fun _ => ())
        (fun _ => gcdxBitsOne t) value)
      (fun a b => pure (JuliaLean.base.int.eq a b)) value)
  exponentEqual := fun value literal => pure (JuliaLean.base.int.eq value literal)
  exponentLess := fun value literal => pure (JuliaLean.base.int.lt value literal)
  exponentGreater := fun value literal => pure
    (JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt value literal)
  iseven := fun value => JuliaLean.base.io.liftJl (powerNativeEven value)
  trailingZeros := fun value => pure (JuliaLean.base.int.trailing_zeros value)
  addCounter := fun a b => pure (JuliaLean.base.int.add a b)
  subCounter := fun a b => pure (JuliaLean.base.int.sub a b)
  counterGreater := fun a b => pure
    (JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt a b)
  counterGreaterEqual := fun a b => pure
    (JuliaLean.base.operators.greaterEqual JuliaLean.base.int.le a b)
  shiftRight := fun value count => pure (JuliaLean.base.int.shr_Int value count)
  throwDomain := fun value exponent =>
    throwPowerDomainInteger (powerDomainIntegerBitsOps e) value exponent

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- The actual result of p == 0 may be a Bool or any other runtime value.
Source reference: base/intfuncs.jl:444-448. -/
-- Source: base/intfuncs.jl:444-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- power_by_squaring(x::Bool, p::Unsigned) = ((p==0) | x)
-- function power_by_squaring(x::Bool, p::Integer)
--     p < 0 && !x && throw_domerr_powbysq(x, p)
--     return (p==0) | x
-- end
-- /Source
inductive BoolPowerValue (Other : Type) where
  | boolean (value : Bool)
  | other (value : Other)

/-- Diagnostic dispatch can select a method specialized on the unfixed
Integer exponent. The known Integer branch retains its implemented body;
only a genuinely selected alternate method carries code. Any normal result
is ignored at this statement boundary. Julia source: base/intfuncs.jl:446. -/
-- Source: base/intfuncs.jl:445-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function power_by_squaring(x::Bool, p::Integer)
--     p < 0 && !x && throw_domerr_powbysq(x, p)
--     return (p==0) | x
-- end
-- /Source
inductive BoolPowerDiagnosticRoute (World P : Type) where
  | integer
  | custom (callee : Bool → P → JuliaLean.base.io.M World Unit)

/-- Full effectful Bool-power leaves. Equality is not a condition: an arbitrary
result reaches bitwise |. Only the less-than call includes adjacent Bool
validation. Diagnostic operations invoke the real Integer error helper.
Source reference: base/intfuncs.jl:444-448. -/
-- Source: base/intfuncs.jl:444-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- power_by_squaring(x::Bool, p::Unsigned) = ((p==0) | x)
-- function power_by_squaring(x::Bool, p::Integer)
--     p < 0 && !x && throw_domerr_powbysq(x, p)
--     return (p==0) | x
-- end
-- /Source
structure BoolPowerOps (World P Other F N : Type) where
  equal : P → JInt64 → JuliaLean.base.io.M World (BoolPowerValue Other)
  orOther : Other → Bool → JuliaLean.base.io.M World (BoolPowerValue Other)
  less : P → JInt64 → JuliaLean.base.io.M World Bool
  diagnostic : PowerDomainIntegerOps World P F N
  selectDiagnostic : Bool → P → BoolPowerDiagnosticRoute World P

/-- Known Bool | Bool calls the installed Base model; only the genuinely
non-Bool left operand retains open dispatch. No Bool validation is inserted.
Source reference: base/intfuncs.jl:444,447. -/
-- Source: base/intfuncs.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- power_by_squaring(x::Bool, p::Unsigned) = ((p==0) | x)
-- /Source
def boolPowerOr {World Other : Type}
    (orOther : Other → Bool → JuliaLean.base.io.M World (BoolPowerValue Other))
    (left : BoolPowerValue Other) (right : Bool) : JuliaLean.base.io.M World (BoolPowerValue Other) :=
  match left with
  | .boolean value => pure (.boolean (JuliaLean.base.bool.orBool value right))
  | .other value => orOther value right

/-- Complete Bool/Unsigned body, retaining arbitrary equality and OR
results, effects and exceptions. Julia source: base/intfuncs.jl:444. -/
-- Source: base/intfuncs.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- power_by_squaring(x::Bool, p::Unsigned) = ((p==0) | x)
-- /Source
def powerBoolUnsigned {World P Other F N : Type}
    (ops : BoolPowerOps World P Other F N) (x : Bool) (p : P) :
    JuliaLean.base.io.M World (BoolPowerValue Other) := do
  let equal ← ops.equal p (JuliaLean.base.int.lit .i64 0)
  boolPowerOr ops.orOther equal x

/-- Complete Bool/Integer body. The negative false-base path dispatches its diagnostic; the known Integer
route invokes the actual helper, including eager float(p) and -p effects.
A selected custom diagnostic may return normally, after which equality/OR
still execute, because the helper call is an expression statement.
The known !x uses the installed primitive Bool method. Equality is never
asserted to be Bool before bitwise OR. Julia source: base/intfuncs.jl:445-448. -/
-- Source: base/intfuncs.jl:445-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function power_by_squaring(x::Bool, p::Integer)
--     p < 0 && !x && throw_domerr_powbysq(x, p)
--     return (p==0) | x
-- end
-- /Source
def powerBoolInteger {World P Other F N : Type}
    (ops : BoolPowerOps World P Other F N) (x : Bool) (p : P) :
    JuliaLean.base.io.M World (BoolPowerValue Other) := do
  if ← ops.less p (JuliaLean.base.int.lit .i64 0) then
    if JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool x then
      match ops.selectDiagnostic x p with
      | .integer =>
          let _ ← throwPowerDomainInteger (R := Unit) ops.diagnostic x p
          pure ()
      | .custom callee =>
          let _ ← callee x p
          pure ()
  let equal ← ops.equal p (JuliaLean.base.int.lit .i64 0)
  boolPowerOr ops.orOther equal x

/-- Fixed identities of the named power operations in these wrappers.
Source reference: base/intfuncs.jl:450-451,478,483-493. -/
-- Source: base/intfuncs.jl:450-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::T, p::T) where {T<:Integer} = power_by_squaring(x,p)
-- ^(x::Number, p::Integer)  = power_by_squaring(x,p)
-- /Source
inductive PowerTailFunction where
  | powerBySquaring
  | basePower
  deriving BEq, DecidableEq

/-- Selected power targets on unfixed argument types; results need not have
the same runtime type as either argument. A supplied target denotes the
actually selected method, not a replacement for this wrapper body.
Source reference: base/intfuncs.jl:450-451. -/
-- Source: base/intfuncs.jl:450-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::T, p::T) where {T<:Integer} = power_by_squaring(x,p)
-- ^(x::Number, p::Integer)  = power_by_squaring(x,p)
-- /Source
structure PowerWrapperOps (World A P R : Type) where
  call : PowerTailFunction → A → P → JuliaLean.base.io.M World R

/-- Complete same-type Integer power wrapper; the selected callee may
return a different runtime type and retain arbitrary effects.
Source reference: base/intfuncs.jl:450. -/
-- Source: base/intfuncs.jl:450-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::T, p::T) where {T<:Integer} = power_by_squaring(x,p)
-- /Source
def powInteger {World A R : Type} (ops : PowerWrapperOps World A A R)
    (x p : A) : JuliaLean.base.io.M World R :=
  ops.call .powerBySquaring x p

/-- Complete Number/Integer power wrapper with independent dynamic
argument and result carriers. Julia source: base/intfuncs.jl:451. -/
-- Source: base/intfuncs.jl:451-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::Number, p::Integer)  = power_by_squaring(x,p)
-- /Source
def powNumber {World A P R : Type} (ops : PowerWrapperOps World A P R)
    (x : A) (p : P) : JuliaLean.base.io.M World R :=
  ops.call .powerBySquaring x p

/-- Apply the actual supplied callable to x and the arbitrary Val parameter.
P includes every permitted value-type parameter, not merely Int; the result
carrier and effects are unrestricted. Julia source: base/intfuncs.jl:460. -/
-- Source: base/intfuncs.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(f, x, ::Val{p}) where {p} = f(x,p)
-- /Source
def literalPowFunction {World F A P R : Type}
    (apply : F → A → P → JuliaLean.base.io.M World R) (f : F) (x : A) (p : P) :
    JuliaLean.base.io.M World R := apply f x p

/-- The HWNumber union does not fix the concrete member type. These
selected leaves include native integers, floats, complex and rational values,
with heterogeneous intermediate/results and full effects.
Source reference: base/intfuncs.jl:470-475. -/
-- Source: base/intfuncs.jl:470-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{0}) = one(x)
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{1}) = x
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{2}) = x*x
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{3}) = x*x*x
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{-1}) = inv(x)
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{-2}) = (i=inv(x); i*i)
-- /Source
structure HardwareLiteralOps (World A Square Inverse Result : Type) where
  one : A → JuliaLean.base.io.M World Result
  square : A → A → JuliaLean.base.io.M World Square
  cube : A → A → A → JuliaLean.base.io.M World Result
  inv : A → JuliaLean.base.io.M World Inverse
  inverseSquare : Inverse → Inverse → JuliaLean.base.io.M World Result

/-- Zero literal power performs the selected one call. Julia source: base/intfuncs.jl:470. -/
-- Source: base/intfuncs.jl:470-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{0}) = one(x)
-- /Source
def literalHardwareZero {World A Square Inverse Result : Type}
    (ops : HardwareLiteralOps World A Square Inverse Result) (x : A) :
    JuliaLean.base.io.M World Result := ops.one x

/-- Square retains both original operands and the actual result type. Julia source: base/intfuncs.jl:472. -/
-- Source: base/intfuncs.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{2}) = x*x
-- /Source
def literalHardwareTwo {World A Square Inverse Result : Type}
    (ops : HardwareLiteralOps World A Square Inverse Result) (x : A) :
    JuliaLean.base.io.M World Square := ops.square x x

/-- Cube preserves the parser-level three-argument multiplication dispatch.
The pinned manual mathematical-operations.md:430-433 specifies this lowering. Julia source: base/intfuncs.jl:473. -/
-- Source: base/intfuncs.jl:473-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{3}) = x*x*x
-- /Source
def literalHardwareThree {World A Square Inverse Result : Type}
    (ops : HardwareLiteralOps World A Square Inverse Result) (x : A) :
    JuliaLean.base.io.M World Result := ops.cube x x x

/-- Negative one performs the selected inverse call. Julia source: base/intfuncs.jl:474. -/
-- Source: base/intfuncs.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{-1}) = inv(x)
-- /Source
def literalHardwareNegOne {World A Square Inverse Result : Type}
    (ops : HardwareLiteralOps World A Square Inverse Result) (x : A) :
    JuliaLean.base.io.M World Inverse := ops.inv x

/-- Negative two evaluates inverse once and passes its actual result twice. Julia source: base/intfuncs.jl:475. -/
-- Source: base/intfuncs.jl:475-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::HWNumber, ::Val{-2}) = (i=inv(x); i*i)
-- /Source
def literalHardwareNegTwo {World A Square Inverse Result : Type}
    (ops : HardwareLiteralOps World A Square Inverse Result) (x : A) :
    JuliaLean.base.io.M World Result := do
  let inverse ← ops.inv x
  ops.inverseSquare inverse inverse

/-- AbstractFloat does not restrict the Val parameter to a machine integer.
Invoke Base.^ with the original input and exponent and arbitrary result.
Source reference: base/intfuncs.jl:478. -/
-- Source: base/intfuncs.jl:478-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::AbstractFloat, ::Val{p}) where {p} = x^p
-- /Source
def literalFloatPower {World A P R : Type} (ops : PowerWrapperOps World A P R)
    (x : A) (p : P) : JuliaLean.base.io.M World R :=
  ops.call .basePower x p

/-- Complete AbstractFloat negative-one wrapper, preserving selected inverse
effects and a possibly different result type. Julia source: base/intfuncs.jl:479. -/
-- Source: base/intfuncs.jl:479-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline literal_pow(::typeof(^), x::AbstractFloat, ::Val{-1}) = inv(x)
-- /Source
def literalFloatNegOne {World A R : Type}
    (inv : A → JuliaLean.base.io.M World R) (x : A) : JuliaLean.base.io.M World R := inv x

/-- Exact runtime isa partition for BitInteger64. The proof is the native
width representation invariant; Other contains every value outside that
closed union, including Bool and 128-bit integers. References remain in Other.
Source reference: base/intfuncs.jl:485. -/
-- Source: base/intfuncs.jl:483-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function literal_pow(f::typeof(^), x, ::Val{p}) where {p}
--     if p < 0
--         if x isa BitInteger64
--             f(Float64(x), p) # inv would cause rounding, while Float64^Integer is able to compensate the inverse
--         else
--             f(inv(x), -p)
--         end
--     else
--         f(x, p)
--     end
-- end
-- /Source
inductive LiteralPowerArgument (Other : Type) where
  | native64 (type : IntTy) (width : type.bits ≤ 64) (value : JInt type)
  | other (value : Other)

/-- Open selected operations for the Base.^ literal fallback. The original
Val parameter, its negation and inverse value have independent carriers.
The less-than leaf includes adjacent conditional Bool validation.
The fixed Float64 conversion of a proven BitInteger64 input is not a callback.
Source reference: base/intfuncs.jl:483-493. -/
-- Source: base/intfuncs.jl:483-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function literal_pow(f::typeof(^), x, ::Val{p}) where {p}
--     if p < 0
--         if x isa BitInteger64
--             f(Float64(x), p) # inv would cause rounding, while Float64^Integer is able to compensate the inverse
--         else
--             f(inv(x), -p)
--         end
--     else
--         f(x, p)
--     end
-- end
-- /Source
structure LiteralBasePowerOps (World A P Negative Inverse R : Type) where
  less : P → JInt64 → JuliaLean.base.io.M World Bool
  inv : A → JuliaLean.base.io.M World Inverse
  neg : P → JuliaLean.base.io.M World Negative
  powerOriginal : PowerTailFunction → LiteralPowerArgument A → P → JuliaLean.base.io.M World R
  powerFloat : PowerTailFunction → JuliaLean.base.float.FV .f64 → P → JuliaLean.base.io.M World R
  powerInverse : PowerTailFunction → Inverse → Negative → JuliaLean.base.io.M World R

/-- Complete literal fallback. The negative test precedes the actual isa
partition. Native conversion calls installed Float64 behavior; the other
branch evaluates inv(x), then -p, then Base.^. The original exponent is
retained on the native-float and nonnegative paths. No unbounded arithmetic
replaces native negation. Julia source: base/intfuncs.jl:483-493. -/
-- Source: base/intfuncs.jl:483-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function literal_pow(f::typeof(^), x, ::Val{p}) where {p}
--     if p < 0
--         if x isa BitInteger64
--             f(Float64(x), p) # inv would cause rounding, while Float64^Integer is able to compensate the inverse
--         else
--             f(inv(x), -p)
--         end
--     else
--         f(x, p)
--     end
-- end
-- /Source
def literalBasePower {World A P Negative Inverse R : Type}
    (ops : LiteralBasePowerOps World A P Negative Inverse R)
    (x : LiteralPowerArgument A) (p : P) : JuliaLean.base.io.M World R := do
  if ← ops.less p (JuliaLean.base.int.lit .i64 0) then
    match x with
    | .native64 _ _ value =>
        ops.powerFloat .basePower (JuliaLean.base.float.floatOfInt .f64 value) p
    | .other value =>
        let inverse ← ops.inv value
        let negative ← ops.neg p
        ops.powerInverse .basePower inverse negative
  else ops.powerOriginal .basePower x p

/-- Concrete exponent adapter uses installed native comparison and wrapping
negation, including signed minima. Selected inverse/power methods remain open
because the base type and selected result are not fixed.
Source reference: base/intfuncs.jl:484,488. -/
-- Source: base/intfuncs.jl:483-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function literal_pow(f::typeof(^), x, ::Val{p}) where {p}
--     if p < 0
--         if x isa BitInteger64
--             f(Float64(x), p) # inv would cause rounding, while Float64^Integer is able to compensate the inverse
--         else
--             f(inv(x), -p)
--         end
--     else
--         f(x, p)
--     end
-- end
-- /Source
def literalNativeExponentOps {World A Inverse R : Type} (t : IntTy)
    (inv : A → JuliaLean.base.io.M World Inverse)
    (original : PowerTailFunction → LiteralPowerArgument A → JInt t → JuliaLean.base.io.M World R)
    (floating : PowerTailFunction → JuliaLean.base.float.FV .f64 → JInt t → JuliaLean.base.io.M World R)
    (inverse : PowerTailFunction → Inverse → JInt t → JuliaLean.base.io.M World R) :
    LiteralBasePowerOps World A (JInt t) (JInt t) Inverse R where
  less := fun value zero => pure (JuliaLean.base.int.lt value zero)
  inv := inv
  neg := fun value => pure (JuliaLean.base.int.neg value)
  powerOriginal := original
  powerFloat := floating
  powerInverse := inverse

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- All values produced by the selected Unsigned helper may have different types.
Source reference: base/intfuncs.jl:582-584. -/
-- Source: base/intfuncs.jl:582-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _powermod_mi_legal(mm::T) where {T<:Unsigned}
--     return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
-- end
-- /Source
structure PowermodMILegalUnsignedOps
    (World U Ty Max Size Count Bound Other : Type) where
  typeOf : U → Ty
  hasTypeMax : Ty → JuliaLean.base.io.M World (Bool ⊕ Other)
  typeMax : Ty → JuliaLean.base.io.M World Max
  sizeOfType : Ty → JuliaLean.base.io.M World Size
  shiftLeft : Size → JInt64 → JuliaLean.base.io.M World Count
  shiftRight : Max → Count → JuliaLean.base.io.M World Bound
  lessEqual : U → Bound → JuliaLean.base.io.M World (Bool ⊕ Other)

/-- Only the first operand of `&&` is checked here; the final comparison may return
non-Bool to its caller. Julia source: base/intfuncs.jl:582-584. -/
-- Source: base/intfuncs.jl:582-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _powermod_mi_legal(mm::T) where {T<:Unsigned}
--     return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
-- end
-- /Source
def powermodMILegalUnsigned {World U Ty Max Size Count Bound Other : Type}
    (ops : PowermodMILegalUnsignedOps World U Ty Max Size Count Bound Other)
    (mm : U) : JuliaLean.base.io.M World (Bool ⊕ Other) := do
  let T := ops.typeOf mm
  if ← gcdxAssertBool (← ops.hasTypeMax T) then
    let upper ← ops.typeMax T
    let size ← ops.sizeOfType T
    let shift ← ops.shiftLeft size (JuliaLean.base.int.lit .i64 2)
    let bound ← ops.shiftRight upper shift
    ops.lessEqual mm bound
  else pure (.inl false)

/-- Known source body or genuinely selected custom method.
Source reference: base/intfuncs.jl:581-584. -/
-- Source: base/intfuncs.jl:581-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _powermod_mi_legal(::Integer) = false
-- function _powermod_mi_legal(mm::T) where {T<:Unsigned}
--     return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
-- end
-- /Source
inductive PowermodMILegalRoute (World V Other : Type) where
  | integer
  | unsigned
  | custom (method : V → JuliaLean.base.io.M World (Bool ⊕ Other))
  | noMethod

/-- Dynamic values include the helper's changed intermediates.
Source reference: base/intfuncs.jl:581-584. -/
-- Source: base/intfuncs.jl:581-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _powermod_mi_legal(::Integer) = false
-- function _powermod_mi_legal(mm::T) where {T<:Unsigned}
--     return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
-- end
-- /Source
structure PowermodMILegalDispatchOps (World V Ty Other : Type) where
  unsigned : PowermodMILegalUnsignedOps World V Ty V V V V Other
  select : V → PowermodMILegalRoute World V Other

/-- Known fallback and Unsigned bodies are explicit, with no body callback.
Source reference: base/intfuncs.jl:581-584. -/
-- Source: base/intfuncs.jl:581-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _powermod_mi_legal(::Integer) = false
-- function _powermod_mi_legal(mm::T) where {T<:Unsigned}
--     return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
-- end
-- /Source
def powermodMILegalSelected {World V Ty Other : Type}
    (ops : PowermodMILegalDispatchOps World V Ty Other) (mm : V) :
    JuliaLean.base.io.M World (Bool ⊕ Other) :=
  match ops.select mm with
  | .integer => pure (.inl (JuliaLean.base.intfuncs.powermodMILegal_Integer mm))
  | .unsigned => powermodMILegalUnsigned ops.unsigned mm
  | .custom method => method mm
  | .noMethod => throw (.jl (.methodError "_powermod_mi_legal"))

/-- Native helper uses installed machine shifts, maximum, and comparison.
Source reference: base/intfuncs.jl:582-584. -/
-- Source: base/intfuncs.jl:582-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _powermod_mi_legal(mm::T) where {T<:Unsigned}
--     return Base.hastypemax(T) && (mm <= (typemax(T) >> (sizeof(T) << 2)))
-- end
-- /Source
def powermodMILegalBitsOps {World : Type} (t : IntTy) :
    PowermodMILegalUnsignedOps World (JInt t) IntTy (JInt t)
      JInt64 JInt64 (JInt t) Empty where
  typeOf := fun _ => t
  hasTypeMax := fun _ => pure (.inl (JuliaLean.base.intfuncs.hasTypeMax true true))
  typeMax := fun _ => pure (JuliaLean.base.int.typemax t)
  sizeOfType := fun u => pure (JuliaLean.base.int.lit .i64 (JuliaLean.base.int.sizeofT u))
  shiftLeft := fun value shift => pure (JuliaLean.base.int.shl_Int value shift)
  shiftRight := fun value shift => pure (JuliaLean.base.int.shr_Int value shift)
  lessEqual := fun a b => pure (.inl (JuliaLean.base.int.leSame a b))

/-- The custom route is only a genuinely selected other method, never a substitute
for this generic body. Julia source: base/intfuncs.jl:524-579. -/
-- Source: base/intfuncs.jl:530-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if p < 0
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
--             #else odd
--             return r
--         else
--             return powermod(invmod(x, m), -p, m)
--         end
-- /Source
inductive PowermodRecursiveRoute (World V : Type) where
  | generic
  | custom (method : V → V → V → JuliaLean.base.io.M World V)
  | noMethod

/-- `V` includes input integers, all changed local values and the inverse object.
Predicates preserve non-Bool values until source conditional validation. Every field
is the actual selected dependency, without arithmetic or termination assumptions.
Source reference: base/intfuncs.jl:524-579. -/
-- Source: base/intfuncs.jl:524-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function powermod(x::Integer, p::Integer, m::T) where T<:Integer
--     p == 0 && return mod(one(m),m)
--     # When the concrete type of p is signed and has the lowest value,
--     # `p < 0 && p == -p` is equivalent to `p == typemin(typeof(p))` for 2's complement representation.
--     # but will work for integer types like `BigInt` that don't have `typemin` defined
--     # It needs special handling otherwise will cause overflow problem.
--     if p < 0
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
--             #else odd
--             return r
--         else
--             return powermod(invmod(x, m), -p, m)
--         end
--     end
--     (m == 1 || m == -1) && return zero(m)
-- 
--     mm = uabs(m)
--     rr = one(mm)
--     bb = oftype(mm, mod(x, mm))
-- 
--     # legal && profitable
--     if _powermod_mi_legal(mm) && (p > 2sizeof(mm))
--         if bb == 0
--             rr = zero(mm)
--         else
--             mis = MultiplicativeInverses.multiplicativeinverse(mm)
--             Base.@assume_effects :terminates_locally while true
--                 if (p & 1) != 0
--                     rr = mod(rr * bb, mis)
--                 end
--                 p >>= 1
--                 p == 0 && break
--                 bb = mod(bb * bb, mis)
--             end
--         end
--     else
--         if bb == 0
--             rr = zero(mm)
--         else
--             Base.@assume_effects :terminates_locally while true
--                 if (p & 1) != 0
--                     rr = oftype(mm, mod(widemul(rr, bb), mm))
--                 end
--                 p >>= 1
--                 p == 0 && break
--                 bb = oftype(mm, mod(widemul(bb, bb), mm))
--             end
--         end
--     end
--     r = oftype(m, rr)
--     return (iszero(r) || (m > 0)) ? r : r + m
-- end
-- /Source
structure PowermodOps (World V Ty Other : Type) where
  typeOf : V → Ty
  equalLiteral : V → JInt64 → JuliaLean.base.io.M World (Bool ⊕ Other)
  equal : V → V → JuliaLean.base.io.M World (Bool ⊕ Other)
  lessLiteral : V → JInt64 → JuliaLean.base.io.M World (Bool ⊕ Other)
  greaterLiteral : V → JInt64 → JuliaLean.base.io.M World (Bool ⊕ Other)
  greater : V → V → JuliaLean.base.io.M World (Bool ⊕ Other)
  notEqualLiteral : V → JInt64 → JuliaLean.base.io.M World (Bool ⊕ Other)
  isodd : V → JuliaLean.base.io.M World (Bool ⊕ Other)
  iszero : V → JuliaLean.base.io.M World (Bool ⊕ Other)
  neg : V → JuliaLean.base.io.M World V
  divLiteral : V → JInt64 → JuliaLean.base.io.M World V
  one : V → JuliaLean.base.io.M World V
  zero : V → JuliaLean.base.io.M World V
  uabs : V → JuliaLean.base.io.M World V
  mod : V → V → JuliaLean.base.io.M World V
  oftype : V → V → JuliaLean.base.io.M World V
  widemul : V → V → JuliaLean.base.io.M World V
  mul : V → V → JuliaLean.base.io.M World V
  add : V → V → JuliaLean.base.io.M World V
  bitAndLiteral : V → JInt64 → JuliaLean.base.io.M World V
  shiftRightLiteral : V → JInt64 → JuliaLean.base.io.M World V
  sizeOf : V → JuliaLean.base.io.M World V
  mulLiteralLeft : JInt64 → V → JuliaLean.base.io.M World V
  multiplicativeinverse : V → JuliaLean.base.io.M World V
  invmod : V → V → JuliaLean.base.io.M World V
  convert : Ty → V → JuliaLean.base.io.M World V
  isInstance : V → Ty → Bool
  legal : PowermodMILegalDispatchOps World V Ty Other
  recursiveDispatch : V → V → V → PowermodRecursiveRoute World V

/-- Saved continuation for the non-tail half-power call.
Source reference: base/intfuncs.jl:531-536. -/
-- Source: base/intfuncs.jl:531-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
--             #else odd
-- /Source
structure PowermodHalfFrame (V Ty : Type) where
  inverse : V
  exponent : V
  modulus : V
  modulusType : Ty

/-- Explicit stack does not assume custom operations decrease an exponent.
Source reference: base/intfuncs.jl:524-579. -/
-- Source: base/intfuncs.jl:530-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if p < 0
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
--             #else odd
--             return r
--         else
--             return powermod(invmod(x, m), -p, m)
--         end
-- /Source
inductive PowermodState (V Ty : Type) where
  | call (x p m : V) (T : Ty) (stack : List (PowermodHalfFrame V Ty))
  | returned (result : V) (stack : List (PowermodHalfFrame V Ty))
  | loop (p mm rr bb m : V) (T : Ty) (inverse : Option V)
      (stack : List (PowermodHalfFrame V Ty))
  | finish (rr m : V) (T : Ty) (stack : List (PowermodHalfFrame V Ty))

/-- Typed-local assignment calls the selected conversion, then the builtin type
assertion; a wrongly typed conversion result raises TypeError without executing
later source operations. Julia source: base/intfuncs.jl:534-535,577. -/
-- Source: base/intfuncs.jl:531-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
-- /Source
def powermodAssignTyped {World V Ty Other : Type}
    (ops : PowermodOps World V Ty Other) (T : Ty) (value : V) :
    JuliaLean.base.io.M World V := do
  let converted ← ops.convert T value
  if ops.isInstance converted T then pure converted
  else throw (JuliaLean.base.io.Error.foreignError "TypeError" "")

/-- Recursive dispatch enters the actual generic body again; other genuinely
selected methods remain dependencies. Julia source: base/intfuncs.jl:533,539. -/
-- Source: base/intfuncs.jl:530-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if p < 0
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
--             #else odd
--             return r
--         else
--             return powermod(invmod(x, m), -p, m)
--         end
-- /Source
def powermodEnterRecursive {World V Ty Other : Type}
    (ops : PowermodOps World V Ty Other) (x p m : V)
    (stack : List (PowermodHalfFrame V Ty)) :
    JuliaLean.base.io.M World (Sum V (PowermodState V Ty)) := do
  match ops.recursiveDispatch x p m with
  | .generic => pure (.inr (.call x p m (ops.typeOf m) stack))
  | .custom method => pure (.inr (.returned (← method x p m) stack))
  | .noMethod => throw (.jl (.methodError "powermod"))

/-- Complete fuel-free body with an explicit recursive continuation stack.
The local `r::T` declaration converts/checks every assignment to `r`, including the
positive-path assignment. Native literals, conditional checks, separate occurrences
of `-p`, error identity, mutation order and divergence are retained.
Source reference: base/intfuncs.jl:524-579. -/
-- Source: base/intfuncs.jl:524-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function powermod(x::Integer, p::Integer, m::T) where T<:Integer
--     p == 0 && return mod(one(m),m)
--     # When the concrete type of p is signed and has the lowest value,
--     # `p < 0 && p == -p` is equivalent to `p == typemin(typeof(p))` for 2's complement representation.
--     # but will work for integer types like `BigInt` that don't have `typemin` defined
--     # It needs special handling otherwise will cause overflow problem.
--     if p < 0
--         if p == -p
--             imod = invmod(x, m)
--             rhalf = powermod(imod, -(p÷2), m)
--             r::T = mod(widemul(rhalf, rhalf), m)
--             isodd(p) && (r = mod(widemul(r, imod), m))
--             #else odd
--             return r
--         else
--             return powermod(invmod(x, m), -p, m)
--         end
--     end
--     (m == 1 || m == -1) && return zero(m)
-- 
--     mm = uabs(m)
--     rr = one(mm)
--     bb = oftype(mm, mod(x, mm))
-- 
--     # legal && profitable
--     if _powermod_mi_legal(mm) && (p > 2sizeof(mm))
--         if bb == 0
--             rr = zero(mm)
--         else
--             mis = MultiplicativeInverses.multiplicativeinverse(mm)
--             Base.@assume_effects :terminates_locally while true
--                 if (p & 1) != 0
--                     rr = mod(rr * bb, mis)
--                 end
--                 p >>= 1
--                 p == 0 && break
--                 bb = mod(bb * bb, mis)
--             end
--         end
--     else
--         if bb == 0
--             rr = zero(mm)
--         else
--             Base.@assume_effects :terminates_locally while true
--                 if (p & 1) != 0
--                     rr = oftype(mm, mod(widemul(rr, bb), mm))
--                 end
--                 p >>= 1
--                 p == 0 && break
--                 bb = oftype(mm, mod(widemul(bb, bb), mm))
--             end
--         end
--     end
--     r = oftype(m, rr)
--     return (iszero(r) || (m > 0)) ? r : r + m
-- end
-- /Source
def powermodGeneric {World V Ty Other : Type}
    (ops : PowermodOps World V Ty Other) (x p m : V) :
    JuliaLean.base.io.M World V :=
  JuliaLean.base.io.whileLoop (fun (state : PowermodState V Ty) => do
    match state with
    | .call x p m T stack =>
      if ← gcdxAssertBool (← ops.equalLiteral p (JuliaLean.base.int.lit .i64 0)) then
        let one ← ops.one m
        pure (.inr (.returned (← ops.mod one m) stack))
      else if ← gcdxAssertBool (← ops.lessLiteral p (JuliaLean.base.int.lit .i64 0)) then
        let negp ← ops.neg p
        if ← gcdxAssertBool (← ops.equal p negp) then
          let inverse ← ops.invmod x m
          let half ← ops.divLiteral p (JuliaLean.base.int.lit .i64 2)
          let exponent ← ops.neg half
          powermodEnterRecursive ops inverse exponent m
            ({ inverse := inverse, exponent := p, modulus := m, modulusType := T } :: stack)
        else
          let inverse ← ops.invmod x m
          let exponent ← ops.neg p
          powermodEnterRecursive ops inverse exponent m stack
      else
        let unit ← do
          if ← gcdxAssertBool (← ops.equalLiteral m (JuliaLean.base.int.lit .i64 1)) then
            pure true
          else gcdxAssertBool (← ops.equalLiteral m (JuliaLean.base.int.lit .i64 (-1)))
        if unit then
          pure (.inr (.returned (← ops.zero m) stack))
        else
          let mm ← ops.uabs m
          let rr ← ops.one mm
          let initial ← ops.mod x mm
          let bb ← ops.oftype mm initial
          let optimized ← if ← gcdxAssertBool (← powermodMILegalSelected ops.legal mm) then do
              let size ← ops.sizeOf mm
              let threshold ← ops.mulLiteralLeft (JuliaLean.base.int.lit .i64 2) size
              gcdxAssertBool (← ops.greater p threshold)
            else pure false
          if ← gcdxAssertBool (← ops.equalLiteral bb (JuliaLean.base.int.lit .i64 0)) then
            pure (.inr (.finish (← ops.zero mm) m T stack))
          else if optimized then
            let inverse ← ops.multiplicativeinverse mm
            pure (.inr (.loop p mm rr bb m T (some inverse) stack))
          else pure (.inr (.loop p mm rr bb m T none stack))
    | .returned result stack =>
      match stack with
      | [] => pure (.inl result)
      | frame :: rest =>
        let square ← ops.widemul result result
        let residue ← ops.mod square frame.modulus
        let r ← powermodAssignTyped ops frame.modulusType residue
        let r ← if ← gcdxAssertBool (← ops.isodd frame.exponent) then do
            let product ← ops.widemul r frame.inverse
            let residue ← ops.mod product frame.modulus
            powermodAssignTyped ops frame.modulusType residue
          else pure r
        pure (.inr (.returned r rest))
    | .loop p mm rr bb m T inverse stack =>
      let mask ← ops.bitAndLiteral p (JuliaLean.base.int.lit .i64 1)
      let rr ← if ← gcdxAssertBool (← ops.notEqualLiteral mask (JuliaLean.base.int.lit .i64 0)) then
          match inverse with
          | some mis => do
            let product ← ops.mul rr bb
            ops.mod product mis
          | none => do
            let product ← ops.widemul rr bb
            let residue ← ops.mod product mm
            ops.oftype mm residue
        else pure rr
      let p ← ops.shiftRightLiteral p (JuliaLean.base.int.lit .i64 1)
      if ← gcdxAssertBool (← ops.equalLiteral p (JuliaLean.base.int.lit .i64 0)) then
        pure (.inr (.finish rr m T stack))
      else
        let bb ← match inverse with
          | some mis => do
            let product ← ops.mul bb bb
            ops.mod product mis
          | none => do
            let product ← ops.widemul bb bb
            let residue ← ops.mod product mm
            ops.oftype mm residue
        pure (.inr (.loop p mm rr bb m T inverse stack))
    | .finish rr m T stack =>
      let result ← ops.oftype m rr
      let r ← powermodAssignTyped ops T result
      let positive ← do
        if ← gcdxAssertBool (← ops.iszero r) then pure true
        else gcdxAssertBool (← ops.greaterLiteral m (JuliaLean.base.int.lit .i64 0))
      let result ← if positive then pure r else ops.add r m
      pure (.inr (.returned result stack)))
    (.call x p m (ops.typeOf m) [])

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Open Unsigned dispatch leaves of base/intfuncs.jl:589. Distinct carriers
retain custom oneunit, subtraction, top-bit and shift result types. -/
-- Source: base/intfuncs.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- /Source
structure NextPow2UnsignedOps (m : Type → Type) (U One D K R : Type) where
  oneunit : U → m One
  sub : U → One → m D
  topBit : D → m K
  shift : One → K → m R

/-- The two oneunit calls are distinct and execute left to right, including
when their outputs alias mutable objects. Julia source: base/intfuncs.jl:589. -/
-- Source: base/intfuncs.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- /Source
def nextpow2Unsigned {m : Type → Type} [Monad m] {U One D K R : Type}
    (ops : NextPow2UnsignedOps m U One D K R) (x : U) : m R := do
  let left ← ops.oneunit x
  let right ← ops.oneunit x
  let difference ← ops.sub x right
  let count ← ops.topBit difference
  ops.shift left count

/-- Open Unsigned dispatch leaves of base/intfuncs.jl:591. The subtraction
receives the actual native Int literal, and unsigned may change its type. -/
-- Source: base/intfuncs.jl:591-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- /Source
structure PrevPow2UnsignedOps (m : Type → Type) (U One K D Shift R : Type) where
  one : U → m One
  topBit : U → m K
  subOne : K → JInt64 → m D
  unsigned : D → m Shift
  shift : One → Shift → m R

/-- Source-order effects and intermediate types, including the unsigned
conversion of a negative shift count. Julia source: base/intfuncs.jl:591. -/
-- Source: base/intfuncs.jl:591-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- /Source
def prevpow2Unsigned {m : Type → Type} [Monad m] {U One K D Shift R : Type}
    (ops : PrevPow2UnsignedOps m U One K D Shift R) (x : U) : m R := do
  let left ← ops.one x
  let top ← ops.topBit x
  let count ← ops.subOne top (JuliaLean.base.int.lit .i64 1)
  let shift ← ops.unsigned count
  ops.shift left shift

/-- Selected function and method routes for the recursive call in
base/intfuncs.jl:590,592. A custom route denotes the actually selected method;
known Integer/Unsigned routes execute the bodies below. -/
-- Source: base/intfuncs.jl:589-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
inductive Pow2Function where
  | next
  | prev
  deriving DecidableEq

/-- Actual dispatch alternatives for the recursive power-of-two call. Known
Integer and Unsigned branches use their implemented bodies; custom records
a selected other method. Julia source: base/intfuncs.jl:589-592. -/
-- Source: base/intfuncs.jl:589-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
inductive Pow2Route where
  | integer
  | unsigned
  | custom
  | noMethod
  deriving DecidableEq

/-- Core typeof is a pure projection of runtime representation. V may be a
sum of all Julia values; custom unsigned need not return an Unsigned value.
lessZero includes the conditional's adjacent Bool validation. The two neg
calls can select different methods because intermediates can change type.
Source reference: base/intfuncs.jl:589-592. -/
-- Source: base/intfuncs.jl:589-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
structure Pow2IntegerOps (World V Ty : Type) where
  typeOf : V → Ty
  lessZero : V → JInt64 → JuliaLean.base.io.M World Bool
  neg : V → JuliaLean.base.io.M World V
  unsigned : V → JuliaLean.base.io.M World V
  reinterpret : Ty → V → JuliaLean.base.io.M World V
  select : Pow2Function → V → Pow2Route
  custom : Pow2Function → V → JuliaLean.base.io.M World V
  nextUnsigned : NextPow2UnsignedOps (JuliaLean.base.io.M World) V V V V V
  prevUnsigned : PrevPow2UnsignedOps (JuliaLean.base.io.M World) V V V V V V

/-- Saved lexical operands while an Integer recursive call is pending.
Source reference: base/intfuncs.jl:590,592. -/
-- Source: base/intfuncs.jl:590-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
structure Pow2Frame (Ty : Type) where
  originalType : Ty
  negateReturned : Bool

/-- Explicit call/return machine for the source recursion; it has no fuel
bound and therefore retains genuinely divergent custom unsigned cycles.
Source reference: base/intfuncs.jl:590,592. -/
-- Source: base/intfuncs.jl:590-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
inductive Pow2State (V Ty : Type) where
  | body (value : V) (frames : List (Pow2Frame Ty))
  | dispatch (value : V) (frames : List (Pow2Frame Ty))
  | returned (value : V) (frames : List (Pow2Frame Ty))

/-- Complete Integer recursion, including method changes, first errors and
unwinding order. A recursive Integer target re-enters this actual body;
Unsigned targets invoke the actual new Unsigned source body. Only an actually
selected custom target is a parameter. Julia source: base/intfuncs.jl:590,592. -/
-- Source: base/intfuncs.jl:589-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
def pow2IntegerLoop {World V Ty : Type} (ops : Pow2IntegerOps World V Ty)
    (fn : Pow2Function) (x : V) : JuliaLean.base.io.M World V :=
  JuliaLean.base.io.whileLoop (fun state => do
    match state with
    | .body value frames =>
        let originalType := ops.typeOf value
        let negative ← ops.lessZero value (JuliaLean.base.int.lit .i64 0)
        let argument ← if negative then ops.neg value else pure value
        let argument ← ops.unsigned argument
        pure (.inr (.dispatch argument ({ originalType := originalType, negateReturned := negative } :: frames)))
    | .dispatch value frames =>
        match ops.select fn value with
        | .integer => pure (.inr (.body value frames))
        | .unsigned =>
            let result ← match fn with
              | .next => nextpow2Unsigned ops.nextUnsigned value
              | .prev => prevpow2Unsigned ops.prevUnsigned value
            pure (.inr (.returned result frames))
        | .custom =>
            let result ← ops.custom fn value
            pure (.inr (.returned result frames))
        | .noMethod =>
            throw (.jl (.methodError (match fn with | .next => "_nextpow2" | .prev => "_prevpow2")))
    | .returned value frames =>
        match frames with
        | [] => pure (.inl value)
        | frame :: rest =>
            let result ← if frame.negateReturned then ops.neg value else pure value
            let result ← ops.reinterpret frame.originalType result
            pure (.inr (.returned result rest))) (Pow2State.body x [])

/-- The queued Integer next-power body, with all recursive calls implemented
by pow2IntegerLoop. Julia source: base/intfuncs.jl:590. -/
-- Source: base/intfuncs.jl:590-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_nextpow2(unsigned(-x)) : _nextpow2(unsigned(x)))
-- /Source
def nextpow2Integer {World V Ty : Type} (ops : Pow2IntegerOps World V Ty) (x : V) :=
  pow2IntegerLoop ops .next x

/-- The queued Integer previous-power body. Julia source: base/intfuncs.jl:592. -/
-- Source: base/intfuncs.jl:592-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _prevpow2(x::Integer) = reinterpret(typeof(x),x < 0 ? -_prevpow2(unsigned(-x)) : _prevpow2(unsigned(x)))
-- /Source
def prevpow2Integer {World V Ty : Type} (ops : Pow2IntegerOps World V Ty) (x : V) :=
  pow2IntegerLoop ops .prev x

/-- Bool is distinguished from every other possible returned Julia value.
Unlike a conditional operand, the final operand of && is not Bool-checked.
Source reference: base/intfuncs.jl:622,624; manual/control-flow.md:378-389. -/
-- Source: base/intfuncs.jl:622-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Number) = isreal(x) && ispow2(real(x))
-- 
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
inductive Pow2BoolResult (Other : Type) where
  | boolean (value : Bool)
  | other (value : Other)
  deriving DecidableEq

/-- Greater-than includes the adjacent Bool check; final equality deliberately
returns an arbitrary dynamic value. Julia source: base/intfuncs.jl:624. -/
-- Source: base/intfuncs.jl:624-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
structure IsPow2IntegerOps (m : Type → Type) (I Count Other : Type) where
  greaterZero : I → JInt64 → m Bool
  countOnes : I → m Count
  equalOne : Count → JInt64 → m (Pow2BoolResult Other)

/-- False short-circuits before population count. The final equality result
is returned unchanged, even when custom dispatch returns a non-Bool value.
Source reference: base/intfuncs.jl:624. -/
-- Source: base/intfuncs.jl:624-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
def ispow2Integer {m : Type → Type} [Monad m] {I Count Other : Type}
    (ops : IsPow2IntegerOps m I Count Other) (x : I) : m (Pow2BoolResult Other) := do
  if ← ops.greaterZero x (JuliaLean.base.int.lit .i64 0) then
    let count ← ops.countOnes x
    ops.equalOne count (JuliaLean.base.int.lit .i64 1)
  else
    pure (.boolean false)

/-- Runtime dispatch after the Number method obtains real(x), including
its own recursive fallback and the Integer specialization.
Source reference: base/intfuncs.jl:622-624. -/
-- Source: base/intfuncs.jl:622-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Number) = isreal(x) && ispow2(real(x))
-- 
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
inductive IsPow2Route where
  | number
  | integer
  | custom
  | noMethod
  deriving DecidableEq

/-- Open Number dispatch with exact known self-recursive and Integer routes.
isReal includes the adjacent condition Bool validation. V ranges over all
intermediates returned by custom real, including non-Numbers; the selection
then records the actual runtime method or absence of a method.
Source reference: base/intfuncs.jl:622,624. -/
-- Source: base/intfuncs.jl:622-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Number) = isreal(x) && ispow2(real(x))
-- 
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
structure IsPow2NumberOps (World V Count Other : Type) where
  isReal : V → JuliaLean.base.io.M World Bool
  real : V → JuliaLean.base.io.M World V
  select : V → IsPow2Route
  custom : V → JuliaLean.base.io.M World (Pow2BoolResult Other)
  integer : IsPow2IntegerOps (JuliaLean.base.io.M World) V Count Other

/-- Actual tail recursion of the Number fallback, including a custom real
returning another Number that selects this same fallback, or an Integer that
selects the actual Integer body. Julia source: base/intfuncs.jl:622. -/
-- Source: base/intfuncs.jl:622-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Number) = isreal(x) && ispow2(real(x))
-- 
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
def ispow2Number {World V Count Other : Type}
    (ops : IsPow2NumberOps World V Count Other) (x : V) :
    JuliaLean.base.io.M World (Pow2BoolResult Other) :=
  JuliaLean.base.io.whileLoop (fun value => do
    if ← ops.isReal value then
      let argument ← ops.real value
      match ops.select argument with
      | .number => pure (.inr argument)
      | .integer => pure (.inl (← ispow2Integer ops.integer argument))
      | .custom => pure (.inl (← ops.custom argument))
      | .noMethod => throw (.jl (.methodError "ispow2"))
    else
      pure (.inl (.boolean false))) x

/-- Concrete one(x) adapter reusing installed Base oneValue and one(T).
Dependency: base/number.jl:405-406; use: base/intfuncs.jl:589,591. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def pow2BitsOne {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  JuliaLean.base.number.oneValue (fun _ => ()) (fun _ => gcdxBitsOne t) x

/-- Installed oneunit(x) with its actual extra T conversion.
Dependency: base/number.jl:430; use: base/intfuncs.jl:589. -/
-- Source: base/number.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- oneunit(x::T) where {T} = T(one(x))
-- /Source
def pow2BitsOneunit {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  JuliaLean.base.number.oneunitValue pow2BitsOne (JuliaLean.base.int.convert t) x

/-- Native instantiation using installed Base machine operations, including
native signed Int shift counts. Julia source: base/intfuncs.jl:589. -/
-- Source: base/intfuncs.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _nextpow2(x::Unsigned) = oneunit(x)<<(top_set_bit(x-oneunit(x)))
-- /Source
def nextpow2UnsignedBitsOps {World : Type} (t : IntTy) :
    NextPow2UnsignedOps (JuliaLean.base.io.M World) (JInt t) (JInt t) (JInt t) JInt64 (JInt t) where
  oneunit := fun x => JuliaLean.base.io.liftJl (pow2BitsOneunit x)
  sub := fun x y => pure (JuliaLean.base.int.sub x y)
  topBit := fun x => pure (JuliaLean.base.int.top_set_bit x)
  shift := fun x n => pure (JuliaLean.base.int.shl_Int x n)

/-- Native unsigned shift conversion preserves the zero-input huge-count
case rather than replacing it by mathematical subtraction on Nat.
Source reference: base/intfuncs.jl:591. -/
-- Source: base/intfuncs.jl:591-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _prevpow2(x::Unsigned) = one(x) << unsigned(top_set_bit(x)-1)
-- /Source
def prevpow2UnsignedBitsOps {World : Type} (t : IntTy) :
    PrevPow2UnsignedOps (JuliaLean.base.io.M World) (JInt t) (JInt t) JInt64 JInt64 (JInt .u64) (JInt t) where
  one := fun x => JuliaLean.base.io.liftJl (pow2BitsOne x)
  topBit := fun x => pure (JuliaLean.base.int.top_set_bit x)
  subOne := fun x one => pure (JuliaLean.base.int.sub x one)
  unsigned := fun x => pure (JuliaLean.base.int.unsigned x)
  shift := fun x n => pure (JuliaLean.base.int.shl_BitInteger_BitUnsigned x n)

/-- Installed comparison, population count and equality for every native
integer width. Julia source: base/intfuncs.jl:624. -/
-- Source: base/intfuncs.jl:624-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Integer) = x > 0 && count_ones(x) == 1
-- /Source
def ispow2IntegerBitsOps {World : Type} (t : IntTy) :
    IsPow2IntegerOps (JuliaLean.base.io.M World) (JInt t) JInt64 Empty where
  greaterZero := fun x zero => pure
    (JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt x zero)
  countOnes := fun x => pure (JuliaLean.base.int.count_ones x)
  equalOne := fun count one => pure (.boolean (JuliaLean.base.int.eq count one))

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- A current heap view of the concrete global Vector{UInt64}
powers_of_ten. const fixes its binding, not its mutable elements or length.
The installed array header/window invariant gives native-sized storage;
UInt64 is an isbits element, so its live cells contain actual bits rather
than unassigned reference slots. Prior mutations, resizing and aliases are
represented by the current memory/header. Julia source: base/intfuncs.jl:718-729. -/
-- Source: base/intfuncs.jl:718-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const powers_of_ten = [
--     0x0000000000000001, 0x000000000000000a, 0x0000000000000064, 0x00000000000003e8,
--     0x0000000000002710, 0x00000000000186a0, 0x00000000000f4240, 0x0000000000989680,
--     0x0000000005f5e100, 0x000000003b9aca00, 0x00000002540be400, 0x000000174876e800,
--     0x000000e8d4a51000, 0x000009184e72a000, 0x00005af3107a4000, 0x00038d7ea4c68000,
--     0x002386f26fc10000, 0x016345785d8a0000, 0x0de0b6b3a7640000, 0x8ac7230489e80000,
-- ]
-- function bit_ndigits0z(x::Base.BitUnsigned64)
--     lz = top_set_bit(x)
--     nd = (1233*lz)>>12+1
--     return nd - (x < powers_of_ten[nd])
-- end
-- /Source
structure DecimalTable where
  memory : JuliaLean.base.array.MutableMemory (JInt .u64)
  handle : Nat
  valid : memory.validVector handle
  assigned : ∀ cell ∈ memory.contents handle, ∃ value, cell = some value

/-- The external mutable world and the current global table heap. 
Source reference: base/intfuncs.jl:718-729. -/
-- Source: base/intfuncs.jl:718-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const powers_of_ten = [
--     0x0000000000000001, 0x000000000000000a, 0x0000000000000064, 0x00000000000003e8,
--     0x0000000000002710, 0x00000000000186a0, 0x00000000000f4240, 0x0000000000989680,
--     0x0000000005f5e100, 0x000000003b9aca00, 0x00000002540be400, 0x000000174876e800,
--     0x000000e8d4a51000, 0x000009184e72a000, 0x00005af3107a4000, 0x00038d7ea4c68000,
--     0x002386f26fc10000, 0x016345785d8a0000, 0x0de0b6b3a7640000, 0x8ac7230489e80000,
-- ]
-- function bit_ndigits0z(x::Base.BitUnsigned64)
--     lz = top_set_bit(x)
--     nd = (1233*lz)>>12+1
--     return nd - (x < powers_of_ten[nd])
-- end
-- /Source
abbrev DecimalWorld (W : Type) := W × DecimalTable

/-- Exception-class adaptation of the installed concrete Array model.
No error is replaced by an ordinary value. Julia dependency:
base/essentials.jl:1073-1077 and its scalar Array memory/bounds primitives. -/
-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
def decimalArrayError : JuliaLean.base.array.Error → JuliaLean.base.io.Error
  | .argument message => .jl (.argumentError message)
  | .bounds => .jl .boundsError
  | .inexact => .jl (.inexactError "")
  | .overflow => .jl (.overflowError "")
  | .divide => .jl .divideError
  | .typeError context => .foreignError "TypeError" context
  | .dimensionMismatch message => .foreignError "DimensionMismatch" message
  | .method name => .jl (.methodError name)
  | .assertion message => .foreignError "AssertionError" message
  | .concurrency message => .foreignError "ConcurrencyViolationError" message
  | .thrownNothing => .foreignError "Nothing" ""
  | .undefinedReference => .foreignError "UndefRefError" ""
  | .showError error => .showError error

/-- Read the current concrete global array through the installed mutableGet
model. This installed read does not mutate its heap. The snapshot is taken at
the actual read, so earlier custom operations in a caller may change table
contents or resize it. Julia source use: base/intfuncs.jl:728. -/
-- Source: base/intfuncs.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return nd - (x < powers_of_ten[nd])
-- /Source
def decimalReadTable {W : Type} (index : JInt64) :
    JuliaLean.base.io.M (DecimalWorld W) (JInt .u64) := do
  let (_, table) ← JuliaLean.base.io.getWorld
  let (result, _) := (JuliaLean.base.array.mutableGet table.handle index).run table.memory
  match result with
  | .ok value => pure value
  | .error error => throw (decimalArrayError error)

/-- Exact concrete native union Base.BitUnsigned64. 
Source reference: base/int.jl:11,15,31. -/
-- Source: base/int.jl:10-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSigned32_types      = (Int8, Int16, Int32)
-- const BitUnsigned32_types    = (UInt8, UInt16, UInt32)
-- const BitInteger32_types     = (BitSigned32_types..., BitUnsigned32_types...)
-- 
-- const BitSigned64_types      = (BitSigned32_types..., Int64)
-- const BitUnsigned64_types    = (BitUnsigned32_types..., UInt64)
-- const BitInteger64_types     = (BitSigned64_types..., BitUnsigned64_types...)
-- 
-- const BitSigned_types        = (BitSigned64_types..., Int128)
-- const BitUnsigned_types      = (BitUnsigned64_types..., UInt128)
-- const BitInteger_types       = (BitSigned_types..., BitUnsigned_types...)
-- 
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- 
-- const BitSigned32      = Union{BitSigned32_types...}
-- const BitUnsigned32    = Union{BitUnsigned32_types...}
-- const BitInteger32     = Union{BitInteger32_types...}
-- 
-- const BitSigned64      = Union{BitSigned64_types...}
-- const BitUnsigned64    = Union{BitUnsigned64_types...}
-- const BitInteger64     = Union{BitInteger64_types...}
-- 
-- const BitSigned        = Union{BitSigned_types...}
-- const BitUnsigned      = Union{BitUnsigned_types...}
-- const BitInteger       = Union{BitInteger_types...}
-- /Source
inductive DecimalUnsigned64 where
  | u8 (value : JInt .u8)
  | u16 (value : JInt .u16)
  | u32 (value : JInt .u32)
  | u64 (value : JInt .u64)

/-- Shared source body used only by the four native unsigned <=64 branches.
All intermediates are native Int, the global read is the installed concrete
Array operation, and Bool subtraction uses the installed Bool-to-Int model.
Source reference: base/intfuncs.jl:725-729. -/
-- Source: base/intfuncs.jl:725-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_ndigits0z(x::Base.BitUnsigned64)
--     lz = top_set_bit(x)
--     nd = (1233*lz)>>12+1
--     return nd - (x < powers_of_ten[nd])
-- end
-- /Source
def bitDigits64Body {W : Type} {t : IntTy} (x : JInt t) :
    JuliaLean.base.io.M (DecimalWorld W) JInt64 := do
  let lz := JuliaLean.base.int.top_set_bit x
  let product := JuliaLean.base.int.mulSame (JuliaLean.base.int.lit .i64 1233) lz
  let quotient := JuliaLean.base.int.shr_Int product (JuliaLean.base.int.lit .i64 12)
  let nd := JuliaLean.base.int.add quotient (JuliaLean.base.int.lit .i64 1)
  let power ← decimalReadTable nd
  let correction := JuliaLean.base.int.ofBool .i64 (JuliaLean.base.int.lt x power)
  pure (JuliaLean.base.int.sub nd correction)

/-- Full BitUnsigned64 method with exactly its four concrete input types.
Its mutable global table is read from the live world, including resized or
modified vectors. Julia source: base/intfuncs.jl:725-729. -/
-- Source: base/intfuncs.jl:725-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_ndigits0z(x::Base.BitUnsigned64)
--     lz = top_set_bit(x)
--     nd = (1233*lz)>>12+1
--     return nd - (x < powers_of_ten[nd])
-- end
-- /Source
def bitDigits64 {W : Type} : DecimalUnsigned64 →
    JuliaLean.base.io.M (DecimalWorld W) JInt64
  | .u8 value => bitDigits64Body value
  | .u16 value => bitDigits64Body value
  | .u32 value => bitDigits64Body value
  | .u64 value => bitDigits64Body value

/-- Necessary known UInt64 instance of the unsigned forwarding method,
used by the UInt128 body. It calls the complete concrete decimal method,
with the same live global world. Julia source: base/intfuncs.jl:740. -/
-- Source: base/intfuncs.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ndigits0z(x::BitUnsigned) = bit_ndigits0z(x)
-- /Source
def decimalUInt64 {W : Type} (x : JInt .u64) :
    JuliaLean.base.io.M (DecimalWorld W) JInt64 := bitDigits64 (.u64 x)

/-- Complete UInt128 source loop. Mixed UInt128/UInt64 division is closed
through installed same-sign promotion and native division. The final UInt64
constructor is checked conversion, not remainder-to-type. Native n retains
the source Int width and wrapping additions. Julia source: base/intfuncs.jl:730-737. -/
-- Source: base/intfuncs.jl:730-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_ndigits0z(x::UInt128)
--     n = 0
--     while x > 0x8ac7230489e80000 # 10e18
--         x = div(x,0x8ac7230489e80000)
--         n += 19
--     end
--     return n + ndigits0z(UInt64(x))
-- end
-- /Source
def bitDigits128 {W : Type} (x : JInt .u128) :
    JuliaLean.base.io.M (DecimalWorld W) JInt64 := do
  let limit := JuliaLean.base.int.lit .u64 0x8ac7230489e80000
  let (x, n) ← JuliaLean.base.io.whileLoop (fun (state : JInt .u128 × JInt64) => do
    if JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt state.1 limit then
      let (a, b) := JuliaLean.base.int.promoteSameSign state.1 limit
      let quotient ← JuliaLean.base.io.liftJl (JuliaLean.base.int.divSame a b)
      let quotient := JuliaLean.base.int.remT .u128 quotient
      let n := JuliaLean.base.int.add state.2 (JuliaLean.base.int.lit .i64 19)
      pure (.inr (quotient, n))
    else pure (.inl state)) (x, JuliaLean.base.int.lit .i64 0)
  let narrowed ← JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .u64 x)
  let digits ← decimalUInt64 narrowed
  pure (JuliaLean.base.int.add n digits)

/-- Exact concrete native BitUnsigned union. 
Source reference: base/int.jl:11,15,19,35. -/
-- Source: base/int.jl:10-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSigned32_types      = (Int8, Int16, Int32)
-- const BitUnsigned32_types    = (UInt8, UInt16, UInt32)
-- const BitInteger32_types     = (BitSigned32_types..., BitUnsigned32_types...)
-- 
-- const BitSigned64_types      = (BitSigned32_types..., Int64)
-- const BitUnsigned64_types    = (BitUnsigned32_types..., UInt64)
-- const BitInteger64_types     = (BitSigned64_types..., BitUnsigned64_types...)
-- 
-- const BitSigned_types        = (BitSigned64_types..., Int128)
-- const BitUnsigned_types      = (BitUnsigned64_types..., UInt128)
-- const BitInteger_types       = (BitSigned_types..., BitUnsigned_types...)
-- 
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- 
-- const BitSigned32      = Union{BitSigned32_types...}
-- const BitUnsigned32    = Union{BitUnsigned32_types...}
-- const BitInteger32     = Union{BitInteger32_types...}
-- 
-- const BitSigned64      = Union{BitSigned64_types...}
-- const BitUnsigned64    = Union{BitUnsigned64_types...}
-- const BitInteger64     = Union{BitInteger64_types...}
-- 
-- const BitSigned        = Union{BitSigned_types...}
-- const BitUnsigned      = Union{BitUnsigned_types...}
-- const BitInteger       = Union{BitInteger_types...}
-- /Source
inductive DecimalUnsigned where
  | small (value : DecimalUnsigned64)
  | u128 (value : JInt .u128)

/-- Exact concrete native BitSigned union. 
Source reference: base/int.jl:10,14,18,34. -/
-- Source: base/int.jl:10-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSigned32_types      = (Int8, Int16, Int32)
-- const BitUnsigned32_types    = (UInt8, UInt16, UInt32)
-- const BitInteger32_types     = (BitSigned32_types..., BitUnsigned32_types...)
-- 
-- const BitSigned64_types      = (BitSigned32_types..., Int64)
-- const BitUnsigned64_types    = (BitUnsigned32_types..., UInt64)
-- const BitInteger64_types     = (BitSigned64_types..., BitUnsigned64_types...)
-- 
-- const BitSigned_types        = (BitSigned64_types..., Int128)
-- const BitUnsigned_types      = (BitUnsigned64_types..., UInt128)
-- const BitInteger_types       = (BitSigned_types..., BitUnsigned_types...)
-- 
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- 
-- const BitSigned32      = Union{BitSigned32_types...}
-- const BitUnsigned32    = Union{BitUnsigned32_types...}
-- const BitInteger32     = Union{BitInteger32_types...}
-- 
-- const BitSigned64      = Union{BitSigned64_types...}
-- const BitUnsigned64    = Union{BitUnsigned64_types...}
-- const BitInteger64     = Union{BitInteger64_types...}
-- 
-- const BitSigned        = Union{BitSigned_types...}
-- const BitUnsigned      = Union{BitUnsigned_types...}
-- const BitInteger       = Union{BitInteger_types...}
-- /Source
inductive DecimalSigned where
  | i8 (value : JInt .i8)
  | i16 (value : JInt .i16)
  | i32 (value : JInt .i32)
  | i64 (value : JInt .i64)
  | i128 (value : JInt .i128)

/-- Close bit_ndigits0z dispatch for every concrete unsigned type.
Source reference: base/intfuncs.jl:740. -/
-- Source: base/intfuncs.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ndigits0z(x::BitUnsigned) = bit_ndigits0z(x)
-- /Source
def decimalUnsigned {W : Type} : DecimalUnsigned →
    JuliaLean.base.io.M (DecimalWorld W) JInt64
  | .small value => bitDigits64 value
  | .u128 value => bitDigits128 value

/-- Complete BitSigned forwarding method. Installed wrapping abs followed
by unsigned preserves the correct magnitude even for signed minimum.
All concrete target calls use the complete unsigned decimal bodies above.
Source reference: base/intfuncs.jl:739. -/
-- Source: base/intfuncs.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ndigits0z(x::BitSigned) = bit_ndigits0z(unsigned(abs(x)))
-- /Source
def decimalSigned {W : Type} : DecimalSigned →
    JuliaLean.base.io.M (DecimalWorld W) JInt64
  | .i8 value => decimalUnsigned (.small (.u8
      (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs value))))
  | .i16 value => decimalUnsigned (.small (.u16
      (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs value))))
  | .i32 value => decimalUnsigned (.small (.u32
      (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs value))))
  | .i64 value => decimalUnsigned (.small (.u64
      (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs value))))
  | .i128 value => decimalUnsigned (.u128
      (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs value)))

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16
open JuliaLean

/-- Dynamic values retain native widths and the exact Bool/Unsigned/other
runtime partition. Other covers every remaining intermediate/reference, not
only Integer results. Julia source: base/intfuncs.jl:748,770. -/
-- Source: base/intfuncs.jl:746-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0znb(x::Integer, b::Integer)
--     d = 0
--     if x isa Unsigned
--         d += (x != 0)::Bool
--         x = -signed(fld(x, -b))
--     end
--     # precondition: b < -1 && !(typeof(x) <: Unsigned)
--     while x != 0
--         x = cld(x,b)
--         d += 1
--     end
--     return d
-- end
-- /Source
inductive DigitValue (Other : Type) where
  | native (type : IntTy) (value : JInt type)
  | boolean (value : Bool)
  | customUnsigned (value : Other)
  | other (value : Other)

/-- Exact Unsigned runtime test, including user Unsigned subtypes.
Source reference: base/intfuncs.jl:748,771. -/
-- Source: base/intfuncs.jl:746-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0znb(x::Integer, b::Integer)
--     d = 0
--     if x isa Unsigned
--         d += (x != 0)::Bool
--         x = -signed(fld(x, -b))
--     end
--     # precondition: b < -1 && !(typeof(x) <: Unsigned)
--     while x != 0
--         x = cld(x,b)
--         d += 1
--     end
--     return d
-- end
-- /Source
def digitIsUnsigned {C : Type} : DigitValue C → Bool
  | .native type _ => !type.signed
  | .customUnsigned _ => true
  | _ => false

/-- Actual Unsigned type assertion at the existing exception-class boundary.
Source reference: base/intfuncs.jl:771. -/
-- Source: base/intfuncs.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         x = unsigned(x)::Unsigned
-- /Source
def digitAssertUnsigned {W C : Type} (value : DigitValue C) :
    JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) :=
  if digitIsUnsigned value then pure value else throw (.foreignError "TypeError" "")

/-- Native unsigned conversion is closed through the installed Base model
for every BitInteger width. Julia source: base/intfuncs.jl:771. -/
-- Source: base/intfuncs.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         x = unsigned(x)::Unsigned
-- /Source
def digitUnsignedOfBits {t : IntTy} (value : JInt t) : DecimalUnsigned :=
  match t, value with
  | .i8, value | .u8, value => .small (.u8 (JuliaLean.base.int.unsigned value))
  | .i16, value | .u16, value => .small (.u16 (JuliaLean.base.int.unsigned value))
  | .i32, value | .u32, value => .small (.u32 (JuliaLean.base.int.unsigned value))
  | .i64, value | .u64, value => .small (.u64 (JuliaLean.base.int.unsigned value))
  | .i128, value | .u128, value => .u128 (JuliaLean.base.int.unsigned value)

/-- Embed a concrete native unsigned value without changing its width.
Source reference: base/intfuncs.jl:771. -/
-- Source: base/intfuncs.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         x = unsigned(x)::Unsigned
-- /Source
def digitUnsignedValue {C : Type} : DecimalUnsigned → DigitValue C
  | .small (.u8 x) => .native .u8 x
  | .small (.u16 x) => .native .u16 x
  | .small (.u32 x) => .native .u32 x
  | .small (.u64 x) => .native .u64 x
  | .u128 x => .native .u128 x

/-- Apply installed concrete native bit operations on the exact unsigned
union. Julia source: base/intfuncs.jl:772-777. -/
-- Source: base/intfuncs.jl:772-777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         b == 2  && return top_set_bit(x)
--         b == 8  && return (top_set_bit(x) + 2) ÷ 3
--         b == 16 && return sizeof(x)<<1 - leading_zeros(x)>>2
--         b == 10 && return bit_ndigits0z(x)
--         if ispow2(b)
--             dv, rm = divrem(top_set_bit(x), trailing_zeros(b))
-- /Source
def digitUnsignedNative {A : Type} (f : {t : IntTy} → JInt t → A) : DecimalUnsigned → A
  | .small (.u8 x) => f x
  | .small (.u16 x) => f x
  | .small (.u32 x) => f x
  | .small (.u64 x) => f x
  | .u128 x => f x

/-- Negative-base selected leaves. notEqual includes its adjacent explicit
Bool assertion or conditional validation. All dynamic results and effects
are retained, including type-changing floor division/signed/negation.
Source reference: base/intfuncs.jl:746-758. -/
-- Source: base/intfuncs.jl:746-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0znb(x::Integer, b::Integer)
--     d = 0
--     if x isa Unsigned
--         d += (x != 0)::Bool
--         x = -signed(fld(x, -b))
--     end
--     # precondition: b < -1 && !(typeof(x) <: Unsigned)
--     while x != 0
--         x = cld(x,b)
--         d += 1
--     end
--     return d
-- end
-- /Source
structure DigitNegativeOps (W C : Type) where
  notEqual : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) Bool
  negBase : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  floorDiv : DigitValue C → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  signed : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  neg : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  ceilDiv : DigitValue C → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)

/-- Complete negative-base body with a real source while loop. The first
(x != 0)::Bool executes before -b/fld/signed/neg. d remains native Int64
with installed wrapping increments; no magnitude/fuel bound is imposed.
Source reference: base/intfuncs.jl:746-758. -/
-- Source: base/intfuncs.jl:746-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0znb(x::Integer, b::Integer)
--     d = 0
--     if x isa Unsigned
--         d += (x != 0)::Bool
--         x = -signed(fld(x, -b))
--     end
--     # precondition: b < -1 && !(typeof(x) <: Unsigned)
--     while x != 0
--         x = cld(x,b)
--         d += 1
--     end
--     return d
-- end
-- /Source
def digitsNegative {W C : Type} (ops : DigitNegativeOps W C) (x b : DigitValue C) :
    JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) := do
  let d := JuliaLean.base.int.lit .i64 0
  let (x, d) ← if digitIsUnsigned x then do
      let nonzero ← ops.notEqual x (JuliaLean.base.int.lit .i64 0)
      let d := JuliaLean.base.int.add d (JuliaLean.base.int.ofBool .i64 nonzero)
      let negativeBase ← ops.negBase b
      let quotient ← ops.floorDiv x negativeBase
      let signed ← ops.signed quotient
      let negative ← ops.neg signed
      pure (negative, d)
    else pure (x, d)
  let count ← JuliaLean.base.io.whileLoop (fun (state : DigitValue C × JInt64) => do
    if ← ops.notEqual state.1 (JuliaLean.base.int.lit .i64 0) then
      let next ← ops.ceilDiv state.1 b
      let count := JuliaLean.base.int.add state.2 (JuliaLean.base.int.lit .i64 1)
      pure (.inr (next, count))
    else pure (.inl state.2)) (x, d)
  pure (.native .i64 count)

/-- Positive-base operations on unfixed runtime types. Int construction may
return a non-Int value, and multiplication/division may change types. Every
condition includes Bool validation. divrem may return an arbitrary iterable:
the two indexed_iterate boundaries retain required extraction and errors.
Source reference: base/intfuncs.jl:764-796. -/
-- Source: base/intfuncs.jl:764-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0zpb(x::Integer, b::Integer)
--     @constprop :aggressive
--     # precondition: b > 1
--     x == 0 && return 0
--     b = Int(b)
--     x = abs(x)
--     if x isa Base.BitInteger
--         x = unsigned(x)::Unsigned
--         b == 2  && return top_set_bit(x)
--         b == 8  && return (top_set_bit(x) + 2) ÷ 3
--         b == 16 && return sizeof(x)<<1 - leading_zeros(x)>>2
--         b == 10 && return bit_ndigits0z(x)
--         if ispow2(b)
--             dv, rm = divrem(top_set_bit(x), trailing_zeros(b))
--             return iszero(rm) ? dv : dv + 1
--         end
--     end
-- 
--     d = 0
--     while x > typemax(Int)
--         x = div(x,b)
--         d += 1
--     end
--     x = div(x,b)
--     d += 1
-- 
--     m = 1
--     while m <= x
--         m *= b
--         d += 1
--     end
--     return d
-- end
-- /Source
structure DigitPositiveOps (W C Pair State : Type) where
  initialZero : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) Bool
  toInt : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  abs : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  baseEqual : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) Bool
  ispow2 : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) Bool
  trailingZeros : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  divrem : JInt64 → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) Pair
  indexedFirst : Pair → JInt64 → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C × State)
  indexedSecond : Pair → JInt64 → State → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  iszero : DigitValue C → JuliaLean.base.io.M (DecimalWorld W) Bool
  addOne : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  greaterMax : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) Bool
  divide : DigitValue C → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)
  lessEqual : DigitValue C → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) Bool
  multiply : DigitValue C → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C)

/-- Complete positive-base method, including early zero, dynamic Int(b),
native unsigned assertion and closed bit/decimal branches. The decimal
branch reads the live global table through the actual decimalUnsigned body.
Both loops are real while loops, d is always native Int, and m starts at
native 1 but may change its runtime type after multiplication.
Source reference: base/intfuncs.jl:764-796. -/
-- Source: base/intfuncs.jl:764-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0zpb(x::Integer, b::Integer)
--     @constprop :aggressive
--     # precondition: b > 1
--     x == 0 && return 0
--     b = Int(b)
--     x = abs(x)
--     if x isa Base.BitInteger
--         x = unsigned(x)::Unsigned
--         b == 2  && return top_set_bit(x)
--         b == 8  && return (top_set_bit(x) + 2) ÷ 3
--         b == 16 && return sizeof(x)<<1 - leading_zeros(x)>>2
--         b == 10 && return bit_ndigits0z(x)
--         if ispow2(b)
--             dv, rm = divrem(top_set_bit(x), trailing_zeros(b))
--             return iszero(rm) ? dv : dv + 1
--         end
--     end
-- 
--     d = 0
--     while x > typemax(Int)
--         x = div(x,b)
--         d += 1
--     end
--     x = div(x,b)
--     d += 1
-- 
--     m = 1
--     while m <= x
--         m *= b
--         d += 1
--     end
--     return d
-- end
-- /Source
def digitsPositive {W C Pair State : Type} (ops : DigitPositiveOps W C Pair State)
    (input base : DigitValue C) : JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) := do
  if ← ops.initialZero input (JuliaLean.base.int.lit .i64 0) then
    return .native .i64 (JuliaLean.base.int.lit .i64 0)
  let b ← ops.toInt base
  let x ← ops.abs input
  let (x, native) ← match x with
    | .native _ value => do
        let native := digitUnsignedOfBits value
        let asserted ← digitAssertUnsigned (digitUnsignedValue native)
        pure (asserted, some native)
    | other => pure (other, none)
  if let some native := native then
    if ← ops.baseEqual b (JuliaLean.base.int.lit .i64 2) then
      return .native .i64 (digitUnsignedNative JuliaLean.base.int.top_set_bit native)
    if ← ops.baseEqual b (JuliaLean.base.int.lit .i64 8) then
      let top := digitUnsignedNative JuliaLean.base.int.top_set_bit native
      let count ← JuliaLean.base.io.liftJl (JuliaLean.base.int.divSame
        (JuliaLean.base.int.add top (JuliaLean.base.int.lit .i64 2)) (JuliaLean.base.int.lit .i64 3))
      return .native .i64 count
    if ← ops.baseEqual b (JuliaLean.base.int.lit .i64 16) then
      let size := digitUnsignedNative JuliaLean.base.int.sizeof native
      let zeros := digitUnsignedNative JuliaLean.base.int.leading_zeros native
      let count := JuliaLean.base.int.sub
        (JuliaLean.base.int.shl_Int size (JuliaLean.base.int.lit .i64 1))
        (JuliaLean.base.int.shr_Int zeros (JuliaLean.base.int.lit .i64 2))
      return .native .i64 count
    if ← ops.baseEqual b (JuliaLean.base.int.lit .i64 10) then
      return .native .i64 (← decimalUnsigned native)
    if ← ops.ispow2 b then
      let top := digitUnsignedNative JuliaLean.base.int.top_set_bit native
      let zeros ← ops.trailingZeros b
      let pair ← ops.divrem top zeros
      let (quotient, state) ← ops.indexedFirst pair (JuliaLean.base.int.lit .i64 1)
      let remainder ← ops.indexedSecond pair (JuliaLean.base.int.lit .i64 2) state
      if ← ops.iszero remainder then return quotient
      else return ← ops.addOne quotient (JuliaLean.base.int.lit .i64 1)
  let (x, d) ← JuliaLean.base.io.whileLoop (fun (state : DigitValue C × JInt64) => do
    if ← ops.greaterMax state.1 (JuliaLean.base.int.typemax .i64) then
      let next ← ops.divide state.1 b
      let count := JuliaLean.base.int.add state.2 (JuliaLean.base.int.lit .i64 1)
      pure (.inr (next, count))
    else pure (.inl state)) (x, JuliaLean.base.int.lit .i64 0)
  let x ← ops.divide x b
  let d := JuliaLean.base.int.add d (JuliaLean.base.int.lit .i64 1)
  let count ← JuliaLean.base.io.whileLoop (fun (state : DigitValue C × JInt64) => do
    if ← ops.lessEqual state.1 x then
      let next ← ops.multiply state.1 b
      let count := JuliaLean.base.int.add state.2 (JuliaLean.base.int.lit .i64 1)
      pure (.inr (next, count))
    else pure (.inl state.2)) (.native .i64 (JuliaLean.base.int.lit .i64 1), d)
  pure (.native .i64 count)

/-- Actual dispatch outside the normal generic/Bool Base family remains
open. The default route invokes the real bodies below, never a callback for
the method being implemented. Julia source: base/intfuncs.jl:741,829-838. -/
-- Source: base/intfuncs.jl:829-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0z(x::Integer, b::Integer)
--     @constprop :aggressive
--     if b < -1
--         ndigits0znb(x, b)
--     elseif b > 1
--         ndigits0zpb(x, b)
--     else
--         throw(DomainError(b, "The base must not be in `[-1, 0, 1]`."))
--     end
-- end
-- /Source
inductive DigitMethodRoute (W C : Type) where
  | base
  | custom (callee : DigitValue C → DigitValue C → JuliaLean.base.io.M (DecimalWorld W) (DigitValue C))

/-- Complete negative/positive dispatch family plus the two outer tests.
A genuinely selected specialization can depend on either dynamic input.
Source reference: base/intfuncs.jl:741,829-838. -/
-- Source: base/intfuncs.jl:829-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0z(x::Integer, b::Integer)
--     @constprop :aggressive
--     if b < -1
--         ndigits0znb(x, b)
--     elseif b > 1
--         ndigits0zpb(x, b)
--     else
--         throw(DomainError(b, "The base must not be in `[-1, 0, 1]`."))
--     end
-- end
-- /Source
structure DigitDispatchOps (W C Pair State : Type) where
  negative : DigitNegativeOps W C
  positive : DigitPositiveOps W C Pair State
  selectNegative : DigitValue C → DigitValue C → DigitMethodRoute W C
  selectPositive : DigitValue C → DigitValue C → DigitMethodRoute W C
  lessBase : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) Bool
  greaterBase : DigitValue C → JInt64 → JuliaLean.base.io.M (DecimalWorld W) Bool

/-- Selected negative method: the normal Bool case reuses its faithful
installed model, and the normal generic case runs the full source body.
Source reference: base/intfuncs.jl:832. -/
-- Source: base/intfuncs.jl:832-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ndigits0znb(x, b)
-- /Source
def digitsNegativeSelected {W C Pair State : Type} (ops : DigitDispatchOps W C Pair State)
    (x b : DigitValue C) : JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) :=
  match ops.selectNegative x b with
  | .custom callee => callee x b
  | .base => match x with
    | .boolean value => pure (.native .i64 (JuliaLean.base.intfuncs.ndigitsNegative_Bool value b))
    | _ => digitsNegative ops.negative x b

/-- Selected positive method: the normal Bool case reuses its faithful
installed model, and the normal generic case runs the full source body.
Source reference: base/intfuncs.jl:834. -/
-- Source: base/intfuncs.jl:834-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ndigits0zpb(x, b)
-- /Source
def digitsPositiveSelected {W C Pair State : Type} (ops : DigitDispatchOps W C Pair State)
    (x b : DigitValue C) : JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) :=
  match ops.selectPositive x b with
  | .custom callee => callee x b
  | .base => match x with
    | .boolean value => pure (.native .i64 (JuliaLean.base.intfuncs.ndigitsPositive_Bool value b))
    | _ => digitsPositive ops.positive x b

/-- Complete generic decimal wrapper with the fixed native literal ten,
using actual positive-method dispatch and its implemented default body.
Source reference: base/intfuncs.jl:741. -/
-- Source: base/intfuncs.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ndigits0z(x::Integer) = ndigits0zpb(x, 10)
-- /Source
def digitsDecimal {W C Pair State : Type} (ops : DigitDispatchOps W C Pair State)
    (x : DigitValue C) : JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) :=
  digitsPositiveSelected ops x (.native .i64 (JuliaLean.base.int.lit .i64 10))

/-- Complete base selector. Each selected normal branch invokes its actual
new helper body, while true custom specializations retain their effects and
results. The second test is skipped after a negative-base selection.
Source reference: base/intfuncs.jl:829-838. -/
-- Source: base/intfuncs.jl:829-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ndigits0z(x::Integer, b::Integer)
--     @constprop :aggressive
--     if b < -1
--         ndigits0znb(x, b)
--     elseif b > 1
--         ndigits0zpb(x, b)
--     else
--         throw(DomainError(b, "The base must not be in `[-1, 0, 1]`."))
--     end
-- end
-- /Source
def digitsZero {W C Pair State : Type} (ops : DigitDispatchOps W C Pair State)
    (x b : DigitValue C) : JuliaLean.base.io.M (DecimalWorld W) (DigitValue C) := do
  if ← ops.lessBase b (JuliaLean.base.int.lit .i64 (-1)) then
    digitsNegativeSelected ops x b
  else if ← ops.greaterBase b (JuliaLean.base.int.lit .i64 1) then
    digitsPositiveSelected ops x b
  else throw (.jl (.domainError "The base must not be in `[-1, 0, 1]`."))

/-- Generic top-bit operations. iszero includes conditional Bool validation;
exponent and addition retain arbitrary changing types/results and effects.
Source reference: base/intfuncs.jl:842. -/
-- Source: base/intfuncs.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- top_set_bit(x::Integer) = iszero(x) ? 0 : exponent(x) + 1
-- /Source
structure DigitTopBitOps (W C : Type) where
  iszero : DigitValue C → JuliaLean.base.io.M W Bool
  exponent : DigitValue C → JuliaLean.base.io.M W (DigitValue C)
  add : DigitValue C → JInt64 → JuliaLean.base.io.M W (DigitValue C)

/-- Complete generic top_set_bit method with its native zero/one literals,
conditional short circuit and dynamic exponent-plus-one call.
Source reference: base/intfuncs.jl:842. -/
-- Source: base/intfuncs.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- top_set_bit(x::Integer) = iszero(x) ? 0 : exponent(x) + 1
-- /Source
def digitTopSetBit {W C : Type} (ops : DigitTopBitOps W C) (x : DigitValue C) :
    JuliaLean.base.io.M W (DigitValue C) := do
  if ← ops.iszero x then pure (.native .i64 (JuliaLean.base.int.lit .i64 0))
  else
    let exponent ← ops.exponent x
    ops.add exponent (JuliaLean.base.int.lit .i64 1)

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- A runtime String identity and the address returned by jl_string_ptr.
Its bytes reside in the shared ByteHeap, so the handle is not a frozen copy
of the bytes under construction. Julia source: base/essentials.jl:745 and
base/strings/string.jl:184-185,206. -/
-- Source: base/essentials.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
-- /Source
structure FormattingString where
  identity : Nat
  data : JuliaLean.base.pointer.Ptr (JInt .u8)

/-- A custom _string_n need not return String, and a custom pointer need not
return Ptr{UInt8}. Known tags close concrete Base behavior; other tags retain
actual selected dispatch. Julia source use: base/intfuncs.jl:881-883,908-910. -/
-- Source: base/intfuncs.jl:881-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
-- /Source
inductive FormattingStringValue (V : Type) where
  | string (value : FormattingString)
  | other (value : V)

/-- Tagged pointer results retain the fixed concrete Ptr{UInt8} case and
arbitrary values returned by custom pointer dispatch.
Source reference: base/intfuncs.jl:881-883. -/
-- Source: base/intfuncs.jl:881-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
-- /Source
inductive FormattingPointer (V : Type) where
  | bytePointer (value : JuliaLean.base.pointer.Ptr (JInt .u8))
  | other (value : V)

/-- Known Integer allocation, actually selected custom allocation, and
missing-method routes for the source _string_n call.
Source reference: base/strings/string.jl:184-185. -/
-- Source: base/strings/string.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @eval _string_n(n::Integer) = $(Expr(:foreigncall, QuoteNode(:jl_alloc_string), Ref{String},
--     :(Core.svec(Csize_t)), 1, QuoteNode((:ccall, _string_n_override, false)), :(convert(Csize_t, n))))
-- /Source
inductive FormattingStringRoute where
  | integer
  | custom
  | noMethod

/-- Dynamic index dispatch at a known Ptr{UInt8}; an unknown index can
select a custom method or no method before the ordinary Integer conversion. 
Source reference: base/pointer.jl:178. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
inductive FormattingStoreRoute where
  | integer
  | custom
  | noMethod

/-- The caller world and shared byte heap retain string allocation and
pointer-store effects. Julia dependency: base/pointer.jl:178. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
abbrev FormattingWorld (W : Type) := W × JuliaLean.base.pointer.ByteHeap

/-- Actual byte layout at a Ptr{UInt8}, using the installed pointer model.
Dependency: base/pointer.jl:178 and the byte-sized pointerset primitive. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
def formattingByteCodec : JuliaLean.base.pointer.ByteCodec (JInt .u8) where
  elementSize := JuliaLean.base.int.lit .i64 1
  size_nonnegative := by decide
  encode := fun value => [value]
  decode := fun bytes => bytes.headD (JuliaLean.base.int.lit .u8 0)
  encode_length := fun _ => rfl
  decode_encode := fun _ => rfl

/-- The numeric source only fixes x as abstract Unsigned. Top-bit, max,
addition and subsequent counters can consequently change runtime types.
V is a tagged runtime carrier, not an unbounded mathematical integer.
Native literals keep their actual types. Bool-valued fields include the
adjacent conditional assertion, and lowByte returns a tagged UInt8 assertion
candidate. No callback replaces either formatting loop.

allocateString is precisely the jl_alloc_string foreign-call boundary;
its failures and heap allocation effects are observable. toCsize includes
the foreign argument's UInt conversion/validation. Other operations are
selected on types not fixed by the source. Julia source: base/intfuncs.jl:878-920. -/
-- Source: base/intfuncs.jl:878-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bin(x::Unsigned, pad::Int, neg::Bool)
--     m = top_set_bit(x)
--     n = neg + max(pad, m)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i >= 4
--             b = UInt32((x % UInt8)::UInt8)
--             d = 0x30303030 +% ((b *% 0x08040201) >> 0x3) & 0x01010101
--             unsafe_store!(p, (d >> 0x00) % UInt8, i-3)
--             unsafe_store!(p, (d >> 0x08) % UInt8, i-2)
--             unsafe_store!(p, (d >> 0x10) % UInt8, i-1)
--             unsafe_store!(p, (d >> 0x18) % UInt8, i)
--             x >>= 0x4
--             i -= 4
--         end
--         while i > neg
--             unsafe_store!(p, 0x30 + ((x % UInt8)::UInt8 & 0x1), i)
--             x >>= 0x1
--             i -= 1
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
--     end
--     return str
-- end
-- 
-- function oct(x::Unsigned, pad::Int, neg::Bool)
--     m = div(top_set_bit(x) + 2, 3)
--     n = neg + max(pad, m)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i > neg
--             unsafe_store!(p, 0x30 + ((x % UInt8)::UInt8 & 0x7), i)
--             x >>= 0x3
--             i -= 1
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
--     end
--     return str
-- end
-- /Source
structure FormattingOps (W V : Type) where
  topBit : V → JuliaLean.base.io.M (FormattingWorld W) V
  maxPad : JInt64 → V → JuliaLean.base.io.M (FormattingWorld W) V
  addBool : Bool → V → JuliaLean.base.io.M (FormattingWorld W) V
  addNative : V → JInt64 → JuliaLean.base.io.M (FormattingWorld W) V
  divNative : V → JInt64 → JuliaLean.base.io.M (FormattingWorld W) V
  stringRoute : V → FormattingStringRoute
  toCsize : V → JuliaLean.base.io.M (FormattingWorld W) (JInt .u64)
  allocateString : JInt .u64 → JuliaLean.base.io.M (FormattingWorld W) FormattingString
  customString : V → JuliaLean.base.io.M (FormattingWorld W) (FormattingStringValue V)
  pointerOther : V → JuliaLean.base.io.M (FormattingWorld W) (FormattingPointer V)
  greaterEqual : V → JInt64 → JuliaLean.base.io.M (FormattingWorld W) Bool
  greaterBool : V → Bool → JuliaLean.base.io.M (FormattingWorld W) Bool
  lowByte : V → JuliaLean.base.io.M (FormattingWorld W) (Sum (JInt .u8) V)
  shiftRight : V → JInt .u8 → JuliaLean.base.io.M (FormattingWorld W) V
  subNative : V → JInt64 → JuliaLean.base.io.M (FormattingWorld W) V
  toNativeIndex : V → JuliaLean.base.io.M (FormattingWorld W) JInt64
  storeByteRoute : V → FormattingStoreRoute
  customByteStore : JuliaLean.base.pointer.Ptr (JInt .u8) → JInt .u8 → V →
    JuliaLean.base.io.M (FormattingWorld W) Unit
  storeOther : V → JInt .u8 → Sum JInt64 V → JuliaLean.base.io.M (FormattingWorld W) Unit

/-- _string_n call dispatch closes the installed Integer method rather than
parameterizing that known body. The foreign allocator itself is an explicit
runtime boundary. Julia source: base/strings/string.jl:184-185. -/
-- Source: base/strings/string.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @eval _string_n(n::Integer) = $(Expr(:foreigncall, QuoteNode(:jl_alloc_string), Ref{String},
--     :(Core.svec(Csize_t)), 1, QuoteNode((:ccall, _string_n_override, false)), :(convert(Csize_t, n))))
-- /Source
def formattingStringN {W V : Type} (ops : FormattingOps W V) (n : V) :
    JuliaLean.base.io.M (FormattingWorld W) (FormattingStringValue V) := do
  match ops.stringRoute n with
  | .integer =>
      let str ← JuliaLean.base.strings.string.stringN ops.toCsize ops.allocateString n
      pure (.string str)
  | .custom => ops.customString n
  | .noMethod => throw (.jl (.methodError "_string_n"))

/-- Heap-identity adapter for the concrete pointer(::String) method. The
jl_string_ptr primitive is the stored data-address projection, keeping the
same object and address through its GC.@preserve lexical lifetime. That
macro introduces compiler rooting, not a dispatched runtime body. The
installed pointerString's value-only JStr representation cannot carry a
string being mutated, hence this necessary handle adapter.
Julia dependencies: base/strings/string.jl:206; base/essentials.jl:745. -/
-- Source: base/strings/string.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pointer(s::String) = unsafe_convert(Ptr{UInt8}, s)
-- /Source
def formattingKnownPointer (value : FormattingString) : JuliaLean.base.pointer.Ptr (JInt .u8) :=
  value.data

/-- Concrete String-pointer wrapper and genuinely selected custom route.
Source reference: base/strings/string.jl:206. -/
-- Source: base/strings/string.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pointer(s::String) = unsafe_convert(Ptr{UInt8}, s)
-- /Source
def formattingPointer {W V : Type} (ops : FormattingOps W V) :
    FormattingStringValue V → JuliaLean.base.io.M (FormattingWorld W) (FormattingPointer V)
  | .string value => pure (.bytePointer (formattingKnownPointer value))
  | .other value => ops.pointerOther value

/-- UInt8 type assertion at the actual source point; custom remainder
results with any other type produce TypeError, never truncation/defaulting.
Source reference: base/intfuncs.jl:886,896,913. -/
-- Source: base/intfuncs.jl:886-886 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             b = UInt32((x % UInt8)::UInt8)
-- /Source
def formattingLowByte {W V : Type} (ops : FormattingOps W V) (x : V) :
    JuliaLean.base.io.M (FormattingWorld W) (JInt .u8) := do
  match ← ops.lowByte x with
  | .inl byte => pure byte
  | .inr _ => throw (.foreignError "TypeError" "typeassert UInt8")

/-- Effectful concrete unsafe_store!(::Ptr{UInt8},::UInt8,index): perform
convert(UInt8,x), then Int(index), then the installed pointerSet at its exact
wrapped native address. A custom pointer uses only its genuinely selected
method. The heap is shared with every custom operation, so earlier writes
and aliases remain visible. Invalid raw pointer stores have the installed
pointer primitive's unchecked memory semantics; no BoundsError is invented.
Julia dependency: base/pointer.jl:178. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
def formattingNativeWrite {W : Type} (pointer : JuliaLean.base.pointer.Ptr (JInt .u8))
    (byte : JInt .u8) (index : JInt64) : JuliaLean.base.io.M (FormattingWorld W) Unit := do
  let (world, heap) ← JuliaLean.base.io.getWorld
  let (heap, _) := JuliaLean.base.pointer.pointerSet formattingByteCodec heap pointer byte index
    (JuliaLean.base.int.lit .i64 1)
  JuliaLean.base.io.setWorld (world, heap)

/-- Concrete native unsafe_store! path, usable by other queued callers
without any unused custom-dispatch record. Julia source: base/pointer.jl:178. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
def formattingStoreNative {W : Type} (pointer : JuliaLean.base.pointer.Ptr (JInt .u8))
    (byte : JInt .u8) (index : JInt64) : JuliaLean.base.io.M (FormattingWorld W) Unit := do
  let byte ← JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .u8 byte)
  let index ← JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 index)
  formattingNativeWrite pointer byte index

/-- Complete pointer/index selection with explicit selected custom methods;
known native stores use the concrete helper and dynamic Integer indices
retain conversion before pointerset. Julia source: base/pointer.jl:178. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
def formattingStore {W V : Type} (ops : FormattingOps W V) (p : FormattingPointer V)
    (byte : JInt .u8) (index : Sum JInt64 V) : JuliaLean.base.io.M (FormattingWorld W) Unit := do
  match p with
  | .other pointer => ops.storeOther pointer byte index
  | .bytePointer pointer =>
      match index with
      | .inl index => formattingStoreNative pointer byte index
      | .inr index =>
          match ops.storeByteRoute index with
          | .custom => ops.customByteStore pointer byte index
          | .noMethod => throw (.jl (.methodError "unsafe_store!"))
          | .integer =>
              let byte ← JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .u8 byte)
              let index ← ops.toNativeIndex index
              formattingNativeWrite pointer byte index

/-- Four binary digits from the low nibble, through the actual installed
UInt32 wrapping and bitwise operations. Julia source: base/intfuncs.jl:887. -/
-- Source: base/intfuncs.jl:887-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             d = 0x30303030 +% ((b *% 0x08040201) >> 0x3) & 0x01010101
-- /Source
def formattingBinaryPacked (b : JInt .u32) : JInt .u32 :=
  JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .u32 0x30303030)
    (JuliaLean.base.int.band
      (JuliaLean.base.int.shr_BitUnsigned_BitUnsigned
        (JuliaLean.base.int.mulWrap b (JuliaLean.base.int.lit .u32 0x08040201))
        (JuliaLean.base.int.lit .u8 3))
      (JuliaLean.base.int.lit .u32 0x01010101))

/-- Full bin body with both actual unbounded loops, arbitrary custom counter
and input types, native byte arithmetic, effectful conversions and raw heap
stores. All successful return paths retain the original allocated/custom
string handle. Julia source: base/intfuncs.jl:878-903. -/
-- Source: base/intfuncs.jl:878-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bin(x::Unsigned, pad::Int, neg::Bool)
--     m = top_set_bit(x)
--     n = neg + max(pad, m)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i >= 4
--             b = UInt32((x % UInt8)::UInt8)
--             d = 0x30303030 +% ((b *% 0x08040201) >> 0x3) & 0x01010101
--             unsafe_store!(p, (d >> 0x00) % UInt8, i-3)
--             unsafe_store!(p, (d >> 0x08) % UInt8, i-2)
--             unsafe_store!(p, (d >> 0x10) % UInt8, i-1)
--             unsafe_store!(p, (d >> 0x18) % UInt8, i)
--             x >>= 0x4
--             i -= 4
--         end
--         while i > neg
--             unsafe_store!(p, 0x30 + ((x % UInt8)::UInt8 & 0x1), i)
--             x >>= 0x1
--             i -= 1
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
--     end
--     return str
-- end
-- /Source
def binUnsigned {W V : Type} (ops : FormattingOps W V)
    (x : V) (pad : JInt64) (neg : Bool) :
    JuliaLean.base.io.M (FormattingWorld W) (FormattingStringValue V) := do
  let m ← ops.topBit x
  let width ← ops.maxPad pad m
  let n ← ops.addBool neg width
  let str ← formattingStringN ops n
  let p ← formattingPointer ops str
  let (x, i) ← JuliaLean.base.io.whileLoop (fun (x, i) => do
    if ← ops.greaterEqual i (JuliaLean.base.int.lit .i64 4) then
      let byte ← formattingLowByte ops x
      let b ← JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .u32 byte)
      let d := formattingBinaryPacked b
      let i3 ← ops.subNative i (JuliaLean.base.int.lit .i64 3)
      formattingStore ops p (JuliaLean.base.int.remT .u8
        (JuliaLean.base.int.shr_BitUnsigned_BitUnsigned d (JuliaLean.base.int.lit .u8 0))) (.inr i3)
      let i2 ← ops.subNative i (JuliaLean.base.int.lit .i64 2)
      formattingStore ops p (JuliaLean.base.int.remT .u8
        (JuliaLean.base.int.shr_BitUnsigned_BitUnsigned d (JuliaLean.base.int.lit .u8 8))) (.inr i2)
      let i1 ← ops.subNative i (JuliaLean.base.int.lit .i64 1)
      formattingStore ops p (JuliaLean.base.int.remT .u8
        (JuliaLean.base.int.shr_BitUnsigned_BitUnsigned d (JuliaLean.base.int.lit .u8 16))) (.inr i1)
      formattingStore ops p (JuliaLean.base.int.remT .u8
        (JuliaLean.base.int.shr_BitUnsigned_BitUnsigned d (JuliaLean.base.int.lit .u8 24))) (.inr i)
      let x ← ops.shiftRight x (JuliaLean.base.int.lit .u8 4)
      let i ← ops.subNative i (JuliaLean.base.int.lit .i64 4)
      pure (.inr (x, i))
    else pure (.inl (x, i))) (x, n)
  let _ ← JuliaLean.base.io.whileLoop (fun (x, i) => do
    if ← ops.greaterBool i neg then
      let byte ← formattingLowByte ops x
      let digit := JuliaLean.base.int.add (JuliaLean.base.int.lit .u8 0x30)
        (JuliaLean.base.int.band byte (JuliaLean.base.int.lit .u8 1))
      formattingStore ops p digit (.inr i)
      let x ← ops.shiftRight x (JuliaLean.base.int.lit .u8 1)
      let i ← ops.subNative i (JuliaLean.base.int.lit .i64 1)
      pure (.inr (x, i))
    else pure (.inl ())) (x, i)
  if neg then
    formattingStore ops p (JuliaLean.base.int.lit .u8 0x2d) (.inl (JuliaLean.base.int.lit .i64 1))
  pure str

/-- Full oct body: top-bit arithmetic and every dynamic dispatch retain
source order, while concrete UInt8 operations and raw pointer stores are
closed. The loop keeps arbitrary type-changing counters and actual effects.
Source reference: base/intfuncs.jl:905-920. -/
-- Source: base/intfuncs.jl:905-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function oct(x::Unsigned, pad::Int, neg::Bool)
--     m = div(top_set_bit(x) + 2, 3)
--     n = neg + max(pad, m)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i > neg
--             unsafe_store!(p, 0x30 + ((x % UInt8)::UInt8 & 0x7), i)
--             x >>= 0x3
--             i -= 1
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
--     end
--     return str
-- end
-- /Source
def octUnsigned {W V : Type} (ops : FormattingOps W V)
    (x : V) (pad : JInt64) (neg : Bool) :
    JuliaLean.base.io.M (FormattingWorld W) (FormattingStringValue V) := do
  let top ← ops.topBit x
  let top ← ops.addNative top (JuliaLean.base.int.lit .i64 2)
  let m ← ops.divNative top (JuliaLean.base.int.lit .i64 3)
  let width ← ops.maxPad pad m
  let n ← ops.addBool neg width
  let str ← formattingStringN ops n
  let p ← formattingPointer ops str
  let _ ← JuliaLean.base.io.whileLoop (fun (x, i) => do
    if ← ops.greaterBool i neg then
      let byte ← formattingLowByte ops x
      let digit := JuliaLean.base.int.add (JuliaLean.base.int.lit .u8 0x30)
        (JuliaLean.base.int.band byte (JuliaLean.base.int.lit .u8 7))
      formattingStore ops p digit (.inr i)
      let x ← ops.shiftRight x (JuliaLean.base.int.lit .u8 3)
      let i ← ops.subNative i (JuliaLean.base.int.lit .i64 1)
      pure (.inr (x, i))
    else pure (.inl ())) (x, n)
  if neg then
    formattingStore ops p (JuliaLean.base.int.lit .u8 0x2d) (.inl (JuliaLean.base.int.lit .i64 1))
  pure str

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Live concrete Vector{UInt16} storage for the const-bound _dec_d100.
All current isbits cells are represented, including arbitrary bits left by
uninitialized storage; they are never replaced by a fixed 100-entry table.
A resized/offset vector retains its underlying memory, so unchecked accesses
can observe other cells in that memory. All sizes are native-representable.
Source reference: base/intfuncs.jl:923-936. -/
-- Source: base/intfuncs.jl:923-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const _dec_d100 = UInt16[
-- # generating expression: UInt16[(0x30 + i % 10) << 0x8 + (0x30 + i ÷ 10) for i = 0:99]
-- #    0 0,    0 1,    0 2,    0 3, and so on in little-endian
--   0x3030, 0x3130, 0x3230, 0x3330, 0x3430, 0x3530, 0x3630, 0x3730, 0x3830, 0x3930,
--   0x3031, 0x3131, 0x3231, 0x3331, 0x3431, 0x3531, 0x3631, 0x3731, 0x3831, 0x3931,
--   0x3032, 0x3132, 0x3232, 0x3332, 0x3432, 0x3532, 0x3632, 0x3732, 0x3832, 0x3932,
--   0x3033, 0x3133, 0x3233, 0x3333, 0x3433, 0x3533, 0x3633, 0x3733, 0x3833, 0x3933,
--   0x3034, 0x3134, 0x3234, 0x3334, 0x3434, 0x3534, 0x3634, 0x3734, 0x3834, 0x3934,
--   0x3035, 0x3135, 0x3235, 0x3335, 0x3435, 0x3535, 0x3635, 0x3735, 0x3835, 0x3935,
--   0x3036, 0x3136, 0x3236, 0x3336, 0x3436, 0x3536, 0x3636, 0x3736, 0x3836, 0x3936,
--   0x3037, 0x3137, 0x3237, 0x3337, 0x3437, 0x3537, 0x3637, 0x3737, 0x3837, 0x3937,
--   0x3038, 0x3138, 0x3238, 0x3338, 0x3438, 0x3538, 0x3638, 0x3738, 0x3838, 0x3938,
--   0x3039, 0x3139, 0x3239, 0x3339, 0x3439, 0x3539, 0x3639, 0x3739, 0x3839, 0x3939
-- ]
-- /Source
structure FormattingPairs where
  cells : List (JInt .u16)
  nativeMemory : cells.length < 2 ^ 63
  offset : Nat
  length : JInt64
  validWindow : 0 ≤ length.val ∧ (offset : Int) + length.val ≤ (cells.length : Int)

/-- The caller world and live decimal-pair table retain table reads and
buffer-store effects. Julia source: base/intfuncs.jl:943-945. -/
-- Source: base/intfuncs.jl:943-945 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         @inbounds d100 = _dec_d100[(c % Int)::Int + 1]
--         @inbounds buf[pos + i - 2] = d100 % UInt8
--         @inbounds buf[pos + i - 1] = (d100 >> 0x8) % UInt8
-- /Source
abbrev FormattingAppendWorld (W : Type) := W × FormattingPairs

/-- Representation embedding into the supplied concrete Array/Memory model.
Integer payloads carry the actual UInt16 bits; no values are manufactured.
The array and all its aliases read the same live cell list.
Julia dependency: base/essentials.jl:1073-1077. -/
-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
def formattingPairsHeap (table : FormattingPairs) : JuliaLean.base.essentials.Heap :=
  [{ slots := table.cells.map (fun x => some (JuliaLean.BootCov.JVal.int x.val)),
     atomic := false, elsize := 2, isunion := false }]

/-- Embed the current table header and window into the supplied concrete
Array representation without copying its cells.
Julia dependency: base/essentials.jl:1073-1077. -/
-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
def formattingPairsArray (table : FormattingPairs) : JuliaLean.base.essentials.Arr :=
  { ref := { mem := { handle := 0 }, index := table.offset }, size := [table.length] }

/-- Preserve every supplied Array/Memory exception class. The distinct
UndefinedBehaviour marker is not a Julia BoundsError or an ordinary value.
Julia dependency: base/essentials.jl:1073-1077 and its memory primitives. -/
-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
def formattingEssentialsError : JuliaLean.base.essentials.Err → JuliaLean.base.io.Error
  | .core (.inexact fn _) => .jl (.inexactError fn)
  | .core (.argument text) => .jl (.argumentError text)
  | .core .bounds => .jl .boundsError
  | .core (.typeError fn) => .foreignError "TypeError" fn
  | .core .typeName => .foreignError "TypeError" "typename"
  | .core (.method fn) => .jl (.methodError fn)
  | .core .undefRef => .foreignError "UndefRefError" ""
  | .core (.error text) => .errorException text
  | .concurrency text => .foreignError "ConcurrencyViolationError" text
  | .undefinedBehaviour text => .foreignError "UndefinedBehaviour" text

/-- Concrete @inbounds Array read through installed getindexArray false,
including its native memory-reference arithmetic and primitive checks.
The table snapshot is obtained only now, after all preceding custom effects.
The checked mutableGet wrapper is deliberately not used for this @inbounds
site. The impossible payload branch protects the representation embedding;
every reachable successful cell comes from an actual typed UInt16 input.
Julia source use: base/intfuncs.jl:943. -/
-- Source: base/intfuncs.jl:943-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         @inbounds d100 = _dec_d100[(c % Int)::Int + 1]
-- /Source
def formattingReadPair {W : Type} (index : JInt64) :
    JuliaLean.base.io.M (FormattingAppendWorld W) (JInt .u16) := fun (world, table) =>
  match (JuliaLean.base.essentials.getindexArray false (formattingPairsArray table) index).run
      (formattingPairsHeap table) with
  | none => none
  | some (.error error) => some (.error (formattingEssentialsError error, (world, table)))
  | some (.ok (.int value, _)) =>
      some (.ok (JuliaLean.base.int.lit .u16 value, (world, table)))
  | some (.ok (_, _)) => some (.error (.foreignError "RepresentationError" "UInt16 cell", (world, table)))

/-- The two indexed_iterate calls are separate operations on the actual
arbitrary divrem result. No Pair-valued correctness assumption truncates
custom iterables, failures or mutable iteration states. buf is unrestricted,
so its selected setindex! under the call-site inbounds context is an
effectful dispatch leaf. indexedFirst/Next include the adjacent lowering
protocol extraction/validation of their result and retain those errors.
Source reference: base/intfuncs.jl:938-980. -/
-- Source: base/intfuncs.jl:962-962 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return @inline append_c_digits(9, digits, buf, pos) # force loop-unrolling on the length
-- /Source
inductive FormattingAppendRoute where
  | base
  | custom
  | noMethod

/-- Selected arithmetic, destructuring, and buffer-store dependencies for
the actual decimal append loops. Intermediate results and iteration states
remain unrestricted. Julia source: base/intfuncs.jl:938-980. -/
-- Source: base/intfuncs.jl:938-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append_c_digits(olength::Int, digits::Unsigned, buf, pos::Int)
--     i = olength
--     while i >= 2
--         d, c = divrem(digits, 0x64)
--         digits = oftype(digits, d)
--         @inbounds d100 = _dec_d100[(c % Int)::Int + 1]
--         @inbounds buf[pos + i - 2] = d100 % UInt8
--         @inbounds buf[pos + i - 1] = (d100 >> 0x8) % UInt8
--         i -= 2
--     end
--     if i == 1
--         @inbounds buf[pos] = UInt8('0') + rem(digits, 0xa) % UInt8
--     end
--     return pos + olength
-- end
-- /Source
structure FormattingAppendOps (W V Iter State Buf Other : Type) where
  divrem100 : V → JInt .u8 → JuliaLean.base.io.M (FormattingAppendWorld W) Iter
  divremChunk : V → JInt .u32 → JuliaLean.base.io.M (FormattingAppendWorld W) Iter
  indexedFirst : Iter → JInt64 → JuliaLean.base.io.M (FormattingAppendWorld W) (V × State)
  indexedNext : Iter → JInt64 → State → JuliaLean.base.io.M (FormattingAppendWorld W) V
  oftype : V → V → JuliaLean.base.io.M (FormattingAppendWorld W) V
  remInt : V → JuliaLean.base.io.M (FormattingAppendWorld W) (Sum JInt64 V)
  remTen : V → JInt .u8 → JuliaLean.base.io.M (FormattingAppendWorld W) V
  remByte : V → JuliaLean.base.io.M (FormattingAppendWorld W) V
  addByte : JInt .u8 → V → JuliaLean.base.io.M (FormattingAppendWorld W) V
  store : Buf → Sum (JInt .u8) V → JInt64 → JuliaLean.base.io.M (FormattingAppendWorld W) Unit
  equalZero : V → JInt64 → JuliaLean.base.io.M (FormattingAppendWorld W) Bool
  greaterUInt : V → JInt .u64 → JuliaLean.base.io.M (FormattingAppendWorld W) Bool
  remUInt32 : V → JuliaLean.base.io.M (FormattingAppendWorld W) V
  remUInt64 : V → JuliaLean.base.io.M (FormattingAppendWorld W) V
  cRoute : V → Buf → FormattingAppendRoute
  customC : JInt64 → V → Buf → JInt64 → JuliaLean.base.io.M (FormattingAppendWorld W) (Sum JInt64 Other)
  nineRoute : V → Buf → FormattingAppendRoute
  customNine : V → Buf → JInt64 → JuliaLean.base.io.M (FormattingAppendWorld W) (Sum JInt64 Other)

/-- Actual two-result destructuring, ignoring extra elements after the
second extraction exactly as Julia does. Julia source: base/intfuncs.jl:941,972. -/
-- Source: base/intfuncs.jl:941-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         d, c = divrem(digits, 0x64)
--         digits = oftype(digits, d)
-- /Source
def formattingDivremPair {W V Iter State Buf Other : Type}
    (ops : FormattingAppendOps W V Iter State Buf Other) (result : Iter) :
    JuliaLean.base.io.M (FormattingAppendWorld W) (V × V) := do
  let (first, state) ← ops.indexedFirst result (JuliaLean.base.int.lit .i64 1)
  let second ← ops.indexedNext result (JuliaLean.base.int.lit .i64 2) state
  pure (first, second)

/-- Full generic append body. olength, pos and i remain native Int and all
position additions/subtractions use installed wrapping arithmetic. Arbitrary
custom division/oftype/iteration/last-digit results and mutable buffer/table
aliasing are retained. Julia source: base/intfuncs.jl:938-952. -/
-- Source: base/intfuncs.jl:938-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append_c_digits(olength::Int, digits::Unsigned, buf, pos::Int)
--     i = olength
--     while i >= 2
--         d, c = divrem(digits, 0x64)
--         digits = oftype(digits, d)
--         @inbounds d100 = _dec_d100[(c % Int)::Int + 1]
--         @inbounds buf[pos + i - 2] = d100 % UInt8
--         @inbounds buf[pos + i - 1] = (d100 >> 0x8) % UInt8
--         i -= 2
--     end
--     if i == 1
--         @inbounds buf[pos] = UInt8('0') + rem(digits, 0xa) % UInt8
--     end
--     return pos + olength
-- end
-- /Source
def appendCDigits {W V Iter State Buf Other : Type}
    (ops : FormattingAppendOps W V Iter State Buf Other)
    (olength : JInt64) (digits : V) (buf : Buf) (pos : JInt64) :
    JuliaLean.base.io.M (FormattingAppendWorld W) JInt64 := do
  let (i, digits) ← JuliaLean.base.io.whileLoop (fun (i, digits) => do
    if JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 2) i then
      let pair ← ops.divrem100 digits (JuliaLean.base.int.lit .u8 0x64)
      let (d, c) ← formattingDivremPair ops pair
      let digits ← ops.oftype digits d
      let c ← ops.remInt c
      let c ← match c with
        | .inl c => pure c
        | .inr _ => throw (.foreignError "TypeError" "typeassert Int")
      let index := JuliaLean.base.int.add c (JuliaLean.base.int.lit .i64 1)
      let d100 ← formattingReadPair index
      let low := JuliaLean.base.int.remT .u8 d100
      let left := JuliaLean.base.int.sub (JuliaLean.base.int.add pos i) (JuliaLean.base.int.lit .i64 2)
      ops.store buf (.inl low) left
      let high := JuliaLean.base.int.remT .u8
        (JuliaLean.base.int.shr_BitUnsigned_BitUnsigned d100 (JuliaLean.base.int.lit .u8 8))
      let right := JuliaLean.base.int.sub (JuliaLean.base.int.add pos i) (JuliaLean.base.int.lit .i64 1)
      ops.store buf (.inl high) right
      pure (.inr (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 2), digits))
    else pure (.inl (i, digits))) (olength, digits)
  if JuliaLean.base.int.eq i (JuliaLean.base.int.lit .i64 1) then
    let rem ← ops.remTen digits (JuliaLean.base.int.lit .u8 0xa)
    let rem ← ops.remByte rem
    let digit ← ops.addByte (JuliaLean.base.int.lit .u8 0x30) rem
    ops.store buf (.inr digit) pos
  pure (JuliaLean.base.int.add pos olength)

/-- Known source callee versus an actually selected more-specific method.
The base tag denotes the queued source body; noMethod retains a
missing method on a type-changing intermediate. No source body is a callback.
Julia source call: base/intfuncs.jl:962,978. -/
-- Source: base/intfuncs.jl:962-962 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return @inline append_c_digits(9, digits, buf, pos) # force loop-unrolling on the length
-- /Source
def formattingAppendCSelected {W V Iter State Buf Other : Type}
    (ops : FormattingAppendOps W V Iter State Buf Other)
    (length : JInt64) (digits : V) (buf : Buf) (pos : JInt64) :
    JuliaLean.base.io.M (FormattingAppendWorld W) (Sum JInt64 Other) := do
  match ops.cRoute digits buf with
  | .base => pure (.inl (← appendCDigits ops length digits buf pos))
  | .custom => ops.customC length digits buf pos
  | .noMethod => throw (.jl (.methodError "append_c_digits"))

/-- Range exception adaptation, preserving every existing exception class.
The concrete range adapters below can be used by other queued constant-range
loops as well. Julia dependency: base/range.jl:935-945. -/
-- Source: base/range.jl:935-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- 
-- /Source
def formattingLiftRange {W A : Type} : JuliaLean.base.range.JlX A → JuliaLean.base.io.M W A
  | .ok value => pure value
  | .error (.jl error) => throw (.jl error)
  | .error (.errorException message) => throw (.errorException message)
  | .error (.dimensionMismatch message) => throw (.foreignError "DimensionMismatch" message)
  | .error .inboundsViolation => throw (.foreignError "UndefinedBehaviour" "range inbounds")
  | .error (.showError error) => throw (.showError error)

/-- Actual native UnitRange construction and installed first/state iteration.
The concrete instance fields use installed native arithmetic/conversion and
installed first/last/empty/step bodies, not a List range or iteration fuel.
Used by base/intfuncs.jl:956-959. Dependencies: range.jl:5,428,439,711,736,
867,877,935-945. -/
-- Source: base/intfuncs.jl:956-959 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         for _ = 1:9
--             @inbounds buf[pos] = UInt8('0')
--             pos += 1
--         end
-- /Source
def formattingForNativeRange {W S : Type} (first last : JInt64)
    (body : S → JInt64 → JuliaLean.base.io.M W S) (initial : S) : JuliaLean.base.io.M W S :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.UnitRange JInt64) JInt64 := ⟨⟩
  letI : JuliaLean.base.range.JFieldStart (JuliaLean.base.range.UnitRange JInt64) JInt64 := ⟨fun r => r.start⟩
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.UnitRange JInt64) JInt64 := ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JFirst (JuliaLean.base.range.UnitRange JInt64) JInt64 :=
    ⟨JuliaLean.base.range.first_OrdinalRange⟩
  letI : JuliaLean.base.range.JLast (JuliaLean.base.range.UnitRange JInt64) JInt64 :=
    ⟨JuliaLean.base.range.last_OrdinalRange⟩
  letI : JuliaLean.base.range.JLt JInt64 JInt64 := ⟨JuliaLean.base.int.lt⟩
  letI : JuliaLean.base.range.JIsempty (JuliaLean.base.range.UnitRange JInt64) :=
    ⟨JuliaLean.base.range.isempty_AbstractUnitRange⟩
  letI : JuliaLean.base.range.JZero JInt64 := ⟨JuliaLean.base.int.lit .i64 0⟩
  letI : HSub JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.sub⟩
  letI : HAdd JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.add⟩
  letI : JuliaLean.base.range.JEq JInt64 JInt64 := ⟨JuliaLean.base.int.eq⟩
  letI : JuliaLean.base.range.JStep (JuliaLean.base.range.UnitRange JInt64) JInt64 :=
    ⟨fun r => pure (JuliaLean.base.range.step_AbstractUnitRange r)⟩
  do
    let interval ← formattingLiftRange (JuliaLean.base.range.colon_T_T_Real first last)
    let next ← formattingLiftRange (JuliaLean.base.range.iterate_OrdinalRange interval)
    JuliaLean.base.io.whileLoop (fun (state, next) => do
      match next with
      | none => pure (.inl state)
      | some (value, iteratorState) =>
          let state ← body state value
          let next ← formattingLiftRange
            (JuliaLean.base.range.iterate_OrdinalRange_state interval iteratorState)
          pure (.inr (state, next))) (initial, next)

/-- Full nine-digit body, including nine sequential writes/increments in
the zero branch and actual selected append_c_digits dispatch otherwise.
The actual constant UnitRange constructor and installed iteration methods
execute, while the unused yielded value is discarded. Julia source: base/intfuncs.jl:954-963. -/
-- Source: base/intfuncs.jl:954-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append_nine_digits(digits::Unsigned, buf, pos::Int)
--     if digits == 0
--         for _ = 1:9
--             @inbounds buf[pos] = UInt8('0')
--             pos += 1
--         end
--         return pos
--     end
--     return @inline append_c_digits(9, digits, buf, pos) # force loop-unrolling on the length
-- end
-- /Source
def appendNineDigits {W V Iter State Buf Other : Type}
    (ops : FormattingAppendOps W V Iter State Buf Other) (digits : V) (buf : Buf) (pos : JInt64) :
    JuliaLean.base.io.M (FormattingAppendWorld W) (Sum JInt64 Other) := do
  if ← ops.equalZero digits (JuliaLean.base.int.lit .i64 0) then
    let pos ← formattingForNativeRange (JuliaLean.base.int.lit .i64 1)
      (JuliaLean.base.int.lit .i64 9) (fun pos _ => do
        ops.store buf (.inl (JuliaLean.base.int.lit .u8 0x30)) pos
        pure (JuliaLean.base.int.add pos (JuliaLean.base.int.lit .i64 1))) pos
    pure (.inl pos)
  else
    formattingAppendCSelected ops (JuliaLean.base.int.lit .i64 9) digits buf pos

/-- Selected append_nine_digits call closes the known source method and
retains unknown/custom/non-Unsigned targets. Julia source: base/intfuncs.jl:975. -/
-- Source: base/intfuncs.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         append_nine_digits(c % UInt32, buf, pos + i - 9)
-- /Source
def formattingAppendNineSelected {W V Iter State Buf Other : Type}
    (ops : FormattingAppendOps W V Iter State Buf Other) (digits : V) (buf : Buf) (pos : JInt64) :
    JuliaLean.base.io.M (FormattingAppendWorld W) (Sum JInt64 Other) := do
  match ops.nineRoute digits buf with
  | .base => appendNineDigits ops digits buf pos
  | .custom => ops.customNine digits buf pos
  | .noMethod => throw (.jl (.methodError "append_nine_digits"))

/-- Complete chunking body with actual helper calls, short-circuiting native
length condition, arbitrary custom intermediates and discarded helper return
values. The final return retains native wrapping position arithmetic.
Source reference: base/intfuncs.jl:965-980. -/
-- Source: base/intfuncs.jl:965-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append_c_digits_fast(olength::Int, digits::Unsigned, buf, pos::Int)
--     i = olength
--     # n.b. olength may be larger than required to print all of `digits` (and will be padded
--     # with zeros), but the printed number will be undefined if it is smaller, and may include
--     # bits of both the high and low bytes.
--     maxpow10 = 0x3b9aca00 # 10e9 as UInt32
--     while i > 9 && digits > typemax(UInt)
--         # do everything in cheap math chunks, using the processor's native math size
--         d, c = divrem(digits, maxpow10)
--         digits = oftype(digits, d)
--         append_nine_digits(c % UInt32, buf, pos + i - 9)
--         i -= 9
--     end
--     append_c_digits(i, digits % UInt, buf, pos)
--     return pos + olength
-- end
-- /Source
def appendCDigitsFast {W V Iter State Buf Other : Type}
    (ops : FormattingAppendOps W V Iter State Buf Other)
    (olength : JInt64) (digits : V) (buf : Buf) (pos : JInt64) :
    JuliaLean.base.io.M (FormattingAppendWorld W) JInt64 := do
  let maxpow10 := JuliaLean.base.int.lit .u32 0x3b9aca00
  let (i, digits) ← JuliaLean.base.io.whileLoop (fun (i, digits) => do
    if JuliaLean.base.int.lt (JuliaLean.base.int.lit .i64 9) i then
      if ← ops.greaterUInt digits (JuliaLean.base.int.lit .u64 (IntTy.max .u64)) then
        let pair ← ops.divremChunk digits maxpow10
        let (d, c) ← formattingDivremPair ops pair
        let digits ← ops.oftype digits d
        let c ← ops.remUInt32 c
        let position := JuliaLean.base.int.sub (JuliaLean.base.int.add pos i) (JuliaLean.base.int.lit .i64 9)
        let _ ← formattingAppendNineSelected ops c buf position
        pure (.inr (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 9), digits))
      else pure (.inl (i, digits))
    else pure (.inl (i, digits))) (olength, digits)
  let digits ← ops.remUInt64 digits
  let _ ← formattingAppendCSelected ops i digits buf pos
  pure (JuliaLean.base.int.add pos olength)

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Concrete UInt8 hexadecimal letter/digit choice using the installed
comparison, ifelse and addition. Julia source: base/intfuncs.jl:1030-1031,1037. -/
-- Source: base/intfuncs.jl:1030-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             unsafe_store!(p, d1 + ifelse(d1 > 0x9, 0x57, 0x30), i-1)
--             unsafe_store!(p, d2 + ifelse(d2 > 0x9, 0x57, 0x30), i)
-- /Source
def formattingHexDigit (digit : JInt .u8) : JInt .u8 :=
  JuliaLean.base.int.add digit
    (JuliaLean.base.operators.ifelseValue
      (JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt digit (JuliaLean.base.int.lit .u8 9))
      (JuliaLean.base.int.lit .u8 0x57) (JuliaLean.base.int.lit .u8 0x30))

/-- Full hexadecimal body with source-ordered dynamic arithmetic, actual
pair loop and final single conditional, explicit byte assertions and the
same concrete shared-memory pointer adapter as bin/oct. No native-counter
assumption is made. Julia source: base/intfuncs.jl:1020-1042. -/
-- Source: base/intfuncs.jl:1020-1042 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function hex(x::Unsigned, pad::Int, neg::Bool)
--     m = (top_set_bit(x) + 3) ÷ 4 # nibbles = ceil(bits / 4)
--     n = neg + max(pad, m)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i >= 2
--             b = (x % UInt8)::UInt8
--             d1, d2 = b >> 0x4, b & 0xf
--             unsafe_store!(p, d1 + ifelse(d1 > 0x9, 0x57, 0x30), i-1)
--             unsafe_store!(p, d2 + ifelse(d2 > 0x9, 0x57, 0x30), i)
--             x >>= 0x8
--             i -= 2
--         end
--         if i > neg
--             d = (x % UInt8)::UInt8 & 0xf
--             unsafe_store!(p, d + ifelse(d > 0x9, 0x57, 0x30), i)
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # UInt8('-')
--     end
--     return str
-- end
-- /Source
def hexUnsigned {W V : Type} (ops : FormattingOps W V)
    (x : V) (pad : JInt64) (neg : Bool) :
    JuliaLean.base.io.M (FormattingWorld W) (FormattingStringValue V) := do
  let top ← ops.topBit x
  let top ← ops.addNative top (JuliaLean.base.int.lit .i64 3)
  let m ← ops.divNative top (JuliaLean.base.int.lit .i64 4)
  let width ← ops.maxPad pad m
  let n ← ops.addBool neg width
  let str ← formattingStringN ops n
  let p ← formattingPointer ops str
  let (x, i) ← JuliaLean.base.io.whileLoop (fun (x, i) => do
    if ← ops.greaterEqual i (JuliaLean.base.int.lit .i64 2) then
      let byte ← formattingLowByte ops x
      let d1 := JuliaLean.base.int.shr_BitUnsigned_BitUnsigned byte (JuliaLean.base.int.lit .u8 4)
      let d2 := JuliaLean.base.int.band byte (JuliaLean.base.int.lit .u8 15)
      let left := formattingHexDigit d1
      let i1 ← ops.subNative i (JuliaLean.base.int.lit .i64 1)
      formattingStore ops p left (.inr i1)
      formattingStore ops p (formattingHexDigit d2) (.inr i)
      let x ← ops.shiftRight x (JuliaLean.base.int.lit .u8 8)
      let i ← ops.subNative i (JuliaLean.base.int.lit .i64 2)
      pure (.inr (x, i))
    else pure (.inl (x, i))) (x, n)
  if ← ops.greaterBool i neg then
    let byte ← formattingLowByte ops x
    let d := JuliaLean.base.int.band byte (JuliaLean.base.int.lit .u8 15)
    formattingStore ops p (formattingHexDigit d) (.inr i)
  if neg then
    formattingStore ops p (JuliaLean.base.int.lit .u8 0x2d) (.inl (JuliaLean.base.int.lit .i64 1))
  pure str

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- The supplied ByteCodec is the runtime's representation of UInt16, not
an open Julia dispatch target. Its existing encoding/decoding laws and the
fixed two-byte width are representation invariants. The ABI is held fixed
throughout a run, while every table cell lives in the shared mutable byte
heap. Julia source use: base/intfuncs.jl:923,996,1007; pointer.jl:151. -/
-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
structure DecABI where
  word : JuliaLean.base.pointer.ByteCodec (JInt .u16)
  wordBytes : word.elementSize.val = 2

/-- Live Array/Memory header for the const-bound _dec_d100. The cells are
not copied here: all values are read from memoryAddress in the very same
ByteHeap modified by String pointer stores. Resizing/offset changes remain
possible through the mutable world. Native lengths and window validity are
actual representation invariants. Julia source: base/intfuncs.jl:923-936. -/
-- Source: base/intfuncs.jl:923-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const _dec_d100 = UInt16[
-- # generating expression: UInt16[(0x30 + i % 10) << 0x8 + (0x30 + i ÷ 10) for i = 0:99]
-- #    0 0,    0 1,    0 2,    0 3, and so on in little-endian
--   0x3030, 0x3130, 0x3230, 0x3330, 0x3430, 0x3530, 0x3630, 0x3730, 0x3830, 0x3930,
--   0x3031, 0x3131, 0x3231, 0x3331, 0x3431, 0x3531, 0x3631, 0x3731, 0x3831, 0x3931,
--   0x3032, 0x3132, 0x3232, 0x3332, 0x3432, 0x3532, 0x3632, 0x3732, 0x3832, 0x3932,
--   0x3033, 0x3133, 0x3233, 0x3333, 0x3433, 0x3533, 0x3633, 0x3733, 0x3833, 0x3933,
--   0x3034, 0x3134, 0x3234, 0x3334, 0x3434, 0x3534, 0x3634, 0x3734, 0x3834, 0x3934,
--   0x3035, 0x3135, 0x3235, 0x3335, 0x3435, 0x3535, 0x3635, 0x3735, 0x3835, 0x3935,
--   0x3036, 0x3136, 0x3236, 0x3336, 0x3436, 0x3536, 0x3636, 0x3736, 0x3836, 0x3936,
--   0x3037, 0x3137, 0x3237, 0x3337, 0x3437, 0x3537, 0x3637, 0x3737, 0x3837, 0x3937,
--   0x3038, 0x3138, 0x3238, 0x3338, 0x3438, 0x3538, 0x3638, 0x3738, 0x3838, 0x3938,
--   0x3039, 0x3139, 0x3239, 0x3339, 0x3439, 0x3539, 0x3639, 0x3739, 0x3839, 0x3939
-- ]
-- /Source
structure DecTableHeader where
  memoryAddress : JuliaLean.base.pointer.Ptr (JInt .u16)
  memoryLength : Nat
  nativeMemory : memoryLength < 2 ^ 63
  offset : Nat
  length : JInt64
  validWindow : 0 ≤ length.val ∧ (offset : Int) + length.val ≤ (memoryLength : Int)

/-- The byte heap is shared by the String and current global Array; custom
callees may mutate either through the same effect state.
Source reference: base/intfuncs.jl:996-998. -/
-- Source: base/intfuncs.jl:996-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 v = @inbounds _dec_d100[1 + (s % Int)]
--                 unsafe_store!(p, (v >> 8) % UInt8, i - 2*j)
--                 unsafe_store!(p, v % UInt8, i - 2*j - 1)
-- /Source
abbrev DecWorld (W : Type) := FormattingWorld (W × DecTableHeader)

/-- Identity of the const global Array passed to genuinely other-index
methods; its mutable header and cells remain in DecWorld.
Source reference: base/intfuncs.jl:996. -/
-- Source: base/intfuncs.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 v = @inbounds _dec_d100[1 + (s % Int)]
-- /Source
inductive DecTableToken where
  | decD100

/-- A current typed view of the shared raw memory, used solely to embed its
contents in the supplied Array model. pointerRef supplies the actual native
address/stride arithmetic and runtime byte decoding. Rebuilding this pure
view at each read makes aliases visible; it is not a source allocation or
an additional effectful traversal. Julia dependency: base/essentials.jl:1073-1077. -/
-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
def decPairView (abi : DecABI) (header : DecTableHeader)
    (heap : JuliaLean.base.pointer.ByteHeap) : FormattingPairs where
  cells := (List.range header.memoryLength).map fun (k : Nat) =>
    JuliaLean.base.pointer.pointerRef abi.word heap header.memoryAddress
      (JuliaLean.base.int.lit .i64 ((k : Int) + 1)) (JuliaLean.base.int.lit .i64 1)
  nativeMemory := by simpa only [List.length_map, List.length_range] using header.nativeMemory
  offset := header.offset
  length := header.length
  validWindow := by simpa only [List.length_map, List.length_range] using header.validWindow

/-- Known native-index table reads use the complete installed Array path
through formattingReadPair, on the current shared-byte-heap view. Earlier
String stores can therefore change the next observed UInt16 table value.
No error or table value is supplied by an arbitrary callback.
Source reference: base/intfuncs.jl:996,1007. -/
-- Source: base/intfuncs.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 v = @inbounds _dec_d100[1 + (s % Int)]
-- /Source
def decReadPairNative {W : Type} (abi : DecABI) (index : JInt64) :
    JuliaLean.base.io.M (DecWorld W) (JInt .u16) := fun state@((_, header), heap) =>
  match formattingReadPair index ((), decPairView abi header heap) with
  | none => none
  | some (.ok (value, _)) => some (.ok (value, state))
  | some (.error (error, _)) => some (.error (error, state))

/-- Full open dispatch for dec's genuinely unknown numeric, protocol, Array
index and stored-value types. rem32/rem64/remInt/remByte do not silently
assert the nominal target type: only explicit tagged known results take a
closed concrete route. indexedFinal extracts only the first field of the
final indexed_iterate result; no unused second state is required.

convertByte retains an arbitrary result until pointerset performs its UInt8
check, AFTER Int(index) has executed and passed its own native check.
Conditional operations include Julia Bool validation and propagate its TypeError.
The fixed global-table token records the actual Array argument to an unknown
index method. All callees share both the live table header and raw byte heap.
Unit-valued store leaves erase only unused return values, without imposing
a Julia Unit assertion or dropping any mutation, error or divergence.
Source reference: base/intfuncs.jl:983-1018; pointer.jl:178. -/
-- Source: base/intfuncs.jl:983-1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function dec(x::Unsigned, pad::Int, neg::Bool)
--     n = neg + ndigits(x, pad=pad)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i > 9 && x > typemax(UInt)
--             d, r = divrem(x, 0x3b9aca00) # 10^9
--             x = oftype(x, d)
--             r32 = r % UInt32
--             for j in 0:3
--                 q, s = divrem(r32, 0x64)
--                 r32 = q
--                 v = @inbounds _dec_d100[1 + (s % Int)]
--                 unsafe_store!(p, (v >> 8) % UInt8, i - 2*j)
--                 unsafe_store!(p, v % UInt8, i - 2*j - 1)
--             end
--             unsafe_store!(p, 0x30 + (r32 % UInt8), i - 8)
--             i -= 9
--         end
--         y = x % UInt
--         while i >= 2
--             d, r = divrem(y, 0x64)
--             y = d
--             v = @inbounds _dec_d100[1 + (r % Int)]
--             unsafe_store!(p, (v >> 8) % UInt8, i)
--             unsafe_store!(p, v % UInt8, i - 1)
--             i -= 2
--         end
--         if i > neg
--             unsafe_store!(p, 0x30 + (rem(y, 0xa) % UInt8), i)
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # '-'
--     end
--     return str
-- end
-- /Source
structure DecOps (W V Iter State : Type) where
  abi : DecABI
  formatting : FormattingOps (W × DecTableHeader) V
  ndigits : V → JInt64 → JuliaLean.base.io.M (DecWorld W) V
  greaterNative : V → JInt64 → JuliaLean.base.io.M (DecWorld W) Bool
  greaterUInt : V → JInt .u64 → JuliaLean.base.io.M (DecWorld W) Bool
  divremChunk : V → JInt .u32 → JuliaLean.base.io.M (DecWorld W) Iter
  divrem100 : V → JInt .u8 → JuliaLean.base.io.M (DecWorld W) Iter
  indexedFirst : Iter → JInt64 → JuliaLean.base.io.M (DecWorld W) (V × State)
  indexedFinal : Iter → JInt64 → State → JuliaLean.base.io.M (DecWorld W) V
  oftype : V → V → JuliaLean.base.io.M (DecWorld W) V
  rem32 : V → JuliaLean.base.io.M (DecWorld W) V
  rem64 : V → JuliaLean.base.io.M (DecWorld W) V
  remInt : V → JuliaLean.base.io.M (DecWorld W) V
  addIndexOne : JInt64 → V → JuliaLean.base.io.M (DecWorld W) (Sum JInt64 V)
  getOtherIndex : DecTableToken → V → JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u16) V)
  shiftPairValue : V → JInt64 → JuliaLean.base.io.M (DecWorld W) V
  remByte : V → JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u8) V)
  addByte : JInt .u8 → V → JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u8) V)
  remTen : V → JInt .u8 → JuliaLean.base.io.M (DecWorld W) V
  valueStoreRoute : V → Sum JInt64 V → FormattingStoreRoute
  customValueStore : JuliaLean.base.pointer.Ptr (JInt .u8) → V → Sum JInt64 V →
    JuliaLean.base.io.M (DecWorld W) Unit
  convertByte : V → JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u8) V)
  storeOtherValue : V → V → Sum JInt64 V → JuliaLean.base.io.M (DecWorld W) Unit

/-- Actual sequential destructuring of the arbitrary divrem result, including
first-state provenance and final-value-only protocol validation.
Source reference: base/intfuncs.jl:990,994,1005. -/
-- Source: base/intfuncs.jl:994-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 q, s = divrem(r32, 0x64)
--                 r32 = q
-- /Source
def decDestructure {W V Iter State : Type} (ops : DecOps W V Iter State) (result : Iter) :
    JuliaLean.base.io.M (DecWorld W) (V × V) := do
  let (first, state) ← ops.indexedFirst result (JuliaLean.base.int.lit .i64 1)
  let second ← ops.indexedFinal result (JuliaLean.base.int.lit .i64 2) state
  pure (first, second)

/-- Source index expression has no Int assertion. A tagged native result
uses the installed concrete Array read; the genuinely other-index route
retains its selected method and arbitrary return type.
Source reference: base/intfuncs.jl:996,1007. -/
-- Source: base/intfuncs.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 v = @inbounds _dec_d100[1 + (s % Int)]
-- /Source
def decGetPair {W V Iter State : Type} (ops : DecOps W V Iter State) (remainder : V) :
    JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u16) V) := do
  let rem ← ops.remInt remainder
  let index ← ops.addIndexOne (JuliaLean.base.int.lit .i64 1) rem
  match index with
  | .inl index => pure (.inl (← decReadPairNative ops.abi index))
  | .inr index => ops.getOtherIndex .decD100 index

/-- The known UInt16 route uses installed native shift/remainder operations;
a custom Array result retains its own dynamic methods and effects.
Source reference: base/intfuncs.jl:997,1008. -/
-- Source: base/intfuncs.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 unsafe_store!(p, (v >> 8) % UInt8, i - 2*j)
-- /Source
def decPairHigh {W V Iter State : Type} (ops : DecOps W V Iter State) :
    Sum (JInt .u16) V → JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u8) V)
  | .inl value => pure (.inl (JuliaLean.base.int.remT .u8
      (JuliaLean.base.int.shr_Int value (JuliaLean.base.int.lit .i64 8))))
  | .inr value => do
      let shifted ← ops.shiftPairValue value (JuliaLean.base.int.lit .i64 8)
      ops.remByte shifted

/-- The low-byte expression runs after the high-byte store, so a mutable
custom pair result can observe that store's effects. A known UInt16 remains
the already-read local value. Julia source: base/intfuncs.jl:998,1009. -/
-- Source: base/intfuncs.jl:998-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 unsafe_store!(p, v % UInt8, i - 2*j - 1)
-- /Source
def decPairLow {W V Iter State : Type} (ops : DecOps W V Iter State) :
    Sum (JInt .u16) V → JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u8) V)
  | .inl value => pure (.inl (JuliaLean.base.int.remT .u8 value))
  | .inr value => ops.remByte value

/-- ASCII addition closes the concrete UInt8 branch while preserving an
arbitrary custom remainder/addition result. There is no source byte assertion.
Source reference: base/intfuncs.jl:1000,1013. -/
-- Source: base/intfuncs.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             unsafe_store!(p, 0x30 + (r32 % UInt8), i - 8)
-- /Source
def decAscii {W V Iter State : Type} (ops : DecOps W V Iter State) (value : V) :
    JuliaLean.base.io.M (DecWorld W) (Sum (JInt .u8) V) := do
  match ← ops.remByte value with
  | .inl byte => pure (.inl (JuliaLean.base.int.add (JuliaLean.base.int.lit .u8 0x30) byte))
  | .inr value => ops.addByte (JuliaLean.base.int.lit .u8 0x30) value

/-- General value/index unsafe_store! selection. On the known typed-pointer
body the value conversion executes first, then Int(index), then pointerset's
argument checks in their actual order. In particular an invalid converted
value does not suppress index-conversion mutation/errors. The C check order
is quoted in the supplied JuliaLean/src/runtime_intrinsics_c.lean for pinned
src/runtime_intrinsics.c:476-497: pointer, long index, alignment,
then element type. Successful bytes use the installed pointerSet helper.
Julia dependency: base/pointer.jl:178. -/
-- Source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
-- /Source
def decStore {W V Iter State : Type} (ops : DecOps W V Iter State) (p : FormattingPointer V)
    (value : Sum (JInt .u8) V) (index : Sum JInt64 V) : JuliaLean.base.io.M (DecWorld W) Unit := do
  match value with
  | .inl byte => formattingStore ops.formatting p byte index
  | .inr value =>
      match p with
      | .other p => ops.storeOtherValue p value index
      | .bytePointer p =>
          match ops.valueStoreRoute value index with
          | .custom => ops.customValueStore p value index
          | .noMethod => throw (.jl (.methodError "unsafe_store!"))
          | .integer =>
              let converted ← ops.convertByte value
              let index ← match index with
                | .inl index => JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 index)
                | .inr index => ops.formatting.toNativeIndex index
              match converted with
              | .inl byte => formattingNativeWrite p byte index
              | .inr _ => throw (.foreignError "TypeError" "pointerset UInt8")

/-- Full decimal formatting, including all unknown arithmetic/protocol
results, both actual unbounded loops, the installed four-iteration UnitRange,
actual global-table aliasing, value/index store dispatch, and all source
check/effect order. No unsigned intermediate or counter is silently narrowed.
Source reference: base/intfuncs.jl:983-1018. -/
-- Source: base/intfuncs.jl:983-1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function dec(x::Unsigned, pad::Int, neg::Bool)
--     n = neg + ndigits(x, pad=pad)
--     str = _string_n(n)
--     GC.@preserve str begin
--         p = pointer(str)
--         i = n
--         while i > 9 && x > typemax(UInt)
--             d, r = divrem(x, 0x3b9aca00) # 10^9
--             x = oftype(x, d)
--             r32 = r % UInt32
--             for j in 0:3
--                 q, s = divrem(r32, 0x64)
--                 r32 = q
--                 v = @inbounds _dec_d100[1 + (s % Int)]
--                 unsafe_store!(p, (v >> 8) % UInt8, i - 2*j)
--                 unsafe_store!(p, v % UInt8, i - 2*j - 1)
--             end
--             unsafe_store!(p, 0x30 + (r32 % UInt8), i - 8)
--             i -= 9
--         end
--         y = x % UInt
--         while i >= 2
--             d, r = divrem(y, 0x64)
--             y = d
--             v = @inbounds _dec_d100[1 + (r % Int)]
--             unsafe_store!(p, (v >> 8) % UInt8, i)
--             unsafe_store!(p, v % UInt8, i - 1)
--             i -= 2
--         end
--         if i > neg
--             unsafe_store!(p, 0x30 + (rem(y, 0xa) % UInt8), i)
--         end
--         neg && unsafe_store!(p, 0x2d, 1) # '-'
--     end
--     return str
-- end
-- /Source
def decUnsigned {W V Iter State : Type} (ops : DecOps W V Iter State)
    (x : V) (pad : JInt64) (neg : Bool) :
    JuliaLean.base.io.M (DecWorld W) (FormattingStringValue V) := do
  let digits ← ops.ndigits x pad
  let n ← ops.formatting.addBool neg digits
  let str ← formattingStringN ops.formatting n
  let p ← formattingPointer ops.formatting str
  let (x, i) ← JuliaLean.base.io.whileLoop (fun (x, i) => do
    if ← ops.greaterNative i (JuliaLean.base.int.lit .i64 9) then
      if ← ops.greaterUInt x (JuliaLean.base.int.lit .u64 (IntTy.max .u64)) then
        let pair ← ops.divremChunk x (JuliaLean.base.int.lit .u32 0x3b9aca00)
        let (d, r) ← decDestructure ops pair
        let x ← ops.oftype x d
        let r32 ← ops.rem32 r
        let r32 ← formattingForNativeRange (JuliaLean.base.int.lit .i64 0)
          (JuliaLean.base.int.lit .i64 3) (fun r32 j => do
            let pair ← ops.divrem100 r32 (JuliaLean.base.int.lit .u8 0x64)
            let (q, s) ← decDestructure ops pair
            let r32 := q
            let v ← decGetPair ops s
            let high ← decPairHigh ops v
            let twice := JuliaLean.base.int.mulSame (JuliaLean.base.int.lit .i64 2) j
            let index ← ops.formatting.subNative i twice
            decStore ops p high (.inr index)
            let low ← decPairLow ops v
            let index ← ops.formatting.subNative i twice
            let index ← ops.formatting.subNative index (JuliaLean.base.int.lit .i64 1)
            decStore ops p low (.inr index)
            pure r32) r32
        let byte ← decAscii ops r32
        let index ← ops.formatting.subNative i (JuliaLean.base.int.lit .i64 8)
        decStore ops p byte (.inr index)
        let i ← ops.formatting.subNative i (JuliaLean.base.int.lit .i64 9)
        pure (.inr (x, i))
      else pure (.inl (x, i))
    else pure (.inl (x, i))) (x, n)
  let y ← ops.rem64 x
  let (y, i) ← JuliaLean.base.io.whileLoop (fun (y, i) => do
    if ← ops.formatting.greaterEqual i (JuliaLean.base.int.lit .i64 2) then
      let pair ← ops.divrem100 y (JuliaLean.base.int.lit .u8 0x64)
      let (d, r) ← decDestructure ops pair
      let y := d
      let v ← decGetPair ops r
      let high ← decPairHigh ops v
      decStore ops p high (.inr i)
      let low ← decPairLow ops v
      let index ← ops.formatting.subNative i (JuliaLean.base.int.lit .i64 1)
      decStore ops p low (.inr index)
      let i ← ops.formatting.subNative i (JuliaLean.base.int.lit .i64 2)
      pure (.inr (y, i))
    else pure (.inl (y, i))) (y, i)
  if ← ops.formatting.greaterBool i neg then
    let rem ← ops.remTen y (JuliaLean.base.int.lit .u8 0xa)
    let byte ← decAscii ops rem
    decStore ops p byte (.inr i)
  if neg then
    formattingStore ops.formatting p (JuliaLean.base.int.lit .u8 0x2d) (.inl (JuliaLean.base.int.lit .i64 1))
  pure str

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Heterogeneous, effectful dispatch for base/intfuncs.jl:1072. The comparison
is a returned tuple element, so it is not conditionally asserted to Bool. -/
-- Source: base/intfuncs.jl:1072-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- split_sign(n::Integer) = (unsigned(abs(n)), n < 0)
-- /Source
structure SplitSignOps (m : Type → Type) (I A U C : Type) where
  abs : I → m A
  unsigned : A → m U
  lessZero : I → JInt64 → m C

/-- Full generic split_sign body, retaining the original n for its second
component and every intermediate reference/effect. Source: base/intfuncs.jl:1072. -/
-- Source: base/intfuncs.jl:1072-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- split_sign(n::Integer) = (unsigned(abs(n)), n < 0)
-- /Source
def splitSignInteger {m : Type → Type} [Monad m] {I A U C : Type}
    (ops : SplitSignOps m I A U C) (n : I) : m (U × C) := do
  let absolute ← ops.abs n
  let magnitude ← ops.unsigned absolute
  let negative ← ops.lessZero n (JuliaLean.base.int.lit .i64 0)
  pure (magnitude, negative)

/-- Concrete installed arithmetic instance, including wrapping signed abs and
unsigned bit-preserving conversion. Source: base/intfuncs.jl:1072. -/
-- Source: base/intfuncs.jl:1072-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- split_sign(n::Integer) = (unsigned(abs(n)), n < 0)
-- /Source
def splitSignBitsOps {W : Type} (t : IntTy) :
    SplitSignOps (JuliaLean.base.io.M W) (JInt t) (JInt t) (JInt t.toUnsigned) Bool where
  abs x := pure (JuliaLean.base.int.abs x)
  unsigned x := pure (JuliaLean.base.int.unsigned x)
  lessZero x zero := pure (JuliaLean.base.int.lt x zero)

/-- Exact selected formatter identity in base/intfuncs.jl:1104-1115. -/
-- Source: base/intfuncs.jl:1104-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if base == 2
--         (n_positive, neg) = split_sign(n)
--         bin(n_positive, pad, neg)
--     elseif base == 8
--         (n_positive, neg) = split_sign(n)
--         oct(n_positive, pad, neg)
--     elseif base == 10
--         (n_positive, neg) = split_sign(n)
--         dec(n_positive, pad, neg)
--     elseif base == 16
--         (n_positive, neg) = split_sign(n)
--         hex(n_positive, pad, neg)
-- /Source
inductive IntegerFormat where
  | binary | octal | decimal | hexadecimal
  deriving BEq, DecidableEq

/-- Full dynamic runtime carrier for the generic string wrapper. No result of
custom min/max, abs, unsigned, split_sign or comparison is forced back into an
input type. V may be a tagged union of all runtime values, and S is the actual
indexed-iterate state. Conditional comparison fields include adjacent Bool
validation; raw comparisons used as operands of & deliberately do not.
Native Int is fixed only after the explicit pad assertion. Fixed Signed and
formatter function identities are encoded in the corresponding fields.
Source reference: base/intfuncs.jl:1101-1119. -/
-- Source: base/intfuncs.jl:1101-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function string(n::Integer; base::Integer = 10, pad::Integer = 1)
--     @constprop :aggressive
--     pad = (min(max(pad, typemin(Int)), typemax(Int)) % Int)::Int
--     if base == 2
--         (n_positive, neg) = split_sign(n)
--         bin(n_positive, pad, neg)
--     elseif base == 8
--         (n_positive, neg) = split_sign(n)
--         oct(n_positive, pad, neg)
--     elseif base == 10
--         (n_positive, neg) = split_sign(n)
--         dec(n_positive, pad, neg)
--     elseif base == 16
--         (n_positive, neg) = split_sign(n)
--         hex(n_positive, pad, neg)
--     else
--         _base(base, base > 0 ? unsigned(abs(n)) : convert(Signed, n), pad, (base>0) & (n<0))
--     end
-- end
-- /Source
structure StringIntegerOps (W V S : Type) where
  maxPad : V → JInt64 → JuliaLean.base.io.M W V
  minPad : V → JInt64 → JuliaLean.base.io.M W V
  remInt : V → JuliaLean.base.io.M W (Sum JInt64 V)
  equalBase : V → JInt64 → JuliaLean.base.io.M W Bool
  splitSign : V → JuliaLean.base.io.M W V
  indexedFirst : V → JInt64 → JuliaLean.base.io.M W (V × S)
  indexedLast : V → JInt64 → S → JuliaLean.base.io.M W V
  format : IntegerFormat → V → JInt64 → V → JuliaLean.base.io.M W V
  positiveCondition : V → JInt64 → JuliaLean.base.io.M W Bool
  abs : V → JuliaLean.base.io.M W V
  unsigned : V → JuliaLean.base.io.M W V
  convertSigned : V → JuliaLean.base.io.M W V
  positiveRaw : V → JInt64 → JuliaLean.base.io.M W V
  negativeRaw : V → JInt64 → JuliaLean.base.io.M W V
  bitAnd : V → V → JuliaLean.base.io.M W V
  general : V → V → JInt64 → V → JuliaLean.base.io.M W V

/-- Source body after keyword argument binding. The native pad assertion occurs
before base dispatch. Destructuring retains arbitrary iterable result/state;
only the final indexed result's value is consumed. The fallback evaluates base>0
twice, at its actual distinct positions, and eagerly computes both operands of &.
All called methods dispatch on a type the generic source does not fix.
Source reference: base/intfuncs.jl:1101-1119. -/
-- Source: base/intfuncs.jl:1101-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function string(n::Integer; base::Integer = 10, pad::Integer = 1)
--     @constprop :aggressive
--     pad = (min(max(pad, typemin(Int)), typemax(Int)) % Int)::Int
--     if base == 2
--         (n_positive, neg) = split_sign(n)
--         bin(n_positive, pad, neg)
--     elseif base == 8
--         (n_positive, neg) = split_sign(n)
--         oct(n_positive, pad, neg)
--     elseif base == 10
--         (n_positive, neg) = split_sign(n)
--         dec(n_positive, pad, neg)
--     elseif base == 16
--         (n_positive, neg) = split_sign(n)
--         hex(n_positive, pad, neg)
--     else
--         _base(base, base > 0 ? unsigned(abs(n)) : convert(Signed, n), pad, (base>0) & (n<0))
--     end
-- end
-- /Source
def stringInteger {W V S : Type} (ops : StringIntegerOps W V S)
    (n base pad : V) : JuliaLean.base.io.M W V := do
  let lower ← ops.maxPad pad (JuliaLean.base.int.typemin .i64)
  let upper ← ops.minPad lower (JuliaLean.base.int.typemax .i64)
  let pad ← match ← ops.remInt upper with
    | .inl native => pure native
    | .inr _ => throw (.foreignError "TypeError" "typeassert Int")
  let selected ← do
    if ← ops.equalBase base (JuliaLean.base.int.lit .i64 2) then pure (some IntegerFormat.binary)
    else if ← ops.equalBase base (JuliaLean.base.int.lit .i64 8) then pure (some IntegerFormat.octal)
    else if ← ops.equalBase base (JuliaLean.base.int.lit .i64 10) then pure (some IntegerFormat.decimal)
    else if ← ops.equalBase base (JuliaLean.base.int.lit .i64 16) then pure (some IntegerFormat.hexadecimal)
    else pure none
  match selected with
  | some kind =>
      let pair ← ops.splitSign n
      let (positive, state) ← ops.indexedFirst pair (JuliaLean.base.int.lit .i64 1)
      let negative ← ops.indexedLast pair (JuliaLean.base.int.lit .i64 2) state
      ops.format kind positive pad negative
  | none =>
      let magnitude ← if ← ops.positiveCondition base (JuliaLean.base.int.lit .i64 0) then do
        let absolute ← ops.abs n
        ops.unsigned absolute
      else ops.convertSigned n
      let positive ← ops.positiveRaw base (JuliaLean.base.int.lit .i64 0)
      let negative ← ops.negativeRaw n (JuliaLean.base.int.lit .i64 0)
      let sign ← ops.bitAnd positive negative
      ops.general base magnitude pad sign

/-- The fixed Core typeof operation is pure runtime metadata, while the selected
typed digits callee may have any result type and arbitrary effects. Keyword
values are passed unchanged. Julia source: base/intfuncs.jl:1207-1208. -/
-- Source: base/intfuncs.jl:1207-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- digits(n::Integer; base::Integer = 10, pad::Integer = 1) =
--     digits(typeof(base), n, base = base, pad = pad)
-- /Source
structure DigitsDefaultOps (W V Ty : Type) where
  typeOf : V → Ty
  typed : Ty → V → V → V → JuliaLean.base.io.M W V

/-- Full default-type digits wrapper. Source: base/intfuncs.jl:1207-1208. -/
-- Source: base/intfuncs.jl:1207-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- digits(n::Integer; base::Integer = 10, pad::Integer = 1) =
--     digits(typeof(base), n, base = base, pad = pad)
-- /Source
def digitsDefault {W V Ty : Type} (ops : DigitsDefaultOps W V Ty)
    (n base pad : V) : JuliaLean.base.io.M W V :=
  ops.typed (ops.typeOf base) n base pad

/-- Dynamic selected leaves: T is an arbitrary Integer subtype, including custom
user types, and ndigits/zeros/digits! may return heterogeneous runtime values.
No concrete Vector allocation or indexing origin is imposed on selected zeros.
Source reference: base/intfuncs.jl:1210-1212. -/
-- Source: base/intfuncs.jl:1210-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function digits(T::Type{<:Integer}, n::Integer; base::Integer = 10, pad::Integer = 1)
--     digits!(zeros(T, ndigits(n, base=base, pad=pad)), n, base=base)
-- end
-- /Source
structure DigitsTypeOps (W V Ty : Type) where
  count : V → V → V → JuliaLean.base.io.M W V
  zeros : Ty → V → JuliaLean.base.io.M W V
  fill : V → V → V → JuliaLean.base.io.M W V

/-- Full typed digits composition; successful allocation precedes any digit
mutation, and arbitrary allocation aliases and errors are retained.
Source reference: base/intfuncs.jl:1210-1212. -/
-- Source: base/intfuncs.jl:1210-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function digits(T::Type{<:Integer}, n::Integer; base::Integer = 10, pad::Integer = 1)
--     digits!(zeros(T, ndigits(n, base=base, pad=pad)), n, base=base)
-- end
-- /Source
def digitsType {W V Ty : Type} (ops : DigitsTypeOps W V Ty)
    (typeValue : Ty) (n base pad : V) : JuliaLean.base.io.M W V := do
  let count ← ops.count n base pad
  let array ← ops.zeros typeValue count
  ops.fill array n base

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

end JuliaLean.base.intfuncs.Models2Group16


namespace JuliaLean.base.intfuncs.Models2Group16
open JuliaLean

/-- Fixed function identities passed to Core.applicable. This is a projection
of the installed runtime_internals.TypeOps.applicable boundary: its callee is
one of the two Base extrema functions, and its sole argument is the exact T.
Source reference: base/intfuncs.jl:1219. -/
-- Source: base/intfuncs.jl:1219-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hastypemax(::Type{T}) where {T} = applicable(typemax, T) && applicable(typemin, T)
-- /Source
inductive ExtremumFunction where
  | maximum | minimum
  deriving BEq, DecidableEq

/-- Typed projection of the existing Core applicability boundary, preserving
the exact queried function and type argument, effects, and exceptions.
Source reference: base/intfuncs.jl:1219. -/
-- Source: base/intfuncs.jl:1219-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hastypemax(::Type{T}) where {T} = applicable(typemax, T) && applicable(typemin, T)
-- /Source
structure HasTypeMaxOps (W Ty : Type) where
  applicable : ExtremumFunction → Ty → JuliaLean.base.io.M W Bool

/-- Preserve Core applicability query order, short circuit, state, errors and
fixed function/argument identity. A minimum query is never executed when the
maximum query returned false. Julia source: base/intfuncs.jl:1219. -/
-- Source: base/intfuncs.jl:1219-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- hastypemax(::Type{T}) where {T} = applicable(typemax, T) && applicable(typemin, T)
-- /Source
def hasTypeMaxType {W Ty : Type} (ops : HasTypeMaxOps W Ty) (typeValue : Ty) :
    JuliaLean.base.io.M W Bool := do
  if ← ops.applicable .maximum typeValue then
    ops.applicable .minimum typeValue
  else pure false

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.base.intfuncs.Models2Group16

open JuliaLean

/-- Every intermediate and the final oftype result may have its own type.
Source reference: base/intfuncs.jl:1293. -/
-- Source: base/intfuncs.jl:1293-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isqrt(x::Integer) = oftype(x, trunc(sqrt(x)))
-- /Source
structure IsqrtOps (m : Type → Type) (I F T R : Type) where
  sqrt : I → m F
  trunc : F → m T
  oftype : I → T → m R

/-- Complete generic composition with the original x supplied to oftype.
Source reference: base/intfuncs.jl:1293. -/
-- Source: base/intfuncs.jl:1293-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isqrt(x::Integer) = oftype(x, trunc(sqrt(x)))
-- /Source
def isqrtInteger {m : Type → Type} [Monad m] {I F T R : Type}
    (ops : IsqrtOps m I F T R) (x : I) : m R := do
  let root ← ops.sqrt x
  let integer ← ops.trunc root
  ops.oftype x integer

/-- Concrete IEEE64 callee uses the installed kernel-computable F64 square-root
model, with lossless representation changes on its input and output. No approximate
root or correctness-law callback is supplied. Julia source: base/math.jl:629-632. -/
-- Source: base/math.jl:629-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function sqrt(x::IEEEFloat)
--     x < zero(x) && throw_complex_domainerror(:sqrt, x)
--     sqrt_llvm(x)
-- end
-- /Source
def isqrtSqrtFloat64 (x : JuliaLean.base.float.FV .f64) :
    Jl (JuliaLean.base.float.FV .f64) := do
  let result ← JuliaLean.Float.F64.sqrt (JuliaLean.Float.F64.ofBits x.toBits)
  pure (JuliaLean.Promotion.Fl.ofBits result.toNat)

/-- Concrete native sqrt follows the installed Real fallback and Float64 conversion.
Native inputs and converted floats have different concrete types, so the fallback's
same-type MethodError check is false. Julia source: base/math.jl:1322-1330. -/
-- Source: base/math.jl:1322-1330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for f in (:sin, :cos, :tan, :asin, :atan, :acos,
--           :sinh, :cosh, :tanh, :asinh, :acosh, :atanh,
--           :exp, :exp2, :exp10, :expm1, :log, :log2, :log10, :log1p,
--           :exponent, :sqrt, :cbrt, :sinpi, :cospi, :sincospi, :tanpi)
--     @eval function ($f)(x::Real)
--         xf = float(x)
--         xf isa typeof(x) && throw(MethodError($f, (x,)))
--         return ($f)(xf)
--     end
-- /Source
def isqrtSqrtBits {t : IntTy} (x : JInt t) : Jl (JuliaLean.base.float.FV .f64) :=
  JuliaLean.base.math.realFallback JuliaLean.base.float.float_BitInteger
    (fun _ => false) "sqrt" isqrtSqrtFloat64 x

/-- Concrete native adapter, with installed float truncation and checked integer
conversion. Julia source: base/intfuncs.jl:1293. -/
-- Source: base/intfuncs.jl:1293-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isqrt(x::Integer) = oftype(x, trunc(sqrt(x)))
-- /Source
def isqrtIntegerBitsOps {World : Type} (t : IntTy) :
    IsqrtOps (JuliaLean.base.io.M World) (JInt t) (JuliaLean.base.float.FV .f64)
      (JuliaLean.base.float.FV .f64) (JInt t) where
  sqrt := fun x => JuliaLean.base.io.liftJl (isqrtSqrtBits x)
  trunc := fun x => pure (JuliaLean.base.float.trunc_llvm x)
  oftype := fun _ x => JuliaLean.base.io.liftJl (JuliaLean.base.float.intOfFloat t x)

/-- All four concrete input types reuse the preserved source-mirrored wide body,
with every concrete callee now closed. The width condition is exactly its source
union. Julia source: base/intfuncs.jl:1295-1302. -/
-- Source: base/intfuncs.jl:1295-1302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isqrt(x::Union{Int64,UInt64,Int128,UInt128})
--     x==0 && return x
--     s = oftype(x, trunc(sqrt(x)))
--     # fix with a Newton iteration, since conversion to float discards
--     # too many bits.
--     s = (s + div(x,s)) >> 1
--     s*s > x ? s-1 : s
-- end
-- /Source
def isqrtWideNative {World : Type} {t : IntTy} (_wide : t.bits = 64 ∨ t.bits = 128)
    (x : JInt t) : JuliaLean.base.io.M World (JInt t) :=
  JuliaLean.base.io.liftJl (JuliaLean.base.intfuncs.isqrt_Wide isqrtSqrtBits
    (fun f => pure (JuliaLean.base.float.trunc_llvm f))
    (JuliaLean.base.float.intOfFloat t) JuliaLean.base.int.divSame x)

/-- Concrete public native dispatch selects the wide method exactly for 64/128-bit
inputs. Julia source: base/intfuncs.jl:1293-1302. -/
-- Source: base/intfuncs.jl:1293-1302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isqrt(x::Integer) = oftype(x, trunc(sqrt(x)))
-- 
-- function isqrt(x::Union{Int64,UInt64,Int128,UInt128})
--     x==0 && return x
--     s = oftype(x, trunc(sqrt(x)))
--     # fix with a Newton iteration, since conversion to float discards
--     # too many bits.
--     s = (s + div(x,s)) >> 1
--     s*s > x ? s-1 : s
-- end
-- /Source
def isqrtNative {World : Type} {t : IntTy} (x : JInt t) :
    JuliaLean.base.io.M World (JInt t) :=
  if h : t.bits = 64 ∨ t.bits = 128 then isqrtWideNative h x
  else isqrtInteger (isqrtIntegerBitsOps t) x


/-- Runtime iteration protocol: either nothing or an item with private next state;
both calls retain effects and errors. See doc/src/manual/interfaces.md:29-54.
Julia source use: base/intfuncs.jl:1519-1521. -/
-- Source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp!(x::AbstractArray, lo, hi)
--     @inbounds for i in eachindex(x)
--         x[i] = clamp(x[i], lo, hi)
--     end
--     x
-- end
-- /Source
structure TailIterationOps (World Iter Item State : Type) where
  first : Iter → JuliaLean.base.io.M World (Option (Item × State))
  next : Iter → State → JuliaLean.base.io.M World (Option (Item × State))

/-- Actual function identity at the existing Core apply-iterate boundary.
Source reference: base/intfuncs.jl:1373. -/
-- Source: base/intfuncs.jl:1373-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- binomial(n::Integer, k::Integer) = binomial(promote(n, k)...)
-- /Source
inductive TailBinomialFunction where
  | binomial
  deriving DecidableEq, BEq

/-- The promote result is opaque: arbitrary tuple, iterator, changed types, or an
invalid splat. applyIterate is the existing CoreOps.applyIterate projection, with
runtime iteration, allocation, arity, dispatch and failures retained.
Source reference: base/intfuncs.jl:1373. -/
-- Source: base/intfuncs.jl:1373-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- binomial(n::Integer, k::Integer) = binomial(promote(n, k)...)
-- /Source
structure BinomialPromoteOps (m : Type → Type) (N K P R : Type) where
  promote : N → K → m P
  applyIterate : IterateToken → TailBinomialFunction → P → m R

/-- Full mixed-Integer forwarding body; the downstream method depends on the
arbitrary promotion result, not a prescribed pair. Julia source: base/intfuncs.jl:1373. -/
-- Source: base/intfuncs.jl:1373-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- binomial(n::Integer, k::Integer) = binomial(promote(n, k)...)
-- /Source
def binomialMixed {m : Type → Type} [Monad m] {N K P R : Type}
    (ops : BinomialPromoteOps m N K P R) (n : N) (k : K) : m R := do
  let promoted ← ops.promote n k
  ops.applyIterate .baseIterate .binomial promoted

/-- V includes all changed values; Iter is the selected OneTo constructor's result.
The source fixes neither k's concrete Integer type nor the target chosen for its
OneTo constructor. Product dispatch likewise depends on that result and the closure.
Source reference: base/intfuncs.jl:1428-1433. -/
-- Source: base/intfuncs.jl:1428-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function binomial(x::Number, k::Integer)
--     k < 0 && return zero(x)/one(k)
--     # we don't use prod(i -> (x-i+1), 1:k) / factorial(k),
--     # and instead divide each term by i, to avoid spurious overflow.
--     return prod(i -> (x-(i-1))/i, OneTo(k), init=oneunit(x)/one(k))
-- end
-- /Source
structure BinomialNumberOps (World V Iter Other : Type) where
  negative : V → JInt64 → JuliaLean.base.io.M World (Bool ⊕ Other)
  zero : V → JuliaLean.base.io.M World V
  one : V → JuliaLean.base.io.M World V
  oneunit : V → JuliaLean.base.io.M World V
  oneTo : V → JuliaLean.base.io.M World Iter
  subtractLiteral : V → JInt64 → JuliaLean.base.io.M World V
  subtract : V → V → JuliaLean.base.io.M World V
  divide : V → V → JuliaLean.base.io.M World V
  product : (V → JuliaLean.base.io.M World V) → Iter → V → JuliaLean.base.io.M World V

/-- Actual product closure evaluates i-1, then x-(i-1), then division by original i.
Source reference: base/intfuncs.jl:1432. -/
-- Source: base/intfuncs.jl:1432-1432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return prod(i -> (x-(i-1))/i, OneTo(k), init=oneunit(x)/one(k))
-- /Source
def binomialNumberTerm {World V Iter Other : Type}
    (ops : BinomialNumberOps World V Iter Other) (x i : V) : JuliaLean.base.io.M World V := do
  let offset ← ops.subtractLiteral i (JuliaLean.base.int.lit .i64 1)
  let numerator ← ops.subtract x offset
  ops.divide numerator i

/-- Complete Number-binomial method with OneTo-before-init evaluation and the
actual captured term closure. Julia source: base/intfuncs.jl:1428-1433. -/
-- Source: base/intfuncs.jl:1428-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function binomial(x::Number, k::Integer)
--     k < 0 && return zero(x)/one(k)
--     # we don't use prod(i -> (x-i+1), 1:k) / factorial(k),
--     # and instead divide each term by i, to avoid spurious overflow.
--     return prod(i -> (x-(i-1))/i, OneTo(k), init=oneunit(x)/one(k))
-- end
-- /Source
def binomialNumberGeneric {World V Iter Other : Type}
    (ops : BinomialNumberOps World V Iter Other) (x k : V) : JuliaLean.base.io.M World V := do
  if ← gcdxAssertBool (← ops.negative k (JuliaLean.base.int.lit .i64 0)) then
    let zero ← ops.zero x
    let one ← ops.one k
    ops.divide zero one
  else
    let iterator ← ops.oneTo k
    let unit ← ops.oneunit x
    let one ← ops.one k
    let initial ← ops.divide unit one
    ops.product (binomialNumberTerm ops x) iterator initial

/-- Full open clamp operations with effectful/non-Bool comparisons and type changes.
Source reference: base/intfuncs.jl:1461-1464. -/
-- Source: base/intfuncs.jl:1461-1464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp(x::X, lo::L, hi::H) where {X,L,H}
--     T = promote_type(X, L, H)
--     return (x > hi) ? convert(T, hi) : (x < lo) ? convert(T, lo) : convert(T, x)
-- end
-- /Source
structure ClampOps (World V Ty Other : Type) where
  typeOf : V → Ty
  promoteType : Ty → Ty → Ty → JuliaLean.base.io.M World Ty
  greater : V → V → JuliaLean.base.io.M World (Bool ⊕ Other)
  less : V → V → JuliaLean.base.io.M World (Bool ⊕ Other)
  convert : Ty → V → JuliaLean.base.io.M World V

/-- Promotion precedes comparisons; only the chosen argument is converted.
Source reference: base/intfuncs.jl:1461-1464. -/
-- Source: base/intfuncs.jl:1461-1464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp(x::X, lo::L, hi::H) where {X,L,H}
--     T = promote_type(X, L, H)
--     return (x > hi) ? convert(T, hi) : (x < lo) ? convert(T, lo) : convert(T, x)
-- end
-- /Source
def clampGeneric {World V Ty Other : Type} (ops : ClampOps World V Ty Other)
    (x lo hi : V) : JuliaLean.base.io.M World V := do
  let T ← ops.promoteType (ops.typeOf x) (ops.typeOf lo) (ops.typeOf hi)
  if ← gcdxAssertBool (← ops.greater x hi) then ops.convert T hi
  else if ← gcdxAssertBool (← ops.less x lo) then ops.convert T lo
  else ops.convert T x

/-- Distinct original-input and changing bound/result carriers.
Source reference: base/intfuncs.jl:1485-1492. -/
-- Source: base/intfuncs.jl:1485-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp(x, ::Type{T}) where {T<:Integer}
--     # delegating to clamp(x, typemin(T), typemax(T)) would promote types
--     # this way, we avoid unnecessary conversions
--     # think of, e.g., clamp(big(2) ^ 200, Int16)
--     lo = typemin(T)
--     hi = typemax(T)
--     return (x > hi) ? hi : (x < lo) ? lo : convert(T, x)
-- end
-- /Source
structure ClampTypeOps (World X Ty V Other : Type) where
  typeMin : Ty → JuliaLean.base.io.M World V
  typeMax : Ty → JuliaLean.base.io.M World V
  greater : X → V → JuliaLean.base.io.M World (Bool ⊕ Other)
  less : X → V → JuliaLean.base.io.M World (Bool ⊕ Other)
  convert : Ty → X → JuliaLean.base.io.M World V

/-- Both extrema are evaluated before comparisons, and out-of-range branches return
actual bounds without extra conversion. Julia source: base/intfuncs.jl:1485-1492. -/
-- Source: base/intfuncs.jl:1485-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp(x, ::Type{T}) where {T<:Integer}
--     # delegating to clamp(x, typemin(T), typemax(T)) would promote types
--     # this way, we avoid unnecessary conversions
--     # think of, e.g., clamp(big(2) ^ 200, Int16)
--     lo = typemin(T)
--     hi = typemax(T)
--     return (x > hi) ? hi : (x < lo) ? lo : convert(T, x)
-- end
-- /Source
def clampType {World X Ty V Other : Type} (ops : ClampTypeOps World X Ty V Other)
    (x : X) (T : Ty) : JuliaLean.base.io.M World V := do
  let lo ← ops.typeMin T
  let hi ← ops.typeMax T
  if ← gcdxAssertBool (← ops.greater x hi) then pure hi
  else if ← gcdxAssertBool (← ops.less x lo) then pure lo
  else ops.convert T x

/-- Native adapter with installed promotion/comparison/conversion.
Source reference: base/intfuncs.jl:1461-1464. -/
-- Source: base/intfuncs.jl:1461-1464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp(x::X, lo::L, hi::H) where {X,L,H}
--     T = promote_type(X, L, H)
--     return (x > hi) ? convert(T, hi) : (x < lo) ? convert(T, lo) : convert(T, x)
-- end
-- /Source
def clampBitsOps {World : Type} (t : IntTy) : ClampOps World (JInt t) IntTy Empty where
  typeOf := fun _ => t
  promoteType := JuliaLean.base.promotion.promoteTypeThree
    (fun a b => pure (if a = b then JuliaLean.base.promotion.promoteTypeSame a else a.promote b))
  greater := fun a b => pure (.inl (JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt a b))
  less := fun a b => pure (.inl (JuliaLean.base.int.lt a b))
  convert := fun _ a => JuliaLean.base.io.liftJl (JuliaLean.base.int.convert t a)

/-- Every native source/target pair uses concrete bounds and checked conversion.
Source reference: base/intfuncs.jl:1485-1492. -/
-- Source: base/intfuncs.jl:1485-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp(x, ::Type{T}) where {T<:Integer}
--     # delegating to clamp(x, typemin(T), typemax(T)) would promote types
--     # this way, we avoid unnecessary conversions
--     # think of, e.g., clamp(big(2) ^ 200, Int16)
--     lo = typemin(T)
--     hi = typemax(T)
--     return (x > hi) ? hi : (x < lo) ? lo : convert(T, x)
-- end
-- /Source
def clampTypeBitsOps {World : Type} (source target : IntTy) :
    ClampTypeOps World (JInt source) IntTy (JInt target) Empty where
  typeMin := fun _ => pure (JuliaLean.base.int.typemin target)
  typeMax := fun _ => pure (JuliaLean.base.int.typemax target)
  greater := fun a b => pure (.inl (JuliaLean.base.operators.greaterThan JuliaLean.base.int.lt a b))
  less := fun a b => pure (.inl (JuliaLean.base.int.lt a b))
  convert := fun _ a => JuliaLean.base.io.liftJl (JuliaLean.base.int.convert target a)

/-- Actually selected custom specialization or the known generic fallback.
Julia source uses: base/intfuncs.jl:1520,1533. -/
-- Source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp!(x::AbstractArray, lo, hi)
--     @inbounds for i in eachindex(x)
--         x[i] = clamp(x[i], lo, hi)
--     end
--     x
-- end
-- /Source
inductive ClampRoute (World V : Type) where
  | generic
  | custom (method : V → V → V → JuliaLean.base.io.M World V)

/-- Known fallback is explicit; only genuinely selected specializations are open.
Julia source uses: base/intfuncs.jl:1520,1533. -/
-- Source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp!(x::AbstractArray, lo, hi)
--     @inbounds for i in eachindex(x)
--         x[i] = clamp(x[i], lo, hi)
--     end
--     x
-- end
-- /Source
structure ClampDispatchOps (World V Ty Other : Type) where
  generic : ClampOps World V Ty Other
  select : V → V → V → ClampRoute World V

/-- Actual dispatch shared by mutating and range wrappers.
Julia source uses: base/intfuncs.jl:1520,1533. -/
-- Source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp!(x::AbstractArray, lo, hi)
--     @inbounds for i in eachindex(x)
--         x[i] = clamp(x[i], lo, hi)
--     end
--     x
-- end
-- /Source
def clampSelected {World V Ty Other : Type}
    (ops : ClampDispatchOps World V Ty Other) (x lo hi : V) : JuliaLean.base.io.M World V :=
  match ops.select x lo hi with
  | .generic => clampGeneric ops.generic x lo hi
  | .custom method => method x lo hi

/-- Bool records the inbounds context. A setindex! return has an independent carrier
and is discarded, never used as a replacement array.
Source reference: base/intfuncs.jl:1518-1523. -/
-- Source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp!(x::AbstractArray, lo, hi)
--     @inbounds for i in eachindex(x)
--         x[i] = clamp(x[i], lo, hi)
--     end
--     x
-- end
-- /Source
structure ClampBangOps (World A Iter Index State V Ty Other SetResult : Type) where
  eachindex : A → JuliaLean.base.io.M World Iter
  iteration : TailIterationOps World Iter Index State
  getindex : Bool → A → Index → JuliaLean.base.io.M World V
  setindex : Bool → A → V → Index → JuliaLean.base.io.M World SetResult
  clamp : ClampDispatchOps World V Ty Other

/-- Live iteration between writes with original-array identity and exact
get/clamp/set order. No finite list or functional rebinding replaces source
mutation. Julia source: base/intfuncs.jl:1518-1523. -/
-- Source: base/intfuncs.jl:1518-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function clamp!(x::AbstractArray, lo, hi)
--     @inbounds for i in eachindex(x)
--         x[i] = clamp(x[i], lo, hi)
--     end
--     x
-- end
-- /Source
def clampBangGeneric {World A Iter Index State V Ty Other SetResult : Type}
    (ops : ClampBangOps World A Iter Index State V Ty Other SetResult)
    (x : A) (lo hi : V) : JuliaLean.base.io.M World A := do
  let iterator ← ops.eachindex x
  JuliaLean.base.io.whileLoop (fun (state : Option State) => do
    let step ← match state with
      | none => ops.iteration.first iterator
      | some state => ops.iteration.next iterator state
    match step with
    | none => pure (.inl x)
    | some (index, next) =>
      let value ← ops.getindex true x index
      let result ← clampSelected ops.clamp value lo hi
      let _ ← ops.setindex true x result index
      pure (.inr (some next))) none

/-- Endpoints can have changed runtime types and observable effects.
Source reference: base/intfuncs.jl:1533. -/
-- Source: base/intfuncs.jl:1533-1533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- clamp(x::Integer, r::AbstractUnitRange{<:Integer}) = clamp(x, first(r), last(r))
-- /Source
structure ClampRangeOps (World V Range Ty Other : Type) where
  first : Range → JuliaLean.base.io.M World V
  last : Range → JuliaLean.base.io.M World V
  clamp : ClampDispatchOps World V Ty Other

/-- Endpoints are evaluated left-to-right before actual clamp dispatch.
Source reference: base/intfuncs.jl:1533. -/
-- Source: base/intfuncs.jl:1533-1533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- clamp(x::Integer, r::AbstractUnitRange{<:Integer}) = clamp(x, first(r), last(r))
-- /Source
def clampRange {World V Range Ty Other : Type}
    (ops : ClampRangeOps World V Range Ty Other) (x : V) (range : Range) :
    JuliaLean.base.io.M World V := do
  let first ← ops.first range
  let last ← ops.last range
  clampSelected ops.clamp x first last

end JuliaLean.base.intfuncs.Models2Group16

namespace JuliaLean.MiscCov.RyuUtils

open JuliaLean

/-- A byte buffer: `buf[k]` for one-based `k`. -/
abbrev Buf := Int → Nat

def Buf.set (b : Buf) (k : Int) (v : Nat) : Buf := fun i => if i = k then v else b i

/-- `Base.append_c_digits_fast(olength, digits, buf, pos)` (`base/intfuncs.jl`):
writes the `olength` low decimal digits of `digits`, most significant first, at
`pos:pos+olength-1` and returns `pos + olength`. -/
def appendCDigits (olength : Nat) (digits : Nat) (buf : Buf) (pos : Int) : Buf × Int :=
  (fun i => if pos ≤ i ∧ i < pos + olength then
      48 + digits / 10 ^ (olength - 1 - (i - pos).toNat) % 10 else buf i, pos + olength)

end JuliaLean.MiscCov.RyuUtils

namespace JuliaLean.IntArith.Checked

open JuliaLean

/-- base/intfuncs.jl:423,435: trailing_zeros(p), counted up to the operand width.
This helper is used only on the strictly positive exponent branches. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 then 1 + trailingZeros fuel (n / 2) else 0

/-- base/intfuncs.jl:430-431,437-438: repeat checked squaring in source order. -/
def squareTimes {t : IntTy} : Nat → JInt t → Jl (JInt t)
  | 0, x => .ok x
  | n + 1, x => do squareTimes n (← checkedMul x x)

/-- base/intfuncs.jl:434-441: each iteration removes trailing zeros and one
set bit, then squares before multiplying the accumulator. -/
def powerLoop {t : IntTy} (width : Nat) (p : Nat) (x y : JInt t) : Jl (JInt t) :=
  match p with
  | 0 => .ok y
  | n + 1 => do
    let z := trailingZeros width (n + 1)
    let x ← squareTimes (z + 1) x
    let y ← checkedMul y x
    powerLoop width ((n + 1) / 2 / 2 ^ z) x y
termination_by p
decreasing_by
  have h := Nat.div_le_self ((n + 1) / 2) (2 ^ trailingZeros width (n + 1))
  have h' := Nat.div_lt_self (by omega : 0 < n + 1) (by omega : 1 < 2)
  omega

/-- base/checked.jl:364-366 and base/intfuncs.jl:399-442. The preliminary
x*x is wrapping and square_is_useful is false for checked_mul. No promotion
with the exponent takes place. The negative-exponent unit test uses wrapping
unary minus, exactly as the source does. -/
def checkedPow {t s : IntTy} (x : JInt t) (p : JInt s) : Jl (JInt t) := do
  let _xSquared := x * x
  if p.val = 1 then pure x
  else if p.val = 0 then pure (JInt.lit t 1)
  else if p.val = 2 then checkedMul x x
  else if p.val < 0 then
    if x.val = 1 then pure x
    else if (-x).val = 1 then
      pure (if p.val % 2 = 0 then JInt.lit t 1 else x)
    else .error (.domainError "")
  else
    let z := trailingZeros s.bits p.val.toNat
    let x ← squareTimes z x
    powerLoop s.bits (p.val.toNat / 2 / 2 ^ z) x x

end JuliaLean.IntArith.Checked

namespace JuliaLean.HashOps

variable {α : Type}

/-- `literal_pow`, `base/intfuncs.jl:470-489`. -/
def literalPowFallback (o : FallbackOps α) (pow : α → Int → α) (x : α) (p : Int) : α :=
  if p < 0 then pow (invFallback o x) (-p) else pow x p

def literalPowHW (o : FallbackOps α) (pow : α → Int → α) (x : α) (p : Int) : α :=
  if p = 0 then oneFallback o x
  else if p = 1 then x
  else if p = 2 then o.mul x x
  else if p = 3 then o.mul (o.mul x x) x
  else if p = -1 then invFallback o x
  else if p = -2 then let i := invFallback o x; o.mul i i
  else literalPowFallback o pow x p

end JuliaLean.HashOps

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- The base-`b` digits of `n`, least significant first, at least one (`ndigits(n; base)`). -/
def absDigits (n b : Nat) : List Nat := go n (n + 1)
where
  go (n : Nat) : Nat → List Nat
    | 0 => []
    | k + 1 => if n < b then [n] else n % b :: go (n / b) k

/-- `digits(T, n; base)` for a machine `n`: `digits!(zeros(T, ndigits(n; base)), n; base)` with
the generic loop `n, d = divrem(n, base); a[i] = d` (`base/intfuncs.jl:1249-1268`). Storing a
digit converts it to `T`, throwing `InexactError` when it does not fit. For a power-of-two base
and `n ≥ 0` Julia shifts instead (`base/intfuncs.jl:1256-1262`), which yields the same digits. -/
def digitsMachine (t : IntTy) (n : Int) (b : Nat) : Jl (List (JInt t)) :=
  let len := (absDigits n.natAbs b).length
  ((List.range len).foldl (fun (acc : Int × List Int) _ =>
      (acc.1.tdiv b, acc.2 ++ [acc.1.tmod b])) (n, [])).2.mapM (JInt.convert (t.name) t)

end JuliaLean.BigNums

namespace JuliaLean.Promotion

/-- Number of binary digits of `|n|`, `ndigits0z(n, 2)`; `base/intfuncs.jl:764-772`. -/
def ndigits2 (n : Int) : Int := if n == 0 then 0 else (n.natAbs.log2 + 1 : Nat)

end JuliaLean.Promotion

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- The digit character for value `d < base` (`mpz_get_str`, GMP manual §5.12: lower-case
letters for bases up to 36; upper-case then lower-case for bases 37 to 62). -/
def digitChar (d base : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d)
  else if base ≤ 36 then Char.ofNat (87 + d)
  else if d < 36 then Char.ofNat (55 + d) else Char.ofNat (61 + d)
/-- The base-`b` digit characters of `abs(n)`, most significant first. -/
def digitChars (n : Int) (b : Nat) : List Char :=
  ((absDigits n.natAbs b).map (fun d => digitChar d b)).reverse

/-- Canonical positive-base rendering with zero padding to `pad` digits: `mpz_get_str` plus the
padding of `string(n::BigInt; base, pad)` (`base/gmp.jl:768-781`), and equally
`dec`/`hex`/`oct`/`bin`/`_base` for machine integers (`base/intfuncs.jl:1047-1119`). -/
def renderPos (n : Int) (b : Nat) (pad : Int) : List Char :=
  if n = 0 ∧ pad < 1 then []
  else
    let ds := digitChars n b
    let z := pad.toNat - ds.length
    (if n < 0 then ['-'] else []) ++ List.replicate z '0' ++ ds

/-- Negative-base digits of `_base` (`base/intfuncs.jl:1056-1066`): `mod(x, -b)` and `cld(x, b)`,
least significant first, at least `pad` of them. -/
def negDigits (x : Int) (b : Nat) (pad : Nat) : List Nat := go x (x.natAbs + pad + 1) 0
where
  go (x : Int) : Nat → Nat → List Nat
    | 0, _ => []
    | k + 1, i =>
      if x = 0 ∧ pad ≤ i then []
      else (x.fmod b).toNat :: go (-((-x).fdiv (-(b : Int)))) k (i + 1)

/-- `_base(base, x, pad, false)` for `base < 0`, `base/intfuncs.jl:1047-1070`. -/
def baseNeg (base : Int) (x : Int) (pad : Int) : Jl (List Char) :=
  if ¬ (2 ≤ -base ∧ -base ≤ 62) then .error (.domainError "base must satisfy 2 ≤ abs(base) ≤ 62")
  else
    let b := (-base).toNat
    let ds := negDigits x b pad.toNat
    .ok ((ds.map fun d => digitChar d b).reverse)
/-- `string(n::Integer; base, pad)` for a machine integer, `base/intfuncs.jl:1101-1119`. -/
def stringMachine (n : Int) (base pad : Int) : Jl (List Char) :=
  if base = 2 ∨ base = 8 ∨ base = 10 ∨ base = 16 then .ok (renderPos n base.toNat pad)
  else if base < 0 then baseNeg base n pad
  else if ¬ (2 ≤ base ∧ base ≤ 62) then
    .error (.domainError "base must satisfy 2 ≤ abs(base) ≤ 62")
  else .ok (renderPos n base.toNat pad)

end JuliaLean.BigNums


namespace JuliaLean.IntArith.NumberTheory

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

/-- `_bezout_coef`, `base/intfuncs.jl:337-341`. -/
def bezoutCoef (gmpGcdx : Int → Int → Jl (Int × Int × Int))
    (t : WorkTy) (n m : Int) : Jl Int := do
  let (g, x, _) ← match t with
    | none => gmpGcdx n m
    | some _ => gcdxVal t n m
  if g ≠ 1 then .error (.domainError "") else pure x

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
  let x ← JInt.convert (r.name) r x.val
  let y ← JInt.convert (r.name) r b.val
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
    let x ← JInt.convert (r.name) r x.val
    let y ← JInt.convert (r.name) r a.val
    gcd x y
  else
    let x ← JInt.convert (r.name) r a.val
    let y ← JInt.convert (r.name) r b.val
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
    let x ← JInt.convert (r.name) r a.val
    let y ← JInt.convert (r.name) r (abs b).val
    lcm x y
  else
    let x ← JInt.convert (r.name) r a.val
    let y ← JInt.convert (r.name) r b.val
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
    let x ← JInt.convert (r.name) r x.val
    let y ← JInt.convert (r.name) r a.val
    let (d, v, u) ← gcdx x y
    let flip := b.val < 0 ∧ r.signed
    let sign := b - JInt.lit t (if flip then 1 else 0)
    pure (d, u, if sign.val < 0 then -v else v)
  else
    let x ← JInt.convert (r.name) r a.val
    let y ← JInt.convert (r.name) r b.val
    gcdx x y

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
def invmod (gmpGcdx : Int → Int → Jl (Int × Int × Int))
    {s t : IntTy} (n : JInt s) (m : JInt t) :
    Jl (JInt (modTy s t)) := do
  if m.val = 0 then .error (.domainError "")
  else
    let r := IntTy.promote s t
    if r.signed then
      let (g, x, _) ← mixedGcdx n m
      if g.val ≠ 1 then .error (.domainError "")
      else
        let z ← mixedMod @uabs x m
        pure (JInt.wrap (modTy s t) z.val)
    else
      let st := r.toSigned
      if n.val ≤ st.max ∧ m.val ≤ st.max then
        let x ← bezoutCoef gmpGcdx (some st) (norm (some st) n.val) (norm (some st) m.val)
        let x := if x < 0 then add (some (IntTy.promote st t)) x (abs m).val else x
        let z ← mixedMod @uabs (JInt.wrap r x) m
        pure (JInt.wrap (modTy s t) z.val)
      else
        let w := widen st
        let x ← bezoutCoef gmpGcdx w (norm w n.val) (norm w m.val)
        let z ← workMod w x (norm w m.val)
        let z := if m.val < 0 then sub w z m.val else z
        let z ← mixedMod @uabs (JInt.wrap r z) m
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

/-- Nonnegative exponent section of `powermod`, `base/intfuncs.jl:542-578`.
The 128-bit overload uses BigInt once, `base/intfuncs.jl:587`. -/
def powermodPositive {s t : IntTy} (x : JInt s) (p : Nat) (m : JInt t) :
    Jl (JInt t) := do
  if m.val = 1 ∨ m.val = -1 then pure (JInt.lit t 0)
  else
    let mm := uabs m
    let bb ← mixedMod @uabs x mm
    let bb := JInt.wrap t.toUnsigned bb.val
    let rr ← if powermodMILegal t.toUnsigned mm && decide (p > 2 * (t.bits / 8)) then
        if bb.val = 0 then pure 0
        else
          let mi ← unsignedMI mm
          pure (powermodMagicLoop mi p (JInt.lit _ 1) bb).val
      else if bb.val = 0 then pure 0
      else powermodLoop (some t.toUnsigned) (widen t.toUnsigned) p mm.val 1 bb.val
    let r ← JInt.convert (t.name) t rr
    pure (if r.val = 0 ∨ m.val > 0 then r else r + m)

/-- `powermod`, `base/intfuncs.jl:524-541,587`, including the 128-bit
BigInt overload before generic p=0 and sign checks. The external GMP
primitive boundary is specified in `gmpPowm`; all Julia conversions,
negative-modulus adjustment, and generic typemin branches are explicit. -/
def powermod (gmpGcdx : Int → Int → Jl (Int × Int × Int))
    (gmpPowermod : Int → Int → Int → Jl Int)
    {s e t : IntTy} (x : JInt s) (p : JInt e) (m : JInt t) :
    Jl (JInt t) := do
  if t.bits = 128 then
    let r ← gmpPowermod x.val p.val m.val
    JInt.convert (t.name) t r
  else if p.val = 0 then JInt.mod (JInt.lit t 1) m
  else if p.val < 0 then
    let imod ← invmod gmpGcdx x m
    if p.val = (-p).val then
      let halfTy := IntTy.promote e .i64
      let half ← JInt.div (JInt.rem halfTy p) (JInt.lit halfTy 2)
      let rhalf ← powermodPositive imod (-half).val.toNat m
      let w := widen t
      let r ← workMod w (mul w rhalf.val rhalf.val) m.val
      let r ← JInt.convert (t.name) t r
      if p.val % 2 ≠ 0 then
        let r ← workMod w (mul w r.val imod.val) m.val
        JInt.convert (t.name) t r
      else pure r
    else powermodPositive imod (-p).val.toNat m
  else powermodPositive x p.val.toNat m

end JuliaLean.IntArith.NumberTheory

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

/-- `base/intfuncs.jl:624`: positivity is checked before population count. -/
def ispow2 {t : IntTy} (x : JInt t) : Bool := x.val > 0 && countOnes x == 1

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
    let b ← JInt.convert (IntTy.i64.name) .i64 base.val
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

end JuliaLean.IntArith.PowersDigits

/-!
Coverage of the `gcd`, `lcm`, `gcdx`, `invmod` methods of `base/intfuncs.jl:44-382`
(master `bbfa0ce4150`). The BitInteger algorithms are the `IntArith.NumberTheory` models
(`gcd` with `binaryGcd`/`absdiff`, `lcm`, `gcdxVal`, `mixedGcd`, `mixedLcm`,
`mixedGcdx`, `promoteMixedSigns`, `invmod`, `bezoutCoef`, `invmodRing`); this file adds
the remaining dispatch methods and states their documented contracts.

The computational regression properties use compact byte grids. Registry coverage uses
the universal source models below, rather than these regression grids.
-/

namespace JuliaLean.IntFuncsCov.Gcd

open JuliaLean JuliaLean.IntArith.NumberTheory JuliaLean.IntFuncsCov

/-! ### Generic `gcd` loop -/

/-- `gcd(a::T, b::T) where T<:Integer`, `base/intfuncs.jl:44-51`, for the integer types
without the BitInteger method (`BigInt`): Euclid's loop with the exact truncating `rem`,
then `checked_abs`, which cannot overflow for an unbounded type. -/
def gcdGeneric (a b : Int) : Int :=
  if _h : b = 0 then (a.natAbs : Int) else gcdGeneric b (a.tmod b)
termination_by b.natAbs
decreasing_by
  simpa only [Int.natAbs_tmod] using Nat.mod_lt a.natAbs (by omega : 0 < b.natAbs)

/-- `gcd(a::Rational) = checked_abs(a.num) // a.den`, `base/intfuncs.jl:153`. -/
def gcdRational {t : IntTy} {R : Type}
    (numerator denominator : R → JInt t) (ofInts : JInt t → JInt t → Jl R) (x : R) : Jl R := do
  let n ← checkedAbs (numerator x)
  ofInts n (denominator x)

/-- `lcm(a::Rational) = gcd(a)`, `base/intfuncs.jl:154`. -/
def lcmRational {t : IntTy} {R : Type}
    (numerator denominator : R → JInt t) (ofInts : JInt t → JInt t → Jl R) (x : R) : Jl R :=
  gcdRational numerator denominator ofInts x

/-- `gcd(a, b, c...) = gcd(a, gcd(b, c...))`, `base/intfuncs.jl:161`. -/
def gcdN {t : IntTy} (a b : JInt t) : List (JInt t) → Jl (JInt t)
  | [] => gcd a b
  | c :: cs => do gcd a (← gcdN b c cs)

/-- `lcm(a, b, c...) = lcm(a, lcm(b, c...))`, `base/intfuncs.jl:162`. -/
def lcmN {t : IntTy} (a b : JInt t) : List (JInt t) → Jl (JInt t)
  | [] => lcm a b
  | c :: cs => do lcm a (← lcmN b c cs)

/-- `gcd(a::T, b::T) where T<:Real` and `lcm(a::T, b::T) where T<:Real`,
`base/intfuncs.jl:163-164`, and `gcdx(a::T, b::T) where T<:Real` (`:262`): a same-type
pair without a more specific method (for example two `Float64`s) throws `MethodError`. -/
def gcdSameReal {α : Type} (_ _ : α) : Jl α := .error (.methodError "gcd")
def lcmSameReal {α : Type} (_ _ : α) : Jl α := .error (.methodError "lcm")
def gcdxSameReal {α : Type} (_ _ : α) : Jl (α × α × α) := .error (.methodError "gcdx")

/-- `gcdx(a, b, cs...)`, `base/intfuncs.jl:264-274`: `d, i, j = gcdx(a, b)`;
`d′, x, ys... = gcdx(d, cs...)`; returns `(d′, i*x, j*x, ys...)`. -/
def gcdxN {t : IntTy} (a b : JInt t) : List (JInt t) → Jl (JInt t × List (JInt t))
  | [] => do
    let (d, u, v) ← gcdx a b
    pure (d, [u, v])
  | c :: cs => do
    let (d, i, j) ← gcdx a b
    let (d', coeffs) ← gcdxN d c cs
    match coeffs with
    | x :: ys => pure (d', i * x :: j * x :: ys)
    | [] => pure (d', [])

/-! ### Arrays -/

/-- The loop of `gcd(abc::AbstractArray{<:Integer})`, `base/intfuncs.jl:178-187`: start from
zero, stop early once the running gcd is one. -/
def gcdArrayLoop {t : IntTy} (a : JInt t) : List (JInt t) → Jl (JInt t)
  | [] => pure a
  | b :: bs => do
    let a ← gcd a b
    if a.val = 1 then pure a else gcdArrayLoop a bs

def gcdArray {t : IntTy} (v : List (JInt t)) : Jl (JInt t) := gcdArrayLoop (JInt.lit t 0) v

/-- `gcd(abc::AbstractArray{<:Real}) = reduce(gcd, abc; init=zero(eltype(abc)))`,
`base/intfuncs.jl:166`, for a two-argument `gcd` `g` of the element type. -/
def gcdRealArray {α : Type} (g : α → α → Jl α) (zero : α) (v : List α) : Jl α :=
  v.foldlM g zero

/-- `lcm(abc::AbstractArray{<:Real})`, `base/intfuncs.jl:167-176`, for integer elements:
`one` for an empty array, `abs(only(abc))` for one element, else `reduce(lcm, abc)`. -/
def lcmArray {t : IntTy} : List (JInt t) → Jl (JInt t)
  | [] => pure (JInt.lit t 1)
  | [a] => pure (if a.val < 0 then -a else a)
  | a :: b :: rest => do
    let l ← lcm a b
    rest.foldlM lcm l

/-- `lcm(abc::AbstractArray{<:Real})` for an empty array of non-integer element type
throws `ArgumentError`, `base/intfuncs.jl:172`. -/
def lcmArrayNonInteger {α : Type} (abs : α → α) (l : α → α → Jl α) : List α → Jl α
  | [] => .error (.argumentError "lcm has no identity")
  | [a] => pure (abs a)
  | a :: b :: rest => do
    let x ← l a b
    rest.foldlM l x

/-- `invmod(n::Integer, ::Type{T})` (`base/intfuncs.jl:370`) computes `invmod(n % T)`:
for every `Int16` value `n` in `-128:127` and both byte types, `(n % T) * invmod(n, T) == 1`
for odd `n`, and `DomainError` for even `n`. `invmod(n, Union{})` throws `MethodError`
(`:371`). -/
def invmodBottom {α : Type} (_ : α) : Jl Unit := .error (.methodError "invmod")

end JuliaLean.IntFuncsCov.Gcd


/-!
Coverage of the integer power methods of `base/intfuncs.jl:384-624` (master
`bbfa0ce4150`): `power_by_squaring`, `^`, `literal_pow`, `throw_domerr_powbysq`, `powermod`,
`_powermod_mi_legal`, `_nextpow2`, `_prevpow2` and `ispow2`. The BitInteger algorithms are
the `IntArith.PowersDigits` (`powerBySquaring`, `nextpow2`, `prevpow2`, `ispow2`) and
`IntArith.NumberTheory` (`powermod`, `powermodMILegal`) models.
-/

namespace JuliaLean.IntFuncsCov.Power

open JuliaLean JuliaLean.IntFuncsCov
open JuliaLean.IntArith.PowersDigits (powerBySquaring nextpow2 prevpow2 ispow2)

/-! ### `power_by_squaring` and `^` -/

/-- `^(x::T, p::T) where {T<:Integer}` and `^(x::Number, p::Integer)`,
`base/intfuncs.jl:450-451`: both are `power_by_squaring(x, p)`. -/
def pow {t pty : IntTy} (x : JInt t) (p : JInt pty) : Jl (JInt t) := powerBySquaring x p

/-- `power_by_squaring(x::Bool, p::Unsigned) = (p==0) | x`, `base/intfuncs.jl:444`, and
`power_by_squaring(x::Bool, p::Integer)`, `:445-448`. -/
def powerBool {pty : IntTy} (x : Bool) (p : JInt pty) : Jl Bool :=
  if pty.signed then
    if p.val < 0 ∧ x = false then .error (.domainError "negative integer exponent")
    else .ok (decide (p.val = 0) || x)
  else .ok (decide (p.val = 0) || x)

/-- The receiver of `throw_domerr_powbysq`: an `Integer`, an `AbstractMatrix`, or anything
else; the three methods at `base/intfuncs.jl:385-397` differ only in their message. -/
inductive PowBase where
  | integer
  | matrix
  | other
  deriving DecidableEq

/-- `throw_domerr_powbysq(x, p)`, `base/intfuncs.jl:385-397`. -/
def throwDomerrPowbysq (k : PowBase) (p : Int) : Jl Unit :=
  match k with
  | .integer => .error (.domainError s!"Cannot raise an integer x to a negative power {p}.")
  | .matrix => .error (.domainError s!"Cannot raise an integer matrix x to a negative power {p}.")
  | .other => .error (.domainError s!"Cannot raise an integer x to a negative power {p}.")

/-! ### `literal_pow` -/

/-- `literal_pow(f, x, ::Val{p}) = f(x, p)`, `base/intfuncs.jl:460`. -/
def literalPowFallback {α β : Type} (f : α → Int → β) (x : α) (p : Int) : β := f x p

/-- The hardware-integer specializations of `literal_pow(^, x, Val(p))` for `p` in `0:3`,
`base/intfuncs.jl:470-473`: `one(x)`, `x`, `x*x`, `x*x*x`. -/
def literalPowHW {t : IntTy} (x : JInt t) (p : Fin 4) : JInt t :=
  match p with
  | 0 => JInt.lit t 1
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x

/-- `literal_pow(^, x::HWNumber, Val{-1}) = inv(x)` and `Val{-2}`: `(i=inv(x); i*i)`,
`base/intfuncs.jl:474-475`, for a BitInteger `x`: `inv` is `1/Float64(x)`. -/
def literalPowHWNeg {t : IntTy} (x : JInt t) (two : Bool) : JuliaLean.Float.F64 :=
  let i := JuliaLean.Float.F64.div JuliaLean.Float.F64.one (JuliaLean.Float.F64.ofJInt x)
  if two then JuliaLean.Float.F64.mul i i else i

/-- `literal_pow(^, x::AbstractFloat, Val{p}) = x^p` and `Val{-1}`: `inv(x)`,
`base/intfuncs.jl:478-479`, for a floating-point `^` and `inv`. -/
def literalPowFloat {α : Type} (pow : α → Int → α) (inv : α → α) (x : α) (p : Int) : α :=
  if p = -1 then inv x else pow x p

/-- The generic `literal_pow(::typeof(^), x, Val{p})`, `base/intfuncs.jl:483-493`: a negative
power of a `BitInteger64` is computed as `Float64(x)^p`, of anything else as `inv(x)^(-p)`. -/
def literalPowGeneric {α β : Type} (pow : α → Int → β) (inv : α → α) (toFloat : α → α)
    (isBitInteger64 : Bool) (x : α) (p : Int) : β :=
  if p < 0 then
    if isBitInteger64 then pow (toFloat x) p else pow (inv x) (-p)
  else pow x p

/-- `ispow2(x::Number) = isreal(x) && ispow2(real(x))`, `base/intfuncs.jl:622`, for a number
type with `isreal`, `real` and the real `ispow2`. -/
def ispow2Number {α ρ : Type} (isreal : α → Bool) (real : α → ρ) (ispow2Real : ρ → Bool)
    (x : α) : Bool :=
  isreal x && ispow2Real (real x)

end JuliaLean.IntFuncsCov.Power

namespace JuliaLean.Combinatorics

open JuliaLean

def checkedValue (t : IntTy) (x : Int) : Jl (JInt t) :=
  if h : t.min ≤ x ∧ x ≤ t.max then .ok ⟨x, h⟩
  else .error (.overflowError "binomial overflows")

private def binomialLoop (t : IntTy) : Nat → JInt t → JInt t → JInt t → Jl (JInt t)
  | 0, x, _, _ => .ok x
  | fuel + 1, x, nn, rr => do
      let xt := (x.val * nn.val) / rr.val
      let x' ← checkedValue t xt
      binomialLoop t fuel x' (nn + JInt.lit t 1) (rr + JInt.lit t 1)

/-- Same-type `binomial`, `base/intfuncs.jl:1375-1402`. The loop counter is
the post-symmetry `k-1`; `widemul` is exact in the mathematical `Int` used for
`xt`, followed by the source range check `x == xt`. -/
def binomialFixed (t : IntTy) (n0 k0 : JInt t) : Jl (JInt t) :=
  if k0.val < 0 then .ok (JInt.lit t 0)
  else
    let sgn := if n0.val < 0 ∧ k0.val % 2 ≠ 0 then JInt.lit t (-1) else JInt.lit t 1
    let n := if n0.val < 0 then -n0 + k0 - JInt.lit t 1 else n0
    if k0.val > n.val then .ok (JInt.lit t 0)
    else if k0.val = 0 ∨ k0.val = n.val then .ok sgn
    else if k0.val = 1 then .ok (sgn * n)
    else
      let k := if k0.val > n.val / 2 then n - k0 else k0
      let x := n - k + JInt.lit t 1
      let nn := x + JInt.lit t 1
      match binomialLoop t (k.val - 1).toNat x nn (JInt.lit t 2) with
      | .error e => .error e
      | .ok r => .ok (if sgn.val < 0 then -r else r)

end JuliaLean.Combinatorics

namespace JuliaLean.FloatRanges

open JuliaLean.Float

/-- `clamp(x, lo, hi)` on Int; `base/intfuncs.jl:1461-1464`. -/
def iclamp (x lo hi : I64) : I64 :=
  if x.val > hi.val then hi else if x.val < lo.val then lo else x

/-- `clamp(x, lo, hi)` on Float64; `base/intfuncs.jl:1461-1464`. -/
def fclamp (x lo hi : F64) : F64 :=
  if F64.lt hi x then hi else if F64.lt x lo then lo else x

end JuliaLean.FloatRanges

/-!
Integer to string and digit functions of `base/intfuncs.jl` at master
`bbfa0ce4150`: `string(n; base, pad)` with its `bin`/`oct`/`dec`/`hex`/`_base`
writers (lines 878-1119), `digits`/`digits!` (1207-1281) and `bitstring`
(1140-1167). Digit counts reuse `JuliaLean.IntArith.PowersDigits`.

Strings are lists of bytes. The writers fill a buffer of `n` bytes by index, as
Julia does with `unsafe_store!`; the buffer starts as zero bytes (Julia's
`_string_n` leaves it uninitialized, but every writer stores every index).

Arithmetic that cannot wrap is exact `Int` arithmetic, each time with the
reason: `_base` and `digits!` only divide by a base of magnitude at least two
(after Julia's promotion of the operands), which can neither overflow nor
change sign. The `string` writers for bases 2, 8, 10, 16 and `bitstring`
use the source's unsigned bit operations.

`digits` is modelled for an `Int` base (`digits(n; base::Int)`, element type
`Int`), Julia's default, with `n` of any `BitInteger` type.

Changes from 1.13.2: `string` clamps the pad with mixed-type `min`/`max`, which
throw `InexactError` for a `UInt64`/`UInt128` pad in 1.13.2; `hex` counts its
digits as `(top_set_bit(x) + 3) ÷ 4` instead of `2sizeof(x) - leading_zeros(x) >> 2`
(equal for these types); writers use `unsafe_store!` instead of `StringMemory`.
-/

namespace JuliaLean.ParsePrint.IntPrint

open JuliaLean JuliaLean.ParsePrint JuliaLean.IntArith.PowersDigits

/-- A byte buffer with one-based indices. -/
abbrev Buf := List Nat

/-- `unsafe_store!(p, v, i)`. -/
def store (b : Buf) (i : Int) (v : Nat) : Buf := b.set (i - 1).toNat v

/-- `_string_n(n)`. -/
def newBuf (n : Int) : Buf := List.replicate n.toNat 0

def chMinus : Nat := 45

/-- `bin` loop storing four digits per step, `base/intfuncs.jl:885-894`. -/
def binLoop4 {t : IntTy} : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i ≥ 4 then
      let b : JInt .u32 := JInt.rem .u32 (JInt.rem .u8 x)
      let d := JInt.lit .u32 0x30303030 +
        band (shr (b * JInt.lit .u32 0x08040201) 3) (JInt.lit .u32 0x01010101)
      let buf := store buf (i - 3) (JInt.rem .u8 d).val.toNat
      let buf := store buf (i - 2) (JInt.rem .u8 (shr d 8)).val.toNat
      let buf := store buf (i - 1) (JInt.rem .u8 (shr d 16)).val.toNat
      let buf := store buf i (JInt.rem .u8 (shr d 24)).val.toNat
      binLoop4 f (buf, shr x 4, i - 4)
    else (buf, x, i)

/-- `bin` loop storing one digit per step, `base/intfuncs.jl:895-899`. -/
def binLoop1 {t : IntTy} (neg : Bool) : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i > (if neg then 1 else 0) then
      let buf := store buf i (48 + Nat.land (JInt.rem .u8 x).val.toNat 1)
      binLoop1 neg f (buf, shr x 1, i - 1)
    else (buf, x, i)

/-- The final `neg && unsafe_store!(p, 0x2d, 1)` of every writer. -/
def signed (neg : Bool) (buf : Buf) : Buf := if neg then store buf 1 chMinus else buf

/-- `bin(x::Unsigned, pad, neg)`, `base/intfuncs.jl:878-903`. -/
def bin {t : IntTy} (x : JInt t) (pad : Int) (neg : Bool) : Buf :=
  let m : Int := topSetBit x
  let n := (if neg then 1 else 0) + max pad m
  let (buf, x, i) := binLoop4 (n.toNat / 4 + 1) (newBuf n, x, n)
  let (buf, _, _) := binLoop1 neg (n.toNat + 1) (buf, x, i)
  signed neg buf

/-- `oct` loop, `base/intfuncs.jl:912-916`. -/
def octLoop {t : IntTy} (neg : Bool) : Nat → Buf × JInt t × Int → Buf
  | 0, (buf, _, _) => buf
  | f+1, (buf, x, i) =>
    if i > (if neg then 1 else 0) then
      octLoop neg f (store buf i (48 + Nat.land (JInt.rem .u8 x).val.toNat 7), shr x 3, i - 1)
    else buf

/-- `oct(x::Unsigned, pad, neg)`, `base/intfuncs.jl:905-920`. -/
def oct {t : IntTy} (x : JInt t) (pad : Int) (neg : Bool) : Buf :=
  let m : Int := (topSetBit x + 2) / 3
  let n := (if neg then 1 else 0) + max pad m
  signed neg (octLoop neg (n.toNat + 1) (newBuf n, x, n))

/-- The two characters of `_dec_d100[1 + s]`, `base/intfuncs.jl:923-936`: the
tens digit in the low byte, the ones digit in the high byte. -/
def d100lo (s : Nat) : Nat := 48 + s / 10
def d100hi (s : Nat) : Nat := 48 + s % 10

/-- `dec` loop over nine-digit chunks of a value above `typemax(UInt)`,
`base/intfuncs.jl:989-1002`. -/
def decChunkLoop {t : IntTy} : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i > 9 ∧ x.val > IntTy.max .u64 then
      let d := udivLit x 1000000000
      let r := x - d * JInt.lit t 1000000000
      let r32 : Nat := (JInt.rem .u32 r).val.toNat
      let (buf, r32) := (List.range 4).foldl (fun (acc : Buf × Nat) (j : Nat) =>
        let (buf, r32) := acc
        let q := r32 / 100
        let s := r32 % 100
        let buf := store buf (i - 2 * (j : Int)) (d100hi s)
        (store buf (i - 2 * (j : Int) - 1) (d100lo s), q)) (buf, r32)
      decChunkLoop f (store buf (i - 8) (48 + r32 % 256), d, i - 9)
    else (buf, x, i)

/-- `dec` loop over two-digit pairs, `base/intfuncs.jl:1004-1011`. -/
def decPairLoop : Nat → Buf × JInt .u64 × Int → Buf × JInt .u64 × Int
  | 0, s => s
  | f+1, (buf, y, i) =>
    if i ≥ 2 then
      let d := udivLit y 100
      let r := (y - d * JInt.lit .u64 100).val.toNat
      decPairLoop f (store (store buf i (d100hi r)) (i - 1) (d100lo r), d, i - 2)
    else (buf, y, i)

/-- `dec(x::Unsigned, pad, neg)`, `base/intfuncs.jl:983-1018`; the digit count is
`ndigits(x, pad=pad)`, and `pad` is an `Int`. -/
def dec {t : IntTy} (x : JInt t) (pad : JInt .i64) (neg : Bool) : Jl Buf := do
  let nd ← ndigits x (JInt.lit .i64 10) pad
  let n : Int := (if neg then 1 else 0) + nd.val
  let (buf, x, i) := decChunkLoop (n.toNat / 9 + 1) (newBuf n, x, n)
  let y : JInt .u64 := JInt.rem .u64 x
  let (buf, y, i) := decPairLoop (n.toNat / 2 + 1) (buf, y, i)
  let buf := if i > (if neg then 1 else 0) then store buf i (48 + (y.val.toNat % 10) % 256) else buf
  pure (signed neg buf)

/-- A hexadecimal digit character, `d + ifelse(d > 0x9, 0x57, 0x30)`. -/
def hexChar (d : Nat) : Nat := d + if d > 9 then 0x57 else 0x30

/-- `hex` loop, `base/intfuncs.jl:1027-1034`. -/
def hexLoop {t : IntTy} : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i ≥ 2 then
      let b := (JInt.rem .u8 x).val.toNat
      let buf := store buf (i - 1) (hexChar (b / 16))
      let buf := store buf i (hexChar (b % 16))
      hexLoop f (buf, shr x 8, i - 2)
    else (buf, x, i)

/-- `hex(x::Unsigned, pad, neg)`, `base/intfuncs.jl:1020-1042`. -/
def hex {t : IntTy} (x : JInt t) (pad : Int) (neg : Bool) : Buf :=
  let m : Int := (topSetBit x + 3) / 4
  let n := (if neg then 1 else 0) + max pad m
  let (buf, x, i) := hexLoop (n.toNat / 2 + 1) (newBuf n, x, n)
  let buf := if i > (if neg then 1 else 0) then
      store buf i (hexChar (Nat.land (JInt.rem .u8 x).val.toNat 15)) else buf
  signed neg buf

/-- `base36digits` and `base62digits`, `base/intfuncs.jl:1044-1045`, at a zero-based index. -/
def digitChar (big : Bool) (k : Nat) : Nat :=
  if k < 10 then 48 + k
  else if big then (if k < 36 then 65 + (k - 10) else 97 + (k - 36))
  else 97 + (k - 10)

/-- `_base` digit loop, `base/intfuncs.jl:1057-1066`. `rem`/`div`/`mod`/`cld` by
`b` with `abs(b) ≥ 2` are exact after promotion. -/
def baseLoop (b : Int) (big : Bool) (neg : Bool) : Nat → Buf × Int × Int → Buf
  | 0, (buf, _, _) => buf
  | f+1, (buf, x, i) =>
    if i > (if neg then 1 else 0) then
      if b > 0 then baseLoop b big neg f (store buf i (digitChar big (x.tmod b).toNat), x.tdiv b, i - 1)
      else
        -- `cld(x, b) = -fld(x, -b)`
        baseLoop b big neg f (store buf i (digitChar big (x % (-b)).toNat), -(x / (-b)), i - 1)
    else buf

/-- `_base(base, x, pad, neg)`, `base/intfuncs.jl:1047-1070`, for `base::JInt bty`. -/
def base_ {t bty : IntTy} (base : JInt bty) (x : JInt t) (pad : JInt .i64) (neg : Bool) : Jl Buf := do
  if ¬ (x.val ≥ 0 ∨ base.val < 0) then
    .error (.domainError "For negative `x`, `base` must be negative.")
  let ab : JInt bty := if base.val < 0 then -base else base
  if ¬ (2 ≤ ab.val ∧ ab.val ≤ 62) then .error (.domainError "base must satisfy 2 ≤ abs(base) ≤ 62")
  let b : JInt .i64 := JInt.rem .i64 base
  let big := decide (b.val.natAbs > 36)
  let nd ← ndigits x b pad
  let n : Int := (if neg then 1 else 0) + nd.val
  pure (signed neg (baseLoop b.val big neg (n.toNat + 1) (newBuf n, x.val, n)))

/-- `split_sign(n)`, `base/intfuncs.jl:1072-1073`: `unsigned(abs(n))` wraps for `typemin`. -/
def splitSign {t : IntTy} (n : JInt t) : JInt t.toUnsigned × Bool :=
  (JInt.rem t.toUnsigned (if n.val < 0 then -n else n), decide (n.val < 0))

/-- `string(n::Integer; base::Integer, pad::Integer)`, `base/intfuncs.jl:1101-1119`.
The pad is clamped into `Int` (line 1103). -/
def string {t bty : IntTy} (n : JInt t) (base : JInt bty) (pad : Int := 1) : Jl Buf := do
  let pad : JInt .i64 := JInt.wrap .i64 (min (max pad (IntTy.min .i64)) (IntTy.max .i64))
  let (np, neg) := splitSign n
  if base.val = 2 then pure (bin np pad.val neg)
  else if base.val = 8 then pure (oct np pad.val neg)
  else if base.val = 10 then dec np pad neg
  else if base.val = 16 then pure (hex np pad.val neg)
  else if base.val > 0 then base_ base np pad (decide (n.val < 0))
  else do
    -- `convert(Signed, n)`
    let s ← JInt.convert (t.toSigned.name) t.toSigned n.val
    base_ base s pad false

/-- `bitstring(x)` for `x::BitInteger`, `base/intfuncs.jl:1140-1167`: the
widths are multiples of four, so only the four-bit loop runs. -/
def bitstring {t : IntTy} (x : JInt t) : Buf :=
  let (buf, _, _) := binLoop4 (t.bits / 4 + 1) (newBuf t.bits, JInt.rem t.toUnsigned x, (t.bits : Int))
  buf

/-! ### `digits` -/

/-- The power-of-two loop of `digits!`, `base/intfuncs.jl:1260-1262`:
`(n >> (k*(i-1))) & c` for `n ≥ 0`. -/
def pow2Digits (n : Int) (k : Nat) (L : Nat) : List Int :=
  (List.range L).map fun i => (n / 2 ^ (k * i)) % 2 ^ k

/-- The `divrem` loop of `digits!`, `base/intfuncs.jl:1264-1267`; truncated division. -/
def divremDigits (b : Int) : Nat → Int → List Int
  | 0, _ => []
  | L+1, n => n.tmod b :: divremDigits b L (n.tdiv b)

/-- The negative-base loop of `digits!` after its first iteration,
`base/intfuncs.jl:1274-1278`: `n, d = fldmod(n, -base); a[i] = d; n = -n`. -/
def negDigits (b : Int) : Nat → Int → List Int
  | 0, _ => []
  | L+1, n => n % (-b) :: negDigits b L (-(n / (-b)))

/-- `digits!(a, n; base)` for `a::Vector{Int}` of length `L`, `base/intfuncs.jl:1249-1281`.
`abs(base)` wraps for `typemin(Int)`. -/
def digitsFill {t : IntTy} (L : Nat) (n : JInt t) (base : JInt .i64) : Jl (List Int) :=
  let ab := if base.val < 0 then -base else base
  if ¬ 2 ≤ ab.val then .error (.domainError "base must be ≥ 2 or ≤ -2")
  else if L = 0 then pure []
  else if base.val > 0 then
    if ispow2 base ∧ n.val ≥ 0 then pure (pow2Digits n.val (trailingZeros base) L)
    else pure (divremDigits base.val L n.val)
  else
    -- the peeled first iteration: `n, d = fldmod(n, -base); a[1] = d; n = -signed(n)`
    let b := base.val
    pure (n.val % (-b) :: negDigits b (L - 1) (-(n.val / (-b))))

/-- `digits(n; base::Int, pad)`, `base/intfuncs.jl:1207-1212`. -/
def digits {t : IntTy} (n : JInt t) (base : JInt .i64) (pad : JInt .i64 := JInt.lit .i64 1) :
    Jl (List Int) := do
  let L ← ndigits n base pad
  digitsFill L.val.toNat n base

end JuliaLean.ParsePrint.IntPrint

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `clamp(x, lo, hi)` with three Float64 arguments; `base/intfuncs.jl:1461-1464`. -/
def clamp (x lo hi : F64) : F64 :=
  if F64.lt hi x then hi else if F64.lt x lo then lo else x

end JuliaLean.MathFuncs

namespace JuliaLean.ParsePrint.Ryu

def chZero : Nat := 48

/-- The two characters of `_dec_d100[n + 1]` for `0 ≤ n < 100` (`base/intfuncs.jl:923-936`). -/
def d100 (n : Nat) : List Nat := [chZero + n / 10, chZero + n % 10]

/-- `append_c_digits(olength, digits, buf, pos)` (`base/intfuncs.jl:938-952`):
two digits per step from the right from the `_dec_d100` table, then a last
single digit. -/
def cDigits : Nat → Nat → List Nat
  | 0, _ => []
  | 1, d => [chZero + d % 10]
  | n+2, d => cDigits n (d / 100) ++ [chZero + (d % 100) / 10, chZero + d % 10]

end JuliaLean.ParsePrint.Ryu

namespace JuliaLean.Show


/-- `(top_set_bit(x) + 3) ÷ 4`, the number of hex digits of `x` (`0` for `0`);
the fuel `16` covers every `UInt64`. -/
def nibbles : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => if x = 0 then 0 else 1 + nibbles k (x / 16)

/-- `string(x, base = 16, pad = pad)` for an unsigned `x` (`base/intfuncs.jl:1101`,
which calls `hex(x, pad, false)`, `:1020-1042`): the `max(pad, m)` low hex
digits of `x`, most significant first. -/
def hexStr (x pad : Nat) : List UInt8 :=
  (List.range (max pad (nibbles 16 x))).reverse.map (fun i => hexDigit (x / 16 ^ i % 16))

end JuliaLean.Show

namespace JuliaLean.MathCov.Special

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- Number of trailing zero bits of a positive integer. -/
def trailingZeros (p : Nat) : Nat :=
  if h : p = 0 then 0 else if p % 2 = 0 then trailingZeros (p / 2) + 1 else 0
decreasing_by omega

/-- `x = mul(x, x)` repeated `t` times. -/
def squareN {T : FTy} (x : FV T) : Nat → FV T
  | 0 => x
  | t + 1 => squareN (mul x x) t

/-- The `while p > 0` loop of `power_by_squaring`; `base/intfuncs.jl:434-441`. -/
def pbsLoop {T : FTy} : Nat → FV T → FV T → Nat → FV T
  | 0, _, y, _ => y
  | fuel + 1, x, y, p =>
    if p == 0 then y
    else
      let t := trailingZeros p + 1
      let x := squareN x t
      pbsLoop fuel x (mul y x) (p / 2 ^ t)

/-- `power_by_squaring(x, p)` for a float `x` and `p ≥ 0` with `mul = *`;
`base/intfuncs.jl:399-443`. -/
def powerBySquaring {T : FTy} (x : FV T) (p : Nat) : FV T :=
  let xsq := mul x x
  if p == 1 then x
  else if p == 0 then one T
  else if p == 2 then xsq
  else
    let t := trailingZeros p + 1
    let p := p / 2 ^ t
    let x := if t - 1 > 0 then squareN xsq (t - 2) else x
    pbsLoop (p + 1) x x p

/-- `clamp(n, Int32)`. -/
def clamp32 (n : Int) : Int := max (IntTy.min .i32) (min (IntTy.max .i32) n)

end JuliaLean.MathCov.Special

namespace JuliaLean.MathCov.FloatFuncs

/-- `hidigit(x::Integer, base) = ndigits0z(x, base)` for `base ≥ 2`: the number of base-`b`
digits of `x`, zero for `x = 0`; `base/floatfuncs.jl:132`. -/
def ndigitsNat (n b : Nat) : Nat :=
  if h : n = 0 ∨ b < 2 then 0 else 1 + ndigitsNat (n / b) b
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def ndigits0z (x : Int) (b : Nat) : Nat := ndigitsNat x.natAbs b

end JuliaLean.MathCov.FloatFuncs

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- Number of trailing zero bits of a positive natural, with fuel. -/
private def tz : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n % 2 == 1 then 0 else 1 + tz k (n / 2)

/-- Square `x` `t` times. -/
private def squareTimes (x : F64) : Nat → F64
  | 0 => x
  | t + 1 => squareTimes (F64.mul x x) t

/-- The outer `while p > 0` loop of `power_by_squaring`; `base/intfuncs.jl:432-439`. -/
private def pbsLoop : Nat → F64 → F64 → Nat → F64
  | 0, _, y, _ => y
  | k + 1, x, y, p =>
    if p == 0 then y
    else
      let t := tz 64 p + 1
      let x := squareTimes x t
      pbsLoop k x (F64.mul y x) (p >>> t)

/-- `power_by_squaring(x::Float64, p)` for `p ≥ 1` with `mul = *`;
`base/intfuncs.jl:399-443`. -/
def powerBySquaring (x : F64) (p : Nat) : F64 :=
  if p == 1 then x
  else if p == 0 then F64.one
  else if p == 2 then F64.mul x x
  else
    let t := tz 64 p + 1
    let p := p >>> t
    let x := if t - 1 > 0 then squareTimes (F64.mul x x) (t - 2) else x
    pbsLoop 64 x x p

/-- `prevpow(a::Float32, x::Float64)`: `log(a, x)` promotes to Float64 and is
`log(x)/log(a)` (`base/math.jl:259,304`); `floor(Integer, v)` is `floor(Int, v)`
(`base/float.jl:456`); comparisons promote Float32 to Float64 (`base/float.jl:479,617`);
`hastypemax(Float32)` holds with `typemax(Float32) == Inf32`; `base/intfuncs.jl:694-713`. -/
def prevpow32 (log : F64 → Jl F64) (pow32I : F32 → Int → F32)
    (a : F32) (x : F64) : Jl F32 := do
  let af := ofF32 a
  if F64.lt x F64.one then throw (.domainError "prevpow")
  if F64.le af F64.one then throw (.domainError "prevpow")
  let lx ← log x
  let la ← log af
  let n ← F64.floorInt .i64 (F64.div lx la)
  let p := pow32I a n.val
  if F64.lt F64.inf x then throw (.domainError "prevpow")
  let wp := pow32I a (n.val + 1)
  if F64.le (ofF32 wp) x then return wp
  if F64.le (ofF32 p) x then return p
  return pow32I a (n.val - 1)

end JuliaLean.MathFuncs
