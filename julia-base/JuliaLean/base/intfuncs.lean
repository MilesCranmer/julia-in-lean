import JuliaLean.base.int
import JuliaLean.base.operators
import JuliaLean.base.checked
import JuliaLean.base.float
import JuliaLean.base.multinverses
import JuliaLean.base.arraymath
import JuliaLean.base.reduce

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

private def repeatM {S : Type} (n : Nat) (step : S → Jl S) (s : S) : Jl S :=
  (List.range n).foldlM (fun s _ => step s) s

private def magnitude {I : Type} (o : IntegerOps I) (x : I) : Nat := (o.value x).natAbs

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
  let length ← JInt.convert .u64 n
  pure ⟨List.replicate length.val.toNat 0, [], []⟩
def store (b : Buffer) (i : Int) (v : Nat) : Buffer :=
  { b with bytes := b.bytes.set (i - 1).toNat (v % 256), writes := b.writes ++ [i] }
def readTable (b : Buffer) (index : Int) (size : Nat) : Buffer :=
  { b with tableReads := b.tableReads ++ [(index, size)] }
private def minusSign (neg : Bool) (b : Buffer) : Buffer := if neg then store b 1 45 else b
private def boolInt (b : Bool) : Int := if b then 1 else 0

def topBit {t : IntTy} (x : JInt t) : Nat :=
  t.bits - (JuliaLean.base.int.ctlz_int x).val.toNat

def minBits {t : IntTy} (a b : JInt t) : JInt t :=
  JuliaLean.base.operators.min JuliaLean.base.int.ltSame JuliaLean.base.int.ifelse a b

def maxBits {t : IntTy} (a b : JInt t) : JInt t :=
  JuliaLean.base.operators.max JuliaLean.base.int.ltSame JuliaLean.base.int.ifelse a b

def unsignedAbs {t : IntTy} (x : JInt t) : JInt t.toUnsigned := JuliaLean.base.int.unsigned (JuliaLean.base.int.abs x)

private def gcdEuclidLoop {I : Type} (o : IntegerOps I) : Nat → I → I → Jl (I × I)
  | 0, a, b => pure (a, b)
  | n + 1, a, b => do
      if o.value b = 0 then pure (a, b) else
        let t := b
        let b ← o.rem a b
        gcdEuclidLoop o n t b

private def powerSquares {A : Type} (mul : A → A → Jl A) (n : Nat) (x : A) : Jl A :=
  repeatM n (fun x => mul x x) x

private def powerLoop {A E : Type} (eo : IntegerOps E) (mul : A → A → Jl A) :
    Nat → A → A → E → Jl A
  | 0, _, y, _ => pure y
  | n + 1, x, y, p => do
      if eo.value p ≤ 0 then pure y else
        let t := eo.trailingZeros p + 1
        let p := eo.shiftRight p t
        let x ← powerSquares mul t x
        let y ← mul y x
        powerLoop eo mul n x y p

private def powermodLoop {P U : Type} (po : IntegerOps P) (value : U → Int)
    (mulmod : U → U → Jl U) : Nat → P → U → U → Jl U
  | 0, _, rr, _ => pure rr
  | n + 1, p, rr, bb => do
      let rr ← if po.value p % 2 ≠ 0 then mulmod rr bb else pure rr
      let p := po.shiftRight p 1
      if po.value p = 0 then pure rr else
        let bb ← mulmod bb bb
        powermodLoop po value mulmod n p rr bb

private def digitChar (large : Bool) (k : Nat) : Jl Nat :=
  match (if large then base62Digits else base36Digits)[k]? with
  | some ch => pure ch
  | none => .error .boundsError

private def hexChar (d : Nat) : Nat := d + if d > 9 then 87 else 48

private def binLoop4 {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) :
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

private def binLoop1 {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) (neg : Bool) :
    Nat → Buffer → U → Int → Buffer
  | 0, b, _, _ => b
  | n + 1, b, x, i =>
      if i ≤ boolInt neg then b else
        binLoop1 lowByte shr neg n (store b i (48 + lowByte x % 2)) (shr x 1) (i - 1)

private def octLoop {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) (neg : Bool) :
    Nat → Buffer → U → Int → Buffer
  | 0, b, _, _ => b
  | n + 1, b, x, i =>
      if i ≤ boolInt neg then b else
        octLoop lowByte shr neg n (store b i (48 + lowByte x % 8)) (shr x 3) (i - 1)

private def hexLoop {U : Type} (lowByte : U → Nat) (shr : U → Nat → U) :
    Nat → Buffer → U → Int → Buffer × U × Int
  | 0, b, x, i => (b, x, i)
  | n + 1, b, x, i =>
      if i < 2 then (b, x, i) else
        let byte := lowByte x % 256
        let b := store b (i - 1) (hexChar (byte / 16))
        let b := store b i (hexChar (byte % 16))
        hexLoop lowByte shr n b (shr x 8) (i - 2)

private def decimalPair (d : Nat) : Jl Nat :=
  match decimalPairs[d]? with
  | some pair => pure pair.val.toNat
  | none => .error .boundsError

private def appendLoop {U : Type} (value : U → Int) (divrem : U → Nat → Jl (U × Nat)) :
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

private def baseLoop {I : Type} (o : IntegerOps I) (divrem : I → Int → Jl (I × Int))
    (mod : I → Int → Jl Int) (cld : I → Int → Jl I) (base : Int) (large neg : Bool) :
    Nat → I → Int → Buffer → Jl Buffer
  | 0, _, _, b => pure b
  | n + 1, x, i, b => do
      if i ≤ boolInt neg then pure b else
        if 0 < base then
          let (q, r) ← divrem x base
          let b := readTable b (r + 1) (if large then 62 else 36)
          let ch ← digitChar large r.toNat
          baseLoop o divrem mod cld base large neg n q (i - 1) (store b i ch)
        else
          let r ← mod x (-base)
          let q ← cld x base
          let b := readTable b (r + 1) (if large then 62 else 36)
          let ch ← digitChar large r.toNat
          baseLoop o divrem mod cld base large neg n q (i - 1) (store b i ch)

structure Vector (A : Type) where
  first : Int := 1
  values : List A
  writes : List Int := []

def vectorStore {A : Type} (a : Vector A) (i : Int) (x : A) : Vector A :=
  { a with values := a.values.set (i - a.first).toNat x, writes := a.writes ++ [i] }

private def factorialLoop {I F : Type} (value : I → Int) (ofInt : Int → Jl F)
    (mul : F → F → Jl F) (n : I) (f : F) : Jl F :=
  (List.range ((value n - 1).toNat)).foldlM (fun f (j : Nat) => do
    let i ← ofInt ((j : Int) + 2)
    mul f i) f

private def binomialLoop {I : Type} (o : IntegerOps I) (wideDiv : I → I → I → Jl Int) :
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

private def binaryGcdLoop {t : IntTy} : Nat → JInt t → JInt t → Nat → JInt t
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

private def gcdxLoop {I : Type} (o : IntegerOps I) : Nat → I → I → I → I → I → I →
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
    (convertSquare : S → Jl T) (copy : T → T) (one : T → T) (neg : T → T)
    (isone : T → Bool) (mul : T → T → Jl T) (squareUseful : Bool)
    (x_ : A) (p : E) : Jl T := do
  let xSquared ← square x_ x_
  let x ← if isNumber then convertNumber x_ else convertOther x_
  if eo.value p = 1 then pure (copy x)
  else if eo.value p = 0 then pure (one x)
  else if eo.value p = 2 then
    if squareUseful then convertSquare xSquared else mul x x
  else if eo.value p < 0 then
    if isone x then pure (copy x)
    else if isone (neg x) then pure (if eo.value p % 2 = 0 then one x else copy x)
    else throwPowerDomain_Any x p
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
def topSetBit_Integer {I : Type} (iszero : I → Bool) (exponent : I → Jl Int) (x : I) : Jl Int :=
  if iszero x then pure 0 else do pure ((← exponent x) + 1)

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
    (divrem : I → Int → Jl (I × Int)) (mod : I → Int → Jl Int) (cld : I → Int → Jl I)
    (ndigits : I → JInt64 → JInt64 → Jl JInt64)
    (base : B) (x : I) (pad : JInt64) (neg : Bool) : Jl Buffer := do
  if ¬ (o.value x ≥ 0 ∨ bo.value base < 0) then .error (.domainError "")
  else if ¬ (2 ≤ bo.value (bo.abs base) ∧ bo.value (bo.abs base) ≤ 62) then .error (.domainError "") else
    let b := remInt base
    let large := decide (b.val.natAbs > 36)
    let n := wrapInt .i64 (boolInt neg + (← ndigits x b pad).val)
    let str ← newBuffer n
    pure (minusSign neg (← baseLoop o divrem mod cld b.val large neg (n.toNat + 1) x n str))

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
    let s := JuliaLean.base.int.ashr_int (JuliaLean.base.int.add s (← div x s)) (JuliaLean.base.int.lit .i64 1)
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
def clampBang {A Axis Index V L H : Type}
    (index : JuliaLean.base.arraymath.ArrayIndexOps Id A Axis)
    (eachindex : JuliaLean.base.arraymath.ArrayIndexOps Id A Axis → A → Jl (List Index))
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
    (fun _ => JuliaLean.base.int.lit t 1) JuliaLean.base.int.neg
    (fun x => decide (x.val = 1)) (fun x y => pure (JuliaLean.base.int.mul x y)) true x p

def powerBig (x p : Int) : Jl Int :=
  powerBySquaring bigOps (fun x y => pure (x * y)) true pure pure pure id
    (fun _ => 1) Int.neg (fun x => decide (x = 1)) (fun x y => pure (x * y)) true x p

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
      (fun _ => JuliaLean.base.int.lit _ 1) JuliaLean.base.int.neg
      (fun x => decide (x.val = 1)) (fun a b => pure (JuliaLean.base.int.mul a b)) true a n).map Subtype.val)
    (fun _ => hasTypeMax true true) (fun x _ => decide (x.val > a.max))
    (fun p x => decide (p ≥ x.val)) (fun p q => decide (p > q)) base input

def prevpowBits {a x : IntTy} (floorLog : JInt a → JInt x → Jl Int)
    (base : JInt a) (input : JInt x) : Jl Int :=
  prevpow (fun x => decide (x.val < 1)) (fun a => decide (a.val = 2)) true
    (fun x => pure (prevpow2Bits x).val) (fun a => decide (a.val ≤ 1)) floorLog
    (fun a n => (powerBySquaring bigOps
      (fun a b => pure (JuliaLean.base.int.mul a b)) true pure pure pure id
      (fun _ => JuliaLean.base.int.lit _ 1) JuliaLean.base.int.neg
      (fun x => decide (x.val = 1)) (fun a b => pure (JuliaLean.base.int.mul a b)) true a n).map Subtype.val)
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
    (fun x b => if b = 0 then .error .divideError
      else pure (JuliaLean.base.int.lit t (x.val.tdiv b), x.val.tmod b))
    (fun x b => if b = 0 then .error .divideError else pure (x.val % b))
    (fun x b => if b = 0 then .error .divideError else pure (JuliaLean.base.int.lit t (-(x.val / (-b)))))
    (fun x base pad => do pure (JuliaLean.base.int.lit .i64 (← ndigitsBits c x base pad)))
    base x pad neg

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
    (JInt.convert e) a n base

def zerosVector {T : Type} (zero : T) (length : Int) : Jl (Vector T) := do
  let length ← JInt.convert .i64 length
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
  factorial_Integer Subtype.val (JInt.convert t) (fun x y => pure (JuliaLean.base.int.mul x y)) n

def clampBits {t : IntTy} (x lo hi : JInt t) : Jl (JInt t) :=
  clamp (fun x hi => decide (x.val > hi.val)) (fun x lo => decide (x.val < lo.val)) pure pure pure x lo hi

/-! Callees from `base/int.jl`, `base/div.jl`, `base/gmp.jl`, and `base/multinverses.jl`. -/
structure NumberCallees where
  mixedMod : {s t : IntTy} → JInt s → JInt t → Jl Int
  gmpGcdx : Int → Int → Jl (Int × Int × Int)
  gmpPowermod : Int → Int → Int → Jl Int

def inverseForBits {t : IntTy} (d : JInt t) :
    Jl (JuliaLean.base.multinverses.MultiplicativeInverse t) :=
  if h : t.signed = true then
    (JuliaLean.base.multinverses.multiplicativeinverseSigned h
      JuliaLean.base.int.remSame divremBits d).map .signed
  else
    (JuliaLean.base.multinverses.multiplicativeinverseUnsigned
      (by cases t <;> simp_all [IntTy.signed]) JuliaLean.base.int.remSame divremBits d).map .unsigned

def magicModBits {t : IntTy} (a b : JInt t) (mis : JuliaLean.base.multinverses.MultiplicativeInverse t) :
    Jl (JInt t) :=
  match mis with
  | .signed inverse => pure (JuliaLean.base.multinverses.modSignedInverse (JuliaLean.base.int.mul a b) inverse)
  | .unsigned inverse => pure (JuliaLean.base.multinverses.modUnsignedInverse (JuliaLean.base.int.mul a b) inverse)


private def workValue (t : Option IntTy) (n : Int) : Int :=
  match t with
  | some t => (JuliaLean.base.int.lit t n).val
  | none => n

private def bezoutWork (c : NumberCallees) (t : Option IntTy) (n m : Int) : Jl Int :=
  match t with
  | some t =>
      (bezoutCoef gcdxBits (fun g => decide (g.val = 1))
        (JuliaLean.base.int.lit t n) (JuliaLean.base.int.lit t m)).map Subtype.val
  | none => bezoutCoef c.gmpGcdx (fun g => decide (g = 1)) n m

private def workMod (c : NumberCallees) (t : Option IntTy) (a b : Int) : Jl Int :=
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
    powermod_128 Subtype.val c.gmpPowermod (JInt.convert t) x.val p.val m
  else
    powermod_Integer (bitsOps t) (bitsOps e) Subtype.val
      (fun _ => JuliaLean.base.int.lit t.toUnsigned 1)
      (fun _ => JuliaLean.base.int.lit t.toUnsigned 0) JuliaLean.base.float.uabs
      (fun a b => do JInt.convert t (← c.mixedMod a b))
      (fun a mm => do JInt.convert t.toUnsigned (← c.mixedMod a mm))
      (fun a mm => if mm.val = 0 then .error .divideError
        else pure (JuliaLean.base.int.lit t.toUnsigned (a % mm.val)))
      (fun a => JInt.convert t a.val)
      (fun a b m => do JInt.convert t (← workMod c (JuliaLean.base.int.widenType t) (a.val * b.val) m.val))
      (fun a b m => do JInt.convert t (← workMod c (JuliaLean.base.int.widenType t) (a.val * b) m.val))
      (fun a b mm => do
        let productMod ← workMod c (JuliaLean.base.int.widenType t.toUnsigned) (a.val * b.val) mm.val
        JInt.convert t.toUnsigned productMod)
      (invmodBits c)
      (powermodMILegal_Unsigned (hasTypeMax true true) (JuliaLean.base.int.lit t.toUnsigned t.toUnsigned.max)
        (fun a b => decide (a.val ≤ b.val))
        (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) (t.bits / 8))
      (fun _ => t.bits / 8) inverseForBits magicModBits x p m

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
    pure pure pure id (fun _ => JuliaLean.base.float.one_float T) JuliaLean.base.float.neg_IEEEFloat
    (fun x => JuliaLean.base.float.eq_IEEEFloat x (JuliaLean.base.float.one_float T))
    (fun x y => pure (JuliaLean.base.float.mul_IEEEFloat x y)) true x p

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
