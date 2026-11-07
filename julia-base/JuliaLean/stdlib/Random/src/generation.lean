import JuliaLean.stdlib.Random.src.Random
import JuliaLean.Runtime.Float
import JuliaLean.base.range
import JuliaLean.base.strings.string

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

/-- `empty_collection_error()`, `generation.jl:244`. -/
def emptyCollectionError : JlError := .argumentError "collection must be non-empty"

/-- `uint_sup(T)`, `generation.jl:240-242`. -/
def uintSup : IntTy → IntTy
  | .i8 | .u8 | .i16 | .u16 | .i32 | .u32 => .u32
  | .i64 | .u64 => .u64
  | .i128 | .u128 => .u128

/-- `SamplerRangeNDL{U,T}`, `generation.jl:374-377`: first element and range length
(zero for the full range of `U`). -/
structure NDL (t : IntTy) where
  a : JInt t
  s : JInt (uintSup t)
  deriving DecidableEq

/-- `SamplerRangeNDL(a:b)`, `generation.jl:379-387`. `b` is the normalized `last(r)`. -/
def ndlSampler {t : IntTy} (a b : JInt t) : Jl (NDL t) :=
  if b.val < a.val then .error emptyCollectionError
  else .ok ⟨a, JInt.rem (uintSup t) (JInt.rem t.toUnsigned (b - a)) + JInt.lit (uintSup t) 1⟩

/-- The `while (m % U) < t` loop of `rand_unlikely`, `generation.jl:400-407`. `m` is the
widened product `widen(x) * s`, exact because both factors are below `2^bits(U)`. -/
def ndlUnlikelyLoop {σ : Type} (g : Rng σ) (u : IntTy) (s thr : Nat) :
    Nat → σ → Nat → Option (Nat × σ)
  | 0, st, m => if m % 2 ^ u.bits < thr then none else some (m / 2 ^ u.bits, st)
  | f + 1, st, m =>
    if m % 2 ^ u.bits < thr then
      let p := g.next st (.int u)
      let x : JInt u := p.1
      ndlUnlikelyLoop g u s thr f p.2 (x.val.toNat * s)
    else some (m / 2 ^ u.bits, st)

/-- `rand(rng, sp::SamplerRangeNDL)`, `generation.jl:389-397`, with `rand_unlikely`
(`:400-407`). `m >> (8*sizeof(U))` is division by `2^bits(U)`. -/
def ndlRand {σ : Type} {t : IntTy} (g : Rng σ) (sp : NDL t) (fuel : Nat) (st : σ) :
    Run σ (JInt t) :=
  let u := uintSup t
  let p := g.next st (.int u)
  let x : JInt u := p.1
  let s := sp.s.val.toNat
  let m := x.val.toNat * s
  let r : Run σ (JInt t) :=
    if m % 2 ^ u.bits < s then
      match JInt.mod (-sp.s) sp.s with
      | .error e => some (.error e)
      | .ok thr =>
        (ndlUnlikelyLoop g u s thr.val.toNat fuel p.2 m).map fun q =>
          .ok (JInt.rem t (JInt.wrap u q.1), q.2)
    else if s = 0 then some (.ok (JInt.rem t x, p.2))
    else some (.ok (JInt.wrap t ((m / 2 ^ u.bits : Nat) : Int), p.2))
  r.map fun res => res.map fun q => (q.1 + sp.a, q.2)

/-- `rand(rng, lo:hi)` for `Int` bounds, through `Sampler` (`generation.jl:232-233`). -/
def randRange {σ : Type} (g : Rng σ) (fuel : Nat) (lo hi : JInt64) (st : σ) : Run σ JInt64 :=
  match ndlSampler lo hi with
  | .error e => some (.error e)
  | .ok sp => ndlRand g sp fuel st

/-- `rand(rng, 1:h)` as drawn by `randperm!`, `randcycle!` and `shuffle!`. -/
def randIndex {σ : Type} (g : Rng σ) (fuel h : Nat) (st : σ) : Run σ JInt64 :=
  randRange g fuel (JInt.lit .i64 1) (JInt.lit .i64 h) st

/-- `SamplerRangeFast{UInt128,T}`, `generation.jl:249-254`. -/
structure Fast (t : IntTy) where
  a : JInt t
  bw : Nat
  m : JInt .u128
  mask : JInt .u128
  deriving DecidableEq

/-- `SamplerRangeFast(a:b, UInt128)`, `generation.jl:256-265`. `(1 % U) << bw` is
`2^bw` reduced modulo `2^128` (zero for `bw = 128`). -/
def fastSampler {t : IntTy} (a b : JInt t) : Jl (Fast t) :=
  if b.val < a.val then .error emptyCollectionError
  else
    let m := JInt.rem .u128 (JInt.rem t.toUnsigned (b - a))
    let bw := topSetBit m.val.toNat
    let mask := JInt.wrap .u128 (2 ^ bw) - JInt.lit .u128 1
    .ok ⟨a, bw, m, mask⟩

/-- The word type `rand(rng, sp::SamplerRangeFast{UInt128})` draws when
`has_fast_64(rng)`: `UInt64` for `bw <= 64`, else `UInt128`; `generation.jl:289-292`. -/
def fastWord (bw : Nat) : IntTy := if bw ≤ 64 then .u64 else .u128

/-- `rand(rng, sp::SamplerRangeFast{UInt128,T})` with `has_fast_64(rng)`,
`generation.jl:287-301`. Both branches are written through the word type `U = fastWord bw`:
for `bw <= 64` this is `rand(rng, LessThan(m % UInt64, Masked(mask % UInt64, uniform(UInt64)))) % UInt128`
(line 291); for `bw > 64` the conversions `% UInt128` are identities and it is line 292. -/
def fastRand {σ : Type} {t : IntTy} (g : Rng σ) (sp : Fast t) (fuel : Nat) (st : σ) :
    Run σ (JInt t) :=
  let u := fastWord sp.bw
  let r : Option (JInt .u128 × σ) :=
    (lessThanMasked g u (JInt.rem u sp.m) (JInt.rem u sp.mask) fuel st).map
      fun q => (JInt.rem .u128 q.1, q.2)
  r.map fun q => .ok (JInt.rem t q.1 + sp.a, q.2)

/-- `Sampler(RNG, r::AbstractArray)` for a `StepRange{Int,Int}`, `generation.jl:469-470`:
an NDL sampler over `firstindex(r):lastindex(r)`, i.e. `1:length(r)` (`base/range.jl:864`).
Lengths of `Int` ranges are `Int` (`base/range.jl:820-829`), so the conversion is exact. -/
def stepRangeSampler (r : Ranges.Rng) : Jl (NDL .i64) := do
  let n ← Ranges.length r
  ndlSampler (JInt.lit .i64 1) (JInt.wrap .i64 n.val)

/-- `Sampler(RNG, str::String, Val(1))`, `generation.jl:545-546,550`: positions `1:sizeof(s)`. -/
def stringSampler (s : Strings.JStr) : Jl (NDL .i64) :=
  ndlSampler (JInt.lit .i64 1) (Strings.ncodeunits s)

/-- `isvalid_unsafe(s::String, i)`, `generation.jl:548`: the byte is not a continuation byte. -/
def isvalidUnsafe (s : Strings.JStr) (i : JInt64) : Bool := !Strings.isCont (Strings.cu s i)

/-- The rejection loop of `rand(rng, sp::SamplerSimple{<:AbstractString})`,
`generation.jl:553-559`; returns the accepted position (Julia returns `str[pos]`). -/
def randStringPos {σ : Type} (g : Rng σ) (sp : NDL .i64) (s : Strings.JStr) (fuel : Nat) :
    Nat → σ → Run σ JInt64
  | 0, _ => none
  | k + 1, st =>
    match ndlRand g sp fuel st with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (pos, st')) =>
      if isvalidUnsafe s pos then some (.ok (pos, st')) else randStringPos g sp s fuel k st'

/-- `rand(r, ::SamplerType{Char})`, `generation.jl:177-180`, as a code point:
`c = rand(r, 0x00000000:0x0010f7ff); c < 0xd800 ? c : c + 0x800`. -/
def randCharCode {σ : Type} (g : Rng σ) (fuel : Nat) (st : σ) : Run σ Nat :=
  match ndlSampler (JInt.lit .u32 0) (JInt.lit .u32 0x10f7ff) with
  | .error e => some (.error e)
  | .ok sp =>
    (ndlRand g sp fuel st).map fun res => res.map fun q =>
      (if q.1.val < 0xd800 then q.1.val.toNat else (q.1 + JInt.lit .u32 0x800).val.toNat, q.2)

/-- `rand(r, SamplerTrivial{CloseOpen01_64})`, `generation.jl:32-35,114-125`:
`reinterpret(Float64, 0x3ff0000000000000 | rand(r, UInt52())) - 1.0` with
`rand(r, UInt52()) = rand(r, UInt52Raw()) & 0x000fffffffffffff`. -/
def randFloat64 {σ : Type} (g : Rng σ) (st : σ) : F64 × σ :=
  let p := g.next st .raw52
  let w : JInt .u64 := p.1
  (F64.sub (F64.ofBits (0x3ff0000000000000 ||| (w.val.toNat &&& 0x000fffffffffffff))) F64.one,
   p.2)

end JuliaLean.RandomSampling
