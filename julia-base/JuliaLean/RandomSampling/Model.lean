import JuliaLean.Core
import JuliaLean.Float.Basic
import JuliaLean.Float.Extras
import JuliaLean.MathFuncs.Log
import JuliaLean.MathFuncs.Exp
import JuliaLean.Ranges.Ordinal
import JuliaLean.Strings.Basic
import JuliaLean.RandomSampling.Tables

/-!
# Model of `stdlib/Random/src` sampling code

Mirrors the RNG-independent sampling functions of `stdlib/Random/src/generation.jl`,
`misc.jl` and `normal.jl` at master `bbfa0ce4150` (unchanged in 1.13.2 for every
modelled function).

* The RNG is an arbitrary state machine `Rng σ`: each call `rand(rng, U)` for a
  `BitInteger` type `U`, and each `rand(rng, UInt52Raw())`, returns some value of
  that type and a new state. Every property quantifies over all such machines, so
  it holds for every RNG and every stream of words.
* RNGs whose `rng_native_52` is `UInt64` (`Xoshiro`, `TaskLocalRNG`, `RandomDevice`)
  are modelled where the sampling code branches on it (`has_fast_64`, the 128-bit
  range sampler). `MersenneTwister`'s `Float64`-native branches are not modelled.
* `rand(rng)` (`Float64` in `[0, 1)`) is the generic method of
  `generation.jl:32-35`; RNG types that override it (`Xoshiro`) are RNG cores and
  out of scope.
* Julia's `while true` rejection loops never stop when every word is rejected.
  Each loop takes a `fuel` bound; `none` means the bound ran out (Julia keeps drawing).
  `Run σ α` is the result: `none`, a Julia exception, or a value and the new state.
-/

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

/-- A request the sampling code makes of the RNG: `rand(rng, U)` for a `BitInteger`
type `U`, or `rand(rng, UInt52Raw())` (`Random.jl:64-65`, a `UInt64`). -/
inductive Req where
  | int (u : IntTy)
  | raw52

/-- The Julia type of the answer to a request. -/
def Req.Out : Req → Type
  | .int u => JInt u
  | .raw52 => JInt .u64

/-- An arbitrary RNG: a state machine answering requests. -/
structure Rng (σ : Type) where
  next : σ → (q : Req) → q.Out × σ

/-- State after answering `i` identical requests `q` starting from `st`. -/
def Rng.stateAfter {σ : Type} (g : Rng σ) (q : Req) (st : σ) : Nat → σ
  | 0 => st
  | i + 1 => (g.next (g.stateAfter q st i) q).2

/-- The `i`-th answer (from zero) to repeated requests `q` starting from `st`. -/
def Rng.wordAt {σ : Type} (g : Rng σ) (q : Req) (st : σ) (i : Nat) : q.Out :=
  (g.next (g.stateAfter q st i) q).1

/-- Outcome of a call that consumes random words (see the module docstring). -/
abbrev Run (σ α : Type) := Option (Jl (α × σ))

/-- `empty_collection_error()`, `generation.jl:244`. -/
def emptyCollectionError : JlError := .argumentError "collection must be non-empty"

/-- Number of `x < n` with `p x`. -/
def countBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countBelow p n + (if p n then 1 else 0)

/-! ## Unit ranges of `BitInteger` types up to 64 bits: `SamplerRangeNDL` -/

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

/-- Rejection-sampling view of `ndlRand`: the value one word `x` yields, or `none` when
the word is rejected. Not Julia code; `NdlUniform` proves `ndlRand` returns the value
of the first word this accepts. -/
def ndlStep {t : IntTy} (sp : NDL t) (x : JInt (uintSup t)) : Option (JInt t) :=
  let N := 2 ^ (uintSup t).bits
  let s := sp.s.val.toNat
  let m := x.val.toNat * s
  if s = 0 then some (JInt.rem t x + sp.a)
  else if m % N < (N - s) % s then none
  else some (JInt.wrap t ((m / N : Nat) : Int) + sp.a)

/-- `rand(rng, lo:hi)` for `Int` bounds, through `Sampler` (`generation.jl:232-233`). -/
def randRange {σ : Type} (g : Rng σ) (fuel : Nat) (lo hi : JInt64) (st : σ) : Run σ JInt64 :=
  match ndlSampler lo hi with
  | .error e => some (.error e)
  | .ok sp => ndlRand g sp fuel st

/-- `rand(rng, 1:h)` as drawn by `randperm!`, `randcycle!` and `shuffle!`. -/
def randIndex {σ : Type} (g : Rng σ) (fuel h : Nat) (st : σ) : Run σ JInt64 :=
  randRange g fuel (JInt.lit .i64 1) (JInt.lit .i64 h) st

/-! ## 128-bit unit ranges: `SamplerRangeFast` -/

/-- `Base.top_set_bit(x)`, `base/int.jl`: the number of significant bits. -/
def topSetBit (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

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

/-- `x & mask` on an unsigned type. -/
def band {u : IntTy} (x y : JInt u) : JInt u := JInt.wrap u (x.val.toNat &&& y.val.toNat)

/-- `rand(rng, LessThan(sup, Masked(mask, uniform(U))))`, `Random.jl:231-243`. -/
def lessThanMasked {σ : Type} (g : Rng σ) (u : IntTy) (sup mask : JInt u) :
    Nat → σ → Option (JInt u × σ)
  | fuel, st =>
    let p := g.next st (.int u)
    let w : JInt u := p.1
    let x := band w mask
    if x.val ≤ sup.val then some (x, p.2)
    else match fuel with
      | 0 => none
      | f + 1 => lessThanMasked g u sup mask f p.2

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

/-- Rejection-sampling view of `fastRand` for one word of type `fastWord sp.bw`. -/
def fastStep {t : IntTy} (sp : Fast t) (w : JInt (fastWord sp.bw)) : Option (JInt t) :=
  let x := w.val.toNat % 2 ^ sp.bw
  if x ≤ sp.m.val.toNat then some (JInt.wrap t x + sp.a) else none

/-! ## Arrays, strings and `StepRange`s -/

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

/-- The `UInt8` path of `randstring(r, chars, n)`, `misc.jl:73-78`: `n` bytes, each
`chars[rand(r, 1:length(chars))]` through one `Val(Inf)` array sampler
(`generation.jl:469-473`). -/
def randstringBytes {σ : Type} (g : Rng σ) (fuel : Nat) (chars : List UInt8) (n : Nat)
    (st : σ) : Run σ (List UInt8) :=
  match ndlSampler (JInt.lit .i64 1) (JInt.lit .i64 chars.length) with
  | .error e => some (.error e)
  | .ok sp =>
    let rec go : Nat → σ → List UInt8 → Run σ (List UInt8)
      | 0, st, acc => some (.ok (acc, st))
      | k + 1, st, acc =>
        match ndlRand g sp fuel st with
        | none => none
        | some (.error e) => some (.error e)
        | some (.ok (i, st')) => go k st' (acc ++ [chars.getD (i.val.toNat - 1) 0])
    go n st []

/-! ## `randperm!`, `randcycle!`, `shuffle!` -/

/-- `a[k] = v` on a one-based array represented as a function. -/
def update (a : Nat → Int) (k : Nat) (v : Int) : Nat → Int := fun x => if x = k then v else a x

/-- The loop `for i = 2:n; j = rand(rng, 1:hi(i)); body; end` shared by `randperm!`,
`randcycle!` and `shuffle!`; `k` iterations remain and the next index is `i`. `draw h` is
`rand(rng, 1:h)` (`randIndex`); it is a parameter so that unfolding the loop never
evaluates the `Int64` literals of the range. -/
def permLoop {σ : Type} (draw : Nat → σ → Run σ JInt64) (hi : Nat → Nat)
    (body : Nat → Nat → (Nat → Int) → (Nat → Int)) :
    Nat → Nat → (Nat → Int) → σ → Run σ (Nat → Int)
  | 0, _, a, st => some (.ok (a, st))
  | k + 1, i, a, st =>
    match draw (hi i) st with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (j, st')) => permLoop draw hi body k (i + 1) (body i j.val.toNat a) st'

/-- Loop body of `randperm!`, `misc.jl:355-359`. -/
def randpermBody (i j : Nat) (a : Nat → Int) : Nat → Int :=
  if i ≠ j then update (update a i (a j)) j i else update a j i

/-- Loop body of `randcycle!` (Sattolo), `misc.jl:437-439`. -/
def randcycleBody (i j : Nat) (a : Nat → Int) : Nat → Int := update (update a i (a j)) j i

/-- Loop body of `shuffle!`, `misc.jl:240-241`: `a[i], a[j] = a[j], a[i]`. -/
def shuffleBody (i j : Nat) (a : Nat → Int) : Nat → Int := update (update a i (a j)) j (a i)

/-- The `#undef` contents of `Vector{Int}(undef, n)`; never read by the modelled code. -/
def undefArray : Nat → Int := fun _ => 0

/-- `randperm(r, n::Int) = randperm!(r, Vector{Int}(undef, n))`, `misc.jl:322,348-362`. -/
def randperm {σ : Type} (g : Rng σ) (fuel n : Nat) (st : σ) : Run σ (Nat → Int) :=
  if n = 0 then some (.ok (undefArray, st))
  else permLoop (randIndex g fuel) id randpermBody (n - 1) 2 (update undefArray 1 1) st

/-- `randcycle(r, n::Int)`, `misc.jl:398,429-442`. -/
def randcycle {σ : Type} (g : Rng σ) (fuel n : Nat) (st : σ) : Run σ (Nat → Int) :=
  if n = 0 then some (.ok (undefArray, st))
  else permLoop (randIndex g fuel) (fun i => i - 1) randcycleBody (n - 1) 2 (update undefArray 1 1) st

/-- `shuffle!(r, a)` for a length-`n` `Vector{Int}` `a`, `misc.jl:236-244`. -/
def shuffle {σ : Type} (g : Rng σ) (fuel n : Nat) (a : Nat → Int) (st : σ) : Run σ (Nat → Int) :=
  permLoop (randIndex g fuel) id shuffleBody (n - 1) 2 a st

/-- `a` restricted to `1..n` is a permutation of `1..n`. -/
def IsPerm (n : Nat) (a : Nat → Int) : Prop :=
  (∀ k, 1 ≤ k → k ≤ n → 1 ≤ a k ∧ a k ≤ n) ∧
  (∀ k l, 1 ≤ k → k ≤ n → 1 ≤ l → l ≤ n → a k = a l → k = l)

/-- `m` applications of the permutation `k ↦ a[k]` to `x`. -/
def iterPerm (a : Nat → Int) : Nat → Nat → Nat
  | 0, x => x
  | m + 1, x => (a (iterPerm a m x)).toNat

/-! ## Characters and floats -/

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

/-! ## `randexp` and `randsubseq` -/

/-- `y <= x` for `y::Int64`, `x::Float64` (Julia's `x >= y`), `base/float.jl:649-664`:
`fy = Float64(y); (fy < x) | ((fy == x) & ((fy == Float64(typemax(Int))) | (y <= unsafe_trunc(Int, fy))))`.
`unsafe_trunc` is only reached for finite `fy`, where it is exact truncation. -/
def intLeF64 (y : JInt64) (x : F64) : Bool :=
  let fy := F64.ofInt y.val
  let q := F64.toRat fy
  F64.lt fy x || (F64.eq fy x &&
    (F64.eq fy (F64.ofInt (2 ^ 63 - 1)) || decide (y.val ≤ q.1.tdiv (q.2 : Int))))

/-- `randexp(rng)`, `normal.jl:153-173`: `_randexp` and `randexp_unlikely`, whose final
branch restarts `randexp(rng)` (bounded by `fuel`). -/
def randexp {σ : Type} (g : Rng σ) : Nat → σ → Run σ F64
  | fuel, st =>
    let p := g.next st .raw52
    let w : JInt .u64 := p.1
    let ri := w.val.toNat &&& 0x000fffffffffffff
    let idx := ri &&& 0xFF
    let x := F64.mul (F64.ofInt ri) (F64.ofBits weTable[idx]!)
    if ri < keTable[idx]! then some (.ok (x, p.2))
    else if idx = 0 then
      let (u, st') := randFloat64 g p.2
      match MathFuncs.log1p (F64.neg u) with
      | .error e => some (.error e)
      | .ok l => some (.ok (F64.sub (F64.ofBits zigguratExpR) l, st'))
    else
      let (u, st') := randFloat64 g p.2
      let lhs := F64.add (F64.mul (F64.sub (F64.ofBits feTable[idx - 1]!)
        (F64.ofBits feTable[idx]!)) u) (F64.ofBits feTable[idx]!)
      if F64.lt lhs (MathFuncs.exp (F64.neg x)) then some (.ok (x, st'))
      else match fuel with
        | 0 => none
        | f + 1 => randexp g f st'

/-- The `p > 0.15` loop of `randsubseq!`, `misc.jl:117-119`. -/
def bernoulliLoop {σ : Type} (g : Rng σ) (p : F64) : List Int → List Int → σ → Run σ (List Int)
  | [], S, st => some (.ok (S, st))
  | x :: xs, S, st =>
    let (u, st') := randFloat64 g st
    bernoulliLoop g p xs (if F64.le u p then S ++ [x] else S) st'

/-- The geometric-skip loop of `randsubseq!`, `misc.jl:129-135`; `fuel` bounds both the
loop and each `randexp` call. -/
def skipLoop {σ : Type} (g : Rng σ) (fuel : Nat) (A : List Int) (L : F64) :
    Nat → JInt64 → List Int → σ → Run σ (List Int)
  | 0, _, _, _ => none
  | k + 1, i, S, st =>
    match randexp g fuel st with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (e, st')) =>
      let s := F64.mul e L
      if intLeF64 (JInt.lit .i64 A.length - i) s then some (.ok (S, st'))
      else match F64.ceilInt .i64 s with
        | .error err => some (.error err)
        | .ok c =>
          let i' := i + c
          if 1 ≤ i'.val ∧ i'.val ≤ A.length then
            skipLoop g fuel A L k i' (S ++ [A.getD (i'.val.toNat - 1) 0]) st'
          else some (.error .boundsError)

/-- `0.15`. -/
def f015 : F64 := F64.ofBits 4594572339843380019

/-- `randsubseq(r, A, p)` for `A::Vector{Int}` and `p::Float64`, `misc.jl:107-141,166-167`. -/
def randsubseq {σ : Type} (g : Rng σ) (fuel : Nat) (A : List Int) (p : F64) (st : σ) :
    Run σ (List Int) :=
  if !(F64.le (F64.zero) p && F64.le p F64.one) then
    some (.error (.argumentError "probability not in [0,1]"))
  else if F64.eq p F64.one then some (.ok (A, st))
  else if F64.eq p F64.zero then some (.ok ([], st))
  else if F64.lt f015 p then bernoulliLoop g p A [] st
  else
    match MathFuncs.log1p (F64.neg p) with
    | .error e => some (.error e)
    | .ok l => skipLoop g fuel A (F64.div (F64.ofInt (-1)) l) fuel (JInt.lit .i64 0) [] st

end JuliaLean.RandomSampling
