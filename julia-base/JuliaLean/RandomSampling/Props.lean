import JuliaLean.RandomSampling.Model

/-!
Properties of the sampling model. Every property quantifies over all RNGs
(`Rng σ` for every state type `σ`), every starting state and every fuel bound.
-/

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

/-- `rand(rng, a:b)` for every `BitInteger` type of at most 64 bits returns a value in
`a:b` (and never throws) for every RNG. Source: `rand` docstring, `Random.jl:326-330`. -/
def NdlInRange : Prop :=
  ∀ (t : IntTy), t.bits ≤ 64 → ∀ (a b : JInt t) (sp : NDL t), ndlSampler a b = .ok sp →
  ∀ (σ : Type) (g : Rng σ) (fuel : Nat) (st : σ) (res : Jl (JInt t × σ)),
    ndlRand g sp fuel st = some res →
    ∃ v st', res = .ok (v, st') ∧ a.val ≤ v.val ∧ v.val ≤ b.val

/-- `rand(rng, a:b)` (types of at most 64 bits) is rejection sampling: it returns the
value of the first word its acceptance test accepts, accepted words only yield values in
`a:b`, and every value of `a:b` is yielded by the same positive number of words of
`uint_sup(T)`. With independent uniform words the result is exactly uniform.
Source: `generation.jl:372` (Lemire, arXiv:1805.10941, algorithm 5). -/
def NdlUniform : Prop :=
  ∀ (t : IntTy), t.bits ≤ 64 → ∀ (a b : JInt t) (sp : NDL t), ndlSampler a b = .ok sp →
  (∀ (σ : Type) (g : Rng σ) (fuel : Nat) (st : σ) (v : JInt t) (st' : σ),
    ndlRand g sp fuel st = some (.ok (v, st')) →
    ∃ n, (∀ i < n, ndlStep sp (g.wordAt (.int (uintSup t)) st i) = none) ∧
      ndlStep sp (g.wordAt (.int (uintSup t)) st n) = some v ∧
      st' = g.stateAfter (.int (uintSup t)) st (n + 1)) ∧
  (∀ (x : JInt (uintSup t)) (v : JInt t), ndlStep sp x = some v → a.val ≤ v.val ∧ v.val ≤ b.val) ∧
  ∃ q, 0 < q ∧ ∀ v : JInt t, a.val ≤ v.val → v.val ≤ b.val →
    countBelow (fun x => decide (ndlStep sp (JInt.wrap (uintSup t) x) = some v))
      (2 ^ (uintSup t).bits) = q

/-- `rand(rng, a:b)` for `Int128`/`UInt128` (including `typemin:typemax`) returns a value in
`a:b`, is rejection sampling on words of `fastWord bw`, and every value of `a:b` is yielded
by the same positive number of words. Source: `Random.jl:326-330`, `generation.jl:219-236`. -/
def FastUniform : Prop :=
  ∀ (t : IntTy), t.bits = 128 → ∀ (a b : JInt t) (sp : Fast t), fastSampler a b = .ok sp →
  (∀ (σ : Type) (g : Rng σ) (fuel : Nat) (st : σ) (res : Jl (JInt t × σ)),
    fastRand g sp fuel st = some res →
    ∃ v st' n, res = .ok (v, st') ∧ a.val ≤ v.val ∧ v.val ≤ b.val ∧
      (∀ i < n, fastStep sp (g.wordAt (.int (fastWord sp.bw)) st i) = none) ∧
      fastStep sp (g.wordAt (.int (fastWord sp.bw)) st n) = some v ∧
      st' = g.stateAfter (.int (fastWord sp.bw)) st (n + 1)) ∧
  ∃ q, 0 < q ∧ ∀ v : JInt t, a.val ≤ v.val → v.val ≤ b.val →
    countBelow (fun x => decide (fastStep sp (JInt.wrap (fastWord sp.bw) x) = some v))
      (2 ^ (fastWord sp.bw).bits) = q

/-- Sampling from an empty unit range of any `BitInteger` type, an empty array (index
range `1:0`) or an empty `String` throws `ArgumentError("collection must be non-empty")`.
Source: invariant; every sampler constructor calls `empty_collection_error()`
(`generation.jl:244,260,380`). -/
def EmptyArgumentError : Prop :=
  (∀ (t : IntTy) (a b : JInt t), b.val < a.val → ndlSampler a b = .error emptyCollectionError) ∧
  (∀ (t : IntTy) (a b : JInt t), b.val < a.val → fastSampler a b = .error emptyCollectionError) ∧
  (∀ s : Strings.JStr, s.bytes = [] → stringSampler s = .error emptyCollectionError)

/-- `rand(rng, r)` for a non-empty `StepRange{Int,Int}` can build its sampler (it does not
throw). Source: `rand` docstring, `Random.jl:326-330` (indexable collections). -/
def StepRangeSamplerNonempty : Prop :=
  ∀ (a s b : JInt64) (r : Ranges.Rng),
    Ranges.stepRange ⟨.bit .i64, a⟩ ⟨.bit .i64, s⟩ ⟨.bit .i64, b⟩ = .ok r →
    Ranges.isEmpty r = false → ∀ e, stepRangeSampler r ≠ .error e

/-- The single-draw `String` sampler accepts exactly the positions `i` where
`isvalid(s, i)`, i.e. the positions of the characters iteration yields
(`strings-iterate-valid-indices`). Source: `Random.jl:326-335` (a string is a collection
of characters). -/
def StringSamplerAcceptsValid : Prop :=
  ∀ (s : Strings.JStr) (i : JInt64), 1 ≤ i.val → i.val ≤ (Strings.ncodeunits s).val →
    isvalidUnsafe s i = Strings.isvalidAt s i

/-- `randstring(rng, chars::Vector{UInt8}, n)` returns a string of length `n`.
Source: `misc.jl:46-47,63-66`. -/
def RandstringCharacterLength : Prop :=
  ∀ (σ : Type) (g : Rng σ) (fuel : Nat) (chars : List UInt8) (n : Nat) (st : σ)
    (bytes : List UInt8) (st' : σ), chars ≠ [] → n < 2 ^ 40 →
    randstringBytes g fuel chars n st = some (.ok (bytes, st')) →
    ∀ h : bytes.length < 2 ^ 62, (Strings.length ⟨bytes, h⟩).val = n

/-- `randsubseq(rng, A, p)` for `0 ≤ p ≤ 1` never throws. Source: `misc.jl:170-175`. -/
def RandsubseqTotal : Prop :=
  ∀ (σ : Type) (g : Rng σ) (fuel : Nat) (A : List Int) (p : F64) (st : σ)
    (res : Jl (List Int × σ)), A.length < 2 ^ 40 →
    F64.le F64.zero p = true → F64.le p F64.one = true →
    randsubseq g fuel A p st = some res → ∃ S st', res = .ok (S, st')

/-- `randperm(rng, n)` returns a permutation of `1:n` for every RNG.
Source: `misc.jl:295-300`. -/
def RandpermIsPerm : Prop :=
  ∀ (σ : Type) (g : Rng σ) (fuel n : Nat) (st : σ) (res : Jl ((Nat → Int) × σ)),
    n < 2 ^ 62 → randperm g fuel n st = some res →
    ∃ a st', res = .ok (a, st') ∧ IsPerm n a

/-- `randcycle(rng, n)` returns a permutation of `1:n` with a single cycle (every element
is reached from 1). Source: `misc.jl:369-378`. -/
def RandcycleSingleCycle : Prop :=
  ∀ (σ : Type) (g : Rng σ) (fuel n : Nat) (st : σ) (res : Jl ((Nat → Int) × σ)),
    n < 2 ^ 62 → randcycle g fuel n st = some res →
    ∃ a st', res = .ok (a, st') ∧ IsPerm n a ∧
      ∀ k, 1 ≤ k → k ≤ n → ∃ m, iterPerm a m 1 = k

/-- `shuffle!(rng, v)` permutes `v` by `randperm(rng, length(v))`, consuming the same
words: `shuffle!(rng, v) == v[randperm(rng, length(v))]` for equal RNG states. Source:
`misc.jl:237` ("keep it consistent with `randperm!`") and the identical docstring examples
(`misc.jl:226-233,312-319`). -/
def ShuffleIsRandperm : Prop :=
  ∀ (σ : Type) (g : Rng σ) (fuel n : Nat) (st : σ) (c : Nat → Int), n < 2 ^ 62 →
    shuffle g fuel n c st = (randperm g fuel n st).map fun res => res.map fun q =>
      (fun k => if 1 ≤ k ∧ k ≤ n then c (q.1 k).toNat else c k, q.2)

/-- `rand(rng, Char)` returns a valid Unicode scalar value. Source: `Random.jl:346`. -/
def RandCharValid : Prop :=
  ∀ (σ : Type) (g : Rng σ) (fuel : Nat) (st : σ) (res : Jl (Nat × σ)),
    randCharCode g fuel st = some res →
    ∃ c st', res = .ok (c, st') ∧ c ≤ 0x10ffff ∧ ¬ (0xd800 ≤ c ∧ c ≤ 0xdfff)

/-- `rand(rng)` lies in `[0, 1)`. Source: `Random.jl:341` ("floating point types sample
from `[0, 1)`"). -/
def RandFloat64CloseOpen : Prop :=
  ∀ (σ : Type) (g : Rng σ) (st : σ),
    F64.le F64.zero (randFloat64 g st).1 = true ∧ F64.lt (randFloat64 g st).1 F64.one = true

end JuliaLean.RandomSampling
