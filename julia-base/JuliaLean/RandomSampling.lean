import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RandomSampling.Model
import JuliaLean.RandomSampling.Props
import JuliaLean.RandomSampling.Count
import JuliaLean.RandomSampling.NdlProofs
import JuliaLean.RandomSampling.FastProofs
import JuliaLean.RandomSampling.PermProofs
import JuliaLean.RandomSampling.Refutations
import JuliaLean.RandomSampling.Validation

namespace JuliaLean.RandomSampling

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted
  { id := "randomsampling-steprange-full-width", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["rand(::AbstractRNG, ::StepRange)", "Sampler(::Type, ::AbstractArray, ::Repetition)"]
    statement := "For every non-empty StepRange{Int,Int} r, building the sampler of rand(rng, r) does not throw."
    source := "stdlib/Random/src/Random.jl:326-330 (rand picks from any indexable collection)"
    status := .refuted, prop := ``StepRangeSamplerNonempty, thm := some ``stepRangeSamplerNonempty_refuted
    issue := "none found (queries: rand StepRange typemin typemax, rand full range StepRange, rand collection must be non-empty range, rand range overflow, Random StepRange, PR rand StepRange)"
    notes := "rand(Xoshiro(1), typemin(Int):1:typemax(Int)) throws ArgumentError(\"collection must be non-empty\"): the index sampler is 1:length(r) and length wraps to 0. The UnitRange typemin(Int):typemax(Int) works. Root cause is the wrapped length (Ranges)." },
  { id := "randomsampling-string-continuation", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["rand(::AbstractRNG, ::AbstractString)", "isvalid_unsafe(::String, ::Int)"]
    statement := "The single-draw String sampler accepts exactly the byte positions i with isvalid(s, i), the positions of the characters iteration yields."
    source := "stdlib/Random/src/Random.jl:326-335 (a string is a collection of characters)"
    status := .refuted, prop := ``StringSamplerAcceptsValid, thm := some ``stringSamplerAcceptsValid_refuted
    issue := "none found (queries: rand invalid string, rand String, rand string invalid UTF-8, rand String continuation, rand malformed string, rand AbstractString, rand string hang, PR rand string)"
    notes := "String(UInt8[0x80]): isvalid(s, 1) but the sampler rejects position 1, so rand loops forever; rand on \"a\\x80\" never returns '\\x80'." },
  { id := "randomsampling-randsubseq-zero", juliaFile := "stdlib/Random/src/misc.jl"
    juliaFns := ["randsubseq(::AbstractRNG, ::AbstractArray, ::Real)", "randexp(::AbstractRNG)"]
    statement := "randsubseq(rng, A, p) with 0 <= p <= 1 never throws, for every RNG."
    source := "stdlib/Random/src/misc.jl:170-175 (randsubseq docstring)"
    status := .refuted, prop := ``RandsubseqTotal, thm := some ``randsubseqTotal_refuted
    issue := "none found (queries: randsubseq zero randexp, randsubseq, randsubseq BoundsError, PR randsubseq)"
    notes := "With an RNG returning zero words, randexp returns 0.0, the skip ceil(Int, 0.0) is 0 and randsubseq indexes A[0] (BoundsError). A zero 52-bit word has probability 2^-52 per exponential draw." },
  { id := "randomsampling-randstring-uint8-length", juliaFile := "stdlib/Random/src/misc.jl"
    juliaFns := ["randstring(::AbstractRNG, ::Vector{UInt8}, ::Int)"]
    statement := "randstring(rng, chars::Vector{UInt8}, n) returns a string of length n."
    source := "stdlib/Random/src/misc.jl:46-47,63-66 (randstring docstring)"
    status := .refuted, prop := ``RandstringCharacterLength, thm := some ``randstringCharacterLength_refuted
    issue := "none found (queries: randstring UInt8 length, randstring UTF, randstring length, PR randstring UInt8)"
    notes := "randstring(rng, UInt8[0xc3, 0xa9], 2) can return \"é\", of length 1: the UInt8 path writes bytes. Documentation finding (P3)." },
  -- proven
  { id := "randomsampling-ndl-in-range", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["rand(::AbstractRNG, ::UnitRange{T}) for T of at most 64 bits", "SamplerRangeNDL"]
    statement := "For every BitInteger type of at most 64 bits, every a <= b (including typemin:typemax) and every RNG, rand(rng, a:b) returns a value in a:b and never throws."
    source := "stdlib/Random/src/Random.jl:326-330 (rand docstring)", status := .proven
    prop := ``NdlInRange, thm := some ``ndlInRange_proven },
  { id := "randomsampling-ndl-uniform", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["rand(::AbstractRNG, ::SamplerRangeNDL)", "rand_unlikely"]
    statement := "rand(rng, a:b) (types up to 64 bits) returns the value of the first word its acceptance test accepts, accepted words yield only values in a:b, and every value of a:b is yielded by the same positive number of uint_sup(T) words."
    source := "stdlib/Random/src/generation.jl:370-407 (Lemire's nearly divisionless method, arXiv:1805.10941)"
    status := .proven, prop := ``NdlUniform, thm := some ``ndlUniform_proven
    notes := "Equal counts per value make the result exactly uniform for independent uniform words." },
  { id := "randomsampling-fast128-uniform", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["rand(::AbstractRNG, ::UnitRange{Int128})", "rand(::AbstractRNG, ::UnitRange{UInt128})", "SamplerRangeFast"]
    statement := "For Int128/UInt128 and every a <= b (including typemin:typemax), rand(rng, a:b) returns a value in a:b, is rejection sampling on UInt64 or UInt128 words, and every value is yielded by the same positive number of words."
    source := "stdlib/Random/src/Random.jl:326-330; generation.jl:247-301"
    status := .proven, prop := ``FastUniform, thm := some ``fastUniform_proven
    notes := "Modelled for RNGs with rng_native_52(rng) == UInt64 (Xoshiro, TaskLocalRNG, RandomDevice); MersenneTwister's Float64-native branches are not modelled." },
  { id := "randomsampling-empty-argerror", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["SamplerRangeNDL", "SamplerRangeFast", "Sampler(::Type, ::String, ::Val{1})"]
    statement := "Sampling from an empty unit range of any BitInteger type, an empty array index range or an empty String throws ArgumentError(\"collection must be non-empty\")."
    source := "invariant; stdlib/Random/src/generation.jl:244,260,380 (empty_collection_error)"
    status := .proven, prop := ``EmptyArgumentError, thm := some ``emptyArgumentError_proven
    notes := "Also observed for empty Vector, Dict, Set, BitSet, IdDict, keys/values, String, SubString, Tuple{}, OneTo(0), BigInt, float and Char ranges, Val(1) and Val(Inf)." },
  { id := "randomsampling-randperm-perm", juliaFile := "stdlib/Random/src/misc.jl"
    juliaFns := ["randperm(::AbstractRNG, ::Int)", "randperm!"]
    statement := "For every n >= 0 and every RNG, randperm(rng, n) returns a permutation of 1:n."
    source := "stdlib/Random/src/misc.jl:295-300 (randperm docstring)", status := .proven
    prop := ``RandpermIsPerm, thm := some ``randpermIsPerm_proven },
  { id := "randomsampling-randcycle-cycle", juliaFile := "stdlib/Random/src/misc.jl"
    juliaFns := ["randcycle(::AbstractRNG, ::Int)", "randcycle!"]
    statement := "For every n >= 0 and every RNG, randcycle(rng, n) returns a permutation of 1:n in which every element is reached from 1, i.e. a single n-cycle."
    source := "stdlib/Random/src/misc.jl:369-378 (randcycle docstring)", status := .proven
    prop := ``RandcycleSingleCycle, thm := some ``randcycleSingleCycle_proven },
  { id := "randomsampling-shuffle-randperm", juliaFile := "stdlib/Random/src/misc.jl"
    juliaFns := ["shuffle!(::AbstractRNG, ::Vector{Int})", "randperm(::AbstractRNG, ::Int)"]
    statement := "For every RNG state, shuffle!(rng, v) equals v[randperm(rng, length(v))] and leaves the RNG in the same state."
    source := "stdlib/Random/src/misc.jl:237 (keep consistent with randperm!) and the identical docstring examples (misc.jl:226-233,312-319)"
    status := .proven, prop := ``ShuffleIsRandperm, thm := some ``shuffleIsRandperm_proven
    notes := "Implies shuffle! is a permutation of its input. shuffle!(::AbstractArray{Bool}) uses a different algorithm and is not covered." },
  { id := "randomsampling-char-valid", juliaFile := "stdlib/Random/src/generation.jl"
    juliaFns := ["rand(::AbstractRNG, ::Type{Char})"]
    statement := "For every RNG, rand(rng, Char) returns a valid Unicode scalar value (at most 0x10ffff, not a surrogate)."
    source := "stdlib/Random/src/Random.jl:346 (AbstractChar types sample valid Unicode scalars)", status := .proven
    prop := ``RandCharValid, thm := some ``randCharValid_proven }
]

end JuliaLean.RandomSampling
