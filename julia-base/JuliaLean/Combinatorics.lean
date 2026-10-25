import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Combinatorics.Integer
import JuliaLean.Combinatorics.Permutation
import JuliaLean.Combinatorics.Matrix
import JuliaLean.Combinatorics.Nextprod

/-!
`base/combinatorics.jl` and the integer `binomial` methods in
`base/intfuncs.jl`/`base/gmp.jl`, master `bbfa0ce4150`. The pinned
`base/combinatorics.jl` contains no `multinomial`, permutation parity/sign, or
`circshift!`; those functions therefore have no entries in this area.
-/

namespace JuliaLean.Combinatorics

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "combinatorics-isperm-definition", juliaFile := "base/combinatorics.jl"
    juliaFns := ["isperm", "_isperm"]
    statement := "For every BitInteger element type and vector, isperm is true exactly when every value 1:length(p) occurs once."
    source := "base/combinatorics.jl:62-101 (isperm docstring and implementations)", status := .proven
    prop := ``IspermTypedDefinition, thm := some ``ispermTypedDefinition_proven
    notes := "Covers empty and non-Int vectors; the normalized differential corpus matched release and nightly." },
  { id := "combinatorics-invperm-inverse", juliaFile := "base/combinatorics.jl"
    juliaFns := ["invperm", "isperm"]
    statement := "For one-based Int permutations, invperm accepts exactly valid permutations and computes the inverse index mapping."
    source := "base/combinatorics.jl:245-316 (invperm docstring and implementations)", status := .proven
    prop := ``InvpermInverse, thm := some ``invpermInverse_proven
    notes := "Reuses the source model and universal inverse-index proof in ReinterpretArrays.ProofIndex." },
  { id := "combinatorics-invperm-offset", juliaFile := "base/combinatorics.jl"
    juliaFns := ["invperm(::AbstractVector)", "isperm(::AbstractVector)"]
    statement := "invperm returns an inverse for every AbstractVector that isperm classifies as a permutation, independent of its axes."
    source := "base/combinatorics.jl:245-251 (invperm docstring; no one-based restriction)", status := .refuted
    prop := ``InvpermEveryPermutation, thm := some ``invpermEveryPermutation_refuted
    issue := "none found (queries: invperm offset array, invperm require_one_based, isperm offset array invperm, invperm one based indexing)"
    notes := "An AbstractVector with axes 0:2 and values [2,3,1] passes isperm but invperm throws ArgumentError." },
  { id := "combinatorics-permute-semantics", juliaFile := "base/combinatorics.jl"
    juliaFns := ["permute!", "invpermute!"]
    statement := "permute! implements v .= v[p] and invpermute! implements v[p] = v, including documented unchecked duplicate indices and preflight errors on invalid bounds or shape."
    source := "base/combinatorics.jl:184-243 (docstrings and one-line implementations)", status := .proven
    prop := ``PermuteSemantics, thm := some ``permuteSemantics_proven
    notes := "Out-of-range and shape-error cases leave v unchanged because indexing/shape checks precede assignment; duplicate p values are not rejected, as the docstring explicitly says no permutation check is done." },
  { id := "combinatorics-permute-roundtrip", juliaFile := "base/combinatorics.jl"
    juliaFns := ["permute!", "invpermute!"]
    statement := "Applying a permutation and then its inverse restores every vector."
    source := "base/combinatorics.jl:184-243 (permute! and invpermute! docstrings)", status := .proven
    prop := ``PermuteRoundtrip, thm := some ``permuteRoundtrip_proven },
  { id := "combinatorics-swap-equal-bounds", juliaFile := "base/combinatorics.jl"
    juliaFns := ["swapcols!", "swaprows!"]
    statement := "swapcols! and swaprows! throw BoundsError whenever either scalar index is outside the relevant matrix axis."
    source := "invariant; explicit checks at base/combinatorics.jl:103-123", status := .refuted
    prop := ``SwapBoundsChecked, thm := some ``swapBoundsChecked_refuted
    issue := "none found (queries: swapcols BoundsError, swaprows BoundsError)"
    notes := "Equal out-of-bounds indices return before either explicit bounds check." },
  { id := "combinatorics-permutecols-unsigned", juliaFile := "base/combinatorics.jl"
    juliaFns := ["permutecols!!", "permutecols!", "permuterows!", "invpermutecols!", "invpermuterows!", "_permute!", "_invpermute!"]
    statement := "The in-place matrix cycle algorithms produce the requested permutation for every valid AbstractVector{<:Integer}, restore p for the non-destructive variants, and zero p for permutecols!!."
    source := "invariant and declared signatures; base/combinatorics.jl:125-182", status := .refuted
    prop := ``PermuteColsCorrect, thm := some ``permuteColsCorrect_refuted
    issue := "none found (queries: permutecols unsigned, _permute! UInt)"
    notes := "With UInt[3,1,2], the sign-marker variants leave the matrix unchanged and replace p by wrapped negative values; permutecols!! works." },
  { id := "combinatorics-factorial-wide-error", juliaFile := "base/combinatorics.jl"
    juliaFns := ["factorial_lookup", "factorial(::BitInteger)", "factorial(::BigInt)"]
    statement := "Factorial returns exact results within its fixed-width or GMP argument range, DomainError for negative n, and an intentional OverflowError when an argument exceeds an implementation limit."
    source := "base/intfuncs.jl:1305-1324 (factorial docstring); base/combinatorics.jl:21-40; base/gmp.jl:717", status := .refuted
    prop := ``FactorialContract, thm := some ``factorialContract_refuted
    issue := "none found (queries: factorial UInt64 InexactError, factorial UInt128 InexactError, factorial Int128 InexactError)"
    notes := "Fixed values outside machine Int range and BigInt values above typemax(Culong) throw narrowing InexactError before an intentional classification." },
  { id := "combinatorics-factorial-bigint", juliaFile := "base/gmp.jl"
    juliaFns := ["factorial(::BigInt)"]
    statement := "BigInt factorial returns the exact mathematical factorial throughout GMP's Culong argument range and DomainError for every negative input."
    source := "base/intfuncs.jl:1305-1324 (factorial docstring); base/gmp.jl:717", status := .proven
    prop := ``FactorialBigWithinCulong, thm := some ``factorialBigWithinCulong_proven },
  { id := "combinatorics-binomial-typemin", juliaFile := "base/intfuncs.jl"
    juliaFns := ["binomial(::T, ::T) where T<:Integer"]
    statement := "For every fixed-width integer type, binomial returns the exact generalized coefficient when representable and OverflowError exactly otherwise."
    source := "base/intfuncs.jl:1339-1402 (binomial docstring and implementation)", status := .refuted
    prop := ``BinomialContract, thm := some ``binomialContract_refuted
    issue := "none found (queries: binomial typemin, binomial -9223372036854775808, binomial negative overflow)"
    notes := "binomial(typemin(T), one(T)) returns zero for all five signed widths instead of typemin(T)." },
  { id := "combinatorics-binomial-nonnegative-edges", juliaFile := "base/intfuncs.jl"
    juliaFns := ["binomial(::T, ::T) where T<:Integer"]
    statement := "For every nonnegative fixed-width n, binomial(n,k) is zero for k<0 or k>n and one for k=0."
    source := "base/intfuncs.jl:1342-1349,1377,1385-1386", status := .proven
    prop := ``BinomialNonnegativeEdges, thm := some ``binomialNonnegativeEdges_proven },
  { id := "combinatorics-binomial-bigint", juliaFile := "base/gmp.jl"
    juliaFns := ["binomial(::BigInt, ::Integer)"]
    statement := "BigInt binomial is exact when k fits Culong, returns zero for k<0 or nonnegative n<k, and uses an explicit resource OverflowError beyond the GMP exponent range."
    source := "base/intfuncs.jl:1339-1354 (definition); base/gmp.jl:719-728", status := .proven
    prop := ``BinomialBigExact, thm := some ``binomialBigExact_proven },
  { id := "combinatorics-nextprod-empty", juliaFile := "base/combinatorics.jl"
    juliaFns := ["nextprod"]
    statement := "For positive x and factors at least two, nextprod returns the least factor product at least x, including the empty tuple's product one."
    source := "base/combinatorics.jl:318-373 (nextprod docstring and implementation)", status := .refuted
    prop := ``NextprodLeast, thm := some ``nextprodLeast_refuted
    issue := "none found (queries: nextprod BoundsError, nextprod empty tuple, nextprod factors empty)"
    notes := "nextprod((),1) throws BoundsError at mx[1]; ordinary positive nonempty cases matched a brute-force oracle. The UInt/typemax hang reduces to catalogued nextpow issue #45880." }
]

end JuliaLean.Combinatorics
