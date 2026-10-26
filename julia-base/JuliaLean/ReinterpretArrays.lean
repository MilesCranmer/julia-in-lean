import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ReinterpretArrays.Refutations
import JuliaLean.ReinterpretArrays.PermutedTyped
import JuliaLean.ReinterpretArrays.NestedView
import JuliaLean.ReinterpretArrays.ProofIndex
import JuliaLean.ReinterpretArrays.ProofUmi
import JuliaLean.ReinterpretArrays.ProofBytes
import JuliaLean.ReinterpretArrays.ProofSmi

namespace JuliaLean.ReinterpretArrays

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  { id := "reinterpretarrays-umi-div", juliaFile := "base/multinverses.jl"
    juliaFns := ["UnsignedMultiplicativeInverse{T}(d)", "div(::T, ::UnsignedMultiplicativeInverse{T})", "rem(::T, ::MultiplicativeInverse{T})"]
    statement := "For every unsigned BitInteger type, every nonzero divisor d and every dividend a, the UnsignedMultiplicativeInverse constructor returns, and div(a, mi) == div(a, d), rem(a, mi) == rem(a, d)."
    source := "invariant (base/multinverses.jl:19-45: computes integer division by a constant)", status := .proven
    prop := ``UmiDivCorrect, thm := some ``umiDivCorrect
    notes := "Constructor model shared with IntArith (unsignedMI); magic numbers, add flags, shifts and quotients differential-checked against Julia for every width. 1.13.2 differs only in using non-wrapping operators that never overflow." },
  { id := "reinterpretarrays-reshape-check-sound", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape(::AbstractArray, ::Dims)", "_reshape", "Core.checked_dims"]
    statement := "reshape(A, dims) of a generic parent succeeds only when every dimension is nonnegative and their exact product equals length(A) (it never accepts a wrapped product)."
    source := "base/reshapedarray.jl:66-80 (reshape docstring: the total number of elements must not change)", status := .proven
    prop := ``ReshapeCheckSound, thm := some ``reshapeCheckSound
    notes := "Master uses Core.checked_dims (base/reshapedarray.jl:223). In 1.13.2 the check was prod(dims) == n, which accepts wrapped products such as reshape(1:6, 1645062, 67280421310721) (observed); fixed on master by PR #62797." },
  { id := "reinterpretarrays-reshape-colon-sound", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape(::AbstractArray, ::Union{Integer,Colon}...)", "_reshape_uncolon"]
    statement := "reshape(A, pre..., :, post...) returns only dimensions (pre..., c, post...) that are nonnegative and multiply exactly to length(A)."
    source := "base/reshapedarray.jl:75-80 (reshape docstring: the colon dimension is computed so the product equals the length)", status := .proven
    prop := ``ReshapeColonSound, thm := some ``reshapeColonSound
    notes := "Int dimensions. 1.13.2 accepted negative pairs on lazy parents, e.g. reshape(1:6, :, -2) == (-3, -2)-shaped (observed); master rejects them." },
  { id := "reinterpretarrays-view-linear-index", juliaFile := "base/subarray.jl"
    juliaFns := ["view(A, r, c...)", "compute_offset1", "compute_linindex", "_reindexlinear"]
    statement := "For a fast linear view(A, r, c2, ..., ck) with a range r and integer scalars, V[i] reads the parent at the linear index of (r[i], c2, ..., ck), for every in-bounds view of a parent whose length is an Int."
    source := "base/subarray.jl:175-183 (view docstring)", status := .proven
    prop := ``ViewIndexCorrect, thm := some ``viewIndexCorrect
    notes := "Wrapping Int arithmetic in offset1/stride1 cancels modulo 2^64. Strides and pointers of random views and reshaped views also matched element addresses (28593 cases)." },
  { id := "reinterpretarrays-permuted-index", juliaFile := "base/permuteddimsarray.jl"
    juliaFns := ["PermutedDimsArray(A, perm)", "getindex(::PermutedDimsArray, I...)", "invperm", "isperm"]
    statement := "PermutedDimsArray(A, perm) with Int entries is constructed exactly when perm is a permutation of 1:N, and B[I...] reads A[J...] with J[perm[d]] == I[d], in bounds whenever I is in bounds of size(B)."
    source := "base/permuteddimsarray.jl:20-40 (PermutedDimsArray docstring: B[3,1,2] == A[1,2,3])", status := .proven
    prop := ``PermutedCorrect, thm := some ``permutedCorrect
    notes := "Element access, permutedims, permutedims!, copyto! and dims-reductions also agreed with the reference for all 3-d permutations and several sizes including empty ones." },
  { id := "reinterpretarrays-ra-getindex-bytes", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["getindex(::ReinterpretArray, i1, tailinds...)", "_getindex_ra(::NonReshapedReinterpretArray)"]
    statement := "reinterpret(T, A)[i1, J...] returns exactly the sizeof(T) parent bytes starting at byte (i1-1)*sizeof(T) of column J (all three _getindex_ra branches), and throws BoundsError outside 1:size(R, 1)."
    source := "base/reinterpretarray.jl:35-39 (reinterpret docstring: a view with the same binary data)", status := .proven
    prop := ``RaGetCorrect, thm := some ``raGetCorrect
    notes := "Element sizes are aligned_sizeof values; padding readability checks are outside the byte model. Differential check: 11 element types (UInt8..UInt128, NTuple{3,5,6,7,12,UInt8}, NTuple{3,UInt16}) over vectors, matrices, strided, reversed and reshaped views: 0 mismatches." },
  { id := "reinterpretarrays-ra-setindex-bytes", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["setindex!(::ReinterpretArray, v, i1, tailinds...)", "_setindex_ra!(::NonReshapedReinterpretArray)"]
    statement := "reinterpret(T, A)[i1, J...] = v changes exactly the sizeof(T) parent bytes starting at byte (i1-1)*sizeof(T) of column J to the bytes of v and leaves every other byte, including the neighbouring bytes of partially overwritten parent elements, unchanged; out of bounds it throws BoundsError."
    source := "base/reinterpretarray.jl:35-39 (reinterpret docstring), base/reshapedarray.jl:70-73 (shared data: setting elements of one alters the other)", status := .proven
    prop := ``RaSetCorrect, thm := some ``raSetCorrect
    notes := "Same differential check as for getindex, comparing the full parent byte image after each write: 0 mismatches. reinterpret(reshape, ...) reads and writes were checked the same way (0 mismatches apart from the nested-shape refutation)." },
  { id := "reinterpretarrays-smi-div", juliaFile := "base/multinverses.jl"
    juliaFns := ["SignedMultiplicativeInverse{T}(d)", "div(::T, ::SignedMultiplicativeInverse{T})"]
    statement := "For every signed BitInteger type and every nonzero divisor d, the SignedMultiplicativeInverse constructor terminates, and div(a, mi) == div(a, d) for every dividend a except typemin(T) with d == -1."
    source := "invariant (base/multinverses.jl:19-45: computes integer division by a constant)", status := .proven
    prop := ``SmiDivCorrect, thm := some ``smiDivCorrect
    notes := "Includes divisors 1, -1, typemax and typemin. Magic numbers, addmul, shift and quotients differential-checked against Julia for all five widths (identical); Julia exhaustive over Int8/UInt8 dividends and divisors. The excluded input is refuted separately (reinterpretarrays-smi-div-typemin)." },
  { id := "reinterpretarrays-smi-rem-mod", juliaFile := "base/multinverses.jl"
    juliaFns := ["rem(::T, ::MultiplicativeInverse{T})", "mod(::T, ::SignedMultiplicativeInverse{T})"]
    statement := "rem(a, mi) == rem(a, d) and mod(a, mi) == mod(a, d) for a SignedMultiplicativeInverse of every nonzero divisor and every dividend."
    source := "invariant (base/multinverses.jl:148-161)", status := .proven
    prop := ``SmiRemModCorrect, thm := some ``smiRemModCorrect
    notes := "Holds even for typemin(T) and -1, where the wrapped quotient still gives remainder 0." },
  { id := "reinterpretarrays-ind2sub-rs", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["ind2sub_rs", "_ind2sub_rs", "getindex(::ReshapedArray, I...)", "setindex!(::ReshapedArray, v, I...)"]
    statement := "The parent subscripts that ReshapedArray computes from a linear index with SignedMultiplicativeInverse division are in bounds and are the column-major subscripts of that index, for every parent size whose length is an Int."
    source := "base/reshapedarray.jl:66-73 (reshape docstring: same data), invariant", status := .proven
    prop := ``Ind2subCorrect, thm := some ``ind2subCorrect
    notes := "Divisors are max(1, size) (base/reshapedarray.jl:238), so empty dimensions are covered. Julia check: getindex/setindex!/linear indexing of reshapes of strided 2-d and 3-d views, including empty and singleton sizes: 0 mismatches." },
  -- refuted
  { id := "reinterpretarrays-rr-nested-size", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["reinterpret(reshape, T, ::ReshapedReinterpretArray)", "size(::ReshapedReinterpretArray)"]
    statement := "reinterpret(reshape, T, reinterpret(reshape, S, a)) has the size (or error) of reinterpret(reshape, T, b) for b = collect(reinterpret(reshape, S, a)), for T, S, eltype(a) distinct."
    source := "base/reinterpretarray.jl:151-158 (reinterpret(reshape, T, A) docstring: B gains or loses A's first dimension)", status := .refuted
    prop := ``RrNestedSize, thm := some ``rrNestedSize_refuted
    issue := "none found (queries: reinterpret reshape, ReshapedReinterpretArray, nested reinterpret, reinterpret of reinterpret, reinterpret nesting; related closed #63305)"
    notes := "base/reinterpretarray.jl:191 forwards to reinterpret(reshape, T, a.parent), skipping the intermediate shape: a::Vector{UInt32} of length 3 gives size (4, 3) instead of (2, 2, 3), and a 2x3 UInt32 matrix through UInt16 to UInt64 gives (3,) instead of an ArgumentError. Same in 1.13.2." },
  { id := "reinterpretarrays-reshape-typemax-dim", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape(::AbstractArray, ::Dims)", "_reshape", "Core.checked_dims"]
    statement := "reshape(A, dims) succeeds whenever every dimension is nonnegative and their product is length(A)."
    source := "base/reshapedarray.jl:66-80 (reshape docstring: the total number of elements must not change)", status := .refuted
    prop := ``ReshapeCheckComplete, thm := some ``reshapeCheckComplete_refuted
    issue := "none found (queries: reshape typemax, invalid Array dimensions reshape, checked_dims, reshape overflow, reshape range typemax; cause merged PR #62797)"
    notes := "_reshape uses Core.checked_dims, which treats a dimension equal to typemax(Int) as invalid: reshape(1:typemax(Int), typemax(Int), 1) and reshape(1:typemax(Int), :, 1) throw ArgumentError. Regression: 1.13.2 used prod(dims) and accepts them (but also accepted wrapped products, which master now rejects)." },
  { id := "reinterpretarrays-size-overflow", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["reinterpret(T, ::AbstractArray)", "size(::NonReshapedReinterpretArray)", "axes(::NonReshapedReinterpretArray)"]
    statement := "reinterpret(T, A) either throws or has size(R, 1) * sizeof(T) == size(A, 1) * sizeof(eltype(A))."
    source := "base/reinterpretarray.jl:3-7 (ReinterpretArray docstring: the array is compressed/expanded in the first dimension), 76-78 (non-integral first dimension error)", status := .refuted
    prop := ``RaSizeExact, thm := some ``raSizeExact_refuted
    issue := "none found (queries: reinterpret size overflow, reinterpret range overflow, reinterpret negative size, reinterpret large range, reinterpret lazy)"
    notes := "psize[1]*aligned_sizeof(S) wraps in Int (lines 96, 373, 387): reinterpret(Int32, 1:2^61) has size (0,) instead of (2^62,), reinterpret(UInt8, 1:2^60) a negative size, and reinterpret(NTuple{3,UInt8}, 1:2^61) is accepted with size (0,). Same in 1.13.2." },
  { id := "reinterpretarrays-permuted-int-type", juliaFile := "base/permuteddimsarray.jl"
    juliaFns := ["PermutedDimsArray(::AbstractArray, perm)"]
    statement := "PermutedDimsArray(A, perm) accepts every permutation of 1:ndims(A), whatever integer type its entries have."
    source := "base/permuteddimsarray.jl:20-27 (PermutedDimsArray docstring: like permutedims without copying), 94-95 (permutedims: perm is a tuple or vector of integers)", status := .refuted
    prop := ``PermutedAnyIntType, thm := some ``permutedAnyIntType_refuted
    issue := "none found (queries: perm and iperm must both be NTuple, PermutedDimsArray Int32, PermutedDimsArray perm type, PermutedDimsArray non-Int, PermutedDimsArray integer permutation)"
    notes := "(perm...,) keeps the element type and line 13 requires NTuple{N,Int}: PermutedDimsArray(A, Int32[2, 1]) throws ErrorException while permutedims(A, Int32[2, 1]) works. Same in 1.13.2." },
  { id := "reinterpretarrays-nested-slice-offset", juliaFile := "base/subarray.jl"
    juliaFns := ["view(::SubArray, ::Colon)", "reindex", "compute_offset1", "getindex(::IdentityUnitRange, ::AbstractUnitRange)"]
    statement := "view(view(M, IdentityUnitRange(lo:hi), c), :)[i] reads M[i, c] for every in-bounds lo:hi, c and i in lo:hi."
    source := "base/subarray.jl:175-183 (view docstring)", status := .refuted
    prop := ``NestedColonViewCorrect, thm := some ``nestedColonViewCorrect_refuted
    issue := "#62906 (open, duplicate), PR #63079 (open)"
    notes := "IdentityUnitRange(lo:hi)[Slice(...)] returns the Slice, so compute_offset1 uses the Slice branch and the nested view is shifted by lo - 1 elements (out of bounds in the last column). Same in 1.13.2." },
  { id := "reinterpretarrays-smi-div-typemin", juliaFile := "base/multinverses.jl"
    juliaFns := ["div(::T, ::SignedMultiplicativeInverse{T})", "divrem(::T, ::MultiplicativeInverse{T})"]
    statement := "div(a, SignedMultiplicativeInverse(d)) equals div(a, d), including its DivideError, for every dividend and nonzero divisor."
    source := "invariant (base/multinverses.jl:19-21: computes floor(n/d) by multiply and shift; div docstring base/div.jl)", status := .refuted
    prop := ``SmiDivAll, thm := some ``smiDivAll_refuted
    issue := "none found (queries: SignedMultiplicativeInverse, multiplicativeinverse, MultiplicativeInverses, multiplicative inverse typemin)"
    notes := "The |divisor| == 1 branch returns a*b.divisor, which wraps: div(typemin(Int), multiplicativeinverse(-1)) == typemin(Int) while div(typemin(Int), -1) throws DivideError. Every other input agrees (exhaustive for 8-bit, edge grids for wider types). Internal API; possibly intended." }
]

end JuliaLean.ReinterpretArrays
