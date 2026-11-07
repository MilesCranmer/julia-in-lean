import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.deleteat_filter
import JuliaLean.Proofs.base.array.deleteat_splice

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesDeleteat1 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-deleteat-index", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(::Vector, i::Integer)", "_deleteat!(a, i, delta)"],
    statement := "deleteat!(a, i) for an index of any BitInteger type throws InexactError when Int(i) fails and BoundsError outside 1:length(a), leaving a unchanged, and otherwise removes exactly a[i], the other elements keeping their order, in a valid vector.",
    source := "base/array.jl:1875-1893 (deleteat! docstring),1894-1898,1307-1322",
    status := .proven, prop := ``DeleteatIndexSpec, thm := some ``deleteatIndexSpec}
]
def entriesDeleteat2 : List JuliaLean.Registry.Entry := [
  { id := "array-filter-bang-native-axes", juliaFile := "base/array.jl",
    juliaFns := ["filter!(f, a::AbstractVector)"],
    statement := "For native-Int-axis mutable vectors supporting indexed assignment and tail deletion, filter! keeps exactly the elements satisfying its Bool predicate, in order, and propagates predicate errors or an undefined slot. The domain includes an axis ending at typemax(Int).",
    source := "base/array.jl:3046-3075", status := .refuted,
    prop := ``JuliaLean.Proofs.base.array.round7.NativeAxisFilterBangSpec,
    thm := some ``JuliaLean.Proofs.base.array.round7.nativeAxisFilterBangSpec_refuted,
    issue := "none found (queries: issues filter! typemax(Int) BoundsError; issues filter! nextind overflow AbstractVector; PRs filter! nextind overflow AbstractVector)",
    notes := "Refuted by a native-Int max-axis counterexample: nextind at typemax(Int) wraps to typemin(Int), so the final tail deletion window is reversed and raises BoundsError. Reproducer: repro/array-filter-bang-native-axes.jl." },
  { id := "multidimcov-array-v2-deleteat-mask", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(a::Vector, inds::AbstractVector{Bool})", "_copy_item!(a::Vector, p, q)"],
    statement := "For representation-valid storage (pointer-free slots are assigned), deleteat!(a, mask) with length(mask) == length(a) leaves exactly the slots where mask is false, in order, unassigned slots included, in a valid vector; another length throws BoundsError with a unchanged.",
    source := "base/array.jl:1911-1939 (deleteat! docstring),1956-1963,2000-2010",
    status := .proven, prop := ``DeleteatMaskSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2DeleteatMask_proven},
  { id := "arrayops-deleteat-mask", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(::Vector, inds::AbstractVector{Bool})"],
    statement := "For representation-valid storage (pointer-free slots are assigned), deleteat!(a, mask) with a Bool vector of length(a) removes the entries marked true, keeping the others in order; another length throws BoundsError leaving a unchanged.",
    source := "base/array.jl:1911-1939 (deleteat! docstring),2000-2010",
    status := .proven, prop := ``DeleteatMaskSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayopsDeleteatMask_proven}
]
def entriesDeleteat4 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-deleteat-range-overflow", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(::Vector, ::AbstractUnitRange{<:Integer})"],
    statement := "`deleteat!(a::Vector, r::AbstractUnitRange{<:Integer})` (array.jl:1900; docstring at array.jl:1910-1939: \"Remove the items at the indices given by `inds`, and return the modified `a`. Subsequent items are shifted to fill the resulting gap.\") for a unit range of any `Integer` element type (`hi ≥ lo - 1`, the normalized stop) on a vector whose slots may be unassigned, with range.jl's `isempty`, `first` and checked `length` (`length(r)` is evaluated before `_deleteat!` starts) and the model's `_deleteat!`: an empty range returns `a` unchanged; otherwise a length that overflows raises `OverflowError`, a first index with no equal `Int` raises `InexactError`, a range inside `1:length(a)` removes exactly `a[lo:hi]` (the others, unassigned ones included, keeping their order) and returns `a`, and any other range raises `BoundsError`; no error changes `a`.",
    source := "base/array.jl:1900, array.jl:1910-1939", status := .refuted,
    prop := ``JuliaLean.Proofs.base.array.round4.DeleteatRangeSpec, thm := some ``JuliaLean.Proofs.base.array.round4.deleteatRangeSpec_refuted,
    issue := "#22055 closed (related)",
    notes := "expected refuted: the file states ¬ DeleteatRangeSpec (theorem deleteatRangeSpec_refuted); repro/arrayops-deleteat-range-overflow.jl" },
  { id := "arrayops-splice-convert-undef", juliaFile := "base/array.jl",
    juliaFns := ["splice!(::Vector, ::AbstractUnitRange{<:Integer}, ins)"],
    statement := "`splice!(a::Vector, r::AbstractUnitRange{<:Integer}, ins)` (array.jl:2120; docstring at array.jl:2061-2096) on a vector whose slots may be unassigned, with an in-bounds `UnitRange{Int}` `lo:hi` (`hi ≥ lo - 1`, an empty range inserting before `lo`) and range.jl's checked `length`: when some replacement value cannot be converted to the element type (`a[f+k-1] = x`, the Array `setindex!` with `convert(T, x)`, any user conversion), the call raises the error of the first such value, in the order of `ins`. Nothing is promised about `a` after the error.",
    source := "base/array.jl:2061-2096, array.jl:2120", status := .todo,
    prop := ``SpliceErrorAssigned, thm := none,
    notes := "Statement/prose mismatch: SpliceErrorAssigned requires every slot to remain assigned after any error; the registered prose expressly promises nothing about post-error state. The returned conversion-failure witness leaves an unassigned slot, which is permitted here, and does not contradict propagation of the first conversion error." }
]
def entriesDeleteat5 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-deleteat-internal", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(a::Vector, inds)", "deleteat!(a::Vector, inds::AbstractVector)", "_push_deleted!(dltd, a::Vector, ind)", "_deleteat!(a::Vector, inds, dltd=Nowhere())", "splice!(a::Vector, inds)"],
    statement := "For representation-valid storage (pointer-free slots are assigned) and strictly increasing Int indices inside 1:length(a), deleteat!(a, inds) keeps exactly the other slots in order (unassigned included) and splice!(a, inds) also returns a fresh vector of the removed slots in order; a first index outside 1:length(a) or a later one above length(a) raises BoundsError and a later index not above its predecessor raises ArgumentError.",
    source := "base/array.jl:1903-1997,2083-2148 (deleteat!/splice! docstrings)", status := .proven, prop := ``DeleteatIndicesSpec, thm := some ``JuliaLean.ChatGPT.Batch5.Group3.MultidimcovArrayV2DeleteatInternal_proven },
  { id := "multidimcov-array-v2-splice-index", juliaFile := "base/array.jl",
    juliaFns := ["splice!(a::Vector, i::Integer, ins=_default_splice)"],
    statement := "splice!(a, i, ins) for an Int index raises BoundsError outside 1:length(a) and UndefRefError for an unassigned a[i], with nothing changed; otherwise with all replacements converting it returns a[i] and leaves a[1:i-1], the converted replacements, then a[i+1:end]; a failing conversion raises its error.",
    source := "base/array.jl:2015-2081 (splice! docstring)", status := .proven, prop := ``SpliceIndexSpec, thm := some ``JuliaLean.Proofs.base.array.solArrayGrow.spliceIndexSpec },
  { id := "multidimcov-array-v2-splice-range", juliaFile := "base/array.jl",
    juliaFns := ["splice!(a::Vector, r::AbstractUnitRange{<:Integer}, ins=_default_splice)"],
    statement := "splice!(a, lo:hi, ins) for an Int range raises BoundsError for a nonempty range outside 1:length(a) (nothing changed) and for an insertion point n:n-1 outside 1:length(a)+1 with replacements; otherwise with all replacements converting it returns a fresh vector of a[lo:hi] and leaves a[1:lo-1], the converted replacements, then a[hi+1:end].",
    source := "base/array.jl:2083-2146 (splice! docstring)", status := .proven, prop := ``SpliceRangeSpec, thm := some ``ChatGPTBatch1.Splice.MultidimcovArrayV2SpliceRange_proven },
  { id := "arrayops-deleteat-range-inbounds", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(a::Vector, r::AbstractUnitRange{<:Integer})"],
    statement := "deleteat!(a, lo:hi) with Int-valued endpoints of any BitInteger type does nothing for an empty range, removes exactly a[lo:hi] for 1 <= lo <= hi <= length(a), and raises BoundsError with a unchanged for a nonempty range outside 1:length(a) whose length is representable.",
    source := "base/array.jl:1871-1909 (deleteat! docstring)", status := .proven, prop := ``DeleteatRangeInboundsSpec, thm := some ``JuliaLean.Proofs.base.array.solArrayGrow.deleteatRangeInboundsSpec }
]
def entriesDeleteat6 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-filter-array", juliaFile := "base/array.jl",
    juliaFns := ["filter(f, a::Array{T, N}) where {T, N}"],
    statement := "filter(f, a::Array) of any shape returns a fresh vector of the elements for which f is true, in order, existing arrays unchanged; otherwise the first element in iteration order that is unassigned (UndefRefError), makes f throw, or gives a non-Bool (TypeError) decides the error.",
    source := "base/array.jl:2990-3025 (filter docstring)", status := .proven, prop := ``FilterArraySpec, thm := some ``ChatGPTBatch1.ArrayFilter.MultidimcovArrayV2FilterArray_proven },
  { id := "multidimcov-array-v2-filter-bang", juliaFile := "base/array.jl",
    juliaFns := ["filter!(f, a::AbstractVector)"],
    statement := "`filter!(f, a::AbstractVector)` (array.jl:3061; docstring at array.jl:3046-3060: \"Update collection `a`, removing elements for which `f` is `false`\") for every `AbstractVector` (`EveryAbstractVector`: a `Vector` of the store, through its `resize!`/`sizehint!` branch, and any user vector type, through `deleteat!(a, j:lastindex(a))`) and any predicate `f` (its result: a `Bool`, an error, or a non-`Bool` value, `TypeError`): when every slot is assigned and `f` returns a `Bool` on every element, `a` ends holding, in order, the elements for which `f` is `true`; otherwise the first element on which `f` fails decides the error, and an unassigned slot read before any such failure raises `UndefRefError`.",
    source := "base/array.jl:3046-3060, array.jl:3061", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.round4.FilterBangSpec, thm := none,
    notes := "Incomplete runtime domain: EveryAbstractVector admits a valid stored native vector independently of layout.allocation, including none. A final sizehint! can then fail on absent metadata despite the success demand; that live-vector/metadata combination is not constructible Julia. Relate allocation to allocationSummary layout.runtime and retain native allocation errors. Returned finalization lemmas do not settle FilterBangSpec." },
  { id := "array-filter-abstractarray", juliaFile := "base/array.jl",
    juliaFns := ["filter(f, a::AbstractArray)"],
    statement := "`filter(f, a)` for an abstract array that is not an `Array` (array.jl:3027; docstring at array.jl:2990-3013: \"Return a copy of collection `a`, removing elements for which `f` is `false`\", with the example `filter(isodd, 1:10)`), for a unit range `lo:hi` of `Int`: when `f` returns a `Bool` for every element, the result is a fresh `Vector{Int}` holding, in order, the elements of the range for which `f` is `true`, the index buffer the call allocates ends empty, and every existing array is unchanged; otherwise the first element on which `f` throws (its error) or returns a non-`Bool` (`TypeError`) decides the error.",
    source := "base/array.jl:2990-3013, array.jl:3027", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.FilterAbstractArraySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayFilterAbstractarray_proven,
    notes := "" },
  { id := "array-filter-curried", juliaFile := "base/array.jl",
    juliaFns := ["filter(f)"],
    statement := "`filter(f)` (array.jl:3100; docstring at array.jl:3077-3099: \"Create a function that filters its arguments with function `f` using [`filter`](@ref), i.e. a function equivalent to `x -> filter(f, x)`.\") for every predicate and every collection type, with the installed model (`filterFix1`): calling the returned function on a collection is `filter(f, collection)`.",
    source := "base/array.jl:3077-3099, array.jl:3100", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.FilterCurriedSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayFilterCurried_proven,
    notes := "" }
]
def entriesDeleteat7 : List JuliaLean.Registry.Entry := [
{ id := "array-deleteat-index-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_deleteat!(a::Vector, i::Integer, delta::Integer)"],
  statement := "Delete-at converts the original index before observing length or comparing, converting or performing arithmetic on the original delta.",
  source := "base/array.jl:1307-1322", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion5.DeleteatIndexConversionFailures, thm := none,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesDeleteat8 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-filter-fix1", juliaFile := "base/array.jl", juliaFns := ["filter(f)"],
    statement := "filter(f) is Fix1(filter, f), a function equivalent to x -> filter(f, x): on an Array it meets the filter(f, a) contract.", source := "docstring base/array.jl:3077-3103", status := .proven,
    prop := ``CurriedFilterContents, thm := some ``curriedFilterContents }
]
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesDeleteat9 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-deleteat-index-range", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(::Vector, ::Integer)", "deleteat!(::Vector, ::AbstractUnitRange{<:Integer})", "empty!(::Vector)"],
    statement := "deleteat!(a, i) and deleteat!(a, lo:hi) inside 1:length(a) remove exactly those elements; an empty range changes nothing; an out-of-range index is a BoundsError; empty! removes everything.",
    source := "docstrings base/array.jl:1884, 2141", status := .todo, prop := ``DeleteIndexRangeContents,
    notes := "The old deletion proof uses a replacement slot-list model. The installed index, checked range length, deletion window and emptying contracts must be composed, retaining their native conversion and overflow behavior." },
  { id := "multidimcov-array-v2-keepat-indices", juliaFile := "base/array.jl",
    juliaFns := ["keepat!(a::Vector, inds)"],
    statement := "keepat!(a, inds) with assigned kept slots: sorted unique in-range indices leave a[inds]; in-range unsorted indices throw ArgumentError; sorted indices outside 1:n throw BoundsError.",
    source := "docstring base/array.jl:3110-3121", status := .todo, prop := ``KeptIndicesContents,
    notes := "The installed keepat loop needs retained-slot, unsorted-index and bounds-error proofs with source state threading; the old list-filter certificate does not establish them." }
]
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesDeleteat10 : List JuliaLean.Registry.Entry := [
{ id := "array-deleteat-mask-boundary", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(a::Vector, inds::AbstractVector{Bool})"],
    statement := "Live-mask deletion preserves effects of the two length observations and their comparison. Their errors propagate; a false comparison raises BoundsError before iteration or writes. Success returns the original array handle.",
    source := "base/array.jl:2000–2010; base/array.jl:1911–1939; error-order and identity invariants" , status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.DeleteatMaskBoundarySpec, thm := none,
    notes := "Uses actual copyItem and deleteend. Custom iteration and mask-length/comparison semantics remain explicit existing runtime interfaces." }
]
end JuliaLean.Proofs.base.array

