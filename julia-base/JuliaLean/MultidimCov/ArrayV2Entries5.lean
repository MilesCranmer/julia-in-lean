import JuliaLean.MultidimCov.ArrayV2FilterProps
import JuliaLean.MultidimCov.ArrayV2SetsProps
import JuliaLean.MultidimCov.ArrayV2Indcopy
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayV2

open JuliaLean.Registry

private def entry (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String := "") : Entry :=
  { id := s!"multidimcov-array-v2-{id}", juliaFile := "base/array.jl", juliaFns := fns,
    statement, source, status := .proven, prop, thm := some thm, notes }

private def refuted (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (issue notes : String) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := fns, statement, source, status := .refuted,
    prop, thm := some thm, issue, notes }

private def pending (id : String) (fns : List String) (statement source : String)
    (prop : Lean.Name) (issue notes : String) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := fns, statement, source, status := .todo,
    prop, issue, notes }

def entries5 : List Entry := [
  entry "filter-array" ["filter(f, a::Array{T, N}) where {T, N}"]
    "filter(f, a) on an Array of any shape returns a new Vector holding, in order, the elements for which f is true; an #undef element (UndefRefError), a non-Bool result of f (TypeError) and an exception of f are errors, met in iteration order."
    "docstring base/array.jl:2995-3018" ``P3020 ``p3020,
  entry "filter-bang" ["filter!(f, a::AbstractVector)"]
    "filter!(f, a) updates a to hold, in order, the elements for which f is true and returns it, through resize!/sizehint! for a Vector and deleteat!(a, j:lastindex(a)) otherwise; errors as for filter."
    "docstring base/array.jl:3048-3063" ``P3066 ``p3066
    "The deleteat! branch for vector types other than Vector assumes the deleteat!(a, lo:hi) contract (DelRangeOK).",
  entry "filter-fix1" ["filter(f)"]
    "filter(f) is Fix1(filter, f), a function equivalent to x -> filter(f, x): on an Array it meets the filter(f, a) contract."
    "docstring base/array.jl:3077-3103" ``P3105 ``p3105,
  pending "multidimcov-filter-cartesian-empty" ["filter(f, a::AbstractArray)"]
    "filter(f, a) on any AbstractArray returns the elements for which f is true, in order, and throws when f throws or returns a non-Bool for some element."
    "docstring base/array.jl:2995-3018" ``P3032
    "none found (queries: filter TypeError empty, filter IndexCartesian, filter map AbstractArray{Bool}, filter empty view TypeError, filter non-linear empty, filter typeassert map, filter TypeError, filter view TypeError, filter SubArray, filter AbstractArray{Bool}, filter cartesian, filter empty array, filter IndexStyle, filter map typeassert)"
    "Historical counterexample: the empty Cartesian view throws TypeError on the earlier implementation. The target uses a Boolean destination; the full indexed linear and custom-array contracts remain unresolved.",
  entry "symdiff-vector" ["symdiff!(v::AbstractVector{T}, itrs...) where {T}", "_grow!(pred!, v::AbstractVector, itrs)",
      "_shrink_filter!(keep)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"]
    "symdiff!(v, itrs...) leaves in v the elements lying in an odd number of the arguments (each argument taken as a set), each once, in order of first appearance across v, itrs..."
    "symdiff docstring base/abstractset.jl:258-277; symdiff! docstring 281-289" ``P3188 ``p3188
    "The symdiff! docstring also says that for arrays the multiplicity of elements matters; the code and the symdiff example symdiff([1,2,1], [2,1,2]) == Int64[] treat each argument as a set, and the differential test agrees.",
  entry "intersect-bang-vector" ["intersect!(v::AbstractVector, itrs...)", "_shrink!(shrinker!::F, v::AbstractVector, itrs) where F",
      "_grow_filter!(seen)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"]
    "intersect!(v, itrs...) leaves in v the distinct elements of v that occur in every itr, in v's order."
    "intersect! docstring base/abstractset.jl:184-191" ``P3198 ``p3198,
  entry "setdiff-bang-vector" ["setdiff!(v::AbstractVector, itrs...)", "_shrink!(shrinker!::F, v::AbstractVector, itrs) where F",
      "_grow_filter!(seen)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"]
    "setdiff!(v, itrs...) leaves in v the distinct elements of v that occur in none of the itrs, in v's order."
    "setdiff docstring base/abstractset.jl:202-221; setdiff! docstring 225-243" ``P3199 ``p3199,
  entry "intersect-vector" ["intersect(itr, itrs...)", "vectorfilter(T::Type, f, v)", "_shrink_filter!(keep)",
      "_unique_filter!(pred::P, update!::U, state) where {P,U}"]
    "intersect(itr, itrs...) with a vector or tuple itr returns the elements occurring in every argument, each once, in the order they first appear in itr."
    "intersect docstring base/abstractset.jl:114-154" ``P3203 ``p3203,
  entry "setdiff-vector" ["setdiff(itr, itrs...)", "vectorfilter(T::Type, f, v)", "_shrink_filter!(keep)",
      "_unique_filter!(pred::P, update!::U, state) where {P,U}"]
    "setdiff(itr, itrs...) with a vector or tuple itr returns the elements of itr in none of the itrs, each once, in itr's order."
    "setdiff docstring base/abstractset.jl:202-221" ``P3209 ``p3209,
  entry "intersect-vector-range" ["intersect(v::AbstractVector, r::AbstractRange)", "vectorfilter(T::Type, f, v)",
      "_shrink_filter!(keep)"]
    "intersect(v, r) for a vector v and a range r returns the distinct elements of v that lie in r, in v's order."
    "intersect docstring base/abstractset.jl:114-154" ``P3215v ``p3215v
    "Elements compare with isequal in the Set and with == in in(r); the model takes them equal, as for integer ranges."
]

end JuliaLean.MultidimCov.ArrayV2
