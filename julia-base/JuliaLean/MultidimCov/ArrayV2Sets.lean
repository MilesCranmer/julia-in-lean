import JuliaLean.MultidimCov.ArrayV2Core

/-!
Set-like operators on vectors (master `base/array.jl:3160-3221`) and the `Set` methods they
call (`base/abstractset.jl`, `base/set.jl`).

Every collection has the same element type `T`, so each `convert(T, x)` (in `push!` and in the
typed comprehension) is the identity, and element equality is `isequal` (`DecidableEq`). A
vector or other iterable is its list of elements in iteration order. A `Set{T}` is the list
of its elements without duplicates: Julia leaves its iteration order unspecified, and here it
is the list order; none of the results below depends on it. Arguments are values, so the
aliasing that `_DOCS_ALIASING_WARNING` excludes cannot occur. A closure that captures a
mutable `Set` (`_unique_filter!`) is a function of the element and the set's current value
that returns its result and the set's new value.
-/

namespace JuliaLean.MultidimCov.ArrayV2

variable {α : Type} [DecidableEq α]

/-- `push!(s::Set, x)`: `x` is added unless already present. -/
def setPush (s : List α) (x : α) : List α := if x ∈ s then s else s ++ [x]

/-- `delete!(s::Set, x)`: `x` is removed if present. -/
def setDelete (s : List α) (x : α) : List α := s.erase x

/-- `pop!(s::Set, x)` for an `x` in `s` (its only use below is guarded by `x ∈ s`, so the
`KeyError` for an absent key is never reached). -/
def setPop (s : List α) (x : α) : List α := s.erase x

/-- base/abstractset.jl:105 `union!(s::AbstractSet{T}, itr)`: `push!(s, x)` for each `x` in
`itr`. The `sizehint!` does not change the contents, and the `length(s) == max_values(T)`
break fires only when `s` already holds every value of `T`, after which pushes change nothing. -/
def setUnion (s : List α) (itr : List α) : List α := itr.foldl setPush s

/-- base/set.jl:47 `Set{T}(itr) = union!(Set{T}(), itr)`. -/
def mkSet (itr : List α) : List α := setUnion [] itr

/-- base/abstractset.jl:192-200 `intersect!(s::AbstractSet, itrs...)`: for each `itr`,
`intersect!(s, union!(emptymutable(s, eltype(itr)), itr))`, which is `filter!(in(s2), s)`
for the set `s2` of `itr`'s elements. -/
def setIntersectAll (s : List α) (itrs : List (List α)) : List α :=
  itrs.foldl (fun s itr => s.filter fun x => decide (x ∈ mkSet itr)) s

/-- base/abstractset.jl:244-255 `setdiff!(s::AbstractSet, itrs...)`: for each `itr`,
`for x in itr; delete!(s, x); end`. -/
def setDiffAll (s : List α) (itrs : List (List α)) : List α :=
  itrs.foldl (fun s itr => itr.foldl setDelete s) s

/-- One step of base/abstractset.jl:299 `symdiff!(s::AbstractSet, itr::AbstractSet)`:
`x in s ? delete!(s, x) : push!(s, x)`. -/
def setToggle (s : List α) (x : α) : List α := if x ∈ s then setDelete s x else setPush s x

/-- base/abstractset.jl:290-304 `symdiff!(s::AbstractSet, itrs...)`: for each `itr`,
`symdiff!(s, Set(itr))`, which toggles each element of `Set(itr)`. -/
def setSymdiffAll (s : List α) (itrs : List (List α)) : List α :=
  itrs.foldl (fun s itr => (mkSet itr).foldl setToggle s) s

/-- base/array.jl:3164 `_unique_filter!(pred, update!, state)`: the closure
`x -> if pred(x, state); update!(state, x); true; else false; end`. -/
def m3164 (pred : α → List α → Bool) (update : List α → α → List α) (x : α) (state : List α) :
    Bool × List α :=
  if pred x state then (true, update state x) else (false, state)

/-- base/array.jl:3174 `_grow_filter!(seen) = _unique_filter!(∉, push!, seen)`. -/
def m3174 : α → List α → Bool × List α := m3164 (fun x s => decide (x ∉ s)) setPush

/-- base/array.jl:3175 `_shrink_filter!(keep) = _unique_filter!(∈, pop!, keep)`. -/
def m3175 : α → List α → Bool × List α := m3164 (fun x s => decide (x ∈ s)) setPop

/-- `filter!(pred!, v)` and `[x for x in v if pred!(x)]` with a closure `pred!` over a set:
`pred!` is called on each element in order (the loop of `filter!`, `base/array.jl:3066`, whose
in-place mechanics `P3066` proves), the set's value threaded through the calls, and the
elements it accepts are kept in order. -/
def filterSt (p : α → List α → Bool × List α) : List α → List α → List α × List α
  | [], s => ([], s)
  | x :: xs, s =>
    let (b, s1) := p x s
    let (r, s2) := filterSt p xs s1
    (if b then x :: r else r, s2)

/-- base/abstractset.jl:636 `mapfilter(pred, f, itr, res)` with `f = push!` onto a vector:
`for x in itr; pred(x) && push!(res, x); end`. -/
def mapfilterPush (p : α → List α → Bool × List α) : List α → List α × List α → List α × List α
  | [], st => st
  | x :: xs, (v, s) =>
    let (b, s1) := p x s
    mapfilterPush p xs (if b then v ++ [x] else v, s1)

/-- base/array.jl:3177 `_grow!(pred!, v, itrs)`: `filter!(pred!, v)`, then
`mapfilter(pred!, push!, itr, v)` for each `itr`, returning `v` (paired with the final
value of the set captured by `pred!`). -/
def m3177 (p : α → List α → Bool × List α) (v : List α) (s : List α) (itrs : List (List α)) :
    List α × List α :=
  itrs.foldl (fun st itr => mapfilterPush p itr st) (filterSt p v s)

/-- base/array.jl:3185 `union!(v, itrs...) = _grow!(_grow_filter!(sizehint!(Set{T}(), length(v))), v, itrs)`. -/
def m3185 (v : List α) (itrs : List (List α)) : List α := (m3177 m3174 v [] itrs).1

/-- base/array.jl:3188
`symdiff!(v, itrs...) = _grow!(_shrink_filter!(symdiff!(Set{T}(), v, itrs...)), v, itrs)`. -/
def m3188 (v : List α) (itrs : List (List α)) : List α :=
  (m3177 m3175 v (setSymdiffAll [] (v :: itrs)) itrs).1

/-- base/array.jl:3191 `_shrink!(shrinker!, v, itrs)`: `seen = Set{eltype(v)}()`,
`filter!(_grow_filter!(seen), v)`, `shrinker!(seen, itrs...)`, `filter!(in(seen), v)`. -/
def m3191 (shrinker : List α → List (List α) → List α) (v : List α) (itrs : List (List α)) : List α :=
  let (v, seen) := filterSt m3174 v []
  let seen := shrinker seen itrs
  v.filter fun x => decide (x ∈ seen)

/-- base/array.jl:3198 `intersect!(v::AbstractVector, itrs...) = _shrink!(intersect!, v, itrs)`. -/
def m3198 (v : List α) (itrs : List (List α)) : List α := m3191 setIntersectAll v itrs

/-- base/array.jl:3199 `setdiff!(v::AbstractVector, itrs...) = _shrink!(setdiff!, v, itrs)`. -/
def m3199 (v : List α) (itrs : List (List α)) : List α := m3191 setDiffAll v itrs

/-- base/array.jl:3201 `vectorfilter(T::Type, f, v) = T[x for x in v if f(x)]`, for a closure
`f` over a set whose value is `s`. -/
def m3201 (f : α → List α → Bool × List α) (s : List α) (v : List α) : List α := (filterSt f v s).1

/-- base/array.jl:3203 `intersect(itr, itrs...)`: `keep = intersect!(Set{T}(itr), itrs...)`,
`vectorfilter(T, _shrink_filter!(keep), itr)`. -/
def m3203 (itr : List α) (itrs : List (List α)) : List α :=
  m3201 m3175 (setIntersectAll (mkSet itr) itrs) itr

/-- base/array.jl:3209 `setdiff(itr, itrs...)`: `keep = setdiff!(Set{T}(itr), itrs...)`,
`vectorfilter(T, _shrink_filter!(keep), itr)`. -/
def m3209 (itr : List α) (itrs : List (List α)) : List α :=
  m3201 m3175 (setDiffAll (mkSet itr) itrs) itr

/-- base/array.jl:3215 `intersect(v::AbstractVector, r::AbstractRange)`:
`common = Iterators.filter(in(r), v)`, `seen = Set{T}(common)`,
`vectorfilter(T, _shrink_filter!(seen), common)`. A range is its elements in order and `in(r)`
is membership (for integer ranges `==` agrees with `isequal`). -/
def m3215 (v r : List α) : List α :=
  let common := v.filter fun x => decide (x ∈ r)
  m3201 m3175 (mkSet common) common

/-- base/array.jl:3221 `intersect(r::AbstractRange, v::AbstractVector) = intersect(v, r)`. -/
def m3221 (r v : List α) : List α := m3215 v r

end JuliaLean.MultidimCov.ArrayV2
