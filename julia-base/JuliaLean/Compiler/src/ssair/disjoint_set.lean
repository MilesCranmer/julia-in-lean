import JuliaLean.Compiler.src.ssair.ir

/-!
Source-mirrored model of `Compiler/src/ssair/disjoint_set.jl` at
f755f49a9e41380d7da126b3c1db9fe7f83dd027: the `IntDisjointSet` union-find that escape analysis
uses for its alias sets.

Modelling choices (see `JuliaLean/Compiler/src/ssair/ir.lean` for the shared conventions):

* `IntDisjointSet{T}` is modelled for `T = Int`, the only instance `EscapeAnalysis.jl` makes
  (`const AliasSet = IntDisjointSet{Int}`).
* The `@inbounds` reads in `find_root_impl!` and `_find_root_impl!` are checked reads in the
  model. On a set built only by `IntDisjointSet(n)`, `union!` and `push!` every parent is in
  `1:n`, so the checks never fire there.
* Recursion depth is bounded by a fuel argument; running out is `outOfBudget`.
-/

namespace JuliaLean.Compiler.ssair

/-- `mutable struct IntDisjointSet{T<:Integer}`.

Julia source: Compiler/src/ssair/disjoint_set.jl:36-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct IntDisjointSet{T<:Integer}
    parents::Vector{T}
    ranks::Vector{T}
    ngroups::T
end
```
-/
structure IntDisjointSet where
  parents : Array Int
  ranks : Array Int
  ngroups : Int
  deriving Repr, BEq, Inhabited

namespace IntDisjointSet

/-- `IntDisjointSet(n)`: every element is its own root with rank 0.

Julia source: Compiler/src/ssair/disjoint_set.jl:42
```julia
IntDisjointSet(n::T) where {T<:Integer} = IntDisjointSet{T}(collect(OneTo(n)), zeros(T, n), n)
```
-/
def new (n : Nat) : IntDisjointSet :=
  ⟨((List.range n).map fun (i : Nat) => (i : Int) + 1).toArray, Array.replicate n 0, n⟩

/-- `length(s::IntDisjointSet)`.

Julia source: Compiler/src/ssair/disjoint_set.jl:44
```julia
length(s::IntDisjointSet) = length(s.parents)
```
-/
def length (s : IntDisjointSet) : Nat := s.parents.size

/-- `num_groups(s)`.

Julia source: Compiler/src/ssair/disjoint_set.jl:51
```julia
num_groups(s::IntDisjointSet) = s.ngroups
```
-/
def numGroups (s : IntDisjointSet) : Int := s.ngroups

end IntDisjointSet

/-- `find_root_impl!` and its `@inbounds` twin `_find_root_impl!` (the same body): returns the
updated `parents` and the root, compressing the path from `x`.

Julia source: Compiler/src/ssair/disjoint_set.jl:56-71
```julia
function find_root_impl!(parents::Vector{T}, x::Integer) where {T<:Integer}
    p = parents[x]
    @inbounds if parents[p] ≠ p
        parents[x] = p = _find_root_impl!(parents, p)
    end
    return p
end

# unsafe version of the above
function _find_root_impl!(parents::Vector{T}, x::Integer) where {T<:Integer}
    @inbounds p = parents[x]
    @inbounds if parents[p] ≠ p
        parents[x] = p = _find_root_impl!(parents, p)
    end
    return p
end
```
-/
def findRootImpl : Nat → Array Int → Int → JM (Array Int × Int)
  | 0, _, _ => outOfBudget
  | fuel + 1, parents, x => do
    let p ← aget parents x
    if (← aget parents p) ≠ p then
      let (parents, r) ← findRootImpl fuel parents p
      let parents ← aset parents x r
      return (parents, r)
    else
      return (parents, p)

namespace IntDisjointSet

/-- `find_root!(s, x)`: the root of `x`'s subset, with path compression.

Julia source: Compiler/src/ssair/disjoint_set.jl:79
```julia
find_root!(s::IntDisjointSet{T}, x::T) where {T<:Integer} = find_root_impl!(s.parents, x)
```
-/
def findRoot (s : IntDisjointSet) (x : Int) : JM (IntDisjointSet × Int) := do
  let (parents, r) ← findRootImpl (s.parents.size + 1) s.parents x
  return ({ s with parents }, r)

/-- `in_same_set(s, x, y)`.

Julia source: Compiler/src/ssair/disjoint_set.jl:86
```julia
in_same_set(s::IntDisjointSet{T}, x::T, y::T) where {T<:Integer} = find_root!(s, x) == find_root!(s, y)
```
-/
def inSameSet (s : IntDisjointSet) (x y : Int) : JM (IntDisjointSet × Bool) := do
  let (s, rx) ← s.findRoot x
  let (s, ry) ← s.findRoot y
  return (s, rx == ry)

/-- `root_union!(s, x, y)` for roots `x ≠ y`: union by rank.

Julia source: Compiler/src/ssair/disjoint_set.jl:108-122
```julia
function root_union!(s::IntDisjointSet{T}, x::T, y::T) where {T<:Integer}
    parents = s.parents
    rks = s.ranks
    @inbounds xrank = rks[x]
    @inbounds yrank = rks[y]

    if xrank < yrank
        x, y = y, x
    elseif xrank == yrank
        rks[x] += one(T)
    end
    @inbounds parents[y] = x
    s.ngroups -= one(T)
    return x
end
```
-/
def rootUnion (s : IntDisjointSet) (x y : Int) : JM (IntDisjointSet × Int) := do
  let xrank ← aget s.ranks x
  let yrank ← aget s.ranks y
  let (x, y, ranks) ←
    if xrank < yrank then pure (y, x, s.ranks)
    else if xrank == yrank then do pure (x, y, ← aset s.ranks x (xrank + 1))
    else pure (x, y, s.ranks)
  let parents ← aset s.parents y x
  return ({ parents, ranks, ngroups := s.ngroups - 1 }, x)

/-- `union!(s, x, y)`: merge the subsets of `x` and `y`, returning the new root.

Julia source: Compiler/src/ssair/disjoint_set.jl:94-99
```julia
function union!(s::IntDisjointSet{T}, x::T, y::T) where {T<:Integer}
    parents = s.parents
    xroot = find_root_impl!(parents, x)
    yroot = find_root_impl!(parents, y)
    return xroot ≠ yroot ? root_union!(s, xroot, yroot) : xroot
end
```
-/
def union (s : IntDisjointSet) (x y : Int) : JM (IntDisjointSet × Int) := do
  let (s, xroot) ← s.findRoot x
  let (s, yroot) ← s.findRoot y
  if xroot ≠ yroot then s.rootUnion xroot yroot else return (s, xroot)

/-- `push!(s)`: a new singleton subset. `typemax(Int)` elements are out of reach, so the
`ArgumentError` branch is not modelled.

Julia source: Compiler/src/ssair/disjoint_set.jl:131-139
```julia
function push!(s::IntDisjointSet{T}) where {T<:Integer}
    l = length(s)
    l < typemax(T) || throw(ArgumentError(_intdisjointset_bounds_err_msg(T)))
    x = l + one(T)
    push!(s.parents, x)
    push!(s.ranks, zero(T))
    s.ngroups += one(T)
    return x
end
```
-/
def push (s : IntDisjointSet) : IntDisjointSet × Int :=
  let x : Int := s.parents.size + 1
  ({ parents := s.parents.push x, ranks := s.ranks.push 0, ngroups := s.ngroups + 1 }, x)

end IntDisjointSet

end JuliaLean.Compiler.ssair
