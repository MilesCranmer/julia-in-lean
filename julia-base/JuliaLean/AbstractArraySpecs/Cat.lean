import JuliaLean.AbstractArraySpecs.Model

/-!
Model of the general `cat(A...; dims)` path of `base/abstractarray.jl` at
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`, lines 1833-1942, 2003-2056
and 2164-2189: `_cat_t`, `dims2cat`, `cat_size_shape`/`_cshp`, `cat_similar`,
`__cat`, `__cat_offset!`, `__cat_offset1!`, `_copy_or_fill!`, and the front ends
`cat`, `vcat`, `hcat`, `typed_vcat`, `typed_hcat`, `cat_t` and `_cat`.

An argument is an array or any other value (`Item`). The output's element type `T`
is reached through `conv : α → R β` (`convert(T, x)` inside `setindex!`/`fill!`);
`zero` is `zero(T)`. The callees outside this file are modelled from master:
`A[inds...] = X` on an `Array` (base/array.jl:1063-1076 for one index,
base/multidimensional.jl:1046-1076 `_setindex!`/`_unsafe_setindex!` otherwise, with
`setindex_shape_check` from base/indices.jl:214-225), `fill!(view(A, inds...), x)`
(the view's `checkbounds`, then `convert(T, x)` once and a store in every cell), and
`Array{T}(undef, dims)` (base/boot.jl:812-850: `ArgumentError` for a negative or
overflowing dimension list).

The output is a 1-based `Array`: its shape and its cells in column-major order,
`none` for an uninitialized cell.
The current model restricts inputs to one Lean element type, assumes the default
`similar` allocation, and models stores into a 1-based `Array`. It does not model
heterogeneous promotion or custom `similar` and destination indexing methods.
-/

namespace JuliaLean.AbstractArraySpecs

/-- A `cat` argument: an array, or any other value (a number, a string, ...). -/
inductive Item (α : Type) where
  | arr (a : Arr α)
  | val (x : α)
  deriving DecidableEq, Repr

/-- `dims2cat(dims)` (base/abstractarray.jl:1898-1903); `maximum` of an empty
collection throws. -/
def dims2cat (dims : List Int) : R (List Bool) :=
  if dims.any (· ≤ 0) then .error .argumentError
  else match dims with
    | [] => .error .argumentError
    | d :: ds => .ok ((List.range (ds.foldl max d).toNat).map (fun (k : Nat) => dims.contains ((k : Int) + 1)))

/-- `dims2cat(::Val{dims}) = dims2cat(dims)` (line 1897); the `Val` parameter is the
list of dimensions. -/
def dims2catVal (dims : List Int) : R (List Bool) := dims2cat dims

/-- `Int + Bool`. -/
def boolI (b : Bool) : I64 := if b then i64 1 else i64 0

/-- `_cs(d, a, b)` (base/abstractarray.jl:1894-1895). -/
def cs (a b : I64) : R I64 := if a = b then .ok a else .error .dimensionMismatch

/-- `_cshp(ndim, dims, shape, nshape)` (base/abstractarray.jl:1872-1892), with fuel
for the simultaneous recursion on three tuples. -/
def cshp : Nat → List Bool → List I64 → List I64 → R (List I64)
  | 0, _, _, _ => .ok []
  | _ + 1, [], [], [] => .ok []
  | _ + 1, [], [], n => .ok n
  | _ + 1, d, [], [] => .ok (List.replicate d.length (i64 1))
  | f + 1, d :: ds, s :: ss, [] => do
      let rest ← cshp f ds ss []
      .ok ((s + boolI d) :: rest)
  | f + 1, _ :: ds, [], n :: ns => do
      let rest ← cshp f ds [] ns
      .ok (n :: rest)
  | f + 1, [], s :: ss, [] => do
      let _ ← cs s (i64 1)
      let rest ← cshp f [] ss []
      .ok (i64 1 :: rest)
  | f + 1, [], s :: ss, n :: ns => do
      let next ← cs s n
      let rest ← cshp f [] ss ns
      .ok (next :: rest)
  | f + 1, d :: ds, s :: ss, n :: ns => do
      let next ← if d then .ok (s + n) else cs s n
      let rest ← cshp f ds ss ns
      .ok (next :: rest)

def cshp' (dims : List Bool) (shape nshape : List I64) : R (List I64) :=
  cshp (dims.length + shape.length + nshape.length + 1) dims shape nshape

/-- `cat_size(A)` (lines 1836-1837): `(1,)` for a value, `size(A)` for an array. -/
def catSizeAll {α : Type} : Item α → List I64
  | .arr a => sizeA a
  | .val _ => [i64 1]

/-- `cat_size(A, d)` (lines 1838-1839) for the 0-based dimension `d`: 1 for a value,
`size(A, d)` for an array (1 past `ndims`). -/
def catSize {α : Type} : Item α → Nat → I64
  | .arr a, d => ((sizeA a)[d]?).getD (i64 1)
  | .val _, _ => i64 1

/-- `size(A, dim)` (lines 42-46) for any Julia `Integer` value `dim`: convert to
`Int` first, read `size(A)`, then tuple-index when `d <= length(s)`, else return 1.
The conversion can throw even when the dimension is past the array's rank. -/
def sizeDimFallback {α : Type} (A : Arr α) (dim : Int) : R I64 :=
  if dim < tmin ∨ tmax < dim then .error .inexactError
  else
    let d := i64 dim
    let s := sizeA A
    if d.val ≤ s.length then
      if d.val < 1 then .error .boundsError
      else match s[(d.val - 1).toNat]? with
        | some n => .ok n
        | none => .error .boundsError
    else .ok (i64 1)

/-- `cat_size(A::AbstractArray, d) = size(A, d)` (line 1839), including the integer
conversion and error behavior of `size(A, d)`. -/
def catSizeIntegerDim {α : Type} (A : Arr α) (dim : Int) : R I64 := sizeDimFallback A dim

/-- `cat_length` (lines 1841-1842): 1 for a value, `length(a)` for an array. -/
def catLength {α : Type} : Item α → I64
  | .arr a => lengthA a
  | .val _ => i64 1

/-- `cat_ndims` (lines 1844-1845): 0 for a value, `ndims(a)` for an array. -/
def catNdims {α : Type} : Item α → Nat
  | .arr a => a.axes.length
  | .val _ => 0

/-- `cat_indices(A, d)` (lines 1847-1848) for the 0-based dimension `d`: `OneTo(1)`
for a value, `axes(A, d)` for an array (`OneTo(1)` past `ndims`). -/
def catIndices {α : Type} : Item α → Nat → Ax
  | .arr a, d => (a.axes[d]?).getD (oneTo (i64 1))
  | .val _, _ => oneTo (i64 1)

/-- `cat_shape(dims, shapes::Tuple)` (lines 1859-1865): fold `_cshp(1, dims, out_shape,
s)` over the shapes from `()`. -/
def catShape (dims : List Bool) (shapes : List (List I64)) : R (List I64) :=
  shapes.foldlM (fun out s => cshp' dims out s) []

/-- `_cat_size_shape(dims, shape, X...)` (lines 1869-1870). -/
def catSizeShapeFrom {α : Type} (dims : List Bool) : List I64 → List (Item α) → R (List I64)
  | shape, [] => .ok shape
  | shape, x :: xs => do
      let s ← cshp' dims shape (catSizeAll x)
      catSizeShapeFrom dims s xs

/-- `cat_size_shape(dims, X...)` (lines 1867-1868). -/
def catSizeShape {α : Type} (dims : List Bool) : List (Item α) → R (List I64)
  | [] => .ok (List.replicate dims.length (i64 0))
  | x :: xs => do
      let s ← cshp' dims [] (catSizeAll x)
      catSizeShapeFrom dims s xs

/-- The output array: its shape and cells, `none` when uninitialized. -/
structure CatOut (β : Type) where
  shape : List I64
  cells : List (Option β)
  deriving DecidableEq, Repr

/-- `Core.checked_dims(d...)` (base/boot.jl:790-817) and the `Memory` constructor
check: `ArgumentError` for a dimension that is negative or `typemax(Int)`, or for a
product that overflows with no zero dimension. -/
def dimsInvalid (shape : List I64) : Bool :=
  shape.any (fun s => decide (s.val < 0) || decide (s.val = tmax)) ||
    (decide (tmax < (shape.map (fun s => s.val)).foldl (· * ·) 1) && !shape.any (fun s => s.val == 0))

/-- `Array{T}(undef, shape)` (base/boot.jl:821-850). -/
def arrayUndef {β : Type} (shape : List I64) : R (CatOut β) :=
  if dimsInvalid shape then .error .argumentError
  else .ok ⟨shape, List.replicate ((shape.map (fun s => s.val.toNat)).foldl (· * ·) 1) none⟩

/-- `cat_similar(A, ::Type{T}, shape::Tuple) = Array{T}(undef, shape)` (line 1850). -/
def catSimilarTuple {α β : Type} (_A : Item α) (shape : List I64) : R (CatOut β) := arrayUndef shape
/-- `cat_similar(A, ::Type{T}, shape::Vector) = Array{T}(undef, shape...)` (line 1851). -/
def catSimilarVector {α β : Type} (_A : Item α) (shape : List I64) : R (CatOut β) := arrayUndef shape
/-- `cat_similar(A::Array, ::Type{T}, shape::Tuple) = Array{T}(undef, shape)` (line 1852). -/
def catSimilarArrayTuple {α β : Type} (_A : Arr α) (shape : List I64) : R (CatOut β) := arrayUndef shape
/-- `cat_similar(A::Array, ::Type{T}, shape::Vector) = Array{T}(undef, shape...)` (line 1853). -/
def catSimilarArrayVector {α β : Type} (_A : Arr α) (shape : List I64) : R (CatOut β) := arrayUndef shape

/-- `similar(a::AbstractArray, ::Type{T}, dims::Dims{N}) = Array{T,N}(undef, dims)`
(line 834), which `similar(a, T, dims::DimOrInd...)` (line 823) reaches for `Int`s. -/
def similarDims {α β : Type} (_a : Arr α) (dims : List I64) : R (CatOut β) := arrayUndef dims

/-- `similar(a, T)` (line 820) calls `similar(a, T, axes(a))`: `OneTo` axes are
converted to lengths (lines 829-834). Other unit axes need a type-specific method;
without one, dispatch throws `MethodError`. -/
def similarDefault {α β : Type} (a : Arr α) : R (CatOut β) :=
  if a.axes.all (fun r => r.kind == .oneTo) then similarDims a (sizeA a)
  else .error .methodError

/-- `cat_similar(A::AbstractArray, T::Type, shape::Tuple) = similar(A, T, shape)` (line 1854). -/
def catSimilarAbsTuple {α β : Type} (A : Arr α) (shape : List I64) : R (CatOut β) := similarDims A shape
/-- `cat_similar(A::AbstractArray, T::Type, shape::Vector) = similar(A, T, shape...)` (line 1855). -/
def catSimilarAbsVector {α β : Type} (A : Arr α) (shape : List I64) : R (CatOut β) :=
  if shape.isEmpty then similarDefault A else similarDims A shape

/-- `cat_similar(X[1], T, shape)` with a tuple shape, dispatching on the argument: an
array (an `Array` or another `AbstractArray`, both allocating `Array{T}(undef, shape)`)
or a value. -/
def catSimilar {α β : Type} (x : Item α) (shape : List I64) : R (CatOut β) :=
  match x with
  | .arr a => catSimilarAbsTuple a shape
  | .val _ => catSimilarTuple x shape

/-- Integers `lo:hi`. -/
def rangeVals (lo hi : I64) : List I64 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun (k : Nat) => i64 (lo.val + (k : Int)))

/-- Tuples of `CartesianIndices(ranges)` in iteration (column-major) order. -/
def cartProd : List (List I64) → List (List I64)
  | [] => [[]]
  | r :: rs => (cartProd rs).flatMap (fun t => r.map (· :: t))

/-- Column-major position of a 1-based index tuple in an `Array` of the given shape. -/
def outPos : List I64 → List I64 → Int
  | [], _ => 0
  | i :: is, s :: ss => (i.val - 1) + s.val * outPos is ss
  | i :: is, [] => (i.val - 1) + outPos is []

/-- `_shapes_match(a, b)` (base/indices.jl:217-220). -/
def shapesMatch : List I64 → List I64 → Bool
  | [], [] => true
  | a, [] => a.all (· == i64 1)
  | [], b => b.all (· == i64 1)
  | a :: as, b :: bs => a == b && shapesMatch as bs

/-- `setindex_shape_check(X, shape)` (base/indices.jl:214-225): with one index or a
vector `X`, the element counts must agree, otherwise the shapes up to trailing ones. -/
def shapeCheck (xs js : List I64) : R Unit :=
  let agrees := if xs.length = 1 ∨ js.length = 1 then prodI xs == prodI js else shapesMatch xs js
  if agrees then .ok () else .error .dimensionMismatch

/-- `checkindex(Bool, OneTo(n), r::AbstractRange)` for a unit range `lo:hi`
(base/abstractarray.jl:756-757). -/
def checkindexRange (n : I64) (lo hi : I64) : Bool :=
  decide (hi < lo) || (checkindex (oneTo n) lo && checkindex (oneTo n) hi)

/-- `checkbounds(A, inds...)` for unit-range indices on the output `Array`. -/
def rangesInBounds {β : Type} (A : CatOut β) (inds : List (I64 × I64)) : Bool :=
  decide (inds.length = A.shape.length) && (inds.zip A.shape).all (fun p => checkindexRange p.2 p.1.1 p.1.2)

/-- Store `v` in the cell of every tuple. -/
def storeCells {β : Type} (A : CatOut β) (tuples : List (List I64)) (vs : List β) : List (Option β) :=
  (tuples.zip vs).foldl (fun cs tv => cs.set (outPos tv.1 A.shape).toNat (some tv.2)) A.cells

/-- `A[inds...] = x` on the `Array` output with unit-range indices: with one index,
base/array.jl:1063-1076 (`setindex_shape_check` before `checkbounds`); otherwise
base/multidimensional.jl `_setindex!` (`checkbounds`, then `setindex_shape_check`);
then `A[I] = x′[idx]` in `CartesianIndices(inds)` order along `x`'s iteration order,
each store converting with `convert(T, ·)`. -/
def setRanges {α β : Type} (conv : α → R β) (A : CatOut β) (inds : List (I64 × I64)) (x : Arr α) :
    R (CatOut β) := do
  let lens := inds.map (fun p => i64 1 + (p.2 - p.1))
  if inds.length = 1 then
    shapeCheck (sizeA x) lens
    if !rangesInBounds A inds then .error .boundsError
  else
    if !rangesInBounds A inds then .error .boundsError
    shapeCheck (sizeA x) lens
  let tuples := cartProd (inds.map (fun p => rangeVals p.1 p.2))
  let vs ← x.data.mapM conv
  .ok ⟨A.shape, storeCells A tuples vs⟩

/-- `fill!(view(A, inds...), x)`: the view's `checkbounds`, then `convert(T, x)` once
and a store in every cell of the box. -/
def fillRanges {α β : Type} (conv : α → R β) (A : CatOut β) (inds : List (I64 × I64)) (x : α) :
    R (CatOut β) := do
  if !rangesInBounds A inds then .error .boundsError
  let v ← conv x
  let tuples := cartProd (inds.map (fun p => rangeVals p.1 p.2))
  .ok ⟨A.shape, storeCells A tuples (tuples.map (fun _ => v))⟩

/-- `_copy_or_fill!(A, inds, x)` (lines 1941-1942): `fill!` for a value, `A[inds...] = x`
for an array. -/
def copyOrFill {α β : Type} (conv : α → R β) (A : CatOut β) (inds : List (I64 × I64)) : Item α → R (CatOut β)
  | .val x => fillRanges conv A inds x
  | .arr x => setRanges conv A inds x

/-- `__cat_offset1!(A, shape, catdims, offsets, x)` (base/abstractarray.jl:1930-1939). -/
def catOffset1 {α β : Type} (conv : α → R β) (A : CatOut β) (shape : List I64) (catdims : List Bool)
    (offsets : List I64) (x : Item α) : R (CatOut β × List I64) := do
  let isCat := fun (i : Nat) => catdims.getD i false
  let inds := (List.range offsets.length).map (fun i =>
    if isCat i then
      let r := catIndices x i
      (offsets.getD i (i64 0) + r.lo, offsets.getD i (i64 0) + r.hi)
    else (i64 1, shape.getD i (i64 0)))
  let A ← copyOrFill conv A inds x
  let newoffsets := (List.range offsets.length).map (fun i =>
    if isCat i then offsets.getD i (i64 0) + catSize x i else offsets.getD i (i64 0))
  .ok (A, newoffsets)

/-- `__cat_offset!(A, shape, catdims, offsets, x, X...)` and `__cat_offset!(A, shape,
catdims, offsets) = A` (lines 1923-1928). -/
def catOffset {α β : Type} (conv : α → R β) (A : CatOut β) (shape : List I64) (catdims : List Bool) :
    List I64 → List (Item α) → R (CatOut β)
  | _, [] => .ok A
  | offsets, x :: X => do
      let (A', newoffsets) ← catOffset1 conv A shape catdims offsets x
      catOffset conv A' shape catdims newoffsets X

/-- `__cat(A, shape, catdims, X...)` (line 1921). -/
def catInner {α β : Type} (conv : α → R β) (A : CatOut β) (shape : List I64) (catdims : List Bool)
    (X : List (Item α)) : R (CatOut β) :=
  catOffset conv A shape catdims (List.replicate shape.length (i64 0)) X

/-- `_cat_t(dims, T, X...)` (lines 1907-1915); `X[1]` throws `BoundsError` without
arguments. -/
def catT {α β : Type} (conv : α → R β) (zero : β) (dims : List Int) (X : List (Item α)) : R (CatOut β) := do
  let catdims ← dims2cat dims
  let shape ← catSizeShape catdims X
  let A ← match X with
    | [] => .error .boundsError
    | x :: _ => catSimilar x shape
  let A : CatOut β := if (catdims.filter id).length > 1 then { A with cells := A.cells.map (fun _ => some zero) } else A
  catInner conv A shape catdims X

/-- `cat_t(::Type{T}, X...; dims) = _cat_t(dims, T, X...)` (line 1918). -/
def catTKw {α β : Type} (conv : α → R β) (zero : β) (X : List (Item α)) (dims : List Int) : R (CatOut β) :=
  catT conv zero dims X

/-- `_cat(dims, X...) = _cat_t(dims, promote_eltypeof(X...), X...)` (line 1905): the
element type is the arguments' common type `α`, so stores need no conversion. -/
def catPromote {α : Type} (zero : α) (dims : List Int) (X : List (Item α)) : R (CatOut α) :=
  catT (fun x => .ok x) zero dims X

/-- `_cat(catdims, A::AbstractArray{T}...) = _cat_t(catdims, T, A...)` (line 2171). -/
def catSame {α : Type} (zero : α) (dims : List Int) (A : List (Arr α)) : R (CatOut α) :=
  catT (fun x => .ok x) zero dims (A.map .arr)

/-- `cat(A...; dims) = _cat(dims, A...)` (line 2169). -/
def catKw {α : Type} (zero : α) (X : List (Item α)) (dims : List Int) : R (CatOut α) := catPromote zero dims X

/-- `vcat(X...) = cat(X...; dims=Val(1))` (line 2003). -/
def vcatAny {α : Type} (zero : α) (X : List (Item α)) : R (CatOut α) := catKw zero X [1]
/-- `hcat(X...) = cat(X...; dims=Val(2))` (line 2053). -/
def hcatAny {α : Type} (zero : α) (X : List (Item α)) : R (CatOut α) := catKw zero X [2]
/-- `typed_vcat(::Type{T}, X...) = _cat_t(Val(1), T, X...)` (line 2055). -/
def typedVcatAny {α β : Type} (conv : α → R β) (zero : β) (X : List (Item α)) : R (CatOut β) := catT conv zero [1] X
/-- `typed_hcat(::Type{T}, X...) = _cat_t(Val(2), T, X...)` (line 2056). -/
def typedHcatAny {α β : Type} (conv : α → R β) (zero : β) (X : List (Item α)) : R (CatOut β) := catT conv zero [2] X

/-- `vcat(A::AbstractArray) = cat(A; dims=Val(1))` (line 2175). -/
def vcat1 {α : Type} (zero : α) (A : Arr α) : R (CatOut α) := catKw zero [.arr A] [1]
/-- `vcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(1))` (line 2176). -/
def vcat2 {α : Type} (zero : α) (A B : Arr α) : R (CatOut α) := catKw zero [.arr A, .arr B] [1]
/-- `vcat(A::AbstractArray...) = cat(A...; dims=Val(1))` (line 2177). -/
def vcatArrs {α : Type} (zero : α) (A : List (Arr α)) : R (CatOut α) := catKw zero (A.map .arr) [1]
/-- `vcat(A::Union{AbstractArray,Number}...) = cat(A...; dims=Val(1))` (line 2178). -/
def vcatMixed {α : Type} (zero : α) (A : List (Item α)) : R (CatOut α) := catKw zero A [1]
/-- `hcat(A::AbstractArray) = cat(A; dims=Val(2))` (line 2179). -/
def hcat1 {α : Type} (zero : α) (A : Arr α) : R (CatOut α) := catKw zero [.arr A] [2]
/-- `hcat(A::AbstractArray, B::AbstractArray) = cat(A, B; dims=Val(2))` (line 2180). -/
def hcat2 {α : Type} (zero : α) (A B : Arr α) : R (CatOut α) := catKw zero [.arr A, .arr B] [2]
/-- `hcat(A::AbstractArray...) = cat(A...; dims=Val(2))` (line 2181). -/
def hcatArrs {α : Type} (zero : α) (A : List (Arr α)) : R (CatOut α) := catKw zero (A.map .arr) [2]
/-- `hcat(A::Union{AbstractArray,Number}...) = cat(A...; dims=Val(2))` (line 2182). -/
def hcatMixed {α : Type} (zero : α) (A : List (Item α)) : R (CatOut α) := catKw zero A [2]

/-- `typed_vcat(T::Type, A::AbstractArray) = _cat_t(Val(1), T, A)` (line 2184). -/
def typedVcat1 {α β : Type} (conv : α → R β) (zero : β) (A : Arr α) : R (CatOut β) := catT conv zero [1] [.arr A]
/-- `typed_vcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(1), T, A, B)` (line 2185). -/
def typedVcat2 {α β : Type} (conv : α → R β) (zero : β) (A B : Arr α) : R (CatOut β) :=
  catT conv zero [1] [.arr A, .arr B]
/-- `typed_vcat(T::Type, A::AbstractArray...) = _cat_t(Val(1), T, A...)` (line 2186). -/
def typedVcatArrs {α β : Type} (conv : α → R β) (zero : β) (A : List (Arr α)) : R (CatOut β) :=
  catT conv zero [1] (A.map .arr)
/-- `typed_hcat(T::Type, A::AbstractArray) = _cat_t(Val(2), T, A)` (line 2187). -/
def typedHcat1 {α β : Type} (conv : α → R β) (zero : β) (A : Arr α) : R (CatOut β) := catT conv zero [2] [.arr A]
/-- `typed_hcat(T::Type, A::AbstractArray, B::AbstractArray) = _cat_t(Val(2), T, A, B)` (line 2188). -/
def typedHcat2 {α β : Type} (conv : α → R β) (zero : β) (A B : Arr α) : R (CatOut β) :=
  catT conv zero [2] [.arr A, .arr B]
/-- `typed_hcat(T::Type, A::AbstractArray...) = _cat_t(Val(2), T, A...)` (line 2189). -/
def typedHcatArrs {α β : Type} (conv : α → R β) (zero : β) (A : List (Arr α)) : R (CatOut β) :=
  catT conv zero [2] (A.map .arr)

/-- The same array with every axis replaced by `OneTo(length)`. -/
def rebase {α : Type} (A : Arr α) : Arr α := { A with axes := A.axes.map (fun r => oneTo (axLength r)) }

end JuliaLean.AbstractArraySpecs
