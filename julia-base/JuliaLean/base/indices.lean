import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.promotion
import JuliaLean.Runtime.Collections
import JuliaLean.base.range

/-!
# Model of `base/indices.jl`

Typed model of every method of `base/indices.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform (`Int === Int64`). Each method is a Lean definition whose docstring carries
the method's verbatim source (with the docstrings and comments that precede it); its body
follows the Julia body call by call.

* `Int` values are `JInt64` (`I64`); other BitIntegers are `JInt t`. A method on `Integer`
  takes its index at an arbitrary type `I` (any BitInteger, `BigInt` or user integer), with
  `convert(Int, i)` as a parameter. Tuples are lists, whose length is the tuple length;
  Julia's dispatch on tuple lengths is trusted.
* `@boundscheck checkbounds(...)` is modelled as executed (the default, outside `@inbounds`).
* `checkbounds`, `axes`, `length`, `size`, `eachindex`, `LogicalIndex`, `prod`, `print` (on an
  `IO` of a parameter type, threaded through the calls), `IOBuffer`, `takestring!`,
  `limitrepr`, `typeof` and the other functions of later-loaded files, and the range methods
  of `range.jl` (`first`, `last`, `length`, `==`, `getindex` and `convert` on `OneTo` and
  `UnitRange`, `range(...; length, step)`), are typed function parameters. For BitIntegers,
  `convert(Int, i)`, and `reinterpret(Int, i)`, `<` and `+` on `Int`, are the
  `JuliaLean.base.int` definitions.
* `BaseRange` is a value of `Base.OneTo{Int}` or `UnitRange{Int}` (range.jl); `AxisRange` adds
  this file's `Slice` and `IdentityUnitRange` wrappers of such ranges. `ArrayType` and the
  `PType` terms of `JuliaLean.base.promotion` are the types that `IndexStyle` and
  `promote_rule` dispatch on.
* Definitions marked *dispatch* select, for the argument kinds modelled here, the method Julia
  selects; they are not models of Julia code.
-/

namespace JuliaLean.base.indices

open JuliaLean JuliaLean.base.promotion

/-- Julia's `Int`. -/
abbrev I64 := JInt64

/-- The `Int` literal `n`. -/
def int (n : Int) : I64 := JInt.lit .i64 n

instance : Inhabited I64 := ⟨int 0⟩

/-- Exceptions thrown by the methods of this file and their callees. -/
inductive IndexError where
  | methodError (fn : String) (args : List String)
  | argumentError (message : String)
  | dimensionMismatch (message : String)
  | boundsError
  | core (error : JlError)
  deriving Repr, DecidableEq, Inhabited

/-- A Julia computation that may throw. -/
abbrev IndexResult (α : Type) := Except IndexError α

/-- An argument recorded in a `MethodError`: a type, or a value of the argument type `V`. -/
inductive MethodArg (V : Type) where
  | type (name : String)
  | value (v : V)
  deriving Repr, DecidableEq

/-- `MethodError(f, args)`: the function's name and the argument tuple, kept as values. -/
structure MethodError (V : Type) where
  fn : String
  args : List (MethodArg V)
  deriving Repr, DecidableEq

/-- One argument of a `LazyString`: a string, or a type rendered when the string is printed. -/
inductive LazyPart where
  | string (s : String)
  | type (t : PType)

/-- `LazyString(args...)`: the arguments, kept unprinted. -/
structure LazyString where
  parts : List LazyPart

/-- `ArgumentError(msg)` with a `LazyString` message. -/
structure LazyArgumentError where
  msg : LazyString

/-- A value of `Base.OneTo{Int}` or `UnitRange{Int}` (`base/range.jl`). -/
inductive BaseRange where
  | oneTo (stop : I64)
  | unitRange (start stop : I64)
  deriving Repr, DecidableEq

/-! ## Dimension and index tuple aliases -/

/--
Julia source: base/indices.jl:1-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

"""
    Dims{N}

An `NTuple` of `N` `Int`s used to represent the dimensions
of an [`AbstractArray`](@ref).
"""
Dims{N} = NTuple{N,Int}
```
-/
abbrev Dims := List I64

/--
Julia source: base/indices.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
DimsInteger{N} = NTuple{N,Integer}
```
-/
abbrev DimsInteger (t : IntTy) := List (JInt t)

/--
Julia source: base/indices.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Indices{N} = NTuple{N,AbstractUnitRange}
```
-/
abbrev Indices (R : Type) := List R

/-! ## Index styles -/

/--
Julia source: base/indices.jl:12-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## Traits for array types ##

abstract type IndexStyle end
```
-/
inductive IndexStyle where
  | linear
  | cartesian
  deriving Repr, DecidableEq, Inhabited

/--
Julia source: base/indices.jl:16-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    IndexLinear()

Subtype of [`IndexStyle`](@ref) used to describe arrays which
are optimally indexed by one linear index.

A linear indexing style uses one integer index to describe the position in the array
(even if it's a multidimensional array) and column-major
ordering is used to efficiently access the elements. This means that
requesting [`eachindex`](@ref) from an array that is `IndexLinear` will return
a simple one-dimensional range, even if it is multidimensional.

A custom array that reports its `IndexStyle` as `IndexLinear` only needs
to implement indexing (and indexed assignment) with a single `Int` index;
all other indexing expressions — including multidimensional accesses — will
be recomputed to the linear index.  For example, if `A` were a `2×3` custom
matrix with linear indexing, and we referenced `A[1, 3]`, this would be
recomputed to the equivalent linear index and call `A[5]` since `1 + 2*(3 - 1) = 5`.

See also [`IndexCartesian`](@ref).
"""
struct IndexLinear <: IndexStyle end
```
-/
def IndexLinear : IndexStyle := .linear

/--
Julia source: base/indices.jl:38-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    IndexCartesian()

Subtype of [`IndexStyle`](@ref) used to describe arrays which
are optimally indexed by a Cartesian index. This is the default
for new custom [`AbstractArray`](@ref) subtypes.

A Cartesian indexing style uses multiple integer indices to describe the position in
a multidimensional array, with exactly one index per dimension. This means that
requesting [`eachindex`](@ref) from an array that is `IndexCartesian` will return
a range of [`CartesianIndices`](@ref).

A `N`-dimensional custom array that reports its `IndexStyle` as `IndexCartesian` needs
to implement indexing (and indexed assignment) with exactly `N` `Int` indices;
all other indexing expressions — including linear indexing — will
be recomputed to the equivalent Cartesian location.  For example, if `A` were a `2×3` custom
matrix with cartesian indexing, and we referenced `A[5]`, this would be
recomputed to the equivalent Cartesian index and call `A[1, 3]` since `5 = 1 + 2*(3 - 1)`.

It is significantly more expensive to compute Cartesian indices from a linear index than it is
to go the other way.  The former operation requires division — a very costly operation — whereas
the latter only uses multiplication and addition and is essentially free. This asymmetry means it
is far more costly to use linear indexing with an `IndexCartesian` array than it is to use
Cartesian indexing with an `IndexLinear` array.

See also [`IndexLinear`](@ref).
"""
struct IndexCartesian <: IndexStyle end
```
-/
def IndexCartesian : IndexStyle := .cartesian

/-- The array types `IndexStyle(::Type)` dispatches on: `Union{}`, subtypes of `Array`,
`AbstractRange` and `LinearIndices`, and any other `AbstractArray` type, with its own
`IndexStyle` method (`some s`) or without one (`none`). -/
inductive ArrayType where
  | bottom
  | array
  | abstractRange
  | linearIndices
  | custom (style : Option IndexStyle)
  deriving Repr, DecidableEq

/--
Julia source: base/indices.jl:67-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    IndexStyle(A)
    IndexStyle(typeof(A))

`IndexStyle` specifies the "native indexing style" for array `A`. When
you define a new [`AbstractArray`](@ref) type, you can choose to implement
either linear indexing (with [`IndexLinear`](@ref)) or cartesian indexing.
If you decide to only implement linear indexing, then you must set this trait for your array
type:

    Base.IndexStyle(::Type{<:MyArray}) = IndexLinear()

The default is [`IndexCartesian()`](@ref).

Julia's internal indexing machinery will automatically (and invisibly)
recompute all indexing operations into the preferred style. This allows users
to access elements of your array using any indexing style, even when explicit
methods have not been provided.

If you define both styles of indexing for your `AbstractArray`, this
trait can be used to select the most performant indexing style. Some
methods check this trait on their inputs, and dispatch to different
algorithms depending on the most efficient access pattern. In
particular, [`eachindex`](@ref) creates an iterator whose type depends
on the setting of this trait.
"""
IndexStyle(A::AbstractArray) = IndexStyle(typeof(A))
```
-/
def IndexStyle_AbstractArray {A : Type} (typeof : A → ArrayType)
    (IndexStyle_Type : ArrayType → IndexStyle) (a : A) : IndexStyle :=
  IndexStyle_Type (typeof a)

/--
Julia source: base/indices.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{Union{}}) = IndexLinear()
```
-/
def IndexStyle_Type_Union : IndexStyle := IndexLinear

/--
Julia source: base/indices.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{Union{}}, slurp...) = throw(MethodError(IndexStyle, (Union{}, slurp...)))
```
-/
def IndexStyle_Type_Union_slurp {V α : Type} (slurp : List V) : Except (MethodError V) α :=
  .error ⟨"IndexStyle", .type "Union{}" :: slurp.map .value⟩

/--
Julia source: base/indices.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:AbstractArray}) = IndexCartesian()
```
-/
def IndexStyle_Type_AbstractArray : IndexStyle := IndexCartesian

/--
Julia source: base/indices.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:Array}) = IndexLinear()
```
-/
def IndexStyle_Type_Array : IndexStyle := IndexLinear

/--
Julia source: base/indices.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:AbstractRange}) = IndexLinear()
```
-/
def IndexStyle_Type_AbstractRange : IndexStyle := IndexLinear

/--
Julia source: base/indices.jl:100-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

IndexStyle(A::AbstractArray, B::AbstractArray) = IndexStyle(IndexStyle(A), IndexStyle(B))
```
-/
def IndexStyle_AbstractArray_AbstractArray {A : Type} (IndexStyle_A : A → IndexStyle)
    (IndexStyle_styles : IndexStyle → IndexStyle → IndexStyle) (a b : A) : IndexStyle :=
  IndexStyle_styles (IndexStyle_A a) (IndexStyle_A b)

/--
Julia source: base/indices.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(A::AbstractArray, B::AbstractArray...) = IndexStyle(IndexStyle(A), IndexStyle(B...))
```
-/
def IndexStyle_AbstractArray_Vararg {A : Type} (IndexStyle_A : A → IndexStyle)
    (IndexStyle_Bs : List A → IndexStyle)
    (IndexStyle_styles : IndexStyle → IndexStyle → IndexStyle) (a : A) (bs : List A) :
    IndexStyle :=
  IndexStyle_styles (IndexStyle_A a) (IndexStyle_Bs bs)

/--
Julia source: base/indices.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::IndexLinear, ::IndexLinear) = IndexLinear()
```
-/
def IndexStyle_IndexLinear_IndexLinear : IndexStyle := IndexLinear

/--
Julia source: base/indices.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::IndexStyle, ::IndexStyle) = IndexCartesian()
```
-/
def IndexStyle_IndexStyle_IndexStyle (_a _b : IndexStyle) : IndexStyle := IndexCartesian

/-! ## Shape promotion -/

/--
Julia source: base/indices.jl:105-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# array shape rules

promote_shape(::Tuple{}, ::Tuple{}) = ()
```
-/
def promote_shape_Tuple0_Tuple0 {α : Type} : List α := []

/-- The callees `throw_promote_shape_mismatch` makes on the elements of its tuples, which are
`Int`s or axes, and on the `IOBuffer` (of type `B`) it writes its message to. -/
structure ShapeCallees (A B : Type) where
  /-- `x isa Base.OneTo`. -/
  isOneTo : A → Bool
  /-- `x isa Int`. -/
  isInt : A → Bool
  /-- An `Int` stored in the tuple (the result of `lastindex`). -/
  ofInt : I64 → A
  lastindex : A → IndexResult I64
  firstindex : A → IndexResult I64
  /-- `x:y` on `Int`s. -/
  colon : I64 → I64 → IndexResult A
  /-- `IOBuffer()`. -/
  IOBuffer : B
  /-- `print(io, s)` for a string `s`. -/
  printString : B → String → B
  /-- `print(io, t)` for a tuple `t`. -/
  printTuple : B → List A → B
  /-- `print(io, i)` for an `Int` `i`. -/
  printInt : B → I64 → B
  /-- `takestring!(io)`. -/
  takestring : B → String

/--
Julia source: base/indices.jl:109-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Consistent error message for promote_shape mismatch, hiding type details like
# OneTo. When b ≡ nothing, it is omitted; i can be supplied for an index.
function throw_promote_shape_mismatch(a::Tuple, b::Union{Nothing,Tuple}, i = nothing)
    if a isa Tuple{Vararg{Base.OneTo}} && (b === nothing || b isa Tuple{Vararg{Base.OneTo}})
        a = map(lastindex, a)::Dims
        b === nothing || (b = map(lastindex, b)::Dims)
    end
    _has_axes = !(a isa Dims && (b === nothing || b isa Dims))
    if _has_axes
        _normalize(d) = map(x -> firstindex(x):lastindex(x), d)
        a = _normalize(a)
        b === nothing || (b = _normalize(b))
        _things = "axes "
    else
        _things = "size "
    end
    msg = IOBuffer()
    print(msg, "a has ", _things)
    print(msg, a)
    if b ≢ nothing
        print(msg, ", b has ", _things)
        print(msg, b)
    end
    if i ≢ nothing
        print(msg, ", mismatch at dim ", i)
    end
    throw(DimensionMismatch(takestring!(msg)))
end
```
-/
def throw_promote_shape_mismatch {A B : Type} (C : ShapeCallees A B) (a : List A)
    (b : Option (List A)) (i : Option I64 := none) : IndexResult Unit := do
  let (a, b) ←
    if a.all C.isOneTo && (b.isNone || (b.getD []).all C.isOneTo) then do
      let a := (← a.mapM C.lastindex).map C.ofInt
      let b ← match b with
        | none => pure none
        | some b => pure (some ((← b.mapM C.lastindex).map C.ofInt))
      pure (a, b)
    else pure (a, b)
  let _has_axes := !(a.all C.isInt && (b.isNone || (b.getD []).all C.isInt))
  let _normalize (d : List A) : IndexResult (List A) :=
    d.mapM fun x => do C.colon (← C.firstindex x) (← C.lastindex x)
  let (a, b, _things) ←
    if _has_axes then do
      let a ← _normalize a
      let b ← match b with
        | none => pure none
        | some b => pure (some (← _normalize b))
      pure (a, b, "axes ")
    else pure (a, b, "size ")
  let msg := C.IOBuffer
  let msg := C.printString (C.printString msg "a has ") _things
  let msg := C.printTuple msg a
  let msg := match b with
    | some b => C.printTuple (C.printString (C.printString msg ", b has ") _things) b
    | none => msg
  let msg := match i with
    | some i => C.printInt (C.printString msg ", mismatch at dim ") i
    | none => msg
  .error (.dimensionMismatch (C.takestring msg))

/--
Julia source: base/indices.jl:138-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function promote_shape(a::Tuple{Int,}, b::Tuple{Int,})
    a[1] != b[1] && throw_promote_shape_mismatch(a, b)
    return a
end
```
-/
def promote_shape_Int_Int {B : Type} (C : ShapeCallees I64 B) (a b : I64) : IndexResult I64 := do
  if a ≠ b then throw_promote_shape_mismatch C [a] (some [b])
  return a

/--
Julia source: base/indices.jl:143-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,})
    (a[1] != b[1] || a[2] != 1) && throw_promote_shape_mismatch(a, b)
    return a
end
```
-/
def promote_shape_IntInt_Int {B : Type} (C : ShapeCallees I64 B) (a : I64 × I64) (b : I64) :
    IndexResult (I64 × I64) := do
  if a.1 ≠ b ∨ a.2 ≠ int 1 then throw_promote_shape_mismatch C [a.1, a.2] (some [b])
  return a

/--
Julia source: base/indices.jl:148-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

promote_shape(a::Tuple{Int,}, b::Tuple{Int,Int}) = promote_shape(b, a)
```
-/
def promote_shape_Int_IntInt {B : Type} (C : ShapeCallees I64 B) (a : I64) (b : I64 × I64) :
    IndexResult (I64 × I64) :=
  promote_shape_IntInt_Int C b a

/--
Julia source: base/indices.jl:150-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function promote_shape(a::Tuple{Int, Int}, b::Tuple{Int, Int})
    (a[1] != b[1] || a[2] != b[2]) && throw_promote_shape_mismatch(a, b)
    return a
end
```
-/
def promote_shape_IntInt_IntInt {B : Type} (C : ShapeCallees I64 B) (a b : I64 × I64) :
    IndexResult (I64 × I64) := do
  if a.1 ≠ b.1 ∨ a.2 ≠ b.2 then throw_promote_shape_mismatch C [a.1, a.2] (some [b.1, b.2])
  return a

/--
Julia source: base/indices.jl:155-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    promote_shape(s1, s2)

Check two array shapes for compatibility, allowing trailing singleton dimensions, and return
whichever shape has more dimensions.

# Examples
```jldoctest
julia> a = fill(1, (3,4,1,1,1));

julia> b = fill(1, (3,4));

julia> promote_shape(a,b)
(Base.OneTo(3), Base.OneTo(4), Base.OneTo(1), Base.OneTo(1), Base.OneTo(1))

julia> promote_shape((2,3,1,4), (2, 3, 1, 4, 1))
(2, 3, 1, 4, 1)
```
"""
function promote_shape(a::Dims, b::Dims)
    if length(a) < length(b)
        return promote_shape(b, a)
    end
    for i=1:length(b)
        a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
    end
    for i=length(b)+1:length(a)
        a[i] != 1 && throw_promote_shape_mismatch(a, nothing, i)
    end
    return a
end
````
-/
def promote_shape_Dims {B : Type} (C : ShapeCallees I64 B) (a b : Dims) : IndexResult Dims :=
  if a.length < b.length then
    promote_shape_Dims C b a
  else do
    (List.range' 1 b.length).forM fun i =>
      if a[i - 1]! ≠ b[i - 1]! then throw_promote_shape_mismatch C a (some b) (some (int i))
      else pure ()
    (List.range' (b.length + 1) (a.length - b.length)).forM fun i =>
      if a[i - 1]! ≠ int 1 then throw_promote_shape_mismatch C a none (some (int i))
      else pure ()
    return a
termination_by if a.length < b.length then 1 else 0
decreasing_by simp_all; omega

/--
Julia source: base/indices.jl:187-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function promote_shape(a::AbstractArray, b::AbstractArray)
    promote_shape(axes(a), axes(b))
end
```
-/
def promote_shape_AbstractArray_AbstractArray {X R : Type} (axes : X → IndexResult (List R))
    (promote_shape_Indices : List R → List R → IndexResult (List R)) (a b : X) :
    IndexResult (List R) := do
  promote_shape_Indices (← axes a) (← axes b)

/--
Julia source: base/indices.jl:191-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function promote_shape(a::Indices, b::Indices)
    if length(a) < length(b)
        return promote_shape(b, a)
    end
    for i=1:length(b)
        a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
    end
    for i=length(b)+1:length(a)
        a[i] != 1:1 && throw_promote_shape_mismatch(a, nothing, i)
    end
    return a
end
```
-/
def promote_shape_Indices {R B : Type} [Inhabited R] (C : ShapeCallees R B) (eq : R → R → Bool)
    (a b : List R) : IndexResult (List R) :=
  if a.length < b.length then
    promote_shape_Indices C eq b a
  else do
    (List.range' 1 b.length).forM fun i =>
      if !eq a[i - 1]! b[i - 1]! then throw_promote_shape_mismatch C a (some b) (some (int i))
      else pure ()
    (List.range' (b.length + 1) (a.length - b.length)).forM fun i => do
      if !eq a[i - 1]! (← C.colon (int 1) (int 1)) then
        throw_promote_shape_mismatch C a none (some (int i))
    return a
termination_by if a.length < b.length then 1 else 0
decreasing_by simp_all; omega

/-! ## Indexed-assignment shape checks -/

/-- The callees of the `setindex_shape_check` methods on an array `X` and shape entries `I`. -/
structure SetindexCallees (X I : Type) where
  length : X → I64
  ndims : X → Nat
  size : X → List I64
  /-- `length(X) == i` (mixed-type `==`). -/
  eqLength : I64 → I → Bool
  prod : List I → I
  /-- `first(a) == first(b)` for a size entry and a shape entry. -/
  eqDim : I64 → I → Bool
  isoneDim : I64 → Bool
  isone : I → Bool
  showLength : I64 → String
  showIndex : I → String
  dims2stringSize : List I64 → String
  dims2string : List I → String

/--
Julia source: base/indices.jl:204-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function throw_setindex_mismatch(X, I)
    @noinline
    if length(I) == 1
        throw(DimensionMismatch("tried to assign $(length(X)) elements to $(I[1]) destinations"))
    else
        throw(DimensionMismatch("tried to assign $(dims2string(size(X))) array to $(dims2string(I)) destination"))
    end
end
```
-/
def throw_setindex_mismatch {X I α : Type} [Inhabited I] (C : SetindexCallees X I) (x : X)
    (I' : List I) : IndexResult α :=
  if I'.length = 1 then
    .error (.dimensionMismatch ("tried to assign " ++ C.showLength (C.length x) ++
      " elements to " ++ C.showIndex I'[0]! ++ " destinations"))
  else
    .error (.dimensionMismatch ("tried to assign " ++ C.dims2stringSize (C.size x) ++
      " array to " ++ C.dims2string I' ++ " destination"))

/--
Julia source: base/indices.jl:213-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

setindex_shape_check(X::AbstractArray, i::Integer) =
    (length(X)==i || throw_setindex_mismatch(X, (i,)))
```
-/
def setindex_shape_check_Integer {X I : Type} [Inhabited I] (C : SetindexCallees X I) (x : X)
    (i : I) : IndexResult Bool :=
  if C.eqLength (C.length x) i then pure true else throw_setindex_mismatch C x [i]

/--
Julia source: base/indices.jl:216-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

_shapes_match(::Tuple{}, ::Tuple{}) = true
```
-/
def _shapes_match_Tuple0_Tuple0 : Bool := true

/--
Julia source: base/indices.jl:218-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_shapes_match(a::Tuple, ::Tuple{}) = all(isone, a)
```
-/
def _shapes_match_Tuple_Tuple0 {A : Type} (isone : A → Bool) (a : List A) : Bool := a.all isone

/--
Julia source: base/indices.jl:219-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_shapes_match(::Tuple{}, b::Tuple) = all(isone, b)
```
-/
def _shapes_match_Tuple0_Tuple {B : Type} (isone : B → Bool) (b : List B) : Bool := b.all isone

/--
Julia source: base/indices.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_shapes_match(a::Tuple, b::Tuple) = first(a) == first(b) && _shapes_match(tail(a), tail(b))
```
-/
def _shapes_match {A B : Type} (eq : A → B → Bool) (isoneA : A → Bool) (isoneB : B → Bool) :
    List A → List B → Bool
  | [], [] => _shapes_match_Tuple0_Tuple0
  | a :: as, [] => _shapes_match_Tuple_Tuple0 isoneA (a :: as)
  | [], b :: bs => _shapes_match_Tuple0_Tuple isoneB (b :: bs)
  | a :: as, b :: bs => eq a b && _shapes_match eq isoneA isoneB as bs

/--
Julia source: base/indices.jl:221-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function setindex_shape_check(X::AbstractArray, shape::Tuple{Vararg{Integer}})
    matches = (ndims(X) == 1 || length(shape) == 1) ? length(X) == prod(shape) : _shapes_match(size(X), shape)
    matches || throw_setindex_mismatch(X, shape)
end
```
-/
def setindex_shape_check_Tuple {X I : Type} [Inhabited I] (C : SetindexCallees X I) (x : X)
    (shape : List I) : IndexResult Bool :=
  let matches_ := if C.ndims x = 1 ∨ shape.length = 1 then C.eqLength (C.length x) (C.prod shape)
    else _shapes_match C.eqDim C.isoneDim C.isone (C.size x) shape
  if matches_ then pure true else throw_setindex_mismatch C x shape

/--
Julia source: base/indices.jl:226-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

setindex_shape_check(::Any, ::Tuple) =
    throw(ArgumentError("indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?"))
```
-/
def setindex_shape_check_Any_Tuple {X I α : Type} (_x : X) (_shape : List I) : IndexResult α :=
  .error (.argumentError
    "indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?")

/-! ## Index conversion -/

/--
Julia source: base/indices.jl:229-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# convert to a supported index type (array or Int)
"""
    to_index(A, i)

Convert index `i` to an `Int` or array of indices to be used as an index into array `A`.

Custom array types may specialize `to_index(::CustomArray, i)` to provide
special indexing behaviors. Note that some index types (like `Colon`) require
more context in order to transform them into an array of indices; those get
converted in the more complicated `to_indices` function. By default, this
simply calls the generic `to_index(i)`. This must return either an `Int` or an
`AbstractArray` of scalar indices that are supported by `A`.
"""
to_index(A, i) = to_index(i)
```
-/
def to_index_A_i {A I O : Type} (to_index : I → IndexResult O) (_A : A) (i : I) :
    IndexResult O :=
  to_index i

/--
Julia source: base/indices.jl:244-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# This is ok for Array because values larger than
# typemax(Int) will BoundsError anyway
to_index(A::Array, i::UInt) = reinterpret(Int, i)
```
-/
def to_index_Array_UInt (i : JInt .u64) : I64 := JuliaLean.base.int.bitcast .i64 i rfl

/--
Julia source: base/indices.jl:248-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    to_index(i)

Convert index `i` to an `Int` or array of `Int`s to be used as an index for all arrays.

Custom index types may specialize `to_index(::CustomIndex)` to provide special
indexing behaviors. This must return either an `Int` or an `AbstractArray` of
`Int`s.
"""
to_index(i::Integer) = convert(Int,i)::Int
```
-/
def to_index_Integer {m : Type → Type} [Monad m] {Index Value : Type} (convertInt : Index → m Value)
    (assertInt : Value → m I64) (index : Index) : m I64 := do
  assertInt (← convertInt index)

/--
Julia source: base/indices.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i::Bool) = throw(ArgumentError("invalid index: $i of type Bool"))
```
-/
def to_index_Bool (i : Bool) : IndexResult I64 :=
  .error (.argumentError ("invalid index: " ++ toString i ++ " of type Bool"))

/--
Julia source: base/indices.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(I::AbstractArray{Bool}) = LogicalIndex(I)
```
-/
def to_index_AbstractArray_Bool {M L : Type} (LogicalIndex : M → L) (I : M) : L := LogicalIndex I

/--
Julia source: base/indices.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(I::AbstractArray) = I
```
-/
def to_index_AbstractArray {M : Type} (I : M) : M := I

/--
Julia source: base/indices.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(I::AbstractArray{Union{}}) = I
```
-/
def to_index_AbstractArray_Union {M : Type} (I : M) : M := I

/--
Julia source: base/indices.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(I::AbstractArray{<:Union{AbstractArray, Colon}}) =
    throw(ArgumentError(LazyString("invalid index: ", limitrepr(I), " of type ", typeof(I))))
```
-/
def to_index_AbstractArray_AbstractArray {M O : Type} (limitrepr : M → String) (typeof : M → PType)
    (I : M) : Except LazyArgumentError O :=
  .error ⟨⟨[.string "invalid index: ", .string (limitrepr I), .string " of type ", .type (typeof I)]⟩⟩

/--
Julia source: base/indices.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(::Colon) = throw(ArgumentError("colons must be converted by to_indices(...)"))
```
-/
def to_index_Colon : IndexResult I64 :=
  .error (.argumentError "colons must be converted by to_indices(...)")

/--
Julia source: base/indices.jl:266-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i) = throw(ArgumentError(LazyString("invalid index: ", limitrepr(i), " of type ", typeof(i))))
```
-/
def to_index_Any {I O : Type} (limitrepr : I → String) (typeof : I → PType) (i : I) :
    Except LazyArgumentError O :=
  .error ⟨⟨[.string "invalid index: ", .string (limitrepr i), .string " of type ", .type (typeof i)]⟩⟩

/-- `convert(Int, i)` for a BitInteger `i`: the `JuliaLean.base.int` definition. -/
def convert_Int_BitInteger {t : IntTy} (i : JInt t) : IndexResult I64 :=
  (JuliaLean.base.int.convert .i64 i).mapError IndexError.core

/-- *dispatch*: `to_index(i)` for a BitInteger `i`. -/
def to_index {t : IntTy} (i : JInt t) : IndexResult I64 := to_index_Integer convert_Int_BitInteger pure i

/-- *dispatch*: `to_index(A, i)` for an `Array` `A` and a BitInteger `i`: `UInt` (`UInt64`)
is reinterpreted, every other BitInteger goes through `to_index(A, i) = to_index(i)`. -/
def to_index_Array {A : Type} : (t : IntTy) → A → JInt t → IndexResult I64
  | .u64, _, i => .ok (to_index_Array_UInt i)
  | _, a, i => to_index_A_i to_index a i

/-! ## Index tuple conversion -/

/--
Julia source: base/indices.jl:267-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

# The general to_indices is mostly defined in multidimensional.jl, but this
# definition is required for bootstrap:
"""
    to_indices(A, I::Tuple)

Convert the tuple `I` to a tuple of indices for use in indexing into array `A`.

The returned tuple must only contain either `Int`s or `AbstractArray`s of
scalar indices that are supported by array `A`. It will error upon encountering
a novel index type that it does not know how to process.

For simple index types, it defers to the unexported `Base.to_index(A, i)` to
process each index `i`. While this internal function is not intended to be
called directly, `Base.to_index` may be extended by custom array or index types
to provide custom indexing behaviors.

More complicated index types may require more context about the dimension into
which they index. To support those cases, `to_indices(A, I)` calls
`to_indices(A, axes(A), I)`, which then recursively walks through both the
given tuple of indices and the dimensional indices of `A` in tandem. As such,
not all index types are guaranteed to propagate to `Base.to_index`.

# Examples
```jldoctest
julia> A = zeros(1,2,3,4);

julia> to_indices(A, (1,1,2,2))
(1, 1, 2, 2)

julia> to_indices(A, (1,1,2,20)) # no bounds checking
(1, 1, 2, 20)

julia> to_indices(A, (CartesianIndex((1,)), 2, CartesianIndex((3,4)))) # exotic index
(1, 2, 3, 4)

julia> to_indices(A, ([1,1], 1:2, 3, 4))
([1, 1], 1:2, 3, 4)

julia> to_indices(A, (1,2)) # no shape checking
(1, 2)
```
"""
to_indices(A, I::Tuple) = (@inline; _to_indices(A, _drop_zerodim(I), I))
````
-/
def to_indices_A_Tuple {A I O : Type}
    (_to_indices : A → List I → List I → IndexResult (List O))
    (_drop_zerodim : List I → List I) (a : A) (I' : List I) : IndexResult (List O) :=
  _to_indices a (_drop_zerodim I') I'

/--
Julia source: base/indices.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{Any}) = (@inline; to_indices(A, (eachindex(IndexLinear(), A),), I))
```
-/
def to_indices_A_Tuple1 {A I J O : Type} (eachindex : IndexStyle → A → J)
    (to_indices : A → List J → List I → IndexResult (List O)) (a : A) (i : I) :
    IndexResult (List O) :=
  to_indices a [eachindex IndexLinear a] [i]

/--
Julia source: base/indices.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_indices(A, ::Tuple, I::Tuple) = (@inline; to_indices(A, axes(A), I))
```
-/
def _to_indices_A_Tuple_Tuple {A I J O : Type} (axes : A → List J)
    (to_indices : A → List J → List I → IndexResult (List O)) (a : A) (_J : List I)
    (I' : List I) : IndexResult (List O) :=
  to_indices a (axes a) I'

/--
Julia source: base/indices.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_indices(A, J::Tuple{Any}, ::Tuple) = (@inline; to_indices(A, J))
```
-/
def _to_indices_A_Tuple1_Tuple {A I O : Type} (to_indices : A → List I → IndexResult (List O))
    (a : A) (J : I) (_I : List I) : IndexResult (List O) :=
  to_indices a [J]

/--
Julia source: base/indices.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_drop_zerodim(::Tuple{}) = ()
```
-/
def _drop_zerodim_Tuple0 {I : Type} : List I := []

/--
Julia source: base/indices.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_drop_zerodim(I::Tuple) = (@inline; (I[1], _drop_zerodim(tail(I))...))
```
-/
def _drop_zerodim {I : Type} : List I → List I
  | [] => _drop_zerodim_Tuple0
  | i :: rest => i :: _drop_zerodim rest

/--
Julia source: base/indices.jl:316-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# In simple cases, we know that we don't need to use axes(A), optimize those.
# Having this here avoids invalidations from multidimensional.jl: to_indices(A, I::Tuple{Vararg{Union{Integer, CartesianIndex}}})
to_indices(A, I::Tuple{}) = ()
```
-/
def to_indices_A_Tuple0 {A O : Type} (_a : A) : List O := []

/--
Julia source: base/indices.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{Vararg{Int}}) = I
```
-/
def to_indices_A_Ints {A : Type} (_a : A) (I' : List I64) : List I64 := I'

/--
Julia source: base/indices.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{Vararg{Integer}}) = (@inline; to_indices(A, (), I))
```
-/
def to_indices_A_Integers {A J I O : Type}
    (to_indices : A → List J → List I → IndexResult (List O)) (a : A) (I' : List I) :
    IndexResult (List O) :=
  to_indices a [] I'

/--
Julia source: base/indices.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, inds, ::Tuple{}) = ()
```
-/
def to_indices_A_inds_Tuple0 {A J O : Type} (_a : A) (_inds : List J) : List O := []

/--
Julia source: base/indices.jl:322-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, inds, I::Tuple{Any, Vararg}) =
    (@inline; (to_index(A, I[1]), to_indices(A, safe_tail(inds), tail(I))...))
```
-/
def to_indices_A_inds_Tuple {A J I O : Type} (to_index : A → I → IndexResult O)
    (safe_tail : List J → List J) (a : A) : List J → List I → IndexResult (List O)
  | inds, [] => pure (to_indices_A_inds_Tuple0 a inds)
  | inds, i :: rest => do
    let head ← to_index a i
    let tail ← to_indices_A_inds_Tuple to_index safe_tail a (safe_tail inds) rest
    pure (head :: tail)

/-! ## `Slice` and `IdentityUnitRange` -/

/--
Julia source: base/indices.jl:324-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    Slice(indices)

Represent an AbstractUnitRange of indices as a vector of the indices themselves,
with special handling to signal they represent a complete slice of a dimension (:).

Upon calling `to_indices`, Colons are converted to Slice objects to represent
the indices over which the Colon spans. Slice objects are themselves unit
ranges with the same indices as those they wrap. This means that indexing into
Slice objects with an integer always returns that exact integer, and they
iterate over all the wrapped indices, even supporting offset indices.
"""
struct Slice{T<:AbstractUnitRange} <: AbstractUnitRange{Int}
    indices::T
end
```
-/
structure Slice (T : Type) where
  indices : T
  deriving Repr, DecidableEq

/--
Julia source: base/indices.jl:355-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    IdentityUnitRange(range::AbstractUnitRange)

Represent an AbstractUnitRange `range` as an offset vector such that `range[i] == i`.

`IdentityUnitRange`s are frequently used as axes for offset arrays.
"""
struct IdentityUnitRange{T<:AbstractUnitRange} <: AbstractUnitRange{Int}
    indices::T
end
```
-/
structure IdentityUnitRange (T : Type) where
  indices : T
  deriving Repr, DecidableEq

/--
Julia source: base/indices.jl:340-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Slice(S::Slice) = S
```
-/
def Slice_Slice {T : Type} (S : Slice T) : Slice T := S

/--
Julia source: base/indices.jl:341-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Slice{T}(S::Slice) where {T<:AbstractUnitRange} = Slice{T}(T(S.indices))
```
-/
def Slice_T_Slice {T U : Type} (T_ctor : U → IndexResult T) (S : Slice U) :
    IndexResult (Slice T) := do
  pure ⟨← T_ctor S.indices⟩

/--
Julia source: base/indices.jl:342-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

axes(S::Slice) = (axes1(S),)
```
-/
def axes_Slice {T AX : Type} (axes1 : Slice T → AX) (S : Slice T) : List AX := [axes1 S]

/--
Julia source: base/indices.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(S::Slice) = IdentityUnitRange(S.indices)
```
-/
def axes1_Slice {T : Type} (S : Slice T) : IdentityUnitRange T := ⟨S.indices⟩

/--
Julia source: base/indices.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices
```
-/
def axes1_Slice_OneTo {T : Type} (S : Slice T) : T := S.indices

/--
Julia source: base/indices.jl:346-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

first(S::Slice) = first(S.indices)
```
-/
def first_Slice {T E : Type} (first : T → E) (S : Slice T) : E := first S.indices

/--
Julia source: base/indices.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(S::Slice) = last(S.indices)
```
-/
def last_Slice {T E : Type} (last : T → E) (S : Slice T) : E := last S.indices

/--
Julia source: base/indices.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(S::Slice) = (length(S.indices),)
```
-/
def size_Slice {T L : Type} (length : T → L) (S : Slice T) : List L := [length S.indices]

/--
Julia source: base/indices.jl:350-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(S::Slice, i::Int) = (@inline; @boundscheck checkbounds(S, i); i)
```
-/
def getindex_Slice_Int {T : Type} (checkbounds : Slice T → I64 → IndexResult Unit)
    (S : Slice T) (i : I64) : IndexResult I64 := do
  checkbounds S i
  pure i

/--
Julia source: base/indices.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(S::Slice, i::AbstractUnitRange{<:Integer}) = (@inline; @boundscheck checkbounds(S, i); i)
```
-/
def getindex_Slice_AbstractUnitRange {T I : Type} (checkbounds : Slice T → I → IndexResult Unit)
    (S : Slice T) (i : I) : IndexResult I := do
  checkbounds S i
  pure i

/--
Julia source: base/indices.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(S::Slice, i::StepRange{<:Integer}) = (@inline; @boundscheck checkbounds(S, i); i)
```
-/
def getindex_Slice_StepRange {T I : Type} (checkbounds : Slice T → I → IndexResult Unit)
    (S : Slice T) (i : I) : IndexResult I := do
  checkbounds S i
  pure i

/--
Julia source: base/indices.jl:353-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, r::Slice) = print(io, "Base.Slice(", r.indices, ")")
```
-/
def show_Slice {T IO : Type} (printString : IO → String → IO) (print : IO → T → IO) (io : IO)
    (r : Slice T) : IO :=
  printString (print (printString io "Base.Slice(") r.indices) ")"

/--
Julia source: base/indices.jl:354-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(S::Slice, s...) = iterate(S.indices, s...)
```
-/
def iterate_Slice {T S V : Type} (iterate : T → List S → Option (V × S)) (S' : Slice T)
    (s : List S) : Option (V × S) :=
  iterate S'.indices s

/--
Julia source: base/indices.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdentityUnitRange(S::IdentityUnitRange) = S
```
-/
def IdentityUnitRange_IdentityUnitRange {T : Type} (S : IdentityUnitRange T) :
    IdentityUnitRange T := S

/--
Julia source: base/indices.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdentityUnitRange{T}(S::IdentityUnitRange) where {T<:AbstractUnitRange} = IdentityUnitRange{T}(T(S.indices))
```
-/
def IdentityUnitRange_T_IdentityUnitRange {T U : Type} (T_ctor : U → IndexResult T)
    (S : IdentityUnitRange U) : IndexResult (IdentityUnitRange T) := do
  pure ⟨← T_ctor S.indices⟩

/--
Julia source: base/indices.jl:368-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# IdentityUnitRanges are offset and thus have offset axes, so they are their own axes
axes(S::IdentityUnitRange) = (axes1(S),)
```
-/
def axes_IdentityUnitRange {T AX : Type} (axes1 : IdentityUnitRange T → AX)
    (S : IdentityUnitRange T) : List AX :=
  [axes1 S]

/--
Julia source: base/indices.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(S::IdentityUnitRange) = S
```
-/
def axes1_IdentityUnitRange {T : Type} (S : IdentityUnitRange T) : IdentityUnitRange T := S

/--
Julia source: base/indices.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices
```
-/
def axes1_IdentityUnitRange_OneTo {T : Type} (S : IdentityUnitRange T) : T := S.indices

/--
Julia source: base/indices.jl:373-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

first(S::IdentityUnitRange) = first(S.indices)
```
-/
def first_IdentityUnitRange {T E : Type} (first : T → E) (S : IdentityUnitRange T) : E :=
  first S.indices

/--
Julia source: base/indices.jl:375-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(S::IdentityUnitRange) = last(S.indices)
```
-/
def last_IdentityUnitRange {T E : Type} (last : T → E) (S : IdentityUnitRange T) : E :=
  last S.indices

/--
Julia source: base/indices.jl:376-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(S::IdentityUnitRange) = (length(S.indices),)
```
-/
def size_IdentityUnitRange {T L : Type} (length : T → L) (S : IdentityUnitRange T) : List L :=
  [length S.indices]

/--
Julia source: base/indices.jl:377-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_length(S::IdentityUnitRange) = unsafe_length(S.indices)
```
-/
def unsafe_length_IdentityUnitRange {T L : Type} (unsafe_length : T → L)
    (S : IdentityUnitRange T) : L :=
  unsafe_length S.indices

/--
Julia source: base/indices.jl:378-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(S::IdentityUnitRange, i::Integer) = (@inline; @boundscheck checkbounds(S, i); convert(eltype(S), i))
```
-/
def getindex_IdentityUnitRange_Integer {T I : Type}
    (checkbounds : IdentityUnitRange T → I → IndexResult Unit)
    (convert_eltype : I → IndexResult I64) (S : IdentityUnitRange T) (i : I) :
    IndexResult I64 := do
  checkbounds S i
  -- `eltype(S)` is `Int` for every `IdentityUnitRange <: AbstractUnitRange{Int}`.
  convert_eltype i

/--
Julia source: base/indices.jl:379-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(S::IdentityUnitRange, i::Bool) = throw(ArgumentError("invalid index: $i of type Bool"))
```
-/
def getindex_IdentityUnitRange_Bool {T : Type} (_S : IdentityUnitRange T) (i : Bool) :
    IndexResult I64 :=
  .error (.argumentError ("invalid index: " ++ toString i ++ " of type Bool"))

/--
Julia source: base/indices.jl:380-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(S::IdentityUnitRange, i::AbstractUnitRange{<:Integer})
    @inline
    @boundscheck checkbounds(S, i)
    return convert(AbstractUnitRange{eltype(S)}, i)
end
```
-/
def getindex_IdentityUnitRange_AbstractUnitRange {T I O : Type}
    (checkbounds : IdentityUnitRange T → I → IndexResult Unit)
    (convert_AbstractUnitRange_Int : I → IndexResult O) (S : IdentityUnitRange T) (i : I) :
    IndexResult O := do
  checkbounds S i
  convert_AbstractUnitRange_Int i

/--
Julia source: base/indices.jl:385-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(S::IdentityUnitRange, i::AbstractUnitRange{Bool})
    @inline
    @boundscheck checkbounds(S, i)
    range(first(i) ? first(S) : last(S), length = last(i))
end
```
-/
def getindex_IdentityUnitRange_AbstractUnitRange_Bool {T I O : Type}
    (checkbounds : IdentityUnitRange T → I → IndexResult Unit) (firstT lastT : T → I64)
    (firstI lastI : I → Bool) (range_length : I64 → Bool → IndexResult O)
    (S : IdentityUnitRange T) (i : I) : IndexResult O := do
  checkbounds S i
  range_length (if firstI i then first_IdentityUnitRange firstT S
    else last_IdentityUnitRange lastT S) (lastI i)

/--
Julia source: base/indices.jl:390-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(S::IdentityUnitRange, i::StepRange{<:Integer})
    @inline
    @boundscheck checkbounds(S, i)
    return convert(AbstractRange{eltype(S)}, i)
end
```
-/
def getindex_IdentityUnitRange_StepRange {T I O : Type}
    (checkbounds : IdentityUnitRange T → I → IndexResult Unit)
    (convert_AbstractRange_Int : I → IndexResult O) (S : IdentityUnitRange T) (i : I) :
    IndexResult O := do
  checkbounds S i
  convert_AbstractRange_Int i

/--
Julia source: base/indices.jl:395-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(S::IdentityUnitRange, i::StepRange{Bool})
    @inline
    @boundscheck checkbounds(S, i)
    range(first(i) ? first(S) : last(S), length = last(i), step = Int(step(i)))
end
```
-/
def getindex_IdentityUnitRange_StepRange_Bool {T I S O : Type}
    (checkbounds : IdentityUnitRange T → I → IndexResult Unit) (firstT lastT : T → I64)
    (firstI lastI : I → Bool) (step : I → S) (Int : S → IndexResult I64)
    (range_length_step : I64 → Bool → I64 → IndexResult O) (S' : IdentityUnitRange T) (i : I) :
    IndexResult O := do
  checkbounds S' i
  let start := if firstI i then first_IdentityUnitRange firstT S'
    else last_IdentityUnitRange lastT S'
  let length := lastI i
  range_length_step start length (← Int (step i))

/--
Julia source: base/indices.jl:400-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Indexing with offset ranges should preserve the axes of the indices
# however, this is only really possible in general with OffsetArrays.
# In some cases, though, we may obtain correct results using Base ranges
# the following methods are added to allow OffsetArrays to dispatch on the first argument without ambiguities
function getindex(S::IdentityUnitRange{<:AbstractUnitRange{<:Integer}},
                    i::IdentityUnitRange{<:AbstractUnitRange{<:Integer}})
    @inline
    @boundscheck checkbounds(S, i)
    return i
end
```
-/
def getindex_IdentityUnitRange_IdentityUnitRange {T U : Type}
    (checkbounds : IdentityUnitRange T → IdentityUnitRange U → IndexResult Unit)
    (S : IdentityUnitRange T) (i : IdentityUnitRange U) : IndexResult (IdentityUnitRange U) := do
  checkbounds S i
  return i

/--
Julia source: base/indices.jl:410-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(S::Slice{<:AbstractUnitRange{<:Integer}},
                    i::IdentityUnitRange{<:AbstractUnitRange{<:Integer}})
    @inline
    @boundscheck checkbounds(S, i)
    return i
end
```
-/
def getindex_Slice_IdentityUnitRange {T U : Type}
    (checkbounds : Slice T → IdentityUnitRange U → IndexResult Unit)
    (S : Slice T) (i : IdentityUnitRange U) : IndexResult (IdentityUnitRange U) := do
  checkbounds S i
  return i

/--
Julia source: base/indices.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, r::IdentityUnitRange) = print(io, "Base.IdentityUnitRange(", r.indices, ")")
```
-/
def show_IdentityUnitRange {T IO : Type} (printString : IO → String → IO) (print : IO → T → IO)
    (io : IO) (r : IdentityUnitRange T) : IO :=
  printString (print (printString io "Base.IdentityUnitRange(") r.indices) ")"

/--
Julia source: base/indices.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(S::IdentityUnitRange, s...) = iterate(S.indices, s...)
```
-/
def iterate_IdentityUnitRange {T S V : Type} (iterate : T → List S → Option (V × S))
    (S' : IdentityUnitRange T) (s : List S) : Option (V × S) :=
  iterate S'.indices s

/--
Julia source: base/indices.jl:418-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# For AbstractOneTo, the values and indices of the values are identical, so this may be defined in Base.
# In general such an indexing operation would produce offset ranges
# This should also ideally return an AbstractUnitRange{eltype(S)}, but currently
# we're restricted to eltype(::IdentityUnitRange) == Int by definition
function getindex(S::AbstractOneTo{<:Integer}, I::IdentityUnitRange{<:AbstractUnitRange{<:Integer}})
    @inline
    @boundscheck checkbounds(S, I)
    return I
end
```
-/
def getindex_AbstractOneTo_IdentityUnitRange {T U : Type}
    (checkbounds : T → IdentityUnitRange U → IndexResult Unit) (S : T)
    (I' : IdentityUnitRange U) : IndexResult (IdentityUnitRange U) := do
  checkbounds S I'
  return I'

/-! ## `LinearIndices` -/

/--
Julia source: base/indices.jl:428-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    LinearIndices(A::AbstractArray)

Return a `LinearIndices` array with the same shape and [`axes`](@ref) as `A`,
holding the linear index of each entry in `A`. Indexing this array with
cartesian indices allows mapping them to linear indices.

For arrays with conventional indexing (indices start at 1), or any multidimensional
array, linear indices range from 1 to `length(A)`. However, for `AbstractVector`s
linear indices are `axes(A, 1)`, and therefore do not start at 1 for vectors with
unconventional indexing.

Calling this function is the "safe" way to write algorithms that
exploit linear indexing.

# Examples
```jldoctest
julia> A = fill(1, (5,6,7));

julia> b = LinearIndices(A);

julia> extrema(b)
(1, 210)
```

    LinearIndices(inds::CartesianIndices) -> R
    LinearIndices(sz::Dims) -> R
    LinearIndices((istart:istop, jstart:jstop, ...)) -> R

Return a `LinearIndices` array with the specified shape or [`axes`](@ref).

# Examples

The main purpose of this constructor is intuitive conversion
from cartesian to linear indexing:

```jldoctest
julia> linear = LinearIndices((1:3, 1:2))
3×2 LinearIndices{2, Tuple{UnitRange{Int64}, UnitRange{Int64}}}:
 1  4
 2  5
 3  6

julia> linear[1,2]
4
```
"""
struct LinearIndices{N,R<:NTuple{N,AbstractUnitRange{Int}}} <: AbstractArray{Int,N}
    indices::R
end
````
-/
structure LinearIndices (R : Type) where
  indices : List R
  deriving Repr, DecidableEq

/--
Julia source: base/indices.jl:479-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{LinearIndices{N,R}}, inds::LinearIndices{N}) where {N,R<:NTuple{N,AbstractUnitRange{Int}}} =
    LinearIndices{N,R}(convert(R, inds.indices))::LinearIndices{N,R}
```
-/
def convert_LinearIndices {R S : Type} (N : Nat)
    (convert_R : {l : List R // l.length = N} → IndexResult {l : List S // l.length = N})
    (inds : {L : LinearIndices R // L.indices.length = N}) :
    IndexResult {L : LinearIndices S // L.indices.length = N} := do
  let r ← convert_R ⟨inds.1.indices, inds.2⟩
  pure ⟨⟨r.1⟩, r.2⟩

/--
Julia source: base/indices.jl:481-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

LinearIndices(::Tuple{}) = LinearIndices{0,typeof(())}(())
```
-/
def LinearIndices_Tuple0 {R : Type} : LinearIndices R := ⟨[]⟩

/--
Julia source: base/indices.jl:483-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}}) where {N} =
    LinearIndices(map(r->convert(AbstractUnitRange{Int}, r), inds))
```
-/
def LinearIndices_AbstractUnitRanges {R S : Type}
    (convert_AbstractUnitRange_Int : R → IndexResult S) (inds : List R) :
    IndexResult (LinearIndices S) := do
  pure ⟨← inds.mapM convert_AbstractUnitRange_Int⟩

/-- An entry of the tuple `LinearIndices(inds)` accepts at `base/indices.jl:485`: an integer
of the `Integer` type `I` or an `AbstractUnitRange{<:Integer}`. -/
inductive IntegerOrRange (I R : Type) where
  | integer (n : I)
  | range (r : R)
  deriving Repr, DecidableEq

/--
Julia source: base/indices.jl:485-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}}) where {N} =
    LinearIndices(map(_convert2ind, inds))
```
-/
def LinearIndices_IntegerOrRanges {I R S T : Type} (_convert2ind : IntegerOrRange I R → S)
    (LinearIndices' : List S → IndexResult (LinearIndices T))
    (inds : List (IntegerOrRange I R)) : IndexResult (LinearIndices T) :=
  LinearIndices' (inds.map _convert2ind)

/--
Julia source: base/indices.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinearIndices(A::Union{AbstractArray,SimpleVector}) = LinearIndices(axes(A))
```
-/
def LinearIndices_AbstractArray {X R S : Type} (axes : X → List R)
    (LinearIndices_inds : List R → IndexResult (LinearIndices S)) (A : X) :
    IndexResult (LinearIndices S) :=
  LinearIndices_inds (axes A)

/--
Julia source: base/indices.jl:488-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

_convert2ind(i::Integer) = oneto(i)
```
-/
def _convert2ind_Integer {I S : Type} (oneto : I → S) (i : I) : S := oneto i

/--
Julia source: base/indices.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_convert2ind(ind::AbstractUnitRange) = first(ind):last(ind)
```
-/
def _convert2ind_AbstractUnitRange {R E S : Type} (first last : R → E) (colon : E → E → S)
    (ind : R) : S :=
  colon (first ind) (last ind)

/-- *dispatch*: `_convert2ind` on an entry of the tuple. -/
def _convert2ind {I R E S : Type} (oneto : I → S) (first last : R → E) (colon : E → E → S) :
    IntegerOrRange I R → S
  | .integer i => _convert2ind_Integer oneto i
  | .range ind => _convert2ind_AbstractUnitRange first last colon ind

/-- `Tuple{R, Vararg{R, N}}`: Julia writes a `Vararg` of known length out, so this is the tuple
type with the `N + 1` entries `R`. -/
def homogeneousTupleType (R : PType) (N : Nat) : PType :=
  .data tupleTypeName "Tuple" (List.replicate (N + 1) R) (some .any)

/-- `some (R, N)` when `T` is `Tuple{R, Vararg{R, N}}`: a tuple type with at least one entry,
every entry equal to the first, `R`, which is not itself a `Vararg`. -/
def homogeneousTupleParams : PType → Option (PType × Nat)
  | .data n _ (R :: rest) _ =>
    if n = tupleTypeName ∧ pIsVararg R = false ∧ rest.all (pEqual R) = true then
      some (R, rest.length)
    else none
  | _ => none

/-- `LinearIndices{N, R}`, a subtype of `AbstractArray{Int, N}`. -/
def linearIndicesType (N : Nat) (R : PType) : PType :=
  .data ⟨"Base", "LinearIndices"⟩ "LinearIndices" [.parameter (toString N), R] (some .any)

/-- `Base.Slice{T}` and `Base.IdentityUnitRange{T}`, subtypes of `AbstractUnitRange{Int}`. -/
def sliceType (T : PType) : PType := .data ⟨"Base", "Slice"⟩ "Base.Slice" [T] (some .any)
def identityUnitRangeType (T : PType) : PType :=
  .data ⟨"Base", "IdentityUnitRange"⟩ "Base.IdentityUnitRange" [T] (some .any)

/--
Julia source: base/indices.jl:491-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function indices_promote_type(::Type{Tuple{R1,Vararg{R1,N}}}, ::Type{Tuple{R2,Vararg{R2,N}}}) where {R1,R2,N}
    R = promote_type(R1, R2)
    return Tuple{R, Vararg{R, N}}
end
```
-/
def indices_promote_type (promote_type : PType → PType → PType) (R1 R2 : PType) (N : Nat) :
    PType :=
  let R := promote_type R1 R2
  homogeneousTupleType R N

/-- *dispatch*: `indices_promote_type(T1, T2)`. Its one method (`base/indices.jl:492`) takes two
tuple types `Tuple{R1, Vararg{R1, N}}` and `Tuple{R2, Vararg{R2, N}}` of the same length; for
any other arguments, such as `Tuple{}` or tuples of mixed entry types, Julia throws a
`MethodError` recording both. -/
def indices_promote_type_dispatch (promote_type : PType → PType → PType) (T1 T2 : PType) :
    Except (MethodError PType) PType :=
  match homogeneousTupleParams T1, homogeneousTupleParams T2 with
  | some (R1, N1), some (R2, N2) =>
    if N1 = N2 then .ok (indices_promote_type promote_type R1 R2 N1)
    else .error ⟨"indices_promote_type", [.value T1, .value T2]⟩
  | _, _ => .error ⟨"indices_promote_type", [.value T1, .value T2]⟩

/--
Julia source: base/indices.jl:496-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

promote_rule(::Type{LinearIndices{N,R1}}, ::Type{LinearIndices{N,R2}}) where {N,R1,R2} =
    LinearIndices{N,indices_promote_type(R1,R2)}
```
-/
def promote_rule_LinearIndices (promote_type : PType → PType → PType) (N : Nat)
    (R1 R2 : PType) : Except (MethodError PType) PType := do
  -- `R1` and `R2` are the tuple types `NTuple{N, …}` of the ranges.
  let R ← indices_promote_type_dispatch promote_type R1 R2
  pure (linearIndicesType N R)

/--
Julia source: base/indices.jl:499-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{Slice{T1}}, b::Type{Slice{T2}}) where {T1,T2} =
    el_same(promote_type(T1, T2), a, b)
```
-/
def promote_rule_Slice (promote_type : PType → PType → PType)
    (el_same : PType → PType → PType → PType) (T1 T2 : PType) : PType :=
  el_same (promote_type T1 T2) (sliceType T1) (sliceType T2)

/--
Julia source: base/indices.jl:501-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{IdentityUnitRange{T1}}, b::Type{IdentityUnitRange{T2}}) where {T1,T2} =
    el_same(promote_type(T1, T2), a, b)
```
-/
def promote_rule_IdentityUnitRange (promote_type : PType → PType → PType)
    (el_same : PType → PType → PType → PType) (T1 T2 : PType) : PType :=
  el_same (promote_type T1 T2) (identityUnitRangeType T1) (identityUnitRangeType T2)

/--
Julia source: base/indices.jl:503-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# AbstractArray implementation
IndexStyle(::Type{<:LinearIndices}) = IndexLinear()
```
-/
def IndexStyle_Type_LinearIndices : IndexStyle := IndexLinear

/--
Julia source: base/indices.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(iter::LinearIndices) = map(axes1, iter.indices)
```
-/
def axes_LinearIndices {R AX : Type} (axes1 : R → AX) (iter : LinearIndices R) : List AX :=
  iter.indices.map axes1

/--
Julia source: base/indices.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(iter::LinearIndices) = map(length, iter.indices)
```
-/
def size_LinearIndices {R : Type} (length : R → I64) (iter : LinearIndices R) : List I64 :=
  iter.indices.map length

/--
Julia source: base/indices.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isassigned(iter::LinearIndices, i::Int) = checkbounds(Bool, iter, i)
```
-/
def isassigned_LinearIndices {R : Type} (checkbounds_Bool : LinearIndices R → I64 → Bool)
    (iter : LinearIndices R) (i : I64) : Bool :=
  checkbounds_Bool iter i

/--
Julia source: base/indices.jl:509-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(iter::LinearIndices, i::Int)
    @inline
    @boundscheck checkbounds(iter, i)
    i
end
```
-/
def getindex_LinearIndices_Int {R : Type}
    (checkbounds : LinearIndices R → I64 → IndexResult Unit) (iter : LinearIndices R)
    (i : I64) : IndexResult I64 := do
  checkbounds iter i
  pure i

/--
Julia source: base/indices.jl:514-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(iter::LinearIndices, i::AbstractRange{<:Integer})
    @inline
    @boundscheck checkbounds(iter, i)
    @inbounds isa(iter, LinearIndices{1}) ? iter.indices[1][i] : (first(iter):last(iter))[i]
end
```
-/
def getindex_LinearIndices_AbstractRange {R I V : Type} [Inhabited R]
    (checkbounds : LinearIndices R → I → IndexResult Unit)
    (getindex_R : R → I → IndexResult V) (first last : LinearIndices R → I64)
    (colon : I64 → I64 → R) (iter : LinearIndices R) (i : I) : IndexResult V := do
  checkbounds iter i
  if iter.indices.length = 1 then getindex_R iter.indices[0]! i
  else getindex_R (colon (first iter) (last iter)) i

/--
Julia source: base/indices.jl:519-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(iter::LinearIndices) = iter
```
-/
def copy_LinearIndices {R : Type} (iter : LinearIndices R) : LinearIndices R := iter

/--
Julia source: base/indices.jl:520-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# More efficient iteration — predominantly for non-vector LinearIndices
# but one-dimensional LinearIndices must be special-cased to support OffsetArrays
iterate(iter::LinearIndices{1}, s...) = iterate(axes1(iter.indices[1]), s...)
```
-/
def iterate_LinearIndices_1 {R AX S V : Type} [Inhabited R] (axes1 : R → AX)
    (iterate : AX → List S → Option (V × S)) (iter : LinearIndices R) (s : List S) :
    Option (V × S) :=
  iterate (axes1 iter.indices[0]!) s

/--
Julia source: base/indices.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(iter::LinearIndices, i=1) = i > length(iter) ? nothing : (i, i+1)
```
-/
def iterate_LinearIndices {R : Type} (length : LinearIndices R → I64) (iter : LinearIndices R)
    (i : I64 := int 1) : Option (I64 × I64) :=
  if JuliaLean.base.int.lt_BitSigned (length iter) i then none
  else some (i, JuliaLean.base.int.add i (int 1))

/--
Julia source: base/indices.jl:524-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Needed since firstindex and lastindex are defined in terms of LinearIndices
first(iter::LinearIndices) = 1
```
-/
def first_LinearIndices {R : Type} (_iter : LinearIndices R) : I64 := int 1

/--
Julia source: base/indices.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(iter::LinearIndices{1}) = (@inline; first(axes1(iter.indices[1])))
```
-/
def first_LinearIndices_1 {m : Type → Type} [Monad m] {R Axes : Type} [Inhabited R]
    (axes1 : R → m Axes) (first : Axes → m I64) (iter : LinearIndices R) : m I64 := do
  first (← axes1 iter.indices[0]!)

/--
Julia source: base/indices.jl:528-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(iter::LinearIndices) = (@inline; length(iter))
```
-/
def last_LinearIndices {R : Type} (length : LinearIndices R → I64) (iter : LinearIndices R) :
    I64 :=
  length iter

/--
Julia source: base/indices.jl:529-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(iter::LinearIndices{1}) = (@inline; last(axes1(iter.indices[1])))
```
-/
def last_LinearIndices_1 {m : Type → Type} [Monad m] {R Axes : Type} [Inhabited R]
    (axes1 : R → m Axes) (last : Axes → m I64) (iter : LinearIndices R) : m I64 := do
  last (← axes1 iter.indices[0]!)

/--
Julia source: base/indices.jl:530-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function show(io::IO, iter::LinearIndices)
    print(io, "LinearIndices(", iter.indices, ")")
end
```
-/
def show_LinearIndices {R IO : Type} (printString : IO → String → IO)
    (printTuple : IO → List R → IO) (io : IO) (iter : LinearIndices R) : IO :=
  printString (printTuple (printString io "LinearIndices(") iter.indices) ")"

/-! ## Dispatch -/

/-- *dispatch*: `IndexStyle(::Type)` for the array types of `ArrayType`. -/
def IndexStyle_Type : ArrayType → IndexStyle
  | .bottom => IndexStyle_Type_Union
  | .array => IndexStyle_Type_Array
  | .abstractRange => IndexStyle_Type_AbstractRange
  | .linearIndices => IndexStyle_Type_LinearIndices
  | .custom none => IndexStyle_Type_AbstractArray
  | .custom (some style) => style

/-- *dispatch*: `IndexStyle(::IndexStyle, ::IndexStyle)`. -/
def IndexStyle_styles : IndexStyle → IndexStyle → IndexStyle
  | .linear, .linear => IndexStyle_IndexLinear_IndexLinear
  | a, b => IndexStyle_IndexStyle_IndexStyle a b

/-- *dispatch*: `IndexStyle(A, Bs...)` for arrays `A, Bs...` whose types `typeof` gives: one
array (`base/indices.jl:94`), two arrays (`:101`) or more (`:102`). -/
def IndexStyle_arrays {A : Type} (typeof : A → ArrayType) : A → List A → IndexStyle
  | a, [] => IndexStyle_AbstractArray typeof IndexStyle_Type a
  | a, [b] => IndexStyle_AbstractArray_AbstractArray
      (IndexStyle_AbstractArray typeof IndexStyle_Type) IndexStyle_styles a b
  | a, b :: c :: cs => IndexStyle_AbstractArray_Vararg
      (IndexStyle_AbstractArray typeof IndexStyle_Type)
      (fun _ => IndexStyle_arrays typeof b (c :: cs)) IndexStyle_styles a (b :: c :: cs)

/-- `AbstractUnitRange{Int}` axis values: a range of `range.jl` or this file's `Slice` or
`IdentityUnitRange` of one. -/
inductive AxisRange where
  | base (r : BaseRange)
  | slice (S : Slice BaseRange)
  | identity (S : IdentityUnitRange BaseRange)
  deriving Repr, DecidableEq

instance : Inhabited BaseRange := ⟨.oneTo (int 0)⟩
instance : Inhabited AxisRange := ⟨.base default⟩

/-- The `range.jl` methods this file's methods call on `Base.OneTo{Int}` and `UnitRange{Int}`
values. -/
structure RangeCallees where
  first : BaseRange → I64
  last : BaseRange → I64
  length : BaseRange → I64
  /-- `axes1(r)` (`Base.OneTo(length(r))`, or `r` for a `OneTo`). -/
  axes1 : BaseRange → BaseRange

/-- *dispatch*: `first` on an axis value. -/
def AxisRange.first (C : RangeCallees) : AxisRange → I64
  | .base r => C.first r
  | .slice S => first_Slice C.first S
  | .identity S => first_IdentityUnitRange C.first S

/-- *dispatch*: `last` on an axis value. -/
def AxisRange.last (C : RangeCallees) : AxisRange → I64
  | .base r => C.last r
  | .slice S => last_Slice C.last S
  | .identity S => last_IdentityUnitRange C.last S

/-- *dispatch*: `axes1` on an axis value: the `range.jl` method, or `base/indices.jl:344-345`
and `:371-372` (the `AbstractOneTo` methods for a wrapped `OneTo`). -/
def AxisRange.axes1 (C : RangeCallees) : AxisRange → AxisRange
  | .base r => .base (C.axes1 r)
  | .slice S => match S.indices with
    | .oneTo _ => .base (axes1_Slice_OneTo S)
    | .unitRange _ _ => .identity (axes1_Slice S)
  | .identity S => match S.indices with
    | .oneTo _ => .base (axes1_IdentityUnitRange_OneTo S)
    | .unitRange _ _ => .identity (axes1_IdentityUnitRange S)

/-- *dispatch*: `firstindex` on an axis value (`first(axes1(r))`, `abstractarray.jl`). -/
def AxisRange.firstindex (C : RangeCallees) (r : AxisRange) : I64 := (r.axes1 C).first C

/-- *dispatch*: `lastindex` on an axis value (`last(axes1(r))`, `abstractarray.jl`). -/
def AxisRange.lastindex (C : RangeCallees) (r : AxisRange) : I64 := (r.axes1 C).last C

/-- An integer index: an `Int`, or a value of another `Integer` type `I` (another BitInteger,
`BigInt`, a user integer), which dispatch tells apart from `Int`. -/
inductive IntegerIndex (I : Type) where
  | int (i : I64)
  | other (i : I)

/-- *dispatch*: `S[i]` for a `Slice` and an integer `i`: `base/indices.jl:350` for an `Int`; for
an integer of any other type no method of this file applies and Julia selects the `range.jl`
method `getindex(::AbstractRange, ::Integer)`, the parameter `getindex_AbstractRange`. -/
def getindex_Slice_Integer {T I : Type} (checkbounds : Slice T → I64 → IndexResult Unit)
    (getindex_AbstractRange : Slice T → I → IndexResult I64) :
    Slice T → IntegerIndex I → IndexResult I64
  | S, .int i => getindex_Slice_Int checkbounds S i
  | S, .other i => getindex_AbstractRange S i

/-- *dispatch*: `first(iter::LinearIndices)`: `base/indices.jl:527` for `LinearIndices{1}`,
`:526` for every other rank. -/
def first_LinearIndices_dispatch (C : RangeCallees) (iter : LinearIndices AxisRange) : I64 :=
  if iter.indices.length = 1 then
    first_LinearIndices_1 (m := Id) (AxisRange.axes1 C) (AxisRange.first C) iter
  else first_LinearIndices iter

/-- *dispatch*: `last(iter::LinearIndices)`: `base/indices.jl:529` for `LinearIndices{1}`,
`:528` for every other rank. -/
def last_LinearIndices_dispatch (C : RangeCallees) (length : LinearIndices AxisRange → I64)
    (iter : LinearIndices AxisRange) : I64 :=
  if iter.indices.length = 1 then
    last_LinearIndices_1 (m := Id) (AxisRange.axes1 C) (AxisRange.last C) iter
  else last_LinearIndices length iter

end JuliaLean.base.indices

namespace JuliaLean.AbstractArraySpecs


/-- Exceptions thrown by the modelled methods. -/
inductive Err where
  | boundsError
  | argumentError
  | dimensionMismatch
  | divideError
  | assertionError
  | methodError
  | canonicalIndexError
  | inexactError
  deriving DecidableEq, Repr

abbrev R (α : Type) := Except Err α

/-- `Int` bounds. -/
def tmin : Int := -(2 ^ 63)
def tmax : Int := 2 ^ 63 - 1

inductive ScalarIndex where
  | machineInt (value : I64)
  | integer (value : Int)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

def ScalarIndex.value : ScalarIndex → Int
  | .machineInt i => i.val
  | .integer i => i
  | .boolean b => if b then 1 else 0

inductive AxisIndexing where
  | unitRange
  | identityRange
  deriving DecidableEq, Repr

structure GenericAxis where
  first : ScalarIndex
  last : ScalarIndex
  indexing : AxisIndexing
  length : Nat
  deriving DecidableEq, Repr

/-- Integer `to_index` on a non-Array, including the Bool specialization
(base/indices.jl:243, 258-259). -/
def scalarToIndex (i : ScalarIndex) : R Int :=
  match i with
  | .machineInt value => .ok value.val
  | .boolean _ => .error .argumentError
  | .integer value =>
      if tmin ≤ value ∧ value ≤ tmax then .ok value else .error .inexactError

def convertScalarIndices : List ScalarIndex → R (List Int)
  | [] => .ok []
  | i :: is => do
      let j ← scalarToIndex i
      let js ← convertScalarIndices is
      .ok (j :: js)

/-- Each axis of `LinearIndices(A)` is converted to an Int range, including
both endpoints, before `first` examines the range's own indexing axes.
UnitRange is indexed from 1; IdentityUnitRange is indexed from its first value
(base/indices.jl:482-487, 525-527). -/
def convertRangeEndpoint (i : ScalarIndex) : R Int :=
  if tmin ≤ i.value ∧ i.value ≤ tmax then .ok i.value else .error .inexactError

def convertLinearAxes : List GenericAxis → R (List (AxisIndexing × Int))
  | [] => .ok []
  | axis :: axes => do
      let first ← convertRangeEndpoint axis.first
      let _ ← convertRangeEndpoint axis.last
      let rest ← convertLinearAxes axes
      .ok ((axis.indexing, first) :: rest)

def genericLinearStart (axes : List GenericAxis) : R Int := do
  let converted ← convertLinearAxes axes
  match converted with
  | [(.identityRange, first)] => .ok first
  | _ => .ok 1

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.Multidim

/-- An index argument. `urange lo hi` is `lo:hi` (it also stands for a `Vector{Int}` with
those values); `slice n` is `Base.Slice(OneTo(n))`; `cart vs` is `CartesianIndex(vs...)`. -/
inductive Idx where
  | int (v : Int)
  | bool (b : Bool)
  | urange (lo hi : Int)
  | colon
  | slice (n : Nat)
  | cart (vs : List Int)
  deriving DecidableEq, Repr

/-- Number of array dimensions an index consumes (`index_ndims`). -/
def Idx.ndims : Idx → Nat
  | .cart vs => vs.length
  | _ => 1

/-- `i == 1` in `_selectdim` (`Int`, `Bool`: numeric equality; ranges, `Colon`,
`CartesianIndex`: `false`). -/
def Idx.eqOne : Idx → Bool
  | .int v => v == 1
  | .bool b => b
  | _ => false

/-- `setindex_shape_check(X, shape)` (`base/indices.jl:216-225`) for an `Array` `X`. -/
def setindexShapeCheck (sz shape : List Nat) : Bool :=
  if sz.length = 1 ∨ shape.length = 1 then sz.foldl (· * ·) 1 == shape.foldl (· * ·) 1
  else
    let rec go : List Nat → List Nat → Bool
      | [], [] => true
      | a, [] => a.all (· == 1)
      | [], b => b.all (· == 1)
      | a :: as, b :: bs => a == b && go as bs
    go sz shape

end JuliaLean.Multidim

namespace JuliaLean.AbstractArrays

open JuliaLean

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

/-- An integer axis with `len` elements beginning at `first`. -/
structure Axis where
  first : I64
  len : Nat
  deriving DecidableEq, Repr

namespace Axis

/-- Last index. Empty axes use `first - 1`, as a Julia unit range does. -/
def last (a : Axis) : I64 := a.first + i64 ((a.len : Int) - 1)

/-- Numeric membership in an axis. Source: `base/abstractarray.jl:751-753`. -/
def contains (a : Axis) (i : I64) : Bool :=
  decide (a.first.val ≤ i.val ∧ i.val < a.first.val + a.len)

/-- `Base.OneTo(n)`. -/
def oneTo (n : Nat) : Axis := ⟨i64 1, n⟩

/-- Whether the axis begins at one. -/
def isOneBased (a : Axis) : Bool := a.first.val == 1

end Axis

/-- Scalar `Real` indices seen by `checkindex`. `integer` is supported by
`to_index`; `unsupportedReal` represents `Bool` and non-integer reals, which
still reach the `i::Real` checkindex method. -/
inductive ScalarIndex where
  | integer (value : I64)
  | unsupportedReal (value : I64)
  deriving DecidableEq, Repr

namespace ScalarIndex

def value : ScalarIndex → I64
  | .integer i | .unsupportedReal i => i

/-- `to_index`, `base/indices.jl:243,258-266`. -/
def toIndex : ScalarIndex → Jl I64
  | .integer i => .ok i
  | .unsupportedReal _ => .error (.argumentError "invalid index")

end ScalarIndex

/-- Range index. `empty` records Julia's `isempty(i)` before endpoint checks. -/
structure RangeIndex where
  first : I64
  last : I64
  empty : Bool
  deriving DecidableEq, Repr

/-- Raw indices accepted by `to_indices`. -/
inductive RawIndex where
  | scalar (i : ScalarIndex)
  | cartesian (is : List ScalarIndex)
  | colon
  | mask (axes : List Axis)
  deriving DecidableEq, Repr

/-- Canonical indices produced by `to_indices`: integers, slices and logical
indices. -/
inductive CanonIndex where
  | integer (i : I64)
  | slice (axis : Axis)
  | logical (axes : List Axis)
  deriving DecidableEq, Repr

/-- `to_indices`, `base/indices.jl:310-323` and
`base/multidimensional.jl:928-939`: CartesianIndex is flattened, Colon becomes
a slice of the current axis, and other scalars go through `to_index`. -/
def toIndices : List Axis → List RawIndex → Jl (List CanonIndex)
  | _, [] => .ok []
  | _, [.cartesian is] => is.mapM (fun i => return .integer (← i.toIndex))
  | axes, .cartesian is :: rest => do
      let head ← is.mapM (fun i => return .integer (← i.toIndex))
      let tail ← toIndices (axes.drop is.length) rest
      return head ++ tail
  | a :: axes, .colon :: rest => do
      let tail ← toIndices axes rest
      return .slice a :: tail
  | [], .colon :: rest => do
      let tail ← toIndices [] rest
      return .slice (Axis.oneTo 1) :: tail
  | axes, .scalar i :: rest => do
      let j ← i.toIndex
      let tail ← toIndices axes.tail rest
      return .integer j :: tail
  | axes, .mask maskAxes :: rest => do
      let tail ← toIndices (axes.drop maskAxes.length) rest
      return .logical maskAxes :: tail

end JuliaLean.AbstractArrays

namespace JuliaLean.AbstractArraySpecs


/-- `Base.OneTo(n)` for `n ≥ 0`. -/
def oneTo (n : I64) : Ax := ⟨.oneTo, i64 1, n⟩

/-- Mathematical length of an axis. -/
def Ax.len (r : Ax) : Int := r.hi.val - r.lo.val + 1

/-- Product of the axis lengths. -/
def totalLen : List Ax → Int
  | [] => 1
  | r :: rs => r.len * totalLen rs

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.ReduceCov

open JuliaLean

/-! ## `IndexStyle`, `base/indices.jl:94-104, 505` -/

inductive IndexStyleV where
  | linear
  | cartesian
  deriving DecidableEq, Repr

/-- Array types for `IndexStyle`: `Array`, ranges, `LinearIndices`, a type with
the `AbstractArray` default, a type that defines its own style, `Union{}`. -/
inductive ArrTy where
  | array
  | range
  | linearIndices
  | plain
  | custom (s : IndexStyleV)
  | bottom
  deriving DecidableEq, Repr

/-- `IndexStyle(::Type{Union{}}) = IndexLinear()`, `base/indices.jl:95`. -/
def indexStyleBottom : IndexStyleV := .linear

/-- `IndexStyle(::Type{<:AbstractArray}) = IndexCartesian()`, `base/indices.jl:97`. -/
def indexStyleAbstractArray : IndexStyleV := .cartesian

/-- `IndexStyle(::Type{<:Array}) = IndexLinear()`, `base/indices.jl:98`. -/
def indexStyleArray : IndexStyleV := .linear

/-- `IndexStyle(::Type{<:AbstractRange}) = IndexLinear()`, `base/indices.jl:99`. -/
def indexStyleRange : IndexStyleV := .linear

/-- `IndexStyle(::Type{<:LinearIndices}) = IndexLinear()`, `base/indices.jl:505`. -/
def indexStyleLinearIndices : IndexStyleV := .linear

/-- `IndexStyle(T)`, dispatching to the most specific method; a custom array type
defines its own method. -/
def indexStyleTy : ArrTy → IndexStyleV
  | .bottom => indexStyleBottom
  | .plain => indexStyleAbstractArray
  | .array => indexStyleArray
  | .range => indexStyleRange
  | .linearIndices => indexStyleLinearIndices
  | .custom s => s

/-- `IndexStyle(A::AbstractArray) = IndexStyle(typeof(A))`, `base/indices.jl:94`. -/
def indexStyle1 (a : ArrTy) : IndexStyleV := indexStyleTy a

/-- `IndexStyle(::IndexLinear, ::IndexLinear) = IndexLinear()` and
`IndexStyle(::IndexStyle, ::IndexStyle) = IndexCartesian()`, `base/indices.jl:103-104`. -/
def indexStyleCombine : IndexStyleV → IndexStyleV → IndexStyleV
  | .linear, .linear => .linear
  | _, _ => .cartesian

/-- `IndexStyle(A, B...)`, `base/indices.jl:101-102`:
`IndexStyle(A, B) = IndexStyle(IndexStyle(A), IndexStyle(B))` and
`IndexStyle(A, B...) = IndexStyle(IndexStyle(A), IndexStyle(B...))`. -/
def indexStyleN : ArrTy → List ArrTy → IndexStyleV
  | a, [] => indexStyle1 a
  | a, b :: rest => indexStyleCombine (indexStyle1 a) (indexStyleN b rest)

/-- `IndexStyle(::Type{Union{}}, slurp...)`, `base/indices.jl:96`. -/
def indexStyleBottomSlurp : Jl IndexStyleV := .error (.methodError "IndexStyle")

end JuliaLean.ReduceCov

namespace JuliaLean.AbstractArraySpecs

/-- `_shapes_match(a, b)` (base/indices.jl:217-220). -/
def shapesMatch : List I64 → List I64 → Bool
  | [], [] => true
  | a, [] => a.all (· == i64 1)
  | [], b => b.all (· == i64 1)
  | a :: as, b :: bs => a == b && shapesMatch as bs

/-- `setindex_shape_check(X, shape)` (base/indices.jl:214-225): with one index or a
vector `X`, the element counts must agree, otherwise the shapes up to trailing ones. -/
def shapeCheck (prodI : List I64 → I64) (xs js : List I64) : R Unit :=
  let agrees := if xs.length = 1 ∨ js.length = 1 then prodI xs == prodI js else shapesMatch xs js
  if agrees then .ok () else .error .dimensionMismatch

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.ArrayOps

open JuliaLean

/-- `to_index(A::Array, i)` for a `BitInteger` index, `base/indices.jl:247, 258`:
`UInt` is reinterpreted as `Int`, every other type is converted with
`convert(Int, i)` (`InexactError` when not representable). -/
def toIndexArray {t : IntTy} (i : JInt t) : Jl JInt64 :=
  if t = .u64 then .ok (JInt.wrap .i64 i.val) else toInt i

/-- `to_index(A, i)` for any other array (`base/indices.jl:243, 258`): `convert(Int, i)`. -/
def toIndexGeneric {t : IntTy} (i : JInt t) : Jl JInt64 := toInt i

/-- `LinearIndices(v)[i]` for a vector, `base/indices.jl:509-513`:
`to_index` (generic, `convert(Int, i)`), bounds check, then `i` itself. -/
def linearGet {t : IntTy} (n : Nat) (i : JInt t) : Jl JInt64 := do
  let i ← toIndexGeneric i
  if 1 ≤ i.val ∧ i.val ≤ n then pure i else throw .boundsError

/-- `LinearIndices(v)[CartesianIndex(i)]` (`base/indices.jl:509` after
`to_indices` splats the `CartesianIndex`): bounds check, then `i`. -/
def linearOfCartesian (n : Nat) (i : JInt64) : Jl JInt64 :=
  if 1 ≤ i.val ∧ i.val ≤ n then pure i else throw .boundsError

end JuliaLean.ArrayOps


/-!
# `base/indices.jl`: index ranges, `LinearIndices`, shape checks, `to_index`

Master `bbfa0ce4150`. A unit range with `Int` elements is a `UR`: `Base.OneTo(n)`,
`a:b`, `IdentityUnitRange(r)` or `Slice(r)`. Its first and last elements are the
`Int64` values of its fields; `len` is its element count and `vals` its elements
in order (`Int` values in the model; every range here is an axis of fewer than
`typemax(Int)` elements, so Julia's `length` does not wrap). An index argument is
an `Ix`; Bool elements of a Bool range are `0`/`1`.
-/

namespace JuliaLean.ReduceCov.Indices

open JuliaLean.ReduceCov

/-- An `AbstractUnitRange{Int}`. -/
inductive UR where
  /-- `Base.OneTo(n)`, `n ≥ 0` (the constructor clamps at zero). -/
  | oneTo (n : I64)
  /-- `a:b`, with `b ≥ a - 1` (the constructor normalizes an empty range). -/
  | unit (a b : I64)
  | ident (r : UR)
  | slice (r : UR)
  deriving DecidableEq, Repr

namespace UR

/-- `first(r)`; `first(S::Slice) = first(S.indices)` (`base/indices.jl:347`),
`first(S::IdentityUnitRange) = first(S.indices)` (`:374`). -/
def first : UR → Int
  | .oneTo _ => 1
  | .unit a _ => a.val
  | .ident r | .slice r => r.first

/-- `last(r)`, `base/indices.jl:348, 375`. -/
def last : UR → Int
  | .oneTo n => n.val
  | .unit _ b => b.val
  | .ident r | .slice r => r.last

/-- `length(r)`; `size(S) = (length(S.indices),)` (`base/indices.jl:349, 376`) and
`unsafe_length(S::IdentityUnitRange) = unsafe_length(S.indices)` (`:377`). -/
def len (r : UR) : Nat := (r.last - r.first + 1).toNat

/-- The elements in iteration order: `iterate(S::Slice, s...) = iterate(S.indices, s...)`
and likewise for `IdentityUnitRange` (`base/indices.jl:354, 417`). -/
def vals (r : UR) : List Int := (List.range r.len).map fun (k : Nat) => r.first + (k : Int)

/-- `axes1(r)`: `axes1(S::Slice) = IdentityUnitRange(S.indices)` and
`axes1(S::Slice{<:AbstractOneTo}) = S.indices` (`base/indices.jl:344-345`),
`axes1(S::IdentityUnitRange) = S` and `axes1(S::IdentityUnitRange{<:AbstractOneTo}) =
S.indices` (`:371-372`); a plain range has `axes1 = OneTo(length(r))`. -/
def axes1 : UR → UR
  | .oneTo n => .oneTo n
  | .unit a b => .oneTo (i64 (UR.unit a b).len)
  | .ident (.oneTo n) => .oneTo n
  | .ident r => .ident r
  | .slice (.oneTo n) => .oneTo n
  | .slice r => .ident r

/-- `axes(S) = (axes1(S),)`, `base/indices.jl:343, 370`. -/
def axes (r : UR) : List UR := [r.axes1]

/-- `Slice(S::Slice) = S` (`base/indices.jl:340`); a `Slice` of any other range wraps it. -/
def mkSlice : UR → UR
  | .slice r => .slice r
  | r => .slice r

/-- `IdentityUnitRange(S::IdentityUnitRange) = S` (`base/indices.jl:366`). -/
def mkIdent : UR → UR
  | .ident r => .ident r
  | r => .ident r

/-- `T(r)` for `T = UnitRange{Int}`: the same elements as a plain range. -/
def toUnitRange (r : UR) : UR := .unit (i64 r.first) (i64 r.last)

/-- `Slice{UnitRange{Int}}(S::Slice) = Slice{T}(T(S.indices))` and the
`IdentityUnitRange` analogue, `base/indices.jl:341, 367`. -/
def convertWrapped : UR → UR
  | .slice r => .slice r.toUnitRange
  | .ident r => .ident r.toUnitRange
  | r => r

/-- `show(io, r)`: `Base.OneTo(n)`, `a:b`, `print(io, "Base.Slice(", r.indices, ")")` and
`print(io, "Base.IdentityUnitRange(", r.indices, ")")`, `base/indices.jl:353, 416`. -/
def str : UR → String
  | .oneTo n => s!"Base.OneTo({n.val})"
  | .unit a b => s!"{a.val}:{b.val}"
  | .ident r => "Base.IdentityUnitRange(" ++ r.str ++ ")"
  | .slice r => "Base.Slice(" ++ r.str ++ ")"

end UR

/-! ## Indexing `Slice` and `IdentityUnitRange`, `base/indices.jl:350-427` -/

/-- An index argument. -/
inductive Ix where
  /-- `i::Int`. -/
  | int (i : I64)
  /-- `i::Integer` of another `BitInteger` type. -/
  | integer (t : IntTy) (i : JInt t)
  /-- `i::Bool`. -/
  | bool (b : Bool)
  /-- An `AbstractUnitRange{Int}`. -/
  | urange (r : UR)
  /-- `a:b::UnitRange{Bool}`. -/
  | brange (a b : Bool)
  /-- `a:s:b::StepRange{Int,Int}`, `s ≠ 0`. -/
  | srange (a s b : I64)
  /-- `StepRange(a, s, b)::StepRange{Bool,Int}`, `s ≠ 0`. -/
  | bsrange (a : Bool) (s : I64) (b : Bool)
  deriving DecidableEq, Repr

/-- `Int(b)`. -/
def bInt (b : Bool) : Int := if b then 1 else 0

/-- The elements of `a:s:b`: `a, a + s, …` up to `b` (`s ≠ 0`). -/
def stepVals (a s b : Int) : List Int :=
  let n : Nat := if s > 0 then (if b < a then 0 else ((b - a) / s + 1).toNat)
    else if s < 0 then (if a < b then 0 else ((a - b) / (-s) + 1).toNat) else 0
  (List.range n).map fun (k : Nat) => a + (k : Int) * s

/-- Whether an index is a Bool mask (an `AbstractRange{Bool}`). -/
def Ix.isMask : Ix → Bool
  | .brange .. | .bsrange .. => true
  | _ => false

/-- The elements of a non-scalar index. -/
def Ix.elems : Ix → List Int
  | .urange r => r.vals
  | .brange a b => stepVals (bInt a) 1 (bInt b)
  | .srange a s b => stepVals a.val s.val b.val
  | .bsrange a s b => stepVals (bInt a) s.val (bInt b)
  | _ => []

/-- `range(start; length = n, step = s)`: `n` elements from `start` in steps of `s`. -/
def rangeLen (start : Int) (n : Int) (s : Int) : List Int :=
  (List.range n.toNat).map fun (k : Nat) => start + (k : Int) * s

/-! ### The methods of `Slice` and `IdentityUnitRange`, one function each -/

namespace SliceM

/-- `Slice(S::Slice) = S`, `base/indices.jl:340`. -/
def ofSlice (S : UR) : UR := S

/-- `Slice{T}(S::Slice) = Slice{T}(T(S.indices))`, `base/indices.jl:341`, for
`T = UnitRange{Int}`. -/
def convert (indices : UR) : UR := .slice indices.toUnitRange

/-- `axes(S::Slice) = (axes1(S),)`, `base/indices.jl:343`. -/
def axes (S : UR) : List UR := [S.axes1]

/-- `axes1(S::Slice) = IdentityUnitRange(S.indices)`, `base/indices.jl:344`. -/
def axes1 (indices : UR) : UR := .ident indices

/-- `axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices`, `base/indices.jl:345`. -/
def axes1OneTo (indices : UR) : UR := indices

/-- `first(S::Slice) = first(S.indices)`, `base/indices.jl:347`. -/
def first (indices : UR) : Int := indices.first

/-- `last(S::Slice) = last(S.indices)`, `base/indices.jl:348`. -/
def last (indices : UR) : Int := indices.last

/-- `size(S::Slice) = (length(S.indices),)`, `base/indices.jl:349`. -/
def size (indices : UR) : List Nat := [indices.len]

/-- `getindex(S::Slice, i::Int) = (@boundscheck checkbounds(S, i); i)`, `base/indices.jl:350`. -/
def getindexInt (checkbounds : UR → Ix → RJ Unit) (S : UR) (i : I64) : RJ (List Int) := do checkbounds S (.int i); pure [i.val]

/-- `getindex(S::Slice, i::AbstractUnitRange{<:Integer})`, `base/indices.jl:351`: bounds
check, then `i` (`i` is a unit range, possibly of `Bool`s). -/
def getindexUnitRange (checkbounds : UR → Ix → RJ Unit) (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::Slice, i::StepRange{<:Integer})`, `base/indices.jl:352`: bounds check,
then `i`. -/
def getindexStepRange (checkbounds : UR → Ix → RJ Unit) (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::Slice{<:AbstractUnitRange{<:Integer}}, i::IdentityUnitRange)`,
`base/indices.jl:410-415`: bounds check, then `i`. -/
def getindexIdent (checkbounds : UR → Ix → RJ Unit) (S : UR) (I : UR) : RJ (List Int) := do
  checkbounds S (.urange (.ident I)); pure (UR.ident I).vals

/-- `show(io, r::Slice) = print(io, "Base.Slice(", r.indices, ")")`, `base/indices.jl:353`. -/
def show_ (indices : UR) : String := "Base.Slice(" ++ indices.str ++ ")"

/-- `iterate(S::Slice, s...) = iterate(S.indices, s...)`, `base/indices.jl:354`: the
iterated values. -/
def iterate (indices : UR) : List Int := indices.vals

end SliceM

namespace IdentM

/-- `IdentityUnitRange(S::IdentityUnitRange) = S`, `base/indices.jl:366`. -/
def ofIdent (S : UR) : UR := S

/-- `IdentityUnitRange{T}(S::IdentityUnitRange) = IdentityUnitRange{T}(T(S.indices))`,
`base/indices.jl:367`, for `T = UnitRange{Int}`. -/
def convert (indices : UR) : UR := .ident indices.toUnitRange

/-- `axes(S::IdentityUnitRange) = (axes1(S),)`, `base/indices.jl:370`. -/
def axes (S : UR) : List UR := [S.axes1]

/-- `axes1(S::IdentityUnitRange) = S`, `base/indices.jl:371`. -/
def axes1 (indices : UR) : UR := .ident indices

/-- `axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices`,
`base/indices.jl:372`. -/
def axes1OneTo (indices : UR) : UR := indices

/-- `first(S::IdentityUnitRange) = first(S.indices)`, `base/indices.jl:374`. -/
def first (indices : UR) : Int := indices.first

/-- `last(S::IdentityUnitRange) = last(S.indices)`, `base/indices.jl:375`. -/
def last (indices : UR) : Int := indices.last

/-- `size(S::IdentityUnitRange) = (length(S.indices),)`, `base/indices.jl:376`. -/
def size (indices : UR) : List Nat := [indices.len]

/-- `unsafe_length(S::IdentityUnitRange) = unsafe_length(S.indices)`, `base/indices.jl:377`. -/
def unsafeLength (indices : UR) : Nat := indices.len

/-- `getindex(S::IdentityUnitRange, i::Integer)`, `base/indices.jl:378`: bounds check,
then `convert(eltype(S), i)`, i.e. `Int(i)`. -/
def getindexInteger (checkbounds : UR → Ix → RJ Unit) (S : UR) (i : Ix) (k : Int) : RJ (List Int) := do checkbounds S i; pure [k]

/-- `getindex(S::IdentityUnitRange, i::Bool)`, `base/indices.jl:379`. -/
def getindexBool (b : Bool) : RJ (List Int) := .error (argErr s!"invalid index: {b} of type Bool")

/-- `getindex(S::IdentityUnitRange, i::AbstractUnitRange{<:Integer})`,
`base/indices.jl:380-384`: bounds check, then `convert(AbstractUnitRange{Int}, i)`. -/
def getindexUnitRange (checkbounds : UR → Ix → RJ Unit) (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::IdentityUnitRange, i::AbstractUnitRange{Bool})`, `base/indices.jl:385-389`:
bounds check, then `range(first(i) ? first(S) : last(S), length = last(i))`. -/
def getindexBoolUnitRange (checkbounds : UR → Ix → RJ Unit) (S : UR) (a b : Bool) : RJ (List Int) := do
  checkbounds S (.brange a b); pure (rangeLen (if a then S.first else S.last) (bInt b) 1)

/-- `getindex(S::IdentityUnitRange, i::StepRange{<:Integer})`, `base/indices.jl:390-394`:
bounds check, then `convert(AbstractRange{Int}, i)`. -/
def getindexStepRange (checkbounds : UR → Ix → RJ Unit) (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::IdentityUnitRange, i::StepRange{Bool})`, `base/indices.jl:395-399`: bounds
check, then `range(first(i) ? first(S) : last(S), length = last(i), step = Int(step(i)))`. -/
def getindexBoolStepRange (checkbounds : UR → Ix → RJ Unit) (S : UR) (a : Bool) (s : I64) (b : Bool) : RJ (List Int) := do
  checkbounds S (.bsrange a s b); pure (rangeLen (if a then S.first else S.last) (bInt b) s.val)

/-- `getindex(S::IdentityUnitRange{<:AbstractUnitRange{<:Integer}}, i::IdentityUnitRange)`,
`base/indices.jl:404-409`: bounds check, then `i`. -/
def getindexIdent (checkbounds : UR → Ix → RJ Unit) (S : UR) (I : UR) : RJ (List Int) := do
  checkbounds S (.urange (.ident I)); pure (UR.ident I).vals

/-- `show(io, r::IdentityUnitRange)`, `base/indices.jl:416`. -/
def show_ (indices : UR) : String := "Base.IdentityUnitRange(" ++ indices.str ++ ")"

/-- `iterate(S::IdentityUnitRange, s...) = iterate(S.indices, s...)`, `base/indices.jl:417`. -/
def iterate (indices : UR) : List Int := indices.vals

end IdentM

/-- `S[i]` for `S = Slice(r)`, dispatching to the methods above. -/
def sliceGet (checkbounds : UR → Ix → RJ Unit) (rangeGetindexInteger : UR → Ix → Int → RJ (List Int)) (r : UR) (i : Ix) : RJ (List Int) :=
  let S := UR.slice r
  match i with
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .int k => (SliceM.getindexInt checkbounds) S k
  | .integer _ k => rangeGetindexInteger S i k.val
  | .urange (.ident I) => (SliceM.getindexIdent checkbounds) S I
  | .urange _ | .brange .. => (SliceM.getindexUnitRange checkbounds) S i
  | .srange .. | .bsrange .. => (SliceM.getindexStepRange checkbounds) S i

/-- `S[i]` for `S = IdentityUnitRange(r)`, dispatching to the methods above. -/
def identGet (checkbounds : UR → Ix → RJ Unit) (r : UR) (i : Ix) : RJ (List Int) :=
  let S := UR.ident r
  match i with
  | .bool b => IdentM.getindexBool b
  | .int k => (IdentM.getindexInteger checkbounds) S i k.val
  | .integer _ k => (IdentM.getindexInteger checkbounds) S i k.val
  | .urange (.ident I) => (IdentM.getindexIdent checkbounds) S I
  | .urange _ => (IdentM.getindexUnitRange checkbounds) S i
  | .brange a b => (IdentM.getindexBoolUnitRange checkbounds) S a b
  | .srange .. => (IdentM.getindexStepRange checkbounds) S i
  | .bsrange a s b => (IdentM.getindexBoolStepRange checkbounds) S a s b

/-- `getindex(S::AbstractOneTo{<:Integer}, I::IdentityUnitRange)`,
`base/indices.jl:423-427`: `checkbounds(S, I)`, then `I`. -/
def oneToGetIdent (checkbounds : UR → Ix → RJ Unit) (n : I64) (I : UR) : RJ (List Int) := do
  checkbounds (.oneTo n) (.urange (.ident I))
  pure (UR.ident I).vals

/-! ## Promotion rules, `base/indices.jl:492-502` -/

/-- `promote_type(R1, R2)` of two `Int` range types. -/
def RT.promote : RT → RT → RT
  | .oneTo, .oneTo => .oneTo
  | _, _ => .unitRange

/-- `promote_rule(::Type{Slice{T1}}, ::Type{Slice{T2}}) = el_same(promote_type(T1, T2), a, b)`,
`base/indices.jl:499-500`. -/
def promoteRuleSlice (t1 t2 : RT) : WT := elSame (.range (t1.promote t2)) (.slice t1) (.slice t2)

/-- `promote_rule` for `IdentityUnitRange`, `base/indices.jl:501-502`. -/
def promoteRuleIdent (t1 t2 : RT) : WT := elSame (.range (t1.promote t2)) (.ident t1) (.ident t2)

/-- `indices_promote_type` and `promote_rule(::Type{LinearIndices{N,R1}}, ...)`,
`base/indices.jl:492-498`: the wrapped tuple types promote elementwise. -/
def promoteRuleLinIdx (r1 r2 : List RT) : WT := .linIdx (List.zipWith RT.promote r1 r2)

/-! ## `LinearIndices`, `base/indices.jl:429-533` -/

/-- `LinearIndices{N,R}` with `indices::R`. -/
structure LinIdx where
  inds : List UR
  deriving DecidableEq, Repr

namespace LinIdx

/-- `axes(iter) = map(axes1, iter.indices)`, `base/indices.jl:506`. -/
def axes (L : LinIdx) : List UR := L.inds.map UR.axes1

/-- `size(iter) = map(length, iter.indices)`, `base/indices.jl:507`. -/
def size (L : LinIdx) : List Nat := L.inds.map UR.len

/-- `length(iter) = prod(size(iter))`. -/
def length (L : LinIdx) : Nat := L.size.foldl (· * ·) 1

/-- `checkbounds(Bool, iter, i)` for one `Int` index (linear indexing): the index of a
one-dimensional `LinearIndices` must be in its axis, otherwise in `1:length(iter)`. -/
def inBounds (L : LinIdx) (i : Int) : Bool :=
  match L.inds with
  | [r] => decide (r.axes1.first ≤ i ∧ i ≤ r.axes1.last)
  | _ => decide (1 ≤ i ∧ i ≤ L.length)

/-- `isassigned(iter, i::Int) = checkbounds(Bool, iter, i)`, `base/indices.jl:508`. -/
def isassigned (L : LinIdx) (i : I64) : Bool := L.inBounds i.val

/-- `getindex(iter::LinearIndices, i::Int)`, `base/indices.jl:509-513`. -/
def get (L : LinIdx) (i : I64) : RJ Int :=
  if L.inBounds i.val then .ok i.val else .error boundsErr

/-- `first(iter::LinearIndices) = 1`, `base/indices.jl:526`. -/
def firstN (_L : LinIdx) : Int := 1

/-- `first(iter::LinearIndices{1}) = first(axes1(iter.indices[1]))`, `base/indices.jl:527`. -/
def first1 (r : UR) : Int := r.axes1.first

/-- `last(iter::LinearIndices) = length(iter)`, `base/indices.jl:528`. -/
def lastN (L : LinIdx) : Int := L.length

/-- `last(iter::LinearIndices{1}) = last(axes1(iter.indices[1]))`, `base/indices.jl:529`. -/
def last1 (r : UR) : Int := r.axes1.last

/-- `first(iter)`, dispatching on the number of dimensions. -/
def first (L : LinIdx) : Int :=
  match L.inds with
  | [r] => first1 r
  | _ => firstN L

/-- `last(iter)`, dispatching on the number of dimensions. -/
def last (L : LinIdx) : Int :=
  match L.inds with
  | [r] => last1 r
  | _ => lastN L

/-- `getindex(iter::LinearIndices, i::AbstractRange{<:Integer})`, `base/indices.jl:514-518`:
after `checkbounds`, `iter.indices[1][i]` for one dimension (indexing a unit range `r`
at `k` gives `first(r) + (k - first(axes1(r)))`) and `(first(iter):last(iter))[i]`
otherwise; `i` is a unit range of `Int`s. -/
def getRange (L : LinIdx) (i : UR) : RJ (List Int) :=
  let ok : Bool := match i.vals.head?, i.vals.getLast? with
    | some x, some y => L.inBounds x && L.inBounds y
    | _, _ => true
  if !ok then .error boundsErr
  else match L.inds with
    | [r] => .ok (i.vals.map fun k => r.first + (k - r.axes1.first))
    | _ => .ok (i.vals.map fun k => L.firstN + (k - 1))

/-- `iterate(iter::LinearIndices, i=1) = i > length(iter) ? nothing : (i, i+1)`,
`base/indices.jl:523`: the values from state `i`, `fuel` steps at most. -/
def iterateN (L : LinIdx) : Nat → Int → List Int
  | 0, _ => []
  | fuel + 1, i => if i > L.length then [] else i :: iterateN L fuel (i + 1)

/-- `iterate(iter::LinearIndices{1}, s...) = iterate(axes1(iter.indices[1]), s...)`,
`base/indices.jl:522`: the iterated values. -/
def iterate1 (r : UR) : List Int := r.axes1.vals

/-- The iterated values, dispatching on the number of dimensions; the general method
starts at state `1` and stops after `length(iter) + 1` calls. -/
def collect (L : LinIdx) : List Int :=
  match L.inds with
  | [r] => iterate1 r
  | _ => L.iterateN (L.length + 1) 1

/-- `copy(iter::LinearIndices) = iter`, `base/indices.jl:519`. -/
def copy (L : LinIdx) : LinIdx := L

/-- `show(io, iter::LinearIndices)`: `LinearIndices(` then the tuple of indices,
`base/indices.jl:531-533`. -/
def str (L : LinIdx) : String :=
  "LinearIndices((" ++ ", ".intercalate (L.inds.map UR.str) ++
    (if L.inds.length = 1 then "," else "") ++ "))"

end LinIdx

/-- An argument of the `LinearIndices` constructor tuple: an integer or a unit range. -/
inductive DimArg where
  | int (n : I64)
  | bool (b : Bool)
  | range (r : UR)
  deriving DecidableEq, Repr

/-- `_convert2ind(i::Integer) = oneto(i)`, `base/indices.jl:489`: `OneTo(n)` clamps a
negative `n` to `0` and rejects a `Bool`. -/
def convert2indInt : DimArg → RJ UR
  | .int n => .ok (.oneTo (if n.val < 0 then i64 0 else n))
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .range r => .ok r

/-- `_convert2ind(ind::AbstractUnitRange) = first(ind):last(ind)`, `base/indices.jl:490`. -/
def convert2indRange (r : UR) : UR := .unit (i64 r.first) (i64 r.last)

/-- `_convert2ind(x)`, dispatching on the argument type. -/
def convert2ind : DimArg → RJ UR
  | .range r => .ok (convert2indRange r)
  | a => convert2indInt a

/-- `LinearIndices(::Tuple{}) = LinearIndices{0,typeof(())}(())`, `base/indices.jl:482`. -/
def linearIndicesEmpty : LinIdx := ⟨[]⟩

/-- `LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}})`, `base/indices.jl:483-484`:
`LinearIndices(map(r->convert(AbstractUnitRange{Int}, r), inds))`, which keeps every
range of `Int`s. -/
def linearIndicesRanges (rs : List UR) : LinIdx := ⟨rs.map id⟩

/-- `LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}})`,
`base/indices.jl:485-486`: `LinearIndices(map(_convert2ind, inds))`. -/
def linearIndicesMixed (args : List DimArg) : RJ LinIdx := (args.mapM convert2ind).map LinIdx.mk

/-- `LinearIndices(A::Union{AbstractArray,SimpleVector}) = LinearIndices(axes(A))`,
`base/indices.jl:487`: `axes` are the array's axes. -/
def linearIndicesOf (axes : List UR) : LinIdx :=
  if axes = [] then linearIndicesEmpty else linearIndicesRanges axes

/-- `LinearIndices(inds)` for a tuple, dispatching to the most specific method. -/
def linearIndices (args : List DimArg) : RJ LinIdx :=
  if args = [] then .ok linearIndicesEmpty
  else if args.all (fun a => match a with | .range _ => true | _ => false) then
    .ok (linearIndicesRanges (args.filterMap fun a => match a with | .range r => some r | _ => none))
  else linearIndicesMixed args

/-- `convert(::Type{LinearIndices{N,R}}, inds::LinearIndices{N})`, `base/indices.jl:479-480`:
the indices are converted to `R`; for `R = NTuple{N, UnitRange{Int}}` each becomes a
plain range with the same elements. -/
def convertToUnitRanges (L : LinIdx) : LinIdx := ⟨L.inds.map UR.toUnitRange⟩

/-! ## `promote_shape`, `base/indices.jl:106-203` -/

/-- A tuple as `print(io, t)` shows it: `(x1, x2)`, or `(x1,)` for one element. -/
def tupleStr (xs : List String) : String :=
  "(" ++ ", ".intercalate xs ++ (if xs.length = 1 then "," else "") ++ ")"

/-- An argument of `throw_promote_shape_mismatch`: `Dims` or a tuple of axes. -/
inductive Shape where
  | dims (ds : List Int)
  | axes (rs : List UR)

namespace Shape

/-- `s isa Tuple{Vararg{Base.OneTo}}` (the empty tuple included). -/
def allOneTo : Shape → Bool
  | .dims ds => ds.isEmpty
  | .axes rs => rs.all fun r => match r with | .oneTo _ => true | _ => false

/-- `s isa Dims`. -/
def isDims : Shape → Bool
  | .dims _ => true
  | .axes rs => rs.isEmpty

/-- `map(lastindex, s)::Dims` for a tuple of `OneTo`s. -/
def toDims : Shape → Shape
  | .axes rs => .dims (rs.map UR.last)
  | s => s

/-- `print(io, s)` after `_normalize(d) = map(x -> firstindex(x):lastindex(x), d)`
when `normalize` holds. -/
def str (normalize : Bool) : Shape → String
  | .dims ds => tupleStr (ds.map toString)
  | .axes rs => tupleStr (rs.map fun r =>
      if normalize then s!"{r.axes1.first}:{r.axes1.last}" else r.str)

end Shape

/-- `throw_promote_shape_mismatch(a, b, i)`, `base/indices.jl:112-137` (with the nested
`_normalize`, `:119`): tuples of `OneTo` are printed as sizes; unless both arguments
are then `Dims`, both are printed as normalized axes. `b = nothing` and `i = nothing`
leave out their parts of the message. -/
def promoteShapeMismatch (a : Shape) (b : Option Shape) (i : Option Nat) : Err :=
  let conv := a.allOneTo && b.all Shape.allOneTo
  let a := if conv then a.toDims else a
  let b := if conv then b.map Shape.toDims else b
  let hasAxes := !(a.isDims && b.all Shape.isDims)
  let things := if hasAxes then "axes " else "size "
  .dimensionMismatch ("a has " ++ things ++ a.str hasAxes ++
    (match b with | some b => ", b has " ++ things ++ b.str hasAxes | none => "") ++
    (match i with | some i => s!", mismatch at dim {i}" | none => ""))

/-- The loops of `promote_shape(a::Dims, b::Dims)`, `base/indices.jl:179-185`, once
`a` has at least as many dimensions as `b`: `for i=1:length(b)` requires
`a[i] == b[i]` and `for i=length(b)+1:length(a)` requires `a[i] == 1`; the first
failing `i` is reported. -/
def promoteShapeDimsGe (a b : List Int) : RJ (List Int) :=
  if !(a.zip b).all (fun p => p.1 = p.2) then
    .error (promoteShapeMismatch (.dims a) (some (.dims b))
      (some (((a.zip b).findIdx fun p => p.1 ≠ p.2) + 1)))
  else if !(a.drop b.length).all (· = 1) then
    .error (promoteShapeMismatch (.dims a) none
      (some (((a.drop b.length).findIdx (· ≠ 1)) + b.length + 1)))
  else .ok a

/-- `promote_shape(a::Dims, b::Dims)`, `base/indices.jl:175-186`:
`length(a) < length(b)` returns `promote_shape(b, a)`. -/
def promoteShapeDims (a b : List Int) : RJ (List Int) :=
  if a.length < b.length then promoteShapeDimsGe b a else promoteShapeDimsGe a b

/-- `promote_shape(::Tuple{}, ::Tuple{}) = ()`, `base/indices.jl:108`. -/
def promoteShape00 : RJ (List Int) := .ok []

/-- `promote_shape(a::Tuple{Int,}, b::Tuple{Int,})`, `base/indices.jl:139-142`. -/
def promoteShape11 (a1 b1 : Int) : RJ (List Int) :=
  if a1 ≠ b1 then .error (promoteShapeMismatch (.dims [a1]) (some (.dims [b1])) none) else .ok [a1]

/-- `promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,})`, `base/indices.jl:144-147`. -/
def promoteShape21 (a1 a2 b1 : Int) : RJ (List Int) :=
  if a1 ≠ b1 ∨ a2 ≠ 1 then .error (promoteShapeMismatch (.dims [a1, a2]) (some (.dims [b1])) none)
  else .ok [a1, a2]

/-- `promote_shape(a::Tuple{Int,}, b::Tuple{Int,Int}) = promote_shape(b, a)`,
`base/indices.jl:149`. -/
def promoteShape12 (a1 b1 b2 : Int) : RJ (List Int) := promoteShape21 b1 b2 a1

/-- `promote_shape(a::Tuple{Int, Int}, b::Tuple{Int, Int})`, `base/indices.jl:151-154`. -/
def promoteShape22 (a1 a2 b1 b2 : Int) : RJ (List Int) :=
  if a1 ≠ b1 ∨ a2 ≠ b2 then .error (promoteShapeMismatch (.dims [a1, a2]) (some (.dims [b1, b2])) none)
  else .ok [a1, a2]

/-- `promote_shape` on `Dims`, dispatching to the most specific method. -/
def promoteShape (a b : List Int) : RJ (List Int) :=
  match a, b with
  | [], [] => promoteShape00
  | [a1], [b1] => promoteShape11 a1 b1
  | [a1, a2], [b1] => promoteShape21 a1 a2 b1
  | [a1], [b1, b2] => promoteShape12 a1 b1 b2
  | [a1, a2], [b1, b2] => promoteShape22 a1 a2 b1 b2
  | a, b => promoteShapeDims a b

/-- The loops of `promote_shape(a::Indices, b::Indices)`, `base/indices.jl:196-202`:
axes are compared as ranges (by their elements, `a[i] != b[i]`) and trailing axes
must equal `1:1`. -/
def promoteShapeAxesGe (a b : List UR) : RJ (List UR) :=
  if !(a.zip b).all (fun p => p.1.vals = p.2.vals) then
    .error (promoteShapeMismatch (.axes a) (some (.axes b))
      (some (((a.zip b).findIdx fun p => p.1.vals ≠ p.2.vals) + 1)))
  else if !(a.drop b.length).all (·.vals = [1]) then
    .error (promoteShapeMismatch (.axes a) none
      (some (((a.drop b.length).findIdx (·.vals ≠ [1])) + b.length + 1)))
  else .ok a

/-- `promote_shape(a::Indices, b::Indices)`, `base/indices.jl:192-203`:
`length(a) < length(b)` returns `promote_shape(b, a)`. -/
def promoteShapeAxes (a b : List UR) : RJ (List UR) :=
  if a.length < b.length then promoteShapeAxesGe b a else promoteShapeAxesGe a b

/-- `promote_shape(a::AbstractArray, b::AbstractArray) = promote_shape(axes(a), axes(b))`,
`base/indices.jl:188-190`; `ax` and `bx` are the arrays' axes. -/
def promoteShapeArrays (ax bx : List UR) : RJ (List UR) := promoteShapeAxes ax bx

/-! ## `setindex_shape_check`, `base/indices.jl:205-228` -/

/-- `_shapes_match(::Tuple{}, ::Tuple{}) = true`, `base/indices.jl:217`. -/
def shapesMatch00 : Bool := true

/-- `_shapes_match(a::Tuple, ::Tuple{}) = all(isone, a)`, `base/indices.jl:218`. -/
def shapesMatchA0 (a : List Int) : Bool := a.all (· = 1)

/-- `_shapes_match(::Tuple{}, b::Tuple) = all(isone, b)`, `base/indices.jl:219`. -/
def shapesMatch0B (b : List Int) : Bool := b.all (· = 1)

/-- `_shapes_match(a::Tuple, b::Tuple) = first(a) == first(b) && _shapes_match(tail(a),
tail(b))`, `base/indices.jl:220`, with the dispatch to the three methods above. -/
def shapesMatch : List Int → List Int → Bool
  | [], [] => shapesMatch00
  | x :: a, [] => shapesMatchA0 (x :: a)
  | [], y :: b => shapesMatch0B (y :: b)
  | x :: a, y :: b => x = y && shapesMatch a b

/-- `throw_setindex_mismatch(X, I)`, `base/indices.jl:205-212`. -/
def setindexMismatch (dims2string : List Int → String) (sx : List Int) (I : List Int) : Err :=
  match I with
  | [i] => .dimensionMismatch s!"tried to assign {sx.foldl (· * ·) 1} elements to {i} destinations"
  | _ => .dimensionMismatch s!"tried to assign {dims2string sx} array to {dims2string I} destination"

/-- `setindex_shape_check(X::AbstractArray, shape::Tuple{Vararg{Integer}})`,
`base/indices.jl:222-225`. -/
def setindexShapeCheck (dims2string : List Int → String) (sx : List Int) (shape : List Int) : RJ Bool :=
  let ok : Bool := if sx.length = 1 ∨ shape.length = 1 then
      decide (sx.foldl (· * ·) 1 = shape.foldl (· * ·) 1)
    else shapesMatch sx shape
  if ok then .ok true else .error (setindexMismatch dims2string sx shape)

/-- `setindex_shape_check(X::AbstractArray, i::Integer) = (length(X) == i || throw...)`,
`base/indices.jl:214-215`. -/
def setindexShapeCheck1 (dims2string : List Int → String) (sx : List Int) (i : Int) : RJ Bool :=
  if sx.foldl (· * ·) 1 = i then .ok true else .error (setindexMismatch dims2string sx [i])

/-- `setindex_shape_check(::Any, ::Tuple)`, `base/indices.jl:227-228`: a non-array
right-hand side. -/
def setindexShapeCheckScalar : RJ Bool :=
  .error (argErr "indexed assignment with a single value to possibly many locations is not supported")

/-! ## `to_index`, `to_indices`, `base/indices.jl:230-323` -/

/-- An index value given to `to_index`. -/
inductive IV where
  | int (i : I64)
  | integer (t : IntTy) (i : JInt t)
  | bool (b : Bool)
  | boolArr (bs : List Bool)
  | intArr (xs : List I64)
  | bottomArr
  | nestedArr
  | colon
  | other
  deriving DecidableEq, Repr

/-- A converted index: an `Int`, an array of `Int`s, or a `LogicalIndex` of a mask. -/
inductive CI where
  | int (i : I64)
  | arr (xs : List I64)
  | logical (mask : List Bool)
  deriving DecidableEq, Repr

/-- `to_index(i)`, `base/indices.jl:258-266`: `convert(Int, i)` for an integer (an
`InexactError` when it does not fit), `ArgumentError` for a `Bool`,
`LogicalIndex(I)` for a Bool array, an integer array or `Union{}[]` itself, and
`ArgumentError` for arrays of arrays or colons, `:` and any other value. -/
def toIndex : IV → RJ CI
  | .int i => .ok (.int i)
  | .integer t i =>
    match JInt.convert (IntTy.i64.name) .i64 i.val with
    | .ok j => .ok (.int j)
    | .error _ => .error (.jl (.inexactError "convert"))
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .boolArr bs => .ok (.logical bs)
  | .intArr xs => .ok (.arr xs)
  | .bottomArr => .ok (.arr [])
  | .nestedArr => .error (argErr "invalid index")
  | .colon => .error (argErr "colons must be converted by to_indices(...)")
  | .other => .error (argErr "invalid index")

/-- `to_index(A, i) = to_index(i)` (`base/indices.jl:243`) and
`to_index(A::Array, i::UInt) = reinterpret(Int, i)` (`:247`); `isArray` says whether
`A` is an `Array`. -/
def toIndexA (isArray : Bool) : IV → RJ CI
  | .integer .u64 i => if isArray then .ok (.int (JInt.wrap .i64 i.val)) else toIndex (.integer .u64 i)
  | i => toIndex i

/-- `to_indices(A, inds, I)`, `base/indices.jl:321-323`:
`(to_index(A, I[1]), to_indices(A, safe_tail(inds), tail(I))...)`. -/
def toIndicesInds (isArray : Bool) : List IV → RJ (List CI)
  | [] => .ok []
  | i :: rest => do
    let c ← toIndexA isArray i
    let cs ← toIndicesInds isArray rest
    pure (c :: cs)

/-- `to_indices(A, I::Tuple)`, `base/indices.jl:310-320`: `()` gives `()`, a tuple of
`Int`s is returned as is, a tuple of integers goes to `to_indices(A, (), I)`, and any
other tuple is processed with `axes(A)` (or with linear indices for one index, after
`_drop_zerodim`, which keeps every element of a tuple, `:314-315`). -/
def toIndices (isArray : Bool) (I : List IV) : RJ (List CI) :=
  if I.all (fun i => match i with | .int _ => true | _ => false) then
    .ok (I.filterMap fun i => match i with | .int j => some (.int j) | _ => none)
  else toIndicesInds isArray I

end JuliaLean.ReduceCov.Indices


/-! Row-level properties for `base/indices.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.IndicesEntries

open JuliaLean.ReduceCov
open JuliaLean.ReduceCov.Indices

/-! Each `to_index` overload has its own model. -/

def m243 (i : IV) : RJ CI := toIndex i
def m259 (b : Bool) : RJ CI := .error (argErr s!"invalid index: {b} of type Bool")
def m260 (bs : List Bool) : RJ CI := .ok (.logical bs)
def m261 (xs : List I64) : RJ CI := .ok (.arr xs)
def m262 : RJ CI := .ok (.arr [])
def m263 : RJ CI := .error (argErr "invalid index")
def m265 : RJ CI := .error (argErr "colons must be converted by to_indices(...)")
def m266 : RJ CI := .error (argErr "invalid index")

def m310 (drop : List IV → List IV) (route : List IV → List IV → RJ (List CI))
    (I : List IV) : RJ (List CI) := route (drop I) I
def m311 (linear : List IV) (route : List IV → List IV → RJ (List CI))
    (I : List IV) : RJ (List CI) := route linear I
def m312 (axes : List IV) (route : List IV → List IV → RJ (List CI))
    (I : List IV) : RJ (List CI) := route axes I
def m313 (fallback : List IV → RJ (List CI)) (J : List IV) : RJ (List CI) := fallback J
def m314 : List IV := []
def m315 : List IV → List IV
  | [] => []
  | i :: rest => i :: m315 rest
def m318 : RJ (List CI) := .ok []
def m319 (I : List I64) : RJ (List CI) := .ok (I.map CI.int)
def m320 (isArray : Bool) (I : List IV) : RJ (List CI) := toIndicesInds isArray I
def m321 : RJ (List CI) := .ok []
def m322 (isArray : Bool) : List IV → RJ (List CI)
  | [] => .ok []
  | i :: rest => do pure ((← toIndexA isArray i) :: (← m322 isArray rest))

end JuliaLean.ReduceCov.IndicesEntries
