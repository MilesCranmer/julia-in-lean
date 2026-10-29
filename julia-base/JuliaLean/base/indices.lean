import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.promotion

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
def to_index_Integer {I : Type} (convert_Int : I → IndexResult I64) (i : I) : IndexResult I64 :=
  convert_Int i

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
def to_index {t : IntTy} (i : JInt t) : IndexResult I64 := to_index_Integer convert_Int_BitInteger i

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
def first_LinearIndices_1 {R AX : Type} [Inhabited R] (axes1 : R → AX) (first : AX → I64)
    (iter : LinearIndices R) : I64 :=
  first (axes1 iter.indices[0]!)

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
def last_LinearIndices_1 {R AX : Type} [Inhabited R] (axes1 : R → AX) (last : AX → I64)
    (iter : LinearIndices R) : I64 :=
  last (axes1 iter.indices[0]!)

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
  if iter.indices.length = 1 then first_LinearIndices_1 (AxisRange.axes1 C) (AxisRange.first C) iter
  else first_LinearIndices iter

/-- *dispatch*: `last(iter::LinearIndices)`: `base/indices.jl:529` for `LinearIndices{1}`,
`:528` for every other rank. -/
def last_LinearIndices_dispatch (C : RangeCallees) (length : LinearIndices AxisRange → I64)
    (iter : LinearIndices AxisRange) : I64 :=
  if iter.indices.length = 1 then last_LinearIndices_1 (AxisRange.axes1 C) (AxisRange.last C) iter
  else last_LinearIndices length iter

end JuliaLean.base.indices
