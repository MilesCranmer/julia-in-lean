import JuliaLean.Core

/-!
# Model of `base/baseext.jl`

`VecElement` conversion is generic over Julia's `convert` and constructor methods. Array
constructors preserve the source's dimension-conversion order and call the existing array
constructor and fill behavior through explicit interfaces.
-/

namespace JuliaLean.base.baseext

/--
Julia source: base/baseext.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VecElement
```
-/

structure VecElement (T : Type) where
  value : T

def makeVecElement {T A E : Type} (convert : A → Except E T) (arg : A) :
    Except E (VecElement T) := do
  pure ⟨← convert arg⟩

/--
Julia source: base/baseext.jl:17-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VecElement{T}(arg) where {T} = VecElement{T}(convert(T, arg))
convert(::Type{T}, arg::T) where {T<:VecElement} = arg
convert(::Type{T}, arg)  where {T<:VecElement} = T(arg)::T
```
-/

def convertVecElementSame {T : Type} (arg : VecElement T) : VecElement T := arg

def convertVecElement {T A E : Type} (construct : A → Except E (VecElement T)) (arg : A) :
    Except E (VecElement T) := construct arg

structure ArrayCtorOps (Elem Dim Arr Val Err : Type) where
  anyElement : Elem
  nothingValue : Val
  missingValue : Val
  toInt : Dim → Except Err Int
  convertDims : List Dim → Except Err (List Int)
  undef : Elem → Nat → List Int → Except Err Arr
  undefRaw : Elem → Nat → List Dim → Except Err Arr
  fill : Arr → Val → Except Err Arr

/--
Julia source: base/baseext.jl:22-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Array{T,N}(::UndefInitializer, d::Vararg{Integer,N}) where {T,N} = Array{T,N}(undef, convert(Tuple{Vararg{Int}}, d))
# type but not dimensionality specified, accepting dims as series of Integers
Array{T}(::UndefInitializer, m::Integer) where {T} = Array{T,1}(undef, Int(m))
Array{T}(::UndefInitializer, m::Integer, n::Integer) where {T} = Array{T,2}(undef, Int(m), Int(n))
Array{T}(::UndefInitializer, m::Integer, n::Integer, o::Integer) where {T} = Array{T,3}(undef, Int(m), Int(n), Int(o))
Array{T}(::UndefInitializer, d::Integer...) where {T} = Array{T}(undef, convert(Tuple{Vararg{Int}}, d))
# dimensionality but not type specified, accepting dims as series of Integers
Vector(::UndefInitializer, m::Integer) = Vector{Any}(undef, Int(m))
Matrix(::UndefInitializer, m::Integer, n::Integer) = Matrix{Any}(undef, Int(m), Int(n))
# Dimensions as a single tuple
Array{T}(::UndefInitializer, d::NTuple{N,Integer}) where {T,N} = Array{T,N}(undef, convert(Tuple{Vararg{Int}}, d))
Array{T,N}(::UndefInitializer, d::NTuple{N,Integer}) where {T,N} = Array{T,N}(undef, convert(Tuple{Vararg{Int}}, d))
```
-/

def arrayUndefIntegerVararg {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (n : Nat) (dims : List Dim) : Except Err Arr := do
  let intDims ← ops.convertDims dims
  ops.undef element n intDims

def arrayUndefT1 {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (dim : Dim) : Except Err Arr := do
  let n ← ops.toInt dim
  ops.undef element 1 [n]

def arrayUndefT2 {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (m n : Dim) : Except Err Arr := do
  let m ← ops.toInt m
  let n ← ops.toInt n
  ops.undef element 2 [m, n]

def arrayUndefT3 {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (m n o : Dim) : Except Err Arr := do
  let m ← ops.toInt m
  let n ← ops.toInt n
  let o ← ops.toInt o
  ops.undef element 3 [m, n, o]

def arrayUndefGenericDims {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (dims : List Dim) : Except Err Arr := do
  let intDims ← ops.convertDims dims
  ops.undef element dims.length intDims

def vectorUndefAny {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (dim : Dim) : Except Err Arr := arrayUndefT1 ops ops.anyElement dim

def matrixUndefAny {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (m n : Dim) : Except Err Arr := arrayUndefT2 ops ops.anyElement m n

def arrayUndefTupleT {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (dims : List Dim) : Except Err Arr := arrayUndefGenericDims ops element dims

def arrayUndefTupleTN {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (n : Nat) (dims : List Dim) : Except Err Arr :=
  arrayUndefIntegerVararg ops element n dims

/--
Julia source: base/baseext.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Vector() = Vector{Any}(undef, 0)
```
-/

def emptyVector {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err) :
    Except Err Arr := ops.undef ops.anyElement 1 [0]

/--
Julia source: base/baseext.jl:39-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Array{T,N}(::Nothing, d...) where {T,N} = fill!(Array{T,N}(undef, d...), nothing)
Array{T,N}(::Missing, d...) where {T,N} = fill!(Array{T,N}(undef, d...), missing)
# type but not dimensionality specified
Array{T}(::Nothing, d...) where {T} = fill!(Array{T}(undef, d...), nothing)
Array{T}(::Missing, d...) where {T} = fill!(Array{T}(undef, d...), missing)
```
-/

def arrayNothingTN {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (n : Nat) (dims : List Dim) : Except Err Arr := do
  let array ← ops.undefRaw element n dims
  ops.fill array ops.nothingValue

def arrayMissingTN {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (n : Nat) (dims : List Dim) : Except Err Arr := do
  let array ← ops.undefRaw element n dims
  ops.fill array ops.missingValue

def arrayNothingT {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (dims : List Dim) : Except Err Arr :=
  arrayNothingTN ops element dims.length dims

def arrayMissingT {Elem Dim Arr Val Err : Type} (ops : ArrayCtorOps Elem Dim Arr Val Err)
    (element : Elem) (dims : List Dim) : Except Err Arr :=
  arrayMissingTN ops element dims.length dims

end JuliaLean.base.baseext

namespace JuliaLean.MiscCov.BaseExt

variable {V : Type}

/-- `VecElement{T}(arg) = VecElement{T}(convert(T, arg))`, `base/baseext.jl:17`; the
inner constructor stores the converted value. -/
def vecElement (convT : V → M V) (arg : V) : M V := convT arg

/-- `convert(::Type{T}, arg::T) where {T<:VecElement} = arg`, `base/baseext.jl:18`. -/
def convertSame (arg : V) : M V := .ok arg

/-- `convert(::Type{T}, arg) where {T<:VecElement} = T(arg)::T`, `base/baseext.jl:19`. -/
def convertOther (convT : V → M V) (arg : V) : M V := vecElement convT arg

/-- The `Integer` dimensions given to an `Array` constructor, as integers. -/
abbrev Dims := List Int

/-- `Int(m)` / `convert(Tuple{Vararg{Int}}, d)`: each dimension must fit in `Int`. -/
def toInt (m : Int) : M Int :=
  if -(2 ^ 63) ≤ m ∧ m < 2 ^ 63 then .ok m else .error .inexactError

def toInts : Dims → M (List Int)
  | [] => .ok []
  | m :: ms =>
    match toInt m with
    | .error e => .error e
    | .ok a =>
      match toInts ms with
      | .error e => .error e
      | .ok rest => .ok (a :: rest)

/-- An array: element type tag, dimensions, and elements (`none` is `#undef`). -/
structure Arr (V : Type) where
  eltype : String
  dims : List Int
  elems : List (Option V)

/-- The builtin `Array{T,N}(undef, dims::NTuple{N,Int})`: `ArgumentError` for a
negative dimension or an element count that does not fit (`2^62` here); elements
are uninitialized. -/
def core (T : String) (dims : List Int) : M (Arr V) :=
  if dims.any (· < 0) ∨ dims.foldl (· * ·) 1 ≥ 2 ^ 62 then .error (.argumentError "invalid GenericMemory size")
  else .ok ⟨T, dims, List.replicate (dims.foldl (· * ·) 1).toNat none⟩

/-- `Array{T,N}(::UndefInitializer, d::Vararg{Integer,N})`, `base/baseext.jl:22`; also
`Array{T}(undef, d::Integer...)` (`:27`), `Array{T}(undef, d::NTuple{N,Integer})` (`:32`)
and `Array{T,N}(undef, d::NTuple{N,Integer})` (`:33`): `convert(Tuple{Vararg{Int}}, d)`. -/
def undefN (T : String) (d : Dims) : M (Arr V) := do core T (← toInts d)

/-- `Array{T}(undef, m)` (`:24`), `(undef, m, n)` (`:25`), `(undef, m, n, o)` (`:26`): `Int(m)` each. -/
def undef1 (T : String) (m : Int) : M (Arr V) := do core T [← toInt m]
def undef2 (T : String) (m n : Int) : M (Arr V) := do core T [← toInt m, ← toInt n]
def undef3 (T : String) (m n o : Int) : M (Arr V) := do core T [← toInt m, ← toInt n, ← toInt o]

/-- `Vector(undef, m) = Vector{Any}(undef, Int(m))` (`:29`), `Matrix(undef, m, n)` (`:30`),
`Vector() = Vector{Any}(undef, 0)` (`:35`). -/
def vectorAny (m : Int) : M (Arr V) := undef1 "Any" m
def matrixAny (m n : Int) : M (Arr V) := undef2 "Any" m n
def vector0 : M (Arr V) := undef1 "Any" 0

/-- `fill!(A, x)`: every element becomes `convert(eltype(A), x)`. -/
def fill (convT : V → M V) (A : Arr V) (x : V) : M (Arr V) := do
  let y ← convT x
  pure { A with elems := A.elems.map (fun _ => some y) }

/-- `Array{T,N}(::Nothing, d...)`, `Array{T,N}(::Missing, d...)`, `Array{T}(::Nothing, d...)`,
`Array{T}(::Missing, d...)` (`:39-43`): `fill!(Array{T}(undef, d...), x)` with `x` the
singleton `nothing`/`missing`. -/
def filled (T : String) (convT : V → M V) (x : V) (d : Dims) : M (Arr V) := do
  fill convT (← undefN T d) x

end JuliaLean.MiscCov.BaseExt
