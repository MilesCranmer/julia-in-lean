import JuliaLean.Core

/-!
# Model of `base/generator.jl`

Typed models of Julia generators and iterator traits at
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Julia values and iterator state
are represented by typed parameters. `IteratorType` records the type cases
needed to model Julia's trait dispatch.
-/

namespace JuliaLean.base.generator

open JuliaLean

inductive IteratorType where
  | unionBottom
  | any
  | tuple
  | abstractArray (dimensions : Nat)
  | generator (inner : Option IteratorType)
  | other
  deriving Repr, Inhabited

/-- The result of one call to an iterator's `iterate` method. -/
inductive IteratorStep (A State : Type) where
  | done
  | yielded (value : A) (state : State)
  /-- A non-`nothing` result that fails the `Tuple{Any,Any}` assertion. -/
  | malformed

/-- Exceptions from the inner iterator and the `Tuple{Any,Any}` assertion. -/
inductive GeneratorError where
  | iterator (error : JlError)
  | tupleTypeAssertion

/-- `Core.TypeEgal{T}` versus `typeof(T)` in the type-valued Generator constructor. -/
inductive GeneratorTypeFunction (T : Type) where
  | typeValue (value : T)
  | typeEgal (value : T)

/--
Julia source: base/generator.jl:3-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Generator(f, iter)

Given a function `f` and an iterator `iter`, construct an iterator that yields
the values of `f` applied to the elements of `iter`.
The syntax `f(x) for x in iter` is syntax for constructing an instance of this
type.

```jldoctest
julia> g = (abs2(x) for x in 1:5);

julia> for x in g
           println(x)
       end
1
4
9
16
25

julia> collect(g)
5-element Vector{Int64}:
  1
  4
  9
 16
 25
```
"""
struct Generator{I,F}
    f::F
    iter::I
end
````
-/
structure Generator (I F : Type) where
  f : F
  iter : I

/--
Julia source: base/generator.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Generator(f, I1, I2, Is...) = Generator(splat(f), zip(I1, I2, Is...))
```
-/
def generatorMany {F G I1 I2 Rest It : Type}
    (splat : F → G) (zip : I1 → I2 → Rest → It)
    (f : F) (i1 : I1) (i2 : I2) (rest : Rest) : Generator It G :=
  ⟨splat f, zip i1 i2 rest⟩

/--
Julia source: base/generator.jl:39-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Generator(::Type{T}, iter::I) where {T,I} =
    Generator{I,has_free_typevars(T) ? typeof(T) : Core.TypeEgal{T}}(T, iter)
```
-/
def generatorFromType {I T : Type}
    (hasFreeTypevars : T → Bool) (typeValue : T) (iter : I) :
    Generator I (GeneratorTypeFunction T) :=
  ⟨if hasFreeTypevars typeValue then .typeValue typeValue else .typeEgal typeValue, iter⟩

/--
Julia source: base/generator.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Generator(::Type{T}, I1, I2, Is...) where {T} = Generator(splat(T), zip(I1, I2, Is...))
```
-/
def generatorTypeMany {T G I1 I2 Rest It : Type}
    (splat : T → G) (zip : I1 → I2 → Rest → It)
    (typeValue : T) (i1 : I1) (i2 : I2) (rest : Rest) : Generator It G :=
  ⟨splat typeValue, zip i1 i2 rest⟩

/--
Julia source: base/generator.jl:44-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(g::Generator, s...)
    @inline
    y = iterate(g.iter, s...)
    y === nothing && return nothing
    y = y::Tuple{Any, Any} # try to give inference some idea of what to expect about the behavior of the next line
    return (g.f(y[1]), y[2])
end
```
-/
def iterateGenerator {I F A B Args : Type} {State : Type}
    (apply : F → A → B)
    (iterate : I → Args → Jl (IteratorStep A State))
    (g : Generator I F) (state : Args) : Except GeneratorError (Option (B × State)) :=
  match iterate g.iter state with
  | .error error => .error (.iterator error)
  | .ok .done => .ok none
  | .ok .malformed => .error .tupleTypeAssertion
  | .ok (.yielded value next) => .ok (some (apply g.f value, next))

/--
Julia source: base/generator.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(g::Generator) = length(g.iter)
```
-/
def generatorLength {I F R : Type} (length : I → R) (g : Generator I F) : R :=
  length g.iter

/--
Julia source: base/generator.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(g::Generator) = size(g.iter)
```
-/
def generatorSize {I F R : Type} (size : I → R) (g : Generator I F) : R :=
  size g.iter

/--
Julia source: base/generator.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(g::Generator) = axes(g.iter)
```
-/
def generatorAxes {I F R : Type} (axes : I → R) (g : Generator I F) : R :=
  axes g.iter

/--
Julia source: base/generator.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(g::Generator) = ndims(g.iter)
```
-/
def generatorNdims {I F R : Type} (ndims : I → R) (g : Generator I F) : R :=
  ndims g.iter

/--
Julia source: base/generator.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(g::Generator) = keys(g.iter)
```
-/
def generatorKeys {I F R : Type} (keys : I → R) (g : Generator I F) : R :=
  keys g.iter

/--
Julia source: base/generator.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(g::Generator) = g.f(last(g.iter))
```
-/
def generatorLast {I F A B : Type}
    (last : I → Jl A) (apply : F → A → B) (g : Generator I F) : Jl B := do
  let value ← last g.iter
  pure (apply g.f value)

/--
Julia source: base/generator.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(g::Generator) = isempty(g.iter)
```
-/
def generatorIsempty {I F R : Type} (isempty : I → R) (g : Generator I F) : R :=
  isempty g.iter

/--
Julia source: base/generator.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(g::Generator, state...) = isdone(g.iter, state...)
```
-/
def generatorIsdone {I F Args R : Type}
    (isdone : I → Args → R) (g : Generator I F) (state : Args) : R :=
  isdone g.iter state

/--
Julia source: base/generator.jl:63-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type IteratorSize end
struct SizeUnknown <: IteratorSize end
struct HasLength <: IteratorSize end
struct HasShape{N} <: IteratorSize end
struct IsInfinite <: IteratorSize end
```
-/
inductive IteratorSize where
  | sizeUnknown
  | hasLength
  | hasShape (dimensions : Nat)
  | isInfinite
  deriving Repr, DecidableEq, Inhabited

/--
Julia source: base/generator.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type) = HasLength()  # HasLength is the default
```
-/
def iteratorSizeDefault (_type : IteratorType) : Jl IteratorSize :=
  .ok .hasLength

/--
Julia source: base/generator.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Union{}}, slurp...) = throw(ArgumentError("Union{} does not have elements"))
```
-/
def iteratorSizeUnionBottom {Arg : Type} (_slurp : List Arg) : Jl IteratorSize :=
  .error (.argumentError "Union{} does not have elements")

/--
Julia source: base/generator.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Any}) = SizeUnknown()
```
-/
def iteratorSizeAny (_type : IteratorType) : Jl IteratorSize :=
  .ok .sizeUnknown

/--
Julia source: base/generator.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Tuple}) = HasLength()
```
-/
def iteratorSizeTuple (_type : IteratorType) : Jl IteratorSize :=
  .ok .hasLength

/--
Julia source: base/generator.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:AbstractArray{<:Any,N}})  where {N} = HasShape{N}()
```
-/
def iteratorSizeArray (dimensions : Nat) : Jl IteratorSize :=
  .ok (.hasShape dimensions)

mutual
/--
Julia source: base/generator.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Generator{I}}) where {I} = (@isdefined I) ? IteratorSize(I) : SizeUnknown()
```
-/
def iteratorSizeGenerator (inner : Option IteratorType) : Jl IteratorSize :=
  match inner with
  | some iteratorType => iteratorSizeType iteratorType
  | none => .ok .sizeUnknown

def iteratorSizeType : IteratorType → Jl IteratorSize
  | .unionBottom => iteratorSizeUnionBottom (Arg := Unit) []
  | .any => iteratorSizeAny .any
  | .tuple => iteratorSizeTuple .tuple
  | .abstractArray dimensions => iteratorSizeArray dimensions
  | .generator inner => iteratorSizeGenerator inner
  | .other => iteratorSizeDefault .other
end
/--
Julia source: base/generator.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(x) = IteratorSize(typeof(x))
```
-/
def iteratorSizeValue {I : Type} (typeof : I → IteratorType) (x : I) : Jl IteratorSize :=
  iteratorSizeType (typeof x)

/--
Julia source: base/generator.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haslength(iter) = IteratorSize(iter) isa Union{HasShape, HasLength}
```
-/
def haslength {I : Type} (iteratorSize : I → Jl IteratorSize) (iter : I) : Jl Bool := do
  let trait ← iteratorSize iter
  pure (match trait with
    | .hasLength | .hasShape _ => true
    | _ => false)

/--
Julia source: base/generator.jl:106-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type IteratorEltype end
struct EltypeUnknown <: IteratorEltype end
struct HasEltype <: IteratorEltype end
```
-/
inductive IteratorEltype where
  | eltypeUnknown
  | hasEltype
  deriving Repr, DecidableEq, Inhabited

/--
Julia source: base/generator.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type) = HasEltype()  # HasEltype is the default
```
-/
def iteratorEltypeDefault (_type : IteratorType) : Jl IteratorEltype :=
  .ok .hasEltype

/--
Julia source: base/generator.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Union{}}, slurp...) = throw(ArgumentError("Union{} does not have elements"))
```
-/
def iteratorEltypeUnionBottom {Arg : Type} (_slurp : List Arg) : Jl IteratorEltype :=
  .error (.argumentError "Union{} does not have elements")

/--
Julia source: base/generator.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Any}) = EltypeUnknown()
```
-/
def iteratorEltypeAny (_type : IteratorType) : Jl IteratorEltype :=
  .ok .eltypeUnknown

/--
Julia source: base/generator.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Generator{I,T}}) where {I,T} = EltypeUnknown()
```
-/
def iteratorEltypeGenerator (_type : IteratorType) : Jl IteratorEltype :=
  .ok .eltypeUnknown

def iteratorEltypeType : IteratorType → Jl IteratorEltype
  | .unionBottom => iteratorEltypeUnionBottom (Arg := Unit) []
  | .any => iteratorEltypeAny .any
  | .generator _ => iteratorEltypeGenerator (.generator none)
  | type => iteratorEltypeDefault type
/--
Julia source: base/generator.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(x) = IteratorEltype(typeof(x))
```
-/
def iteratorEltypeValue {I : Type} (typeof : I → IteratorType) (x : I) : Jl IteratorEltype :=
  iteratorEltypeType (typeof x)

end JuliaLean.base.generator
