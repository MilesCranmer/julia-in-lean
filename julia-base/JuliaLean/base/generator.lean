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
def iterateGenerator {m : Type → Type} [Monad m] {I F A B Args Y State : Type}
    (apply : F → A → m B)
    (iterate : I → Args → m (Option Y)) (assertPair : Y → m (A × State))
    (g : Generator I F) (state : Args) : m (Option (B × State)) := do
  match ← iterate g.iter state with
  | none => pure none
  | some raw =>
      let pair ← assertPair raw
      pure (some (← apply g.f pair.1,pair.2))

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
/-!
# Shared model for the method coverage of `base/iterators.jl`,
`base/generator.jl`, `base/anyall.jl` and `base/simdloop.jl` (master `bbfa0ce4150`)

A Julia iterator is an `It`: the two `iterate` methods (`first` is
`iterate(itr)`, `next s` is `iterate(itr, s)`), the type-level traits
(`IteratorSize`, `IteratorEltype`, `eltype` of `typeof(itr)`), `length`,
`size` and the two `isdone` methods. Iteration states are Julia values (`V`),
exactly as Julia's states are ordinary objects such as `(n, inner_state)`.
Wrappers (`Take`, `Zip`, ...) are functions `It → It` whose fields mirror the
Julia methods of the wrapper type.

`Yields it xs`: iterating `it` produces exactly `xs` and then `nothing`.
`Pre it xs`: `xs` is a prefix of what `it` produces (all steps succeed).
`Endless it`: `it` produces arbitrarily many elements.

Julia exceptions are `E.jl`; `E.typeError` is `TypeError` (a non-`Bool` in a
boolean context or a failed type assertion), `E.eof` is `EOFError`, and
`E.fuel` is the model-only result of a loop bound being reached (never a
Julia result).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Julia values. Iteration states are values too. `vec` is a `Vector`,
`tup` a `Tuple`, `pair k v` is `k => v`, `str s` a `String` (as its
characters), `obj n` any other object. -/
inductive V where
  | int (x : Int)
  | bool (b : Bool)
  | missing
  | nothing
  | sym (s : String)
  | chr (c : Nat)
  | tup (vs : List V)
  | vec (vs : List V)
  | pair (k v : V)
  | obj (n : Nat)
  deriving Repr, Inhabited

/-- Julia exceptions, plus the model-only `fuel`. -/
inductive E where
  | jl (e : JlError)
  | typeError
  | eof
  | simdError (msg : String)
  | dimensionMismatch
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except E α

/-- `throw(e)` for a Julia exception. -/
def jthrow {α : Type} (e : JlError) : R α := .error (.jl e)

/-- The result of one `iterate` call: `nothing` or `(value, state)`. -/
abbrev Step := R (Option (V × V))

/-- `Int64` literal. -/
abbrev i64 (x : Int) : JInt64 := JInt.lit .i64 x

/-- `Base.IteratorSize` values, base/generator.jl:63-67. -/
inductive Isz where
  | sizeUnknown
  | hasLength
  | hasShape (n : Nat)
  | isInfinite
  deriving Repr, DecidableEq, Inhabited

/-- `HasLength` or `HasShape`: a length is promised. -/
def Isz.finite : Isz → Bool
  | .hasLength | .hasShape _ => true
  | _ => false

/-- The part of a Julia type the iterator methods inspect: `tuple ts` is
`Tuple{ts...}`, `vararg t` is `Tuple{Vararg{t}}`, `vector t` is `Vector{t}`,
`pair k v` is `Pair{k, v}`, `bottom` is `Union{}`, `union a b` is
`Union{a, b}`, `char` is `Char`. -/
inductive Ty where
  | any
  | bottom
  | int
  | bool
  | missing
  | nothing
  | sym
  | char
  | obj
  | tuple (ts : List Ty)
  | vararg (t : Ty)
  | vector (t : Ty)
  | pair (k v : Ty)
  | union (a b : Ty)
  deriving Repr, Inhabited

mutual
/-- `v isa T`. -/
def Ty.mem : Ty → V → Prop
  | .any, _ => True
  | .bottom, _ => False
  | .int, v => ∃ x, v = .int x
  | .bool, v => ∃ b, v = .bool b
  | .missing, v => v = .missing
  | .nothing, v => v = .nothing
  | .sym, v => ∃ s, v = .sym s
  | .char, v => ∃ c, v = .chr c
  | .obj, v => ∃ n, v = .obj n
  | .tuple ts, v => ∃ vs, v = .tup vs ∧ Ty.memList ts vs
  | .vararg t, v => ∃ vs, v = .tup vs ∧ ∀ x ∈ vs, t.mem x
  | .vector t, v => ∃ vs, v = .vec vs ∧ ∀ x ∈ vs, t.mem x
  | .pair k w, v => ∃ a b, v = .pair a b ∧ k.mem a ∧ w.mem b
  | .union a b, v => a.mem v ∨ b.mem v
/-- Componentwise `isa` for tuple fields. -/
def Ty.memList : List Ty → List V → Prop
  | [], [] => True
  | t :: ts, v :: vs => t.mem v ∧ Ty.memList ts vs
  | _, _ => False
end

/-- A Julia iterator object as seen through its methods. The defaults are
Julia's fallbacks: `IteratorSize` `HasLength()`, `IteratorEltype`
`HasEltype()`, `eltype` `Any`, `isdone` `missing` (base/essentials.jl), and a
`MethodError` for `length` and `size`. -/
structure It where
  /-- `iterate(itr)`. -/
  first : Step
  /-- `iterate(itr, s)`. -/
  next : V → Step
  /-- `IteratorSize(typeof(itr))`. -/
  isz : Isz := .hasLength
  /-- `IteratorEltype(typeof(itr)) === HasEltype()`. -/
  iel : Bool := true
  /-- `eltype(typeof(itr))`. -/
  elt : Ty := .any
  /-- `length(itr)`. -/
  len : R JInt64 := jthrow (.methodError "length")
  /-- `size(itr)`. -/
  size : R (List JInt64) := jthrow (.methodError "size")
  /-- `isdone(itr)`; `none` is `missing`. -/
  done0 : R (Option Bool) := .ok none
  /-- `isdone(itr, s)`; `none` is `missing`. -/
  doneS : V → R (Option Bool) := fun _ => .ok none
  /-- `last(itr)`. -/
  lastv : R V := jthrow (.methodError "last")

/-- `min(x, y)` on `Int`: `ifelse(y < x, y, x)` (base/promotion.jl). -/
def jmin (x y : JInt64) : JInt64 := if y < x then y else x

/-- `max(x, y)` on `Int`: `ifelse(y < x, x, y)` (base/promotion.jl). -/
def jmax (x y : JInt64) : JInt64 := if y < x then x else y

end JuliaLean.IteratorsCov


/-!
# `Generator` and iterator traits (`base/generator.jl`)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- The body of `iterate(g::Generator, s...)`, `base/generator.jl:44-50`. -/
def generatorStep (f : V → V) : Step → Step
  | .ok (some (x, s)) => .ok (some (f x, s))
  | y => y

/-- `Generator(f, iter)` together with all one-line delegating methods at
`base/generator.jl:52-59`. -/
def generatorIt (f : V → V) (it : It) : It where
  first := generatorStep f it.first
  next := fun s => generatorStep f (it.next s)
  isz := it.isz
  iel := false
  elt := .any
  len := it.len
  size := it.size
  done0 := it.done0
  doneS := it.doneS
  lastv := it.lastv.map f

/-- `Generator(f, I1, I2, Is...) = Generator(splat(f), zip(...))`, line 37.
The dynamic model receives the splatted function on the tuple value. -/
def generatorMany (zipIt : List It → It) (f : List V → V) (its : List It) : It :=
  generatorIt (fun | .tup xs => f xs | x => f [x]) (zipIt its)

/-- The one-line delegation methods at lines 52-59. Their arguments are the
results of calling the corresponding method on `g.iter`. -/
def generatorLength (inner : R JInt64) : R JInt64 := inner
def generatorSize (inner : R (List JInt64)) : R (List JInt64) := inner
def generatorAxes (inner : R (List JInt64)) : R (List JInt64) := inner
def generatorNdims (inner : R JInt64) : R JInt64 := inner
def generatorKeys (inner : R (List V)) : R (List V) := inner
def generatorLast (f : V → V) (inner : R V) : R V := inner.map f
def generatorIsempty (inner : R Bool) : R Bool := inner
def generatorIsdone (inner : R (Option Bool)) : R (Option Bool) := inner

/-- The constructor's function-field representation at lines 39-42. -/
inductive GeneratorFunctionTag where
  | value | freeType | egalType
  deriving Repr, DecidableEq

def generatorTypeTag (hasFreeTypevars : Bool) : GeneratorFunctionTag :=
  if hasFreeTypevars then .freeType else .egalType

/-- Type shapes dispatched on by `IteratorSize`, lines 95-104. -/
inductive IteratorType where
  | bottom | any | tuple | array (rank : Nat) | generator (inner : Option Isz) | other
  deriving Repr, DecidableEq

/-- `IteratorSize(x)` calls the type method; `IteratorSize(::Type)` defaults
to HasLength; Bottom throws; Any is SizeUnknown; tuples, arrays and generators
take their source branches (`base/generator.jl:95-104`). -/
def iteratorSizeType : IteratorType → R Isz
  | .bottom => jthrow (.argumentError "Union{} does not have elements")
  | .any => .ok .sizeUnknown
  | .tuple => .ok .hasLength
  | .array rank => .ok (.hasShape rank)
  | .generator none => .ok .sizeUnknown
  | .generator (some inner) => .ok inner
  | .other => .ok .hasLength

def iteratorSizeValue (typeOf : α → IteratorType) (x : α) : R Isz :=
  iteratorSizeType (typeOf x)

/-- `haslength(iter)`, line 104. -/
def hasLengthTrait (size : R Isz) : Bool :=
  match size with
  | .ok .hasLength | .ok (.hasShape _) => true
  | _ => false

/-- Type shapes dispatched on by `IteratorEltype`, lines 129-134. -/
inductive EltypeIteratorType where
  | bottom | any | generator | other
  deriving Repr, DecidableEq

def iteratorEltypeType : EltypeIteratorType → R Bool
  | .bottom => jthrow (.argumentError "Union{} does not have elements")
  | .any | .generator => .ok false
  | .other => .ok true

def iteratorEltypeValue (typeOf : α → EltypeIteratorType) (x : α) : R Bool :=
  iteratorEltypeType (typeOf x)
end JuliaLean.IteratorsCov
