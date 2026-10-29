import JuliaLean.Core

/-!
# Model of `base/pair.jl`

`Pair A B` keeps the two field types separate. `PairType` represents a Julia pair type object,
and `Sum` represents the `Union{A, B}` returned by `eltype`. Calls to generic operators and
conversions are typed parameters, preserving Julia dispatch without importing later Base files.
The hash model accepts either Julia word width; the pinned target is 64-bit.
-/

namespace JuliaLean.base.pair

open JuliaLean

structure Pair (A B : Type) where
  first : A
  second : B

structure PairType where
  first : Type
  second : Type

inductive PairError where
  | julia (error : JlError)
  | typeError
  deriving Repr, DecidableEq

abbrev PairResult (α : Type) := Except PairError α

inductive BoolResult where
  | bool (value : Bool)
  | other
  deriving Repr, DecidableEq

def assertBool : BoolResult → PairResult Bool
  | .bool value => .ok value
  | .other => .error .typeError

inductive UIntWidth where
  | w32
  | w64
  deriving Repr, DecidableEq

namespace UIntWidth

def intTy : UIntWidth → IntTy
  | .w32 => .u32
  | .w64 => .u64

end UIntWidth

/-- Integer `getfield` on a pair: Julia field indices are one-based. -/
def getfieldInt {A B : Type} (p : Pair A B) (i : JInt .i64) : Jl (A ⊕ B) :=
  if i.val = 1 then .ok (.inl p.first)
  else if i.val = 2 then .ok (.inr p.second)
  else .error .boundsError

/--
`eltype` returns the union of a pair's two field types.

Julia source: base/pair.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(p::Type{Pair{A, B}}) where {A, B} = Union{A, B}
```
-/
def eltype (p : PairType) : Type := p.first ⊕ p.second

/--
`iterate` tests the state, then reads the field, then increments the state. The callbacks model
Julia's generic `>`, `getfield`, and `+` operations.

Julia source: base/pair.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(p::Pair, i=1) = i > 2 ? nothing : (getfield(p, i), i + 1)
```
-/
def iterate {A B I : Type} (greaterThanTwo : I → Jl Bool)
    (getfield : Pair A B → I → Jl (A ⊕ B)) (addOne : I → Jl I)
    (p : Pair A B) (i : I) : Jl (Option ((A ⊕ B) × I)) := do
  if ← greaterThanTwo i then pure none
  else pure (some ((← getfield p i), (← addOne i)))

/-- Call the optional-argument `iterate` method with Julia's default `i = 1`. -/
def iterateDefault {A B : Type} (greaterThanTwo : JInt .i64 → Jl Bool)
    (getfield : Pair A B → JInt .i64 → Jl (A ⊕ B))
    (addOne : JInt .i64 → Jl (JInt .i64)) (p : Pair A B) : Jl (Option ((A ⊕ B) × JInt .i64)) :=
  iterate greaterThanTwo getfield addOne p (JInt.lit .i64 1)

/--
`indexed_iterate` reads the selected field and increments its `Int` index; `state` is unused.

Julia source: base/pair.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexed_iterate(p::Pair, i::Int, state=1) = (getfield(p, i), i + 1)
```
-/
def indexedIterate {A B S : Type} (getfield : Pair A B → JInt .i64 → Jl (A ⊕ B))
    (addOne : JInt .i64 → Jl (JInt .i64)) (p : Pair A B) (i : JInt .i64)
    (_state : S) : Jl ((A ⊕ B) × JInt .i64) := do
  pure ((← getfield p i), (← addOne i))

/-- Call the optional-argument `indexed_iterate` method with its default `state = 1`. -/
def indexedIterateDefault {A B : Type}
    (getfield : Pair A B → JInt .i64 → Jl (A ⊕ B))
    (addOne : JInt .i64 → Jl (JInt .i64)) (p : Pair A B) (i : JInt .i64) :
    Jl ((A ⊕ B) × JInt .i64) :=
  indexedIterate getfield addOne p i (JInt.lit .i64 1)

/--
The pair hash seed depends on Julia's `UInt` width.

Julia source: base/pair.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let seed = (UInt === UInt64) ? 0x94cb2bb20a28ce96 : 0x1f60a087
```
-/
def hashSeed : (width : UIntWidth) → JInt width.intTy
  | .w32 => JInt.lit .u32 0x1f60a087
  | .w64 => JInt.lit .u64 0x94cb2bb20a28ce96

/--
Pair hashing xors the seed into the incoming hash, hashes `first`, then hashes `second`.

Julia source: base/pair.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(p::Pair, h::UInt) = hash(p.second, hash(p.first, xor(seed, h)))
```
-/
def hash {A B : Type} (width : UIntWidth)
    (xor : JInt width.intTy → JInt width.intTy → Jl (JInt width.intTy))
    (hashFirst : A → JInt width.intTy → Jl (JInt width.intTy))
    (hashSecond : B → JInt width.intTy → Jl (JInt width.intTy))
    (p : Pair A B) (h : JInt width.intTy) : Jl (JInt width.intTy) := do
  let salted ← xor (hashSeed width) h
  let firstHash ← hashFirst p.first salted
  hashSecond p.second firstHash

/--
Pair `==` computes each field comparison and combines the results with Julia's `&` operation.

Julia source: base/pair.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(p::Pair, q::Pair) = (p.first==q.first) & (p.second==q.second)
```
-/
def eq {A B C D R S U : Type} (eqFirst : A → C → Jl R) (eqSecond : B → D → Jl S)
    (bitAnd : R → S → Jl U) (p : Pair A B) (q : Pair C D) : Jl U := do
  let firstEq ← eqFirst p.first q.first
  let secondEq ← eqSecond p.second q.second
  bitAnd firstEq secondEq

/--
Pair `isequal` evaluates both field calls, asserts their `Bool` results, then combines them.

Julia source: base/pair.jl:50-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(p::Pair, q::Pair) = isequal(p.first,q.first)::Bool & isequal(p.second,q.second)::Bool
```
-/
def isequal {A B C D : Type} (eqFirst : A → C → PairResult BoolResult)
    (eqSecond : B → D → PairResult BoolResult)
    (p : Pair A B) (q : Pair C D) : PairResult Bool := do
  let firstValue ← eqFirst p.first q.first
  let firstEq ← assertBool firstValue
  let secondValue ← eqSecond p.second q.second
  let secondEq ← assertBool secondValue
  pure (firstEq && secondEq)

/--
Pair `isless` evaluates `isequal` and both `isless` calls before selecting the lexicographic result.

Julia source: base/pair.jl:52-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(p::Pair, q::Pair) = ifelse(!isequal(p.first,q.first), isless(p.first,q.first),
                                                             isless(p.second,q.second))
```
-/
def isless {A B C D : Type} (eqFirst : A → C → Jl Bool) (lessFirst : A → C → Jl Bool)
    (lessSecond : B → D → Jl Bool) (p : Pair A B) (q : Pair C D) : Jl Bool := do
  let firstEq ← eqFirst p.first q.first
  let firstLess ← lessFirst p.first q.first
  let secondLess ← lessSecond p.second q.second
  pure (if !firstEq then firstLess else secondLess)

/--
Integer Pair indexing delegates to `getfield`.

Julia source: base/pair.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(p::Pair,i::Int) = getfield(p,i)
```
-/
def getindexInt {A B : Type} (getfield : Pair A B → JInt .i64 → Jl (A ⊕ B))
    (p : Pair A B) (i : JInt .i64) : Jl (A ⊕ B) :=
  getfield p i

/--
Real Pair indexing converts to Julia `Int` before reading the field.

Julia source: base/pair.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(p::Pair,i::Real) = getfield(p, convert(Int, i))
```
-/
def getindexReal {A B X : Type} (convertInt : X → Jl (JInt .i64))
    (p : Pair A B) (i : X) : Jl (A ⊕ B) := do
  let intIndex ← convertInt i
  getfieldInt p intIndex

/--
Pair reversal swaps both values and their field types.

Julia source: base/pair.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(p::Pair{A,B}) where {A,B} = Pair{B,A}(p.second, p.first)
```
-/
def reverse {A B : Type} (p : Pair A B) : Pair B A := ⟨p.second, p.first⟩

/--
The first index of a pair is `1`.

Julia source: base/pair.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(p::Pair) = 1
```
-/
def firstindex {A B : Type} (_p : Pair A B) : JInt .i64 := JInt.lit .i64 1

/--
The last index of a pair is `2`.

Julia source: base/pair.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(p::Pair) = 2
```
-/
def lastindex {A B : Type} (_p : Pair A B) : JInt .i64 := JInt.lit .i64 2

/--
A pair has length `2`.

Julia source: base/pair.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(p::Pair) = 2
```
-/
def length {A B : Type} (_p : Pair A B) : JInt .i64 := JInt.lit .i64 2

/--
The first value of a pair is its `first` field.

Julia source: base/pair.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(p::Pair) = p.first
```
-/
def first {A B : Type} (p : Pair A B) : A := p.first

/--
The last value of a pair is its `second` field.

Julia source: base/pair.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(p::Pair) = p.second
```
-/
def last {A B : Type} (p : Pair A B) : B := p.second

/--
Conversion with an already matching target type returns the original pair.

Julia source: base/pair.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Pair{A,B}}, x::Pair{A,B}) where {A,B} = x
```
-/
def convertSame (target : PairType) (p : Pair target.first target.second) :
    Pair target.first target.second := p

/--
Otherwise Pair conversion checks and converts `first` before `second`, then builds the requested
pair type.

Julia source: base/pair.jl:65-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{Pair{A,B}}, x::Pair) where {A,B}
    a = getfield(x, :first)
    a isa A || (a = convert(A, a))
    b = getfield(x, :second)
    b isa B || (b = convert(B, b))
    return Pair{A,B}(a, b)::Pair{A,B}
end
```
-/
def convert (target : PairType) {X Y : Type}
    (isFirst : X → Bool) (upcastFirst : X → target.first)
    (convertFirst : X → Jl target.first)
    (isSecond : Y → Bool) (upcastSecond : Y → target.second)
    (convertSecond : Y → Jl target.second) (p : Pair X Y) :
    Jl (Pair target.first target.second) := do
  let firstValue ← if isFirst p.first then pure (upcastFirst p.first) else convertFirst p.first
  let secondValue ← if isSecond p.second then pure (upcastSecond p.second) else convertSecond p.second
  pure ⟨firstValue, secondValue⟩

/--
`promote_rule` promotes each pair field type independently.

Julia source: base/pair.jl:73-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Pair{A1,B1}}, ::Type{Pair{A2,B2}}) where {A1,B1,A2,B2} =
    Pair{promote_type(A1, A2), promote_type(B1, B2)}
```
-/
def promoteRule (promoteType : Type → Type → Type) (left right : PairType) : PairType :=
  ⟨promoteType left.first right.first, promoteType left.second right.second⟩

end JuliaLean.base.pair
