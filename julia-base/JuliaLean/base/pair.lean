import JuliaLean.Core
import JuliaLean.base.tuple

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


/-!
Model of `base/pair.jl` (master `bbfa0ce4150`).

A `Pair` holds two values of a universe `V`; element comparisons and hashing
are the abstract `Ops` of the tuple model (`none` is `missing` for `==`).
Types are an abstract `T` with `Union{A, B}` (`union`), `promote_type`
(`promote`), `isa` and `convert` (which may throw).
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds Ops Idx liftJ)

structure Pair (V : Type) where
  first : V
  second : V

namespace Pair

variable {V : Type}

/-- The fields as a tuple, for `getfield(p, i::Int)`. -/
def fields (p : Pair V) : List V := [p.first, p.second]

/-- `eltype(::Type{Pair{A, B}}) = Union{A, B}`, `base/pair.jl:40`. -/
def eltype {T : Type} (union : T → T → T) (A B : T) : T := union A B

/-- `iterate(p::Pair, i=1) = i > 2 ? nothing : (getfield(p, i), i + 1)`,
`base/pair.jl:41`. -/
def iterate (p : Pair V) (i : Int := 1) : R (Option (V × Int)) :=
  if i > 2 then .ok none else do
    let x ← getfield p.fields i
    pure (some (x, i + 1))

/-- `indexed_iterate(p::Pair, i::Int, state=1) = (getfield(p, i), i + 1)`,
`base/pair.jl:42`. -/
def indexedIterate (p : Pair V) (i : Int) : R (V × Int) := do
  let x ← getfield p.fields i
  pure (x, i + 1)

/-- The 64-bit seed of `hash(::Pair)`, `base/pair.jl:44`. -/
def hashSeed : Nat := 0x94cb2bb20a28ce96

/-- `hash(p::Pair, h::UInt) = hash(p.second, hash(p.first, xor(seed, h)))`,
`base/pair.jl:46`. -/
def hash (o : Ops V) (p : Pair V) (h : Nat) : Nat := o.hash p.second (o.hash p.first (hashSeed ^^^ h))

/-- Three-valued `&`: `false & x === false`, `missing & true === missing`. -/
def and3 : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- `==(p::Pair, q::Pair) = (p.first==q.first) & (p.second==q.second)`, `base/pair.jl:49`. -/
def eq (o : Ops V) (p q : Pair V) : Option Bool := and3 (o.eq p.first q.first) (o.eq p.second q.second)

/-- `isequal(p, q) = isequal(p.first,q.first)::Bool & isequal(p.second,q.second)::Bool`,
`base/pair.jl:50`. -/
def isequal (o : Ops V) (p q : Pair V) : Bool := o.isequal p.first q.first && o.isequal p.second q.second

/-- `isless(p, q) = ifelse(!isequal(p.first,q.first), isless(p.first,q.first),
isless(p.second,q.second))`, `base/pair.jl:52-53`. -/
def isless (o : Ops V) (p q : Pair V) : Bool :=
  if !o.isequal p.first q.first then o.isless p.first q.first else o.isless p.second q.second

/-- `getindex(p::Pair, i::Int) = getfield(p, i)`, `base/pair.jl:54`. -/
def getindexInt (p : Pair V) (i : Int) : R V := getfield p.fields i

/-- A `Real` index: an `Integer` (a `BitInteger` or `Bool`), a non-`Integer`
real with integer value `n` (such as `2.0`), or a non-`Integer` real that is
not an integer (such as `1.5`, `Inf` or `NaN`). -/
inductive RealIdx where
  | integer (i : Idx)
  | integral (n : Int)
  | fractional

/-- `convert(Int, x)` for a `Real`: `InexactError` outside `Int` or for a non-integer. -/
def RealIdx.toInt : RealIdx → R Int
  | .integer (.int _ v) => do let j ← liftJ (JInt.convert (IntTy.i64.name) .i64 v.val); pure j.val
  | .integer (.bool b) => .ok (if b then 1 else 0)
  | .integral n => do let j ← liftJ (JInt.convert (IntTy.i64.name) .i64 n); pure j.val
  | .fractional => .error (.jl (.inexactError "Int64"))

/-- `getindex(p::Pair, i::Real) = getfield(p, convert(Int, i))`, `base/pair.jl:55`;
an `Int` index takes the method of line 54. -/
def getindexReal (p : Pair V) : RealIdx → R V
  | .integer (.int .i64 v) => getindexInt p v.val
  | i => do let j ← i.toInt; getfield p.fields j

/-- `reverse(p::Pair{A,B}) = Pair{B,A}(p.second, p.first)`, `base/pair.jl:56`. -/
def reverse (p : Pair V) : Pair V := ⟨p.second, p.first⟩

/-- `firstindex(p) = 1`, `lastindex(p) = 2`, `length(p) = 2`, `first(p) = p.first`,
`last(p) = p.second`, `base/pair.jl:58-62`. -/
def firstindex (_ : Pair V) : Int := 1
def lastindex (_ : Pair V) : Int := 2
def length (_ : Pair V) : Int := 2
def firstOf (p : Pair V) : V := p.first
def lastOf (p : Pair V) : V := p.second

/-- `convert(::Type{Pair{A,B}}, x::Pair)`, `base/pair.jl:64-71`: `x` itself when
it already is a `Pair{A,B}` (`:64`), else each field is kept when it `isa` the
target and otherwise converted, first before second (`:65-71`). -/
def convert {T : Type} (isa : V → T → Bool) (conv : T → V → R V) (A B : T)
    (xIsAB : Bool) (x : Pair V) : R (Pair V) :=
  if xIsAB then .ok x else do
    let a ← if isa x.first A then pure x.first else conv A x.first
    let b ← if isa x.second B then pure x.second else conv B x.second
    pure ⟨a, b⟩

/-- `promote_rule(Pair{A1,B1}, Pair{A2,B2}) = Pair{promote_type(A1,A2), promote_type(B1,B2)}`,
`base/pair.jl:73-74`, on the type parameters. -/
def promoteRule {T : Type} (promote : T → T → T) (A1 B1 A2 B2 : T) : T × T :=
  (promote A1 A2, promote B1 B2)

end Pair

open Pair

variable {V : Type}

end JuliaLean.SortTuplesCov


/-! Generic and effect-aware models for the remaining `base/pair.jl` method
coverage findings. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean.Tuples (R Err)

structure HPair (A B : Type) where
  first : A
  second : B

/-- `iterate(p::Pair, i=1)`, `base/pair.jl:41`, with Julia's untyped state
represented by its `>`, field access, and `+` operations. -/
def pairIterateGeneric {P S V : Type} (greaterThanTwo : S → R Bool)
    (field : P → S → R V) (addOne : S → R S) (p : P) (state : S) :
    R (Option (V × S)) := do
  if ← greaterThanTwo state then pure none
  else pure (some ((← field p state), (← addOne state)))

/-- `indexed_iterate(p,i,state)`, `base/pair.jl:42`; `state` is accepted and
ignored. -/
def pairIndexedIterateGeneric {P I S V : Type} (field : P → I → R V)
    (addOne : I → R I) (p : P) (i : I) (_state : S) : R (V × I) := do
  pure ((← field p i), (← addOne i))

def uintModulus (bits : Nat) : Nat := 2 ^ bits
def pairHashSeed (bits : Nat) : Nat := if bits = 64 then 0x94cb2bb20a28ce96 else 0x1f60a087

/-- `hash(p::Pair,h::UInt)`, `base/pair.jl:44-46`, with fixed-width UInt
wrapping and both architecture-specific seeds. -/
def pairHashFixed {A B : Type} (bits : Nat) (hashA : A → Nat → Nat)
    (hashB : B → Nat → Nat) (p : HPair A B) (h : Nat) : Nat :=
  let seed := (pairHashSeed bits ^^^ h) % uintModulus bits
  hashB p.second (hashA p.first seed % uintModulus bits) % uintModulus bits

/-- Eager `isequal` and `isless`, `base/pair.jl:50,52-53`. -/
def pairIsequalEager {A B : Type} (eqA : A → A → R Bool)
    (eqB : B → B → R Bool) (p q : HPair A B) : R Bool := do
  let a ← eqA p.first q.first
  let b ← eqB p.second q.second
  pure (a && b)

def pairIslessEager {A B : Type} (equalA : A → A → R Bool)
    (lessA : A → A → R Bool) (lessB : B → B → R Bool)
    (p q : HPair A B) : R Bool := do
  let eq ← equalA p.first q.first
  let firstLess ← lessA p.first q.first
  let secondLess ← lessB p.second q.second
  pure (if !eq then firstLess else secondLess)

/-- `getindex(p,i::Int)` and the Real overload, `base/pair.jl:54-55`. -/
def pairGetindexInt {V : Type} (p : HPair V V) (i : Int) : R V :=
  if i = 1 then .ok p.first else if i = 2 then .ok p.second else .error (.jl .boundsError)
def pairGetindexRealGeneric {X V : Type} (convertInt : X → R Int)
    (p : HPair V V) (i : X) : R V := do
  pairGetindexInt p (← convertInt i)

/-- Typed reverse, `base/pair.jl:56`. -/
def reverseHPair {A B : Type} (p : HPair A B) : HPair B A := ⟨p.second, p.first⟩

structure TypedPair (T V : Type) where
  firstType : T
  secondType : T
  first : V
  second : V

/-- Heterogeneous target conversion, `base/pair.jl:65-71`, including the
target Pair type carried by the result. -/
def convertTypedPair {T V : Type} (isa : V → T → Bool) (convert : T → V → R V)
    (A B : T) (p : HPair V V) : R (TypedPair T V) := do
  let a ← if isa p.first A then pure p.first else convert A p.first
  let b ← if isa p.second B then pure p.second else convert B p.second
  pure ⟨A, B, a, b⟩

end JuliaLean.SortTuplesCov
