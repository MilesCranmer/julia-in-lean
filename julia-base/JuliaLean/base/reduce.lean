import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.number

/-!
# Typed model of `base/reduce.jl`

The iterator model uses lists. `Reducer` carries the typed accumulator/input interface and the
single-element and empty-iterator behavior selected by Julia dispatch. Array indexing uses a typed
getter and an inclusive index interval. Bool-array lists are immutable snapshots of byte storage:
`wordAt i` is the `unsafe_load(Ptr{UInt}(pointer(x)), i)` read of the same storage. `GC.@preserve`
has no observable effect on these immutable reads.

`MappingIdentity` records the callable identity selected by Julia dispatch. A mapped empty call keeps
the neutral element's type separate from the mapping's result type.
-/

namespace JuliaLean.base.reduce

open JuliaLean

inductive FoldInit (α : Type) where
  | initial
  | value (x : α)
  deriving Repr

inductive MappingIdentity where
  | identity | abs | abs2 | other
  deriving Repr, DecidableEq

inductive IdentityFn where
  | identity
  deriving Repr, DecidableEq

inductive AbsFn where
  | abs
  deriving Repr, DecidableEq

inductive Abs2Fn where
  | abs2
  deriving Repr, DecidableEq

class AbsCallable (α : Type) (β : outParam Type) where
  abs : α → β

instance {t : IntTy} : AbsCallable (JInt t) (JInt t) where
  abs := JuliaLean.base.int.abs

instance {t : JuliaLean.base.float.FTy} :
    AbsCallable (JuliaLean.base.float.FV t) (JuliaLean.base.float.FV t) where
  abs := JuliaLean.base.float.abs_IEEEFloat

class Abs2Callable (α : Type) (β : outParam Type) where
  abs2 : α → β

instance {t : IntTy} : Abs2Callable (JInt t) (JInt t) where
  abs2 := fun x => JuliaLean.base.int.mul x x

instance {t : JuliaLean.base.float.FTy} :
    Abs2Callable (JuliaLean.base.float.FV t) (JuliaLean.base.float.FV t) where
  abs2 := fun x => JuliaLean.base.float.mul_IEEEFloat x x

class MapCallable (F : Type) (Input : Type) (Output : outParam Type) where
  apply : F → Input → Output
  mappingKind : F → MappingIdentity := fun _ => .other
  isIdentity : F → Bool := fun _ => false
  identityTypes : ∀ f, isIdentity f = true → Input = Output := by intros; contradiction
  identityValues : ∀ f x, isIdentity f = true → HEq (apply f x) x := by intros; contradiction

instance {Input Output : Type} : MapCallable (Input → Output) Input Output where
  apply := fun f x => f x

instance {α : Type} : MapCallable IdentityFn α α where
  apply := fun _ x => x
  mappingKind := fun _ => .identity
  isIdentity := fun f => f == .identity
  identityTypes := fun _ _ => rfl
  identityValues := fun _ _ _ => HEq.rfl

structure IdentityMapper (α : Type) where
  fn : α → α

instance {α : Type} : MapCallable (IdentityMapper α) α α where
  apply := fun _ x => x
  mappingKind := fun _ => .identity
  isIdentity := fun _ => true
  identityTypes := fun _ _ => rfl
  identityValues := fun _ _ _ => HEq.rfl

instance {α β : Type} [AbsCallable α β] : MapCallable AbsFn α β where
  apply := fun _ x => AbsCallable.abs x
  mappingKind := fun _ => .abs

instance {α β : Type} [Abs2Callable α β] : MapCallable Abs2Fn α β where
  apply := fun _ x => Abs2Callable.abs2 x
  mappingKind := fun _ => .abs2

/-- Calls to the selected methods from other Base files, on the accumulator's type. -/
class EmptyMappingOps (Acc : Type) where
  abs : Acc → Jl Acc
  abs2 : Acc → Jl Acc
  zero : Jl Acc

instance (priority := 0) {Acc : Type} : EmptyMappingOps Acc where
  abs := fun _ => .error (.methodError "abs")
  abs2 := fun _ => .error (.methodError "abs2")
  zero := .error (.methodError "zero")

instance {t : IntTy} : EmptyMappingOps (JInt t) where
  abs := fun x => .ok (JuliaLean.base.int.abs x)
  abs2 := JuliaLean.base.number.abs2Real (fun x y => .ok (JuliaLean.base.int.mul x y))
  zero := .ok (JuliaLean.base.int.lit t 0)

instance {t : JuliaLean.base.float.FTy} : EmptyMappingOps (JuliaLean.base.float.FV t) where
  abs := fun x => .ok (JuliaLean.base.float.abs_IEEEFloat x)
  abs2 := JuliaLean.base.number.abs2Real (fun x y => .ok (JuliaLean.base.float.mul_IEEEFloat x y))
  zero := .ok (JuliaLean.base.float.zero_float t)

inductive JIterator : Type → Type 1 where
  | values {α : Type} (xs : List α) : JIterator α
  | generator {F α β : Type} [MapCallable F α β] (f : F) (itr : JIterator α) : JIterator β
  | filter {α : Type} (predicate : α → Bool) (itr : JIterator α) : JIterator α
  | flatten {α : Type} (itr : JIterator (List α)) : JIterator α

def iteratorValues {α : Type} : JIterator α → List α
  | .values xs => xs
  | @JIterator.generator F _ _ _ f itr =>
      (iteratorValues itr).map (MapCallable.apply (F := F) f)
  | .filter predicate itr => (iteratorValues itr).filter predicate
  | .flatten itr => (iteratorValues itr).flatten

structure EmptyReducer (Result : Type) where
  empty : Jl Result

structure MappingEmptyCall (Result : Type) where
  Arg : Type
  emptyOp : EmptyReducer Arg
  apply : Arg → Jl Result
  zero : Jl Arg


structure Reducer (Acc Input : Type) where
  first : Input → FoldInit Acc
  step : FoldInit Acc → Input → FoldInit Acc
  empty : Jl Acc
  mappingAbs : MappingEmptyCall Acc :=
    ⟨Acc, ⟨empty⟩, fun _ => .error (.methodError "abs"), .error (.methodError "zero")⟩
  mappingAbs2 : MappingEmptyCall Acc :=
    ⟨Acc, ⟨empty⟩, fun _ => .error (.methodError "abs2"), .error (.methodError "zero")⟩
  isMax : Bool := false

class EmptyDispatch (Op : Type u) (T : Type) (Result : outParam Type) where
  empty : Op → Jl Result

instance {T Result : Type} : EmptyDispatch (EmptyReducer Result) T Result where
  empty := fun op => op.empty

instance {T Result Input : Type} : EmptyDispatch (Reducer Result Input) T Result where
  empty := fun op => op.empty

structure BottomRF (Acc Input : Type) where
  rf : Reducer Acc Input

structure MappingRF (F : Type u) (RF : Type v) where
  f : F
  rf : RF

class StepCallable (RF : Type v) (Acc : Type) (Output : Type) where
  step : RF → Acc → Output → Acc

instance {Acc Output : Type} : StepCallable (Acc → Output → Acc) Acc Output where
  step := fun rf acc y => rf acc y

instance {Acc Output : Type} : StepCallable (Reducer Acc Output) (FoldInit Acc) Output where
  step := fun op acc y => op.step acc y
structure FilteringRF (Input Acc : Type) where
  predicate : Input → Bool
  rf : Acc → Input → Acc

structure FlatteningRF (Input Acc : Type) where
  rf : Reducer Acc Input

structure XFAResult (Input Acc : Type) where
  Base : Type
  op : Reducer Acc Base
  itr : JIterator Base

structure XFAUnwrapped (Output : Type) where
  Base : Type
  itr : JIterator Base
  wrap : {Acc : Type} → Reducer Acc Output → Reducer Acc Base

inductive EltypeStatus where
  | hasEltype
  | unknown
  deriving Repr, DecidableEq

structure LinearArray (α : Type) (Index : Type := Nat) where
  first : Index
  last : Index
  get : Index → α
  length : Nat

structure LinearIndexRange (Index : Type := Nat) where
  first : Index
  last : Index
  length : Nat

def LinearArray.indices {A Index : Type} (array : LinearArray A Index) : LinearIndexRange Index :=
  ⟨array.first, array.last, array.length⟩

/-- Integer arithmetic supplied by the selected Julia index type. The laws justify recursion. -/
class ReductionIndex (Index : Type) [LE Index] [LT Index] where
  offset : Index → Nat → Index
  distance : Index → Index → Nat
  offset_zero : ∀ a : Index, offset a 0 = a
  offset_add : ∀ (a : Index) (m n : Nat), offset (offset a m) n = offset a (m + n)
  distance_self : ∀ a : Index, distance a a = 0
  distance_pos : ∀ a b : Index, a ≤ b → a ≠ b → 0 < distance a b
  distance_offset_le : ∀ (a b : Index) (k : Nat), a ≤ b → k ≤ distance a b →
    offset a k ≤ b ∧ distance (offset a k) b = distance a b - k
  distance_to_offset : ∀ (a : Index) (k : Nat), distance a (offset a k) = k
  offset_le_iff : ∀ (a b : Index) (k : Nat), a ≤ b → (offset a k ≤ b ↔ k ≤ distance a b)
  lt_iff_le_and_ne : ∀ (a b : Index), a < b ↔ (a ≤ b ∧ a ≠ b)
  le_offset : ∀ (a : Index) (k : Nat), a ≤ offset a k
  le_trans : ∀ {a b c : Index}, a ≤ b → b ≤ c → a ≤ c
  middle_le : ∀ a b, a ≤ b → a ≠ b → a ≤ offset a (distance a b / 2)
  next_middle_le : ∀ a b, a ≤ b → a ≠ b → offset (offset a (distance a b / 2)) 1 ≤ b
  left_decreases : ∀ a b, a ≤ b → a ≠ b →
    distance a (offset a (distance a b / 2)) < distance a b
  right_decreases : ∀ a b, a ≤ b → a ≠ b →
    distance (offset (offset a (distance a b / 2)) 1) b < distance a b
  next_decreases : ∀ a b, a < b → distance (offset a 1) b < distance a b

instance : ReductionIndex Nat where
  offset := fun a n => a + n
  distance := fun a b => b - a
  offset_zero := by intros; omega
  offset_add := by intros; omega
  distance_self := by intros; omega
  distance_pos := by intros; omega
  distance_offset_le := by intros; omega
  distance_to_offset := by intros; omega
  offset_le_iff := by intros; omega
  lt_iff_le_and_ne := by intros; omega
  le_offset := by intros; omega
  le_trans := by intros; omega
  middle_le := by intros; omega
  next_middle_le := by
    intro a b h ne
    have hd : 0 < b - a := by omega
    have hh := Nat.div_lt_self hd (by decide : 1 < 2)
    omega
  left_decreases := by
    intro a b h ne
    have hd : 0 < b - a := by omega
    have hh := Nat.div_lt_self hd (by decide : 1 < 2)
    omega
  right_decreases := by intros; omega
  next_decreases := by intros; omega

instance : ReductionIndex Int where
  offset := fun a n => a + n
  distance := fun a b => (b - a).toNat
  offset_zero := by intros; omega
  offset_add := by intros; omega
  distance_self := by intros; omega
  distance_pos := by intros; omega
  distance_offset_le := by intros; omega
  distance_to_offset := by intros; omega
  offset_le_iff := by intros; omega
  lt_iff_le_and_ne := by intros; omega
  le_offset := by intros; omega
  le_trans := by intros; omega
  middle_le := by intros; omega
  next_middle_le := by
    intro a b h ne
    have hd : 0 < (b - a).toNat := by omega
    have hh := Nat.div_lt_self hd (by decide : 1 < 2)
    omega
  left_decreases := by
    intro a b h ne
    have hd : 0 < (b - a).toNat := by omega
    have hh := Nat.div_lt_self hd (by decide : 1 < 2)
    omega
  right_decreases := by intros; omega
  next_decreases := by intros; omega
inductive IndexStyle where
  | linear
  | cartesian
  deriving Repr, DecidableEq

structure ExtremaMap (F : Type) where
  f : F

structure FlipArgs (A B C : Type) where
  f : A → B → C


inductive Abs2Function where
  | abs2

inductive PlusFunction where
  | plus

inductive BoolTypeError where
  | typeError
  deriving Repr, DecidableEq

def assertBool {Other : Type} : Bool ⊕ Other → Except BoolTypeError Bool
  | .inl b => .ok b
  | .inr _ => .error .typeError

/-- The result type specializes when the predicate's Julia return type is already Bool. -/
class BoolAssertion (R : Type) where
  Result : Type
  assert : R → Result

instance : BoolAssertion Bool where
  Result := Bool
  assert := id

instance {Other : Type} : BoolAssertion (Bool ⊕ Other) where
  Result := Except BoolTypeError Bool
  assert := assertBool


inductive RealTypeError where
  | typeError
  deriving Repr, DecidableEq

def assertReal {RealValue Other : Type} : RealValue ⊕ Other → Except RealTypeError RealValue
  | .inl r => .ok r
  | .inr _ => .error .typeError

/-- The result type specializes when the operator's Julia return type is already Real. -/
class RealAssertion (R : Type) where
  Result : Type
  assert : R → Result

instance (priority := 0) {R : Type} : RealAssertion R where
  Result := R
  assert := id

instance {RealValue Other : Type} : RealAssertion (RealValue ⊕ Other) where
  Result := Except RealTypeError RealValue
  assert := assertReal
/-! ## Reduction operators -/

/--
Julia source: base/reduce.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_sum(x, y) = x + y
```
-/
def add_sum {A B C : Type} (plus : A → B → C) (x : A) (y : B) : C := plus x y

/--
Julia source: base/reduce.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_sum(x::Union{Bool,BitIntegerSmall}, y::Union{Bool,BitIntegerSmall}) = Int(x) + Int(y)
```
-/
def add_sum_small {A B C : Type} (toIntA : A → C) (toIntB : B → C) (plus : C → C → C)
    (x : A) (y : B) : C := plus (toIntA x) (toIntB y)

/--
Julia source: base/reduce.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_sum(x::BitUnsignedSmall, y::BitUnsignedSmall) = UInt(x) + UInt(y)
```
-/
def add_sum_unsigned_small {A B C : Type} (toUIntA : A → C) (toUIntB : B → C) (plus : C → C → C)
    (x : A) (y : B) : C := plus (toUIntA x) (toUIntB y)

/--
Julia source: base/reduce.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_sum(x::Real, y::Real)::Real = x + y
```
-/
def add_sum_real {A B C : Type} [RealAssertion C] (plus : A → B → C) (x : A) (y : B) :
    RealAssertion.Result C :=
  RealAssertion.assert (plus x y)

/--
Julia source: base/reduce.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_prod(x, y) = x * y
```
-/
def mul_prod {A B C : Type} (mul : A → B → C) (x : A) (y : B) : C := mul x y

/--
Julia source: base/reduce.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_prod(x::BitSignedSmall, y::BitSignedSmall) = Int(x) * Int(y)
```
-/
def mul_prod_signed_small {A B C : Type} (toIntA : A → C) (toIntB : B → C) (mul : C → C → C)
    (x : A) (y : B) : C := mul (toIntA x) (toIntB y)

/--
Julia source: base/reduce.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_prod(x::BitUnsignedSmall, y::BitUnsignedSmall) = UInt(x) * UInt(y)
```
-/
def mul_prod_unsigned_small {A B C : Type} (toUIntA : A → C) (toUIntB : B → C) (mul : C → C → C)
    (x : A) (y : B) : C := mul (toUIntA x) (toUIntB y)

/--
Julia source: base/reduce.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_prod(x::Real, y::Real)::Real = x * y
```
-/
def mul_prod_real {A B C : Type} [RealAssertion C] (mul : A → B → C) (x : A) (y : B) :
    RealAssertion.Result C :=
  RealAssertion.assert (mul x y)

/--
Julia source: base/reduce.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_all(x, y) = (x && y)::Bool
```
-/
def and_all {A B : Type} (x : Bool ⊕ A) (y : Bool ⊕ B) : Except BoolTypeError Bool := do
  let condition ← assertBool x
  assertBool (if condition then y else .inl false)

/--
Julia source: base/reduce.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
or_any(x, y) = (x || y)::Bool
```
-/
def or_any {A B : Type} (x : Bool ⊕ A) (y : Bool ⊕ B) : Except BoolTypeError Bool := do
  let condition ← assertBool x
  assertBool (if condition then .inl true else y)

/--
Julia source: base/reduce.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_all(x::Bool, y::Bool) = (x & y)::Bool
```
-/
def and_all_bool (bitAnd : Bool → Bool → Bool) (x y : Bool) : Bool := bitAnd x y

/--
Julia source: base/reduce.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
or_any(x::Bool, y::Bool) = (x | y)::Bool
```
-/
def or_any_bool (bitOr : Bool → Bool → Bool) (x y : Bool) : Bool := bitOr x y

/-! ## Left folds and iterator transforms -/

/--
Julia source: base/reduce.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    MappingRF(f::F, rf::T) where {F,T} = new{F,T}(f, rf)
```
-/
def mappingRF_constructor {F : Type u} {RF : Type v} (f : F) (rf : RF) : MappingRF F RF :=
  ⟨f, rf⟩

/--
Julia source: base/reduce.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    MappingRF(::Type{f}, rf::T) where {f,T} = new{Type{f},T}(f, rf)
```
-/
def mappingRF_type_constructor {F : Type u} {RF : Type v} (typeCall : F) (rf : RF) : MappingRF F RF :=
  ⟨typeCall, rf⟩

/--
Julia source: base/reduce.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (op::MappingRF)(acc, x) = op.rf(acc, op.f(x))
```
-/
def mappingRF_apply {Input Output Acc F : Type} {RF : Type v} [MapCallable F Input Output]
    [StepCallable RF Acc Output] (op : MappingRF F RF) (acc : Acc) (x : Input) : Acc :=
  StepCallable.step op.rf acc (MapCallable.apply (Input := Input) op.f x)

/--
Julia source: base/reduce.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (op::FilteringRF)(acc, x) = op.f(x) ? op.rf(acc, x) : acc
```
-/
def filteringRF_apply {Input Acc : Type} (op : FilteringRF Input Acc) (acc : Acc) (x : Input) : Acc :=
  if op.predicate x then op.rf acc x else acc

/--
Julia source: base/reduce.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_empty_reduce_error() = throw(ArgumentError("reducing over an empty collection is not allowed; consider supplying `init` to the reducer"))
```
-/
def _empty_reduce_error {α : Type} : Jl α :=
  .error (.argumentError "reducing over an empty collection is not allowed; consider supplying `init` to the reducer")

/--
Julia source: base/reduce.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(f, T) = _empty_reduce_error()
```
-/
def reduce_empty_fallback {Acc Input : Type} (_op : Reducer Acc Input) (_T : Type) : Jl Acc := _empty_reduce_error

/--
Julia source: base/reduce.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(f, op, T) = _empty_reduce_error()
```
-/
def mapreduce_empty {Acc Input Output : Type} (_f : Input → Output)
    (_op : Reducer Acc Output) (_T : Type) : Jl Acc := _empty_reduce_error

/--
Julia source: base/reduce.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(f, ::Type{Union{}}, splat...) = _empty_reduce_error()
```
-/
def reduce_empty_union {Acc Input Splat : Type} (_op : Input → Input → Acc) (_splat : Splat) : Jl Acc :=
  _empty_reduce_error

/--
Julia source: base/reduce.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(f, op, ::Type{Union{}}, splat...) = _empty_reduce_error()
```
-/
def mapreduce_empty_union {Acc Input Output Splat : Type} (_f : Input → Output)
    (_op : Output → Output → Acc) (_splat : Splat) : Jl Acc := _empty_reduce_error

/--
Julia source: base/reduce.jl:342-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(+), ::Type{T}) where {T} = zero(T)
```
-/
def reduce_empty_add {α : Type} (zero : Type → α) (T : Type) : Jl α := .ok (zero T)

/--
Julia source: base/reduce.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(+), ::Type{Bool}) = zero(Int)
```
-/
def reduce_empty_add_bool {α : Type} (zeroInt : Type → α) (intType : Type) : Jl α := .ok (zeroInt intType)

/--
Julia source: base/reduce.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(*), ::Type{T}) where {T} = one(T)
```
-/
def reduce_empty_mul {α : Type} (one : Type → α) (T : Type) : Jl α := .ok (one T)

/--
Julia source: base/reduce.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(*), ::Type{<:AbstractChar}) = ""
```
-/
def reduce_empty_mul_char : Jl String := .ok ""

/--
Julia source: base/reduce.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(&), ::Type{Bool}) = true
```
-/
def reduce_empty_and_bool : Jl Bool := .ok true

/--
Julia source: base/reduce.jl:347-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(|), ::Type{Bool}) = false
```
-/
def reduce_empty_or_bool : Jl Bool := .ok false

/--
Julia source: base/reduce.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(and_all), ::Type{T}) where {T} = true
```
-/
def reduce_empty_and_all : Jl Bool := .ok true

/--
Julia source: base/reduce.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(or_any), ::Type{T}) where {T} = false
```
-/
def reduce_empty_or_any : Jl Bool := .ok false

/--
Julia source: base/reduce.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(add_sum), ::Type{T}) where {T} = reduce_empty(+, T)
```
-/
def reduce_empty_add_sum {Acc _Input : Type} (reduceEmptyPlus : Type → Jl Acc) (T : Type) : Jl Acc :=
  reduceEmptyPlus T

/--
Julia source: base/reduce.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(add_sum), ::Type{T}) where {T<:BitSignedSmall}  = zero(Int)
```
-/
def reduce_empty_add_sum_signed_small {Acc : Type} (zeroInt : Type → Acc) (intType : Type) : Jl Acc :=
  .ok (zeroInt intType)

/--
Julia source: base/reduce.jl:353-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(add_sum), ::Type{T}) where {T<:BitUnsignedSmall} = zero(UInt)
```
-/
def reduce_empty_add_sum_unsigned_small {Acc : Type} (zeroUInt : Type → Acc) (uintType : Type) : Jl Acc :=
  .ok (zeroUInt uintType)

/--
Julia source: base/reduce.jl:354-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(mul_prod), ::Type{T}) where {T} = reduce_empty(*, T)
```
-/
def reduce_empty_mul_prod {Acc _Input : Type} (reduceEmptyTimes : Type → Jl Acc) (T : Type) : Jl Acc :=
  reduceEmptyTimes T

/--
Julia source: base/reduce.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(mul_prod), ::Type{T}) where {T<:BitSignedSmall}  = one(Int)
```
-/
def reduce_empty_mul_prod_signed_small {Acc : Type} (oneInt : Type → Acc) (intType : Type) : Jl Acc :=
  .ok (oneInt intType)

/--
Julia source: base/reduce.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(::typeof(mul_prod), ::Type{T}) where {T<:BitUnsignedSmall} = one(UInt)
```
-/
def reduce_empty_mul_prod_unsigned_small {Acc : Type} (oneUInt : Type → Acc) (uintType : Type) : Jl Acc :=
  .ok (oneUInt uintType)

/-- Trusted dispatch selects the empty method stored with the typed callable. -/
def reduce_empty {Op : Type u} {Result : Type} (op : Op) (T : Type) [EmptyDispatch Op T Result] : Jl Result :=
  EmptyDispatch.empty T op

/--
Julia source: base/reduce.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(op::BottomRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
```
-/
def reduce_empty_bottom {Acc Input : Type} (op : BottomRF Acc Input) (T : Type) : Jl Acc :=
  reduce_empty op.rf T

/--
Julia source: base/reduce.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(op::FilteringRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
```
-/
def reduce_empty_filtering {Acc Input : Type} (op : FilteringRF Input Acc)
    (reduceEmpty : (Acc → Input → Acc) → Type → Jl Acc) (T : Type) : Jl Acc :=
  reduceEmpty op.rf T

/--
Julia source: base/reduce.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(op::FlatteningRF, ::Type{T}) where {T} = reduce_empty(op.rf, eltype(T))
```
-/
def reduce_empty_flattening {Acc Input : Type} (op : FlatteningRF Input Acc)
    (eltype : Type → Type) (reduceEmpty : Reducer Acc Input → Type → Jl Acc) (T : Type) : Jl Acc :=
  reduceEmpty op.rf (eltype T)

/--
Julia source: base/reduce.jl:362-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(op::FlipArgs, ::Type{T}) where {T} = reduce_empty(op.f, T)
```
-/
def reduce_empty_flip {Acc Input : Type} (op : FlipArgs Acc Input Acc)
    (reduceEmpty : (Acc → Input → Acc) → Type → Jl Acc) (T : Type) : Jl Acc :=
  reduceEmpty op.f T

/--
Julia source: base/reduce.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(::typeof(identity), op, T) = reduce_empty(op, T)
```
-/
def mapreduce_empty_identity {Op : Type u} {Result : Type}
    (op : Op) (T : Type) [EmptyDispatch Op T Result] : Jl Result :=
  reduce_empty op T

/--
Julia source: base/reduce.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(::typeof(abs), op, T)      = abs(reduce_empty(op, T))
```
-/
def mapreduce_empty_abs {Acc Output : Type} {Op : Type u}
    (abs : Acc → Jl Output) (op : Op) (T : Type) [EmptyDispatch Op T Acc] : Jl Output :=
  (reduce_empty op T).bind abs

/--
Julia source: base/reduce.jl:373-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(::typeof(abs2), op, T)     = abs2(reduce_empty(op, T))
```
-/
def mapreduce_empty_abs2 {Acc Output : Type} {Op : Type u}
    (abs2 : Acc → Jl Output) (op : Op) (T : Type) [EmptyDispatch Op T Acc] : Jl Output :=
  (reduce_empty op T).bind abs2

/--
Julia source: base/reduce.jl:375-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(f::typeof(abs),  ::typeof(max), T) = abs(zero(T))
```
-/
def mapreduce_empty_abs_max {Input Output : Type}
    (zero : Type → Jl Input) (abs : Input → Jl Output) (T : Type) : Jl Output :=
  (zero T).bind abs

/--
Julia source: base/reduce.jl:376-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty(f::typeof(abs2), ::typeof(max), T) = abs2(zero(T))
```
-/
def mapreduce_empty_abs2_max {Input Output : Type}
    (zero : Type → Jl Input) (abs2 : Input → Jl Output) (T : Type) : Jl Output :=
  (zero T).bind abs2

class MapreduceEmptyDispatch (F : Type u) (Op : Type v) (Input : Type) (Result : outParam Type) where
  dispatch : F → Op → Type → Jl Result

instance {Input Output F Acc : Type} [MapCallable F Input Output] :
    MapreduceEmptyDispatch F (Reducer Acc Output) Input Acc where
  dispatch := fun f op T =>
    match MapCallable.mappingKind (Input := Input) f with
    | .identity => mapreduce_empty_identity op T
    | .abs =>
      if op.isMax then mapreduce_empty_abs_max (fun _ => op.mappingAbs.zero) op.mappingAbs.apply T
      else mapreduce_empty_abs op.mappingAbs.apply op.mappingAbs.emptyOp T
    | .abs2 =>
      if op.isMax then mapreduce_empty_abs2_max (fun _ => op.mappingAbs2.zero) op.mappingAbs2.apply T
      else mapreduce_empty_abs2 op.mappingAbs2.apply op.mappingAbs2.emptyOp T
    | .other => mapreduce_empty (MapCallable.apply (Input := Input) f) op T

/--
Julia source: base/reduce.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty(op::MappingRF, ::Type{T}) where {T} = mapreduce_empty(op.f, op.rf, T)
```
-/
def reduce_empty_mapping {F : Type u} {Op : Type v} {Result : Type}
    (op : MappingRF F Op) (T : Type) [MapreduceEmptyDispatch F Op T Result] : Jl Result :=
  MapreduceEmptyDispatch.dispatch (Input := T) op.f op.rf T

instance {F : Type u} {Op : Type v} {T Result : Type} [MapreduceEmptyDispatch F Op T Result] :
    EmptyDispatch (MappingRF F Op) T Result where
  empty := fun op => reduce_empty_mapping op T

/--
Julia source: base/reduce.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline reduce_empty_iter(op, itr, ::HasEltype) = reduce_empty(op, eltype(itr))
```
-/
def reduce_empty_iter_has_eltype {Op : Type u} {Acc Input : Type} [EmptyDispatch Op Input Acc]
    (op : Op) (_itr : JIterator Input) : Jl Acc :=
  reduce_empty op Input

/--
Julia source: base/reduce.jl:393-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_empty_iter(op, itr, ::EltypeUnknown) = throw(ArgumentError("""
    reducing over an empty collection of unknown element type is not allowed.
    You may be able to prevent this error by supplying an `init` value to the reducer."""))
```
-/
def reduce_empty_iter_unknown {Op : Type u} {Acc : Type} (_op : Op) : Jl Acc :=
  .error (.argumentError "reducing over an empty collection of unknown element type is not allowed. You may be able to prevent this error by supplying an `init` value to the reducer.")

def reduce_empty_iter_eltype {Op : Type u} {Acc Input : Type} [EmptyDispatch Op Input Acc]
    (op : Op) (itr : JIterator Input) (itrEltype : EltypeStatus) : Jl Acc :=
  match itrEltype with
  | .hasEltype => reduce_empty_iter_has_eltype op itr
  | .unknown => reduce_empty_iter_unknown op

/--
Julia source: base/reduce.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline reduce_empty_iter(op, itr) = reduce_empty_iter(op, itr, IteratorEltype(itr))
```
-/
def reduce_empty_iter {Op : Type u} {Acc Input : Type} [EmptyDispatch Op Input Acc]
    (elementType : JIterator Input → EltypeStatus)
    (op : Op) (itr : JIterator Input) : Jl Acc :=
  reduce_empty_iter_eltype op itr (elementType itr)
/--
Julia source: base/reduce.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline reduce_empty_iter(op::FlatteningRF, itr) = reduce_empty_iter(op.rf, Iterators.flatten(itr))
```
-/
def reduce_empty_iter_flattening {Acc Input : Type}
    (elementType : JIterator Input → EltypeStatus) (op : FlatteningRF Input Acc)
    (itr : JIterator (List Input)) : Jl Acc :=
  reduce_empty_iter elementType op.rf (.flatten itr)

/--
Julia source: base/reduce.jl:391-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline reduce_empty_iter(op, itr::Tuple{Vararg{T}}, ::HasEltype) where {T} =
    reduce_empty(op, @isdefined(T) ? T : Union{})
```
-/
def reduce_empty_iter_tuple {Acc Input : Type} (op : Reducer Acc Input) (T : Option Type) : Jl Acc :=
  let elementType := match T with
    | some T => T
    | none => PEmpty
  reduce_empty op elementType

/--
Julia source: base/reduce.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_xfadjoint_unwrap(itr) = itr, identity
```
-/
def _xfadjoint_unwrap_values {Input : Type} (itr : JIterator Input) : XFAUnwrapped Input :=
  ⟨Input, itr, fun op => op⟩

def mappingRFReducer {Input Output F Acc : Type} [MapCallable F Input Output]
    (mapped : MappingRF F (Reducer Acc Output)) : Reducer Acc Input :=
  { first := fun x => mapped.rf.first (MapCallable.apply (Input := Input) mapped.f x),
    step := mappingRF_apply mapped,
    empty := reduce_empty_mapping mapped Input,
    mappingAbs := mapped.rf.mappingAbs,
    mappingAbs2 := mapped.rf.mappingAbs2,
    isMax := mapped.rf.isMax }

/--
Julia source: base/reduce.jl:152-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _xfadjoint_unwrap(itr::Generator)
    itr′, wrap = _xfadjoint_unwrap(itr.iter)
    itr.f === identity && return itr′, wrap
    return itr′, wrap ∘ Fix1(MappingRF, itr.f)
end
```
-/
def _xfadjoint_unwrap_generator {Input Output F : Type} [MapCallable F Input Output]
    (unwrapped : XFAUnwrapped Input) (f : F) : XFAUnwrapped Output :=
  if h : MapCallable.isIdentity (Input := Input) f = true then
    match MapCallable.identityTypes (Input := Input) f h with
    | rfl => ⟨unwrapped.Base, unwrapped.itr, unwrapped.wrap⟩
  else ⟨unwrapped.Base, unwrapped.itr, fun op =>
    unwrapped.wrap (mappingRFReducer (mappingRF_constructor f op))⟩
/--
Julia source: base/reduce.jl:157-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _xfadjoint_unwrap(itr::Filter)
    itr′, wrap = _xfadjoint_unwrap(itr.itr)
    return itr′, wrap ∘ Fix1(FilteringRF, itr.flt)
end
```
-/
def _xfadjoint_unwrap_filter {Input : Type} (unwrapped : XFAUnwrapped Input)
    (predicate : Input → Bool) : XFAUnwrapped Input :=
  ⟨unwrapped.Base, unwrapped.itr, fun op => unwrapped.wrap
    { first := fun x => if predicate x then op.first x else .initial,
      step := filteringRF_apply ⟨predicate, op.step⟩,
      empty := op.empty, mappingAbs := op.mappingAbs, mappingAbs2 := op.mappingAbs2,
      isMax := op.isMax }⟩

/--
Julia source: base/reduce.jl:161-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _xfadjoint_unwrap(itr::Flatten)
    itr′, wrap = _xfadjoint_unwrap(itr.it)
    return itr′, wrap ∘ FlatteningRF
end
```
-/
def _xfadjoint_unwrap_flatten {Input : Type} (unwrapped : XFAUnwrapped (List Input)) : XFAUnwrapped Input :=
  ⟨unwrapped.Base, unwrapped.itr, fun op => unwrapped.wrap
    { first := fun xs => xs.foldl op.step .initial,
      step := fun state xs => xs.foldl op.step state,
      empty := op.empty, mappingAbs := op.mappingAbs, mappingAbs2 := op.mappingAbs2,
      isMax := op.isMax }⟩

def _xfadjoint_unwrap_dispatch {Input : Type} : JIterator Input → XFAUnwrapped Input
  | .values xs => _xfadjoint_unwrap_values (.values xs)
  | @JIterator.generator F _ _ _ f itr =>
      _xfadjoint_unwrap_generator (F := F) (_xfadjoint_unwrap_dispatch itr) f
  | .filter predicate itr => _xfadjoint_unwrap_filter (_xfadjoint_unwrap_dispatch itr) predicate
  | .flatten itr => _xfadjoint_unwrap_flatten (_xfadjoint_unwrap_dispatch itr)

/--
Julia source: base/reduce.jl:146-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _xfadjoint(op, itr)
    itr′, wrap = _xfadjoint_unwrap(itr)
    wrap(op), itr′
end
```
-/
def _xfadjoint {Input Acc : Type} (op : Reducer Acc Input) (itr : JIterator Input) : XFAResult Input Acc :=
  let unwrapped := _xfadjoint_unwrap_dispatch itr
  ⟨unwrapped.Base, unwrapped.wrap op, unwrapped.itr⟩

/--
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _foldl_impl(op::OP, init, itr) where {OP}
    # Unroll the loop once to check if the iterator is empty.
    # If init is known, the call to op may be evaluated at compile time
    y = iterate(itr)
    y === nothing && return init
    v = op(init, y[1])
    # Using a for loop is more performant than a while loop (see #56492)
    # This unrolls the loop a second time before entering the body
    for x in Iterators.rest(itr, y[2])
        v = op(v, x)
    end
    return v
end
```
-/
def _foldl_impl {Acc Input : Type} (op : Reducer Acc Input) (init : FoldInit Acc) (itr : JIterator Input) :
    FoldInit Acc :=
  let y := iteratorValues itr
  match y with
  | [] => init
  | x :: xs => xs.foldl op.step (op.step init x)

/--
Julia source: base/reduce.jl:45-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function foldl_impl(op::OP, nt, itr) where {OP}
    v = _foldl_impl(op, nt, itr)
    v isa _InitialValue && return reduce_empty_iter(op, itr)
    return v
end
```
-/
def foldl_impl {Acc Input : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (op : Reducer Acc Input) (nt : FoldInit Acc) (itr : JIterator Input) : Jl Acc :=
  match _foldl_impl op nt itr with
  | .initial => reduce_empty_iter iteratorEltype op itr
  | .value x => .ok x

/--
Julia source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
    length(itr) <= 32 && return afoldl(op, init, itr...)
    @invoke _foldl_impl(op, init, itr::Any)
end
```
-/
def _foldl_impl_tuple {Tuple Acc Input : Type} (length : Tuple → Nat)
    (iterateTuple : Tuple → JIterator Input)
    (afoldl : Reducer Acc Input → FoldInit Acc → Tuple → FoldInit Acc)
    (fallback : Reducer Acc Input → FoldInit Acc → JIterator Input → FoldInit Acc)
    (op : Reducer Acc Input) (init : FoldInit Acc) (itr : Tuple) : FoldInit Acc :=
  if length itr ≤ 32 then afoldl op init itr else fallback op init (iterateTuple itr)

/--
Julia source: base/reduce.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (op::BottomRF)(::_InitialValue, x) = reduce_first(op.rf, x)
```
-/
def bottomRF_initial {Acc Input : Type} (op : BottomRF Acc Input) (x : Input) : FoldInit Acc := op.rf.first x

/--
Julia source: base/reduce.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (op::BottomRF)(acc, x) = op.rf(acc, x)
```
-/
def bottomRF_apply {Acc Input : Type} (op : BottomRF Acc Input) (acc : Acc) (x : Input) : FoldInit Acc :=
  op.rf.step (.value acc) x

def bottomRFReducer {Acc Input : Type} (op : Reducer Acc Input) : Reducer Acc Input :=
  { first := op.first,
    step := fun state x => match state with
      | .initial => bottomRF_initial ⟨op⟩ x
      | .value acc => bottomRF_apply ⟨op⟩ acc x,
    empty := op.empty, mappingAbs := op.mappingAbs, mappingAbs2 := op.mappingAbs2,
    isMax := op.isMax }

/--
Julia source: base/reduce.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mapfoldl_impl(f::F, op::OP, nt, itr) where {F,OP}
    op′, itr′ = _xfadjoint(BottomRF(op), Generator(f, itr))
    return foldl_impl(op′, nt, itr′)
end
```
-/
def mapfoldl_impl {Input Output F Acc : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : F) (op : Reducer Acc Output) (nt : FoldInit Acc) (itr : JIterator Input) : Jl Acc :=
  let result := _xfadjoint (bottomRFReducer op) (.generator f itr)
  foldl_impl iteratorEltype result.op nt result.itr

/--
Julia source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function (op::FlatteningRF)(acc, x)
    op′, itr′ = _xfadjoint(op.rf, x)
    return _foldl_impl(op′, acc, itr′)
end
```
-/
def flatteningRF_apply {Input Acc : Type} (op : FlatteningRF Input Acc)
    (acc : FoldInit Acc) (x : JIterator Input) : FoldInit Acc :=
  let result := _xfadjoint op.rf x
  _foldl_impl result.op acc result.itr

/--
Julia source: base/reduce.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapfoldl(f, op, itr; init=_InitialValue()) = mapfoldl_impl(f, op, init, itr)
```
-/
def mapfoldl {Input Output F Acc : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : F) (op : Reducer Acc Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapfoldl_impl iteratorEltype f op init itr

/--
Julia source: base/reduce.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foldl(op, itr; kw...) = mapfoldl(identity, op, itr; kw...)
```
-/
def foldl {Input : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Input) (op : Reducer Input Input) (itr : JIterator Input) (init : FoldInit Input) : Jl Input :=
  mapfoldl iteratorEltype (IdentityMapper.mk identity) op itr init

/--
Julia source: base/reduce.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse_iter(itr) = Iterators.reverse(itr)
```
-/
def _reverse_iter {Input : Type} (iteratorsReverse : JIterator Input → JIterator Input) (itr : JIterator Input) : JIterator Input :=
  iteratorsReverse itr

/--
Julia source: base/reduce.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse_iter(itr::Union{Tuple,NamedTuple}) = length(itr) <= 32 ? reverse(itr) : Iterators.reverse(itr) #33235
```
-/
def _reverse_iter_tuple {Tuple Input : Type} (length : Tuple → Nat)
    (iterateTuple : Tuple → JIterator Input) (reverse : Tuple → Tuple)
    (iteratorsReverse : JIterator Input → JIterator Input) (itr : Tuple) : JIterator Input :=
  if length itr ≤ 32 then iterateTuple (reverse itr) else iteratorsReverse (iterateTuple itr)

def flipReducer {α : Type} (op : Reducer α α) : Reducer α α :=
  { first := op.first,
    step := fun state x => match state with
      | .initial => op.first x
      | .value acc => op.step (.value x) acc,
    empty := op.empty, mappingAbs := op.mappingAbs, mappingAbs2 := op.mappingAbs2,
    isMax := op.isMax }

/--
Julia source: base/reduce.jl:200-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mapfoldr_impl(f, op, nt, itr)
    op′, itr′ = _xfadjoint(BottomRF(FlipArgs(op)), Generator(f, _reverse_iter(itr)))
    return foldl_impl(op′, nt, itr′)
end
```
-/
def mapfoldr_impl {Input Output F : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (iteratorsReverse : JIterator Input → JIterator Input) (f : F)
    (op : Reducer Output Output) (nt : FoldInit Output) (itr : JIterator Input) : Jl Output :=
  let reversed := _reverse_iter iteratorsReverse itr
  let result := _xfadjoint (bottomRFReducer (flipReducer op)) (.generator f reversed)
  foldl_impl iteratorEltype result.op nt result.itr

/--
Julia source: base/reduce.jl:213-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (f::FlipArgs)(x, y) = f.f(y, x)
```
-/
def flipArgs_apply {A B C : Type} (f : FlipArgs A B C) (x : B) (y : A) : C := f.f y x

/--
Julia source: base/reduce.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapfoldr(f::F, op::F2, itr; init=_InitialValue()) where {F,F2} = mapfoldr_impl(f, op, init, itr)
```
-/
def mapfoldr {Input Output F : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (iteratorsReverse : JIterator Input → JIterator Input) (f : F)
    (op : Reducer Output Output) (itr : JIterator Input) (init : FoldInit Output) : Jl Output :=
  mapfoldr_impl iteratorEltype iteratorsReverse f op init itr

/--
Julia source: base/reduce.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foldr(op::F, itr; kw...) where {F} = mapfoldr(identity, op, itr; kw...)
```
-/
def foldr {Input : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (iteratorsReverse : JIterator Input → JIterator Input) (identity : Input → Input) (op : Reducer Input Input)
    (itr : JIterator Input) (init : FoldInit Input) : Jl Input :=
  mapfoldr iteratorEltype iteratorsReverse (IdentityMapper.mk identity) op itr init


def combineFoldInit {Acc : Type} (op : Reducer Acc Acc) (left right : FoldInit Acc) : FoldInit Acc :=
  match left, right with
  | .initial, r => r
  | l, .initial => l
  | .value a, .value b => op.step (.value a) b

/--
Julia source: base/reduce.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(op, x) = x
```
-/
def reduce_first {Input OP : Type} (_op : OP) (x : Input) : Input := x

def reduce_first_dispatch {Acc Input : Type} (op : Reducer Acc Input) (x : Input) : FoldInit Acc :=
  op.first x

/--
Julia source: base/reduce.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(+), x::Bool) = Int(x)
```
-/
def reduce_first_plus_bool {Output : Type} (toInt : Bool → Output) (x : Bool) : Output := toInt x

/--
Julia source: base/reduce.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(*), x::AbstractChar) = string(x)
```
-/
def reduce_first_times_char {CharValue : Type} (singleton : CharValue → String) (x : CharValue) : String := singleton x

/--
Julia source: base/reduce.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(add_sum), x) = reduce_first(+, x)
```
-/
def reduce_first_add_sum {Input Output : Type} (plusFirst : Input → Output) (x : Input) : Output := plusFirst x

/--
Julia source: base/reduce.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(add_sum), x::BitSignedSmall)   = Int(x)
```
-/
def reduce_first_add_sum_signed_small {Input Output : Type} (toInt : Input → Output) (x : Input) : Output := toInt x

/--
Julia source: base/reduce.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(add_sum), x::BitUnsignedSmall) = UInt(x)
```
-/
def reduce_first_add_sum_unsigned_small {Input Output : Type} (toUInt : Input → Output) (x : Input) : Output := toUInt x

/--
Julia source: base/reduce.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(mul_prod), x) = reduce_first(*, x)
```
-/
def reduce_first_mul_prod {Input Output : Type} (timesFirst : Input → Output) (x : Input) : Output := timesFirst x

/--
Julia source: base/reduce.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(mul_prod), x::BitSignedSmall)   = Int(x)
```
-/
def reduce_first_mul_prod_signed_small {Input Output : Type} (toInt : Input → Output) (x : Input) : Output := toInt x

/--
Julia source: base/reduce.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(mul_prod), x::BitUnsignedSmall) = UInt(x)
```
-/
def reduce_first_mul_prod_unsigned_small {Input Output : Type} (toUInt : Input → Output) (x : Input) : Output := toUInt x

/--
Julia source: base/reduce.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(vcat), x) = vcat(x)
```
-/
def reduce_first_vcat {Input Output : Type} (vcat : Input → Output) (x : Input) : Output := vcat x

/--
Julia source: base/reduce.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(::typeof(hcat), x) = hcat(x)
```
-/
def reduce_first_hcat {Input Output : Type} (hcat : Input → Output) (x : Input) : Output := hcat x

/--
Julia source: base/reduce.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce_first(op::FlipArgs, x) = reduce_first(op.f, x)
```
-/
def reduce_first_flip {Input Output : Type} (first : Input → Output) (x : Input) : Output := first x

/--
Julia source: base/reduce.jl:435-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_first(f, op, x) = reduce_first(op, f(x))
```
-/
def mapreduce_first {Input Output Acc : Type} (f : Input → Output) (op : Reducer Acc Output) (x : Input) : FoldInit Acc :=
  reduce_first_dispatch op (f x)

/--
Julia source: base/reduce.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairwise_blocksize(f, op) = 1024
```
-/
def pairwise_blocksize {F : Sort u} {OP : Sort v} (_f : F) (_op : OP) : Nat := 1024

/--
Julia source: base/reduce.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairwise_blocksize(::typeof(abs2), ::typeof(+)) = 4096
```
-/
def pairwise_blocksize_abs2_plus (_f : Abs2Function) (_op : PlusFunction) : Nat := 4096

/--
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
                                  ifirst::Integer, ilast::Integer, blksize::Int)
    if ifirst == ilast
        @inbounds a1 = A[ifirst]
        return mapreduce_first(f, op, a1)
    elseif ilast - ifirst < blksize
        # sequential portion
        @inbounds a1 = A[ifirst]
        @inbounds a2 = A[ifirst+1]
        v = op(f(a1), f(a2))
        @simd for i = ifirst + 2 : ilast
            @inbounds ai = A[i]
            v = op(v, f(ai))
        end
        return v
    else
        # pairwise portion
        imid = ifirst + (ilast - ifirst) >> 1
        v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
        v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
        return op(v1, v2)
    end
end
```
-/
def mapreduce_impl {Input Output Index : Type} [LE Index] [LT Index] [DecidableLE Index]
    [DecidableEq Index] [ReductionIndex Index] (f : Input → Output) (op : Reducer Output Output)
    (A : LinearArray Input Index) (ifirst ilast : Index) (blockSize : Nat) (h : ifirst ≤ ilast) :
    FoldInit Output :=
  if hEq : ifirst = ilast then
    mapreduce_first f op (A.get ifirst)
  else if hSeq : ReductionIndex.distance ifirst ilast < blockSize then
    let a1 := A.get ifirst
    let a2 := A.get (ReductionIndex.offset ifirst 1)
    let v := op.step (.value (f a1)) (f a2)
    let start := ReductionIndex.offset ifirst 2
    let count := if start ≤ ilast then ReductionIndex.distance start ilast + 1 else 0
    (List.range count).foldl
      (fun acc k => op.step acc (f (A.get (ReductionIndex.offset start k)))) v
  else
    let half := ReductionIndex.distance ifirst ilast / 2
    let imid := ReductionIndex.offset ifirst half
    have hLeft : ifirst ≤ imid := ReductionIndex.middle_le ifirst ilast h hEq
    have hRight : ReductionIndex.offset imid 1 ≤ ilast :=
      ReductionIndex.next_middle_le ifirst ilast h hEq
    let left := mapreduce_impl f op A ifirst imid blockSize hLeft
    let right := mapreduce_impl f op A (ReductionIndex.offset imid 1) ilast blockSize hRight
    combineFoldInit op left right
termination_by ReductionIndex.distance ifirst ilast
decreasing_by
  · exact ReductionIndex.left_decreases ifirst ilast h hEq
  · exact ReductionIndex.right_decreases ifirst ilast h hEq

/--
Julia source: base/reduce.jl:276-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted, ifirst::Integer, ilast::Integer) =
    mapreduce_impl(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
```
-/
def mapreduce_impl_default {Input Output Index : Type} {F : Sort u} {OP : Sort v}
    [LE Index] [LT Index] [DecidableLE Index]
    [DecidableEq Index] [ReductionIndex Index] (f : Input → Output) (op : Reducer Output Output)
    (fTag : F) (opTag : OP) (A : LinearArray Input Index)
    (ifirst ilast : Index) (h : ifirst ≤ ilast) : FoldInit Output :=
  mapreduce_impl f op A ifirst ilast (pairwise_blocksize fTag opTag) h

/--
Julia source: base/reduce.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce(f, op, itr; kw...) = mapfoldl(f, op, itr; kw...)
```
-/
def mapreduce {Input Output F Acc : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : F) (op : Reducer Acc Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapfoldl iteratorEltype f op itr init

/--
Julia source: base/reduce.jl:462-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce(f, op, a::Number) = mapreduce_first(f, op, a)
```
-/
def mapreduce_number {Input Output Acc : Type} (f : Input → Output) (op : Reducer Acc Output) (x : Input) : FoldInit Acc :=
  mapreduce_first f op x

/--
Julia source: base/reduce.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce(op, itr; kw...) = mapreduce(identity, op, itr; kw...)
```
-/
def reduce {Input Acc : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Input) (op : Reducer Acc Input) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype (IdentityMapper.mk identity) op itr init

/--
Julia source: base/reduce.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reduce(op, a::Number) = a  # Do we want this?
```
-/
def reduce_number {Input Acc : Type} (_op : Reducer Acc Input) (x : Input) : Input := x

/--
Julia source: base/reduce.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sum(f, a; kw...) = mapreduce(f, add_sum, a; kw...)
```
-/
def sum_f {Input Output F Acc : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : F) (addSum : Reducer Acc Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype f addSum itr init

/--
Julia source: base/reduce.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sum(a; kw...) = sum(identity, a; kw...)
```
-/
def sum {Input Acc : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Input) (addSum : Reducer Acc Input) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  sum_f iteratorEltype (IdentityMapper.mk identity) addSum itr init


/--
Julia source: base/reduce.jl:602-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod(f, a; kw...) = mapreduce(f, mul_prod, a; kw...)
```
-/
def prod_f {Input Output Acc : Type}
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : Input → Output) (mulProd : Reducer Acc Output) (itr : JIterator Input) (init : FoldInit Acc)
    (_mappingIdentity : MappingIdentity := .other) : Jl Acc :=
  mapreduce iteratorEltype f mulProd itr init

/--
Julia source: base/reduce.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod(a; kw...) = mapreduce(identity, mul_prod, a; kw...)
```
-/
def prod {Input Acc : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Input) (mulProd : Reducer Acc Input) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype (IdentityMapper.mk identity) mulProd itr init

/--
Julia source: base/reduce.jl:659-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maximum(f, a; kw...) = mapreduce(f, max, a; kw...)
```
-/
def maximum_f {Input Output F Acc : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : F) (maxOp : Reducer Acc Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype f maxOp itr init

/--
Julia source: base/reduce.jl:686-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum(f, a; kw...) = mapreduce(f, min, a; kw...)
```
-/
def minimum_f {Input Output F Acc : Type} [MapCallable F Input Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : F) (minOp : Reducer Acc Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype f minOp itr init

/--
Julia source: base/reduce.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maximum(a; kw...) = mapreduce(identity, max, a; kw...)
```
-/
def maximum {Input Acc : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Input) (maxOp : Reducer Acc Input) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype (IdentityMapper.mk identity) maxOp itr init

/--
Julia source: base/reduce.jl:750-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum(a; kw...) = mapreduce(identity, min, a; kw...)
```
-/
def minimum {Input Acc : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Input) (minOp : Reducer Acc Input) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  mapreduce iteratorEltype (IdentityMapper.mk identity) minOp itr init

/--
Julia source: base/reduce.jl:816-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ExtremaMap(::Type{T}) where {T} = ExtremaMap{Type{T}}(T)
```
-/
def extremaMap_type {F : Type} (f : F) : ExtremaMap F := ⟨f⟩

/--
Julia source: base/reduce.jl:817-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (f::ExtremaMap)(x) = (y = f.f(x); (y, y))
```
-/
def extremaMap_apply {Input Output : Type} (f : ExtremaMap (Input → Output)) (x : Input) : Output × Output :=
  let y := f.f x
  (y, y)

/--
Julia source: base/reduce.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _extrema_rf((min1, max1), (min2, max2)) = (min(min1, min2), max(max1, max2))
```
-/
def extrema_rf {A : Type} (minOp maxOp : A → A → A) (left right : A × A) : A × A :=
  (minOp left.1 right.1, maxOp left.2 right.2)

/--
Julia source: base/reduce.jl:809-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
extrema(f, itr; kw...) = mapreduce(ExtremaMap(f), _extrema_rf, itr; kw...)
```
-/
def extrema_f {Input Output : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : Input → Output) (extremaRF : Reducer (Output × Output) (Output × Output))
    (itr : JIterator Input) (init : FoldInit (Output × Output)) : Jl (Output × Output) :=
  mapreduce iteratorEltype (extremaMap_apply (extremaMap_type f)) extremaRF itr init

/--
Julia source: base/reduce.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
extrema(itr; kw...) = extrema(identity, itr; kw...)
```
-/
def extrema {Input Output : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (identity : Input → Output) (op : Reducer (Output × Output) (Output × Output))
    (itr : JIterator Input) (init : FoldInit (Output × Output)) : Jl (Output × Output) :=
  extrema_f iteratorEltype identity op itr init

/--
Julia source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_rf_findmax((fm, im), (fx, ix)) = isless(fm, fx) ? (fx, ix) : (fm, im)
```
-/
def rf_findmax {A B : Type} (isless : A → A → Bool) (left right : A × B) : A × B :=
  if isless left.1 right.1 then right else left

/--
Julia source: base/reduce.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_rf_findmin((fm, im), (fx, ix)) = isgreater(fm, fx) ? (fx, ix) : (fm, im)
```
-/
def rf_findmin {A B : Type} (isgreater : A → A → Bool) (left right : A × B) : A × B :=
  if isgreater left.1 right.1 then right else left

def findmaxReducer {A K : Type} (isless : A → A → Bool) : Reducer (A × K) (A × K) :=
  { first := fun x => .value x,
    step := fun state x => match state with
      | .initial => .value x
      | .value best => .value (rf_findmax isless best x),
    empty := _empty_reduce_error }

def findminReducer {A K : Type} (isgreater : A → A → Bool) : Reducer (A × K) (A × K) :=
  { first := fun x => .value x,
    step := fun state x => match state with
      | .initial => .value x
      | .value best => .value (rf_findmin isgreater best x),
    empty := _empty_reduce_error }

/--
Julia source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findmax(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmax, pairs(domain) )
```
-/
def _findmax {A B K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (f : A → B) (isless : B → B → Bool)
    (domain : JIterator A) : Jl (B × K) :=
  mapfoldl iteratorEltype (fun p : K × A => (f p.2, p.1)) (findmaxReducer isless) (pairs domain) .initial

/--
Julia source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmax(f, domain) = _findmax(f, domain, :)
```
-/
def findmax_f {A B K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (f : A → B) (isless : B → B → Bool)
    (domain : JIterator A) : Jl (B × K) :=
  _findmax iteratorEltype pairs f isless domain

/--
Julia source: base/reduce.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findmax(a, ::Colon) = findmax(identity, a)
```
-/
def _findmax_identity {A K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (identity : A → A) (isless : A → A → Bool)
    (itr : JIterator A) : Jl (A × K) :=
  findmax_f iteratorEltype pairs identity isless itr

/--
Julia source: base/reduce.jl:883-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmax(itr) = _findmax(itr, :)
```
-/
def findmax {A K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (identity : A → A) (isless : A → A → Bool)
    (itr : JIterator A) : Jl (A × K) :=
  _findmax_identity iteratorEltype pairs identity isless itr

/--
Julia source: base/reduce.jl:921-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findmin(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmin, pairs(domain) )
```
-/
def _findmin {A B K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (f : A → B) (isgreater : B → B → Bool)
    (domain : JIterator A) : Jl (B × K) :=
  mapfoldl iteratorEltype (fun p : K × A => (f p.2, p.1)) (findminReducer isgreater) (pairs domain) .initial

/--
Julia source: base/reduce.jl:920-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmin(f, domain) = _findmin(f, domain, :)
```
-/
def findmin_f {A B K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (f : A → B) (isgreater : B → B → Bool)
    (domain : JIterator A) : Jl (B × K) :=
  _findmin iteratorEltype pairs f isgreater domain

/--
Julia source: base/reduce.jl:950-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findmin(a, ::Colon) = findmin(identity, a)
```
-/
def _findmin_identity {A K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (identity : A → A) (isgreater : A → A → Bool)
    (itr : JIterator A) : Jl (A × K) :=
  findmin_f iteratorEltype pairs identity isgreater itr

/--
Julia source: base/reduce.jl:949-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmin(itr) = _findmin(itr, :)
```
-/
def findmin {A K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (identity : A → A) (isgreater : A → A → Bool)
    (itr : JIterator A) : Jl (A × K) :=
  _findmin_identity iteratorEltype pairs identity isgreater itr

/--
Julia source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argmax(f, domain) = mapfoldl(x -> (f(x), x), _rf_findmax, domain)[2]
```
-/
def argmax_f {A B : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (isless : B → B → Bool) (domain : JIterator A) : Jl A :=
  (mapfoldl iteratorEltype (fun x => (f x, x)) (findmaxReducer isless) domain .initial).map Prod.snd

/--
Julia source: base/reduce.jl:1005-1005 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argmax(itr) = findmax(itr)[2]
```
-/
def argmax {A K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (identity : A → A) (isless : A → A → Bool)
    (itr : JIterator A) : Jl K :=
  (findmax iteratorEltype pairs identity isless itr).map Prod.snd

/--
Julia source: base/reduce.jl:1034-1034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argmin(f, domain) = mapfoldl(x -> (f(x), x), _rf_findmin, domain)[2]
```
-/
def argmin_f {A B : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (isgreater : B → B → Bool) (domain : JIterator A) : Jl A :=
  (mapfoldl iteratorEltype (fun x => (f x, x)) (findminReducer isgreater) domain .initial).map Prod.snd

/--
Julia source: base/reduce.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argmin(itr) = findmin(itr)[2]
```
-/
def argmin {A K : Type} (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (identity : A → A) (isgreater : A → A → Bool)
    (itr : JIterator A) : Jl K :=
  (findmin iteratorEltype pairs identity isgreater itr).map Prod.snd

/--
Julia source: base/reduce.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bool(f) = x->f(x)::Bool
```
-/
def _bool {Input Output : Type} [BoolAssertion Output] (f : Input → Output) :
    Input → BoolAssertion.Result Output := fun x => BoolAssertion.assert (f x)

/--
Julia source: base/reduce.jl:1094-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
count(itr; init=0) = count(identity, itr; init)
```
-/
def count {Input Acc : Type} (countF : (Input → Input) → JIterator Input → FoldInit Acc → Jl Acc)
    (identity : Input → Input) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  countF identity itr init

/--
Julia source: base/reduce.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
count(f, itr; init=0) = _simple_count(f, itr, init)
```
-/
def count_f {Input Output Acc : Type}
    (simpleCount : (Input → Output) → JIterator Input → FoldInit Acc → Jl Acc)
    (predicate : Input → Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  simpleCount predicate itr init

/--
Julia source: base/reduce.jl:1098-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_simple_count(pred, itr, init) = sum(_bool(pred), itr; init)
```
-/
def _simple_count {Input Output Acc : Type} [BoolAssertion Output]
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus)
    (addSum : Reducer Acc (BoolAssertion.Result Output))
    (predicate : Input → Output) (itr : JIterator Input) (init : FoldInit Acc) : Jl Acc :=
  sum_f iteratorEltype (_bool predicate) addSum itr init

structure Ptr (T : Type) where
  bytes : List Bool
  offset : Nat := 0

structure ArrayBool where
  elements : List Bool

def gcPreserve {X α : Type} (_x : X) (body : α) : α := body

def pointerBoolArray (x : ArrayBool) : Ptr Bool := ⟨x.elements, 0⟩

def ptrUIntOfPtr {T : Type} (p : Ptr T) : Ptr (JInt .u64) := ⟨p.bytes, p.offset⟩

def sizeofUInt : Nat := 8

def lengthBoolArray (x : ArrayBool) : Nat := x.elements.length

def packBoolBytes : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 256 * packBoolBytes bs

def unsafeLoadUInt (ptr : Ptr (JInt .u64)) (i : Nat) : JInt .u64 :=
  JuliaLean.base.int.lit .u64 (packBoolBytes ((ptr.bytes.drop (ptr.offset + 8 * (i - 1))).take 8))

def getindexBoolArray (x : ArrayBool) (i : Nat) : Bool :=
  x.elements.getD (i - 1) false

def simpleCountChunkLoop {Acc : Type}
    (addWord : Acc → JInt .i64 → Acc) (remT : Acc → Jl Acc)
    (ptr : Ptr (JInt .u64)) (mask : JInt .u64) (chunks i : Nat) (n : Acc) : Jl Acc :=
  if h : i ≤ chunks then do
    let word := unsafeLoadUInt ptr i
    let ones := JuliaLean.base.int.count_ones (JuliaLean.base.int.and_int word mask)
    let n ← remT (addWord n ones)
    simpleCountChunkLoop addWord remT ptr mask chunks (i + 1) n
  else
    .ok n
termination_by chunks + 1 - i
decreasing_by omega

def simpleCountTailLoop {Acc : Type}
    (addBool : Acc → Bool → Acc) (remT : Acc → Jl Acc)
    (x : ArrayBool) (len i : Nat) (n : Acc) : Jl Acc :=
  if h : i ≤ len then do
    let xi := getindexBoolArray x i
    let n ← remT (addBool n xi)
    simpleCountTailLoop addBool remT x len (i + 1) n
  else
    .ok n
termination_by len + 1 - i
decreasing_by omega

/--
Julia source: base/reduce.jl:1100-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _simple_count(::typeof(identity), x::Array{Bool}, init=0)
    v0 = Base.add_sum(init, false)
    T = typeof(v0)
    n::T = v0
    chunks = length(x) ÷ sizeof(UInt)
    mask = 0x0101010101010101 % UInt
    GC.@preserve x begin
        ptr = Ptr{UInt}(pointer(x))
        for i in 1:chunks
            n = (n + count_ones(unsafe_load(ptr, i) & mask)) % T
        end
    end
    for i in sizeof(UInt)*chunks+1:length(x)
        n = (n + x[i]) % T
    end
    return n
end
```
-/
def _simple_count_bool_array {Init Acc : Type}
    (addSumInit : Init → Bool → Acc) (addWord : Acc → JInt .i64 → Acc)
    (addBool : Acc → Bool → Acc) (remT : Acc → Jl Acc)
    (x : ArrayBool) (init : Init) : Jl Acc := do
  let v0 := addSumInit init false
  let n := v0
  let chunks := lengthBoolArray x / sizeofUInt
  let mask := JuliaLean.base.int.remT .u64 (JInt.lit .u64 0x0101010101010101)
  let n ← gcPreserve x (do
    let ptr := ptrUIntOfPtr (pointerBoolArray x)
    simpleCountChunkLoop addWord remT ptr mask chunks 1 n)
  let start := sizeofUInt * chunks + 1
  simpleCountTailLoop addBool remT x (lengthBoolArray x) start n

/--
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sum(a::AbstractArray{Bool}; kw...) =
    isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
```
-/
def sum_bool_array {Acc : Type}
    (iteratorEltype : {I : Type} → JIterator I → EltypeStatus) (hasKeywords : Bool)
    (addSum : Reducer Acc Bool) (zero : Acc)
    (itr : JIterator Bool) (init : FoldInit Acc) : Jl Acc :=
  if hasKeywords then reduce iteratorEltype id addSum itr init
  else count (count_f (_simple_count iteratorEltype addSum)) id itr (.value zero)
/--
Julia source: base/reduce.jl:1120-1122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
        isempty(r) ? init : op(init, $fred(r))
    end
```
-/
def foldl_range_special {Range Acc Input : Type} (isempty : Range → Bool)
    (fred : Range → Input) (op : Reducer Acc Input) (init : FoldInit Acc) (r : Range) : FoldInit Acc :=
  if isempty r then init else op.step init (fred r)

/-- Typed representation of a binary callable, with the first-element and empty dispatch results. -/
def valueReducer {Acc Input : Type} [EmptyMappingOps Acc] (binary : Acc → Input → Acc)
    (first : Input → Acc) (empty : Jl Acc) (isMax : Bool := false) : Reducer Acc Input :=
  { first := fun x => .value (first x),
    step := fun state x => match state with
      | .initial => .value (first x)
      | .value a => .value (binary a x),
    empty := empty,
    mappingAbs := ⟨Acc, ⟨empty⟩, EmptyMappingOps.abs, EmptyMappingOps.zero⟩,
    mappingAbs2 := ⟨Acc, ⟨empty⟩, EmptyMappingOps.abs2, EmptyMappingOps.zero⟩,
    isMax := isMax }

/-- The type of an integer accumulator may change after its first operation. -/
abbrev IntegerAccumulator := Sigma JInt

def integerPromotion (t s : IntTy) : IntTy :=
  if hEq : t = s then t else
    match ht : JuliaLean.base.int.promote_rule t s, hs : JuliaLean.base.int.promote_rule s t with
    | some u, _ => u
    | _, some u => u
    | none, none => False.elim (by
        cases t <;> cases s <;> simp_all [JuliaLean.base.int.promote_rule])

def integerBinary (binary : {t : IntTy} → JInt t → JInt t → JInt t)
    (x y : IntegerAccumulator) : IntegerAccumulator :=
  let t := integerPromotion x.1 y.1
  ⟨t, binary (JuliaLean.base.int.widenTo t x.2) (JuliaLean.base.int.widenTo t y.2)⟩

def integerAddSum (x y : IntegerAccumulator) : IntegerAccumulator :=
  if x.1.bits < 64 ∧ y.1.bits < 64 then
    if x.1.signed = false ∧ y.1.signed = false then
      ⟨.u64, add_sum_unsigned_small (JuliaLean.base.int.widenTo .u64)
        (JuliaLean.base.int.widenTo .u64) JuliaLean.base.int.add x.2 y.2⟩
    else
      ⟨.i64, add_sum_small (JuliaLean.base.int.widenTo .i64)
        (JuliaLean.base.int.widenTo .i64) JuliaLean.base.int.add x.2 y.2⟩
  else add_sum (integerBinary JuliaLean.base.int.add) x y

def integerMulProd (x y : IntegerAccumulator) : IntegerAccumulator :=
  if x.1.bits < 64 ∧ y.1.bits < 64 ∧ x.1.signed = true ∧ y.1.signed = true then
    ⟨.i64, mul_prod_signed_small (JuliaLean.base.int.widenTo .i64)
      (JuliaLean.base.int.widenTo .i64) JuliaLean.base.int.mul x.2 y.2⟩
  else if x.1.bits < 64 ∧ y.1.bits < 64 ∧ x.1.signed = false ∧ y.1.signed = false then
    ⟨.u64, mul_prod_unsigned_small (JuliaLean.base.int.widenTo .u64)
      (JuliaLean.base.int.widenTo .u64) JuliaLean.base.int.mul x.2 y.2⟩
  else mul_prod (integerBinary JuliaLean.base.int.mul) x y

def integerFirstSum (x : IntegerAccumulator) : IntegerAccumulator :=
  if x.1.bits < 64 then
    if x.1.signed then
      ⟨.i64, reduce_first_add_sum_signed_small (JuliaLean.base.int.widenTo .i64) x.2⟩
    else ⟨.u64, reduce_first_add_sum_unsigned_small (JuliaLean.base.int.widenTo .u64) x.2⟩
  else ⟨x.1, reduce_first_add_sum id x.2⟩

def integerFirstProd (x : IntegerAccumulator) : IntegerAccumulator :=
  if x.1.bits < 64 then
    if x.1.signed then
      ⟨.i64, reduce_first_mul_prod_signed_small (JuliaLean.base.int.widenTo .i64) x.2⟩
    else ⟨.u64, reduce_first_mul_prod_unsigned_small (JuliaLean.base.int.widenTo .u64) x.2⟩
  else ⟨x.1, reduce_first_mul_prod id x.2⟩

def integerCountAdd (n : IntegerAccumulator) (b : Bool) : IntegerAccumulator :=
  integerAddSum n ⟨.i8, JuliaLean.base.int.ofBool .i8 b⟩

def integerCountWord (n : IntegerAccumulator) (c : JInt .i64) : IntegerAccumulator :=
  integerBinary JuliaLean.base.int.add n ⟨.i64, c⟩

def integerCountModulo (n : IntegerAccumulator) : Jl IntegerAccumulator :=
  .ok ⟨n.1, JuliaLean.base.int.remT n.1 n.2⟩

/--
Julia source: base/reduce.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce(f, op, itr, itrs...; kw...) = reduce(op, Generator(f, itr, itrs...); kw...)
```
-/
def mapreduce_multi {F I IS Output Acc : Type}
    (iteratorEltype : {T : Type} → JIterator T → EltypeStatus)
    (generator : F → I → IS → JIterator Output) (f : F) (op : Reducer Acc Output)
    (itr : I) (itrs : IS) (init : FoldInit Acc) : Jl Acc :=
  reduce iteratorEltype id op (generator f itr itrs) init

/--
Julia source: base/reduce.jl:379-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_empty_iter(f::F, op::F2, itr, ItrEltype) where {F,F2} =
    reduce_empty_iter(MappingRF(f, op), itr, ItrEltype)
```
-/
def mapreduce_empty_iter {F : Type u} {Op : Type v} {Input Acc : Type}
    [MapreduceEmptyDispatch F Op Input Acc]
    (f : F) (op : Op) (itr : JIterator Input) (itrEltype : EltypeStatus) : Jl Acc :=
  reduce_empty_iter_eltype (mappingRF_constructor f op) itr itrEltype

def linearReduceWhile {Input Output Index F : Type} [MapCallable F Input Output]
    [LE Index] [LT Index] [DecidableLT Index]
    [ReductionIndex Index] (f : F)
    (op : Reducer Output Output) (getindex : Index → Input) (last i : Index)
    (s : FoldInit Output) : FoldInit Output :=
  if h : i < last then
    let i := ReductionIndex.offset i 1
    let ai := getindex i
    let s := op.step s (MapCallable.apply (Input := Input) f ai)
    linearReduceWhile f op getindex last i s
  else s
termination_by ReductionIndex.distance i last
decreasing_by exact ReductionIndex.next_decreases _ _ h

/--
Julia source: base/reduce.jl:439-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mapreduce(f, op, ::IndexLinear, A::AbstractArrayOrBroadcasted)
    inds = LinearIndices(A)
    n = length(inds)
    if n == 0
        return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
    elseif n == 1
        @inbounds a1 = A[first(inds)]
        return mapreduce_first(f, op, a1)
    elseif n < 16 # process short array here, avoid mapreduce_impl() compilation
        @inbounds i = first(inds)
        @inbounds a1 = A[i]
        @inbounds a2 = A[i+=1]
        s = op(f(a1), f(a2))
        while i < last(inds)
            @inbounds Ai = A[i+=1]
            s = op(s, f(Ai))
        end
        return s
    else
        return mapreduce_impl(f, op, A, first(inds), last(inds))
    end
end
```
-/
def _mapreduce_linear {Array Input Output Index F : Type} [MapCallable F Input Output]
    [LE Index] [LT Index] [DecidableLE Index] [DecidableLT Index] [DecidableEq Index] [ReductionIndex Index]
    (linearIndices : Array → LinearIndexRange Index) (getindex : Array → Index → Input)
    (iterateArray : Array → JIterator Input)
    (iteratorEltype : JIterator Input → EltypeStatus) (f : F)
    (op : Reducer Output Output) (A : Array)
    (indexInterval : ∀ a, (linearIndices a).length > 0 →
      (linearIndices a).first ≤ (linearIndices a).last) : Jl Output :=
  let inds := linearIndices A
  let n := inds.length
  if _hEmpty : n = 0 then
    mapreduce_empty_iter f op (iterateArray A) (iteratorEltype (iterateArray A))
  else
    let fn := MapCallable.apply (Input := Input) f
    let result :=
      if n = 1 then
        let a1 := getindex A inds.first
        mapreduce_first fn op a1
      else if n < 16 then
        let i := inds.first
        let a1 := getindex A i
        let i := ReductionIndex.offset i 1
        let a2 := getindex A i
        let s := op.step (.value (fn a1)) (fn a2)
        linearReduceWhile f op (getindex A) inds.last i s
      else
        mapreduce_impl_default fn op f op
          ⟨inds.first, inds.last, getindex A, inds.length⟩ inds.first inds.last
          (indexInterval A (by change 0 < n; omega))
    match result with
    | .initial => op.empty
    | .value x => .ok x

/--
Julia source: base/reduce.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce(f, op, ::IndexCartesian, A::AbstractArrayOrBroadcasted) = mapfoldl(f, op, A)
```
-/
def _mapreduce_cartesian {Array Input Output F : Type} [MapCallable F Input Output]
    (iterateArray : Array → JIterator Input)
    (iteratorEltype : {T : Type} → JIterator T → EltypeStatus)
    (f : F) (op : Reducer Output Output) (A : Array) : Jl Output :=
  mapfoldl iteratorEltype f op (iterateArray A) .initial

/--
Julia source: base/reduce.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce(f, op, A::AbstractArrayOrBroadcasted) = _mapreduce(f, op, IndexStyle(A), A)
```
-/
def _mapreduce {Array Input Output Index F : Type} [MapCallable F Input Output]
    [LE Index] [LT Index] [DecidableLE Index] [DecidableLT Index] [DecidableEq Index] [ReductionIndex Index]
    (indexStyle : Array → IndexStyle) (linearIndices : Array → LinearIndexRange Index)
    (getindex : Array → Index → Input) (iterateArray : Array → JIterator Input)
    (iteratorEltype : {T : Type} → JIterator T → EltypeStatus)
    (f : F) (op : Reducer Output Output) (A : Array)
    (indexInterval : ∀ a, (linearIndices a).length > 0 →
      (linearIndices a).first ≤ (linearIndices a).last) : Jl Output :=
  match indexStyle A with
  | .linear => _mapreduce_linear linearIndices getindex iterateArray iteratorEltype f op A indexInterval
  | .cartesian => _mapreduce_cartesian iterateArray iteratorEltype f op A
end JuliaLean.base.reduce
