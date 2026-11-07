import JuliaLean.base.bool
import JuliaLean.base.range
import JuliaLean.base.essentials
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.number
import JuliaLean.Runtime.Collections
import JuliaLean.base.math

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

/-- `none` records a loop that does not terminate. -/
def whileLoop {S A : Type} {E : Type u} (step : S → Except E (Sum A S)) (state : S) :
    Option (Except E A) :=
  match step state with
  | .error e => some (.error e)
  | .ok (.inl value) => some (.ok value)
  | .ok (.inr next) => whileLoop step next
partial_fixpoint

theorem whileLoop_some_unfold {S A : Type} {E : Type u}
    (step : S → Except E (Sum A S)) (state : S) {result : Except E A}
    (h : whileLoop step state = some result) :
    match step state with
    | .error err => result = .error err
    | .ok (.inl value) => result = .ok value
    | .ok (.inr next) => whileLoop step next = some result := by
  rw [whileLoop] at h
  cases hstep : step state with
  | error err =>
      simp only [hstep, Option.some.injEq, Except.error.injEq] at h
      simpa [hstep, h]
  | ok value =>
    cases value with
    | inl value =>
        simp only [hstep, Option.some.injEq, Except.ok.injEq, Sum.inl.injEq] at h
        simpa [hstep, h]
    | inr next =>
        simpa [hstep] using h

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

def iteratorValues {α : Type} : JIterator α → List α
  | .values xs => xs
  | @JIterator.generator F _ _ _ f itr =>
      (iteratorValues itr).map (MapCallable.apply (F := F) f)
  | .filter predicate itr => (iteratorValues itr).filter predicate
  | .flatten itr => (iteratorValues itr).flatten

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

/-! ## Left folds over a user iterator's own `iterate` (`for x in itr` with a throwing,
possibly non-terminating `iterate`, and a throwing reducing step) -/

/-- A reducing operator whose call `op(acc, x)` may throw. `first` is
`reduce_first(op, x)` (the call `BottomRF(op)(::_InitialValue, x)` makes, reduce.jl:83). -/
structure ProtocolReducer (E Acc Input : Type) where
  first : Input → Except E (FoldInit Acc)
  step : FoldInit Acc → Input → Except E (FoldInit Acc)

/-- reduce.jl:83-84 `BottomRF(op)` with a throwing `op`. -/
def protocolBottomRF {E Acc Input : Type} (op : ProtocolReducer E Acc Input) :
    ProtocolReducer E Acc Input where
  first := op.first
  step := fun state x => match state with
    | .initial => op.first x
    | .value acc => op.step (.value acc) x

/-- reduce.jl:98 `(op::MappingRF)(acc, x) = op.rf(acc, op.f(x))` with throwing `f` and `op.rf`:
`f(x)` is evaluated first. -/
def protocolMappingRF_apply {E Input Output Acc : Type}
    (f : Input → Except E Output) (rf : ProtocolReducer E Acc Output)
    (acc : FoldInit Acc) (x : Input) : Except E (FoldInit Acc) := do
  let y ← f x
  rf.step acc y

def protocolMappingRFReducer {E Input Output Acc : Type}
    (mapped : MappingRF (Input → Except E Output) (ProtocolReducer E Acc Output)) :
    ProtocolReducer E Acc Input where
  first := fun x => do mapped.rf.first (← mapped.f x)
  step := protocolMappingRF_apply mapped.f mapped.rf

/-- reduce.jl:146-149 `_xfadjoint(op, Generator(f, itr))` for a non-`identity` `f` over an
iterator `itr` that is neither a `Generator`, `Filter` nor `Flatten`: reduce.jl:152-156 unwraps
the generator to `itr, identity ∘ Fix1(MappingRF, f)` (reduce.jl:151 for the inner `itr`), so
the reducer becomes `MappingRF(f, op)` and the iterator is `itr` itself, returned unchanged. -/
def _xfadjoint_generator_protocol {E Input Output Acc : Type}
    (op : ProtocolReducer E Acc Output) (f : Input → Except E Output) :
    ProtocolReducer E Acc Input :=
  protocolMappingRFReducer (mappingRF_constructor f op)

/-- reduce.jl:51-63 `_foldl_impl(op, init, itr)` over `itr`'s own `iterate`; the `for` loop
runs over iterators.jl:696 `Iterators.rest(itr, y[2])`, iterated by iterators.jl:732
(`restWithState`, `iterateRest`: iterators.lean imports this file, so they are parameters). -/
def _foldl_impl_protocol {E Acc α St : Type} {Rest : Type → Type → Type}
    (restWithState : {I S : Type} → I → S → Rest I S)
    (iterateRest : {I B S : Type} → (I → Option S → Except E (Option (B × S))) →
      Rest I S → Option S → Except E (Option (B × S)))
    (op : ProtocolReducer E Acc α)
    (iterate : Option St → Except E (Option (α × St))) (init : FoldInit Acc) :
    Option (Except E (FoldInit Acc)) :=
  match iterate none with
  | .error e => some (.error e)
  | .ok none => some (.ok init)
  | .ok (some (x, st)) =>
    match op.step init x with
    | .error e => some (.error e)
    | .ok v =>
      let r := restWithState () st
      whileLoop (fun (v, s) => do
        match ← iterateRest (fun _ s => iterate s) r s with
        | none => return .inl v
        | some (x, s') => return .inr (← op.step v x, some s')) (v, none)

/-- reduce.jl:45-49 `foldl_impl(op, nt, itr)`; `reduceEmptyIter` is the call
`reduce_empty_iter(op, itr)` (reduce.jl:382), which dispatches on the types of `op` and `itr`. -/
def foldl_impl_protocol {E Acc Input St : Type} {Rest : Type → Type → Type}
    (restWithState : {I S : Type} → I → S → Rest I S)
    (iterateRest : {I B S : Type} → (I → Option S → Except E (Option (B × S))) →
      Rest I S → Option S → Except E (Option (B × S)))
    (reduceEmptyIter : Except E Acc)
    (op : ProtocolReducer E Acc Input) (nt : FoldInit Acc)
    (iterate : Option St → Except E (Option (Input × St))) : Option (Except E Acc) :=
  match _foldl_impl_protocol restWithState iterateRest op iterate nt with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok .initial) => some reduceEmptyIter
  | some (.ok (.value x)) => some (.ok x)

/-- reduce.jl:40-43 `mapfoldl_impl(f, op, nt, itr)`:
`op′, itr′ = _xfadjoint(BottomRF(op), Generator(f, itr)); foldl_impl(op′, nt, itr′)`. -/
def mapfoldl_impl_protocol {E Input Output Acc St : Type} {Rest : Type → Type → Type}
    (restWithState : {I S : Type} → I → S → Rest I S)
    (iterateRest : {I B S : Type} → (I → Option S → Except E (Option (B × S))) →
      Rest I S → Option S → Except E (Option (B × S)))
    (reduceEmptyIter : Except E Acc)
    (f : Input → Except E Output) (op : ProtocolReducer E Acc Output)
    (nt : FoldInit Acc)
    (iterate : Option St → Except E (Option (Input × St))) : Option (Except E Acc) :=
  let op' := _xfadjoint_generator_protocol (protocolBottomRF op) f
  foldl_impl_protocol restWithState iterateRest reduceEmptyIter op' nt iterate

/-- reduce.jl:173 `mapfoldl(f, op, itr; init=_InitialValue()) = mapfoldl_impl(f, op, init, itr)`. -/
def mapfoldl_protocol {E Input Output Acc St : Type} {Rest : Type → Type → Type}
    (restWithState : {I S : Type} → I → S → Rest I S)
    (iterateRest : {I B S : Type} → (I → Option S → Except E (Option (B × S))) →
      Rest I S → Option S → Except E (Option (B × S)))
    (reduceEmptyIter : Except E Acc)
    (f : Input → Except E Output) (op : ProtocolReducer E Acc Output)
    (iterate : Option St → Except E (Option (Input × St)))
    (init : FoldInit Acc) : Option (Except E Acc) :=
  mapfoldl_impl_protocol restWithState iterateRest reduceEmptyIter f op init iterate

/-- reduce.jl:306 `mapreduce(f, op, itr; kw...) = mapfoldl(f, op, itr; kw...)`. -/
def mapreduce_protocol {E Input Output Acc St : Type} {Rest : Type → Type → Type}
    (restWithState : {I S : Type} → I → S → Rest I S)
    (iterateRest : {I B S : Type} → (I → Option S → Except E (Option (B × S))) →
      Rest I S → Option S → Except E (Option (B × S)))
    (reduceEmptyIter : Except E Acc)
    (f : Input → Except E Output) (op : ProtocolReducer E Acc Output)
    (iterate : Option St → Except E (Option (Input × St)))
    (init : FoldInit Acc) : Option (Except E Acc) :=
  mapfoldl_protocol restWithState iterateRest reduceEmptyIter f op iterate init

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



namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-! Additive models for the first source-ordered operators.
The packet runtime uses native Int64/UInt64, as do the installed Core/int models.
SmallInteger includes every signed/unsigned 8-, 16-, and 32-bit value.
The two arms of Real ⊕ Other are semantic runtime-type tags: the latter contains
all non-Real results, including custom objects. The callback monad retains state,
exceptions, and arbitrary selected dispatch; no callback correctness law is assumed.
-/

/-- Every BitIntegerSmall value on the installed 64-bit runtime. The width bound is a
representation invariant, not an input-value precondition.
Julia source: base/int.jl:22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/int.jl:22-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- /Source
structure SmallInteger where
  ty : IntTy
  value : JInt ty
  small : ty.bits < 64

/-- The complete Bool-or-small-bit-integer argument domain of add_sum at line 17.
Julia source: base/reduce.jl:17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Union{Bool,BitIntegerSmall}, y::Union{Bool,BitIntegerSmall}) = Int(x) + Int(y)
-- /Source
abbrev SmallOrBool := Bool ⊕ SmallInteger

/-- All BitSignedSmall values, including heterogeneous widths in a pair of inputs.
Julia source: base/int.jl:22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/int.jl:22-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- /Source
abbrev SmallSigned := { x : SmallInteger // x.ty.signed = true }

/-- All BitUnsignedSmall values, including heterogeneous widths in a pair of inputs.
Julia source: base/int.jl:22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/int.jl:22-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- /Source
abbrev SmallUnsigned := { x : SmallInteger // x.ty.signed = false }

/-- The concrete Int(x) subexpression. All represented values fit Int64; the installed
Bool conversion and widening models implement the selected concrete Base calls.
Julia source: base/reduce.jl:17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Union{Bool,BitIntegerSmall}, y::Union{Bool,BitIntegerSmall}) = Int(x) + Int(y)
-- /Source
def smallOrBoolInt : SmallOrBool → JInt .i64
  | .inl b => JuliaLean.base.int.ofBool .i64 b
  | .inr x => JuliaLean.base.int.widenTo .i64 x.value

/-- Convert each operand to native Int in source order, then perform the installed
wrapping Int addition. Mixed signed/unsigned/Bool pairs are all included. The more
specific unsigned/unsigned method is modelled separately.
Julia source: base/reduce.jl:17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Union{Bool,BitIntegerSmall}, y::Union{Bool,BitIntegerSmall}) = Int(x) + Int(y)
-- /Source
def addSumSmall (x y : SmallOrBool) : JInt .i64 :=
  let a := smallOrBoolInt x
  let b := smallOrBoolInt y
  JuliaLean.base.int.add a b

/-- The concrete UInt conversions and native UInt addition for all small unsigned
width combinations. No dispatch callback replaces these fixed Base operations.
Julia source: base/reduce.jl:18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::BitUnsignedSmall, y::BitUnsignedSmall) = UInt(x) + UInt(y)
-- /Source
def addSumUnsignedSmall (x y : SmallUnsigned) : JInt .u64 :=
  let a := JuliaLean.base.int.widenTo .u64 x.val.value
  let b := JuliaLean.base.int.widenTo .u64 y.val.value
  JuliaLean.base.int.add a b

/-- Open arithmetic and conversion dispatch leaves for the Real-return methods.
The method fixes neither the concrete input subtypes nor the type of the binary
result. Conversion is called only for an Other result. Both leaves can mutate,
throw any error supported by m, or invoke arbitrary user code.
Julia source: base/reduce.jl:19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Real, y::Real)::Real = x + y
-- /Source
structure RealReturnOps (m : Type → Type) (A B Real Other : Type) where
  binary : A → B → m (Real ⊕ Other)
  convertReal : Other → m (Real ⊕ Other)

/-- Lower the return annotation, keeping its native isa fast path. A Real result is
returned unchanged. A non-Real result calls the selected convert(Real, value),
then the installed Real type assertion; a failed assertion throws TypeError.
Pinned lowering evidence: src/julia-syntax.scm:3870-3892 (convert-for-type-decl),
4807 (emit-return) at the same pin. This is a necessary language-runtime boundary,
not an unconditional call to convert.
Julia source: base/reduce.jl:19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Real, y::Real)::Real = x + y
-- /Source
def returnReal {m : Type → Type} [Monad m] [MonadExceptOf RealTypeError m]
    {Real Other : Type} (convertReal : Other → m (Real ⊕ Other)) :
    Real ⊕ Other → m Real
  | .inl value => pure value
  | .inr value => do
      let converted ← convertReal value
      liftExcept (JuliaLean.base.reduce.assertReal converted)

/-- The full Real add_sum method: evaluate the selected addition once, then execute
the conditional conversion and return-type assertion. Effects and errors are
sequenced by m and no identity/correctness assumptions are imposed on dispatch.
Julia source: base/reduce.jl:19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- add_sum(x::Real, y::Real)::Real = x + y
-- /Source
def addSumReal {m : Type → Type} [Monad m] [MonadExceptOf RealTypeError m]
    {A B Real Other : Type} (ops : RealReturnOps m A B Real Other)
    (x : A) (y : B) : m Real := do
  let value ← ops.binary x y
  returnReal ops.convertReal value

/-- The concrete Int conversions and native Int product for every pair of small
signed integer types. The installed multiplication retains machine arithmetic.
Julia source: base/reduce.jl:28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mul_prod(x::BitSignedSmall, y::BitSignedSmall) = Int(x) * Int(y)
-- /Source
def mulProdSignedSmall (x y : SmallSigned) : JInt .i64 :=
  let a := JuliaLean.base.int.widenTo .i64 x.val.value
  let b := JuliaLean.base.int.widenTo .i64 y.val.value
  JuliaLean.base.int.mul a b

/-- The concrete UInt conversions and native UInt product for every pair of small
unsigned integer types. The installed multiplication retains machine arithmetic.
Julia source: base/reduce.jl:29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mul_prod(x::BitUnsignedSmall, y::BitUnsignedSmall) = UInt(x) * UInt(y)
-- /Source
def mulProdUnsignedSmall (x y : SmallUnsigned) : JInt .u64 :=
  let a := JuliaLean.base.int.widenTo .u64 x.val.value
  let b := JuliaLean.base.int.widenTo .u64 y.val.value
  JuliaLean.base.int.mul a b

/-- The full Real mul_prod method, with one selected multiplication followed by the
return annotation's isa fast path or selected conversion and type assertion.
Julia source: base/reduce.jl:30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mul_prod(x::Real, y::Real)::Real = x * y
-- /Source
def mulProdReal {m : Type → Type} [Monad m] [MonadExceptOf RealTypeError m]
    {A B Real Other : Type} (ops : RealReturnOps m A B Real Other)
    (x : A) (y : B) : m Real := do
  let value ← ops.binary x y
  returnReal ops.convertReal value

/-- The Bool specialization uses the installed concrete Bool bitwise and.
Its result is already Bool, so the trailing type assertion succeeds.
Julia source: base/reduce.jl:35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- and_all(x::Bool, y::Bool) = (x & y)::Bool
-- /Source
def andAllBool (x y : Bool) : Bool := JuliaLean.base.bool.andBool x y

/-- The Bool specialization uses the installed concrete Bool bitwise or.
Its result is already Bool, so the trailing type assertion succeeds.
Julia source: base/reduce.jl:36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- or_any(x::Bool, y::Bool) = (x | y)::Bool
-- /Source
def orAnyBool (x y : Bool) : Bool := JuliaLean.base.bool.orBool x y

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Selected dispatch calls on the unfixed operator and iterator types. These
are different callees, not a callback replacing foldl_impl itself. No laws are
assumed. FoldInit preserves the possibility that a user method returns the
_InitialValue singleton, including from reduce_empty_iter itself.
Julia source: base/reduce.jl:45-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:45-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function foldl_impl(op::OP, nt, itr) where {OP}
--     v = _foldl_impl(op, nt, itr)
--     v isa _InitialValue && return reduce_empty_iter(op, itr)
--     return v
-- end
-- /Source
structure FoldDispatchOps (m : Type → Type) (Op I V : Type) where
  fold : Op → FoldInit V → I → m (FoldInit V)
  empty : Op → I → m (FoldInit V)

/-- Call the selected fold once, inspect its actual result tag, and call the
selected empty reduction only for _InitialValue. All arguments, effects, and
errors retain their source order. The empty call's result is returned as-is,
even if it is itself _InitialValue. The generic loop is supplied separately as
a concrete instantiation; custom dispatch is unrestricted.
Julia source: base/reduce.jl:45-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:45-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function foldl_impl(op::OP, nt, itr) where {OP}
--     v = _foldl_impl(op, nt, itr)
--     v isa _InitialValue && return reduce_empty_iter(op, itr)
--     return v
-- end
-- /Source
def foldlImpl {m : Type → Type} [Monad m] {Op I V : Type}
    (ops : FoldDispatchOps m Op I V) (op : Op) (nt : FoldInit V) (itr : I) :
    m (FoldInit V) := do
  let value ← ops.fold op nt itr
  match value with
  | .initial => ops.empty op itr
  | .value _ => pure value

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean


/-- An arbitrary mutable world, arbitrary Julia callback exceptions, and nontermination.
The transformer order retains the final world when a call throws; none is divergence.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
abbrev FoldEval (W E A : Type) := ExceptT E (StateT W Option) A


/-- The open-dispatch error carrier plus the concrete Core.getfield errors reached
by field access, including FieldError for an absent Symbol field. The tags preserve exception class and throw point.
FieldError evidence: base/boot.jl:575-579; src/datatype.c:1859-1883; src/rtutils.c:170-172.
A dispatch error can itself represent any Julia exception, including these classes.
Core evidence: src/builtins.c:1173-1234,1572-1583 at the same pin.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
-- Source: base/boot.jl:575-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct FieldError <: Exception
--     type::DataType
--     field::Symbol
--     FieldError(type::DataType, field::Symbol) = new(type, field)
-- end
-- /Source
inductive FoldError (E : Type) where
  | dispatch (error : E)
  | boundsError
  | undefRefError
  | fieldError
  | typeError
  deriving Repr, DecidableEq


/-- The current storage view of a Julia object. A list slot exists precisely when
the corresponding field exists; none marks an uninitialized reference field.
The list is bounded by native addressable size and is not an unrestricted Julia array.
Modules have distinct integer-field behavior. The view is semantic storage data,
not a callable Julia method or an assumed correctness law.
Core evidence: src/builtins.c:1173-1234,1572-1583 at the same pin.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
inductive FoldObjectView (V : Type) where
  | module
  | fields (slots : List (Option V)) (fits : slots.length ≤ IntTy.i64.max.toNat)


/-- Concrete integer Core.getfield at the default unspecified atomic ordering.
It checks a native field index, then distinguishes uninitialized fields. Modules
redirect to getglobal, whose Symbol assertion rejects an integer index.
Both atomic and non-atomic fields accept the unspecified order; these reads do
not invoke user dispatch or mutate the world. No callback replaces this primitive.
Core evidence: src/builtins.c:1173-1234,1572-1583 at the same pin.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
def foldFieldRead {E V : Type} (view : FoldObjectView V) (index : JInt .i64) :
    Except (FoldError E) V :=
  match view with
  | .module => .error .typeError
  | .fields slots _ =>
      if index.val < 1 then .error .boundsError
      else
        match slots[(index.val - 1).toNat]? with
        | none => .error .boundsError
        | some none => .error .undefRefError
        | some (some value) => .ok value


/-- Opaque iterator handles retain runtime identity. customRest marks a selected
opaque rest method; knownRest stores the actual concrete Rest fields. Explicit
ops selections retain genuinely more specific methods on those unfixed fields. Opaque handles preserve mutable iterator identity, and V can be a tagged
universal carrier for heterogeneous values, accumulators, states and result objects.
Julia source: base/iterators.jl:669-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:669-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Rest{I,S}
--     itr::I
--     st::S
-- end
--
-- /Source
inductive FoldIterator (I V : Type) where
  | ordinary (handle : I)
  | knownRest (iterator : FoldIterator I V) (state : V)
  | customRest (handle : I)


/-- The open calls selected on types not fixed by _foldl_impl. An iterate result
is tagged none exactly for Julia nothing; a successful result object is retained
as V and is not required to be a pair. getindex can mutate or throw independently
at indices 1 and 2. A selected custom rest may return any represented iterator.
fields reads the present storage representation and is pure; the concrete Core
primitive below owns its checks, exceptions and field selection. No laws on any
dispatch leaf are assumed. The five default-none selections denote only genuinely
more specific methods enabled by the unfixed Rest parameters/constructor operands;
none selects the concrete pinned Base body. They do not model overwriting Base's
method table. Property selections receive the original concrete Rest object and
may return arbitrary iterators/states; constructors may return any iterator.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
structure FoldProtocolOps (W E I V O : Type) where
  iterate : I → Option V → FoldEval W (FoldError E) (Option V)
  getindex : V → JInt .i64 → FoldEval W (FoldError E) V
  apply : O → V → V → FoldEval W (FoldError E) V
  customRest : I → V → FoldEval W (FoldError E) (FoldIterator I V)
  fields : W → V → FoldObjectView V
  selectedRest : FoldIterator I V → V →
    Option (FoldEval W (FoldError E) (FoldIterator I V)) := fun _ _ => none
  selectedRestConstructor : FoldIterator I V → V →
    Option (FoldEval W (FoldError E) (FoldIterator I V)) := fun _ _ => none
  selectedRestIterate : FoldIterator I V → Option V →
    Option (FoldEval W (FoldError E) (Option V)) := fun _ _ => none
  selectedRestIteratorProperty : FoldIterator I V →
    Option (FoldEval W (FoldError E) (FoldIterator I V)) := fun _ => none
  selectedRestStateProperty : FoldIterator I V →
    Option (FoldEval W (FoldError E) V) := fun _ => none


/-- Read the actual itr property of a concrete Rest receiver. The default uses fixed initialized storage; a genuinely more specific getproperty method receives the whole original receiver and retains arbitrary results/effects/errors.
Julia source: base/iterators.jl:696-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:696-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rest(itr,state) = Rest(itr,state)
-- rest(itr::Rest,state) = Rest(itr.itr,state)
-- /Source
def foldRestItr {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (inner : FoldIterator I V) (stored : V) : FoldEval W (FoldError E) (FoldIterator I V) :=
  match ops.selectedRestIteratorProperty (.knownRest inner stored) with
  | some call => call
  | none => pure inner

/-- Read the st property only for the generated unary iterate(::Rest) default argument. A selected getter can fail, mutate or diverge and supplies the exact state used for subsequent binary redispatch.
Julia source: base/iterators.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds iterate(i::Rest, st=i.st) = iterate(i.itr, st)
-- /Source
def foldRestState {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (inner : FoldIterator I V) (stored : V) : FoldEval W (FoldError E) V :=
  match ops.selectedRestStateProperty (.knownRest inner stored) with
  | some call => call
  | none => pure stored

/-- The known generated Rest constructor retains both argument identities. A genuinely different selected constructor on unfixed iterator/state types can return an arbitrary iterator and retain errors, mutation or divergence.
Julia source: base/iterators.jl:669-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:669-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Rest{I,S}
--     itr::I
--     st::S
-- end
-- 
-- /Source
def foldRestConstruct {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (inner : FoldIterator I V) (state : V) : FoldEval W (FoldError E) (FoldIterator I V) :=
  match ops.selectedRestConstructor inner state with
  | some call => call
  | none => pure (.knownRest inner state)

/-- Concrete rest preserves the one-layer collapse: for Rest, read only itr then call the selected Rest constructor with the new state. The stored old state is not read. Custom rest methods are distinct dispatch alternatives; no callback replaces either concrete Base body.
Julia source: base/iterators.jl:696-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:696-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rest(itr,state) = Rest(itr,state)
-- rest(itr::Rest,state) = Rest(itr.itr,state)
-- /Source
def foldRest {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) :
    FoldEval W (FoldError E) (FoldIterator I V) := do
  match ops.selectedRest iterator state with
  | some call => call
  | none =>
    match iterator with
    | .ordinary _ => foldRestConstruct ops iterator state
    | .knownRest inner stored =>
      let observed ← foldRestItr ops inner stored
      foldRestConstruct ops observed state
    | .customRest handle => ops.customRest handle state

/-- Full unary/binary Rest iteration dispatch. With no explicit state, the selected st getter is evaluated before binary iterate is redispatched on the SAME Rest receiver. The concrete binary body then reads itr and recursively calls iterate with the exact explicit state. More specific iterate methods are selected before their respective Base body. A getter may return its receiver or another cyclic route, so this is an actual least fixed point, preserving infinite getter/delegation cycles without a fuel bound.
Julia source: base/iterators.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds iterate(i::Rest, st=i.st) = iterate(i.itr, st)
-- /Source
def foldIterate {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : Option V) :
    FoldEval W (FoldError E) (Option V) := do
  match iterator with
  | .ordinary handle => ops.iterate handle state
  | .customRest handle => ops.iterate handle state
  | .knownRest inner stored =>
    match ops.selectedRestIterate iterator state with
    | some call => call
    | none =>
      match state with
      | none =>
        let observed ← foldRestState ops inner stored
        foldIterate ops iterator (some observed)
      | some explicit =>
        let observed ← foldRestItr ops inner stored
        foldIterate ops observed (some explicit)
partial_fixpoint

/-- Read a field from the current mutable object representation using the
concrete Core primitive. A failure preserves the complete world.
The lowering in src/julia-syntax.scm:1888-1909,2070-2110 uses direct
Core.getfield reads, not indexed_iterate, for the for-loop pair extraction.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
def foldGetfield {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (object : V) (index : JInt .i64) : FoldEval W (FoldError E) V := do
  let world ← get
  match foldFieldRead (E := E) (ops.fields world object) index with
  | .ok value => pure value
  | .error error => throw error


/-- The actual lowered for-loop recursion. Each non-nothing iteration result
has its first and second Core fields read, in that order, before reducing.
The next iterate receives the second field, not the accumulator or a synthetic
counter. The fixed point includes an infinite loop and divergence within leaves;
there is no fuel bound or list-materialization approximation.
Lowering evidence: src/julia-syntax.scm:1888-1909,2070-2110 at the same pin.
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
def foldTail {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (iterator : FoldIterator I V) (value : V) (state : Option V) :
    FoldEval W (FoldError E) V := do
  match ← foldIterate ops iterator state with
  | none => pure value
  | some result =>
      let item ← foldGetfield ops result (JuliaLean.base.int.lit .i64 1)
      let nextState ← foldGetfield ops result (JuliaLean.base.int.lit .i64 2)
      let nextValue ← ops.apply op value item
      foldTail ops op iterator nextValue (some nextState)
partial_fixpoint


/-- Full generic _foldl_impl, with arbitrary mutable iterator/results/accumulator
types and arbitrary selected operator behavior. The first getindex(result,1)
precedes the first reduction; getindex(result,2) is evaluated only afterwards.
Rest construction, property access and Rest iteration retain concrete defaults and only genuinely selected specific alternatives.
An empty first iterate returns the original init without reading any result or
calling the operator. The tail is the actual for-loop above.
Documentation: doc/src/manual/interfaces.md:8-54 (iteration protocol);
base/reduce.jl:175-180 (left-associative fold with init used once).
Julia source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
def foldlGeneric {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (init : V) (iterator : FoldIterator I V) : FoldEval W (FoldError E) V := do
  match ← foldIterate ops iterator none with
  | none => pure init
  | some result =>
      let item ← ops.getindex result (JuliaLean.base.int.lit .i64 1)
      let value ← ops.apply op init item
      let state ← ops.getindex result (JuliaLean.base.int.lit .i64 2)
      let rest ← foldRest ops iterator state
      foldTail ops op rest value none


end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Runtime value tags distinguish native counters and concrete two-field iterate
results from arbitrary other Julia values. Atom can be a tagged universal carrier
for all remaining values and mutable references; heterogeneous values are retained.
Julia source: base/tuple.jl:69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
inductive TupleFoldValue (Atom : Type) where
  | atom (value : Atom)
  | native (value : JInt .i64)
  | pair (first second : TupleFoldValue Atom)
  deriving Repr

/-- The two concrete tuple kinds select their installed iteration semantics.
Concrete iteration uses field order. Full name/type/object identity is retained
by FoldTuple.original for selected length/invoke callees.
Julia source: base/reduce.jl:65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- end
-- /Source
inductive TupleFoldKind where
  | tuple
  | namedTuple
  deriving Repr, DecidableEq

/-- An immutable tuple or NamedTuple with a constructible native field count.
The bound is the representation invariant of nfields/length, not a restriction
on the values. References in the fields retain their identity in the mutable world. The optional
original token retains complete source object/type/name identity for selected
callees; none denotes the canonical concrete storage-only test representation.
Julia source: base/reduce.jl:65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- end
-- /Source
structure FoldTuple (Atom : Type) where
  kind : TupleFoldKind
  values : List (TupleFoldValue Atom)
  fits : values.length ≤ IntTy.i64.max.toNat
  original : Option Atom := none

/-- Native nfields/length. The stored bound makes the representation conversion exact.
It performs no Julia arithmetic in an unbounded accumulator.
Julia source: base/tuple.jl:28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- /Source
def foldTupleLength {Atom : Type} (t : FoldTuple Atom) : JInt .i64 :=
  JuliaLean.base.int.lit .i64 t.values.length

/-- Concrete immutable tuple storage view. Every actual tuple field is present;
the generic Core field reader retains its actual bounds/error behavior.
Julia source: base/tuple.jl:33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def foldTupleView {Atom : Type} (t : FoldTuple Atom) : FoldObjectView (TupleFoldValue Atom) :=
  .fields (t.values.map some) (by simpa using t.fits)

/-- Concrete native tuple/NamedTuple field access, used by afoldl and by the
known iterate methods. The Core primitive performs the bounds check.
Julia source: base/tuple.jl:33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def foldTupleGet {Atom E : Type} (t : FoldTuple Atom) (i : JInt .i64) :
    Except (FoldError E) (TupleFoldValue Atom) :=
  foldFieldRead (foldTupleView t) i

/-- Bounded positional varargs retain original field order and aliases.
NamedTuple names are not passed to afoldl. Julia source: base/reduce.jl:65-68. -/
-- Source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- end
-- /Source
structure TupleFoldArguments (Atom : Type) where
  values : List (TupleFoldValue Atom)
  fits : values.length ≤ IntTy.i64.max.toNat

/-- Selected operator behavior is unrestricted and includes changing accumulator
types, errors, mutation and divergence. atomGetindex and nonNativeIterate are
selected dispatch only on types the corresponding calls do not fix. They may
be reached after a selected iteration or indexing method returns a different
result/state. atomFields is current runtime storage metadata, as in FoldProtocolOps.
Julia source: base/reduce.jl:65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- end
-- /Source
structure TupleFoldOps (W E Atom O : Type) where
  apply : O → TupleFoldValue Atom → TupleFoldValue Atom →
    FoldEval W (FoldError E) (TupleFoldValue Atom)
  atomGetindex : Atom → JInt .i64 → FoldEval W (FoldError E) (TupleFoldValue Atom)
  nonNativeIterate : FoldTuple Atom → TupleFoldValue Atom →
    FoldEval W (FoldError E) (Option (TupleFoldValue Atom))
  atomFields : W → Atom → FoldObjectView (TupleFoldValue Atom)
  selectedLength : FoldTuple Atom → Option (FoldEval W (FoldError E) (TupleFoldValue Atom)) := fun _ => none
  compareLength : TupleFoldValue Atom → JInt .i64 →
    FoldEval W (FoldError E) (Bool ⊕ TupleFoldValue Atom)
  selectedAfoldl : O → TupleFoldValue Atom → TupleFoldArguments Atom →
    Option (FoldEval W (FoldError E) (TupleFoldValue Atom)) := fun _ _ _ => none
  selectedInvoke : O → TupleFoldValue Atom → FoldTuple Atom →
    Option (FoldEval W (FoldError E) (TupleFoldValue Atom)) := fun _ _ _ => none

/-- Known tuple iteration uses the lower and upper native bound tests before
reading a field, and increments with installed wrapping native addition.
Julia source: base/tuple.jl:69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def iterateFoldTuple {W E Atom : Type} (t : FoldTuple Atom) (i : JInt .i64) :
    FoldEval W (FoldError E) (Option (TupleFoldValue Atom)) := do
  if JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1) i &&
      JuliaLean.base.int.le i (foldTupleLength t) then
    let value ← liftExcept (foldTupleGet (E := E) t i)
    pure (some (.pair value (.native
      (JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1)))))
  else pure none

/-- Known NamedTuple iteration tests only the upper bound. A negative wrapped
native state reaches the real Core field bounds error, rather than becoming done.
The field count and all additions are native Int values.
Julia source: base/namedtuple.jl:159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/namedtuple.jl:159-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::NamedTuple) = nfields(t)
-- iterate(t::NamedTuple, iter=1) = iter > nfields(t) ? nothing : (getfield(t, iter), iter + 1)
-- /Source
def iterateFoldNamedTuple {W E Atom : Type} (t : FoldTuple Atom) (i : JInt .i64) :
    FoldEval W (FoldError E) (Option (TupleFoldValue Atom)) := do
  if JuliaLean.base.int.lt (foldTupleLength t) i then pure none
  else
    let value ← liftExcept (foldTupleGet (E := E) t i)
    pure (some (.pair value (.native
      (JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1)))))

/-- Stored native integers have no fields, and a generated pair has its two
actual fields in order. Other values retain their runtime storage view. This
view performs no user call and is read only for the concrete iterate pair.
Julia source: base/tuple.jl:33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def tupleProtocolFields {W E Atom O : Type} (ops : TupleFoldOps W E Atom O)
    (world : W) : TupleFoldValue Atom → FoldObjectView (TupleFoldValue Atom)
  | .atom value => ops.atomFields world value
  | .native _ => .fields [] (by change 0 ≤ IntTy.i64.max.toNat; decide)
  | .pair first second => .fields [some first, some second] (by change 2 ≤ IntTy.i64.max.toNat; decide)

/-- Concrete pair getindex is Core.getfield. Native-number getindex calls the
installed number method with installed native equality. Other types select their
genuine getindex method. Selected iteration may return any represented value.
Julia source: base/tuple.jl:33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def tupleProtocolGetindex {W E Atom O : Type} (ops : TupleFoldOps W E Atom O)
    (value : TupleFoldValue Atom) (i : JInt .i64) :
    FoldEval W (FoldError E) (TupleFoldValue Atom) := do
  match value with
  | .atom atom => ops.atomGetindex atom i
  | .pair first second =>
      liftExcept (foldFieldRead (E := E) (.fields [some first, some second] (by change 2 ≤ IntTy.i64.max.toNat; decide)) i)
  | .native number =>
      match JuliaLean.base.number.getindexOne
          (fun j => .ok (JuliaLean.base.int.eq j (JuliaLean.base.int.lit .i64 1))) number i with
      | .ok result => pure (.native result)
      | .error _ => throw .boundsError

/-- Zero-argument afoldl returns the original accumulator, with no operator call.
Julia source: base/operators.jl:622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- afoldl(op, a) = a
-- /Source
def tupleAfoldlOne {W E Atom O : Type} (_op : O) (a : TupleFoldValue Atom) :
    FoldEval W (FoldError E) (TupleFoldValue Atom) := pure a

/-- Close the installed OrdinalRange iterator over the concrete Int64 UnitRange
used by afoldl. Field reads, native equality/arithmetic and same-type conversion
are fixed to their installed Base models. The proof argument only eliminates an
impossible error from this closed call; it states no callback correctness law.
Julia source: base/range.jl:937-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:937-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(r::OrdinalRange{T}, i) where {T}
--     @inline
--     i == last(r) && return nothing
--     next = convert(T, i + step(r))
--     (next, next)
-- end
-- /Source
def tupleRangeNext (r : JuliaLean.base.range.UnitRange (JInt .i64)) (i : JInt .i64) :
    Option (JInt .i64 × JInt .i64) :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨⟩
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JConvert (JInt .i64) (JInt .i64) :=
    ⟨fun x => .ok (JuliaLean.base.number.convertSame x)⟩
  letI : JuliaLean.base.range.JLast (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.last_OrdinalRange (T := JInt .i64) (A := JInt .i64)⟩
  letI : JuliaLean.base.range.JZero (JInt .i64) := ⟨JuliaLean.base.int.lit .i64 0⟩
  letI : JuliaLean.base.range.JOneunit (JInt .i64) := ⟨JuliaLean.base.int.lit .i64 1⟩
  letI : HSub (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.sub⟩
  letI : JuliaLean.base.range.JStep (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨fun r => .ok (JuliaLean.base.range.step_AbstractUnitRange (T := JInt .i64) (D := JInt .i64) r)⟩
  letI : JuliaLean.base.range.JEq (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.eq⟩
  letI : HAdd (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.add⟩
  JuliaLean.base.int.okOf (JuliaLean.base.range.iterate_OrdinalRange_state (T := JInt .i64) (S := JInt .i64) (E := JInt .i64) r i)
    (by
      intro error impossible
      let next := JuliaLean.base.int.add i
        (JuliaLean.base.int.sub (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 0))
      change ((if JuliaLean.base.int.eq i r.stop then .ok none
        else .ok (some (next, next))) :
        JuliaLean.base.range.JlX (Option (JInt .i64 × JInt .i64))) = .error error at impossible
      split at impossible <;> cases impossible)


/-- Close the installed native colon, UnitRange constructor and unitrange_last methods over concrete native comparison, wrapping subtraction, oneunit and same-type conversion. The small proof only eliminates impossible error cases of those closed primitives.
Julia source: base/range.jl:5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- /Source
def tupleRangeConstruct (start stop : JInt .i64) : JuliaLean.base.range.UnitRange (JInt .i64) :=
  letI : JuliaLean.base.range.JLe (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.le⟩
  letI : JuliaLean.base.range.JWrappingSub (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.sub⟩
  letI : JuliaLean.base.range.JRangeWrappingSub (JInt .i64) (JInt .i64) (JInt .i64) :=
    ⟨JuliaLean.base.range._range_wrapping_sub_BitInteger⟩
  letI : JuliaLean.base.range.JOneunit (JInt .i64) := ⟨JuliaLean.base.int.lit .i64 1⟩
  letI : JuliaLean.base.range.JConvert (JInt .i64) (JInt .i64) := ⟨fun x => .ok (JuliaLean.base.number.convertSame x)⟩
  letI : JuliaLean.base.range.JUnitrangeLast (JInt .i64) (JInt .i64) :=
    ⟨JuliaLean.base.range.unitrange_last_Integer (D := JInt .i64) (Q := JInt .i64)⟩
  letI : JuliaLean.base.range.JUnitRangeT (JInt .i64) (JInt .i64) (JInt .i64) :=
    ⟨JuliaLean.base.range.UnitRange_T_new⟩
  JuliaLean.base.int.okOf (JuliaLean.base.range.colon_T_T_Real start stop) (by
    intro error impossible
    change ((do
      let last ← (if JuliaLean.base.int.le start stop then .ok stop else
        .ok (JuliaLean.base.int.sub start (JuliaLean.base.int.lit .i64 1)))
      pure ⟨start, last⟩) : JuliaLean.base.range.JlX (JuliaLean.base.range.UnitRange (JInt .i64))) = .error error at impossible
    split at impossible <;> cases impossible)

/-- Close installed first/last/isempty and initial OrdinalRange iteration over the native UnitRange; first is evaluated twice as in the pinned source. The representation-only proof excludes impossible primitive errors.
Julia source: base/range.jl:935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:935-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- /Source
def tupleRangeStart (r : JuliaLean.base.range.UnitRange (JInt .i64)) : Option (JInt .i64 × JInt .i64) :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨⟩
  letI : JuliaLean.base.range.JFieldStart (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨fun r => r.start⟩
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JConvert (JInt .i64) (JInt .i64) := ⟨fun x => .ok (JuliaLean.base.number.convertSame x)⟩
  letI : JuliaLean.base.range.JFirst (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.first_OrdinalRange (T := JInt .i64) (A := JInt .i64)⟩
  letI : JuliaLean.base.range.JLast (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.last_OrdinalRange (T := JInt .i64) (A := JInt .i64)⟩
  letI : JuliaLean.base.range.JLt (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.lt⟩
  letI : JuliaLean.base.range.JIsempty (JuliaLean.base.range.UnitRange (JInt .i64)) :=
    ⟨JuliaLean.base.range.isempty_AbstractUnitRange (T := JInt .i64)⟩
  JuliaLean.base.int.okOf (JuliaLean.base.range.iterate_OrdinalRange (T := JInt .i64) r) (by
    intro error impossible
    change ((if JuliaLean.base.int.lt r.stop r.start then .ok none
      else .ok (some (r.start, r.start))) : JuliaLean.base.range.JlX (Option (JInt .i64 × JInt .i64))) = .error error at impossible
    split at impossible <;> cases impossible)

/-- Native UnitRange and an arbitrary dynamic range returned by colon are distinguished without losing the returned object.
Julia source: base/operators.jl:658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:658-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
inductive TupleDynamicRange (A : Type) where
  | native (value : JuliaLean.base.range.UnitRange (JInt .i64))
  | other (value : TupleFoldValue A)

/-- Full selected routes for the tuple method and its necessary concrete callees. All leaves preserve mutation, errors and divergence. none selects the pinned Base body; some selects a genuinely more specific method on unfixed parameter types. Symbol classification and the NamedTuple field-name table are pure runtime metadata; they are not callable Julia methods. Other iterators remain representable after a selected Rest getter or constructor.
Julia source: base/reduce.jl:65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- end
-- /Source
structure TupleFullOps (W E A O : Type) extends TupleFoldOps W E A O where
  selectedIterate : FoldTuple A → Option (TupleFoldValue A) → Option (FoldEval W (FoldError E) (Option (TupleFoldValue A))) := fun _ _ => none
  selectedTupleIndex : FoldTuple A → TupleFoldValue A → Option (FoldEval W (FoldError E) (TupleFoldValue A)) := fun _ _ => none
  selectedResultIndex : TupleFoldValue A → JInt .i64 → Option (FoldEval W (FoldError E) (TupleFoldValue A)) := fun _ _ => none
  lessEqual : TupleFoldValue A → TupleFoldValue A → FoldEval W (FoldError E) (Bool ⊕ TupleFoldValue A)
  greater : TupleFoldValue A → JInt .i64 → FoldEval W (FoldError E) (Bool ⊕ TupleFoldValue A)
  addOne : TupleFoldValue A → FoldEval W (FoldError E) (TupleFoldValue A)
  equalLength : TupleFoldValue A → JInt .i64 → FoldEval W (FoldError E) (Bool ⊕ TupleFoldValue A)
  nonNativeTupleIndex : FoldTuple A → TupleFoldValue A → FoldEval W (FoldError E) (TupleFoldValue A)
  symbolView : A → Option String
  namedFieldNames : FoldTuple A → {names : List String // names.length ≤ IntTy.i64.max.toNat}
  colon : JInt .i64 → TupleFoldValue A → FoldEval W (FoldError E) (TupleDynamicRange A)
  rangeIterate : TupleFoldValue A → Option (TupleFoldValue A) → FoldEval W (FoldError E) (Option (TupleFoldValue A))
  otherIterate : A → Option (TupleFoldValue A) → FoldEval W (FoldError E) (Option (TupleFoldValue A))
  customRest : A → TupleFoldValue A → FoldEval W (FoldError E) (FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A))
  selectedRest : FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A) → TupleFoldValue A → Option (FoldEval W (FoldError E) (FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A))) := fun _ _ => none
  selectedRestConstructor : FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A) → TupleFoldValue A → Option (FoldEval W (FoldError E) (FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A))) := fun _ _ => none
  selectedRestIterate : FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A) → Option (TupleFoldValue A) → Option (FoldEval W (FoldError E) (Option (TupleFoldValue A))) := fun _ _ => none
  selectedRestIteratorProperty : FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A) → Option (FoldEval W (FoldError E) (FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A))) := fun _ => none
  selectedRestStateProperty : FoldIterator (FoldTuple A ⊕ A) (TupleFoldValue A) → Option (FoldEval W (FoldError E) (TupleFoldValue A)) := fun _ => none

/-- Conditions use the installed Bool assertion and retain its TypeError throw point.
Julia source: base/tuple.jl:69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def tupleFullBool {W E A : Type} (value : Bool ⊕ TupleFoldValue A) : FoldEval W (FoldError E) Bool :=
  match JuliaLean.base.reduce.assertBool value with
  | .ok result => pure result
  | .error _ => throw .typeError

/-- Concrete nfields length or the actual selected more specific length method.
Julia source: base/tuple.jl:28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- /Source
def tupleFullLength {W E A O : Type} (ops : TupleFullOps W E A O) (t : FoldTuple A) : FoldEval W (FoldError E) (TupleFoldValue A) :=
  match ops.selectedLength t with
  | some call => call
  | none => pure (.native (foldTupleLength t))

/-- Selected tuple indexing preserves every argument. The known native-index body uses concrete Core field access.
Julia source: base/tuple.jl:33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def tupleFullIndex {W E A O : Type} (ops : TupleFullOps W E A O) (t : FoldTuple A) (i : TupleFoldValue A) : FoldEval W (FoldError E) (TupleFoldValue A) :=
  match ops.selectedTupleIndex t i with
  | some call => call
  | none => match i with
    | .native index => liftExcept (foldTupleGet (E := E) t index)
    | other => ops.nonNativeTupleIndex t other

/-- Core field access accepts a native integer or Symbol. Missing names raise FieldError (base/boot.jl575–578); invalid index types raise TypeError. Name lookup is pure immutable metadata, and the value is selected from the actual stored fields.
Julia source: base/namedtuple.jl:159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/namedtuple.jl:159-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::NamedTuple) = nfields(t)
-- iterate(t::NamedTuple, iter=1) = iter > nfields(t) ? nothing : (getfield(t, iter), iter + 1)
-- /Source
def tupleFullNamedField {W E A O : Type} (ops : TupleFullOps W E A O) (t : FoldTuple A) (i : TupleFoldValue A) : FoldEval W (FoldError E) (TupleFoldValue A) := do
  match i with
  | .native index => liftExcept (foldTupleGet (E := E) t index)
  | .atom atom =>
    match ops.symbolView atom with
    | none => throw .typeError
    | some name =>
      match (ops.namedFieldNames t).val.idxOf? name with
      | none => throw .fieldError
      | some index =>
        match t.values[index]? with
        | some value => pure value
        | none => throw .boundsError
  | .pair _ _ => throw .typeError

/-- The known Tuple body checks the native lower bound before the selected length and upper comparison, then selects getindex and increments natively.
Julia source: base/tuple.jl:69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def tupleFullTupleIterate {W E A O : Type} (ops : TupleFullOps W E A O) (t : FoldTuple A) (i : JInt .i64) : FoldEval W (FoldError E) (Option (TupleFoldValue A)) :=
  match ops.selectedLength t, ops.selectedTupleIndex t (.native i) with
  | none, none => iterateFoldTuple t i
  | _, _ => do
    if !(JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1) i) then return none
    let len ← tupleFullLength ops t
    let within ← match len with
      | .native n => pure (JuliaLean.base.int.le i n)
      | other => tupleFullBool (← ops.lessEqual (.native i) other)
    if !within then return none
    let value ← tupleFullIndex ops t (.native i)
    pure (some (.pair value (.native (JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1)))))


/-- The full NamedTuple body retains its untyped state, upper test, concrete nfields/getfield, and selected state addition after the field read.
Julia source: base/namedtuple.jl:159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/namedtuple.jl:159-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::NamedTuple) = nfields(t)
-- iterate(t::NamedTuple, iter=1) = iter > nfields(t) ? nothing : (getfield(t, iter), iter + 1)
-- /Source
def tupleFullNamedIterate {W E A O : Type} (ops : TupleFullOps W E A O) (t : FoldTuple A) (i : TupleFoldValue A) : FoldEval W (FoldError E) (Option (TupleFoldValue A)) :=
  match i with
  | .native native => iterateFoldNamedTuple t native
  | other => do
    let done ← tupleFullBool (← ops.greater other (foldTupleLength t))
    if done then return none
    let value ← tupleFullNamedField ops t other
    let next ← ops.addOne other
    pure (some (.pair value next))

/-- Unary iteration supplies native one and redispatches on the same receiver. Each genuinely selected iterate route precedes the pinned body; a nonnative state on Tuple selects its own method.
Julia source: base/tuple.jl:69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def tupleFullIterate {W E A O : Type} (ops : TupleFullOps W E A O) (t : FoldTuple A) (state : Option (TupleFoldValue A)) : FoldEval W (FoldError E) (Option (TupleFoldValue A)) := do
  match ops.selectedIterate t state with
  | some call => call
  | none => match state with
    | none => tupleFullIterate ops t (some (.native (JuliaLean.base.int.lit .i64 1)))
    | some actual => match t.kind with
      | .namedTuple => tupleFullNamedIterate ops t actual
      | .tuple => match actual with
        | .native i => tupleFullTupleIterate ops t i
        | other => ops.nonNativeIterate t other
partial_fixpoint

/-- Close the actual generic loop over Tuple/NamedTuple and arbitrary iterators returned by selected Rest routes. Initial pair getindex can specialize; the for-loop Core field reads remain fixed.
Julia source: base/reduce.jl:51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:51-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op::OP, init, itr) where {OP}
--     # Unroll the loop once to check if the iterator is empty.
--     # If init is known, the call to op may be evaluated at compile time
--     y = iterate(itr)
--     y === nothing && return init
--     v = op(init, y[1])
--     # Using a for loop is more performant than a while loop (see #56492)
--     # This unrolls the loop a second time before entering the body
--     for x in Iterators.rest(itr, y[2])
--         v = op(v, x)
--     end
--     return v
-- end
-- /Source
def tupleFullProtocol {W E A O : Type} (ops : TupleFullOps W E A O) : FoldProtocolOps W E (FoldTuple A ⊕ A) (TupleFoldValue A) O where
  iterate := fun object state => match object with
    | .inl t => tupleFullIterate ops t state
    | .inr object => ops.otherIterate object state
  getindex := fun value i => match ops.selectedResultIndex value i with
    | some call => call
    | none => tupleProtocolGetindex ops.toTupleFoldOps value i
  apply := ops.apply
  customRest := fun object state => match object with
    | .inl t => pure (.knownRest (.ordinary (.inl t)) state)
    | .inr object => ops.customRest object state
  fields := tupleProtocolFields ops.toTupleFoldOps
  selectedRest := ops.selectedRest
  selectedRestConstructor := ops.selectedRestConstructor
  selectedRestIterate := ops.selectedRestIterate
  selectedRestIteratorProperty := ops.selectedRestIteratorProperty
  selectedRestStateProperty := ops.selectedRestStateProperty

/-- Each afoldl length equality preserves native equality or the actual selected nonnative equality plus Bool assertion.
Julia source: base/operators.jl:623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:623-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function afoldl(op, a, bs...)
--     @_terminates_locally_meta
--     l = length(bs)
--     i =  0; y = a;            l == i && return y
--     #@nexprs 31 i -> (y = op(y, bs[i]); l == i && return y)
--     i =  1; y = op(y, bs[i]); l == i && return y
-- /Source
def tupleFullEqual {W E A O : Type} (ops : TupleFullOps W E A O) (length : TupleFoldValue A) (i : JInt .i64) : FoldEval W (FoldError E) Bool :=
  match length with
  | .native n => pure (JuliaLean.base.int.eq n i)
  | other => do tupleFullBool (← ops.equalLength other i)

/-- Dispatch unary or binary closed native range iteration while retaining the native state type.
Julia source: base/range.jl:935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:935-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- 
-- function iterate(r::OrdinalRange{T}, i) where {T}
--     @inline
--     i == last(r) && return nothing
--     next = convert(T, i + step(r))
--     (next, next)
-- end
-- /Source
def tupleNativeRangeStep (range : JuliaLean.base.range.UnitRange (JInt .i64)) (state : Option (JInt .i64)) :
    Option (JInt .i64 × JInt .i64) :=
  match state with
  | none => tupleRangeStart range
  | some i => tupleRangeNext range i

/-- The concrete native range tail uses installed initial/next iteration. Its returned two-field tuple contains native value/state, so the two fixed Core field reads are its product projections. No impossible nonnative state is given a fabricated behavior.
Julia source: base/operators.jl:658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:658-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
def tupleFullNativeTail {W E A O : Type} (ops : TupleFullOps W E A O) (op : O) (t : FoldTuple A)
    (range : JuliaLean.base.range.UnitRange (JInt .i64)) (state : Option (JInt .i64)) (acc : TupleFoldValue A) :
    FoldEval W (FoldError E) (TupleFoldValue A) := do
  match tupleNativeRangeStep range state with
  | none => pure acc
  | some pair =>
    let index := pair.1
    let next := pair.2
    let value ← tupleFullIndex ops t (.native index)
    let acc ← ops.apply op acc value
    tupleFullNativeTail ops op t range (some next) acc
partial_fixpoint

/-- The actual dynamic tail for-loop extracts Core fields in order, indexes the varargs tuple, reduces, and recurs with the returned state. Arbitrary returned objects/errors/divergence are preserved without a fuel bound.
Julia source: base/operators.jl:658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:658-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
def tupleFullDynamicTail {W E A O : Type} (ops : TupleFullOps W E A O) (op : O) (t : FoldTuple A)
    (range : TupleFoldValue A) (state : Option (TupleFoldValue A)) (acc : TupleFoldValue A) :
    FoldEval W (FoldError E) (TupleFoldValue A) := do
  match ← ops.rangeIterate range state with
  | none => pure acc
  | some result =>
    let index ← foldGetfield (tupleFullProtocol ops) result (JuliaLean.base.int.lit .i64 1)
    let next ← foldGetfield (tupleFullProtocol ops) result (JuliaLean.base.int.lit .i64 2)
    let value ← tupleFullIndex ops t index
    let acc ← ops.apply op acc value
    tupleFullDynamicTail ops op t range (some next) acc
partial_fixpoint

/-- Choose the concrete native loop or the actual dynamic loop for the exact range returned by colon. Both begin with unary iteration and retain their own returned states.
Julia source: base/operators.jl:658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:658-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
def tupleFullAfoldlTail {W E A O : Type} (ops : TupleFullOps W E A O) (op : O) (t : FoldTuple A)
    (range : TupleDynamicRange A) (acc : TupleFoldValue A) : FoldEval W (FoldError E) (TupleFoldValue A) :=
  match range with
  | .native range => tupleFullNativeTail ops op t range none acc
  | .other range => tupleFullDynamicTail ops op t range none acc

/-- All31 unrolled stages and the initial length-zero test remain explicit. Every interior length, equality, indexing and dynamic colon call keeps its exact evaluation order.
Julia source: base/operators.jl:623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:623-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function afoldl(op, a, bs...)
--     @_terminates_locally_meta
--     l = length(bs)
--     i =  0; y = a;            l == i && return y
--     #@nexprs 31 i -> (y = op(y, bs[i]); l == i && return y)
--     i =  1; y = op(y, bs[i]); l == i && return y
--     i =  2; y = op(y, bs[i]); l == i && return y
--     i =  3; y = op(y, bs[i]); l == i && return y
--     i =  4; y = op(y, bs[i]); l == i && return y
--     i =  5; y = op(y, bs[i]); l == i && return y
--     i =  6; y = op(y, bs[i]); l == i && return y
--     i =  7; y = op(y, bs[i]); l == i && return y
--     i =  8; y = op(y, bs[i]); l == i && return y
--     i =  9; y = op(y, bs[i]); l == i && return y
--     i = 10; y = op(y, bs[i]); l == i && return y
--     i = 11; y = op(y, bs[i]); l == i && return y
--     i = 12; y = op(y, bs[i]); l == i && return y
--     i = 13; y = op(y, bs[i]); l == i && return y
--     i = 14; y = op(y, bs[i]); l == i && return y
--     i = 15; y = op(y, bs[i]); l == i && return y
--     i = 16; y = op(y, bs[i]); l == i && return y
--     i = 17; y = op(y, bs[i]); l == i && return y
--     i = 18; y = op(y, bs[i]); l == i && return y
--     i = 19; y = op(y, bs[i]); l == i && return y
--     i = 20; y = op(y, bs[i]); l == i && return y
--     i = 21; y = op(y, bs[i]); l == i && return y
--     i = 22; y = op(y, bs[i]); l == i && return y
--     i = 23; y = op(y, bs[i]); l == i && return y
--     i = 24; y = op(y, bs[i]); l == i && return y
--     i = 25; y = op(y, bs[i]); l == i && return y
--     i = 26; y = op(y, bs[i]); l == i && return y
--     i = 27; y = op(y, bs[i]); l == i && return y
--     i = 28; y = op(y, bs[i]); l == i && return y
--     i = 29; y = op(y, bs[i]); l == i && return y
--     i = 30; y = op(y, bs[i]); l == i && return y
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
def tupleFullAfoldlMany {W E A O : Type} (ops : TupleFullOps W E A O) (op : O) (init : TupleFoldValue A) (t : FoldTuple A) : FoldEval W (FoldError E) (TupleFoldValue A) := do
  let length ← tupleFullLength ops t
  let y := init
  if ← tupleFullEqual ops length (JuliaLean.base.int.lit .i64 0) then return y
  let i := JuliaLean.base.int.lit .i64 1
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 2
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 3
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 4
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 5
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 6
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 7
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 8
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 9
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 10
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 11
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 12
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 13
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 14
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 15
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 16
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 17
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 18
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 19
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 20
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 21
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 22
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 23
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 24
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 25
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 26
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 27
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 28
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 29
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 30
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let i := JuliaLean.base.int.lit .i64 31
  let value ← tupleFullIndex ops t (.native i)
  let y ← ops.apply op y value
  if ← tupleFullEqual ops length i then return y
  let start := JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1)
  let range ← match length with
    | .native stop => pure (.native (tupleRangeConstruct start stop))
    | other => ops.colon start other
  tupleFullAfoldlTail ops op t range y

/-- Full tuple specialization: selected length/comparison, actual native positional splat, selected or real afoldl, and selected invoke or the real generic loop. Varargs are a Tuple even when the original receiver is NamedTuple. The fixed Core._apply_iterate fastpath explicitly copies fields of both Tuple and NamedTuple (src/builtins.c939–951 at the pin), without selected iteration.
Julia source: base/reduce.jl:65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:65-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _foldl_impl(op, init, itr::Union{Tuple,NamedTuple})
--     length(itr) <= 32 && return afoldl(op, init, itr...)
--     @invoke _foldl_impl(op, init, itr::Any)
-- end
-- /Source
def foldlTuple {W E A O : Type} (ops : TupleFullOps W E A O) (op : O) (init : TupleFoldValue A) (t : FoldTuple A) : FoldEval W (FoldError E) (TupleFoldValue A) := do
  let length ← tupleFullLength ops t
  let short ← match length with
    | .native n => pure (JuliaLean.base.int.le n (JuliaLean.base.int.lit .i64 32))
    | other => tupleFullBool (← ops.compareLength other (JuliaLean.base.int.lit .i64 32))
  if short then
    match ops.selectedAfoldl op init ⟨t.values, t.fits⟩ with
    | some call => call
    | none => match t.values with
      | [] => tupleAfoldlOne op init
      | _ :: _ => tupleFullAfoldlMany ops op init {kind := .tuple, values := t.values, fits := t.fits}
  else
    match ops.selectedInvoke op init t with
    | some call => call
    | none => foldlGeneric (tupleFullProtocol ops) op init (.ordinary (.inl t))

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Selected property access: stored uses the fixed concrete field; custom
is only a genuinely selected user getproperty method for that same field.
Julia source: base/Base_compiler.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/Base_compiler.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getproperty(x, f::Symbol) = (@inline; getfield(x, f))
-- /Source
inductive PropertySelection (m : Type → Type) (Object Value : Type) where
  | stored
  | custom (call : Object → m Value)

/-- Each call below supplies a fixed stored-field projection for the
installed Base getfield path. Selected user access can retain arbitrary effects.
Julia source: base/Base_compiler.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/Base_compiler.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getproperty(x, f::Symbol) = (@inline; getfield(x, f))
-- /Source
def readSelectedProperty {m : Type → Type} [Monad m] {Object Value : Type}
    (selection : PropertySelection m Object Value) (field : Object → Value)
    (object : Object) : m Value :=
  match selection with
  | .stored => pure (field object)
  | .custom call => call object

/-- BottomRF storage retains arbitrary callable or non-callable values.
Non-callable values fail at invocation, not at construction.
Julia source: base/reduce.jl:79-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:79-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct BottomRF{T}
--     rf::T
-- end
-- /Source
structure BottomAdapter (F : Type) where
  rf : F

/-- Open property, first-element, and binary invocation dispatch. No laws
are assumed; the concrete stored-property case remains implemented.
Julia source: base/reduce.jl:83-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:83-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BottomRF)(::_InitialValue, x) = reduce_first(op.rf, x)
-- @inline (op::BottomRF)(acc, x) = op.rf(acc, x)
-- /Source
structure BottomAdapterOps (m : Type → Type) (F Acc Input Result : Type) where
  rfProperty : PropertySelection m (BottomAdapter F) F := .stored
  first : F → Input → m Result
  call : F → Acc → Input → m Result

/-- The sentinel specialization reads rf then invokes reduce_first once
with the original element. The binary reducer is not called.
Julia source: base/reduce.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BottomRF)(::_InitialValue, x) = reduce_first(op.rf, x)
-- /Source
def bottomInitial {m : Type → Type} [Monad m] {F Acc Input Result : Type}
    (ops : BottomAdapterOps m F Acc Input Result) (op : BottomAdapter F)
    (x : Input) : m Result := do
  let rf ← readSelectedProperty ops.rfProperty BottomAdapter.rf op
  ops.first rf x

/-- Read rf and invoke it with the original accumulator and element.
Acc may be a universal Julia-value carrier, allowing dynamic type changes.
Julia source: base/reduce.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BottomRF)(acc, x) = op.rf(acc, x)
-- /Source
def bottomApply {m : Type → Type} [Monad m] {F Acc Input Result : Type}
    (ops : BottomAdapterOps m F Acc Input Result) (op : BottomAdapter F)
    (acc : Acc) (x : Input) : m Result := do
  let rf ← readSelectedProperty ops.rfProperty BottomAdapter.rf op
  ops.call rf acc x

/-- Selected mapping/reduction leaves and property routes. The immutable
MappingRF storage and both constructors are reused from the baseline.
Julia source: base/reduce.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::MappingRF)(acc, x) = op.rf(acc, op.f(x))
-- /Source
structure MappingAdapterOps (m : Type → Type) (F RF Acc Input Mapped Result : Type) where
  rfProperty : PropertySelection m (MappingRF F RF) RF := .stored
  fProperty : PropertySelection m (MappingRF F RF) F := .stored
  map : F → Input → m Mapped
  call : RF → Acc → Mapped → m Result

/-- Read rf before evaluating f(x), then call the saved rf with the
original accumulator and mapped result. Selected property effects keep this order.
Julia source: base/reduce.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::MappingRF)(acc, x) = op.rf(acc, op.f(x))
-- /Source
def mappingApply {m : Type → Type} [Monad m] {F RF Acc Input Mapped Result : Type}
    (ops : MappingAdapterOps m F RF Acc Input Mapped Result)
    (op : MappingRF F RF) (acc : Acc) (x : Input) : m Result := do
  let rf ← readSelectedProperty ops.rfProperty MappingRF.rf op
  let f ← readSelectedProperty ops.fProperty MappingRF.f op
  let mapped ← ops.map f x
  ops.call rf acc mapped

/-- FilteringRF storage keeps arbitrary predicate and reducer identities.
Julia source: base/reduce.jl:105-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:105-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct FilteringRF{F, T}
--     f::F
--     rf::T
-- end
-- /Source
structure FilteringAdapter (F RF : Type) where
  f : F
  rf : RF

/-- All predicate results are represented, including every non-Bool Other
value. A universal Acc carrier permits changing accumulator types.
Julia source: base/reduce.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::FilteringRF)(acc, x) = op.f(x) ? op.rf(acc, x) : acc
-- /Source
structure FilteringAdapterOps (m : Type → Type) (F RF Acc Input Other : Type) where
  fProperty : PropertySelection m (FilteringAdapter F RF) F := .stored
  rfProperty : PropertySelection m (FilteringAdapter F RF) RF := .stored
  predicate : F → Input → m (Bool ⊕ Other)
  call : RF → Acc → Input → m Acc

/-- Evaluate the predicate once and enforce its Bool condition. False
returns acc without reading rf; true reads and invokes rf. Non-Bool throws
the installed TypeError at the branch, after predicate effects.
Julia source: base/reduce.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::FilteringRF)(acc, x) = op.f(x) ? op.rf(acc, x) : acc
-- /Source
def filteringApply {m : Type → Type} [Monad m] [MonadExceptOf BoolTypeError m]
    {F RF Acc Input Other : Type}
    (ops : FilteringAdapterOps m F RF Acc Input Other)
    (op : FilteringAdapter F RF) (acc : Acc) (x : Input) : m Acc := do
  let f ← readSelectedProperty ops.fProperty FilteringAdapter.f op
  let condition ← ops.predicate f x
  let decision ← liftExcept (JuliaLean.base.reduce.assertBool condition)
  if decision then
    let rf ← readSelectedProperty ops.rfProperty FilteringAdapter.rf op
    ops.call rf acc x
  else pure acc

/-- FlatteningRF storage retains the arbitrary original reducer.
Julia source: base/reduce.jl:118-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:118-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct FlatteningRF{T}
--     rf::T
-- end
-- /Source
structure FlatteningAdapter (F : Type) where
  rf : F

/-- A returned concrete pair using the known Base Tuple destructuring methods,
or any raw Julia object with selected indexed_iterate dispatch. Custom dispatch
on tuple subtypes is represented by custom as well. The raw result is not
assumed iterable, initialized or a pair.
Julia source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function (op::FlatteningRF)(acc, x)
--     op′, itr′ = _xfadjoint(op.rf, x)
--     return _foldl_impl(op′, acc, itr′)
-- end
-- /Source
inductive FlattenTransformResult (V : Type) where
  | pair (op iterator : V)
  | custom (object : V)

/-- Open dispatch for the receiver types that this method does not fix. All
values can inhabit one heterogeneous universal carrier. A custom transform
result is destructured explicitly with indexed_iterate and concrete Core field
reads. The fields map is a pure view of current object storage, not a callee.
Julia source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function (op::FlatteningRF)(acc, x)
--     op′, itr′ = _xfadjoint(op.rf, x)
--     return _foldl_impl(op′, acc, itr′)
-- end
-- /Source
structure FlatteningAdapterOps (W E V : Type) where
  rfProperty : PropertySelection (FoldEval W (FoldError E)) (FlatteningAdapter V) V := .stored
  transform : V → V → FoldEval W (FoldError E) (FlattenTransformResult V)
  indexedIterate : V → JInt .i64 → Option V → FoldEval W (FoldError E) V
  fields : W → V → FoldObjectView V
  fold : V → V → V → FoldEval W (FoldError E) V

/-- Concrete Base indexed_iterate for the known two-element Tuple. The tuple
field read is checked by the installed local Core primitive; the next index
uses native wrapping addition. The state argument is received and ignored,
exactly as in the Julia method. This is a necessary concrete specialization,
not a substitute callback.
Julia source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- /Source
def flattenPairIndexed {E V : Type} (pair : V × V) (index state : JInt .i64) :
    Except (FoldError E) (V × JInt .i64) := do
  let _ := state
  let value ← foldFieldRead (.fields [some pair.1, some pair.2] (by change (2 : Nat) ≤ IntTy.i64.max.toNat; decide)) index
  pure (value, JuliaLean.base.int.add index (JuliaLean.base.int.lit .i64 1))

/-- Read the current storage through the already implemented concrete Core
getter. BoundsError, UndefRefError and the module integer-access TypeError are
raised at the read, preserving its world. The same runtime representation
is used by the generic fold. Lowering: src/julia-syntax.scm:1888-1909,2597-2608.
Julia source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function (op::FlatteningRF)(acc, x)
--     op′, itr′ = _xfadjoint(op.rf, x)
--     return _foldl_impl(op′, acc, itr′)
-- end
-- /Source
def flatteningGetfield {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (object : V) (index : JInt .i64) : FoldEval W (FoldError E) V := do
  let world ← get
  match foldFieldRead (E := E) (ops.fields world object) index with
  | .ok value => pure value
  | .error error => throw error

/-- Ordinary two-variable destructuring uses indexed_iterate at native 1,
then Core fields 1 and 2, then indexed_iterate at native 2 with the observed
destructuring state, then only Core field 1. The second indexed result need
not have a second field. Known Base pair behavior is concrete.
Lowering: src/julia-syntax.scm:1888-1909,2597-2608 at the same pin.
Julia source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function (op::FlatteningRF)(acc, x)
--     op′, itr′ = _xfadjoint(op.rf, x)
--     return _foldl_impl(op′, acc, itr′)
-- end
-- /Source
def flatteningDestructure {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (result : FlattenTransformResult V) : FoldEval W (FoldError E) (V × V) := do
  match result with
  | .pair op iterator =>
      let first ← liftExcept (flattenPairIndexed (E := E) (op, iterator)
        (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 1))
      let second ← liftExcept (flattenPairIndexed (E := E) (op, iterator)
        (JuliaLean.base.int.lit .i64 2) first.2)
      pure (first.1, second.1)
  | .custom object =>
      let first ← ops.indexedIterate object (JuliaLean.base.int.lit .i64 1) none
      let op ← flatteningGetfield ops first (JuliaLean.base.int.lit .i64 1)
      let state ← flatteningGetfield ops first (JuliaLean.base.int.lit .i64 2)
      let second ← ops.indexedIterate object (JuliaLean.base.int.lit .i64 2) (some state)
      let iterator ← flatteningGetfield ops second (JuliaLean.base.int.lit .i64 1)
      pure (op, iterator)

/-- Read the selected rf, transform it with the original input, destructure
the actual returned object, and fold with the observed operator/iterator and
original accumulator. Every dispatch effect/error remains at its source point.
All ordinary and custom result shapes are represented.
Julia source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:122-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function (op::FlatteningRF)(acc, x)
--     op′, itr′ = _xfadjoint(op.rf, x)
--     return _foldl_impl(op′, acc, itr′)
-- end
-- /Source
def flatteningApply {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (op : FlatteningAdapter V) (acc x : V) : FoldEval W (FoldError E) V := do
  let rf ← readSelectedProperty ops.rfProperty FlatteningAdapter.rf op
  let result ← ops.transform rf x
  let transformed ← flatteningDestructure ops result
  ops.fold transformed.1 acc transformed.2

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- A concrete Base pair using installed Tuple destructuring, or any raw
returned object (including a tuple with selected custom indexed_iterate). The
views interpret one heterogeneous Julia-value carrier in the two typed result
positions; they are pure representation maps, not called methods or assumptions
about user behavior. Raw results need not be iterable or initialized.
Julia source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
-- 
-- _xfadjoint_unwrap(itr) = itr, identity
-- function _xfadjoint_unwrap(itr::Generator)
--     itr′, wrap = _xfadjoint_unwrap(itr.iter)
--     itr.f === identity && return itr′, wrap
--     return itr′, wrap ∘ Fix1(MappingRF, itr.f)
-- end
-- function _xfadjoint_unwrap(itr::Filter)
--     itr′, wrap = _xfadjoint_unwrap(itr.itr)
--     return itr′, wrap ∘ Fix1(FilteringRF, itr.flt)
-- end
-- function _xfadjoint_unwrap(itr::Flatten)
--     itr′, wrap = _xfadjoint_unwrap(itr.it)
--     return itr′, wrap ∘ FlatteningRF
-- end
-- /Source
inductive TransformPairResult (O A B : Type) where
  | pair (first : A) (second : B)
  | custom (object : O) (firstView : O → A) (secondView : O → B)

/-- Open indexed_iterate and current raw-object storage. The storage view
is representation data; concrete Core field reads own their checks and errors.
No successful-call, shape or termination law is assumed.
Julia source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
-- 
-- _xfadjoint_unwrap(itr) = itr, identity
-- function _xfadjoint_unwrap(itr::Generator)
--     itr′, wrap = _xfadjoint_unwrap(itr.iter)
--     itr.f === identity && return itr′, wrap
--     return itr′, wrap ∘ Fix1(MappingRF, itr.f)
-- end
-- function _xfadjoint_unwrap(itr::Filter)
--     itr′, wrap = _xfadjoint_unwrap(itr.itr)
--     return itr′, wrap ∘ Fix1(FilteringRF, itr.flt)
-- end
-- function _xfadjoint_unwrap(itr::Flatten)
--     itr′, wrap = _xfadjoint_unwrap(itr.it)
--     return itr′, wrap ∘ FlatteningRF
-- end
-- /Source
structure TransformRawOps (W E I : Type) where
  indexedIterate : I → JInt .i64 → Option I → FoldEval W (FoldError E) I
  fields : W → I → FoldObjectView I

/-- Read present storage with the concrete Core primitive. BoundsError,
UndefRefError and the module integer-field TypeError retain their exact read
point and current world. Core source: src/builtins.c:1173-1234,1572-1583.
Julia source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
-- 
-- _xfadjoint_unwrap(itr) = itr, identity
-- function _xfadjoint_unwrap(itr::Generator)
--     itr′, wrap = _xfadjoint_unwrap(itr.iter)
--     itr.f === identity && return itr′, wrap
--     return itr′, wrap ∘ Fix1(MappingRF, itr.f)
-- end
-- function _xfadjoint_unwrap(itr::Filter)
--     itr′, wrap = _xfadjoint_unwrap(itr.itr)
--     return itr′, wrap ∘ Fix1(FilteringRF, itr.flt)
-- end
-- function _xfadjoint_unwrap(itr::Flatten)
--     itr′, wrap = _xfadjoint_unwrap(itr.it)
--     return itr′, wrap ∘ FlatteningRF
-- end
-- /Source
def transformGetfield {W E I : Type} (ops : TransformRawOps W E I)
    (object : I) (index : JInt .i64) : FoldEval W (FoldError E) I := do
  let world ← get
  match foldFieldRead (E := E) (ops.fields world object) index with
  | .ok value => pure value
  | .error error => throw error

/-- Concrete indexed_iterate at field 1 of a known two-element Tuple.
That initialized field exists. The state is the actual native wrapping 1+1,
and the supplied previous state is ignored, as in Base.
Julia source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- /Source
def transformPairFirst {A B : Type} (a : A) (_b : B) (_state : JInt .i64) : A × JInt .i64 :=
  (a, JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 1))

/-- Concrete indexed_iterate at field 2 of a known two-element Tuple.
It preserves the second field and computes native 2+1; the caller discards
that state. The input state is received and ignored exactly as in Base.
Julia source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- /Source
def transformPairSecond {A B : Type} (_a : A) (b : B) (_state : JInt .i64) : B × JInt .i64 :=
  (b, JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 2) (JuliaLean.base.int.lit .i64 1))

/-- Execute ordinary two-variable destructuring: indexed_iterate at 1;
Core fields 1 and 2; indexed_iterate at 2 with that observed state; Core field 1
only. Known two-element Tuple behavior is concrete. Raw objects may be malformed
or use custom iteration. Lowering: src/julia-syntax.scm:1888-1909,2597-2608.
Julia source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
-- 
-- _xfadjoint_unwrap(itr) = itr, identity
-- function _xfadjoint_unwrap(itr::Generator)
--     itr′, wrap = _xfadjoint_unwrap(itr.iter)
--     itr.f === identity && return itr′, wrap
--     return itr′, wrap ∘ Fix1(MappingRF, itr.f)
-- end
-- function _xfadjoint_unwrap(itr::Filter)
--     itr′, wrap = _xfadjoint_unwrap(itr.itr)
--     return itr′, wrap ∘ Fix1(FilteringRF, itr.flt)
-- end
-- function _xfadjoint_unwrap(itr::Flatten)
--     itr′, wrap = _xfadjoint_unwrap(itr.it)
--     return itr′, wrap ∘ FlatteningRF
-- end
-- /Source
def destructureTransformPair {W E I A B : Type} (ops : TransformRawOps W E I)
    (result : TransformPairResult I A B) : FoldEval W (FoldError E) (A × B) := do
  match result with
  | .pair a b =>
      let first := transformPairFirst a b (JuliaLean.base.int.lit .i64 1)
      let second := transformPairSecond a b first.2
      pure (first.1, second.1)
  | .custom object firstView secondView =>
      let first ← ops.indexedIterate object (JuliaLean.base.int.lit .i64 1) none
      let a ← transformGetfield ops first (JuliaLean.base.int.lit .i64 1)
      let state ← transformGetfield ops first (JuliaLean.base.int.lit .i64 2)
      let second ← ops.indexedIterate object (JuliaLean.base.int.lit .i64 2) (some state)
      let b ← transformGetfield ops second (JuliaLean.base.int.lit .i64 1)
      pure (firstView a, secondView b)

/-- The generic _xfadjoint method fixes neither the iterator type nor the returned wrapper type. Both selected calls are unrestricted dispatch leaves. Known/raw result destructuring remains the actual indexed_iterate/Core-field algorithm, with all errors and state retained. This interface models this generic own body, not the constructed-Generator specialization used by blocked row40.
Julia source: base/reduce.jl:146-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:146-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
-- /Source
structure GenericAdjointOps (W E V : Type) where
  raw : TransformRawOps W E V
  unwrap : V → FoldEval W (FoldError E) (TransformPairResult V V V)
  apply : V → V → FoldEval W (FoldError E) V

/-- Call the selected unwrap on the original iterator, destructure its actual return, invoke the observed wrapper with the original operator, then pair its actual result with the observed iterator. No callee correctness, success, or termination law is imposed.
Julia source: base/reduce.jl:146-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:146-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _xfadjoint(op, itr)
--     itr′, wrap = _xfadjoint_unwrap(itr)
--     wrap(op), itr′
-- end
-- /Source
def xfadjoint {W E V : Type} (ops : GenericAdjointOps W E V) (op itr : V) :
    FoldEval W (FoldError E) (V × V) := do
  let (itr', wrap) ← destructureTransformPair ops.raw (← ops.unwrap itr)
  let op' ← ops.apply wrap op
  pure (op', itr')
/-- The exact Base.identity singleton returned by the generic fallback. No invocation occurs in this method.
Julia source: base/reduce.jl:151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _xfadjoint_unwrap(itr) = itr, identity
-- /Source
inductive TransformIdentity where
  | identity

/-- The generic fallback own body returns its original object and the identity singleton without inspecting the object or invoking any callable. Its domain includes all object types, even ones selecting another overload in ordinary dispatch.
Julia source: base/reduce.jl:151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _xfadjoint_unwrap(itr) = itr, identity
-- /Source
def xfadjointUnwrapFallback {Object : Type} (itr : Object) : Object × TransformIdentity :=
  (itr, .identity)

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Selected mapfoldl_impl dispatch on the unfixed callable, operator, iterator
and initial-value types. This is a distinct selected callee, not a parameter
for the public method body. It may return any result, mutate, fail or diverge.
Julia source: base/reduce.jl:173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapfoldl(f, op, itr; init=_InitialValue()) = mapfoldl_impl(f, op, init, itr)
-- /Source
structure PublicMapfoldOps (m : Type → Type) (F Op I V Result : Type) where
  impl : F → Op → FoldInit V → I → m Result

/-- Public mapfoldl preserves every argument and forwards one initial value.
Omission selects the actual _InitialValue singleton; a supplied value, including
an explicitly supplied sentinel, is retained. The selected implementation is
called once, with no added check, conversion, fallback or result interpretation.
Julia source: base/reduce.jl:173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapfoldl(f, op, itr; init=_InitialValue()) = mapfoldl_impl(f, op, init, itr)
-- /Source
def mapfoldlPublic {m : Type → Type} {F Op I V Result : Type}
    (ops : PublicMapfoldOps m F Op I V Result) (f : F) (op : Op) (itr : I)
    (init : Option (FoldInit V) := none) : m Result :=
  ops.impl f op (init.getD .initial) itr

/-- Selected public mapfoldl dispatch with its actual identity singleton and
the complete keyword object. Kw denotes an already-constructed Julia keyword
object (Pairs over a NamedTuple), including empty, with arbitrary heterogeneous values and aliases.
No list or unbounded surrogate for keyword storage is introduced or inspected.
Julia source: base/reduce.jl:196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- foldl(op, itr; kw...) = mapfoldl(identity, op, itr; kw...)
-- /Source
structure PublicFoldOps (m : Type → Type) (Op I Kw Result : Type) where
  mapfoldl : IdentityFn → Op → I → Kw → m Result

/-- Public foldl passes the actual identity singleton and all keyword arguments
unchanged to selected mapfoldl. Unsupported-keyword errors, mutations and
divergence remain those of the selected call. The source body does not inspect
or reinterpret the keyword object.
Julia source: base/reduce.jl:196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- foldl(op, itr; kw...) = mapfoldl(identity, op, itr; kw...)
-- /Source
def foldlPublic {m : Type → Type} {Op I Kw Result : Type}
    (ops : PublicFoldOps m Op I Kw Result) (op : Op) (itr : I) (kw : Kw) : m Result :=
  ops.mapfoldl .identity op itr kw

end JuliaLean.base.reduce.Models2Group7



namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- The selected Iterators.reverse call for an iterator whose type the generic source method does not fix. It can mutate, throw, diverge or return an arbitrary iterator object. Julia source: base/reduce.jl:206. -/
-- Source: base/reduce.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _reverse_iter(itr) = Iterators.reverse(itr)
-- /Source
structure ReverseIterOps (m : Type → Type) (I R : Type) where
  reverse : I → m R

/-- Generic _reverse_iter forwards the original iterator exactly once to selected Iterators.reverse, retaining its effects and result. Julia source: base/reduce.jl:206. -/
-- Source: base/reduce.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _reverse_iter(itr) = Iterators.reverse(itr)
-- /Source
def reverseIterDefault {m : Type → Type} {I R : Type}
    (ops : ReverseIterOps m I R) (itr : I) : m R :=
  ops.reverse itr

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- FlipArgs immutable storage preserves any callable, type object or other
value. A non-callable value fails at invocation, not at construction.
Julia source: base/reduce.jl:209-211. -/
-- Source: base/reduce.jl:209-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct FlipArgs{F}
--     f::F
-- end
-- /Source
structure FlipAdapter (F : Type) where
  f : F

/-- The known stored f property and genuinely selected custom getproperty
routes are explicit. The call is selected on the arbitrary returned callable;
heterogeneous argument/result types and all effects remain unrestricted.
Julia source: base/reduce.jl:213. -/
-- Source: base/reduce.jl:213-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (f::FlipArgs)(x, y) = f.f(y, x)
-- /Source
structure FlipAdapterOps (m : Type → Type) (F X Y Result : Type) where
  fProperty : PropertySelection m (FlipAdapter F) F := .stored
  call : F → Y → X → m Result

/-- Read f once, then invoke that exact callable with y followed by x.
Getter errors precede invocation; invocation mutations/errors/divergence are
retained without a conversion or any interpretation of the returned value.
Julia source: base/reduce.jl:213. -/
-- Source: base/reduce.jl:213-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (f::FlipArgs)(x, y) = f.f(y, x)
-- /Source
def flipApply {m : Type → Type} [Monad m] {F X Y Result : Type}
    (ops : FlipAdapterOps m F X Y Result) (wrapper : FlipAdapter F)
    (x : X) (y : Y) : m Result := do
  let f ← readSelectedProperty ops.fProperty FlipAdapter.f wrapper
  ops.call f y x

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Public mapfoldr preserves every argument and forwards one initial value.
Omission selects the actual _InitialValue singleton; a supplied value, including
an explicitly supplied sentinel, is retained. The selected implementation is
called once, with no added check, conversion, fallback or result interpretation.
Julia source: base/reduce.jl:222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapfoldr(f::F, op::F2, itr; init=_InitialValue()) where {F,F2} = mapfoldr_impl(f, op, init, itr)
-- /Source
def mapfoldrPublic {m : Type → Type} {F Op I V Result : Type}
    (ops : PublicMapfoldOps m F Op I V Result) (f : F) (op : Op) (itr : I)
    (init : Option (FoldInit V) := none) : m Result :=
  ops.impl f op (init.getD .initial) itr

/-- Selected public mapfoldr dispatch with its actual identity singleton and
the complete keyword object. Kw denotes an already-constructed Julia keyword
object (Pairs over a NamedTuple), including empty, with arbitrary heterogeneous values and aliases.
No list or unbounded surrogate for keyword storage is introduced or inspected.
Julia source: base/reduce.jl:241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- foldr(op::F, itr; kw...) where {F} = mapfoldr(identity, op, itr; kw...)
-- /Source
structure PublicFoldrOps (m : Type → Type) (Op I Kw Result : Type) where
  mapfoldr : IdentityFn → Op → I → Kw → m Result

/-- Public foldr passes the actual identity singleton and all keyword arguments
unchanged to selected mapfoldr. Unsupported-keyword errors, mutations and
divergence remain those of the selected call. The source body does not inspect
or reinterpret the keyword object.
Julia source: base/reduce.jl:241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- foldr(op::F, itr; kw...) where {F} = mapfoldr(identity, op, itr; kw...)
-- /Source
def foldrPublic {m : Type → Type} {Op I Kw Result : Type}
    (ops : PublicFoldrOps m Op I Kw Result) (op : Op) (itr : I) (kw : Kw) : m Result :=
  ops.mapfoldr .identity op itr kw

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean


/-- Dynamic values distinguish native Int64, every other Integer (including
Bool and arbitrary user integers), and all non-Integer values. Tags are runtime
type representation, not assumptions about arithmetic closure. The payload
carrier can preserve every heterogeneous value and mutable object identity.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
inductive PairwiseValue (V : Type) where
  | native (value : JInt .i64)
  | integer (value : V)
  | other (value : V)
  deriving Repr, DecidableEq


/-- The runtime Integer type test used only when resolving a recursive method
call. The body itself does not add validation that Julia does not perform.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
def PairwiseValue.isInteger {V : Type} : PairwiseValue V → Bool
  | .native _ => true
  | .integer _ => true
  | .other _ => false


/-- The source Integer parameter domain. The sole proof is its explicit
Julia type annotation, not an arithmetic or indexing correctness law.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
abbrev PairwiseIndex (V : Type) := {value : PairwiseValue V // value.isInteger = true}


/-- The selected recursive call target. generic invokes the actual body below;
custom denotes only a genuinely different method; missing raises MethodError.
This distinguishes dispatch from a callback replacing this method recursion.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
inductive PairwiseTarget where
  | generic
  | custom
  | missing
  deriving Repr, DecidableEq


/-- Arbitrary callback exceptions coexist with the installed Julia MethodError
class and the concrete Core-field/condition errors. State survives exceptions;
none denotes divergence inside a call or an actual recursive/loop computation.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
abbrev PairwiseM (W E A : Type) := FoldEval W (FoldError (JlError ⊕ E)) A


/-- Only calls selected on types unfixed by this source method are parameters.
Integer input types and arithmetic intermediates are unrestricted; native
literal arguments use JInt64. getindex receives the actual array/index plus
the active inbounds context (true), not an added bounds check. SIMD calls are
open dispatch on the Colon result; the macro body is implemented below.
fields is the pure current-storage representation for concrete Core reads.
The pure target field represents runtime method selection, not execution.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
structure PairwiseOps (W E V F O A : Type) where
  equal : PairwiseValue V → PairwiseValue V → PairwiseM W E (Bool ⊕ PairwiseValue V)
  less : PairwiseValue V → PairwiseValue V → PairwiseM W E (Bool ⊕ PairwiseValue V)
  subtract : PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  add : PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  addLiteral : PairwiseValue V → JInt .i64 → PairwiseM W E (PairwiseValue V)
  shiftRight : PairwiseValue V → JInt .i64 → PairwiseM W E (PairwiseValue V)
  zero : PairwiseValue V → PairwiseM W E (PairwiseValue V)
  colon : PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  simdOuterRange : PairwiseValue V → PairwiseM W E (PairwiseValue V)
  simdInnerLength : PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  simdIndex : PairwiseValue V → PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  iterate : PairwiseValue V → Option (PairwiseValue V) → PairwiseM W E (Option (PairwiseValue V))
  fields : W → PairwiseValue V → FoldObjectView (PairwiseValue V)
  getindex : A → PairwiseValue V → Bool → PairwiseM W E (PairwiseValue V)
  map : F → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  reduce : O → PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  first : F → O → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  target : F → O → A → PairwiseValue V → PairwiseValue V → PairwiseValue V → PairwiseTarget
  custom : F → O → A → PairwiseValue V → PairwiseValue V → PairwiseValue V → PairwiseM W E (PairwiseValue V)
  blockSize : F → O → PairwiseM W E (PairwiseValue V)


/-- Julia condition checking accepts exactly Bool and raises TypeError for
every other value after retaining the effects of the condition expression.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
def pairwiseAssertBool {W E V : Type} (condition : Bool ⊕ PairwiseValue V) : PairwiseM W E Bool :=
  match JuliaLean.base.reduce.assertBool condition with
  | .ok value => pure value
  | .error _ => throw .typeError


/-- Core field extraction for the outer SIMD loop uses the already implemented
fixed primitive, not user getindex or indexed_iterate. Missing/undefined fields
and module integer accesses preserve their exact error class and current world.
Lowering: src/julia-syntax.scm:1888-1909,2070-2110 at the same pin.
Julia source: base/simdloop.jl:67-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/simdloop.jl:67-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
--     end
-- /Source
def pairwiseReadField {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (object : PairwiseValue V) (index : JInt .i64) : PairwiseM W E (PairwiseValue V) := do
  let world ← get
  match foldFieldRead (E := JlError ⊕ E) (ops.fields world object) index with
  | .ok value => pure value
  | .error error => throw error


/-- The actual SIMD inner while loop. Its comparison is checked as Bool,
the selected simd_index precedes the source inbounds array access, mapping
precedes reduction, and the native-one increment follows the whole body.
The fixed point preserves divergence; it imposes no laws on n or arithmetic.
Julia source: base/simdloop.jl:70-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/simdloop.jl:70-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
-- /Source
def pairwiseSimdInner {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (range outer n i value : PairwiseValue V) :
    PairwiseM W E (PairwiseValue V) := do
  if ← pairwiseAssertBool (← ops.less i n) then
    let index ← ops.simdIndex range outer i
    let element ← ops.getindex array index true
    let mapped ← ops.map f element
    let nextValue ← ops.reduce op value mapped
    let nextIndex ← ops.addLiteral i (JuliaLean.base.int.lit .i64 1)
    pairwiseSimdInner ops f op array range outer n nextIndex nextValue
  else pure value
partial_fixpoint


/-- The actual SIMD outer for loop over selected simd_outer_range. Both Core
fields are read before simd_inner_length. The first zero(n) belongs to the guard;
the second zero(n) initializes the inner index and is evaluated only on true.
Outer iteration state and shared reduction value survive every inner loop.
Julia source: base/simdloop.jl:67-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/simdloop.jl:67-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
--     end
-- /Source
def pairwiseSimdOuter {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (range outerRange value : PairwiseValue V)
    (state : Option (PairwiseValue V)) : PairwiseM W E (PairwiseValue V) := do
  match ← ops.iterate outerRange state with
  | none => pure value
  | some result =>
      let outer ← pairwiseReadField ops result (JuliaLean.base.int.lit .i64 1)
      let nextState ← pairwiseReadField ops result (JuliaLean.base.int.lit .i64 2)
      let n ← ops.simdInnerLength range outer
      let firstZero ← ops.zero n
      let nonempty ← pairwiseAssertBool (← ops.less firstZero n)
      let nextValue ← if nonempty then do
        let initialIndex ← ops.zero n
        pairwiseSimdInner ops f op array range outer n initialIndex value
      else pure value
      pairwiseSimdOuter ops f op array range outerRange nextValue (some nextState)
partial_fixpoint


/-- Evaluate the selected outer-range function once, then execute the real
expanded loops. The source Colon expression is evaluated before this helper.
Julia source: base/simdloop.jl:67-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/simdloop.jl:67-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
--     end
-- /Source
def pairwiseSimd {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (range value : PairwiseValue V) :
    PairwiseM W E (PairwiseValue V) := do
  let outerRange ← ops.simdOuterRange range
  pairwiseSimdOuter ops f op array range outerRange value none


/-- Full generic mapreduce_impl with runtime redispatch on recursive calls.
At entry, false means this exact source method has already been selected.
At recursive/default calls, true resolves the target: the generic branch
executes this same body; only a different selected method uses custom.
A generic target requires Integer indices and native-Int block size; otherwise
the call has no matching generic method. No check is inserted into the body.
Sequential reads precede both mappings. The midpoint is first + ((last-first) >> 1):
shifts bind more tightly than addition (manual/mathematical-operations.md:481-484).
Left recursion completes before mid+1/right recursion. Arithmetic can change
types, wrap, throw or diverge; the fixed point makes no termination assumption.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
def pairwiseGo {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (redispatch : Bool) (f : F) (op : O) (array : A)
    (first last block : PairwiseValue V) : PairwiseM W E (PairwiseValue V) := do
  if redispatch then
    match ops.target f op array first last block with
    | .custom => ops.custom f op array first last block
    | .missing => throw (.dispatch (.inl (.methodError "mapreduce_impl")))
    | .generic =>
      match block with
      | .native _ =>
          if first.isInteger && last.isInteger then
            pairwiseGo ops false f op array first last block
          else throw (.dispatch (.inl (.methodError "mapreduce_impl")))
      | _ => throw (.dispatch (.inl (.methodError "mapreduce_impl")))
  else
    if ← pairwiseAssertBool (← ops.equal first last) then
      let element ← ops.getindex array first true
      ops.first f op element
    else
      let distance ← ops.subtract last first
      if ← pairwiseAssertBool (← ops.less distance block) then
        let a1 ← ops.getindex array first true
        let secondIndex ← ops.addLiteral first (JuliaLean.base.int.lit .i64 1)
        let a2 ← ops.getindex array secondIndex true
        let mapped1 ← ops.map f a1
        let mapped2 ← ops.map f a2
        let value ← ops.reduce op mapped1 mapped2
        let begin ← ops.addLiteral first (JuliaLean.base.int.lit .i64 2)
        let range ← ops.colon begin last
        pairwiseSimd ops f op array range value
      else
        let distance ← ops.subtract last first
        let half ← ops.shiftRight distance (JuliaLean.base.int.lit .i64 1)
        let middle ← ops.add first half
        let left ← pairwiseGo ops true f op array first middle block
        let rightStart ← ops.addLiteral middle (JuliaLean.base.int.lit .i64 1)
        let right ← pairwiseGo ops true f op array rightStart last block
        ops.reduce op left right
partial_fixpoint


/-- Entry to the exact queued generic method. The subtype witnesses are only
its Integer annotations, and block is an actual native Julia Int. The source
assumes a valid nonempty index interval (reduce.jl:245-248) but performs no
validation; the model likewise adds none. User arrays/broadcasted objects
remain opaque A values and all selected effects are retained.
Julia source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:252-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted,
--                                   ifirst::Integer, ilast::Integer, blksize::Int)
--     if ifirst == ilast
--         @inbounds a1 = A[ifirst]
--         return mapreduce_first(f, op, a1)
--     elseif ilast - ifirst < blksize
--         # sequential portion
--         @inbounds a1 = A[ifirst]
--         @inbounds a2 = A[ifirst+1]
--         v = op(f(a1), f(a2))
--         @simd for i = ifirst + 2 : ilast
--             @inbounds ai = A[i]
--             v = op(v, f(ai))
--         end
--         return v
--     else
--         # pairwise portion
--         imid = ifirst + (ilast - ifirst) >> 1
--         v1 = mapreduce_impl(f, op, A, ifirst, imid, blksize)
--         v2 = mapreduce_impl(f, op, A, imid+1, ilast, blksize)
--         return op(v1, v2)
--     end
-- end
-- /Source
def mapreduceImpl {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (first last : PairwiseIndex V) (block : JInt .i64) :
    PairwiseM W E (PairwiseValue V) :=
  pairwiseGo ops false f op array first.val last.val (.native block)


/-- The default wrapper calls selected pairwise_blocksize once, then performs
the actual six-argument dispatch with that exact result. A custom block-size
method can return any type; it may select a different method or cause MethodError.
No callback replaces the generic six-argument method when that method is selected.
Julia source: base/reduce.jl:276-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:276-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted, ifirst::Integer, ilast::Integer) =
--     mapreduce_impl(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
-- /Source
def mapreduceImplDefault {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (first last : PairwiseIndex V) :
    PairwiseM W E (PairwiseValue V) := do
  let block ← ops.blockSize f op
  pairwiseGo ops true f op array first.val last.val block


end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Selected mapfoldl dispatch on unfixed callable, operator, iterator and keyword types. Kw is the complete already-constructed Julia keyword object (Pairs over a NamedTuple); its values and aliases are not interpreted.
Julia source: base/reduce.jl:306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, itr; kw...) = mapfoldl(f, op, itr; kw...)
-- /Source
structure PublicMapreduceOps (m : Type → Type) (F Op I Kw R : Type) where
  mapfoldl : F → Op → I → Kw → m R

/-- The public one-iterator wrapper makes exactly the selected mapfoldl call, retaining all argument objects and keyword contents. Errors, state changes and divergence belong to that unrestricted selected call.
Julia source: base/reduce.jl:306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, itr; kw...) = mapfoldl(f, op, itr; kw...)
-- /Source
def mapreducePublic {m : Type → Type} {F Op I Kw R : Type}
    (ops : PublicMapreduceOps m F Op I Kw R) (f : F) (op : Op) (itr : I) (kw : Kw) : m R :=
  ops.mapfoldl f op itr kw

/-- Selected constructor and reduction dispatch on types the source does not fix. Tail denotes the machine-valid tuple of additional positional arguments, including empty; Kw denotes the keyword iterator over a NamedTuple. Generator dispatch is open on F/I/Tail: this leaf includes genuinely selected constructors, possibly returning an arbitrary G, and does not replace iteration or any body defined here.
Julia source: base/reduce.jl:307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, itr, itrs...; kw...) = reduce(op, Generator(f, itr, itrs...); kw...)
-- /Source
structure PublicMultiMapreduceOps (m : Type → Type) (F Op I Tail Kw G R : Type) where
  generator : F → I → Tail → m G
  reduce : Op → G → Kw → m R

/-- Construct the selected generator using every positional iterator, then pass its actual result to selected reduce with the original operator and complete keyword object. No iterator is materialized, no purity or successful-constructor law is imposed, and the reduction is suppressed on constructor failure or divergence.
Julia source: base/reduce.jl:307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, itr, itrs...; kw...) = reduce(op, Generator(f, itr, itrs...); kw...)
-- /Source
def mapreduceMultiPublic {m : Type → Type} [Monad m] {F Op I Tail Kw G R : Type}
    (ops : PublicMultiMapreduceOps m F Op I Tail Kw G R)
    (f : F) (op : Op) (itr : I) (itrs : Tail) (kw : Kw) : m R := do
  let generated ← ops.generator f itr itrs
  ops.reduce op generated kw

/-- The default internal block-size literal is a native signed Int64 in the supplied runtime. Callable and operator values are unrestricted and unused.
Julia source: base/reduce.jl:311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pairwise_blocksize(f, op) = 1024
-- /Source
def pairwiseBlocksize {F Op : Type} (_f : F) (_op : Op) : JInt .i64 :=
  JuliaLean.base.int.lit .i64 1024

/-- The abs2/plus specialization returns its native signed Int64 literal. Existing singleton tags represent the exact source callable identities.
Julia source: base/reduce.jl:314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pairwise_blocksize(::typeof(abs2), ::typeof(+)) = 4096
-- /Source
def pairwiseBlocksizeAbs2Plus (_f : Abs2Function) (_op : PlusFunction) : JInt .i64 :=
  JuliaLean.base.int.lit .i64 4096

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- The generic empty fallback accepts arbitrary operator and type objects, including non-callable operators. It raises the installed ArgumentError without inspecting either argument.
Julia source: base/reduce.jl:319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(f, T) = _empty_reduce_error()
-- /Source
def emptyFallback {F Ty R : Type} (_f : F) (_T : Ty) : Jl R :=
  JuliaLean.base.reduce._empty_reduce_error

/-- All three argument domains are unrestricted. The known zero-argument error helper is reused directly, with no selected dispatch or callback.
Julia source: base/reduce.jl:320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(f, op, T) = _empty_reduce_error()
-- /Source
def mapemptyFallback {F Op Ty R : Type} (_f : F) (_op : Op) (_T : Ty) : Jl R :=
  JuliaLean.base.reduce._empty_reduce_error

/-- The Union{} specialization accepts every operator and machine-valid extra-argument tuple. The exact Union{} dispatch tag is erased because the body never reads it.
Julia source: base/reduce.jl:321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(f, ::Type{Union{}}, splat...) = _empty_reduce_error()
-- /Source
def emptyUnion {F Tail R : Type} (_f : F) (_tail : Tail) : Jl R :=
  JuliaLean.base.reduce._empty_reduce_error

/-- The Union{} map-reduction specialization retains arbitrary callable/operator/extra-argument domains and raises the same concrete error before making any call.
Julia source: base/reduce.jl:322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(f, op, ::Type{Union{}}, splat...) = _empty_reduce_error()
-- /Source
def mapemptyUnion {F Op Tail R : Type} (_f : F) (_op : Op) (_tail : Tail) : Jl R :=
  JuliaLean.base.reduce._empty_reduce_error

/-- Exact callable singleton identities used by the empty arithmetic forwarding methods.
Julia source: base/reduce.jl:342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:342-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(+), ::Type{T}) where {T} = zero(T)
-- reduce_empty(::typeof(+), ::Type{Bool}) = zero(Int)
-- reduce_empty(::typeof(*), ::Type{T}) where {T} = one(T)
-- /Source
inductive EmptyArithmetic where
  | plus
  | times
  deriving DecidableEq

/-- Selected zero/one/reduce_empty dispatch on the unfixed type object. Any result type, error, mutation and divergence is retained without laws.
Julia source: base/reduce.jl:342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:342-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(+), ::Type{T}) where {T} = zero(T)
-- reduce_empty(::typeof(+), ::Type{Bool}) = zero(Int)
-- reduce_empty(::typeof(*), ::Type{T}) where {T} = one(T)
-- reduce_empty(::typeof(*), ::Type{<:AbstractChar}) = ""
-- reduce_empty(::typeof(&), ::Type{Bool}) = true
-- reduce_empty(::typeof(|), ::Type{Bool}) = false
-- reduce_empty(::typeof(and_all), ::Type{T}) where {T} = true
-- reduce_empty(::typeof(or_any), ::Type{T}) where {T} = false
-- 
-- reduce_empty(::typeof(add_sum), ::Type{T}) where {T} = reduce_empty(+, T)
-- reduce_empty(::typeof(add_sum), ::Type{T}) where {T<:BitSignedSmall}  = zero(Int)
-- reduce_empty(::typeof(add_sum), ::Type{T}) where {T<:BitUnsignedSmall} = zero(UInt)
-- reduce_empty(::typeof(mul_prod), ::Type{T}) where {T} = reduce_empty(*, T)
-- reduce_empty(::typeof(mul_prod), ::Type{T}) where {T<:BitSignedSmall}  = one(Int)
-- reduce_empty(::typeof(mul_prod), ::Type{T}) where {T<:BitUnsignedSmall} = one(UInt)
-- /Source
structure EmptyScalarOps (m : Type → Type) (Ty R : Type) where
  zero : Ty → m R
  one : Ty → m R
  reduceEmpty : EmptyArithmetic → Ty → m R

/-- The plus empty method calls the zero method selected by T once. T is not restricted to native numeric types.
Julia source: base/reduce.jl:342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:342-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(+), ::Type{T}) where {T} = zero(T)
-- /Source
def emptyPlus {m : Type → Type} {Ty R : Type}
    (ops : EmptyScalarOps m Ty R) (T : Ty) : m R := ops.zero T

/-- Concrete native zero uses the installed zero(Type) body and integer conversion. The callee supplies the fixed literal zero; Lean Int here is the installed literal interface, never a variable machine arithmetic value.
Julia source: base/number.jl:364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zero(::Type{T}) where {T<:Number} = convert(T,0)
-- /Source
def emptyNativeZero (ty : IntTy) : Jl (JInt ty) :=
  JuliaLean.base.number.zeroType
    (fun (_target : IntTy) (literal : Int) =>
      JuliaLean.base.int.convert ty (JuliaLean.base.int.lit .i64 literal)) ty

/-- Concrete native one uses the installed one(Type) body and integer conversion. Its only literal is the exact native Int value one; UInt conversion is the installed concrete callee.
Julia source: base/number.jl:405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- /Source
def emptyNativeOne (ty : IntTy) : Jl (JInt ty) :=
  JuliaLean.base.number.oneType
    (fun (_target : IntTy) (literal : Int) =>
      JuliaLean.base.int.convert ty (JuliaLean.base.int.lit .i64 literal)) ty

/-- The Bool plus method returns native Int zero, through the concrete installed zero and conversion path.
Julia source: base/reduce.jl:343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(+), ::Type{Bool}) = zero(Int)
-- /Source
def emptyPlusBool : Jl (JInt .i64) := emptyNativeZero .i64

/-- The multiplication empty method invokes the one method selected by arbitrary T, with all effects and outcomes retained.
Julia source: base/reduce.jl:344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(*), ::Type{T}) where {T} = one(T)
-- /Source
def emptyTimes {m : Type → Type} {Ty R : Type}
    (ops : EmptyScalarOps m Ty R) (T : Ty) : m R := ops.one T

/-- The generic add_sum method forwards the exact plus singleton and original type object to selected reduce_empty.
Julia source: base/reduce.jl:351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(add_sum), ::Type{T}) where {T} = reduce_empty(+, T)
-- /Source
def emptyAddSum {m : Type → Type} {Ty R : Type}
    (ops : EmptyScalarOps m Ty R) (T : Ty) : m R := ops.reduceEmpty .plus T

/-- Every signed native small-bit type on the supplied 64-bit runtime. The width/signedness bounds are exact dispatch representation invariants.
Julia source: base/int.jl:22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/int.jl:22-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- /Source
abbrev SmallSignedType := { ty : IntTy // ty.bits < 64 ∧ ty.signed = true }

/-- Every unsigned native small-bit type on the supplied 64-bit runtime, without narrowing any value domain.
Julia source: base/int.jl:22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/int.jl:22-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
-- const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
-- const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)
-- /Source
abbrev SmallUnsignedType := { ty : IntTy // ty.bits < 64 ∧ ty.signed = false }

/-- Every small signed source type selects native Int zero; concrete zero/convert bodies are shared with the Bool specialization.
Julia source: base/reduce.jl:352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(add_sum), ::Type{T}) where {T<:BitSignedSmall}  = zero(Int)
-- /Source
def emptyAddSumSigned (_T : SmallSignedType) : Jl (JInt .i64) := emptyNativeZero .i64

/-- Every small unsigned source type selects native UInt zero, through the installed conversion path.
Julia source: base/reduce.jl:353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:353-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(add_sum), ::Type{T}) where {T<:BitUnsignedSmall} = zero(UInt)
-- /Source
def emptyAddSumUnsigned (_T : SmallUnsignedType) : Jl (JInt .u64) := emptyNativeZero .u64

/-- The generic mul_prod method passes the exact multiplication singleton and original T to selected reduce_empty.
Julia source: base/reduce.jl:354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:354-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(mul_prod), ::Type{T}) where {T} = reduce_empty(*, T)
-- /Source
def emptyMulProd {m : Type → Type} {Ty R : Type}
    (ops : EmptyScalarOps m Ty R) (T : Ty) : m R := ops.reduceEmpty .times T

/-- Every small signed source type returns native Int one via the concrete installed one/convert bodies.
Julia source: base/reduce.jl:355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(mul_prod), ::Type{T}) where {T<:BitSignedSmall}  = one(Int)
-- /Source
def emptyMulProdSigned (_T : SmallSignedType) : Jl (JInt .i64) := emptyNativeOne .i64

/-- Every small unsigned source type returns native UInt one, preserving its result type.
Julia source: base/reduce.jl:356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(::typeof(mul_prod), ::Type{T}) where {T<:BitUnsignedSmall} = one(UInt)
-- /Source
def emptyMulProdUnsigned (_T : SmallUnsignedType) : Jl (JInt .u64) := emptyNativeOne .u64

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- All values inhabit an unrestricted dynamic carrier V, allowing different runtime types and shared mutable references. Stored/custom getter routes are explicit. Every called reducer, map-empty, eltype, zero and absolute operation is selected on an unfixed input type and has no correctness law.
Julia source: base/reduce.jl:358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:358-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::BottomRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
-- reduce_empty(op::MappingRF, ::Type{T}) where {T} = mapreduce_empty(op.f, op.rf, T)
-- reduce_empty(op::FilteringRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
-- reduce_empty(op::FlatteningRF, ::Type{T}) where {T} = reduce_empty(op.rf, eltype(T))
-- reduce_empty(op::FlipArgs, ::Type{T}) where {T} = reduce_empty(op.f, T)
-- 
-- """
--     Base.mapreduce_empty(f, op, T)
-- 
-- The value to be returned when calling [`mapreduce`](@ref), [`mapfoldl`](@ref) or
-- [`mapfoldr`](@ref) with map `f` and reduction `op` over an empty array with element type
-- of `T`. See [`Base.reduce_empty`](@ref) for more information.
-- """
-- mapreduce_empty(::typeof(identity), op, T) = reduce_empty(op, T)
-- mapreduce_empty(::typeof(abs), op, T)      = abs(reduce_empty(op, T))
-- mapreduce_empty(::typeof(abs2), op, T)     = abs2(reduce_empty(op, T))
-- 
-- mapreduce_empty(f::typeof(abs),  ::typeof(max), T) = abs(zero(T))
-- mapreduce_empty(f::typeof(abs2), ::typeof(max), T) = abs2(zero(T))
-- /Source
structure EmptyAdapterOps (m : Type → Type) (V : Type) where
  bottomProperty : PropertySelection m (BottomAdapter V) V := .stored
  mappingFProperty : PropertySelection m (MappingRF V V) V := .stored
  mappingRfProperty : PropertySelection m (MappingRF V V) V := .stored
  filteringProperty : PropertySelection m (FilteringAdapter V V) V := .stored
  flatteningProperty : PropertySelection m (FlatteningAdapter V) V := .stored
  flipProperty : PropertySelection m (FlipAdapter V) V := .stored
  empty : V → V → m V
  mapEmpty : V → V → V → m V
  eltype : V → m V
  absolute : V → m V
  absolute2 : V → m V
  zero : V → m V

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::BottomRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
-- /Source
def emptyBottom {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : BottomAdapter V) (T : V) : m V := do
  let rf ← readSelectedProperty ops.bottomProperty BottomAdapter.rf op
  ops.empty rf T

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::MappingRF, ::Type{T}) where {T} = mapreduce_empty(op.f, op.rf, T)
-- /Source
def emptyMapping {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : MappingRF V V) (T : V) : m V := do
  let f ← readSelectedProperty ops.mappingFProperty MappingRF.f op
  let rf ← readSelectedProperty ops.mappingRfProperty MappingRF.rf op
  ops.mapEmpty f rf T

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::FilteringRF, ::Type{T}) where {T} = reduce_empty(op.rf, T)
-- /Source
def emptyFiltering {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : FilteringAdapter V V) (T : V) : m V := do
  let rf ← readSelectedProperty ops.filteringProperty FilteringAdapter.rf op
  ops.empty rf T

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::FlatteningRF, ::Type{T}) where {T} = reduce_empty(op.rf, eltype(T))
-- /Source
def emptyFlattening {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : FlatteningAdapter V) (T : V) : m V := do
  let rf ← readSelectedProperty ops.flatteningProperty FlatteningAdapter.rf op
  let elementType ← ops.eltype T
  ops.empty rf elementType

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:362-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty(op::FlipArgs, ::Type{T}) where {T} = reduce_empty(op.f, T)
-- /Source
def emptyFlip {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : FlipAdapter V) (T : V) : m V := do
  let f ← readSelectedProperty ops.flipProperty FlipAdapter.f op
  ops.empty f T

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(::typeof(identity), op, T) = reduce_empty(op, T)
-- /Source
def mapemptyIdentity {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : V) (T : V) : m V := do
  ops.empty op T

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(::typeof(abs), op, T)      = abs(reduce_empty(op, T))
-- /Source
def mapemptyAbsolute {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : V) (T : V) : m V := do
  let value ← ops.empty op T
  ops.absolute value

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:373-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(::typeof(abs2), op, T)     = abs2(reduce_empty(op, T))
-- /Source
def mapemptyAbsolute2 {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (op : V) (T : V) : m V := do
  let value ← ops.empty op T
  ops.absolute2 value

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:375-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(f::typeof(abs),  ::typeof(max), T) = abs(zero(T))
-- /Source
def mapemptyAbsoluteMax {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (T : V) : m V := do
  let value ← ops.zero T
  ops.absolute value

/-- Execute every selected property/callee in source order and preserve each actual result, exception and world update. The method has no success or purity assumption; dynamic type changes are retained in V.
Julia source: base/reduce.jl:376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:376-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty(f::typeof(abs2), ::typeof(max), T) = abs2(zero(T))
-- /Source
def mapemptyAbsolute2Max {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyAdapterOps m V) (T : V) : m V := do
  let value ← ops.zero T
  ops.absolute2 value

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Mapper type classification separates ordinary values and exact type objects; V is a universal value/reference carrier. No source value is omitted.
Julia source: base/reduce.jl:94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:94-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     MappingRF(f::F, rf::T) where {F,T} = new{F,T}(f, rf)
--     MappingRF(::Type{f}, rf::T) where {f,T} = new{Type{f},T}(f, rf)
-- /Source
inductive EmptyMapperArgument (V : Type) where
  | ordinary (f : V)
  | typeValue (T : V)

/-- Both known MappingRF parameter shapes and arbitrary selected constructor results are retained.
Julia source: base/reduce.jl:94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:94-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     MappingRF(f::F, rf::T) where {F,T} = new{F,T}(f, rf)
--     MappingRF(::Type{f}, rf::T) where {f,T} = new{Type{f},T}(f, rf)
-- /Source
inductive EmptyMappingValue (V : Type) where
  | known (typeSingleton : Bool) (fields : MappingRF V V)
  | custom (object : V)

/-- Use the installed ordinary/type-specialized immutable constructors, retaining exact f and rf objects.
Julia source: base/reduce.jl:94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:94-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     MappingRF(f::F, rf::T) where {F,T} = new{F,T}(f, rf)
--     MappingRF(::Type{f}, rf::T) where {f,T} = new{Type{f},T}(f, rf)
-- /Source
def emptyMappingConstructor {V : Type} (f : EmptyMapperArgument V) (op : V) : EmptyMappingValue V :=
  match f with
  | .ordinary value => .known false (mappingRF_constructor value op)
  | .typeValue value => .known true (mappingRF_type_constructor value op)

/-- Known Flatten storage has the original iterator in its it field; custom represents other selected construction results.
Julia source: base/iterators.jl:1261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:1261-1263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Flatten{I}
--     it::I
-- end
-- /Source
inductive EmptyFlattenValue (V : Type) where
  | known (it : V)
  | custom (object : V)

/-- Union{} is an exact singleton. Other denotes all other runtime type objects. Option around this type below represents whether the static type parameter is bound, independently of the bottom singleton itself.
Julia source: base/reduce.jl:391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:391-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline reduce_empty_iter(op, itr::Tuple{Vararg{T}}, ::HasEltype) where {T} =
--     reduce_empty(op, @isdefined(T) ? T : Union{})
-- /Source
inductive EmptyTypeToken (Other : Type) where
  | bottom
  | value (T : Other)

/-- All values, traits, eltype returns and iterator identities stay dynamic; selected calls may return arbitrary values, mutate, fail or diverge. Known MappingRF and Flatten constructors have actual branches. Pure selector fields describe method dispatch, not correctness laws.
Julia source: base/reduce.jl:379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:379-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty_iter(f::F, op::F2, itr, ItrEltype) where {F,F2} =
--     reduce_empty_iter(MappingRF(f, op), itr, ItrEltype)
-- 
-- @inline reduce_empty_iter(op, itr) = reduce_empty_iter(op, itr, IteratorEltype(itr))
-- @inline reduce_empty_iter(op::FlatteningRF, itr) = reduce_empty_iter(op.rf, Iterators.flatten(itr))
-- @inline reduce_empty_iter(op, itr, ::HasEltype) = reduce_empty(op, eltype(itr))
-- # a homogeneous tuple binds the element type as a static parameter, which stays
-- # precise for abstract `Tuple{Vararg{T}}` queries where `eltype` of the
-- # `@nospecialize`d tuple type does not (#61323). `T` is undefined only for the
-- # empty tuple (vacuous `Vararg` match), whose eltype is `Union{}`; the
-- # `@isdefined` guard keeps this method's intentional unbound sparam (see the
-- # `detect_unbound_args` allow-list in test/ambiguous.jl), like `_eltype_ntuple`.
-- @inline reduce_empty_iter(op, itr::Tuple{Vararg{T}}, ::HasEltype) where {T} =
--     reduce_empty(op, @isdefined(T) ? T : Union{})
-- reduce_empty_iter(op, itr, ::EltypeUnknown) = throw(ArgumentError("""
--     reducing over an empty collection of unknown element type is not allowed.
--     You may be able to prevent this error by supplying an `init` value to the reducer."""))
-- /Source
structure EmptyIteratorOps (m : Type → Type) (V : Type) where
  selectMapping : EmptyMapperArgument V → V → Bool := fun _ _ => false
  mapping : EmptyMapperArgument V → V → m (EmptyMappingValue V)
  emptyMapping : EmptyMappingValue V → V → V → m V
  iteratorEltype : V → m V
  emptyIter : V → V → V → m V
  flatteningProperty : PropertySelection m (FlatteningAdapter V) V := .stored
  selectFlatten : V → Bool := fun _ => false
  flatten : V → m (EmptyFlattenValue V)
  selectFlattenConstructor : V → Bool := fun _ => false
  flattenConstructor : V → m (EmptyFlattenValue V)
  emptyFlatten : V → EmptyFlattenValue V → m V
  eltype : V → m V
  empty : V → V → m V
  emptyTyped : V → EmptyTypeToken V → m V

/-- Construct MappingRF through the actual concrete constructor or genuinely selected alternative, then call reduce_empty_iter with the resulting object, original iterator and original trait.
Julia source: base/reduce.jl:379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:379-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_empty_iter(f::F, op::F2, itr, ItrEltype) where {F,F2} =
--     reduce_empty_iter(MappingRF(f, op), itr, ItrEltype)
-- /Source
def mapemptyIterator {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyIteratorOps m V) (f : EmptyMapperArgument V) (op itr trait : V) : m V := do
  let mapped ← if ops.selectMapping f op then ops.mapping f op else pure (emptyMappingConstructor f op)
  ops.emptyMapping mapped itr trait

/-- Obtain the selected IteratorEltype result, then forward that actual value with the original operator and iterator. Nonstandard trait results are not silently coerced.
Julia source: base/reduce.jl:382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline reduce_empty_iter(op, itr) = reduce_empty_iter(op, itr, IteratorEltype(itr))
-- /Source
def emptyIterator {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyIteratorOps m V) (op itr : V) : m V := do
  let trait ← ops.iteratorEltype itr
  ops.emptyIter op itr trait

/-- Execute the known flatten body by constructing Flatten with its original iterator, unless dispatch selects a genuinely different flatten or constructor method.
Julia source: base/iterators.jl:1291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:1291-1291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flatten(itr) = Flatten(itr)
-- /Source
def emptyFlattenConstructor {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyIteratorOps m V) (itr : V) : m (EmptyFlattenValue V) := do
  if ops.selectFlatten itr then ops.flatten itr
  else if ops.selectFlattenConstructor itr then ops.flattenConstructor itr
  else pure (.known itr)

/-- Read rf before flattening the original iterator; forward the actual flatten result to selected reduce_empty_iter. All selected getters, constructors and calls preserve source errors and effects.
Julia source: base/reduce.jl:383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline reduce_empty_iter(op::FlatteningRF, itr) = reduce_empty_iter(op.rf, Iterators.flatten(itr))
-- /Source
def emptyIteratorFlattening {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyIteratorOps m V) (op : FlatteningAdapter V) (itr : V) : m V := do
  let rf ← readSelectedProperty ops.flatteningProperty FlatteningAdapter.rf op
  let flattened ← emptyFlattenConstructor ops itr
  ops.emptyFlatten rf flattened

/-- HasEltype selects eltype on the original iterator, then passes the actual result to selected reduce_empty with the original operator. The callback can return a non-Type and produce downstream dispatch errors.
Julia source: base/reduce.jl:384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline reduce_empty_iter(op, itr, ::HasEltype) = reduce_empty(op, eltype(itr))
-- /Source
def emptyIteratorHasEltype {m : Type → Type} [Monad m] {V : Type}
    (ops : EmptyIteratorOps m V) (op itr : V) : m V := do
  let T ← ops.eltype itr
  ops.empty op T

/-- The iterator is an opaque machine-valid homogeneous Tuple. Its compiler-supplied static parameter is either bound to the exact type token or unbound (the empty tuple case). The body does not inspect the tuple or call eltype; unbound selects the concrete Union{} token.
Julia source: base/reduce.jl:391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:391-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline reduce_empty_iter(op, itr::Tuple{Vararg{T}}, ::HasEltype) where {T} =
--     reduce_empty(op, @isdefined(T) ? T : Union{})
-- /Source
def emptyIteratorTuple {m : Type → Type} {V : Type}
    (ops : EmptyIteratorOps m V) (op _itr : V) (staticType : Option (EmptyTypeToken V)) : m V :=
  ops.emptyTyped op (staticType.getD .bottom)

/-- The exact triple-quoted string has one newline after the first sentence, after Julia indentation removal. Neither operator nor iterator is inspected; the concrete ArgumentError is raised directly.
Julia source: base/reduce.jl:393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:393-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_empty_iter(op, itr, ::EltypeUnknown) = throw(ArgumentError("""
--     reducing over an empty collection of unknown element type is not allowed.
--     You may be able to prevent this error by supplying an `init` value to the reducer."""))
-- /Source
def emptyIteratorUnknown {Op I R : Type} (_op : Op) (_itr : I) : Jl R :=
  .error (.argumentError "reducing over an empty collection of unknown element type is not allowed.\nYou may be able to prevent this error by supplying an `init` value to the reducer.")

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- The Bool specialization calls the installed Bool-to-native-Int conversion. Both truth values return their concrete Int64 result.
Julia source: base/reduce.jl:412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(+), x::Bool) = Int(x)
-- /Source
def firstPlusBool (x : Bool) : JInt .i64 := JuliaLean.base.int.ofBool .i64 x

/-- String dispatch is selected on an unfixed AbstractChar subtype. Custom character identity, arbitrary results, effects and exceptions remain explicit.
Julia source: base/reduce.jl:413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(*), x::AbstractChar) = string(x)
-- /Source
structure FirstCharOps (m : Type → Type) (C R : Type) where
  string : C → m R

/-- Invoke selected string once on the original abstract-character value, with no purity or result-type law.
Julia source: base/reduce.jl:413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(*), x::AbstractChar) = string(x)
-- /Source
def firstTimesChar {m : Type → Type} {C R : Type}
    (ops : FirstCharOps m C R) (x : C) : m R := ops.string x

/-- Every small-bit width and value is represented. The installed concrete widening conversion preserves the value in the native signed/unsigned result type.
Julia source: base/reduce.jl:416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(add_sum), x::BitSignedSmall)   = Int(x)
-- /Source
def firstAddSumSigned (x : SmallSigned) : JInt .i64 :=
  JuliaLean.base.int.widenTo .i64 x.val.value

/-- Every small-bit width and value is represented. The installed concrete widening conversion preserves the value in the native signed/unsigned result type.
Julia source: base/reduce.jl:417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(add_sum), x::BitUnsignedSmall) = UInt(x)
-- /Source
def firstAddSumUnsigned (x : SmallUnsigned) : JInt .u64 :=
  JuliaLean.base.int.widenTo .u64 x.val.value

/-- Every small-bit width and value is represented. The installed concrete widening conversion preserves the value in the native signed/unsigned result type.
Julia source: base/reduce.jl:419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(mul_prod), x::BitSignedSmall)   = Int(x)
-- /Source
def firstMulProdSigned (x : SmallSigned) : JInt .i64 :=
  JuliaLean.base.int.widenTo .i64 x.val.value

/-- Every small-bit width and value is represented. The installed concrete widening conversion preserves the value in the native signed/unsigned result type.
Julia source: base/reduce.jl:420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(::typeof(mul_prod), x::BitUnsignedSmall) = UInt(x)
-- /Source
def firstMulProdUnsigned (x : SmallUnsigned) : JInt .u64 :=
  JuliaLean.base.int.widenTo .u64 x.val.value

/-- Selected f property access and reduce_first dispatch on arbitrary callable/input types. The known Base stored-field path remains explicit.
Julia source: base/reduce.jl:423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(op::FlipArgs, x) = reduce_first(op.f, x)
-- /Source
structure FlipFirstOps (m : Type → Type) (F X R : Type) where
  fProperty : PropertySelection m (FlipAdapter F) F := .stored
  first : F → X → m R

/-- Read selected f, then call reduce_first with that callable and the original input; getter failure/divergence suppresses invocation.
Julia source: base/reduce.jl:423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce_first(op::FlipArgs, x) = reduce_first(op.f, x)
-- /Source
def firstFlip {m : Type → Type} [Monad m] {F X R : Type}
    (ops : FlipFirstOps m F X R) (op : FlipAdapter F) (x : X) : m R := do
  let f ← readSelectedProperty ops.fProperty FlipAdapter.f op
  ops.first f x

/-- Both mapping and first-element dispatch are selected on unfixed types. M can represent every dynamic Julia value; no callee laws are assumed.
Julia source: base/reduce.jl:435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:435-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_first(f, op, x) = reduce_first(op, f(x))
-- /Source
structure MapreduceFirstOps (m : Type → Type) (F Op X M R : Type) where
  map : F → X → m M
  first : Op → M → m R

/-- Map once, then selected reduce_first receives the original operator and actual mapped result. Evaluation order, state, errors and divergence are retained.
Julia source: base/reduce.jl:435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:435-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_first(f, op, x) = reduce_first(op, f(x))
-- /Source
def mapreduceFirst {m : Type → Type} [Monad m] {F Op X M R : Type}
    (ops : MapreduceFirstOps m F Op X M R) (f : F) (op : Op) (x : X) : m R := do
  let mapped ← ops.map f x
  ops.first op mapped

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- IndexStyle and the subsequent distinct _mapreduce call are selected on unfixed array/trait types. Traits are arbitrary objects, and every call can mutate, throw or diverge. Julia source: base/reduce.jl:437-437. -/
-- Source: base/reduce.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mapreduce(f, op, A::AbstractArrayOrBroadcasted) = _mapreduce(f, op, IndexStyle(A), A)
-- /Source
structure ArrayMapreduceDispatchOps (m : Type → Type) (F O A Style Result : Type) where
  indexStyle : A → m Style
  reduce : F → O → Style → A → m Result

/-- Evaluate IndexStyle first, then forward its exact result with original f, op and array. No trait validation is added. Julia source: base/reduce.jl:437-437. -/
-- Source: base/reduce.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mapreduce(f, op, A::AbstractArrayOrBroadcasted) = _mapreduce(f, op, IndexStyle(A), A)
-- /Source
def mapreduceArrayDispatch {m : Type → Type} [Monad m] {F O A Style Result : Type}
    (ops : ArrayMapreduceDispatchOps m F O A Style Result) (f : F) (op : O) (array : A) : m Result := do
  let style ← ops.indexStyle array
  ops.reduce f op style array

/-- Native Int64 values remain exact. V represents every other dynamic Julia value and alias. No positivity, arithmetic closure, length or indexing law is imposed. Julia source: base/reduce.jl:439-460. -/
-- Source: base/reduce.jl:439-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f, op, ::IndexLinear, A::AbstractArrayOrBroadcasted)
--     inds = LinearIndices(A)
--     n = length(inds)
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     elseif n == 1
--         @inbounds a1 = A[first(inds)]
--         return mapreduce_first(f, op, a1)
--     elseif n < 16 # process short array here, avoid mapreduce_impl() compilation
--         @inbounds i = first(inds)
--         @inbounds a1 = A[i]
--         @inbounds a2 = A[i+=1]
--         s = op(f(a1), f(a2))
--         while i < last(inds)
--             @inbounds Ai = A[i+=1]
--             s = op(s, f(Ai))
--         end
--         return s
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
inductive LinearValue (V : Type) where
  | native (value : JInt .i64)
  | other (value : V)
  deriving Repr, DecidableEq

/-- Selected calls on unfixed array, indices, mapper/reducer and non-native types. C represents all non-Bool condition results. Bool context parameters record source inbounds context, not additional Julia arguments. I/T are arbitrary index/trait objects. Native arithmetic is closed concretely by helpers below. Julia source: base/reduce.jl:439-460. -/
-- Source: base/reduce.jl:439-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f, op, ::IndexLinear, A::AbstractArrayOrBroadcasted)
--     inds = LinearIndices(A)
--     n = length(inds)
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     elseif n == 1
--         @inbounds a1 = A[first(inds)]
--         return mapreduce_first(f, op, a1)
--     elseif n < 16 # process short array here, avoid mapreduce_impl() compilation
--         @inbounds i = first(inds)
--         @inbounds a1 = A[i]
--         @inbounds a2 = A[i+=1]
--         s = op(f(a1), f(a2))
--         while i < last(inds)
--             @inbounds Ai = A[i+=1]
--             s = op(s, f(Ai))
--         end
--         return s
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
structure LinearMapreduceOps (W E V C F O A I T : Type) where
  indices : A → FoldEval W (FoldError E) I
  length : I → FoldEval W (FoldError E) (LinearValue V)
  equalLiteral : V → JInt .i64 → FoldEval W (FoldError E) (Bool ⊕ C)
  lessLiteral : V → JInt .i64 → FoldEval W (FoldError E) (Bool ⊕ C)
  less : LinearValue V → LinearValue V → FoldEval W (FoldError E) (Bool ⊕ C)
  addLiteral : V → JInt .i64 → Bool → FoldEval W (FoldError E) (LinearValue V)
  firstIndex : I → Bool → FoldEval W (FoldError E) (LinearValue V)
  lastIndex : I → Bool → FoldEval W (FoldError E) (LinearValue V)
  getindex : A → LinearValue V → Bool → FoldEval W (FoldError E) (LinearValue V)
  iteratorEltype : A → FoldEval W (FoldError E) T
  empty : F → O → A → T → FoldEval W (FoldError E) (LinearValue V)
  single : F → O → LinearValue V → FoldEval W (FoldError E) (LinearValue V)
  map : F → LinearValue V → FoldEval W (FoldError E) (LinearValue V)
  reduce : O → LinearValue V → LinearValue V → FoldEval W (FoldError E) (LinearValue V)
  impl : F → O → A → LinearValue V → LinearValue V → FoldEval W (FoldError E) (LinearValue V)

/-- Reuse installed Bool assertion, throwing TypeError at the condition after retaining every preceding effect. Julia source: base/reduce.jl:442-452. -/
-- Source: base/reduce.jl:442-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     elseif n == 1
--         @inbounds a1 = A[first(inds)]
--         return mapreduce_first(f, op, a1)
--     elseif n < 16 # process short array here, avoid mapreduce_impl() compilation
--         @inbounds i = first(inds)
--         @inbounds a1 = A[i]
--         @inbounds a2 = A[i+=1]
--         s = op(f(a1), f(a2))
--         while i < last(inds)
-- /Source
def linearAssertBool {W E C : Type} (condition : Bool ⊕ C) : FoldEval W (FoldError E) Bool :=
  match JuliaLean.base.reduce.assertBool condition with
  | .ok value => pure value
  | .error _ => throw .typeError

/-- Native equality uses installed Base integer equality. Only non-native left operands reach selected dynamic dispatch, followed by Bool assertion. Julia source: base/reduce.jl:442-444. -/
-- Source: base/reduce.jl:442-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     elseif n == 1
-- /Source
def linearEqualLiteral {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) (value : LinearValue V) (literal : JInt .i64) :
    FoldEval W (FoldError E) Bool := do
  match value with
  | .native n => pure (JuliaLean.base.int.eq n literal)
  | .other other => linearAssertBool (← ops.equalLiteral other literal)

/-- Native n<16 uses installed integer comparison; other types select their own comparison and must return Bool. Julia source: base/reduce.jl:447-447. -/
-- Source: base/reduce.jl:447-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     elseif n < 16 # process short array here, avoid mapreduce_impl() compilation
-- /Source
def linearLessLiteral {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) (value : LinearValue V) (literal : JInt .i64) :
    FoldEval W (FoldError E) Bool := do
  match value with
  | .native n => pure (JuliaLean.base.int.lt n literal)
  | .other other => linearAssertBool (← ops.lessLiteral other literal)

/-- Native/native guard comparison uses installed signed comparison. Other pairs preserve selected dispatch and Bool checking. Julia source: base/reduce.jl:452-452. -/
-- Source: base/reduce.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         while i < last(inds)
-- /Source
def linearLess {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) (left right : LinearValue V) :
    FoldEval W (FoldError E) Bool := do
  match left, right with
  | .native x, .native y => pure (JuliaLean.base.int.lt x y)
  | _, _ => linearAssertBool (← ops.less left right)

/-- Source i+=1 preserves native wrapping via installed Int64 addition. Other arithmetic can change index type and retains the enclosing inbounds context. Julia source: base/reduce.jl:449-454. -/
-- Source: base/reduce.jl:449-454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         @inbounds a1 = A[i]
--         @inbounds a2 = A[i+=1]
--         s = op(f(a1), f(a2))
--         while i < last(inds)
--             @inbounds Ai = A[i+=1]
--             s = op(s, f(Ai))
-- /Source
def linearIncrement {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) (index : LinearValue V) :
    FoldEval W (FoldError E) (LinearValue V) := do
  match index with
  | .native n => pure (.native (JuliaLean.base.int.add n (JuliaLean.base.int.lit .i64 1)))
  | .other other => ops.addLiteral other (JuliaLean.base.int.lit .i64 1) true

/-- Actual while recursion re-evaluates last(inds) on every guard, then compares, increments, reads, maps and reduces in source order. No termination, monotonicity or length/index law is imposed. The fixed point includes divergent calls and loops. Julia source: base/reduce.jl:452-455. -/
-- Source: base/reduce.jl:452-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         while i < last(inds)
--             @inbounds Ai = A[i+=1]
--             s = op(s, f(Ai))
--         end
-- /Source
def mapreduceLinearWhile {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) (f : F) (op : O) (array : A)
    (indices : I) (index value : LinearValue V) : FoldEval W (FoldError E) (LinearValue V) := do
  let last ← ops.lastIndex indices false
  if ← linearLess ops index last then
    let index ← linearIncrement ops index
    let element ← ops.getindex array index true
    let mapped ← ops.map f element
    let value ← ops.reduce op value mapped
    mapreduceLinearWhile ops f op array indices index value
  else pure value
partial_fixpoint

/-- Full IndexLinear body, including non-native/negative/custom lengths and changing or nonstandard indices. Both initial reads precede both mappings. The large branch evaluates first before last. Native literals remain JInt64, with no added interval premise. Julia source: base/reduce.jl:439-460. -/
-- Source: base/reduce.jl:439-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f, op, ::IndexLinear, A::AbstractArrayOrBroadcasted)
--     inds = LinearIndices(A)
--     n = length(inds)
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     elseif n == 1
--         @inbounds a1 = A[first(inds)]
--         return mapreduce_first(f, op, a1)
--     elseif n < 16 # process short array here, avoid mapreduce_impl() compilation
--         @inbounds i = first(inds)
--         @inbounds a1 = A[i]
--         @inbounds a2 = A[i+=1]
--         s = op(f(a1), f(a2))
--         while i < last(inds)
--             @inbounds Ai = A[i+=1]
--             s = op(s, f(Ai))
--         end
--         return s
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def mapreduceLinear {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) (f : F) (op : O) (array : A) :
    FoldEval W (FoldError E) (LinearValue V) := do
  let indices ← ops.indices array
  let n ← ops.length indices
  if ← linearEqualLiteral ops n (JuliaLean.base.int.lit .i64 0) then
    let trait ← ops.iteratorEltype array
    ops.empty f op array trait
  else if ← linearEqualLiteral ops n (JuliaLean.base.int.lit .i64 1) then
    let index ← ops.firstIndex indices true
    let element ← ops.getindex array index true
    ops.single f op element
  else if ← linearLessLiteral ops n (JuliaLean.base.int.lit .i64 16) then
    let index ← ops.firstIndex indices true
    let a1 ← ops.getindex array index true
    let index ← linearIncrement ops index
    let a2 ← ops.getindex array index true
    let mapped1 ← ops.map f a1
    let mapped2 ← ops.map f a2
    let value ← ops.reduce op mapped1 mapped2
    mapreduceLinearWhile ops f op array indices index value
  else
    let first ← ops.firstIndex indices false
    let last ← ops.lastIndex indices false
    ops.impl f op array first last

/-- Selected mapreduce_first on an arbitrary Number subtype and mapper/operator. Numeric tokens retain custom fields and aliases. Julia source: base/reduce.jl:462-462. -/
-- Source: base/reduce.jl:462-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, a::Number) = mapreduce_first(f, op, a)
-- /Source
structure NumberMapreduceOps (m : Type → Type) (F O N Result : Type) where
  first : F → O → N → m Result

/-- Forward the original Number and mapper/operator once to selected mapreduce_first, with every effect preserved. Julia source: base/reduce.jl:462-462. -/
-- Source: base/reduce.jl:462-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce(f, op, a::Number) = mapreduce_first(f, op, a)
-- /Source
def mapreduceNumber {m : Type → Type} {F O N Result : Type}
    (ops : NumberMapreduceOps m F O N Result) (f : F) (op : O) (number : N) : m Result :=
  ops.first f op number

/-- Selected mapfoldl on an unfixed abstract array and callable types. The source passes no init keyword. Julia source: base/reduce.jl:464-464. -/
-- Source: base/reduce.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mapreduce(f, op, ::IndexCartesian, A::AbstractArrayOrBroadcasted) = mapfoldl(f, op, A)
-- /Source
structure CartesianMapreduceOps (m : Type → Type) (F O A Result : Type) where
  mapfoldl : F → O → A → m Result

/-- IndexCartesian forwards f, op and the original array exactly once to selected mapfoldl. Julia source: base/reduce.jl:464-464. -/
-- Source: base/reduce.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mapreduce(f, op, ::IndexCartesian, A::AbstractArrayOrBroadcasted) = mapfoldl(f, op, A)
-- /Source
def mapreduceCartesian {m : Type → Type} {F O A Result : Type}
    (ops : CartesianMapreduceOps m F O A Result) (f : F) (op : O) (array : A) : m Result :=
  ops.mapfoldl f op array

/-- Selected mapreduce retains actual identity and the complete keyword object (Pairs over a NamedTuple). Kw is an opaque already-constructed Julia object, including heterogeneous values, aliases and unsupported-keyword cases. Julia source: base/reduce.jl:501-501. -/
-- Source: base/reduce.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce(op, itr; kw...) = mapreduce(identity, op, itr; kw...)
-- /Source
structure PublicReduceOps (m : Type → Type) (O I Kw Result : Type) where
  mapreduce : IdentityFn → O → I → Kw → m Result

/-- Public reduce forwards actual identity and all positional/keyword objects unchanged at the sole selected call. Julia source: base/reduce.jl:501-501. -/
-- Source: base/reduce.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce(op, itr; kw...) = mapreduce(identity, op, itr; kw...)
-- /Source
def reducePublic {m : Type → Type} {O I Kw Result : Type}
    (ops : PublicReduceOps m O I Kw Result) (op : O) (itr : I) (kw : Kw) : m Result :=
  ops.mapreduce .identity op itr kw

/-- Return the original Number without invoking any operator, including non-callable objects. Reuse the baseline generic identity body reduce_first, which permits the full ignored-operator domain; baseline reduce_number fixes the unused argument to Reducer. Julia source: base/reduce.jl:503-503. -/
-- Source: base/reduce.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reduce(op, a::Number) = a  # Do we want this?
-- /Source
def reduceNumber {O N : Type} (op : O) (number : N) : N :=
  JuliaLean.base.reduce.reduce_first op number

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Exact reduction function singleton identities. Their bodies are not invoked by forwarding wrappers.
Julia source: base/reduce.jl:546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(f, a; kw...) = mapreduce(f, add_sum, a; kw...)
-- /Source
inductive ReductionSingleton where
  | addSum
  | mulProd
  | maximum
  | minimum
  | extremaRF
  deriving DecidableEq

/-- Selected public dispatch on unfixed callable/iterator/keyword types. Kw is the complete immutable keyword iterator (Pairs over a NamedTuple), including unsupported keywords and aliased values. Identity routes retain the exact singleton.
Julia source: base/reduce.jl:546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(f, a; kw...) = mapreduce(f, add_sum, a; kw...)
-- /Source
structure ReductionPublicOps (m : Type → Type) (F I Kw R : Type) where
  mapreduce : F → ReductionSingleton → I → Kw → m R
  mapreduceIdentity : IdentityFn → ReductionSingleton → I → Kw → m R
  sumIdentity : IdentityFn → I → Kw → m R
  extremaIdentity : IdentityFn → I → Kw → m R

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(f, a; kw...) = mapreduce(f, add_sum, a; kw...)
-- /Source
def sumMapped {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (f : F) (itr : I) (kw : Kw) : m R :=
  ops.mapreduce f .addSum itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a; kw...) = sum(identity, a; kw...)
-- /Source
def sumPublic {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (itr : I) (kw : Kw) : m R :=
  ops.sumIdentity .identity itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:602-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prod(f, a; kw...) = mapreduce(f, mul_prod, a; kw...)
-- /Source
def prodMapped {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (f : F) (itr : I) (kw : Kw) : m R :=
  ops.mapreduce f .mulProd itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prod(a; kw...) = mapreduce(identity, mul_prod, a; kw...)
-- /Source
def prodPublic {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (itr : I) (kw : Kw) : m R :=
  ops.mapreduceIdentity .identity .mulProd itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:659-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- maximum(f, a; kw...) = mapreduce(f, max, a; kw...)
-- /Source
def maximumMapped {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (f : F) (itr : I) (kw : Kw) : m R :=
  ops.mapreduce f .maximum itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:686-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- minimum(f, a; kw...) = mapreduce(f, min, a; kw...)
-- /Source
def minimumMapped {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (f : F) (itr : I) (kw : Kw) : m R :=
  ops.mapreduce f .minimum itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- maximum(a; kw...) = mapreduce(identity, max, a; kw...)
-- /Source
def maximumPublic {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (itr : I) (kw : Kw) : m R :=
  ops.mapreduceIdentity .identity .maximum itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:750-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- minimum(a; kw...) = mapreduce(identity, min, a; kw...)
-- /Source
def minimumPublic {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (itr : I) (kw : Kw) : m R :=
  ops.mapreduceIdentity .identity .minimum itr kw

/-- Forward the exact source callable identity, original iterator and complete keyword object to selected public dispatch. Arbitrary results, mutations, errors and divergence pass through unchanged.
Julia source: base/reduce.jl:779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- extrema(itr; kw...) = extrema(identity, itr; kw...)
-- /Source
def extremaPublic {m : Type → Type} {F I Kw R : Type}
    (ops : ReductionPublicOps m F I Kw R) (itr : I) (kw : Kw) : m R :=
  ops.extremaIdentity .identity itr kw

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean JuliaLean.BootCov

/-- Dynamic values reserve Symbols, native integers and known two-tuples for concrete storage/iteration; Atom contains all other values and mutable references. Symbol identities are interned names.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
abbrev KeywordValue (Atom : Type) := TupleFoldValue (String ⊕ Atom)

/-- The NamedTuple backing a keyword Pairs object has distinct names, fully initialized fields, and a native representable field count. valueType represents the actual Pairs value parameter type; its membership condition is a storage invariant, not a law imposed on any dispatch callee.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
structure BoolKeywordPacket (Atom : Type) where
  entries : List (String × KeywordValue Atom)
  unique : (entries.map Prod.fst).Nodup
  fits : entries.length ≤ IntTy.i64.max.toNat
  valueType : KeywordValue Atom → Bool
  storedTypes : ∀ entry ∈ entries, valueType entry.2 = true

/-- Core missing named fields raise FieldError; unknown index methods raise MethodError. User errors retain their distinct payload. Core bounds, undefined references and type assertions use FoldError.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
inductive KeywordFailure (E : Type) where
  | user (error : E)
  | methodError
  deriving Repr, DecidableEq

/-- The state/error transformer retains worlds on failure; Option none represents divergent calls.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
abbrev KeywordM (W E A : Type) := FoldEval W (FoldError (KeywordFailure E)) A

/-- Explicit method selection distinguishes the concrete default from a genuinely more specific Julia method. Default behavior is never delegated to the custom callback.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
inductive KeywordSelection (m : Type → Type) (Args R : Type) where
  | base
  | custom (call : Args → m R)

/-- Keys are either a concrete Tuple, with its kind tag checked as a representation invariant, every heterogeneous field and a native count, or an arbitrary object returned by a genuinely different selected keys method.
Julia source: base/iterators.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(v::Pairs) = getfield(v, :itr) === nothing ? keys(getfield(v, :data)) : getfield(v, :itr)
-- /Source
inductive KeywordKeys (Atom : Type) where
  | tuple (value : FoldTuple (String ⊕ Atom)) (kind : value.kind = .tuple)
  | custom (value : KeywordValue Atom)

/-- Selections retain specialized keyword methods when parameter types permit them. The base path implements every concrete Pairs/NamedTuple/Tuple call. Only iterateOther/getindexOther act on receiver or index types not fixed by that path. Empty tests observe only nothing-versus-other, so iteratePairs custom return payload is erased after the call; no observable payload is dropped. raw uses only indexedIterate and fields. count/reduce are selected on the unfixed AbstractArray type.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
structure BoolSumOps (W E Atom A R : Type) where
  empty : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom) JVal := .base
  donePairs : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom) JVal := .base
  keysPairs : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom) (KeywordKeys Atom) := .base
  keysNamedTuple : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom) (KeywordKeys Atom) := .base
  doneKeys : KeywordSelection (KeywordM W E) (KeywordKeys Atom) JVal := .base
  iteratePairs : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom) (Option Unit) := .base
  iterateKeys : KeywordSelection (KeywordM W E) (KeywordKeys Atom) (Option (FlattenTransformResult (KeywordValue Atom))) := .base
  iterateOther : KeywordValue Atom → KeywordM W E (Option (FlattenTransformResult (KeywordValue Atom)))
  keyTupleBinary : KeywordSelection (KeywordM W E) (FoldTuple (String ⊕ Atom) × JInt .i64)
    (Option (FlattenTransformResult (KeywordValue Atom))) := .base
  keyTupleLength : KeywordSelection (KeywordM W E) (FoldTuple (String ⊕ Atom)) (KeywordValue Atom) := .base
  keyTupleIndex : KeywordSelection (KeywordM W E) (FoldTuple (String ⊕ Atom) × JInt .i64) (KeywordValue Atom) := .base
  keyTupleCompare : KeywordValue Atom → KeywordValue Atom → KeywordM W E (Bool ⊕ KeywordValue Atom) :=
    fun _ _ => throw (.dispatch .methodError)
  pairsElement : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom × KeywordValue Atom) Unit := .base
  getindexNamedTuple : KeywordSelection (KeywordM W E) (BoolKeywordPacket Atom × KeywordValue Atom) (KeywordValue Atom) := .base
  getindexOther : BoolKeywordPacket Atom → KeywordValue Atom → KeywordM W E (KeywordValue Atom)
  raw : FlatteningAdapterOps W (KeywordFailure E) (KeywordValue Atom)
  count : A → KeywordM W E R
  reduce : ReductionSingleton → A → BoolKeywordPacket Atom → KeywordM W E R

/-- The keyword packet is a Pairs with data equal to its NamedTuple and itr equal to nothing. Default keys(Pairs) therefore reads data, then executes keys(NamedTuple), producing its actual name tuple. A selected override can return arbitrary keys and retain effects.
Julia source: base/iterators.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(v::Pairs) = getfield(v, :itr) === nothing ? keys(getfield(v, :data)) : getfield(v, :itr)
-- /Source
def boolKeywordKeys {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (kw : BoolKeywordPacket Atom) : KeywordM W E (KeywordKeys Atom) := do
  match ops.keysPairs with
  | .custom call => call kw
  | .base =>
    match ops.keysNamedTuple with
    | .custom call => call kw
    | .base =>
      pure (.tuple { kind := .tuple, values := kw.entries.map (fun x => .atom (.inl x.1)), fits := by simpa using kw.fits } rfl)

/-- Default isdone(Pairs) calls keys first and forwards its actual result to isdone. The known tuple fallback is the installed missing singleton; selected specialized methods retain arbitrary non-Bool answers and effects.
Julia source: base/iterators.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline isdone(v::Pairs, state...) = isdone(keys(v), state...)
-- /Source
def boolKeywordDone {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (kw : BoolKeywordPacket Atom) : KeywordM W E JVal := do
  match ops.donePairs with
  | .custom call => call kw
  | .base =>
    let keys ← boolKeywordKeys ops kw
    match ops.doneKeys with
    | .custom call => call keys
    | .base => JuliaLean.base.essentials.isdoneDefault keys

/-- Close the existing full concrete Tuple iterate body over keyword-name Tuple
storage. Exactly length, the nonnative upper comparison, and getindex can be
selected inside this body. Every other required TupleFullOps slot is unreachable
from tupleFullTupleIterate and is filled with an inert value; no source call is
replaced by those values. Default native comparison/indexing remain concrete.
Julia source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def boolKeywordTupleOps {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R) :
    TupleFullOps W (KeywordFailure E) (String ⊕ Atom) Unit :=
  { apply := fun _ acc _ => pure acc
    atomGetindex := fun _ _ => throw (.dispatch .methodError)
    nonNativeIterate := fun _ _ => throw (.dispatch .methodError)
    atomFields := fun world atom => ops.raw.fields world (.atom atom)
    selectedLength := fun tuple => match ops.keyTupleLength with
      | .base => none
      | .custom call => some (call tuple)
    compareLength := fun _ _ => throw (.dispatch .methodError)
    selectedTupleIndex := fun tuple index => match index, ops.keyTupleIndex with
      | .native i, .custom call => some (call (tuple, i))
      | _, _ => none
    lessEqual := ops.keyTupleCompare
    greater := fun _ _ => throw (.dispatch .methodError)
    addOne := fun _ => throw (.dispatch .methodError)
    equalLength := fun _ _ => throw (.dispatch .methodError)
    nonNativeTupleIndex := fun _ _ => throw (.dispatch .methodError)
    symbolView := fun atom => match atom with | .inl name => some name | .inr _ => none
    namedFieldNames := fun _ => ⟨[], by decide⟩
    colon := fun _ _ => throw (.dispatch .methodError)
    rangeIterate := fun _ _ => throw (.dispatch .methodError)
    otherIterate := fun _ _ => throw (.dispatch .methodError)
    customRest := fun _ _ => throw (.dispatch .methodError) }

/-- The Base unary keys-Tuple iterator supplies native one and redispatches the
binary method. Its selected result can be arbitrary; otherwise the installed
full Tuple body preserves interior length/getindex/comparison dispatch and
returns its actual known pair. The outer generic iterate selection is separate.
Julia source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def boolKeywordTupleIterate {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (tuple : FoldTuple (String ⊕ Atom)) : KeywordM W E (Option (FlattenTransformResult (KeywordValue Atom))) := do
  let first := JuliaLean.base.int.lit .i64 1
  match ops.keyTupleBinary with
  | .custom call => call (tuple, first)
  | .base =>
    match ← tupleFullTupleIterate (boolKeywordTupleOps ops) tuple first with
    | none => pure none
    | some (.pair x state) => pure (some (.pair x state))
    | some other => pure (some (.custom other))

/-- Default iteration of a concrete keys Tuple executes unary-to-binary redispatch with native one and the existing full concrete Tuple body. A genuine selected override or an arbitrary keys object retains full raw result shapes; nothing is distinguished without destructuring it.
Julia source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def boolKeywordIterateKeys {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (keys : KeywordKeys Atom) : KeywordM W E (Option (FlattenTransformResult (KeywordValue Atom))) := do
  match ops.iterateKeys with
  | .custom call => call keys
  | .base =>
    match keys with
    | .custom object => ops.iterateOther object
    | .tuple t _ => boolKeywordTupleIterate ops t

/-- Concrete NamedTuple Symbol getindex resolves its actual named field; absent names raise FieldError. Native getindex delegates to the concrete Core integer reader with actual stored fields. Other index types select their unrestricted method. Stored immutable values and aliases are returned unchanged.
Julia source: base/namedtuple.jl:165-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/namedtuple.jl:165-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(t::NamedTuple, i::Int) = getfield(t, i)
-- getindex(t::NamedTuple, i::Symbol) = getfield(t, i)
-- /Source
def boolKeywordGet {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (kw : BoolKeywordPacket Atom) (key : KeywordValue Atom) : KeywordM W E (KeywordValue Atom) := do
  match ops.getindexNamedTuple with
  | .custom call => call (kw, key)
  | .base =>
    match key with
    | .atom (.inl name) =>
      match kw.entries.find? (fun entry => entry.1 == name) with
      | some entry => pure entry.2
      | none => throw .fieldError
    | .native index =>
      liftExcept (foldFieldRead (E := KeywordFailure E) (.fields (kw.entries.map (fun x => some x.2))
        (by simpa using kw.fits)) index)
    | other => ops.getindexOther kw other

/-- The selected _pairs_elt call retains the original Pairs receiver and actual
key. Its default reads the NamedTuple value before the raw Pair field-type
assertions. A more specific selected method can return any object; isempty never
observes that object, so only its successful presence is represented by Unit.
Julia source: base/iterators.jl:298-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:298-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@eval @propagate_inbounds function _pairs_elt(p::Pairs{K, V}, idx) where {K, V}
--     return $(Expr(:new, :(Pair{K, V}), :idx, :(getfield(p, :data)[idx])))
-- end
-- /Source
def boolKeywordElement {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (kw : BoolKeywordPacket Atom) (key : KeywordValue Atom) : KeywordM W E Unit := do
  match ops.pairsElement with
  | .custom call => call (kw, key)
  | .base =>
    let value ← boolKeywordGet ops kw key
    match key with
    | .atom (.inl _) =>
      if kw.valueType value then pure () else throw .typeError
    | _ => throw .typeError

/-- Concrete Pairs iteration calls keys, then iterate, stops on nothing, and ordinarily destructures the returned object before the NamedTuple lookup. The actual generated Pair allocation checks Symbol key and the stored value-parameter type after lookup; it performs no converting constructor. The returned payload is unobserved by isempty and is erased only after these effects and failures.
Julia source: base/iterators.jl:298-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iterators.jl:298-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@eval @propagate_inbounds function _pairs_elt(p::Pairs{K, V}, idx) where {K, V}
--     return $(Expr(:new, :(Pair{K, V}), :idx, :(getfield(p, :data)[idx])))
-- end
-- 
-- @propagate_inbounds function iterate(p::Pairs{K, V}, state...) where {K, V}
--     x = iterate(keys(p), state...)
--     x === nothing && return x
--     idx, next = x
--     return (_pairs_elt(p, idx), next)
-- end
-- /Source
def boolKeywordIterate {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (kw : BoolKeywordPacket Atom) : KeywordM W E (Option Unit) := do
  match ops.iteratePairs with
  | .custom call => call kw
  | .base =>
    let keys ← boolKeywordKeys ops kw
    match ← boolKeywordIterateKeys ops keys with
    | none => pure none
    | some raw =>
      let (key, _state) ← flatteningDestructure ops.raw raw
      boolKeywordElement ops kw key
      pure (some ())

/-- The installed complete isempty boundary preserves the non-missing hint unchanged and only calls iteration for missing. The adapter erases the unused iterate payload while preserving nothing, state, errors, mutation and divergence. A genuinely selected isempty override is explicit.
Julia source: base/essentials.jl:1235-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1235-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isempty(itr)
--     d = isdone(itr)
--     d !== missing && return d
--     iterate(itr) === nothing
-- end
-- /Source
def boolKeywordEmpty {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (kw : BoolKeywordPacket Atom) : KeywordM W E JVal := do
  match ops.empty with
  | .custom call => call kw
  | .base =>
    JuliaLean.base.essentials.Models1Group18.isemptyAtBoundary
      { isdone := boolKeywordDone ops
        iterate := fun packet => do
          let result ← boolKeywordIterate ops packet
          pure (result.map fun _ => (JVal.nothing, ())) } kw

/-- The AbstractArray{Bool} wrapper evaluates real keyword emptiness first, asserts its actual answer is Bool, and makes exactly the selected count or reduce(add_sum) call. Every original array/keyword object is retained. No array shape, purity, indexing, termination or successful-callee law is assumed.
Julia source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:576-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(a::AbstractArray{Bool}; kw...) =
--     isempty(kw) ? count(a) : reduce(add_sum, a; kw...)
-- /Source
def sumBoolArray {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R)
    (a : A) (kw : BoolKeywordPacket Atom) : KeywordM W E R := do
  let hint ← boolKeywordEmpty ops kw
  let condition : Bool ⊕ JVal := match hint with | .bool b => .inl b | other => .inr other
  let empty ← liftExcept ((assertBool condition).mapError fun _ => (FoldError.typeError : FoldError (KeywordFailure E)))
  if empty then ops.count a else ops.reduce .addSum a kw

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- The full mapper argument domain separates arbitrary ordinary values from type objects, so the concrete type-specialized constructor keeps its Type{T} parameter identity.
Julia source: base/reduce.jl:812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:812-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # to avoid type-instability (#23618).
-- struct ExtremaMap{F} <: Function
--     f::F
-- end
-- ExtremaMap(::Type{T}) where {T} = ExtremaMap{Type{T}}(T)
-- /Source
inductive ExtremaArgument (F Ty : Type) where
  | value (f : F)
  | typeValue (T : Ty)

/-- Known immutable ExtremaMap storage is distinguished from genuinely selected alternative constructor results. Other can carry every other dynamic value and mutable reference.
Julia source: base/reduce.jl:812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:812-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # to avoid type-instability (#23618).
-- struct ExtremaMap{F} <: Function
--     f::F
-- end
-- ExtremaMap(::Type{T}) where {T} = ExtremaMap{Type{T}}(T)
-- /Source
inductive ExtremaConstructed (F Ty Other : Type) where
  | known (typeSingleton : Bool) (fields : ExtremaMap (ExtremaArgument F Ty))
  | custom (object : Other)

/-- Actual ordinary construction and installed Type{T} construction retain the same argument object, with exact parameter-shape metadata. No constructor callback replaces these known branches.
Julia source: base/reduce.jl:812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:812-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # to avoid type-instability (#23618).
-- struct ExtremaMap{F} <: Function
--     f::F
-- end
-- ExtremaMap(::Type{T}) where {T} = ExtremaMap{Type{T}}(T)
-- /Source
def makeExtremaMap {F Ty Other : Type} (f : ExtremaArgument F Ty) : ExtremaConstructed F Ty Other :=
  match f with
  | .value _ => .known false ⟨f⟩
  | .typeValue _ => .known true (JuliaLean.base.reduce.extremaMap_type f)

/-- Constructor selection can choose a genuinely different method on unfixed f types; otherwise makeExtremaMap implements the concrete constructors. The selected public reduction retains arbitrary output types, keywords, state and errors.
Julia source: base/reduce.jl:809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:809-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- extrema(f, itr; kw...) = mapreduce(ExtremaMap(f), _extrema_rf, itr; kw...)
-- /Source
structure ExtremaPublicOps (m : Type → Type) (F Ty Other I Kw R : Type) where
  customConstructor : ExtremaArgument F Ty → Bool := fun _ => false
  construct : ExtremaArgument F Ty → m (ExtremaConstructed F Ty Other)
  mapreduce : ExtremaConstructed F Ty Other → ReductionSingleton → I → Kw → m R

/-- Construct the actual ExtremaMap or selected alternative, then forward the observed result, exact _extrema_rf singleton, original iterator and keyword object. Constructor errors or divergence suppress reduction.
Julia source: base/reduce.jl:809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:809-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- extrema(f, itr; kw...) = mapreduce(ExtremaMap(f), _extrema_rf, itr; kw...)
-- /Source
def extremaMapped {m : Type → Type} [Monad m] {F Ty Other I Kw R : Type}
    (ops : ExtremaPublicOps m F Ty Other I Kw R) (f : ExtremaArgument F Ty)
    (itr : I) (kw : Kw) : m R := do
  let mapped ← if ops.customConstructor f then ops.construct f else pure (makeExtremaMap f)
  ops.mapreduce mapped .extremaRF itr kw

/-- Selected getter and invocation on arbitrary stored callable and input types. The concrete stored f projection is explicit and preserves all aliasing.
Julia source: base/reduce.jl:817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:817-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (f::ExtremaMap)(x) = (y = f.f(x); (y, y))
-- /Source
structure ExtremaMapOps (m : Type → Type) (F X Y : Type) where
  fProperty : PropertySelection m (ExtremaMap F) F := .stored
  apply : F → X → m Y

/-- Read f once and map x once, then construct a two-field tuple containing the same result reference twice. Arbitrary mutations/errors/divergence occur at their original points.
Julia source: base/reduce.jl:817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:817-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (f::ExtremaMap)(x) = (y = f.f(x); (y, y))
-- /Source
def extremaMapApply {m : Type → Type} [Monad m] {F X Y : Type}
    (ops : ExtremaMapOps m F X Y) (f : ExtremaMap F) (x : X) : m (Y × Y) := do
  let callable ← readSelectedProperty ops.fProperty ExtremaMap.f f
  let y ← ops.apply callable x
  pure (y, y)

/-- Min/max are selected on unfixed dynamic operand types and may change types, mutate, fail or diverge. A universal V carrier retains every intermediate value.
Julia source: base/reduce.jl:819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _extrema_rf((min1, max1), (min2, max2)) = (min(min1, min2), max(max1, max2))
-- /Source
structure ExtremaCompareOps (m : Type → Type) (V : Type) where
  minimum : V → V → m V
  maximum : V → V → m V

/-- Destructure the two source arguments in order using the already implemented full ordinary destructuring protocol. Known two-tuples use concrete Base indexed_iterate; arbitrary raw objects retain custom dispatch, malformed results and Core errors. Only indexedIterate/fields of pairOps are used. Then min executes before max, returning their actual results.
Julia source: base/reduce.jl:819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _extrema_rf((min1, max1), (min2, max2)) = (min(min1, min2), max(max1, max2))
-- /Source
def extremaReduce {W E V : Type} (pairOps : FlatteningAdapterOps W E V)
    (ops : ExtremaCompareOps (FoldEval W (FoldError E)) V)
    (left right : FlattenTransformResult V) : FoldEval W (FoldError E) (V × V) := do
  let (min1, max1) ← flatteningDestructure pairOps left
  let (min2, max2) ← flatteningDestructure pairOps right
  let lo ← ops.minimum min1 min2
  let hi ← ops.maximum max1 max2
  pure (lo, hi)

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Exact maximum/minimum function identities. In a dispatch record the tag selects which source function is called; it is not an additional Julia positional argument.
Julia source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmax(f, domain) = _findmax(f, domain, :)
-- /Source
inductive FindDirection where
  | maximum
  | minimum
  deriving Repr, DecidableEq

/-- The exact Colon singleton passed by the public wrappers.
Julia source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmax(f, domain) = _findmax(f, domain, :)
-- /Source
inductive FindColon where
  | colon
  deriving Repr, DecidableEq

/-- The two indexed lambda types retain their original f in an initialized immutable field; direction distinguishes the maximum and minimum source closure identities.
Julia source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmax(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmax, pairs(domain) )
-- /Source
structure FindIndexedClosure (V : Type) where
  direction : FindDirection
  f : V

/-- The two value lambda types retain original f and distinguish maximum/minimum source closure identities.
Julia source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argmax(f, domain) = mapfoldl(x -> (f(x), x), _rf_findmax, domain)[2]
-- /Source
structure FindValueClosure (V : Type) where
  direction : FindDirection
  f : V

/-- Concrete compiler-created closures distinguish indexed and value bodies, each with stored capture identity. Their capture is read by Core.getfield, never user getproperty.
Julia source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmax(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmax, pairs(domain) )
-- /Source
inductive FindClosure (V : Type) where
  | indexed (fields : FindIndexedClosure V)
  | value (fields : FindValueClosure V)

/-- Open dispatch on the source-unfixed callable, iterator and intermediate result types. V is a universal heterogeneous carrier retaining object identities. Tokens preserve known closure and callee identities; actual lambda/reducer bodies are separately implemented below. Selected pairs/mapfoldl/getindex/find calls retain arbitrary outputs, mutations, exceptions and divergence through m.
Julia source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmax(f, domain) = _findmax(f, domain, :)
-- /Source
structure FindPublicOps (m : Type → Type) (V : Type) where
  internalMapped : FindDirection → V → V → FindColon → m V
  internalSingle : FindDirection → V → FindColon → m V
  publicIdentity : FindDirection → IdentityFn → V → m V
  publicSingle : FindDirection → V → m V
  pairs : V → m V
  mapfoldl : FindClosure V → FindDirection → V → m V
  getindex : V → JInt .i64 → m V

/-- Read the actual initialized capture after full ordinary argument destructuring, call that f once on the observed v, and construct the tuple of its result with the observed k. Known pair arguments use concrete Base tuple indexed_iterate; arbitrary objects retain selected indexed_iterate, direct Core fields, mutation, failures and divergence.
Julia source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmax(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmax, pairs(domain) )
-- /Source
def findIndexedClosureApply {W E V : Type} (pairOps : FlatteningAdapterOps W E V)
    (apply : V → V → FoldEval W (FoldError E) V)
    (closure : FindIndexedClosure V) (argument : FlattenTransformResult V) :
    FoldEval W (FoldError E) (V × V) := do
  let (key, value) ← flatteningDestructure pairOps argument
  let mapped ← apply closure.f value
  pure (mapped, key)

/-- The value lambda reads its stored f directly, maps the exact original x once, then returns the mapped value paired with that original object. No custom property getter intervenes.
Julia source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argmax(f, domain) = mapfoldl(x -> (f(x), x), _rf_findmax, domain)[2]
-- /Source
def findValueClosureApply {m : Type → Type} [Monad m] {V : Type}
    (apply : V → V → m V) (closure : FindValueClosure V) (x : V) : m (V × V) := do
  let mapped ← apply closure.f x
  pure (mapped, x)

/-- Selected comparison methods on completely unfixed dynamic operand types; non-Bool results remain representable for the actual conditional TypeError.
Julia source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _rf_findmax((fm, im), (fx, ix)) = isless(fm, fx) ? (fx, ix) : (fm, im)
-- /Source
structure FindCompareOps (m : Type → Type) (V : Type) where
  isless : V → V → m (Bool ⊕ V)
  isgreater : V → V → m (Bool ⊕ V)

/-- The source conditional accepts exactly Bool after the comparison has completed. The installed Bool assertion supplies the result or the concrete TypeError without changing the current world.
Julia source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _rf_findmax((fm, im), (fx, ix)) = isless(fm, fx) ? (fx, ix) : (fm, im)
-- /Source
def findCondition {W E V : Type} (value : Bool ⊕ V) : FoldEval W (FoldError E) Bool :=
  liftExcept ((assertBool value).mapError fun _ => (FoldError.typeError : FoldError E))

/-- Forward original f/domain with the actual Colon singleton to selected _findmax.
Julia source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmax(f, domain) = _findmax(f, domain, :)
-- /Source
def findMaxMapped {m : Type → Type} {V : Type} (ops : FindPublicOps m V)
    (f domain : V) : m V := ops.internalMapped .maximum f domain .colon

/-- Construct the exact indexed maximum closure, obtain pairs(domain), then pass that observed iterator and _rf_findmax identity to selected mapfoldl. Failure/divergence of pairs suppresses reduction.
Julia source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:855-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmax(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmax, pairs(domain) )
-- /Source
def findMaxColon {m : Type → Type} [Monad m] {V : Type} (ops : FindPublicOps m V)
    (f domain : V) (_ : FindColon) : m V := do
  let paired ← ops.pairs domain
  ops.mapfoldl (.indexed ⟨.maximum, f⟩) .maximum paired

/-- Destructure both arbitrary arguments left to right, compare the observed values once with isless, and return the actual entire selected pair. False retains the left pair, preserving first-tie behavior without assuming any ordering law.
Julia source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _rf_findmax((fm, im), (fx, ix)) = isless(fm, fx) ? (fx, ix) : (fm, im)
-- /Source
def findReduceMax {W E V : Type} (pairOps : FlatteningAdapterOps W E V)
    (ops : FindCompareOps (FoldEval W (FoldError E)) V)
    (left right : FlattenTransformResult V) : FoldEval W (FoldError E) (V × V) := do
  let (fm, im) ← flatteningDestructure pairOps left
  let (fx, ix) ← flatteningDestructure pairOps right
  let better ← findCondition (← ops.isless fm fx)
  if better then pure (fx, ix) else pure (fm, im)

/-- Forward the original collection with the actual Colon singleton to selected unary _findmax.
Julia source: base/reduce.jl:883-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:883-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmax(itr) = _findmax(itr, :)
-- /Source
def findMaxSingle {m : Type → Type} {V : Type} (ops : FindPublicOps m V)
    (itr : V) : m V := ops.internalSingle .maximum itr .colon

/-- Forward the exact identity function singleton and original collection to selected findmax.
Julia source: base/reduce.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmax(a, ::Colon) = findmax(identity, a)
-- /Source
def findMaxIdentity {m : Type → Type} {V : Type} (ops : FindPublicOps m V)
    (a : V) (_ : FindColon) : m V := ops.publicIdentity .maximum .identity a

/-- Forward original f/domain with the actual Colon singleton to selected _findmin.
Julia source: base/reduce.jl:920-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:920-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmin(f, domain) = _findmin(f, domain, :)
-- /Source
def findMinMapped {m : Type → Type} {V : Type} (ops : FindPublicOps m V)
    (f domain : V) : m V := ops.internalMapped .minimum f domain .colon

/-- Construct the exact indexed minimum closure, obtain pairs(domain), then pass that observed iterator and _rf_findmin identity to selected mapfoldl. The shared closure implementation gives the actual lambda body.
Julia source: base/reduce.jl:921-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:921-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmin(f, domain, ::Colon) = mapfoldl( ((k, v),) -> (f(v), k), _rf_findmin, pairs(domain) )
-- /Source
def findMinColon {m : Type → Type} [Monad m] {V : Type} (ops : FindPublicOps m V)
    (f domain : V) (_ : FindColon) : m V := do
  let paired ← ops.pairs domain
  ops.mapfoldl (.indexed ⟨.minimum, f⟩) .minimum paired

/-- Destructure both arbitrary arguments left to right, compare their observed first values once with isgreater, assert Bool, and return the actual selected pair. False retains the left pair with no assumed comparison laws.
Julia source: base/reduce.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _rf_findmin((fm, im), (fx, ix)) = isgreater(fm, fx) ? (fx, ix) : (fm, im)
-- /Source
def findReduceMin {W E V : Type} (pairOps : FlatteningAdapterOps W E V)
    (ops : FindCompareOps (FoldEval W (FoldError E)) V)
    (left right : FlattenTransformResult V) : FoldEval W (FoldError E) (V × V) := do
  let (fm, im) ← flatteningDestructure pairOps left
  let (fx, ix) ← flatteningDestructure pairOps right
  let better ← findCondition (← ops.isgreater fm fx)
  if better then pure (fx, ix) else pure (fm, im)

/-- Forward the original collection with the actual Colon singleton to selected unary _findmin.
Julia source: base/reduce.jl:949-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:949-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- findmin(itr) = _findmin(itr, :)
-- /Source
def findMinSingle {m : Type → Type} {V : Type} (ops : FindPublicOps m V)
    (itr : V) : m V := ops.internalSingle .minimum itr .colon

/-- Forward the exact identity function singleton and original collection to selected findmin.
Julia source: base/reduce.jl:950-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:950-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _findmin(a, ::Colon) = findmin(identity, a)
-- /Source
def findMinIdentity {m : Type → Type} {V : Type} (ops : FindPublicOps m V)
    (a : V) (_ : FindColon) : m V := ops.publicIdentity .minimum .identity a

/-- Mapfoldl receives the concrete value-maximum closure, exact _rf_findmax identity and original domain. Its arbitrary observed result is indexed by the actual native Int64 two; no pair result is assumed.
Julia source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argmax(f, domain) = mapfoldl(x -> (f(x), x), _rf_findmax, domain)[2]
-- /Source
def argMaxMapped {m : Type → Type} [Monad m] {V : Type} (ops : FindPublicOps m V)
    (f domain : V) : m V := do
  let result ← ops.mapfoldl (.value ⟨.maximum, f⟩) .maximum domain
  ops.getindex result (JuliaLean.base.int.lit .i64 2)

/-- Call selected findmax on the original iterator, then selected getindex on its actual result with native Int64 two. Earlier failure/divergence suppresses indexing.
Julia source: base/reduce.jl:1005-1005 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1005-1005 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argmax(itr) = findmax(itr)[2]
-- /Source
def argMaxSingle {m : Type → Type} [Monad m] {V : Type} (ops : FindPublicOps m V)
    (itr : V) : m V := do
  let result ← ops.publicSingle .maximum itr
  ops.getindex result (JuliaLean.base.int.lit .i64 2)

/-- Mapfoldl receives the concrete value-minimum closure, exact _rf_findmin identity and original domain. Its arbitrary observed result is indexed by native Int64 two, preserving selected getter effects/errors.
Julia source: base/reduce.jl:1034-1034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1034-1034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argmin(f, domain) = mapfoldl(x -> (f(x), x), _rf_findmin, domain)[2]
-- /Source
def argMinMapped {m : Type → Type} [Monad m] {V : Type} (ops : FindPublicOps m V)
    (f domain : V) : m V := do
  let result ← ops.mapfoldl (.value ⟨.minimum, f⟩) .minimum domain
  ops.getindex result (JuliaLean.base.int.lit .i64 2)

/-- Call selected findmin on the original iterator, then selected getindex on its actual result with native Int64 two. Every result, mutation, error and divergence remains at the source call point.
Julia source: base/reduce.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argmin(itr) = findmin(itr)[2]
-- /Source
def argMinSingle {m : Type → Type} [Monad m] {V : Type} (ops : FindPublicOps m V)
    (itr : V) : m V := do
  let result ← ops.publicSingle .minimum itr
  ops.getindex result (JuliaLean.base.int.lit .i64 2)

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- The anonymous closure captures the original f object without invoking it. Captured-variable reads lower to primitive storage access, not getproperty.
Julia source: base/reduce.jl:1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bool(f) = x->f(x)::Bool
-- /Source
structure BoolClosure (F : Type) where
  captured : F

/-- Actual closure allocation preserves the captured object. No mapping or Bool assertion occurs until invocation.
Julia source: base/reduce.jl:1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bool(f) = x->f(x)::Bool
-- /Source
def makeBoolClosure {F : Type} (f : F) : BoolClosure F := ⟨f⟩

/-- The source is an expression type assertion, not a function return annotation: there is no conversion. Every non-Bool result throws TypeError after the selected mapper has run.
Julia source: base/reduce.jl:1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bool(f) = x->f(x)::Bool
-- /Source
def applyBoolClosure {W E F X Other : Type}
    (invoke : F → X → FoldEval W (FoldError E) (Bool ⊕ Other))
    (closure : BoolClosure F) (x : X) : FoldEval W (FoldError E) Bool := do
  let result ← invoke closure.captured x
  match result with
  | .inl value => pure value
  | .inr _ => throw .typeError

/-- Native Int initial values are distinguished from every other dynamic value, including UInt, custom integers and non-integers. The full source body does not assert that init is an Integer.
Julia source: base/reduce.jl:1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1094-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- count(itr; init=0) = count(identity, itr; init)
-- 
-- count(f, itr; init=0) = _simple_count(f, itr, init)
-- /Source
inductive CountArgument (Other : Type) where
  | native (value : JInt .i64)
  | other (value : Other)

/-- The omitted init default is the actual native Int64 literal zero. Explicitly supplied values retain their exact type/value tag.
Julia source: base/reduce.jl:1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1094-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- count(itr; init=0) = count(identity, itr; init)
-- 
-- count(f, itr; init=0) = _simple_count(f, itr, init)
-- /Source
def countInitial {V : Type} (init : Option (CountArgument V)) : CountArgument V :=
  init.getD (.native (JuliaLean.base.int.lit .i64 0))

/-- The selected downstream call receives exactly one keyword, named init, containing the actual chosen value. Opaque other values retain mutable references.
Julia source: base/reduce.jl:1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1094-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- count(itr; init=0) = count(identity, itr; init)
-- /Source
structure CountKeyword (V : Type) where
  init : CountArgument V

/-- Known closures and arbitrary values returned by genuinely selected _bool methods remain distinct. Only the known closure branch uses makeBoolClosure.
Julia source: base/reduce.jl:1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1098-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _simple_count(pred, itr, init) = sum(_bool(pred), itr; init)
-- /Source
inductive BoolClosureResult (F Other : Type) where
  | known (closure : BoolClosure F)
  | custom (value : Other)

/-- Selected count/simple_count/sum and alternative _bool calls depend on unfixed input types. No result-type, purity, termination or correctness law is assumed.
Julia source: base/reduce.jl:1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1094-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- count(itr; init=0) = count(identity, itr; init)
-- 
-- count(f, itr; init=0) = _simple_count(f, itr, init)
-- 
-- _simple_count(pred, itr, init) = sum(_bool(pred), itr; init)
-- /Source
structure CountGeneralOps (m : Type → Type) (F I V OtherClosure R : Type) where
  count : IdentityFn → I → CountKeyword V → m R
  simple : F → I → CountArgument V → m R
  selectBool : F → Bool := fun _ => false
  bool : F → m (BoolClosureResult F OtherClosure)
  sum : BoolClosureResult F OtherClosure → I → CountKeyword V → m R

/-- Forward identity and the original iterator to selected count with the exact native default or explicitly supplied init keyword. There is no element traversal in this wrapper.
Julia source: base/reduce.jl:1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1094-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- count(itr; init=0) = count(identity, itr; init)
-- /Source
def countPublic {m : Type → Type} {F I V OtherClosure R : Type}
    (ops : CountGeneralOps m F I V OtherClosure R) (itr : I)
    (init : Option (CountArgument V) := none) : m R :=
  ops.count .identity itr ⟨countInitial init⟩

/-- Forward the actual mapper and iterator with the chosen initial value as a positional argument to selected _simple_count. Errors and arbitrary outcomes pass through unchanged.
Julia source: base/reduce.jl:1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- count(f, itr; init=0) = _simple_count(f, itr, init)
-- /Source
def countMapped {m : Type → Type} {F I V OtherClosure R : Type}
    (ops : CountGeneralOps m F I V OtherClosure R) (f : F) (itr : I)
    (init : Option (CountArgument V) := none) : m R :=
  ops.simple f itr (countInitial init)

/-- Construct the actual Bool assertion closure unless dispatch selects an alternative _bool method, then call selected sum with that result, the original iterator and exact init keyword. Closure creation itself never evaluates the predicate.
Julia source: base/reduce.jl:1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1098-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _simple_count(pred, itr, init) = sum(_bool(pred), itr; init)
-- /Source
def simpleCount {m : Type → Type} [Monad m] {F I V OtherClosure R : Type}
    (ops : CountGeneralOps m F I V OtherClosure R) (pred : F) (itr : I)
    (init : CountArgument V) : m R := do
  let mapped ← if ops.selectBool pred then ops.bool pred else pure (.known (makeBoolClosure pred))
  ops.sum mapped itr ⟨init⟩

end JuliaLean.base.reduce.Models2Group7

namespace JuliaLean.base.reduce.Models2Group7

open JuliaLean

/-- Exactly the three generated source pairs are represented; no other range reduction method is added.
Julia source: base/reduce.jl:1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1119-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fred, f) in ((maximum, max), (minimum, min), (sum, add_sum))
--     @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
--         isempty(r) ? init : op(init, $fred(r))
--     end
-- end
-- /Source
inductive RangeFoldKind where
  | maximum
  | minimum
  | sum
  deriving DecidableEq

/-- The loop bindings connect maximum/max, minimum/min and sum/add_sum. These singleton tags are source constants, not callback choices.
Julia source: base/reduce.jl:1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1119-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fred, f) in ((maximum, max), (minimum, min), (sum, add_sum))
--     @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
--         isempty(r) ? init : op(init, $fred(r))
--     end
-- end
-- /Source
def rangeFoldReducer : RangeFoldKind → ReductionSingleton
  | .maximum => .maximum
  | .minimum => .minimum
  | .sum => .addSum

/-- Known source singleton callables and arbitrary getter-returned values share the full callable/non-callable domain. Selected non-callables fail at their invocation leaf.
Julia source: base/reduce.jl:1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1119-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fred, f) in ((maximum, max), (minimum, min), (sum, add_sum))
--     @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
--         isempty(r) ? init : op(init, $fred(r))
--     end
-- end
-- /Source
inductive RangeCallable (Other : Type) where
  | standard (function : ReductionSingleton)
  | other (value : Other)

/-- The generated method receiver contains exactly the source singleton; immutable BottomRF instances with that singleton have the same fields. A selected getproperty override can still replace the invoked callable.
Julia source: base/reduce.jl:1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1119-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fred, f) in ((maximum, max), (minimum, min), (sum, add_sum))
--     @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
--         isempty(r) ? init : op(init, $fred(r))
--     end
-- end
-- /Source
def rangeFoldBottom {F : Type} (kind : RangeFoldKind) : BottomAdapter (RangeCallable F) :=
  ⟨.standard (rangeFoldReducer kind)⟩

/-- Range types remain abstract, so isempty and maximum/minimum/sum are unrestricted selected calls. BottomRF invocation can select a genuinely different method on unfixed accumulator/result types; otherwise the actual installed first/binary adapter bodies run.
Julia source: base/reduce.jl:1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1119-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fred, f) in ((maximum, max), (minimum, min), (sum, add_sum))
--     @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
--         isempty(r) ? init : op(init, $fred(r))
--     end
-- end
-- /Source
structure RangeFoldOps (W E Range F V Other : Type) where
  isempty : Range → FoldEval W (FoldError E) (Bool ⊕ Other)
  reduceRange : RangeFoldKind → Range → FoldEval W (FoldError E) V
  selectBottom : RangeFoldKind → FoldInit V → V → Bool := fun _ _ _ => false
  customBottom : BottomAdapter (RangeCallable F) → FoldInit V → V →
    FoldEval W (FoldError E) (FoldInit V)
  bottom : BottomAdapterOps (FoldEval W (FoldError E)) (RangeCallable F) (FoldInit V) V (FoldInit V)

/-- All three generated bodies enforce the Bool condition; empty returns the exact original init with no reduction or operator call. Nonempty evaluates the selected range reduction then dispatches the actual BottomRF call. Sentinel init selects reduce_first; other init values select the binary body. No law is assumed for range behavior or callbacks.
Julia source: base/reduce.jl:1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reduce.jl:1119-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fred, f) in ((maximum, max), (minimum, min), (sum, add_sum))
--     @eval function _foldl_impl(op::typeof(BottomRF($f)), init, r::AbstractRange)
--         isempty(r) ? init : op(init, $fred(r))
--     end
-- end
-- /Source
def foldlRangeSpecial {W E Range F V Other : Type}
    (ops : RangeFoldOps W E Range F V Other) (kind : RangeFoldKind)
    (init : FoldInit V) (range : Range) : FoldEval W (FoldError E) (FoldInit V) := do
  let condition ← ops.isempty range
  match condition with
  | .inr _ => throw .typeError
  | .inl true => pure init
  | .inl false =>
      let value ← ops.reduceRange kind range
      let op : BottomAdapter (RangeCallable F) := rangeFoldBottom kind
      if ops.selectBottom kind init value then ops.customBottom op init value
      else match init with
        | .initial => bottomInitial ops.bottom op value
        | .value _ => bottomApply ops.bottom op init value

end JuliaLean.base.reduce.Models2Group7
/-!
Generic list model of the reductions in `base/reduce.jl` and `base/accumulate.jl`.

A one-dimensional array or iterator is a `List`. Julia's dynamically typed
`op`, `f`, `reduce_first`, `reduce_empty` are passed as Lean functions, so the
same definitions serve every element type. Exceptions are `Err`.
-/

namespace JuliaLean.Reduce


section
variable {α β γ : Type}


/-- `mapreduce_impl(f, op, A, ifirst, ilast, blksize)`, `base/reduce.jl:252-274`, applied to
the nonempty slice `A[ifirst:ilast] = a :: rest`. `ilast - ifirst` is `rest.length`;
`imid = ifirst + (ilast - ifirst) >> 1`, so the left half `A[ifirst:imid]` is
`a :: rest.take (rest.length / 2)` and the right half `A[imid+1:ilast]` is
`rest.drop (rest.length / 2)`. `first` is `mapreduce_first(f, op, ·)`. The sequential
portion is a `@simd` loop, which lets the compiler reassociate floating-point `op`s; the
model fixes the left-to-right order written in the source. -/
def mrImpl (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a : α) (rest : List α) : β :=
  match rest with
  | [] => first a
  | b :: rest' =>
    if rest'.length + 1 < blk then
      rest'.foldl (fun v x => op v (f x)) (op (f a) (f b))
    else
      match h : (b :: rest').drop ((rest'.length + 1) / 2) with
      | [] => first a
      | c :: rest2 =>
        op (mrImpl f op first blk a ((b :: rest').take ((rest'.length + 1) / 2)))
          (mrImpl f op first blk c rest2)
termination_by rest.length
decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · have := congrArg List.length h
    simp only [List.length_drop, List.length_cons] at this
    simp only [List.length_cons]; omega

/-- `_mapreduce(f, op, ::IndexLinear, A)`, `base/reduce.jl:436-457`: `empty` is the result of
`mapreduce_empty_iter` for an empty array, `first` is `mapreduce_first`, and `blk` is
`pairwise_blocksize(f, op)` (`base/reduce.jl:311-314`). -/
def mapreduceArr (f : α → β) (op : β → β → β) (first : α → β) (empty : R β) (blk : Nat) :
    List α → R β
  | [] => empty
  | [a] => .ok (first a)
  | a :: b :: rest =>
    if rest.length + 2 < 16 then .ok (rest.foldl (fun s x => op s (f x)) (op (f a) (f b)))
    else .ok (mrImpl f op first blk a (b :: rest))


/-- `mapfoldl(f, op, itr)` without `init`, `base/reduce.jl:40-63, 83-84`: the first element
goes through `BottomRF`, i.e. `reduce_first(op, f(x))` (`first`), the rest through `op`;
an empty iterator gives `reduce_empty_iter` (`empty`). -/
def mapfoldlNoInit (f : α → β) (op : β → β → β) (first : β → β) (empty : R β) :
    List α → R β
  | [] => empty
  | a :: rest => .ok (rest.foldl (fun v x => op v (f x)) (first (f a)))

/-- `mapfoldl(f, op, itr; init)`, `base/reduce.jl:40-63`: `op(init, f(x1))`, then left fold. -/
def mapfoldlInit (f : α → β) (op : γ → β → γ) (init : γ) (A : List α) : γ :=
  A.foldl (fun v x => op v (f x)) init

/-- `mapfoldr(f, op, itr)` without `init`, `base/reduce.jl:200-213`: a left fold of
`BottomRF(FlipArgs(op))` over the reversed iterator. The first visited (last) element goes
through `reduce_first(FlipArgs(op), ·)`, given as `firstFlip`. -/
def mapfoldrNoInit (f : α → β) (op : β → β → β) (firstFlip : β → β) (empty : R β)
    (A : List α) : R β :=
  mapfoldlNoInit f (fun acc x => op x acc) firstFlip empty A.reverse

/-- `mapfoldr(f, op, itr; init)`, `base/reduce.jl:200-213`: `op(f(x), acc)` from the right. -/
def mapfoldrInit (f : α → β) (op : β → γ → γ) (init : γ) (A : List α) : γ :=
  A.reverse.foldl (fun acc x => op (f x) acc) init


end

end JuliaLean.Reduce

/-!
A small dynamically typed value universe for reductions whose result type is
chosen at run time: `BitInteger` values, `Float64`, `Bool` and `missing`, with
the element types of arrays built from them (`Ty`, including two-member unions
and `Union{}`). Arithmetic promotes as Julia's `promote` does for these types
(integers wrap into the promoted type, `base/int.jl:809-822`; `Bool` promotes
to the other integer type; integers and `Bool` promote to `Float64`).
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

namespace Val

instance : Inhabited Val := ⟨.missing⟩

/-- `Int64` literal. -/
def i64 (x : Int) : Val := .int .i64 (JInt.lit .i64 x)

/-- `typeof(v)`. -/
def typeOf : Val → Ty
  | .int t _ => .int t
  | .f64 _ => .f64
  | .bool _ => .bool
  | .missing => .missing

/-- `isnan(v)` for a `Number` (`false` for integers and `Bool`, never called on `missing`). -/
def isnan : Val → Bool
  | .f64 x => F64.isnan x
  | _ => false

/-- `isunordered(v)`, `base/operators.jl:283-285`, `base/missing.jl:71`. -/
def isunordered : Val → Bool
  | .f64 x => F64.isnan x
  | .missing => true
  | _ => false

/-- `max(x, y)`: `max(x::T, y::T) = ifelse(y < x, x, y)` for integers and `Bool`
(`base/promotion.jl`), `base/math.jl:835` for floats, `missing` absorbing
(`base/missing.jl:129-137`). -/
def vmax : Val → Val → Val :=
  numBin (fun t x y => .int t (if y.val < x.val then x else y)) (fun x y => .f64 (fmax x y))
    (fun a b => .bool (if !b && a then a else b))

/-- `min(x, y)`, mirror of `vmax`. -/
def vmin : Val → Val → Val :=
  numBin (fun t x y => .int t (if y.val < x.val then y else x)) (fun x y => .f64 (fmin x y))
    (fun a b => .bool (if !b && a then b else a))

/-- `isless(x, y)`: `missing` is greater than everything (`base/missing.jl:86-88`), numbers
compare after promotion, floats with `F64.isless`. -/
def visless : Val → Val → Bool
  | .missing, _ => false
  | _, .missing => true
  | x, y =>
    match numBin (fun _ a b => .bool (decide (a.val < b.val)))
        (fun a b => .bool (F64.isless a b)) (fun a b => .bool (!a && b)) x y with
    | .bool r => r
    | _ => false

/-- `abs(x)`: wrapping for signed integers (`abs(typemin(T)) == typemin(T)`), identity for
unsigned integers and `Bool`, sign bit cleared for floats, `missing` absorbing. -/
def vabs : Val → Val
  | .int t x => .int t (JInt.wrap t (if x.val < 0 then -x.val else x.val))
  | .f64 x => .f64 (F64.abs x)
  | v => v

/-- Signed `BitInteger` types narrower than `Int` (`BitSignedSmall`). -/
def smallSigned : IntTy → Bool
  | .i8 | .i16 | .i32 => true
  | _ => false

/-- Unsigned `BitInteger` types narrower than `UInt` (`BitUnsignedSmall`). -/
def smallUnsigned : IntTy → Bool
  | .u8 | .u16 | .u32 => true
  | _ => false

/-- `Union{Bool, BitIntegerSmall}` membership. -/
def smallOrBool : Val → Bool
  | .int t _ => smallSigned t || smallUnsigned t
  | .bool _ => true
  | _ => false

/-- Integer value of a `Bool` or integer. -/
def intVal : Val → Int
  | .int _ x => x.val
  | .bool b => if b then 1 else 0
  | _ => 0

/-- `Base.add_sum(x, y)`, `base/reduce.jl:16-19`. -/
def addSum (x y : Val) : Val :=
  match x, y with
  | .int s _, .int t _ =>
    if smallUnsigned s && smallUnsigned t then .int .u64 (JInt.wrap .u64 (intVal x + intVal y))
    else if smallOrBool x && smallOrBool y then .int .i64 (JInt.wrap .i64 (intVal x + intVal y))
    else plus x y
  | _, _ =>
    if smallOrBool x && smallOrBool y then .int .i64 (JInt.wrap .i64 (intVal x + intVal y))
    else plus x y

/-- `Base.mul_prod(x, y)`, `base/reduce.jl:27-30`. -/
def mulProd (x y : Val) : Val :=
  match x, y with
  | .int s _, .int t _ =>
    if smallSigned s && smallSigned t then .int .i64 (JInt.wrap .i64 (intVal x * intVal y))
    else if smallUnsigned s && smallUnsigned t then .int .u64 (JInt.wrap .u64 (intVal x * intVal y))
    else times x y
  | _, _ => times x y

/-- `reduce_first(add_sum, x)`, `base/reduce.jl:410, 413-415`. -/
def firstAddSum : Val → Val
  | .int t x =>
    if smallSigned t then .int .i64 (JInt.wrap .i64 x.val)
    else if smallUnsigned t then .int .u64 (JInt.wrap .u64 x.val)
    else .int t x
  | .bool b => .int .i64 (boolInt .i64 b)
  | v => v

/-- `reduce_first(mul_prod, x)`, `base/reduce.jl:416-418`. -/
def firstMulProd : Val → Val
  | .int t x =>
    if smallSigned t then .int .i64 (JInt.wrap .i64 x.val)
    else if smallUnsigned t then .int .u64 (JInt.wrap .u64 x.val)
    else .int t x
  | v => v

/-- `reduce_first(+, x)`, `base/reduce.jl:409-410`. -/
def firstPlus : Val → Val
  | .bool b => .int .i64 (boolInt .i64 b)
  | v => v

/-- `or_any(x, y)`, `base/reduce.jl:33, 36`: `(x || y)::Bool`, `x | y` on two `Bool`s. -/
def orAny : Val → Val → R Val
  | .bool true, _ => .ok (.bool true)
  | .bool false, .bool b => .ok (.bool b)
  | _, _ => .error .typeError

/-- `and_all(x, y)`, `base/reduce.jl:32, 35`: `(x && y)::Bool`, `x & y` on two `Bool`s. -/
def andAll : Val → Val → R Val
  | .bool false, _ => .ok (.bool false)
  | .bool true, .bool b => .ok (.bool b)
  | _, _ => .error .typeError

/-- `x | y` on `Bool` and `missing`, `base/bool.jl:15`, `base/missing.jl:162-164`. -/
def bor : Val → Val → R Val
  | .bool a, .bool b => .ok (.bool (a || b))
  | .missing, .bool b | .bool b, .missing => .ok (if b then .bool true else .missing)
  | .missing, .missing => .ok .missing
  | _, _ => .error .methodError

end Val

namespace Ty

/-- `v isa T`. -/
def isa (v : Val) : Ty → Bool
  | .union a b => isa v a || isa v b
  | .bottom => false
  | t => decide (v.typeOf = t)

/-- `promote_type(a, b)` on the modelled types (`base/promotion.jl`, `base/int.jl:809-822`,
`base/missing.jl:48`). -/
def promote : Ty → Ty → Ty
  | .int s, .int t => .int (IntTy.promote s t)
  | .int t, .bool | .bool, .int t => .int t
  | .int _, .f64 | .f64, .int _ | .bool, .f64 | .f64, .bool | .f64, .f64 => .f64
  | .bool, .bool => .bool
  | .missing, .missing => .missing
  | .missing, s | s, .missing => .union s .missing
  | .bottom, s | s, .bottom => s
  | a, b => .union a b

/-- `T <: Union{BitInteger, IEEEFloat, BigFloat}`; `Union{}` is a subtype of every type. -/
def bitIntFloat : Ty → Bool
  | .int _ | .f64 | .bottom => true
  | .union a b => bitIntFloat a && bitIntFloat b
  | _ => false

/-- `typemax(T)` (`Inf` for `Float64`); no method for `Union{}` or unions. -/
def typemax : Ty → R Val
  | .int t => .ok (.int t (JInt.typemax t))
  | .f64 => .ok (.f64 (F64.inf false))
  | _ => .error .methodError

/-- `typemin(T)` (`-Inf` for `Float64`). -/
def typemin : Ty → R Val
  | .int t => .ok (.int t (JInt.typemin t))
  | .f64 => .ok (.f64 (F64.inf true))
  | _ => .error .methodError

/-- `zero(T)`, with `zero(Union{T, Missing}) = zero(T)` (`base/missing.jl:105-108`) and, for
a union of numbers, `zero(T) = convert(T, 0)` (`base/number.jl`), which is the `Int` `0`
when `Int` is a member; `none` when no method applies. -/
def zero : Ty → Option Val
  | .int t => some (.int t (JInt.lit t 0))
  | .f64 => some (.f64 F64.zero)
  | .bool => some (.bool false)
  | .missing => some .missing
  | .union a b =>
    if a = .missing then zero b else if b = .missing then zero a
    else if isa (Val.i64 0) (.union a b) then some (Val.i64 0) else none
  | .bottom => none

/-- `one(T)`, the analogue of `zero`. -/
def one : Ty → Option Val
  | .int t => some (.int t (JInt.lit t 1))
  | .f64 => some (.f64 F64.one)
  | .bool => some (.bool true)
  | .missing => some .missing
  | .union a b =>
    if a = .missing then one b else if b = .missing then one a
    else if isa (Val.i64 1) (.union a b) then some (Val.i64 1) else none
  | .bottom => none

/-- `convert(T, v)` as performed by `setindex!` on an array with element type `T`. -/
def convert (ty : Ty) (v : Val) : R Val :=
  if isa v ty then .ok v
  else
    match ty, v with
    | .int t, .int _ x =>
      match JInt.convert (t.name) t x.val with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .int t, .f64 x =>
      match F64.int t x with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .int t, .bool b => .ok (.int t (Val.boolInt t b))
    | .f64, .int _ x => .ok (.f64 (F64.ofJInt x))
    | .f64, .bool b => .ok (.f64 (Val.toF64 (.bool b)))
    | .bool, .int _ x =>
      if x.val = 0 then .ok (.bool false) else if x.val = 1 then .ok (.bool true)
      else .error .inexactError
    | .union a b, v =>
      if a = .missing then convertNonmissing b v
      else if b = .missing then convertNonmissing a v
      else .error .methodError
    | _, _ => .error .methodError
where
  /-- `convert(T, v)` for the non-missing member of `Union{T, Missing}`. -/
  convertNonmissing (t : Ty) (v : Val) : R Val :=
    match t, v with
    | .int t, .int _ x =>
      match JInt.convert (t.name) t x.val with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .int t, .f64 x =>
      match F64.int t x with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .f64, .int _ x => .ok (.f64 (F64.ofJInt x))
    | _, _ => .error .methodError

end Ty

end JuliaLean.Reduce
/-!
Whole-collection reductions of a vector of `Val`s (`dims = :`), `base/reduce.jl`,
`base/anyall.jl`, `base/reducedim.jl:333-346`.
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

namespace Vec

/-- `reduce_empty(add_sum, T)`, `base/reduce.jl:342-353`: `Int`/`UInt` zero for small
integer types and `Bool`, `zero(T)` otherwise. -/
def emptyAddSum : Ty → R Val
  | .int t =>
    if Val.smallSigned t then .ok (Val.i64 0)
    else if Val.smallUnsigned t then .ok (.int .u64 (JInt.lit .u64 0))
    else .ok (.int t (JInt.lit t 0))
  | .bool => .ok (Val.i64 0)
  | t => match t.zero with
    | some z => .ok z
    | none => .error .argumentError

/-- `reduce_empty(mul_prod, T)`, `base/reduce.jl:344, 354-356`: `Int`/`UInt` one for small
integer types, `one(T)` otherwise. -/
def emptyMulProd : Ty → R Val
  | .int t =>
    if Val.smallSigned t then .ok (Val.i64 1)
    else if Val.smallUnsigned t then .ok (.int .u64 (JInt.lit .u64 1))
    else .ok (.int t (JInt.lit t 1))
  | t => match t.one with
    | some o => .ok o
    | none => .error .argumentError

/-- `reduce_empty(+, T)`, `base/reduce.jl:342-343`: `zero(T)`, `zero(Int)` for `Bool`. -/
def emptyPlus : Ty → R Val
  | .bool => .ok (Val.i64 0)
  | t => match t.zero with
    | some z => .ok z
    | none => .error .argumentError

/-- `sum(v)` for `v::Vector{T}`: `mapreduce(identity, add_sum, v)` → `_mapreduce`. -/
def sum (eltype : Ty) (v : List Val) : R Val :=
  mapreduceArr id Val.addSum Val.firstAddSum (emptyAddSum eltype) 1024 v


/-- `prod(v)`. -/
def prod (eltype : Ty) (v : List Val) : R Val :=
  mapreduceArr id Val.mulProd Val.firstMulProd (emptyMulProd eltype) 1024 v


/-- `maximum(v)`: `mapreduce(identity, max, v)`; `reduce_empty(max, T)` throws. -/
def maximum (v : List Val) : R Val := mapreduceArr id Val.vmax id (.error .argumentError) 1024 v

/-- `minimum(v)`. -/
def minimum (v : List Val) : R Val := mapreduceArr id Val.vmin id (.error .argumentError) 1024 v


/-- `extrema(v)`: `mapreduce(ExtremaMap(identity), _extrema_rf, v)`,
`base/reduce.jl:806-816`; `reduce_first` of a tuple is the tuple. -/
def extrema (v : List Val) : R (Val × Val) :=
  mapreduceArr (fun x => (x, x)) (fun a b => (Val.vmin a.1 b.1, Val.vmax a.2 b.2))
    (fun x => (x, x)) (.error .argumentError) 1024 v

/-- `maximum(abs, v)`: `mapreduce(abs, max, v)`; `mapreduce_empty(abs, max, T) = abs(zero(T))`
(`base/reduce.jl:374`). -/
def maxAbs (eltype : Ty) (v : List Val) : R Val :=
  mapreduceArr Val.vabs Val.vmax Val.vabs
    (match eltype.zero with | some z => .ok (Val.vabs z) | none => .error .argumentError) 1024 v

/-- `isgreater(x, y)`, `base/operators.jl:295`. -/
def isgreater (x y : Val) : Bool :=
  if x.isunordered || y.isunordered then Val.visless x y else Val.visless y x

/-- `findmax(v)`: `mapfoldl(((k, v),) -> (v, k), _rf_findmax, pairs(v))`,
`base/reduce.jl:851-853, 880-881`; indices are 1-based. -/
def findmax (v : List Val) : R (Val × Nat) :=
  mapfoldlNoInit id (fun (a b : Val × Nat) => if Val.visless a.1 b.1 then b else a) id
    (.error .argumentError) (v.zipIdx 1)

/-- `findmin(v)`: `_rf_findmin` with `isgreater`, `base/reduce.jl:917-919, 946-947`. -/
def findmin (v : List Val) : R (Val × Nat) :=
  mapfoldlNoInit id (fun (a b : Val × Nat) => if isgreater a.1 b.1 then b else a) id
    (.error .argumentError) (v.zipIdx 1)


/-- `count(identity, x::Array{Bool}; init)`: `_simple_count`, `base/reduce.jl:1097-1113`.
`v0 = add_sum(init, false)`, `T = typeof(v0)`; each chunk and each remaining element is
added with `n = (n + c) % T`, which exists only for integer `T` (a `Float64` `init` hits
`rem(::Float64, ::Type{Float64})`, a `MethodError`). The sum of the chunk counts is the
number of `true` elements, so for integer `T` the result is that count added to `v0`
modulo `T`. -/
def countBoolArray (init : Val) (xs : List Bool) : R Val :=
  let v0 := Val.addSum init (.bool false)
  match xs, v0 with
  | [], _ => .ok v0
  | _, .int t n => .ok (.int t (JInt.wrap t (n.val + (xs.filter id).length)))
  | _, _ => .error .methodError

/-- `count(identity, itr; init)` for an iterator that is not an array (e.g. a tuple):
`sum(_bool(identity), itr; init)` → `mapfoldl` from `init` (`base/reduce.jl:1093-1095`). -/
def countIter (init : Val) (xs : List Bool) : Val :=
  mapfoldlInit Val.bool Val.addSum init xs

/-- An element type of the outer iterator, here a vector type. -/
inductive OuterEltype where
  | vector (element : Ty)

/-- `eltype(Vector{T})`, used by `reduce_empty` on `FlatteningRF`. -/
def OuterEltype.eltype : OuterEltype → Ty
  | .vector element => element

/-- `foldl(op, itr)` over `Iterators.flatten(vs)` without `init`: `FlatteningRF(BottomRF(op))`,
`base/reduce.jl:83-84, 118-125, 161-164, 361`. The empty reduction delegates to the
wrapped reducer with `eltype(T)`, where `T` is the outer iterator's element type. -/
def foldlFlatten (op : Val → Val → Val) (first : Val → Val) (empty : Ty → R Val)
    (outerEltype : OuterEltype) (vs : List (List Val)) : R Val :=
  let step : Option Val → Val → Option Val := fun acc x =>
    match acc with
    | none => some (first x)
    | some a => some (op a x)
  match vs.foldl (fun acc v => v.foldl step acc) none with
  | none => empty outerEltype.eltype
  | some r => .ok r

/-- `foldl(op, Iterators.flatten(vs); init)`: the same nested fold started from `init`. -/
def foldlFlattenInit (op : Val → Val → Val) (init : Val) (vs : List (List Val)) : Val :=
  vs.foldl (fun acc v => v.foldl op acc) init

/-- `foldr(op, v)`: `reduce_first(FlipArgs(op), x)` delegates to
`reduce_first(op, x)`; an empty `v` uses `reduce_empty(op, T)`
(`base/reduce.jl:361, 420`). -/
def foldr (op : Val → Val → Val) (first : Val → Val) (empty : R Val) (v : List Val) : R Val :=
  mapfoldrNoInit id op first empty v

/-- `foldl(op, v)` with `reduce_first(op, x)` given as `first`. -/
def foldl (op : Val → Val → Val) (first : Val → Val) (v : List Val) : R Val :=
  mapfoldlNoInit id op first (.error .argumentError) v

end Vec


end JuliaLean.Reduce

namespace JuliaLean.ArrayOps

open JuliaLean
open JuliaLean.Float

variable {α β : Type}

/-- `mapfoldl` of `_rf_findmax`/`_rf_findmin` over `pairs(v)`, `base/reduce.jl:852-853,
918-919`: the accumulator `(fm, im)` is replaced by `(fx, ix)` when `better fm fx`. -/
def findFold (better : F64 → F64 → Bool) (acc : F64 × Nat) : List F64 → Nat → F64 × Nat
  | [], _ => acc
  | x :: rest, i => findFold better (if better acc.1 x then (x, i) else acc) rest (i + 1)

/-- `findmax(v)`, `base/reduce.jl:880-881, 851-853`: empty collections throw. -/
def findmax (v : List F64) : Jl (F64 × Nat) :=
  match v with
  | [] => .error (.argumentError "reducing over an empty collection is not allowed")
  | x :: rest => .ok (findFold F64.isless (x, 1) rest 2)

/-- `findmin(v)`, `base/reduce.jl:946-947, 917-919`. -/
def findmin (v : List F64) : Jl (F64 × Nat) :=
  match v with
  | [] => .error (.argumentError "reducing over an empty collection is not allowed")
  | x :: rest => .ok (findFold isgreater (x, 1) rest 2)

/-! ### `sum`, `prod` of integer vectors -/

/-- Result type of `add_sum`/`mul_prod` on `T` (`base/reduce.jl:16-30, 351-356, 413-418`):
`Int` for signed types narrower than `Int`, `UInt` for narrower unsigned types. -/
def sumTy : IntTy → IntTy
  | .i8 | .i16 | .i32 => .i64
  | .u8 | .u16 | .u32 => .u64
  | t => t

/-- `mapreduce_impl(f, op, A, ifirst, ilast, blksize)`, `base/reduce.jl:252-273`,
over the widened values (`f` composed with `reduce_first`'s widening); `op` wraps in
the widened type. Indices are 0-based positions into `xs`; Julia calls it with
`ifirst ≤ ilast`, so the first test `ifirst == ilast` is written `ilast ≤ ifirst`. -/
def mapreduceImpl {t : IntTy} (op : JInt t → JInt t → JInt t) (xs : List (JInt t))
    (blksize : Nat) (ifirst ilast : Nat) : JInt t :=
  let z : JInt t := JInt.lit t 0
  if ilast ≤ ifirst then xs.getD ifirst z
  else if ilast - ifirst < blksize then
    ((List.range (ilast + 1 - (ifirst + 2))).map (· + (ifirst + 2))).foldl
      (fun v i => op v (xs.getD i z)) (op (xs.getD ifirst z) (xs.getD (ifirst + 1) z))
  else
    let imid := ifirst + (ilast - ifirst) / 2
    op (mapreduceImpl op xs blksize ifirst imid) (mapreduceImpl op xs blksize (imid + 1) ilast)
termination_by ilast - ifirst
decreasing_by all_goals omega

/-- `_mapreduce(f, op, IndexLinear(), A)`, `base/reduce.jl:436-457`, with
`pairwise_blocksize = 1024` (`base/reduce.jl:311-314`); `empty` is `reduce_empty`. -/
def mapreduceLinear {t : IntTy} (op : JInt t → JInt t → JInt t) (empty : JInt t)
    (xs : List (JInt t)) : JInt t :=
  let n := xs.length
  let z : JInt t := JInt.lit t 0
  if n = 0 then empty
  else if n = 1 then xs.getD 0 z
  else if n < 16 then (xs.drop 2).foldl op (op (xs.getD 0 z) (xs.getD 1 z))
  else mapreduceImpl op xs 1024 0 (n - 1)

/-- Widening of `reduce_first(add_sum, x)`/`add_sum(x, y)` for small types. -/
def widen {t : IntTy} (x : JInt t) : JInt (sumTy t) := JInt.wrap _ x.val

/-- `sum(v)` for `v::Vector{T}`, `T` a `BitInteger`: `mapreduce(identity, add_sum, v)`. -/
def sum {t : IntTy} (v : List (JInt t)) : JInt (sumTy t) :=
  mapreduceLinear (· + ·) (JInt.lit _ 0) (v.map widen)

/-- `prod(v)`: `mapreduce(identity, mul_prod, v)`. -/
def prod {t : IntTy} (v : List (JInt t)) : JInt (sumTy t) :=
  mapreduceLinear (· * ·) (JInt.lit _ 1) (v.map widen)

end JuliaLean.ArrayOps


namespace JuliaLean.ReduceCov.Fold

open JuliaLean.Reduce

/-- `reduce(op, a::Number) = a`, `base/reduce.jl:500`. -/
def reduceNumber (a : Val) : Val := a

end JuliaLean.ReduceCov.Fold


/-! Method-specific models for `base/reduce.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.ReduceRows

open JuliaLean.Reduce

/-! Arithmetic reduction operators, lines 16-36. -/

def m16 (add : α → β → γ) (x : α) (y : β) : γ := add x y
def m17 (toInt : α → JInt .i64) (x y : α) : JInt .i64 := toInt x + toInt y
def m18 (toUInt : α → JInt .u64) (x y : α) : JInt .u64 := toUInt x + toUInt y
def m19 (add : α → α → α) (x y : α) : α := add x y
def m27 (mul : α → β → γ) (x : α) (y : β) : γ := mul x y
def m28 (toInt : α → JInt .i64) (x y : α) : JInt .i64 := toInt x * toInt y
def m29 (toUInt : α → JInt .u64) (x y : α) : JInt .u64 := toUInt x * toUInt y
def m30 (mul : α → α → α) (x y : α) : α := mul x y
def m32 (x y : Val) : R Val := Val.andAll x y
def m33 (x y : Val) : R Val := Val.orAny x y
def m35 (x y : Bool) : Bool := x && y
def m36 (x y : Bool) : Bool := x || y

/-! Left folds and transducer wrappers, lines 40-164. -/

def m40 {α β γ δ : Type} (xf : (α → β → β) → List γ → ((α → β → β) × List γ))
    (fold : (α → β → β) → α → List γ → δ) (fop : α → β → β) (init : α) (itr : List γ) : δ :=
  let pair := xf fop itr
  fold pair.1 init pair.2

def m45 (core : α → List β → Option γ) (empty : List β → γ) (op : α) (itr : List β) : γ :=
  match core op itr with | none => empty itr | some value => value

def m51 (op : α → β → α) (init : α) (itr : List β) : α :=
  itr.foldl op init

def m65 (afoldl fallback : (α → β → α) → α → List β → α)
    (op : α → β → α) (init : α) (itr : List β) : α :=
  if itr.length ≤ 32 then afoldl op init itr else fallback op init itr

def m83 (first : (α → α → α) → α → α) (op : α → α → α) (x : α) : α := first op x
def m84 (op : α → α → α) (acc x : α) : α := op acc x

structure Mapping (α β γ : Type) where
  f : α → β
  rf : γ → β → γ

def m94 (f : α → β) (rf : γ → β → γ) : Mapping α β γ := ⟨f, rf⟩
def m95 (f : α → β) (rf : γ → β → γ) : Mapping α β γ := ⟨f, rf⟩
def m98 (op : Mapping α β γ) (acc : γ) (x : α) : γ := op.rf acc (op.f x)
def m110 (pred : β → Bool) (rf : α → β → α) (acc : α) (x : β) : α :=
  if pred x then rf acc x else acc
def m122 {α β : Type} (xf : (α → β → α) → List β → ((α → β → α) × List β))
    (rf : α → β → α) (acc : α) (x : List β) : α :=
  let pair := xf rf x
  m51 pair.1 acc pair.2

def m146 {α β γ δ : Type} (unwrap : α → β × (γ → δ)) (op : γ) (itr : α) : δ × β :=
  let pair := unwrap itr
  (pair.2 op, pair.1)
def m151 {α β : Type} (itr : α) : α × (β → β) := (itr, id)
def m152 {α β γ δ ε ζ : Type} (unwrap : α → β × (γ → δ)) (f : ε → ζ) (isIdentity : Bool) (itr : α) : β × (γ → δ) :=
  let pair := unwrap itr
  if isIdentity then pair else (pair.1, pair.2)
def m157 {α β γ δ : Type} (unwrap : α → β × (γ → δ)) (itr : α) : β × (γ → δ) := unwrap itr
def m161 {α β γ δ : Type} (unwrap : α → β × (γ → δ)) (itr : α) : β × (γ → δ) := unwrap itr

/-! Right-fold routes, lines 200-213. -/

def m200 (xf : (α → α → α) → List β → ((α → α → α) × List β))
    (fold : (α → α → α) → α → List β → γ) (fop : α → α → α)
    (init : α) (itr : List β) : γ := let pair := xf fop itr; fold pair.1 init pair.2
def m206 (reverse : α → β) (itr : α) : β := reverse itr
def m207 (fast slow : List α → List α) (itr : List α) : List α :=
  if itr.length ≤ 32 then fast itr else slow itr
def m213 (f : α → β → γ) (x : β) (y : α) : γ := f y x

/-! Pairwise mapreduce and call routes, lines 252-314, 432-461. -/

def m252 (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat)
    (a : α) (rest : List α) : β := mrImpl f op first blk a rest
def m276 (pairwise : (α → β) → (β → β → β) → Nat) (f : α → β)
    (op : β → β → β) (first : α → β) (a : α) (rest : List α) : β :=
  m252 f op first (pairwise f op) a rest
def m306 (mapfoldl : (α → β) → (β → β → β) → List α → γ)
    (f : α → β) (op : β → β → β) (itr : List α) : γ := mapfoldl f op itr
def m307 (generator : (α → β) → List α → List β) (reduce : (β → β → β) → List β → γ)
    (f : α → β) (op : β → β → β) (itr : List α) : γ := reduce op (generator f itr)
def m311 (_f : α) (_op : β) : Nat := 1024
def m314 (_f : α) (_op : β) : Nat := 4096
def m432 (first : (β → β → β) → β → γ) (f : α → β) (op : β → β → β) (x : α) : γ :=
  first op (f x)
def m434 (style : List α → β) (route : (α → γ) → (γ → γ → γ) → β → List α → δ)
    (f : α → γ) (op : γ → γ → γ) (A : List α) : δ := route f op (style A) A
def m436 (f : α → β) (op : β → β → β) (first : α → β) (empty : R β)
    (blk : Nat) (A : List α) : R β := mapreduceArr f op first empty blk A
def m459 (first : (α → β) → (β → β → β) → α → γ)
    (f : α → β) (op : β → β → β) (a : α) : γ := first f op a
def m461 (mapfoldl : (α → β) → (β → β → β) → List α → γ)
    (f : α → β) (op : β → β → β) (A : List α) : γ := mapfoldl f op A

/-! Empty and first-element methods, lines 318-420. -/

def emptyError : R α := .error .argumentError
def m318 (α : Type) : R α := emptyError
def m320 (α : Type) : R α := emptyError
def m321 (α : Type) : R α := emptyError
def m322 (α : Type) : R α := emptyError
def m342 (zero : τ → α) (T : τ) : α := zero T
def m343 : Int := 0
def m344 (one : τ → α) (T : τ) : α := one T
def m345 : String := ""
def m346 : Bool := true
def m347 : Bool := false
def m348 (α : Type) : Bool := true
def m349 (α : Type) : Bool := false
def m351 (emptyPlus : τ → R α) (T : τ) : R α := emptyPlus T
def m352 : Val := Val.i64 0
def m353 : Val := .int .u64 (JInt.lit .u64 0)
def m354 (emptyTimes : τ → R α) (T : τ) : R α := emptyTimes T
def m355 : Val := Val.i64 1
def m356 : Val := .int .u64 (JInt.lit .u64 1)
def m358 (empty : τ → R α) (T : τ) : R α := empty T
def m359 (mappedEmpty : τ → R α) (T : τ) : R α := mappedEmpty T
def m360 (empty : τ → R α) (T : τ) : R α := empty T
def m361 (empty : τ → R α) (T : τ) : R α := empty T
def m370 (empty : τ → R α) (T : τ) : R α := empty T
def m371 (abs : α → β) (empty : τ → R α) (T : τ) : R β := (empty T).map abs
def m372 (abs2 : α → β) (empty : τ → R α) (T : τ) : R β := (empty T).map abs2
def m374 (zero : τ → α) (abs : α → β) (T : τ) : β := abs (zero T)
def m375 (zero : τ → α) (abs2 : α → β) (T : τ) : β := abs2 (zero T)
def m378 (reduceEmpty : α → β → γ → δ) (mapping : ε → α → α)
    (f : ε) (op : α) (itr : β) (style : γ) : δ := reduceEmpty (mapping f op) itr style
def m381 (style : α → β) (route : γ → α → β → δ) (op : γ) (itr : α) : δ := route op itr (style itr)
def m382 (eltype : α → β) (empty : γ → β → δ) (op : γ) (itr : α) : δ := empty op (eltype itr)
def m389 (empty : α → β → γ) (op : α) (T : β) : γ := empty op T
def m391 (α : Type) : R α := .error .argumentError

def m409 (_op : α) (x : β) : β := x
def m410 (x : Bool) : Int := if x then 1 else 0
def m411 (x : Char) : String := String.singleton x
def m413 (firstPlus : α → β) (x : α) : β := firstPlus x
def m414 (x : Val) : Val := Val.firstAddSum x
def m415 (x : Val) : Val := Val.firstAddSum x
def m416 (firstTimes : α → β) (x : α) : β := firstTimes x
def m417 (x : Val) : Val := Val.firstMulProd x
def m418 (x : Val) : Val := Val.firstMulProd x
def m419 (vcat : α → β) (x : α) : β := vcat x
def m420 (hcat : α → β) (x : α) : β := hcat x

/-! Public reduction wrappers and extrema/search methods. -/

def route2 (call : α → β → γ) (a : α) (b : β) : γ := call a b
def route3 (call : α → β → γ → δ) (a : α) (b : β) (c : γ) : δ := call a b c

def m543 := @route3
def m572 := @route2
def m573 (count reduce : List Bool → α) (hasKw : Bool) (a : List Bool) : α := if hasKw then reduce a else count a
def m599 := @route3
def m628 := @route2
def m656 := @route3
def m683 := @route3
def m715 := @route2
def m747 := @route2
def m776 := @route2
def m806 := @route3

structure ExtremaMap (α β : Type) where f : α → β
def m813 (f : α → β) : ExtremaMap α β := ⟨f⟩
def m814 (f : ExtremaMap α β) (x : α) : β × β := let y := f.f x; (y, y)
def m816 (min max : α → α → α) (a b : α × α) : α × α := (min a.1 b.1, max a.2 b.2)

def m851 (find : (α → β) → List α → γ) (f : α → β) (domain : List α) : γ := find f domain
def m852 (mapfoldl : ((Nat × α) → (β × Nat)) → ((β × Nat) → (β × Nat) → (β × Nat)) →
    List (Nat × α) → γ) (f : α → β) (rf : (β × Nat) → (β × Nat) → (β × Nat))
    (domain : List (Nat × α)) : γ := mapfoldl (fun p => (f p.2, p.1)) rf domain
def m853 (isless : α → α → Bool) (a b : α × β) : α × β := if isless a.1 b.1 then b else a
def m880 (find : List α → α × Nat) (itr : List α) := find itr
def m881 (find : (α → α) → List α → α × Nat) (a : List α) := find id a
def m917 := @m851
def m918 := @m852
def m919 (isgreater : α → α → Bool) (a b : α × β) : α × β := if isgreater a.1 b.1 then b else a
def m946 := @m880
def m947 := @m881
def m973 (mapfoldl : (α → β × α) → ((β × α) → (β × α) → (β × α)) → List α → β × α)
    (f : α → β) (rf : (β × α) → (β × α) → (β × α)) (domain : List α) : α :=
  (mapfoldl (fun x => (f x, x)) rf domain).2
def m1002 (findmax : List α → α × β) (itr : List α) : β := (findmax itr).2
def m1031 := @m973
def m1060 (findmin : List α → α × β) (itr : List α) : β := (findmin itr).2

/-! Count methods, lines 1064-1119. -/

def m1064 (f : α → Bool) : α → Bool := fun x => f x
def m1091 (count : (Bool → Bool) → List Bool → β → γ) (init : β) (itr : List Bool) : γ := count id itr init
def m1093 (simple : (α → Bool) → List α → β → γ) (f : α → Bool) (itr : List α) (init : β) : γ := simple f itr init
def m1095 (sum : (α → Bool) → List α → β → γ) (pred : α → Bool) (itr : List α) (init : β) : γ :=
  sum (m1064 pred) itr init
def m1097 (init : Val) (x : List Bool) : R Val := Vec.countBoolArray init x
def m1117 (op : α → β → α) (init : α) (empty : Bool) (aggregate : β) : α :=
  if empty then init else op init aggregate

end JuliaLean.ReduceCov.ReduceRows

namespace JuliaLean.Reduce

/-- `mapreduce(f, op, A1)` on the view `A1`, which has `IndexCartesian` and so is a
`mapfoldl` (`base/reduce.jl:461`), with `reduce_first(op, x) = x` for `max`/`min`. -/
def foldView (f : Val → R Val) (op : Val → Val → Val) : List Val → R Val
  | [] => .error .argumentError
  | a :: rest => do
    let v ← f a
    rest.foldlM (fun v x => do pure (op v (← f x))) v

/-- `_bool(f)`, `base/reduce.jl:1064`: `f(x)::Bool`. -/
def boolf (f : Val → Val) (x : Val) : R Val :=
  match f x with
  | .bool b => .ok (.bool b)
  | _ => .error .typeError

end JuliaLean.Reduce
