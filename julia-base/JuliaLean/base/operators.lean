import JuliaLean.Core
import JuliaLean.Runtime.Collections
import JuliaLean.base.float
import JuliaLean.base.tuple
import JuliaLean.src.julia_h
import JuliaLean.src.jltypes_c
import JuliaLean.Registry.Types

/-!
# Typed source model of `base/operators.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

Julia dispatch is represented by separate typed definitions. Operations implemented by other Base
files, the runtime, or user-defined types are function parameters; they are called in the order used
by the corresponding Julia method. Where a method calls its own generic function (composition), a
method-selection definition (`maybeconstructor`, `unwrapComposedAny`, `callComposedAny`,
`composeAny`, and `callPlain`/`callCallee` for calling a callable value) picks the method Julia
selects and contains no other behaviour.
-/

namespace JuliaLean.base.operators

open JuliaLean

/-- Field symbols of a `DataType` inspected by `supertype` and `getproperty`. -/
inductive DataTypeSymbol where
  | super
  | name
  | parameters
  deriving DecidableEq, Repr

/-- A `DataType` with a declared supertype and a lazily populated `:super` cache (#61347). -/
structure DataTypeDesc (T : Type) where
  declaredSuper : T
  cachedSuper : Option T
  otherField : DataTypeSymbol → Option T

/-- Model of `ccall(:jl_datatype_compute_super, Ptr{Cvoid}, (Any,), T)`: populates the
deferred `:super` cache from `declaredSuper` if not yet materialized. -/
def jlDatatypeComputeSuper {T : Type} (d : DataTypeDesc T) : DataTypeDesc T :=
  { d with cachedSuper := some (d.cachedSuper.getD d.declaredSuper) }

/-- Model of `getfield(T, s)` on a `DataType`, reading the raw `:super` cache or other field. -/
def getDataTypeField {T : Type} (d : DataTypeDesc T) : DataTypeSymbol → Option T
  | .super => d.cachedSuper
  | s => d.otherField s

/--
Julia source: base/operators.jl:86-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function supertype(T::DataType)
    @_foldable_meta
    # force the computation of a deferred supertype (an instantiation of a
    # self-referential definition materializes its supertype graph lazily,
    # one level per demand, see issue #61347); idempotent, so still foldable.
    # The subsequent plain field read keeps `getfield`'s inference precision.
    ccall(:jl_datatype_compute_super, Ptr{Cvoid}, (Any,), T)
    return getfield(T, :super)
end
```
-/
def supertypeData (computeSuper : α → α) (getSuper : α → β) (t : α) : β :=
  let t := computeSuper t
  getSuper t

/--
Julia source: base/operators.jl:95-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getproperty(T::DataType, s::Symbol)
    @inline
    # fill the deferred supertype cache on access, so raw `.super` reads keep
    # working for instantiations of self-referential definitions (#61347)
    s === :super && return supertype(T)
    return getfield(T, s)
end
```
-/
def getpropertyData (isSuper : σ → Bool) (supertype : α → β)
    (getfield : α → σ → β) (t : α) (s : σ) : β :=
  if isSuper s then supertype t else getfield t s

/--
Julia source: base/operators.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
supertype(T::UnionAll) = (@_foldable_meta; UnionAll(T.var, supertype(T.body)))
```
-/
def supertypeUnionAll (wrap : α → γ → δ) (supertype : β → γ) (var : α) (body : β) : δ :=
  wrap var (supertype body)

/-- A type with zero or more outer `UnionAll` binders around a `DataType` body. -/
inductive UnionAllType (V D : Type) where
  | data (t : D)
  | unionAll (var : V) (body : UnionAllType V D)
  deriving DecidableEq, Repr

/-- Recursive `supertype` dispatch across `UnionAll` binders to `DataType` `supertype`. -/
def supertypeUnionAllChain {V D₁ D₂ : Type} (computeSuper : D₁ → D₁) (getSuper : D₁ → D₂) :
    UnionAllType V D₁ → UnionAllType V D₂
  | .data t => .data (supertypeData computeSuper getSuper t)
  | .unionAll var body =>
      let bodySuper := supertypeUnionAllChain computeSuper getSuper body
      supertypeUnionAll UnionAllType.unionAll (fun _ => bodySuper) var body

/--
Julia source: base/operators.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
supertype(::TypeEq) = Core.AnyType
```
-/
def supertypeTypeEq (_parameter : JuliaLean.C.Val) : JuliaLean.C.Val := JuliaLean.C.anytypeType

/--
Julia source: base/operators.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
supertype(T::Core.TypeEgal) = Type{type_parameter(T)}
```
-/
def supertypeTypeEgal (typeOf : α → β) (parameter : α) : β := typeOf parameter

/--
Julia source: base/operators.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x, y) = (x == y)::Bool # all `missing` cases are handled in missing.jl
```
-/
def isequalDefault (eq : α → β → Bool) (x : α) (y : β) : Bool := eq x y

/-- A unary predicate callable on both operand types `α` and `β` (either a single
predicate `α → Bool` when `α = β`, or a pair `(α → Bool) × (β → Bool)` for distinct types). -/
class UnaryPredPair (P : Type) (α β : Type) where
  onLeft : P → α → Bool
  onRight : P → β → Bool

instance {α : Type} : UnaryPredPair (α → Bool) α α where
  onLeft p x := p x
  onRight p y := p y

instance {α β : Type} : UnaryPredPair ((α → Bool) × (β → Bool)) α β where
  onLeft p x := p.1 x
  onRight p y := p.2 y

@[simp] theorem unaryPredPair_same_left {α : Type} (p : α → Bool) (x : α) :
    UnaryPredPair.onLeft (α := α) (β := α) p x = p x := rfl

@[simp] theorem unaryPredPair_same_right {α : Type} (p : α → Bool) (y : α) :
    UnaryPredPair.onRight (α := α) (β := α) p y = p y := rfl

@[simp] theorem unaryPredPair_pair_left {α β : Type} (p : (α → Bool) × (β → Bool)) (x : α) :
    UnaryPredPair.onLeft (α := α) (β := β) p x = p.1 x := rfl

@[simp] theorem unaryPredPair_pair_right {α β : Type} (p : (α → Bool) × (β → Bool)) (y : β) :
    UnaryPredPair.onRight (α := α) (β := β) p y = p.2 y := rfl

/-- Eager Boolean `&`, evaluating both `Bool` arguments before combining them. -/
def bitAnd (x y : Bool) : Bool :=
  match x, y with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => false

/-- Eager Boolean `|`, evaluating both `Bool` arguments before combining them. -/
def bitOr (x y : Bool) : Bool :=
  match x, y with
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => true

@[simp] theorem bitAnd_eq (x y : Bool) : bitAnd x y = (x && y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem bitOr_eq (x y : Bool) : bitOr x y = (x || y) := by
  cases x <;> cases y <;> rfl

/--
Julia source: base/operators.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signequal(x, y) = signbit(x)::Bool == signbit(y)::Bool
```
-/
def signequal {α β S : Type} [UnaryPredPair S α β] (signbit : S) (x : α) (y : β) : Bool :=
  UnaryPredPair.onLeft (α := α) (β := β) signbit x == UnaryPredPair.onRight (α := α) (β := β) signbit y

/--
Julia source: base/operators.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signless(x, y) = signbit(x)::Bool & !signbit(y)::Bool
```
-/
def signless {α β S : Type} [UnaryPredPair S α β] (signbit : S) (x : α) (y : β) : Bool :=
  let sx := UnaryPredPair.onLeft (α := α) (β := β) signbit x
  let sy := !UnaryPredPair.onRight (α := α) (β := β) signbit y
  bitAnd sx sy

/--
Julia source: base/operators.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x::AbstractFloat, y::AbstractFloat) = (isnan(x) & isnan(y)) | signequal(x, y) & (x == y)::Bool
```
-/
def isequalFloatFloat {α β N S : Type} [UnaryPredPair N α β] [UnaryPredPair S α β]
    (isnan : N) (signbit : S) (eq : α → β → Bool) (x : α) (y : β) : Bool :=
  let nx := UnaryPredPair.onLeft (α := α) (β := β) isnan x
  let ny := UnaryPredPair.onRight (α := α) (β := β) isnan y
  let bothNan := bitAnd nx ny
  let sameSign := signequal signbit x y
  let sameVal := eq x y
  bitOr bothNan (bitAnd sameSign sameVal)

/--
Julia source: base/operators.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x::Real,          y::AbstractFloat) = (isnan(x) & isnan(y)) | signequal(x, y) & (x == y)::Bool
```
-/
def isequalRealFloat (isnanX : α → Bool) (isnanY : β → Bool)
    (signX : α → Bool) (signY : β → Bool) (eq : α → β → Bool)
    (x : α) (y : β) : Bool :=
  let nx := isnanX x
  let ny := isnanY y
  let bothNan := bitAnd nx ny
  let sameSign := signequal (signX, signY) x y
  let sameVal := eq x y
  bitOr bothNan (bitAnd sameSign sameVal)

/--
Julia source: base/operators.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x::AbstractFloat, y::Real         ) = (isnan(x) & isnan(y)) | signequal(x, y) & (x == y)::Bool
```
-/
def isequalFloatReal (isnanX : α → Bool) (isnanY : β → Bool)
    (signX : α → Bool) (signY : β → Bool) (eq : α → β → Bool)
    (x : α) (y : β) : Bool :=
  let nx := isnanX x
  let ny := isnanY y
  let bothNan := bitAnd nx ny
  let sameSign := signequal (signX, signY) x y
  let sameVal := eq x y
  bitOr bothNan (bitAnd sameSign sameVal)

/--
Julia source: base/operators.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::AbstractFloat, y::AbstractFloat) = (!isnan(x) & (isnan(y) | signless(x, y))) | (x < y)
```
-/
def islessFloatFloat {α β N S : Type} [UnaryPredPair N α β] [UnaryPredPair S α β]
    (isnan : N) (signbit : S) (lt : α → β → Bool) (x : α) (y : β) : Bool :=
  let notNanX := !UnaryPredPair.onLeft (α := α) (β := β) isnan x
  let nanY := UnaryPredPair.onRight (α := α) (β := β) isnan y
  let signLt := signless signbit x y
  let ltXY := lt x y
  bitOr (bitAnd notNanX (bitOr nanY signLt)) ltXY

/--
Julia source: base/operators.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::Real,          y::AbstractFloat) = (!isnan(x) & (isnan(y) | signless(x, y))) | (x < y)
```
-/
def islessRealFloat (isnanX : α → Bool) (isnanY : β → Bool)
    (signX : α → Bool) (signY : β → Bool) (lt : α → β → Bool)
    (x : α) (y : β) : Bool :=
  let notNanX := !isnanX x
  let nanY := isnanY y
  let signLt := signless (signX, signY) x y
  let ltXY := lt x y
  bitOr (bitAnd notNanX (bitOr nanY signLt)) ltXY

/--
Julia source: base/operators.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::AbstractFloat, y::Real         ) = (!isnan(x) & (isnan(y) | signless(x, y))) | (x < y)
```
-/
def islessFloatReal (isnanX : α → Bool) (isnanY : β → Bool)
    (signX : α → Bool) (signY : β → Bool) (lt : α → β → Bool)
    (x : α) (y : β) : Bool :=
  let notNanX := !isnanX x
  let nanY := isnanY y
  let signLt := signless (signX, signY) x y
  let ltXY := lt x y
  bitOr (bitAnd notNanX (bitOr nanY signLt)) ltXY

/--
Julia source: base/operators.jl:248-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::Tuple{BitInteger, BitInteger}, b::Tuple{BitInteger, BitInteger}) =
    isless(a[1], b[1]) | (isequal(a[1], b[1]) & isless(a[2], b[2]))
```
-/
def islessPair (ltFirst eqFirst : α → γ → Bool) (ltSecond : β → δ → Bool)
    (a : α × β) (b : γ × δ) : Bool :=
  let firstLt := ltFirst a.1 b.1
  let firstEq := eqFirst a.1 b.1
  let secondLt := ltSecond a.2 b.2
  bitOr firstLt (bitAnd firstEq secondLt)

/--
Julia source: base/operators.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isgreater(x, y) = isunordered(x) || isunordered(y) ? isless(x, y) : isless(y, x)
```
-/
def isgreater (isunorderedX : α → Bool) (isunorderedY : β → Bool)
    (islessXY : α → β → Bool) (islessYX : β → α → Bool) (x : α) (y : β) : Bool :=
  if isunorderedX x || isunorderedY y then islessXY x y else islessYX y x

/--
Julia source: base/operators.jl:309-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isunordered(_) = false
```
-/
def isunordered (_ : α) : Bool := false

/--
Julia source: base/operators.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isunordered(x::AbstractFloat) = isnan(x)
```
-/
def isunorderedFloat (isnan : α → Bool) (x : α) : Bool := isnan x

/--
Julia source: base/operators.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isunordered(::Missing) = true
```
-/
def isunorderedMissing (_ : Unit) : Bool := true

/-- Model of `ccall(:jl_types_equal, Cint, (Any, Any), a, b)` (`src/subtype.c:4110-4190`),
which checks pointer/structural identity, `obviously_unequal`, `jl_obvious_subtype` in both
directions, and full `jl_subtype` in both directions, returning `Cint(1)` or `Cint(0)`. -/
def jlTypesEqual {α : Type} [DecidableEq α]
    (structEquiv obviouslyUnequal : α → α → Bool)
    (obviousSubtype : α → α → Option Bool)
    (subtype : α → α → Bool) (a b : α) : JInt .i32 :=
  if a = b then JInt.lit .i32 1
  else if structEquiv a b then JInt.lit .i32 1
  else if obviouslyUnequal a b then JInt.lit .i32 0
  else
    let ab := match obviousSubtype a b with
      | some res => res
      | none => subtype a b
    if !ab then JInt.lit .i32 0
    else
      let ba := match obviousSubtype b a with
        | some res => res
        | none => subtype b a
      if ab && ba then JInt.lit .i32 1 else JInt.lit .i32 0

/--
Julia source: base/operators.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(T::Type, S::Type) = (@_total_meta; ccall(:jl_types_equal, Cint, (Any, Any), T, S) != 0)
```
-/
def typeEqual (jlTypesEqual : α → β → JInt .i32) (t : α) (s : β) : Bool :=
  jlTypesEqual t s != JInt.lit .i32 0

/--
Julia source: base/operators.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(T::TypeVar, S::Type) = false
```
-/
def typeVarEqual (_ : α) (_ : β) : Bool := false

/--
Julia source: base/operators.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(T::Type, S::TypeVar) = false
```
-/
def typeEqualVar (_ : α) (_ : β) : Bool := false

/--
Julia source: base/operators.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!=(x, y) = !(x == y)
```
-/
def notEqual (eq : α → β → γ) (not : γ → δ) (x : α) (y : β) : δ := not (eq x y)

/--
Julia source: base/operators.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x, y) = isless(x, y)
```
-/
def lessThan (isless : α → β → γ) (x : α) (y : β) : γ := isless x y

/--
Julia source: base/operators.jl:443-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>(x, y) = y < x
```
-/
def greaterThan (less : β → α → γ) (x : α) (y : β) : γ := less y x

/--
Julia source: base/operators.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x, y) = (x < y) | (x == y)
```
-/
def lessEqual (lt : α → β → γ) (eq : α → β → δ) (or : γ → δ → ε)
    (x : α) (y : β) : ε := or (lt x y) (eq x y)

/--
Julia source: base/operators.jl:499-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>=(x, y) = (y <= x)
```
-/
def greaterEqual (le : β → α → γ) (x : α) (y : β) : γ := le y x

/--
Julia source: base/operators.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::Real, y::Real) = x<y
```
-/
def islessReal (lt : α → β → Bool) (x : α) (y : β) : Bool := lt x y

/-- Eager `Core.ifelse(cond, a, b)`, evaluating both branch arguments before selecting. -/
def ifelseValue (cond : Bool) (thenVal elseVal : α) : α :=
  match cond, thenVal, elseVal with
  | true, a, _ => a
  | false, _, b => b

@[simp] theorem ifelseValue_eq (cond : Bool) (thenVal elseVal : α) :
    ifelseValue cond thenVal elseVal = (if cond then thenVal else elseVal) := by
  cases cond <;> rfl

/--
Julia source: base/operators.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)
```
-/
def cmp (islessXY : α → β → Bool) (islessYX : β → α → Bool) (x : α) (y : β) : Int :=
  if islessXY x y then -1 else ifelseValue (islessYX y x) 1 0

/--
Julia source: base/operators.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(<, x, y) = (x < y) ? -1 : ifelse(y < x, 1, 0)
```
-/
def cmpBy (ltXY : α → β → Bool) (ltYX : β → α → Bool) (x : α) (y : β) : Int :=
  if ltXY x y then -1 else ifelseValue (ltYX y x) 1 0

/--
Julia source: base/operators.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(x::Integer, y::Integer) = ifelse(isless(x, y), -1, ifelse(isless(y, x), 1, 0))
```
-/
def cmpInteger (islessXY : α → β → Bool) (islessYX : β → α → Bool) (x : α) (y : β) : Int :=
  let c1 := islessXY x y
  let c2 := islessYX y x
  let inner := ifelseValue c2 1 0
  ifelseValue c1 (-1) inner

/--
Julia source: base/operators.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x, y) = ifelse(isless(y, x), x, y)
```
-/
def max (isless : β → α → Bool) (ifelse : Bool → α → β → γ) (x : α) (y : β) : γ :=
  ifelse (isless y x) x y

/--
Julia source: base/operators.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x,y) = ifelse(isless(y, x), y, x)
```
-/
def min (isless : β → α → Bool) (ifelse : Bool → β → α → γ) (x : α) (y : β) : γ :=
  ifelse (isless y x) y x

/--
Julia source: base/operators.jl:588-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x,y) = isless(y, x) ? (y, x) : (x, y)
```
-/
def minmax (isless : β → α → Bool) (x : α) (y : β) : (α ⊕ β) × (α ⊕ β) :=
  if isless y x then (.inr y, .inl x) else (.inl x, .inr y)
/--
Julia source: base/operators.jl:605-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
identity(@nospecialize x) = x
```
-/
def identity (x : α) : α := x

/--
Julia source: base/operators.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Number) = x
```
-/
def unaryPlusNumber (x : α) : α := x

/--
Julia source: base/operators.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Number) = x
```
-/
def unaryMulNumber (x : α) : α := x

/--
Julia source: base/operators.jl:609-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(x::Integer) = x
```
-/
def unaryAndInteger (x : α) : α := x

/--
Julia source: base/operators.jl:610-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(x::Integer) = x
```
-/
def unaryOrInteger (x : α) : α := x

/--
Julia source: base/operators.jl:611-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(x::Integer) = x
```
-/
def unaryXorInteger (x : α) : α := x

/--
Julia source: base/operators.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
afoldl(op, a) = a
```
-/
def afoldlOne (_op : φ) (a : α) : α := a

/-- One-based tuple element fold step used by `afoldl`, allowing each element type `Elem s`
and accumulator type `Acc t` to vary across steps. -/
def afoldlAt {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (y : Σ t : τ, Acc t) (bs : List (Σ s : σ, Elem s)) (i : Nat) : Σ t : τ, Acc t :=
  match bs[i - 1]? with
  | some b => op y b
  | none => y

/-- Tail loop `for i in start:l` of `afoldl`. -/
def afoldlFrom {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (bs : List (Σ s : σ, Elem s)) (start count : Nat) (y : Σ t : τ, Acc t) : Σ t : τ, Acc t :=
  match count with
  | 0 => y
  | count' + 1 =>
    let y := afoldlAt op y bs start
    afoldlFrom op bs (start + 1) count' y

/--
Julia source: base/operators.jl:623-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function afoldl(op, a, bs...)
    @_terminates_locally_meta
    l = length(bs)
    i =  0; y = a;            l == i && return y
    #@nexprs 31 i -> (y = op(y, bs[i]); l == i && return y)
    i =  1; y = op(y, bs[i]); l == i && return y
    i =  2; y = op(y, bs[i]); l == i && return y
    i =  3; y = op(y, bs[i]); l == i && return y
    i =  4; y = op(y, bs[i]); l == i && return y
    i =  5; y = op(y, bs[i]); l == i && return y
    i =  6; y = op(y, bs[i]); l == i && return y
    i =  7; y = op(y, bs[i]); l == i && return y
    i =  8; y = op(y, bs[i]); l == i && return y
    i =  9; y = op(y, bs[i]); l == i && return y
    i = 10; y = op(y, bs[i]); l == i && return y
    i = 11; y = op(y, bs[i]); l == i && return y
    i = 12; y = op(y, bs[i]); l == i && return y
    i = 13; y = op(y, bs[i]); l == i && return y
    i = 14; y = op(y, bs[i]); l == i && return y
    i = 15; y = op(y, bs[i]); l == i && return y
    i = 16; y = op(y, bs[i]); l == i && return y
    i = 17; y = op(y, bs[i]); l == i && return y
    i = 18; y = op(y, bs[i]); l == i && return y
    i = 19; y = op(y, bs[i]); l == i && return y
    i = 20; y = op(y, bs[i]); l == i && return y
    i = 21; y = op(y, bs[i]); l == i && return y
    i = 22; y = op(y, bs[i]); l == i && return y
    i = 23; y = op(y, bs[i]); l == i && return y
    i = 24; y = op(y, bs[i]); l == i && return y
    i = 25; y = op(y, bs[i]); l == i && return y
    i = 26; y = op(y, bs[i]); l == i && return y
    i = 27; y = op(y, bs[i]); l == i && return y
    i = 28; y = op(y, bs[i]); l == i && return y
    i = 29; y = op(y, bs[i]); l == i && return y
    i = 30; y = op(y, bs[i]); l == i && return y
    i = 31; y = op(y, bs[i]); l == i && return y
    for i in (i + 1):l
        y = op(y, bs[i])
    end
    return y
end
```
-/
def afoldlMany {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (a : Σ t : τ, Acc t) (bs : List (Σ s : σ, Elem s)) : Σ t : τ, Acc t :=
  let l := bs.length
  let i := 0; let y := a; if l == i then y else
  let i := 1; let y := afoldlAt op y bs i; if l == i then y else
  let i := 2; let y := afoldlAt op y bs i; if l == i then y else
  let i := 3; let y := afoldlAt op y bs i; if l == i then y else
  let i := 4; let y := afoldlAt op y bs i; if l == i then y else
  let i := 5; let y := afoldlAt op y bs i; if l == i then y else
  let i := 6; let y := afoldlAt op y bs i; if l == i then y else
  let i := 7; let y := afoldlAt op y bs i; if l == i then y else
  let i := 8; let y := afoldlAt op y bs i; if l == i then y else
  let i := 9; let y := afoldlAt op y bs i; if l == i then y else
  let i := 10; let y := afoldlAt op y bs i; if l == i then y else
  let i := 11; let y := afoldlAt op y bs i; if l == i then y else
  let i := 12; let y := afoldlAt op y bs i; if l == i then y else
  let i := 13; let y := afoldlAt op y bs i; if l == i then y else
  let i := 14; let y := afoldlAt op y bs i; if l == i then y else
  let i := 15; let y := afoldlAt op y bs i; if l == i then y else
  let i := 16; let y := afoldlAt op y bs i; if l == i then y else
  let i := 17; let y := afoldlAt op y bs i; if l == i then y else
  let i := 18; let y := afoldlAt op y bs i; if l == i then y else
  let i := 19; let y := afoldlAt op y bs i; if l == i then y else
  let i := 20; let y := afoldlAt op y bs i; if l == i then y else
  let i := 21; let y := afoldlAt op y bs i; if l == i then y else
  let i := 22; let y := afoldlAt op y bs i; if l == i then y else
  let i := 23; let y := afoldlAt op y bs i; if l == i then y else
  let i := 24; let y := afoldlAt op y bs i; if l == i then y else
  let i := 25; let y := afoldlAt op y bs i; if l == i then y else
  let i := 26; let y := afoldlAt op y bs i; if l == i then y else
  let i := 27; let y := afoldlAt op y bs i; if l == i then y else
  let i := 28; let y := afoldlAt op y bs i; if l == i then y else
  let i := 29; let y := afoldlAt op y bs i; if l == i then y else
  let i := 30; let y := afoldlAt op y bs i; if l == i then y else
  let i := 31; let y := afoldlAt op y bs i; if l == i then y else
  afoldlFrom op bs (i + 1) (l - i) y

/--
Julia source: base/operators.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(a, b, c, xs...) = (@inline; afoldl($op, ($op)(($op)(a,b),c), xs...))
```
-/
def naryOperator {τ σ α β γ δ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (opAB : α → β → δ) (opABC : δ → γ → Σ t₀ : τ, Acc t₀)
    (opRest : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (a : α) (b : β) (c : γ) (xs : List (Σ s : σ, Elem s)) : Σ t : τ, Acc t :=
  afoldlMany opRest (opABC (opAB a b) c) xs

/--
Julia source: base/operators.jl:709-709 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
\(x,y) = adjoint(adjoint(y)/adjoint(x))
```
-/
def leftDiv {μ : Type → Type} [Monad μ]
    (adjointX : α → μ α') (adjointY : β → μ β')
    (divide : β' → α' → μ γ) (adjointOut : γ → μ δ) (x : α) (y : β) : μ δ := do
  let ay ← adjointY y
  let ax ← adjointX x
  let quotient ← divide ay ax
  adjointOut quotient

/--
Julia source: base/operators.jl:735-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function <<(x::Integer, c::Integer)
    @inline
    typemin(Int) <= c <= typemax(Int) && return x << (c % Int)
    (x >= 0 || c >= 0) && return zero(x) << 0  # for type stability
    oftype(x, -1)
end
```
-/
def shiftLeftInteger (inIntRange : β → Bool) (remInt : β → γ)
    (shiftInt : α → γ → α) (zero : α → α) (zeroCount : γ)
    (ofType : α → Int → α) (nonnegativeX : α → Bool) (nonnegativeC : β → Bool)
    (x : α) (c : β) : α :=
  if inIntRange c then shiftInt x (remInt c)
  else if nonnegativeX x || nonnegativeC c then shiftInt (zero x) zeroCount
  else ofType x (-1)

/--
Julia source: base/operators.jl:741-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function <<(x::Integer, c::Unsigned)
    @inline
    if c isa UInt
        throw(MethodError(<<, (x, c)))
    end
    c <= typemax(UInt) ? x << (c % UInt) : zero(x) << UInt(0)
end
```
-/
def shiftLeftUnsigned (isUInt : Bool) (maxUInt : Nat)
    (toUInt : Nat → Nat) (shiftUInt : α → Nat → α) (zero : α → α)
    (x : α) (c : Nat) : Jl α :=
  if isUInt then .error (.methodError "<<")
  else if c ≤ maxUInt then .ok (shiftUInt x (toUInt c))
  else .ok (shiftUInt (zero x) 0)

/--
Julia source: base/operators.jl:748-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<<(x::Integer, c::Int) = c >= 0 ? x << unsigned(c) : x >> unsigned(-c)
```
-/
def shiftLeftInt (toUnsigned : Int → β) (shiftLeft shiftRight : α → β → α)
    (x : α) (c : Int) : α :=
  if c >= 0 then shiftLeft x (toUnsigned c) else shiftRight x (toUnsigned (-c))

/--
Julia source: base/operators.jl:780-788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function >>(x::Integer, c::Integer)
    @inline
    if c isa UInt
        throw(MethodError(>>, (x, c)))
    end
    typemin(Int) <= c <= typemax(Int) && return x >> (c % Int)
    (x >= 0 || c < 0) && return zero(x) >> 0
    oftype(x, -1)
end
```
-/
def shiftRightInteger (isUInt : Bool) (inIntRange : β → Bool) (remInt : β → γ)
    (shiftInt : α → γ → α) (zero : α → α) (zeroCount : γ)
    (ofType : α → Int → α) (nonnegativeX : α → Bool) (negativeC : β → Bool)
    (x : α) (c : β) : Jl α :=
  if isUInt then .error (.methodError ">>")
  else if inIntRange c then .ok (shiftInt x (remInt c))
  else if nonnegativeX x || negativeC c then .ok (shiftInt (zero x) zeroCount)
  else .ok (ofType x (-1))

/--
Julia source: base/operators.jl:789-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>(x::Integer, c::Int) = c >= 0 ? x >> unsigned(c) : x << unsigned(-c)
```
-/
def shiftRightInt (toUnsigned : Int → β) (shiftRight shiftLeft : α → β → α)
    (x : α) (c : Int) : α :=
  if c >= 0 then shiftRight x (toUnsigned c) else shiftLeft x (toUnsigned (-c))

/--
Julia source: base/operators.jl:818-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function >>>(x::Integer, c::Integer)
    @inline
    typemin(Int) <= c <= typemax(Int) ? x >>> (c % Int) : zero(x) >>> 0
end
```
-/
def shiftLogicalInteger (inIntRange : β → Bool) (remInt : β → γ)
    (shiftInt : α → γ → α) (zero : α → α) (zeroCount : γ)
    (x : α) (c : β) : α :=
  if inIntRange c then shiftInt x (remInt c) else shiftInt (zero x) zeroCount

/--
Julia source: base/operators.jl:822-828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function >>>(x::Integer, c::Unsigned)
    @inline
    if c isa UInt
        throw(MethodError(>>>, (x, c)))
    end
    c <= typemax(UInt) ? x >>> (c % UInt) : zero(x) >>> 0
end
```
-/
def shiftLogicalUnsigned (isUInt : Bool) (maxUInt : Nat) (toUInt : Nat → Nat)
    (shiftUInt : α → Nat → α) (zero : α → α) (x : α) (c : Nat) : Jl α :=
  if isUInt then .error (.methodError ">>>")
  else if c ≤ maxUInt then .ok (shiftUInt x (toUInt c))
  else .ok (shiftUInt (zero x) 0)

/--
Julia source: base/operators.jl:829-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>>(x::Integer, c::Int) = c >= 0 ? x >>> unsigned(c) : x << unsigned(-c)
```
-/
def shiftLogicalInt (toUnsigned : Int → β) (shiftLogical shiftLeft : α → β → α)
    (x : α) (c : Int) : α :=
  if c >= 0 then shiftLogical x (toUnsigned c) else shiftLeft x (toUnsigned (-c))

/--
Julia source: base/operators.jl:914-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod1(x::T, y::T) where {T<:Real} = (m = mod(x, y); iszero(m) ? y : m)
```
-/
def mod1 {m : Type → Type} [Monad m] {P : Type}
    (mod : α → α → m β) (iszero : β → m P) (assertBool : P → m Bool)
    (x y : α) : m (α ⊕ β) := do
  let remainder ← mod x y
  if ← assertBool (← iszero remainder) then pure (.inl y)
  else pure (.inr remainder)

/--
Julia source: base/operators.jl:943-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cldmod1(x, y) = (cld(x, y), mod1(x, y))
```
-/
def cldmod1 (cld : α → β → Jl γ) (mod1 : α → β → Jl δ)
    (x : α) (y : β) : Jl (γ × δ) := do
  let quotient ← cld x y
  let remainder ← mod1 x y
  pure (quotient, remainder)

/--
Julia source: base/operators.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fldmod1(x, y) = (fld1(x, y), mod1(x, y))
```
-/
def fldmod1 (fld1 : α → β → Jl γ) (mod1 : α → β → Jl δ)
    (x : α) (y : β) : Jl (γ × δ) := do
  let quotient ← fld1 x y
  let remainder ← mod1 x y
  pure (quotient, remainder)

/--
Julia source: base/operators.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(x::T) where {T} = convert(widen(T), x)
```
-/
def widenValue (widenType : α → β) (convert : β → α → γ) (typeOf : α → α) (x : α) : γ :=
  convert (widenType (typeOf x)) x
/--
Julia source: base/operators.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(x::Type{T}) where {T} = throw(MethodError(widen, (T,)))
```
-/
def widenTypeError (methodError : α → Jl β) (typeParameter : α) : Jl β :=
  methodError typeParameter

/--
Julia source: base/operators.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(x::Type{Union{}}, slurp...) = throw(MethodError(widen, (Union{},)))
```
-/
def widenBottomError {α β σ : Type} (methodError : JuliaLean.C.Val → Jl β) (_x : α)
    (_slurp : List σ) : Jl β :=
  methodError JuliaLean.C.Val.bottom

/--
Julia source: base/operators.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
|>(x, f) = f(x)
```
-/
def pipe (x : α) (f : α → β) : β := f x

/--
Julia source: base/operators.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_stable_typeof(x) = typeof(x)
```
-/
def stableTypeof (typeOf : α → β) (x : α) : β := typeOf x

/--
Julia source: base/operators.jl:1004-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_stable_typeof(::Type{T}) where {T} = @isdefined(T) && !Core.has_free_typevars(T) ? Type{T} : DataType
```
-/
-- Source: base/operators.jl:1004-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _stable_typeof(::Type{T}) where {T} = @isdefined(T) && !Core.has_free_typevars(T) ? Type{T} : DataType
-- /Source
def stableTypeofType (isDefined hasFreeTypevars : α → Bool)
    (typeTag : α → β) (dataType : β) (t : α) : β :=
  if isDefined t then
    if !hasFreeTypevars t then typeTag t else dataType
  else dataType

/-- The typed and stable `Returns` constructors store the returned value. -/
structure Returns (Tag Value : Type) where
  typeParam : Tag
  value : Value

/--
Julia source: base/operators.jl:1031-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Returns{V}(value) where {V} = new{V}(value)
```
-/
def returnsTyped {τ V α : Type} (convert : τ → α → Jl V) (typeParam : τ) (value : α) :
    Jl (Returns τ V) := do
  let v ← convert typeParam value
  pure ⟨typeParam, v⟩

/--
Julia source: base/operators.jl:1032-1032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Returns(value) = new{_stable_typeof(value)}(value)
```
-/
def returnsStable (typeOf : α → β) (value : α) : Returns β α :=
  ⟨typeOf value, value⟩

/--
Julia source: base/operators.jl:1035-1035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(obj::Returns)(@nospecialize(args...); @nospecialize(kw...)) = obj.value
```
-/
def returnsCall (r : Returns tag α) (_args : List β) (_kw : κ) : Jl α := pure r.value

/-- A composed function stores outer then inner, matching its Julia fields. -/
structure ComposedFunction (Outer Inner : Type) where
  outer : Outer
  inner : Inner

/--
Julia source: base/operators.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ComposedFunction{O, I}(outer, inner) where {O, I} = new{O, I}(outer, inner)
```
-/
def composedTyped {O I α β : Type} (convertOuter : α → Jl O) (convertInner : β → Jl I)
    (outer : α) (inner : β) : Jl (ComposedFunction O I) := do
  let o ← convertOuter outer
  let i ← convertInner inner
  pure ⟨o, i⟩

/--
Julia source: base/operators.jl:1122-1122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ComposedFunction(outer, inner) = new{Core.Typeof(outer),Core.Typeof(inner)}(outer, inner)
```
-/
def composed (outer : α) (inner : β) : ComposedFunction α β := ⟨outer, inner⟩

/-- `Constructor{F}`: the callable adapter of the type object `F`. -/
structure Constructor (T : Type) where
  type : T

/--
Julia source: base/operators.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Constructor{F})(args...; kw...) where {F} = (@inline; F(args...; kw...))
```
-/
def constructorCall {T A K R : Type} (construct : T → A → K → R) (c : Constructor T)
    (args : A) (kw : K) : R :=
  construct c.type args kw

/--
Julia source: base/operators.jl:1133-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybeconstructor(::Type{F}) where {F} = Constructor{F}()
```
-/
def maybeConstructorType {T : Type} (t : T) : Constructor T := ⟨t⟩

/--
Julia source: base/operators.jl:1134-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybeconstructor(f) = f
```
-/
def maybeConstructorValue (f : α) : α := f

/-- A callable value that is not a `ComposedFunction`: a callable object `f : F` whose methods
are defined in other files or by users, a type object `t : T`, or a `Constructor{F}` adapter. -/
inductive PlainCallable (F T : Type) where
  | fn (f : F)
  | type (t : T)
  | ctor (c : Constructor T)

/-- A callable value passed to `∘`: a plain callable or a `ComposedFunction` of callables.
Julia selects the `unwrap_composed` method by this distinction. -/
inductive Callee (F T : Type) where
  | plain (p : PlainCallable F T)
  | composed (c : ComposedFunction (Callee F T) (Callee F T))

/-- The call methods of plain callables, defined outside this file: `callFn f args kw` is
`f(args...; kw...)` for a callable object and `callType t args kw` is `T(args...; kw...)` for
a type object. Values `V` and keyword names `σ` are arbitrary; keywords are name/value pairs. -/
structure CallMethods (F T V σ : Type) where
  callFn : F → List V → List (σ × V) → Jl V
  callType : T → List V → List (σ × V) → Jl V

/-- Julia's method selection for `maybeconstructor`: a type object selects
`maybeconstructor(::Type{F})`, every other callable `maybeconstructor(f)`. -/
def maybeconstructor {F T : Type} : PlainCallable F T → PlainCallable F T
  | .type t => .ctor (maybeConstructorType t)
  | p => maybeConstructorValue p

/--
Julia source: base/operators.jl:1127-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unwrap_composed(c) = (maybeconstructor(c),)
```
-/
def unwrapCallable {F T : Type} (c : PlainCallable F T) : List (PlainCallable F T) :=
  [maybeconstructor c]

mutual
  /-- Julia's method selection for `unwrap_composed`: a `ComposedFunction` selects
  `unwrap_composed(c::ComposedFunction)`, every other callable `unwrap_composed(c)`. -/
  def unwrapComposedAny {F T : Type} : Callee F T → List (PlainCallable F T)
    | .plain p => unwrapCallable p
    | .composed c => unwrapComposed c

/--
Julia source: base/operators.jl:1126-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unwrap_composed(c::ComposedFunction) = (unwrap_composed(c.outer)..., unwrap_composed(c.inner)...)
```
-/
  -- Source: base/operators.jl:1126-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
  -- unwrap_composed(c::ComposedFunction) = (unwrap_composed(c.outer)..., unwrap_composed(c.inner)...)
  -- /Source
  def unwrapComposed {F T : Type} :
      ComposedFunction (Callee F T) (Callee F T) → List (PlainCallable F T)
    | c => unwrapComposedAny c.outer ++ unwrapComposedAny c.inner
end

/-- Julia's call `p(args...; kw...)` of a plain callable: the callable's own method, the
type's constructor, or the `Constructor{F}` call method. -/
def callPlain {F T V σ : Type} (m : CallMethods F T V σ) :
    PlainCallable F T → List V → List (σ × V) → Jl V
  | .fn f, args, kw => m.callFn f args kw
  | .type t, args, kw => m.callType t args kw
  | .ctor c, args, kw => constructorCall m.callType c args kw

/--
Julia source: base/operators.jl:1129-1129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
call_composed(fs::Tuple{Any}, x, kw) = fs[1](x...; kw...)
```
-/
def callComposedOne {F T V σ : Type} (m : CallMethods F T V σ) (f : PlainCallable F T)
    (x : List V) (kw : List (σ × V)) : Jl V :=
  callPlain m f x kw

mutual
  /-- Julia's method selection for `call_composed`: a one-element tuple selects
  `call_composed(fs::Tuple{Any}, x, kw)`, every other tuple `call_composed(fs, x, kw)`. -/
  def callComposedAny {F T V σ : Type} (m : CallMethods F T V σ) :
      List (PlainCallable F T) → List V → List (σ × V) → Jl V
    | [f], x, kw => callComposedOne m f x kw
    | fs, x, kw => callComposed m fs x kw
  termination_by fs => 2 * fs.length + 2

/--
Julia source: base/operators.jl:1128-1128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
call_composed(fs, x, kw) = (@inline; fs[1](call_composed(tail(fs), x, kw)))
```
-/
  -- Source: base/operators.jl:1128-1128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
  -- call_composed(fs, x, kw) = (@inline; fs[1](call_composed(tail(fs), x, kw)))
  -- /Source
  def callComposed {F T V σ : Type} (m : CallMethods F T V σ)
      (fs : List (PlainCallable F T)) (x : List V) (kw : List (σ × V)) : Jl V :=
    match fs with
    | [] => .error .boundsError
    | f :: rest => do
        let v ← callComposedAny m rest x kw
        callPlain m f [v] []
  termination_by 2 * fs.length + 1
end

/--
Julia source: base/operators.jl:1125-1125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(c::ComposedFunction)(x...; kw...) = call_composed(unwrap_composed(c), x, kw)
```
-/
def composedCall {F T V σ : Type} (m : CallMethods F T V σ)
    (c : ComposedFunction (Callee F T) (Callee F T)) (x : List V) (kw : List (σ × V)) : Jl V :=
  callComposedAny m (unwrapComposed c) x kw

/-- Julia's call `f(args...; kw...)` of any callable in a composition: a plain callable uses
`callPlain`, a `ComposedFunction` its call method `(c::ComposedFunction)(x...; kw...)`. -/
def callCallee {F T V σ : Type} (m : CallMethods F T V σ) :
    Callee F T → List V → List (σ × V) → Jl V
  | .plain p, x, kw => callPlain m p x kw
  | .composed c, x, kw => composedCall m c x kw

/--
Julia source: base/operators.jl:1136-1136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∘(f) = f
```
-/
def composeOne (f : α) : α := f

/--
Julia source: base/operators.jl:1137-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∘(f, g) = ComposedFunction(f, g)
```
-/
def composeTwo (f : α) (g : β) : ComposedFunction α β := composed f g

mutual
  /-- Julia's method selection for `∘` by argument count: no method for zero arguments,
  then `∘(f)`, `∘(f, g)`, and `∘(f, g, h...)` for three or more callables. -/
  def composeAny {F T : Type} : List (Callee F T) → Jl (Callee F T)
    | [] => .error (.methodError "∘")
    | [f] => .ok (composeOne f)
    | [f, g] => .ok (.composed (composeTwo f g))
    | f :: g :: h :: hs => composeMany f g (h :: hs)
  termination_by fs => 2 * fs.length

/--
Julia source: base/operators.jl:1138-1138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∘(f, g, h...) = ∘(f ∘ g, h...)
```
-/
  -- Source: base/operators.jl:1138-1138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
  -- ∘(f, g, h...) = ∘(f ∘ g, h...)
  -- /Source
  def composeMany {F T : Type} (f g : Callee F T) (h : List (Callee F T)) : Jl (Callee F T) :=
    composeAny (.composed (composeTwo f g) :: h)
  termination_by 2 * h.length + 3
end

/-- Heterogeneous tuple whose element types are indexed by `Elem : τ → Type`. -/
inductive HTuple {τ : Type} (Elem : τ → Type) : List τ → Type where
  | nil : HTuple Elem []
  | cons {t : τ} {ts : List τ} (head : Elem t) (tail : HTuple Elem ts) :
      HTuple Elem (t :: ts)

/--
Julia source: base/operators.jl:1140-1144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, c::ComposedFunction)
    c.outer isa ComposedFunction ? show(io, c.outer) : _showcomposed(io, c.outer)
    print(io, " ∘ ")
    _showcomposed(io, c.inner)
end
```
-/
def showComposed {IO α β : Type} (isComposed : α → Bool)
    (showComposedOuter showOuter : IO → α → Jl IO)
    (print : IO → String → Jl IO)
    (showInner : IO → β → Jl IO)
    (io : IO) (c : ComposedFunction α β) : Jl IO := do
  let io ← if isComposed c.outer then showComposedOuter io c.outer else showOuter io c.outer
  let io ← print io " ∘ "
  showInner io c.inner

/--
Julia source: base/operators.jl:1147-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, c::ComposedFunction{typeof(!)})
    print(io, '!')
    _showcomposed(io, c.inner)
end
```
-/
def showNegatedComposed {IO α β : Type}
    (printChar : IO → Char → Jl IO)
    (showPart : IO → β → Jl IO)
    (io : IO) (c : ComposedFunction α β) : Jl IO := do
  let io ← printChar io '!'
  showPart io c.inner

/--
Julia source: base/operators.jl:1152-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_showcomposed(io::IO, x) = show(io, x)
```
-/
def showComposedDefault {IO α : Type} (showVal : IO → α → Jl IO) (io : IO) (x : α) : Jl IO :=
  showVal io x

/--
Julia source: base/operators.jl:1154-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_showcomposed(io::IO, f::Function) = isoperator(Symbol(f)) ? (print(io, '('); show(io, f); print(io, ')')) : show(io, f)
```
-/
def showComposedFunction {IO α σ : Type}
    (symbolOf : α → σ) (isOperator : σ → Bool)
    (printChar : IO → Char → Jl IO) (showFn : IO → α → Jl IO)
    (io : IO) (f : α) : Jl IO :=
  if isOperator (symbolOf f) then do
    let io ← printChar io '('
    let io ← showFn io f
    printChar io ')'
  else
    showFn io f

/--
Julia source: base/operators.jl:1156-1156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_showcomposed(io::IO, f::ComposedFunction) = (print(io, '('); show(io, f); print(io, ')'))
```
-/
def showNestedComposed {IO α β : Type}
    (printChar : IO → Char → Jl IO)
    (showComp : IO → ComposedFunction α β → Jl IO)
    (io : IO) (f : ComposedFunction α β) : Jl IO := do
  let io ← printChar io '('
  let io ← showComp io f
  printChar io ')'

/--
Julia source: base/operators.jl:1158-1158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_showcomposed(io::IO, f::ComposedFunction{typeof(!)}) = show(io, f)
```
-/
def showNestedNegatedComposed {IO α β : Type}
    (showNegComp : IO → ComposedFunction α β → Jl IO)
    (io : IO) (f : ComposedFunction α β) : Jl IO :=
  showNegComp io f
/--
Julia source: base/operators.jl:1182-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!(f::Function) = (!) ∘ f
```
-/
def negateFunction (notFunction : α) (f : β) : ComposedFunction α β :=
  composeTwo notFunction f

/--
Julia source: base/operators.jl:1183-1183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!(f::ComposedFunction{typeof(!)}) = f.inner #allows !!f === f
```
-/
def doubleNegatedComposition (f : ComposedFunction α β) : β := f.inner

/-- Operator identity tag carried in `Fix2{typeof(op), _stable_typeof(x)}`. -/
inductive Fix2OpTag where
  | isequal
  | eq
  | ne
  | ge
  | le
  | gt
  | lt
  | inOp
  | notIn
  | contains
  | notContains
  deriving DecidableEq, Repr

structure Fix (N : Nat) (F T : Type) {FT XT : Type} (fTag : FT) (xTag : XT) where
  f : F
  x : T

def fixPosition {N : Nat} {F T FT XT : Type} {fTag : FT} {xTag : XT}
    (_ : Fix N F T fTag xTag) : Nat := N

def fixFunctionTag {N : Nat} {F T FT XT : Type} {fTag : FT} {xTag : XT}
    (_ : Fix N F T fTag xTag) : FT := fTag

def fixValueTag {N : Nat} {F T FT XT : Type} {fTag : FT} {xTag : XT}
    (_ : Fix N F T fTag xTag) : XT := xTag

/--
Julia source: base/operators.jl:1206-1213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Fix{N}(f::F, x) where {N,F}
        if !(N isa Int)
            throw(ArgumentError(LazyString("expected type parameter in `Fix` to be `Int`, but got `", N, "::", typeof(N), "`")))
        elseif N < 1
            throw(ArgumentError(LazyString("expected `N` in `Fix{N}` to be integer greater than 0, but got ", N)))
        end
        new{N,_stable_typeof(f),_stable_typeof(x)}(f, x)
    end
```
-/
def makeFix {F T σ τ : Type} (isInt : Bool) (n : Int) (showInt typeName : Int → String)
    (toNat : Int → Nat) (stableTypeFunction : F → σ)
    (stableTypeValue : T → τ)
    (f : F) (x : T) : Jl (Fix (toNat n) F T (stableTypeFunction f) (stableTypeValue x)) :=
  if !isInt then
    .error (.argumentError
      ("expected type parameter in `Fix` to be `Int`, but got `" ++ showInt n ++ "::" ++ typeName n ++ "`"))
  else if n < 1 then
    .error (.argumentError
      ("expected `N` in `Fix{N}` to be integer greater than 0, but got " ++ showInt n))
  else
    .ok ⟨f, x⟩

/--
Julia source: base/operators.jl:1216-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (f::Fix{N})(args::Vararg{Any,M}; kws...) where {N,M}
    M < N-1 && throw(ArgumentError(LazyString("expected at least ", N-1, " arguments to `Fix{", N, "}`, but got ", M)))
    (left, right) = _split_tuple(args, N-1)
    return f.f(left..., f.x, right...; kws...)
end
```
-/
def fixCall {N : Nat} {τ β κ FT XT : Type} {Elem : τ → Type} {tx : τ} {fTag : FT} {xTag : XT}
    (splitTuple : List (Σ t : τ, Elem t) → Nat →
      JuliaLean.base.tuple.R (List (Σ t : τ, Elem t) × List (Σ t : τ, Elem t)))
    (fix : Fix N (List (Σ t : τ, Elem t) → κ → β) (Elem tx) fTag xTag)
    (args : List (Σ t : τ, Elem t)) (kw : κ) : JuliaLean.base.tuple.R β :=
  if args.length < N - 1 then
    .error (.julia (.argumentError
      ("expected at least " ++ toString (N - 1) ++ " arguments to `Fix{" ++
        toString N ++ "}`, but got " ++ toString args.length)))
  else do
    let (left, right) ← splitTuple args (N - 1)
    pure (fix.f (left ++ [⟨tx, fix.x⟩] ++ right) kw)

/--
Julia source: base/operators.jl:1223-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(f::Fix{1})(arg; kws...) = f.f(f.x, arg; kws...)
```
-/
def fixOneCall {α β γ κ FT XT : Type} {fTag : FT} {xTag : XT}
    (fix : Fix 1 (α → β → κ → γ) α fTag xTag) (arg : β) (kw : κ) : γ :=
  fix.f fix.x arg kw

/--
Julia source: base/operators.jl:1224-1224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(f::Fix{2})(arg; kws...) = f.f(arg, f.x; kws...)
```
-/
def fixTwoCall {α β γ κ FT XT : Type} {fTag : FT} {xTag : XT}
    (fix : Fix 2 (α → β → κ → γ) β fTag xTag) (arg : α) (kw : κ) : γ :=
  fix.f arg fix.x kw

/--
Julia source: base/operators.jl:1226-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, fix::Fix{N}) where {N}
    constr = Fix{N}
    callable = fix.f
    fixed_argument = fix.x
    show(io, constr)
    print(io, '(')
    show(io, callable)
    print(io, ',')
    print(io, ' ')
    show(io, fixed_argument)
    print(io, ')')
end
```
-/
def showFix {IO : Type} {N : Nat} {F T FT XT : Type} {fTag : FT} {xTag : XT}
    (showConstructor : IO → Nat → Jl IO)
    (printChar : IO → Char → Jl IO)
    (showFunction : IO → F → Jl IO)
    (showValue : IO → T → Jl IO)
    (io : IO) (fix : Fix N F T fTag xTag) : Jl IO := do
  let constr := N
  let callable := fix.f
  let fixed_argument := fix.x
  let io ← showConstructor io constr
  let io ← printChar io '('
  let io ← showFunction io callable
  let io ← printChar io ','
  let io ← printChar io ' '
  let io ← showValue io fixed_argument
  printChar io ')'
/--
Julia source: base/operators.jl:1259-1259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x) = Fix2(isequal, x)
```
-/
def fixIsequal {α β γ : Type} (isequal : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.isequal x :=
  ⟨fun a b _ => isequal a b, x⟩

/--
Julia source: base/operators.jl:1270-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x) = Fix2(==, x)
```
-/
def fixEqual {α β γ : Type} (eq : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.eq x :=
  ⟨fun a b _ => eq a b, x⟩

/--
Julia source: base/operators.jl:1283-1283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!=(x) = Fix2(!=, x)
```
-/
def fixNotEqual {α β γ : Type} (ne : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.ne x :=
  ⟨fun a b _ => ne a b, x⟩

/--
Julia source: base/operators.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>=(x) = Fix2(>=, x)
```
-/
def fixGreaterEqual {α β γ : Type} (ge : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.ge x :=
  ⟨fun a b _ => ge a b, x⟩

/--
Julia source: base/operators.jl:1309-1309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x) = Fix2(<=, x)
```
-/
def fixLessEqual {α β γ : Type} (le : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.le x :=
  ⟨fun a b _ => le a b, x⟩

/--
Julia source: base/operators.jl:1322-1322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>(x) = Fix2(>, x)
```
-/
def fixGreater {α β γ : Type} (gt : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.gt x :=
  ⟨fun a b _ => gt a b, x⟩

/--
Julia source: base/operators.jl:1335-1335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x) = Fix2(<, x)
```
-/
def fixLess {α β γ : Type} (lt : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.lt x :=
  ⟨fun a b _ => lt a b, x⟩

/-- A `Splat{F}` value wraps an arbitrary callable `f : F`. -/
structure Splat (F : Type) where
  f : F

/--
Julia source: base/operators.jl:1366-1366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
splat(f) = Splat(f)
```
-/
def splat {F : Type} (makeSplat : F → Splat F) (f : F) : Splat F := makeSplat f

/--
Julia source: base/operators.jl:1384-1384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Splat(f) = new{Core.Typeof(f)}(f)
```
-/
def makeSplat {F : Type} (f : F) : Splat F := ⟨f⟩

/--
Julia source: base/operators.jl:1386-1386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(s::Splat)(args) = s.f(args...)
```
-/
def splatCall {F α β : Type} (applySplatted : F → α → β) (s : Splat F) (args : α) : β :=
  applySplatted s.f args

/--
Julia source: base/operators.jl:1387-1387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::Splat) = (print(io, "splat("); show(io, s.f); print(io, ")"))
```
-/
def showSplat {IO F : Type}
    (print : IO → String → Jl IO)
    (showFunction : IO → F → Jl IO)
    (io : IO) (s : Splat F) : Jl IO := do
  let io ← print io "splat("
  let io ← showFunction io s.f
  print io ")"
/--
Julia source: base/operators.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsplat(f) = f ∘ tuple
```
-/
def unsplatGeneric (tuple : β) (f : α) : ComposedFunction α β :=
  composeTwo f tuple

/--
Julia source: base/operators.jl:1416-1416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsplat(s::Splat) = s.f
```
-/
def unsplatSplat {F : Type} (s : Splat F) : F := s.f

/-- Type tag for Julia's `typeof(tuple)` dispatch. -/
inductive TupleFunction where
  | tuple

/--
Julia source: base/operators.jl:1417-1417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
splat(f::ComposedFunction{<:Any,typeof(tuple)}) = f.outer
```
-/
-- Source: base/operators.jl:1417-1417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- splat(f::ComposedFunction{<:Any,typeof(tuple)}) = f.outer
-- /Source
def splatComposed (f : ComposedFunction α TupleFunction) : α := f.outer

/--
Julia source: base/operators.jl:1438-1438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tap(f) = x -> (f(x); x)
```
-/
def tap [Monad m] (f : α → m β) : α → m α := fun x => do
  let _ ← f x
  pure x

/-- Three-valued truth used for generic membership equality results. -/
inductive Truth where
  | false
  | missing
  | true
  deriving Repr, BEq, DecidableEq

/-- Kleene negation used by `∉` and `∌`. -/
def Truth.not : Truth → Truth
  | .false => .true
  | .missing => .missing
  | .true => .false

/-- Kleene disjunction used by `any` and `_in_tuple`. -/
def Truth.or : Truth → Truth → Truth
  | .true, _ => .true
  | _, .true => .true
  | .missing, _ => .missing
  | _, .missing => .missing
  | .false, .false => .false

/--
Julia source: base/operators.jl:1453-1453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x) = Fix2(in, x)
```
-/
def inUnary {α β γ : Type} (contains : α → β → γ) (collection : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.inOp collection :=
  ⟨fun a b _ => contains a b, collection⟩

/--
Julia source: base/operators.jl:1455-1455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x, itr::Any) = any(==(x), itr)
```
-/
def inAny {α β γ δ ε : Type}
    (any : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
      Fix 2 (α → γ → Unit → δ) γ fTag xTag → β → ε)
    (eq : α → γ → δ) (x : γ) (itr : β) : ε :=
  any (fixEqual eq x) itr

/--
Julia source: base/operators.jl:1463-1471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _in_tuple(x, @nospecialize(itr::Tuple), result = false)
    @inline
    isempty(itr) && return result
    v = (itr[1] == x)
    if v === true
        return true
    end
    return _in_tuple(x, tail(itr), result | v)
end
```
-/
def inTupleHelper {τ β : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → β → Truth) (x : β) :
    {ts : List τ} → HTuple Elem ts → Truth → Truth
  | [], .nil, result => result
  | _ :: _, .cons v rest, result =>
      match eq v x with
      | .true => .true
      | comparison => inTupleHelper eq x rest (Truth.or result comparison)

/--
Julia source: base/operators.jl:1459-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x, itr::Tuple) = _in_tuple(x, itr)
```
-/
def inTuple {τ β : Type} {Elem : τ → Type} {ts : List τ}
    (eq : {t : τ} → Elem t → β → Truth) (x : β)
    (itr : HTuple Elem ts) : Truth :=
  inTupleHelper eq x itr .false

/-- operators.lean `inTupleHelper` (operators.jl:1463-1471 `_in_tuple`) with `==` in a
monad, so a throwing `itr[1] == x` propagates; `m := Id` is the installed definition. -/
def inTupleHelperM {m : Type → Type} [Monad m] {τ β : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → β → m Truth) (x : β) :
    {ts : List τ} → HTuple Elem ts → Truth → m Truth
  | [], .nil, result => pure result
  | _ :: _, .cons v rest, result => do
      match ← eq v x with
      | .true => pure .true
      | comparison => inTupleHelperM eq x rest (Truth.or result comparison)

/-- operators.lean `inTuple` (operators.jl:1459). -/
def inTupleM {m : Type → Type} [Monad m] {τ β : Type} {Elem : τ → Type} {ts : List τ}
    (eq : {t : τ} → Elem t → β → m Truth) (x : β)
    (itr : HTuple Elem ts) : m Truth :=
  inTupleHelperM eq x itr .false

/-- operators.lean `isequal` (operators.jl:196 `isequal(x, y) = (x == y)::Bool`) on the
pair's three-valued `==`: a `missing` fails the `::Bool` assertion (`TypeError`). -/
def isequalM {Q K E : Type} (typeError : E) (eq : Q → K → Except E Truth) (q : Q)
    (k : K) : Except E Bool := do
  match ← eq q k with
  | .true => pure true
  | .false => pure false
  | .missing => throw typeError

/--
Julia source: base/operators.jl:1474-1474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x, itr::Any32) = invoke(in, Tuple{Any,Any}, x, itr)
```
-/
def inAny32 (invoke : α → β → γ) (x : α) (itr : β) : γ := invoke x itr

/--
Julia source: base/operators.jl:1477-1477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∉(x, itr) = !∈(x, itr)
```
-/
def notIn (not : γ → δ) (membership : α → β → γ)
    (item : α) (itr : β) : δ :=
  not (membership item itr)

/--
Julia source: base/operators.jl:1478-1478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∉(itr) = Fix2(∉, itr)
```
-/
def notInUnary {α β γ : Type} (notIn : α → β → γ) (collection : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.notIn collection :=
  ⟨fun a b _ => notIn a b, collection⟩

/--
Julia source: base/operators.jl:1486-1486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∋(itr, x) = in(x, itr)
```
-/
def contains (membership : α → β → γ) (itr : β) (x : α) : γ := membership x itr

/--
Julia source: base/operators.jl:1497-1497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∋(x) = Fix2(∋, x)
```
-/
def containsUnary {α β γ : Type} (contains : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.contains x :=
  ⟨fun a b _ => contains a b, x⟩

/--
Julia source: base/operators.jl:1499-1499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∌(itr, x) = !∋(itr, x)
```
-/
def notContains (not : γ → δ) (contains : β → α → γ)
    (itr : β) (x : α) : δ :=
  not (contains itr x)

/--
Julia source: base/operators.jl:1500-1500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
∌(x) = Fix2(∌, x)
```
-/
def notContainsUnary {α β γ : Type} (notContains : α → β → γ) (x : β) : Fix 2 (α → β → Unit → γ) β Fix2OpTag.notContains x :=
  ⟨fun a b _ => notContains a b, x⟩

end JuliaLean.base.operators

/- Additive recovery reconstruction for models batch 2, group 15.
   These declarations were reconstructed from the exact pinned Julia source
   and the recovered independent property interfaces after the transient
   workspace disappeared. They do not include or replace any baseline file.
   Julia commit: f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/

namespace JuliaLean.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple

/-- A complete separation of concrete Bool values from arbitrary other Julia
values. Other is unrestricted and may carry reference identity, mutable state
handles, abstract/custom values, and heterogeneous runtime tags. The bool tag
is reserved for actual Julia Bool values; it is not a user predicate. -/
inductive Value (Other : Type) where
  | bool (value : Bool)
  | other (value : Other)

/-- The concrete ::Bool assertion used by the reached Julia methods. It does
not invoke conversion or an arbitrary membership callback. Source assertion
semantics: doc/src/manual/types.md:67-83 at the pinned commit. -/
def assertBool {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {Other : Type} : Value Other → m Bool
  | .bool value => pure value
  | .other _ => throwThe TupleError .typeError

/-- Selected equality on the unfixed argument types of generic isequal.
The action retains effects, arbitrary intermediate values, and exceptions. -/
structure EqualityOps (m : Type → Type) (A B Other : Type) where
  equal : A → B → m (Value Other)

/-- Generic equality wrapper. The equality call is evaluated once, before the
concrete assertion. Documentation: base/operators.jl:145-177 and
doc/src/manual/types.md:67-83 at the pinned commit. -/
-- Source: base/operators.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(x, y) = (x == y)::Bool # all `missing` cases are handled in missing.jl
-- /Source
def isequal {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A B Other : Type} (ops : EqualityOps m A B Other) (x : A) (y : B) : m Bool := do
  let value ← ops.equal x y
  assertBool value

/-- The two selected signbit methods can have different operand domains and
arbitrary effects, exceptions, and dynamic results. -/
structure SignOps (m : Type → Type) (A B Other : Type) where
  signLeft : A → m (Value Other)
  signRight : B → m (Value Other)

/-- The selected same-type numeric equality fallback specialized to the
closed concrete Bool domain. Its === compares immutable Bool bit patterns,
represented by Bool BEq; no open equality callback is introduced.
Identity semantics: base/operators.jl:343-350 at the pinned commit. -/
-- Source: base/promotion.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (==)(x::T, y::T) where {T<:Number} = x === y
-- /Source
def boolEqual (left right : Bool) : Bool := left == right

/-- Both assertions occur before concrete Bool equality. The second sign
query is reached only after the first call and assertion succeed. -/
-- Source: base/operators.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- signequal(x, y) = signbit(x)::Bool == signbit(y)::Bool
-- /Source
def signequal {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A B Other : Type} (ops : SignOps m A B Other) (x : A) (y : B) : m Bool := do
  let leftValue ← ops.signLeft x
  let left ← assertBool leftValue
  let rightValue ← ops.signRight y
  let right ← assertBool rightValue
  pure (boolEqual left right)

/-- Eager sign order. Julia parses the right operand as !(signbit(y)::Bool):
the assertion precedes concrete Bool negation. Both sign queries occur even
when the first asserted sign is false; only an exception interrupts them.
Concrete conjunction reuses the installed operator model. -/
-- Source: base/operators.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- signless(x, y) = signbit(x)::Bool & !signbit(y)::Bool
-- /Source
def signless {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A B Other : Type} (ops : SignOps m A B Other) (x : A) (y : B) : m Bool := do
  let leftValue ← ops.signLeft x
  let left ← assertBool leftValue
  let rightValue ← ops.signRight y
  let right ← assertBool rightValue
  pure (JuliaLean.base.operators.bitAnd left (!right))

/-- Open operations selected only when the arguments are not both fixed
concrete Bool values. Their values, exceptions, and world changes are
unrestricted. Non-Bool does not mean nonnumeric: Other may include every
other concrete, abstract, and custom runtime value. -/
structure BoolOps (m : Type → Type) (Other : Type) where
  notOther : Other → m (Value Other)
  andOther : Value Other → Value Other → m (Value Other)
  orOther : Value Other → Value Other → m (Value Other)

/-- Necessary concrete Bool negation uses the one-bit complement primitive.
Every other runtime value is passed unchanged to its selected open method. -/
-- Source: base/essentials.jl:1294-1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- !(x::Bool) = not_int(x)
-- /Source
def notValue {m : Type → Type} [Monad m] {Other : Type}
    (ops : BoolOps m Other) : Value Other → m (Value Other)
  | .bool value => pure (.bool (!value))
  | .other value => ops.notOther value

/-- Necessary concrete Bool conjunction reuses the installed Boolean
operator model; all other combinations use selected open dispatch. -/
-- Source: base/bool.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (&)(x::Bool, y::Bool) = and_int(x, y)
-- /Source
def andValue {m : Type → Type} [Monad m] {Other : Type}
    (ops : BoolOps m Other) (left right : Value Other) : m (Value Other) :=
  match left, right with
  | .bool x, .bool y => pure (.bool (JuliaLean.base.operators.bitAnd x y))
  | _, _ => ops.andOther left right

/-- Necessary concrete Bool disjunction reuses the installed Boolean
operator model; all other combinations use selected open dispatch. -/
-- Source: base/bool.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (|)(x::Bool, y::Bool) = or_int(x, y)
-- /Source
def orValue {m : Type → Type} [Monad m] {Other : Type}
    (ops : BoolOps m Other) (left right : Value Other) : m (Value Other) :=
  match left, right with
  | .bool x, .bool y => pure (.bool (JuliaLean.base.operators.bitOr x y))
  | _, _ => ops.orOther left right

/-- AbstractFloat and Real are not concrete dispatch types. These fields
represent selected methods on the actual operands, including custom numeric
subtypes and their effects. Only the explicit equality assertion fixes Bool.
The Boolean operation helpers still perform the concrete Bool dispatch. -/
structure FloatEqualOps (m : Type → Type) (A B Other : Type) where
  nanLeft : A → m (Value Other)
  nanRight : B → m (Value Other)
  signEqual : A → B → m (Value Other)
  equal : A → B → m (Value Other)
  boolOps : BoolOps m Other

/-- Full eager evaluation of AbstractFloat equality, including interleaved
Boolean operations and terminal effects/errors. The method does not assert
Bool for isnan or signequal and does not short-circuit either conjunction.
Documentation: base/operators.jl:145-177; doc/src/manual/control-flow.md:
264-268,361-376; doc/src/manual/types.md:67-83 at the pinned commit. -/
-- Source: base/operators.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(x::AbstractFloat, y::AbstractFloat) = (isnan(x) & isnan(y)) | signequal(x, y) & (x == y)::Bool
-- /Source
def isequalFloatFloat {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A B Other : Type} (ops : FloatEqualOps m A B Other)
    (x : A) (y : B) : m (Value Other) := do
  let leftNan ← ops.nanLeft x
  let rightNan ← ops.nanRight y
  let bothNan ← andValue ops.boolOps leftNan rightNan
  let sameSign ← ops.signEqual x y
  let equalValue ← ops.equal x y
  let equalBool ← assertBool equalValue
  let signedEqual ← andValue ops.boolOps sameSign (.bool equalBool)
  orValue ops.boolOps bothNan signedEqual

/-- The Real/AbstractFloat method retains independently typed operands and
the same source evaluation order, including non-Bool intermediate results.
There is no extra assertion or conversion at the abstract type boundary. -/
-- Source: base/operators.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(x::Real,          y::AbstractFloat) = (isnan(x) & isnan(y)) | signequal(x, y) & (x == y)::Bool
-- /Source
def isequalRealFloat {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A B Other : Type} (ops : FloatEqualOps m A B Other)
    (x : A) (y : B) : m (Value Other) := do
  let leftNan ← ops.nanLeft x
  let rightNan ← ops.nanRight y
  let bothNan ← andValue ops.boolOps leftNan rightNan
  let sameSign ← ops.signEqual x y
  let equalValue ← ops.equal x y
  let equalBool ← assertBool equalValue
  let signedEqual ← andValue ops.boolOps sameSign (.bool equalBool)
  orValue ops.boolOps bothNan signedEqual

/-- Open operand-level methods for the AbstractFloat ordering wrapper. None
of the source intermediate predicates carries a concrete Bool assertion. -/
structure FloatLessOps (m : Type → Type) (A B Other : Type) where
  nanLeft : A → m (Value Other)
  nanRight : B → m (Value Other)
  signLess : A → B → m (Value Other)
  less : A → B → m (Value Other)
  boolOps : BoolOps m Other

/-- Full eager evaluation of the floating ordering expression. Negation is
evaluated immediately after the left NaN query; the inner disjunction and
conjunction complete before the final less-than query. All selected methods
share the surrounding monad and retain arbitrary effects and exceptions.
Documentation: base/operators.jl:206-237; doc/src/manual/control-flow.md:
264-268,361-376 at the pinned commit. -/
-- Source: base/operators.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isless(x::AbstractFloat, y::AbstractFloat) = (!isnan(x) & (isnan(y) | signless(x, y))) | (x < y)
-- /Source
def islessFloatFloat {m : Type → Type} [Monad m]
    {A B Other : Type} (ops : FloatLessOps m A B Other)
    (x : A) (y : B) : m (Value Other) := do
  let leftNan ← ops.nanLeft x
  let leftOrdered ← notValue ops.boolOps leftNan
  let rightNan ← ops.nanRight y
  let signsLess ← ops.signLess x y
  let rightOrSign ← orValue ops.boolOps rightNan signsLess
  let orderedPart ← andValue ops.boolOps leftOrdered rightOrSign
  let numericLess ← ops.less x y
  orValue ops.boolOps orderedPart numericLess

/-- The predicate values can be non-Bool and the comparison result R is
entirely unrestricted. Forward and backward dispatch preserve the actual
argument order, including heterogeneous operand domains. -/
structure GreaterOps (m : Type → Type) (A B Other R : Type) where
  unorderedLeft : A → m (Value Other)
  unorderedRight : B → m (Value Other)
  lessForward : A → B → m R
  lessBackward : B → A → m R

/-- Short-circuit unordered testing followed by one selected comparison.
Only reached conditions are asserted Bool; the returned ordering value is
not asserted. Documentation: base/operators.jl:252-294 and
doc/src/manual/control-flow.md (short-circuit evaluation) at the pinned commit. -/
-- Source: base/operators.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isgreater(x, y) = isunordered(x) || isunordered(y) ? isless(x, y) : isless(y, x)
-- /Source
def isgreater {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A B Other R : Type} (ops : GreaterOps m A B Other R)
    (x : A) (y : B) : m R := do
  let leftValue ← ops.unorderedLeft x
  let left ← assertBool leftValue
  if left then
    ops.lessForward x y
  else
    let rightValue ← ops.unorderedRight y
    let right ← assertBool rightValue
    if right then ops.lessForward x y else ops.lessBackward y x

/-- The isnan method is open for an unfixed AbstractFloat subtype, and its
result is not constrained by the source wrapper. -/
structure UnorderedFloatOps (m : Type → Type) (A R : Type) where
  isnan : A → m R

/-- Forward exactly one selected isnan call, without asserting Bool.
Documentation: base/operators.jl:297-308 at the pinned commit. -/
-- Source: base/operators.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isunordered(x::AbstractFloat) = isnan(x)
-- /Source
def isunorderedFloat {m : Type → Type} {A R : Type}
    (ops : UnorderedFloatOps m A R) (x : A) : m R :=
  ops.isnan x

/-- Equality remains open on arbitrary inputs. Its dynamic returned value
determines whether the following negation uses the concrete Bool primitive. -/
structure NotEqualOps (m : Type → Type) (A B Other : Type) where
  equal : A → B → m (Value Other)
  boolOps : BoolOps m Other

/-- Equality is evaluated before negation, with no source Bool assertion.
Documentation: base/operators.jl:319-337 at the pinned commit. -/
-- Source: base/operators.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- !=(x, y) = !(x == y)
-- /Source
def notEqual {m : Type → Type} [Monad m] {A B Other : Type}
    (ops : NotEqualOps m A B Other) (x : A) (y : B) : m (Value Other) := do
  let equalValue ← ops.equal x y
  notValue ops.boolOps equalValue

/-- Arbitrary comparison results are retained so result-level | dispatch is
concrete only when both actual returned values are Bool. -/
structure LessEqualOps (m : Type → Type) (A B Other : Type) where
  less : A → B → m (Value Other)
  equal : A → B → m (Value Other)
  boolOps : BoolOps m Other

/-- Eager < followed by == and then result-level disjunction.
Documentation: base/operators.jl:446-466 at the pinned commit. -/
-- Source: base/operators.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x, y) = (x < y) | (x == y)
-- /Source
def lessEqual {m : Type → Type} [Monad m] {A B Other : Type}
    (ops : LessEqualOps m A B Other) (x : A) (y : B) : m (Value Other) := do
  let lessValue ← ops.less x y
  let equalValue ← ops.equal x y
  orValue ops.boolOps lessValue equalValue

/-- Real is abstract, so selected < dispatch is open; its actual result R
can be arbitrary and need not be Bool. -/
structure RealLessOps (m : Type → Type) (A B R : Type) where
  less : A → B → m R

/-- Forward exactly one selected < call on the original ordered operands.
Documentation: base/operators.jl:206-237,503-505 at the pinned commit. -/
-- Source: base/operators.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isless(x::Real, y::Real) = x<y
-- /Source
def islessReal {m : Type → Type} {A B R : Type}
    (ops : RealLessOps m A B R) (x : A) (y : B) : m R :=
  ops.less x y

end JuliaLean.base.operators.Models2Group15


namespace JuliaLean.base.operators.Models2Group15

/-!
Full-domain comparison and argument-fold models reconstructed from the pinned
source. Open calls retain state, errors, unrestricted results and actual
argument identities. All native literals and fold counters use 64-bit Int.
-/

-- Source: base/operators.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::Integer) = ifelse(isless(x, y), -1, ifelse(isless(y, x), 1, 0))
-- /Source
/-- Comparison results distinguish native Int values from every other
possible result type of an open ifelse method. -/
inductive CmpValue (Other : Type) where
  | integer (value : JInt .i64)
  | other (value : Other)
  deriving Repr, DecidableEq

/-- Native Int minus one returned or supplied by the comparison bodies. -/
def cmpMinusOne : JInt .i64 := JInt.lit .i64 (-1)

/-- Native Int zero supplied by the comparison bodies. -/
def cmpZero : JInt .i64 := JInt.lit .i64 0

/-- Native Int one supplied by the comparison bodies. -/
def cmpOne : JInt .i64 := JInt.lit .i64 1

-- Source: base/operators.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::Integer) = ifelse(isless(x, y), -1, ifelse(isless(y, x), 1, 0))
-- /Source
/-- Dispatched ifelse calls whose argument types are not all fixed by the
source. Bool conditions with a non-native branch still allow user dispatch. -/
structure IfelseOps (m : Type → Type) (CondOther Other : Type) where
  other : CondOther → CmpValue Other → CmpValue Other → m (CmpValue Other)
  boolOther : Bool → CmpValue Other → CmpValue Other → m (CmpValue Other)

-- Source: base/operators.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::Integer) = ifelse(isless(x, y), -1, ifelse(isless(y, x), 1, 0))
-- /Source
/-- Close only the fully concrete Bool/native-Int/native-Int call through the
installed Base model. Every remaining argument-type combination is dispatched
with the original condition and both evaluated branch values. -/
def choose {m : Type → Type} [Monad m] {CondOther Other : Type}
    (ops : IfelseOps m CondOther Other) (condition : Value CondOther)
    (trueValue falseValue : CmpValue Other) : m (CmpValue Other) :=
  match condition with
  | .bool b =>
      match trueValue, falseValue with
      | .integer x, .integer y =>
          pure (.integer (JuliaLean.base.operators.ifelseValue b x y))
      | _, _ => ops.boolOther b trueValue falseValue
  | .other c => ops.other c trueValue falseValue

-- Source: base/operators.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)
-- /Source
/-- Both selected isless calls and the potentially dispatched final ifelse.
The two comparisons may have arbitrary results, failures and state changes. -/
structure CmpOps (m : Type → Type) (A B CondOther Other : Type) where
  lessForward : A → B → m (Value CondOther)
  lessBackward : B → A → m (Value CondOther)
  ifelseOps : IfelseOps m CondOther Other

-- Source: base/operators.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)
-- /Source
/-- Generic cmp first checks the forward result as a Bool. Only false reaches
the reverse comparison, whose result is passed to ifelse without a Bool check. -/
def cmp {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m]
    {A B CondOther Other : Type}
    (ops : CmpOps m A B CondOther Other) (x : A) (y : B) :
    m (CmpValue Other) := do
  let forward ← ops.lessForward x y
  let before ← assertBool forward
  if before then
    pure (.integer cmpMinusOne)
  else do
    let backward ← ops.lessBackward y x
    choose ops.ifelseOps backward (.integer cmpOne) (.integer cmpZero)

-- Source: base/operators.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(<, x, y) = (x < y) ? -1 : ifelse(y < x, 1, 0)
-- /Source
/-- Calls of the explicitly supplied comparison object in each argument
order, together with the open cases of the final ifelse dispatch. -/
structure CmpByOps (m : Type → Type) (F A B CondOther Other : Type) where
  callForward : F → A → B → m (Value CondOther)
  callBackward : F → B → A → m (Value CondOther)
  ifelseOps : IfelseOps m CondOther Other

-- Source: base/operators.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(<, x, y) = (x < y) ? -1 : ifelse(y < x, 1, 0)
-- /Source
/-- Comparison using the original callable object in both directions.
The source's conditional and final ifelse have distinct Bool behavior. -/
def cmpBy {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m]
    {F A B CondOther Other : Type}
    (ops : CmpByOps m F A B CondOther Other) (less : F) (x : A) (y : B) :
    m (CmpValue Other) := do
  let forward ← ops.callForward less x y
  let before ← assertBool forward
  if before then
    pure (.integer cmpMinusOne)
  else do
    let backward ← ops.callBackward less y x
    choose ops.ifelseOps backward (.integer cmpOne) (.integer cmpZero)

-- Source: base/operators.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::Integer) = ifelse(isless(x, y), -1, ifelse(isless(y, x), 1, 0))
-- /Source
/-- Integer cmp eagerly evaluates both comparisons in source argument order,
then the inner ifelse, then the outer ifelse. Neither comparison is Bool-checked
by this body, and the inner call may return a value of another type. -/
def cmpInteger {m : Type → Type} [Monad m]
    {A B CondOther Other : Type}
    (ops : CmpOps m A B CondOther Other) (x : A) (y : B) :
    m (CmpValue Other) := do
  let forward ← ops.lessForward x y
  let backward ← ops.lessBackward y x
  let inner ← choose ops.ifelseOps backward (.integer cmpOne) (.integer cmpZero)
  choose ops.ifelseOps forward (.integer cmpMinusOne) inner

-- Source: base/operators.jl:588-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- minmax(x,y) = isless(y, x) ? (y, x) : (x, y)
-- /Source
/-- The one selected comparison of minmax, in the source's reverse order. -/
structure MinmaxOps (m : Type → Type) (A B Other : Type) where
  lessBackward : B → A → m (Value Other)

-- Source: base/operators.jl:588-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- minmax(x,y) = isless(y, x) ? (y, x) : (x, y)
-- /Source
/-- Return the two original values in comparison-selected order. Sum tags
preserve their heterogeneous carriers; the comparison is checked as a Bool. -/
def minmax {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m] {A B Other : Type}
    (ops : MinmaxOps m A B Other) (x : A) (y : B) :
    m ((A ⊕ B) × (A ⊕ B)) := do
  let comparison ← ops.lessBackward y x
  let reverse ← assertBool comparison
  if reverse then
    pure (.inr y, .inl x)
  else
    pure (.inl x, .inr y)

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
/-- An immutable Julia argument tuple represented in a universal value
carrier. The bound is the native Int length bound of a constructible tuple;
it does not require the represented Julia values to have one Julia type. -/
structure Arguments (V : Type) where
  values : List V
  sizeFits : values.length ≤ (IntTy.max .i64).toNat

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
/-- The actual callable and two current values are retained at every fold
step. The universal value carrier permits each application to change type. -/
structure FoldOps (m : Type → Type) (F V : Type) where
  apply : F → V → V → m V

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
/-- Tuple length as native Int. The Arguments bound prevents wraparound. -/
def argumentLength {V : Type} (args : Arguments V) : JInt .i64 :=
  JInt.lit .i64 (Int.ofNat args.values.length)

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
/-- Invoke the installed concrete Tuple/native-Int indexing model, preserving
its exact value or TupleError. Indexing is not an open callback. -/
def argumentAt {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m] {V : Type}
    (args : Arguments V) (index : JInt .i64) : m V :=
  match JuliaLean.base.tuple.getindexInt args.values index with
  | .ok value => pure value
  | .error error => throw error

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
/-- The actual tail loop after the 31 literal stages. Remaining is the exact
number of elements still to consume and serves as the structural recursion
measure; the source counter and endpoint check remain native Int. The endpoint
returns before any further counter increment, even at typemax(Int). -/
def afoldlTail {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m] {F V : Type}
    (ops : FoldOps m F V) (op : F) (args : Arguments V) :
    Nat → JInt .i64 → V → m V
  | 0, _, accumulator => pure accumulator
  | remaining + 1, index, accumulator => do
      let value ← argumentAt args index
      let next ← ops.apply op accumulator value
      if index = argumentLength args then
        pure next
      else do
        afoldlTail ops op args remaining (index + JInt.lit .i64 1) next

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
/-- Faithful argument-list fold: the zero-length check and all 31 literal
read/application/endpoint stages precede the actual recursive native-index
tail. No callback replaces the loop or the selected tuple indexing behavior. -/
def afoldlMany {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m] {F V : Type}
    (ops : FoldOps m F V) (op : F) (a : V) (args : Arguments V) : m V := do
  let len := argumentLength args
  if len = JInt.lit .i64 0 then
    pure a
  else do
    let value1 ← argumentAt args (JInt.lit .i64 1)
    let accumulator1 ← ops.apply op a value1
    if len = JInt.lit .i64 1 then
      pure accumulator1
    else do
      let value2 ← argumentAt args (JInt.lit .i64 2)
      let accumulator2 ← ops.apply op accumulator1 value2
      if len = JInt.lit .i64 2 then
        pure accumulator2
      else do
        let value3 ← argumentAt args (JInt.lit .i64 3)
        let accumulator3 ← ops.apply op accumulator2 value3
        if len = JInt.lit .i64 3 then
          pure accumulator3
        else do
          let value4 ← argumentAt args (JInt.lit .i64 4)
          let accumulator4 ← ops.apply op accumulator3 value4
          if len = JInt.lit .i64 4 then
            pure accumulator4
          else do
            let value5 ← argumentAt args (JInt.lit .i64 5)
            let accumulator5 ← ops.apply op accumulator4 value5
            if len = JInt.lit .i64 5 then
              pure accumulator5
            else do
              let value6 ← argumentAt args (JInt.lit .i64 6)
              let accumulator6 ← ops.apply op accumulator5 value6
              if len = JInt.lit .i64 6 then
                pure accumulator6
              else do
                let value7 ← argumentAt args (JInt.lit .i64 7)
                let accumulator7 ← ops.apply op accumulator6 value7
                if len = JInt.lit .i64 7 then
                  pure accumulator7
                else do
                  let value8 ← argumentAt args (JInt.lit .i64 8)
                  let accumulator8 ← ops.apply op accumulator7 value8
                  if len = JInt.lit .i64 8 then
                    pure accumulator8
                  else do
                    let value9 ← argumentAt args (JInt.lit .i64 9)
                    let accumulator9 ← ops.apply op accumulator8 value9
                    if len = JInt.lit .i64 9 then
                      pure accumulator9
                    else do
                      let value10 ← argumentAt args (JInt.lit .i64 10)
                      let accumulator10 ← ops.apply op accumulator9 value10
                      if len = JInt.lit .i64 10 then
                        pure accumulator10
                      else do
                        let value11 ← argumentAt args (JInt.lit .i64 11)
                        let accumulator11 ← ops.apply op accumulator10 value11
                        if len = JInt.lit .i64 11 then
                          pure accumulator11
                        else do
                          let value12 ← argumentAt args (JInt.lit .i64 12)
                          let accumulator12 ← ops.apply op accumulator11 value12
                          if len = JInt.lit .i64 12 then
                            pure accumulator12
                          else do
                            let value13 ← argumentAt args (JInt.lit .i64 13)
                            let accumulator13 ← ops.apply op accumulator12 value13
                            if len = JInt.lit .i64 13 then
                              pure accumulator13
                            else do
                              let value14 ← argumentAt args (JInt.lit .i64 14)
                              let accumulator14 ← ops.apply op accumulator13 value14
                              if len = JInt.lit .i64 14 then
                                pure accumulator14
                              else do
                                let value15 ← argumentAt args (JInt.lit .i64 15)
                                let accumulator15 ← ops.apply op accumulator14 value15
                                if len = JInt.lit .i64 15 then
                                  pure accumulator15
                                else do
                                  let value16 ← argumentAt args (JInt.lit .i64 16)
                                  let accumulator16 ← ops.apply op accumulator15 value16
                                  if len = JInt.lit .i64 16 then
                                    pure accumulator16
                                  else do
                                    let value17 ← argumentAt args (JInt.lit .i64 17)
                                    let accumulator17 ← ops.apply op accumulator16 value17
                                    if len = JInt.lit .i64 17 then
                                      pure accumulator17
                                    else do
                                      let value18 ← argumentAt args (JInt.lit .i64 18)
                                      let accumulator18 ← ops.apply op accumulator17 value18
                                      if len = JInt.lit .i64 18 then
                                        pure accumulator18
                                      else do
                                        let value19 ← argumentAt args (JInt.lit .i64 19)
                                        let accumulator19 ← ops.apply op accumulator18 value19
                                        if len = JInt.lit .i64 19 then
                                          pure accumulator19
                                        else do
                                          let value20 ← argumentAt args (JInt.lit .i64 20)
                                          let accumulator20 ← ops.apply op accumulator19 value20
                                          if len = JInt.lit .i64 20 then
                                            pure accumulator20
                                          else do
                                            let value21 ← argumentAt args (JInt.lit .i64 21)
                                            let accumulator21 ← ops.apply op accumulator20 value21
                                            if len = JInt.lit .i64 21 then
                                              pure accumulator21
                                            else do
                                              let value22 ← argumentAt args (JInt.lit .i64 22)
                                              let accumulator22 ← ops.apply op accumulator21 value22
                                              if len = JInt.lit .i64 22 then
                                                pure accumulator22
                                              else do
                                                let value23 ← argumentAt args (JInt.lit .i64 23)
                                                let accumulator23 ← ops.apply op accumulator22 value23
                                                if len = JInt.lit .i64 23 then
                                                  pure accumulator23
                                                else do
                                                  let value24 ← argumentAt args (JInt.lit .i64 24)
                                                  let accumulator24 ← ops.apply op accumulator23 value24
                                                  if len = JInt.lit .i64 24 then
                                                    pure accumulator24
                                                  else do
                                                    let value25 ← argumentAt args (JInt.lit .i64 25)
                                                    let accumulator25 ← ops.apply op accumulator24 value25
                                                    if len = JInt.lit .i64 25 then
                                                      pure accumulator25
                                                    else do
                                                      let value26 ← argumentAt args (JInt.lit .i64 26)
                                                      let accumulator26 ← ops.apply op accumulator25 value26
                                                      if len = JInt.lit .i64 26 then
                                                        pure accumulator26
                                                      else do
                                                        let value27 ← argumentAt args (JInt.lit .i64 27)
                                                        let accumulator27 ← ops.apply op accumulator26 value27
                                                        if len = JInt.lit .i64 27 then
                                                          pure accumulator27
                                                        else do
                                                          let value28 ← argumentAt args (JInt.lit .i64 28)
                                                          let accumulator28 ← ops.apply op accumulator27 value28
                                                          if len = JInt.lit .i64 28 then
                                                            pure accumulator28
                                                          else do
                                                            let value29 ← argumentAt args (JInt.lit .i64 29)
                                                            let accumulator29 ← ops.apply op accumulator28 value29
                                                            if len = JInt.lit .i64 29 then
                                                              pure accumulator29
                                                            else do
                                                              let value30 ← argumentAt args (JInt.lit .i64 30)
                                                              let accumulator30 ← ops.apply op accumulator29 value30
                                                              if len = JInt.lit .i64 30 then
                                                                pure accumulator30
                                                              else do
                                                                let value31 ← argumentAt args (JInt.lit .i64 31)
                                                                let accumulator31 ← ops.apply op accumulator30 value31
                                                                if len = JInt.lit .i64 31 then
                                                                  pure accumulator31
                                                                else do
                                                                  afoldlTail ops op args (args.values.length - 31) (JInt.lit .i64 32) accumulator31

-- Source: base/operators.jl:666-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:+, :(+%), :*, :(*%), :&, :|, :xor, :min, :max, :kron)
--     @eval begin
--         # note: these definitions must not cause a dispatch loop when +(a,b) is
--         # not defined, and must only try to call 2-argument definitions, so
--         # that defining +(a,b) is sufficient for full functionality.
--         ($op)(a, b, c, xs...) = (@inline; afoldl($op, ($op)(($op)(a,b),c), xs...))
--         # a further concern is that it's easy for a type like (Int,Int...)
--         # to match many definitions, so we need to keep the number of
--         # definitions down to avoid losing type information.
--     end
-- end
-- /Source
/-- The ten distinct operator objects named by the source generator. -/
inductive NaryOperator where
  | add
  | wrappingAdd
  | multiply
  | wrappingMultiply
  | bitAnd
  | bitOr
  | xor
  | min
  | max
  | kron
  deriving Repr, DecidableEq

-- Source: base/operators.jl:666-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:+, :(+%), :*, :(*%), :&, :|, :xor, :min, :max, :kron)
--     @eval begin
--         # note: these definitions must not cause a dispatch loop when +(a,b) is
--         # not defined, and must only try to call 2-argument definitions, so
--         # that defining +(a,b) is sufficient for full functionality.
--         ($op)(a, b, c, xs...) = (@inline; afoldl($op, ($op)(($op)(a,b),c), xs...))
--         # a further concern is that it's easy for a type like (Int,Int...)
--         # to match many definitions, so we need to keep the number of
--         # definitions down to avoid losing type information.
--     end
-- end
-- /Source
/-- Every generated method performs two initial binary applications of its
original operator. The remaining argument tuple reaches the installed
zero-rest afoldl method or the concrete afoldlMany body according to arity. -/
def naryOperator {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.tuple.TupleError m] {V : Type}
    (ops : FoldOps m NaryOperator V) (op : NaryOperator)
    (a b c : V) (args : Arguments V) : m V := do
  let first ← ops.apply op a b
  let second ← ops.apply op first c
  if args.values.isEmpty then
    pure (JuliaLean.base.operators.afoldlOne op second)
  else do
    afoldlMany ops op second args

end JuliaLean.base.operators.Models2Group15



/- Additive recovery reconstruction for the reached post-shift methods.
   Reconstructed from Julia commit f755f49a9e41380d7da126b3c1db9fe7f83dd027
   and the recovered independent property interfaces. The original baseline
   declarations are neither included nor replaced. This fragment follows
   NewEarlyModels15 and the fragment defining Arguments. -/

namespace JuliaLean.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple

/-- Same-type Real operands remain abstract at this method boundary. The
selected mod and iszero calls retain their full effects and result domains. -/
structure Mod1Ops (m : Type → Type) (A Rem Other : Type) where
  modulus : A → A → m Rem
  iszero : Rem → m (Value Other)

/-- Reuse the installed effectful mod1 control flow with the concrete Bool
assertion for the source condition. The result preserves the original divisor
or the exact remainder object through distinct sum alternatives.
Documentation: base/operators.jl:888-913 at the pinned commit. -/
-- Source: base/operators.jl:914-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mod1(x::T, y::T) where {T<:Real} = (m = mod(x, y); iszero(m) ? y : m)
-- /Source
def mod1 {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {A Rem Other : Type} (ops : Mod1Ops m A Rem Other) (x y : A) : m (A ⊕ Rem) :=
  JuliaLean.base.operators.mod1 ops.modulus ops.iszero assertBool x y

/-- The two generic selected methods may have different result types and
arbitrary effects, including exceptions after mutating the shared world. -/
structure CldmodOps (m : Type → Type) (A B Quot Rem : Type) where
  cld : A → B → m Quot
  mod1 : A → B → m Rem

/-- Construct the result tuple after cld and then mod1 have completed.
Documentation: base/operators.jl:917-942 at the pinned commit. -/
-- Source: base/operators.jl:943-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cldmod1(x, y) = (cld(x, y), mod1(x, y))
-- /Source
def cldmod1 {m : Type → Type} [Monad m] {A B Quot Rem : Type}
    (ops : CldmodOps m A B Quot Rem) (x : A) (y : B) : m (Quot × Rem) := do
  let quotient ← ops.cld x y
  let remainder ← ops.mod1 x y
  pure (quotient, remainder)

/-- The legacy spelling calls its own selected fld1 method, followed by
selected mod1; no equivalence with cld is assumed. -/
structure FldmodOps (m : Type → Type) (A B Quot Rem : Type) where
  fld1 : A → B → m Quot
  mod1 : A → B → m Rem

/-- Preserve the source's ordered pair of calls and their actual results.
Documentation: base/operators.jl:945-951 at the pinned commit. -/
-- Source: base/operators.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fldmod1(x, y) = (fld1(x, y), mod1(x, y))
-- /Source
def fldmod1 {m : Type → Type} [Monad m] {A B Quot Rem : Type}
    (ops : FldmodOps m A B Quot Rem) (x : A) (y : B) : m (Quot × Rem) := do
  let quotient ← ops.fld1 x y
  let remainder ← ops.mod1 x y
  pure (quotient, remainder)

/-- T is the method's actual type parameter. The type returned by widening
and the converted value are unrestricted: the source has no assertions for
either intermediate or final result. The original value retains its T index. -/
structure WidenOps (m : Type → Type) (Ty : Type) (Values : Ty → Type)
    (Widened R : Type) where
  widenType : Ty → m Widened
  convert : {T : Ty} → Widened → Values T → m R

/-- Widen the actual type parameter before converting the original object.
Documentation: base/operators.jl:954-974 at the pinned commit. -/
-- Source: base/operators.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::T) where {T} = convert(widen(T), x)
-- /Source
def widenValue {m : Type → Type} [Monad m]
    {Ty : Type} {Values : Ty → Type} {Widened R : Type}
    (ops : WidenOps m Ty Values Widened R) (T : Ty) (value : Values T) : m R := do
  let widened ← ops.widenType T
  ops.convert (T := T) widened value

/-- The explicit type fallback introduces the existing runtime error
representation, with no open error-producing callback or world changes.
Documentation: base/operators.jl:954-974 at the pinned commit. -/
-- Source: base/operators.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::Type{T}) where {T} = throw(MethodError(widen, (T,)))
-- /Source
def widenTypeError {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {Ty R : Type} (_T : Ty) : m R :=
  throwThe TupleError (.julia (.methodError "widen"))

/-- Bottom is a fixed singleton, represented by Unit. Every positional pack
within the runtime tuple-size bound is accepted and ignored by this fallback.
The existing error abstraction records the selected function's MethodError.
Documentation: base/operators.jl:954-974 at the pinned commit. -/
-- Source: base/operators.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::Type{Union{}}, slurp...) = throw(MethodError(widen, (Union{},)))
-- /Source
def widenBottomError {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {Arg R : Type} (_bottom : Unit) (_slurp : Arguments Arg) : m R :=
  throwThe TupleError (.julia (.methodError "widen"))

/-- Bind the installed wrapper to the actual Core typeof implementation.
typeof is a closed runtime operation and is not an arbitrary callback. -/
-- Source: base/operators.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _stable_typeof(x) = typeof(x)
-- /Source
def stableTypeof (value : JuliaLean.C.Val) : JuliaLean.C.Val :=
  JuliaLean.base.operators.stableTypeof JuliaLean.C.typeOf value

/-- Bind the static-parameter type method to the installed Core free-typevar
traversal, `Type{T}` constructor, and `DataType` object. When the static
parameter `T` is undefined (`none`, as for `DataType` or an abstract `Type{T}`
with unbound `T`), `@isdefined(T)` is false and the result is `DataType`. -/
-- Source: base/operators.jl:1004-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _stable_typeof(::Type{T}) where {T} = @isdefined(T) && !Core.has_free_typevars(T) ? Type{T} : DataType
-- /Source
def stableTypeofType (t : Option JuliaLean.C.Val) : JuliaLean.C.Val :=
  JuliaLean.base.operators.stableTypeofType
    Option.isSome
    (fun o => match o with | some T => JuliaLean.C.Val.hasFreeTypevars T | none => false)
    (fun o => match o with | some T => JuliaLean.C.Val.typeeq T | none => JuliaLean.C.datatypeType)
    JuliaLean.C.datatypeType t

/-- The actual result of the closed field-membership test, with original
values carried in both alternatives. Accepted values already belong to the
declared field type; rejected values do not. This is a runtime tag, not an
arbitrary predicate, and both value domains remain unrestricted. -/
inductive FieldValue (Accepted Rejected : Type) where
  | accepted (value : Accepted)
  | rejected (value : Rejected)

/-- Conditional field preparation used by typed new: preserve an already
accepted object exactly, or run the selected conversion once. Conversion's
result is still dynamically tagged and is checked by new only later.
Necessary lowering semantics: base/essentials.jl:1468-1488 at the pinned commit. -/
def prepareField {m : Type → Type} [Monad m] {Accepted Rejected : Type}
    (convert : Rejected → m (FieldValue Accepted Rejected)) :
    FieldValue Accepted Rejected → m (FieldValue Accepted Rejected)
  | .accepted value => pure (.accepted value)
  | .rejected value => convert value

/-- The concrete new-field check. A conversion result of the wrong runtime
type raises TypeError, without conversion retry or an arbitrary check callback.
Necessary lowering semantics: base/essentials.jl:1468-1488 at the pinned commit. -/
def finishField {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {Accepted Rejected : Type} : FieldValue Accepted Rejected → m Accepted
  | .accepted value => pure value
  | .rejected _ => throwThe TupleError .typeError

/-- Conversion is open on unfixed declared field types. Values and Invalid
retain actual membership, custom value domains, and reference identity. -/
structure ReturnsConstructorOps (m : Type → Type) (Ty : Type)
    (Values Invalid : Ty → Type) where
  convert : (T : Ty) → Invalid T → m (FieldValue (Values T) (Invalid T))

/-- Explicitly typed Returns preserves the declared parameter. It bypasses
conversion for accepted inputs; otherwise it converts once and performs the
final concrete field check before storing the actual accepted object.
Documentation: base/operators.jl:1006-1028; necessary new lowering:
base/essentials.jl:1468-1488 at the pinned commit. -/
-- Source: base/operators.jl:1031-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     Returns{V}(value) where {V} = new{V}(value)
-- /Source
def returnsTyped {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {Ty : Type} {Values Invalid : Ty → Type}
    (ops : ReturnsConstructorOps m Ty Values Invalid) (T : Ty)
    (value : FieldValue (Values T) (Invalid T)) :
    m (JuliaLean.base.operators.Returns Ty (Values T)) := do
  let prepared ← prepareField (ops.convert T) value
  let stored ← finishField prepared
  pure ⟨T, stored⟩

/-- Both field conversions use the actual declared type and are open on
unfixed parameter/value domains. Membership and final checks stay concrete. -/
structure ComposedConstructorOps (m : Type → Type) (Ty : Type)
    (Values Invalid : Ty → Type) where
  convert : (T : Ty) → Invalid T → m (FieldValue (Values T) (Invalid T))

/-- Julia prepares both fields before executing new. Consequently a rejected
outer conversion result does not suppress the inner conversion; an inner
conversion exception occurs before the pending outer field TypeError.
Final field checks occur in outer/inner order and preserve accepted identity.
Documentation: base/operators.jl:1087-1117; necessary new lowering:
base/essentials.jl:1468-1488 at the pinned commit. -/
-- Source: base/operators.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ComposedFunction{O, I}(outer, inner) where {O, I} = new{O, I}(outer, inner)
-- /Source
def composedTyped {m : Type → Type} [Monad m] [MonadExceptOf TupleError m]
    {Ty : Type} {Values Invalid : Ty → Type}
    (ops : ComposedConstructorOps m Ty Values Invalid) (O I : Ty)
    (outer : FieldValue (Values O) (Invalid O))
    (inner : FieldValue (Values I) (Invalid I)) :
    m (JuliaLean.base.operators.ComposedFunction (Values O) (Values I)) := do
  let preparedOuter ← prepareField (ops.convert O) outer
  let preparedInner ← prepareField (ops.convert I) inner
  let storedOuter ← finishField preparedOuter
  let storedInner ← finishField preparedInner
  pure ⟨storedOuter, storedInner⟩

/-- maybeconstructor dispatch remains open on the fallback's unfixed value.
The tuple construction itself is performed by the wrapper. -/
structure UnwrapFallbackOps (m : Type → Type) (C R : Type) where
  maybeconstructor : C → m R

/-- Forward one maybeconstructor call, then construct the actual singleton.
This is the nonrecursive fallback only; it contains no hidden unwrap recursion. -/
-- Source: base/operators.jl:1127-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unwrap_composed(c) = (maybeconstructor(c),)
-- /Source
def unwrapFallback {m : Type → Type} [Monad m] {C R : Type}
    (ops : UnwrapFallbackOps m C R) (value : C) : m (List R) := do
  let constructor ← ops.maybeconstructor value
  pure [constructor]

/-- Constructor dispatch is open on both unfixed operands. The selected
constructor result R is not forced to be the built-in field-pair result. -/
structure ComposeTwoOps (m : Type → Type) (F G R : Type) where
  construct : F → G → m R

/-- Forward the binary composition's one selected constructor call.
Documentation: base/operators.jl:1039-1083 at the pinned commit. -/
-- Source: base/operators.jl:1137-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ∘(f, g) = ComposedFunction(f, g)
-- /Source
def composeTwo {m : Type → Type} {F G R : Type}
    (ops : ComposeTwoOps m F G R) (outer : F) (inner : G) : m R :=
  ops.construct outer inner

/-- IO is abstract in the Julia signature. The selected print and helper
methods may be custom and effectful; their return types are unrestricted. -/
structure ShowNegatedOps (m : Type → Type) (IO Inner Printed R : Type) where
  printChar : IO → Char → m Printed
  showPart : IO → Inner → m R

/-- The fixed outer ! singleton is represented by Unit. Ignore the print
result and pass the same original IO object to the selected _showcomposed
method; return that method's whole result. -/
-- Source: base/operators.jl:1147-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, c::ComposedFunction{typeof(!)})
--     print(io, '!')
--     _showcomposed(io, c.inner)
-- end
-- /Source
def showNegatedComposed {m : Type → Type} [Monad m]
    {IO Inner Printed R : Type} (ops : ShowNegatedOps m IO Inner Printed R)
    (io : IO) (value : JuliaLean.base.operators.ComposedFunction Unit Inner) : m R := do
  let _ ← ops.printChar io '!'
  ops.showPart io value.inner

/-- The selected show method is open on abstract IO and arbitrary values.
Escaped field spelling avoids Lean's reserved show keyword. -/
structure ShowValueOps (m : Type → Type) (IO Value R : Type) where
  «show» : IO → Value → m R

/-- Forward one selected show call with the original IO and value objects. -/
-- Source: base/operators.jl:1152-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _showcomposed(io::IO, x) = show(io, x)
-- /Source
def showComposedDefault {m : Type → Type} {IO Value R : Type}
    (ops : ShowValueOps m IO Value R) (io : IO) (value : Value) : m R :=
  ops.«show» io value

/-- The IO subtype remains unfixed even though the value is a composition.
Its selected show method and each print method can retain arbitrary effects. -/
structure ShowNestedOps (m : Type → Type) (IO Outer Inner Shown Printed : Type) where
  printChar : IO → Char → m Printed
  «show» : IO → JuliaLean.base.operators.ComposedFunction Outer Inner → m Shown

/-- Print an opening parenthesis, show the same composed object, and print a
closing parenthesis on the original IO. Ignore the first two returned values
and return the actual closing-print result. -/
-- Source: base/operators.jl:1156-1156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _showcomposed(io::IO, f::ComposedFunction) = (print(io, '('); show(io, f); print(io, ')'))
-- /Source
def showNestedComposed {m : Type → Type} [Monad m]
    {IO Outer Inner Shown Printed : Type}
    (ops : ShowNestedOps m IO Outer Inner Shown Printed)
    (io : IO) (value : JuliaLean.base.operators.ComposedFunction Outer Inner) : m Printed := do
  let _ ← ops.printChar io '('
  let _ ← ops.«show» io value
  ops.printChar io ')'

/-- The specialized nested form forwards show directly. The concrete !
singleton outer field does not fix the actual abstract-IO show dispatch. -/
-- Source: base/operators.jl:1158-1158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _showcomposed(io::IO, f::ComposedFunction{typeof(!)}) = show(io, f)
-- /Source
def showNestedNegatedComposed {m : Type → Type} {IO Inner R : Type}
    (ops : ShowValueOps m IO
      (JuliaLean.base.operators.ComposedFunction Unit Inner) R)
    (io : IO) (value : JuliaLean.base.operators.ComposedFunction Unit Inner) : m R :=
  ops.«show» io value

/-- The left operator is the fixed canonical ! singleton. The argument's
Function subtype is unfixed, so the selected binary composition can be custom. -/
structure NegateFunctionOps (m : Type → Type) (F R : Type) where
  compose : Unit → F → m R

/-- Forward one selected composition call with canonical ! first and the
original function second. The selected result is unrestricted.
Documentation: base/operators.jl:1160-1181 at the pinned commit. -/
-- Source: base/operators.jl:1182-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- !(f::Function) = (!) ∘ f
-- /Source
def negateFunction {m : Type → Type} {F R : Type}
    (ops : NegateFunctionOps m F R) (function : F) : m R :=
  ops.compose () function

end JuliaLean.base.operators.Models2Group15

namespace JuliaLean.NumbersCov

open JuliaLean

namespace OperatorModel

/-- `supertype(::DataType)` computes the deferred edge before reading it;
`base/operators.jl:86-94`. -/
def supertypeData (compute : α → Unit) (super : α → β) (t : α) : β :=
  let _ := compute t
  super t

/-- `getproperty(::DataType, ::Symbol)` special-cases `:super`;
`base/operators.jl:95-101`. -/
def getpropertyData (isSuper : γ → Bool) (supertype : α → β)
    (getfield : α → γ → β) (t : α) (s : γ) : β :=
  if isSuper s then supertype t else getfield t s

/-- UnionAll and Type-kind supertype methods; `base/operators.jl:102-105`. -/
def supertypeUnionAll (wrap : α → β → γ) (supertype : β → β) (v : α) (body : β) : γ :=
  wrap v (supertype body)
def supertypeTypeEq (anyType : α) : α := anyType
def supertypeTypeEgal (typeOf : α → β) (parameter : α) : β := typeOf parameter

structure FloatOrder (α : Type) where
  eq : α → α → Bool
  lt : α → α → Bool
  isnan : α → Bool
  signbit : α → Bool

def signequal (o : FloatOrder α) (x y : α) : Bool := o.signbit x == o.signbit y
def signless (o : FloatOrder α) (x y : α) : Bool := o.signbit x && !o.signbit y

/-- Float-aware `isequal`; `base/operators.jl:196-203`. -/
def isequalFloat (o : FloatOrder α) (x y : α) : Bool :=
  (o.isnan x && o.isnan y) || (signequal o x y && o.eq x y)

/-- Float-aware `isless`; `base/operators.jl:240-242`. -/
def islessFloat (o : FloatOrder α) (x y : α) : Bool :=
  (!o.isnan x && (o.isnan y || signless o x y)) || o.lt x y

/-- Optimized pair order; `base/operators.jl:248-249`. -/
def pairIsless (lt eq : α → α → Bool) (a b : α × α) : Bool :=
  lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2)

/-- Generic comparisons; `base/operators.jl:196,295,309-315,338,417-588`. -/
def isequal (eq : α → α → Bool) (x y : α) : Bool := eq x y
def isgreater (unordered : α → Bool) (lt : α → α → Bool) (x y : α) : Bool :=
  if unordered x || unordered y then lt x y else lt y x
def isunordered (_ : α) : Bool := false
def isunorderedFloat (isnan : α → Bool) (x : α) : Bool := isnan x
def typeEqual (typesEqual : α → α → Bool) (t s : α) : Bool := typesEqual t s
def typeVarTypeEqual (_ : α) (_ : β) : Bool := false
def ne (eq : α → α → Bool) (x y : α) : Bool := !eq x y
def neGeneric (eq : α → α → β) (not : β → γ) (x y : α) : γ := not (eq x y)
def ltFallback (lt : α → α → Bool) (x y : α) : Bool := lt x y
def gtFallback (lt : α → α → Bool) (x y : α) : Bool := lt y x
def leFallback (lt eq : α → α → Bool) (x y : α) : Bool := lt x y || eq x y
def leGeneric (lt : α → α → β) (eq : α → α → γ) (bitOr : β → γ → δ)
    (x y : α) : δ := bitOr (lt x y) (eq x y)
def geFallback (le : α → α → Bool) (x y : α) : Bool := le y x
def geGeneric (le : α → α → β) (x y : α) : β := le y x
def cmp (lt : α → α → Bool) (x y : α) : Int :=
  if lt x y then -1 else if lt y x then 1 else 0
def max (lt : α → α → Bool) (x y : α) : α := if lt y x then x else y
def min (lt : α → α → Bool) (x y : α) : α := if lt y x then y else x
def minmax (lt : α → α → Bool) (x y : α) : α × α := if lt y x then (y, x) else (x, y)

/-- Identity unary arithmetic methods; `base/operators.jl:605-611`. -/
def identity (x : α) : α := x

/-- `afoldl`; the source manually unrolls the first 31 applications and then
continues with the same left fold; `base/operators.jl:622-663`. -/
def afoldl (op : α → α → α) (a : α) (bs : List α) : α := bs.foldl op a

/-- Generated n-ary arithmetic methods; `base/operators.jl:666-675`. -/
def nary (op : α → α → α) (a b c : α) (xs : List α) : α :=
  afoldl op (op (op a b) c) xs

def intMin : Int := -(2^63)
def intMax : Int := 2^63 - 1

/-- Generic integer-count left shift; `base/operators.jl:735-740`. -/
def shiftLeftInteger (shiftInt : α → Int → α) (zero negOne : α)
    (nonnegative : α → Bool) (x : α) (c : Int) : α :=
  if intMin ≤ c && c ≤ intMax then shiftInt x c
  else if nonnegative x || 0 ≤ c then shiftInt zero 0 else negOne

/-- Generic integer-count arithmetic right shift; `base/operators.jl:780-788`. -/
def shiftRightInteger (shiftInt : α → Int → α) (zero negOne : α)
    (nonnegative : α → Bool) (x : α) (c : Int) : α :=
  if intMin ≤ c && c ≤ intMax then shiftInt x c
  else if nonnegative x || c < 0 then shiftInt zero 0 else negOne

/-- The `>>(x::Integer,c::Integer)` method rejects a machine `UInt` before its
range test; `base/operators.jl:780-788`. -/
def shiftRightGenericCount (shiftInt : α → Int → α) (zero negOne : α)
    (nonnegative : α → Bool) (x : α) (c : Int) (isMachineUInt : Bool) : Jl α :=
  if isMachineUInt then .error (.methodError ">>")
  else .ok (shiftRightInteger shiftInt zero negOne nonnegative x c)

/-- Generic integer-count logical right shift; `base/operators.jl:818-821`. -/
def shiftUnsignedRightInteger (shiftInt : α → Int → α) (zero : α) (x : α) (c : Int) : α :=
  if intMin ≤ c && c ≤ intMax then shiftInt x c else shiftInt zero 0

/-- Signed Int count redirects negative counts to the opposite shift;
`base/operators.jl:748,789,829`. -/
def shiftSignedCount (forward backward : α → Nat → α) (x : α) (c : Int) : α :=
  if 0 ≤ c then forward x c.toNat else backward x (-c).toNat

/-- Unsigned-count overloads, including the deliberate UInt MethodError;
`base/operators.jl:741-747,822-828`. -/
def shiftUnsignedCount (fn : α → Nat → α) (zero : α) (x : α)
    (c : Nat) (isMachineUInt : Bool) : Jl α :=
  if isMachineUInt then .error (.methodError "shift")
  else if c ≤ 2^64 - 1 then .ok (fn x c) else .ok (fn zero 0)

/-- `mod1`, `cldmod1`, and `fldmod1`; `base/operators.jl:914-952`. -/
def mod1 (mod : α → α → α) (iszero : α → Bool) (x y : α) : α :=
  let m := mod x y
  if iszero m then y else m
def cldmod1 (cld : α → α → β) (mod1 : α → α → γ) (x y : α) : β × γ :=
  (cld x y, mod1 x y)
def fldmod1 (fld1 : α → α → β) (mod1 : α → α → γ) (x y : α) : β × γ :=
  (fld1 x y, mod1 x y)

/-- Generic left division; `base/operators.jl:709`. -/
def leftDiv (adjoint : α → α) (div : α → α → α) (x y : α) : α :=
  adjoint (div (adjoint y) (adjoint x))

/-- `widen(x)`; `base/operators.jl:975`. -/
def widenValue (widenType : α → β) (convert : β → α → γ) (typeOf : α → α) (x : α) : γ :=
  convert (widenType (typeOf x)) x

def widenTypeError (typeName : String) : Jl α := .error (.methodError typeName)

/-- Function piping; `base/operators.jl:1001`. -/
def pipe (x : α) (f : α → β) : β := f x

/-- Stable type tags used by Returns and Fix constructors;
`base/operators.jl:1003-1004`. -/
def stableTypeof (typeOf : α → β) (x : α) : β := typeOf x
def stableTypeofType (hasFreeVars : α → Bool) (typeTag dataType : β) (t : α) : β :=
  if !hasFreeVars t then typeTag else dataType

structure Returns (α : Type) where value : α
def returnsTyped (value : α) : Returns α := ⟨value⟩
def returnsStable (value : α) : Returns α := ⟨value⟩
def Returns.call (r : Returns α) (_ : List β) : α := r.value

structure Composed (α : Type) where
  functions : List (α → α)

/-- `call_composed` and the ComposedFunction call; `base/operators.jl:1125-1129`. -/
def callComposed (fs : List (α → α)) (x : α) : α := fs.foldr (fun f x => f x) x
def Composed.call (c : Composed α) (x : α) : α := callComposed c.functions x
def compose1 (f : α → α) : Composed α := ⟨[f]⟩
def compose2 (f g : α → α) : Composed α := ⟨[f, g]⟩
def composeMany (f g : α → α) (hs : List (α → α)) : Composed α := ⟨f :: g :: hs⟩
def unwrapComposed (c : Composed α) : List (α → α) := c.functions
def unwrapSingle (f : α → α) : List (α → α) := [f]

/-- `Constructor{F}` and `maybeconstructor` preserve the callable behaviour;
`base/operators.jl:1131-1134`. -/
def constructorCall (f : List α → β) (args : List α) : β := f args
def maybeConstructorType (f : List α → β) : List α → β := f
def maybeConstructorValue (f : List α → β) : List α → β := f

/-- Observable text of composition show methods; `base/operators.jl:1140-1158`. -/
def showComposed (render showPart : α → String) (outerIsComposed : Bool)
    (outer inner : α) : String :=
  (if outerIsComposed then render outer else showPart outer) ++ " ∘ " ++ showPart inner
def showNegatedComposed (render : α → String) (inner : α) : String := "!" ++ render inner
def showComposedPart (render : α → String) (isOperator isNested : Bool) (x : α) : String :=
  if isOperator || isNested then "(" ++ render x ++ ")" else render x

/-- Predicate negation and its double-negation specialization;
`base/operators.jl:1182-1183`. -/
def negatePredicate (f : α → Bool) : α → Bool := fun x => !f x
def doubleNegationInner (f : α → Bool) : α → Bool := f

structure Fix (α β : Type) where
  n : Nat
  f : List α → β
  value : α

/-- `Fix{N}(f,x)` validates that N is an Int and positive;
`base/operators.jl:1206-1213`. -/
def Fix.make (n : Option Int) (f : List α → β) (value : α) : Jl (Fix α β) :=
  match n with
  | none => .error (.argumentError "Fix index must be Int")
  | some n =>
    if n < 1 then .error (.argumentError "Fix index must be positive")
    else .ok ⟨n.toNat, f, value⟩

/-- General Fix insertion; `base/operators.jl:1206-1224`. -/
def Fix.call (fix : Fix α β) (args : List α) : Jl β :=
  if fix.n < 1 then .error (.argumentError "Fix position")
  else if args.length < fix.n - 1 then .error (.argumentError "Fix arguments")
  else .ok (fix.f (args.take (fix.n - 1) ++ [fix.value] ++ args.drop (fix.n - 1)))

/-- Unary comparison constructors are `Fix2`; `base/operators.jl:1259-1335`. -/
def fix2 (f : α → α → β) (x : α) : α → β := fun y => f y x
def fixSecond (f : α → β → γ) (x : β) : α → γ := fun y => f y x

def fix1Call (f : α → α → β) (fixed arg : α) : β := f fixed arg
def fix2Call (f : α → α → β) (fixed arg : α) : β := f arg fixed

def showFix (renderF : (List α → β) → String) (render : α → String) (fix : Fix α β) : String :=
  "Fix{" ++ toString fix.n ++ "}(" ++ renderF fix.f ++ ", " ++ render fix.value ++ ")"

structure Splat (α β : Type) where f : List α → β
def Splat.call (s : Splat α β) (args : List α) : β := s.f args
def splat (f : List α → β) : Splat α β := ⟨f⟩
def unsplat (f : List α → β) : List α → β := fun args => f args
def unsplatSplat (s : Splat α β) : List α → β := s.f
def splatUnsplat (f : List α → β) : List α → β := f
def showSplat (render : (List α → β) → String) (s : Splat α β) : String :=
  "splat(" ++ render s.f ++ ")"

/-- `tap(f)`; `base/operators.jl:1438`. -/
def tap (f : α → β) : α → α := fun x => let _ := f x; x

inductive Truth where | false | missing | true
  deriving BEq, Repr

def Truth.not : Truth → Truth
  | .false => .true | .true => .false | .missing => .missing

def Truth.or : Truth → Truth → Truth
  | .true, _ | _, .true => .true
  | .missing, _ | _, .missing => .missing
  | .false, .false => .false

/-- Generic iterable membership with three-valued equality;
`base/operators.jl:1455`. -/
def mem (eq : α → α → Truth) (x : α) : List α → Truth
  | [] => .false
  | y :: ys => Truth.or (eq y x) (mem eq x ys)

/-- `∉`, `∋`, and `∌`; `base/operators.jl:1477-1500`. -/
def notMem (m : α → β → Truth) (x : α) (ys : β) : Truth := (m x ys).not
def contains (m : α → β → Truth) (ys : β) (x : α) : Truth := m x ys
def notContains (m : α → β → Truth) (ys : β) (x : α) : Truth := (m x ys).not

end OperatorModel

end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Operators

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def m86 (compute : α → Unit) (super : α → β) (t : α) : β :=
  let _ := compute t; super t
def m95 (isSuper : σ → Bool) (super : α → β) (field : α → σ → β) (t : α) (s : σ) : β :=
  if isSuper s then super t else field t s
def m102 (wrap : α → β → γ) (super : β → β) (v : α) (body : β) : γ := wrap v (super body)
def m104 (anyType : α) : α := anyType
def m105 (typeOf : α → β) (p : α) : β := typeOf p
def m196 (eq : α → β → Bool) (x : α) (y : β) : Bool := eq x y
def m198 (signbit : α → Bool) (x y : α) : Bool := signbit x == signbit y
def m199 (signbit : α → Bool) (x y : α) : Bool := signbit x && !signbit y
def m201 (isnan : α → Bool) (signbit : α → Bool) (eq : α → α → Bool) (x y : α) : Bool :=
  (isnan x && isnan y) || ((signbit x == signbit y) && eq x y)
def m202 (isnanA : α → Bool) (isnanB : β → Bool) (signA : α → Bool)
    (signB : β → Bool) (eq : α → β → Bool) (x : α) (y : β) : Bool :=
  (isnanA x && isnanB y) || ((signA x == signB y) && eq x y)
def m240 (isnan : α → Bool) (signbit : α → Bool) (lt : α → α → Bool) (x y : α) : Bool :=
  (!isnan x && (isnan y || (signbit x && !signbit y))) || lt x y
def m248 (lt eq : α → α → Bool) (a b : α × α) : Bool :=
  lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2)
def m309 (_ : α) : Bool := false
def m310 (isnan : α → Bool) (x : α) : Bool := isnan x
def m313 (typesEqual : α → α → Bool) (t s : α) : Bool := typesEqual t s
def m314 (_ : α) (_ : β) : Bool := false
def m315 := @m314
def m338 (eq : α → β → γ) (not : γ → δ) (x : α) (y : β) : δ := not (eq x y)
def m417 (isless : α → β → Bool) (x : α) (y : β) := isless x y
def m443 (lt : β → α → Bool) (x : α) (y : β) := lt y x
def m467 (lt : α → β → γ) (eq : α → β → δ) (bitOr : γ → δ → ε) (x : α) (y : β) :=
  bitOr (lt x y) (eq x y)
def m499 (le : β → α → γ) (x : α) (y : β) := le y x
def m526 (isless : α → α → Bool) (x y : α) : Int :=
  if isless x y then -1 else if isless y x then 1 else 0
def m534 (lt : α → α → Bool) (x y : α) : Int :=
  if lt x y then -1 else if lt y x then 1 else 0
def m588 (isless : α → α → Bool) (x y : α) : α × α := if isless y x then (y, x) else (x, y)
def m605 (x : α) := x
def m607 := @m605
def m608 := @m605
def m609 := @m605
def m610 := @m605
def m611 := @m605
def m622 (_op : α → α → α) (a : α) : α := a
def m623 (op : α → α → α) (a : α) (bs : List α) := bs.foldl op a
def m671 (op : α → α → α) (a b c : α) (xs : List α) := xs.foldl op (op (op a b) c)
def m709 (adj : α → α) (div : α → α → α) (x y : α) := adj (div (adj y) (adj x))
def m735 (shift : α → Int → α) (zero negOne : α) (nonneg : α → Bool) x c :=
  OperatorModel.shiftLeftInteger shift zero negOne nonneg x c
def m741 (shift : α → Nat → α) (zero x : α) (c : Nat) (isUInt : Bool) : Jl α :=
  if isUInt then .error (.methodError "<<")
  else if c ≤ 2^64 - 1 then .ok (shift x c) else .ok (shift zero 0)
def m748 (left right : α → Nat → α) x c := OperatorModel.shiftSignedCount left right x c
def m780 (shift : α → Int → α) (zero negOne : α) (nonneg : α → Bool) x c isUInt :=
  OperatorModel.shiftRightGenericCount shift zero negOne nonneg x c isUInt
def m789 (right left : α → Nat → α) x c := OperatorModel.shiftSignedCount right left x c
def m818 (shift : α → Int → α) zero x c := OperatorModel.shiftUnsignedRightInteger shift zero x c
def m822 (shift : α → Nat → α) (zero x : α) (c : Nat) (isUInt : Bool) : Jl α :=
  if isUInt then .error (.methodError ">>>")
  else if c ≤ 2^64 - 1 then .ok (shift x c) else .ok (shift zero 0)
def m829 (right left : α → Nat → α) x c := OperatorModel.shiftSignedCount right left x c
def m914 (mod : α → α → α) (zero : α → Bool) x y := OperatorModel.mod1 mod zero x y
def m943 (cld : α → α → β) (mod1 : α → α → γ) x y := (cld x y, mod1 x y)
def m952 (fld1 : α → α → β) (mod1 : α → α → γ) x y := (fld1 x y, mod1 x y)
def m975 (typeOf : α → β) (widenType : β → γ) (convert : γ → α → δ) x :=
  convert (widenType (typeOf x)) x
def m976 (name : String) : Jl α := .error (.methodError name)
def m977 := @m976
def m1001 (x : α) (f : α → β) := f x
def m1003 (typeOf : α → β) x := typeOf x
def m1004 (hasFree : α → Bool) (typeTag dataType : β) t := if !hasFree t then typeTag else dataType
structure ReturnsF (α : Type) where value : α
def m1031 (value : α) : ReturnsF α := ⟨value⟩
def m1032 := @m1031
def m1035 (r : ReturnsF α) (_args : β) (_kw : γ) : α := r.value
structure ComposedF (O I : Type) where
  outer : O
  inner : I
def m1121 (o : O) (i : I) : ComposedF O I := ⟨o, i⟩
def m1122 := @m1121
def m1125 (unwrap : ComposedF O I → F) (call : F → X → K → Y)
    (c : ComposedF O I) (x : X) (kw : K) := call (unwrap c) x kw
def m1126 (unwrapO : O → List F) (unwrapI : I → List F) (c : ComposedF O I) :=
  unwrapO c.outer ++ unwrapI c.inner
def m1127 (maybe : α → β) (x : α) : List β := [maybe x]
def m1128 (head : F → A → B) (tailCall : Fs → X → K → A)
    (fsHead : F) (fsTail : Fs) (x : X) (kw : K) :=
  head fsHead (tailCall fsTail x kw)
def m1129 (call : F → X → K → Y) (f : F) (x : X) (kw : K) := call f x kw
def m1132 (call : F → A → K → Y) (f : F) (a : A) (kw : K) := call f a kw
def m1133 (wrap : F → C) (f : F) := wrap f
def m1134 (f : F) := f
def m1136 (f : F) := f
def m1137 (f : O) (g : I) := ComposedF.mk f g
def m1138 (compose2 : A → B → C) (composeRest : C → H → R)
    (f : A) (g : B) (rest : H) : R := composeRest (compose2 f g) rest
def m1140 (showOuter showPartOuter : α → String) (showPartInner : β → String)
    (nested : Bool) (outer : α) (inner : β) :=
  (if nested then showOuter outer else showPartOuter outer) ++ " ∘ " ++ showPartInner inner
def m1147 (showPart : α → String) (inner : α) := "!" ++ showPart inner
def m1152 (render : α → String) (x : α) := render x
def m1154 (operator : α → Bool) (render : α → String) (x : α) :=
  if operator x then "(" ++ render x ++ ")" else render x
def m1156 (render : α → String) (x : α) := "(" ++ render x ++ ")"
def m1158 := @m1152
def m1182 (f : α → Bool) : α → Bool := fun x => !f x
def m1183 (inner : F) := inner
structure FixF (F X : Type) where
  f : F
  x : X
def m1206 (n : Option Int) (f : F) (x : X) : Jl (FixF F X) :=
  match n with
  | none => .error (.argumentError "Fix index must be Int")
  | some n => if n < 1 then .error (.argumentError "Fix index must be positive") else .ok ⟨f, x⟩
def m1216 (n m : Int) (split : Args → Int → L × R)
    (call : F → L → X → R → K → Y) (f : FixF F X) (args : Args) (kw : K) : Jl Y :=
  if m < n - 1 then .error (.argumentError "Fix arguments")
  else let p := split args (n - 1); .ok (call f.f p.1 f.x p.2 kw)
def m1223 (call : F → X → A → K → Y) (f : FixF F X) (arg : A) (kw : K) := call f.f f.x arg kw
def m1224 (call : F → A → X → K → Y) (f : FixF F X) (arg : A) (kw : K) := call f.f arg f.x kw
def m1226 (showF : F → String) (showX : X → String) (n : Int) (f : FixF F X) :=
  "Fix{" ++ toString n ++ "}(" ++ showF f.f ++ ", " ++ showX f.x ++ ")"
def fixSecond (f : α → β → γ) (x : β) : α → γ := fun y => f y x
def m1259 := @fixSecond
def m1270 := @fixSecond
def m1283 := @fixSecond
def m1296 := @fixSecond
def m1309 := @fixSecond
def m1322 := @fixSecond
def m1335 := @fixSecond
structure SplatF (F : Type) where f : F
def m1366 (f : F) := SplatF.mk f
def m1384 := @m1366
def m1386 (apply : F → Args → Y) (s : SplatF F) (args : Args) := apply s.f args
def m1387 (render : F → String) (s : SplatF F) := "splat(" ++ render s.f ++ ")"
def m1415 (compose : F → TupleF → C) f tupleF := compose f tupleF
def m1416 (s : SplatF F) := s.f
def m1417 (outer : F) := outer
def m1438 (f : α → β) : α → α := fun x => let _ := f x; x
def m1453 := @fixSecond
def m1455 (any : (α → γ) → I → γ) (eq : X → α → γ) x itr := any (eq x) itr
def m1477 (mem : α → β → γ) (not : γ → δ) x y := not (mem x y)
def m1478 := @fixSecond
def m1486 (mem : α → β → γ) (itr : β) (x : α) := mem x itr
def m1497 := @fixSecond
def m1499 (contains : β → α → γ) (not : γ → δ) itr x := not (contains itr x)
def m1500 := @fixSecond

end JuliaLean.NumbersCov.Rows.Operators

namespace JuliaLean.HashOps

open JuliaLean

structure FallbackOps (α : Type) where
  eq : α → α → Bool
  lt : α → α → Bool
  zero : α → α
  one : α → α
  neg : α → α
  add : α → α → α
  mul : α → α → α
  div : α → α → α
  castOne : α → α

def isequalFallback (o : FallbackOps α) (x y : α) : Bool := o.eq x y
def islessFallback (o : FallbackOps α) (x y : α) : Bool := o.lt x y
def cmpFallback (o : FallbackOps α) (x y : α) : Int :=
  if islessFallback o x y then -1 else if islessFallback o y x then 1 else 0
def neFallback (o : FallbackOps α) (x y : α) : Bool := !o.eq x y
def leFallback (o : FallbackOps α) (x y : α) : Bool := o.lt x y || o.eq x y
def geFallback (o : FallbackOps α) (x y : α) : Bool := leFallback o y x

/-! ## `widen`, `base/operators.jl:955-977`, `base/int.jl:911-918` -/

def widenTarget : IntTy → Option IntTy
  | .i8 => some .i16 | .i16 => some .i32 | .i32 => some .i64 | .i64 => some .i128
  | .u8 => some .u16 | .u16 => some .u32 | .u32 => some .u64 | .u64 => some .u128
  | .i128 | .u128 => none

def widenAdd (t : IntTy) (x y : JInt t) : Int :=
  match widenTarget t with
  | some s => wrapInt s (x.val + y.val)
  | none => x.val + y.val

def widenSub (t : IntTy) (x y : JInt t) : Int :=
  match widenTarget t with
  | some s => wrapInt s (x.val - y.val)
  | none => x.val - y.val

end JuliaLean.HashOps

namespace JuliaLean.Promotion

open JuliaLean.Float

/-- `isequal(x::AbstractFloat, y::Real)`; `base/operators.jl:203`. -/
def isequalFI {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Bool :=
  (x.signbit == decide (y.val < 0)) && cmpFI .eq x y

/-- `isless(x::AbstractFloat, y::Real)`; `base/operators.jl:242`. -/
def islessFI {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Bool :=
  (!x.isnan && (x.signbit && !decide (y.val < 0))) || cmpFI .lt x y

/-- `isless(x::Real, y::AbstractFloat)`; `base/operators.jl:241`. -/
def islessIF {T : FTy} {t : IntTy} (x : JInt t) (y : FV T) : Bool :=
  (y.isnan || (decide (x.val < 0) && !y.signbit)) || cmpIF .lt x y

/-- `cmp(x, y)`; `base/operators.jl:526`. -/
def cmpOrderFI {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Int :=
  if islessFI x y then -1 else if islessIF y x then 1 else 0

/-- `cmp(a, b)` on integers, `base/operators.jl:537`. -/
def icmp (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

end JuliaLean.Promotion

namespace JuliaLean.IntArith.Rational

open JuliaLean

/-- Generic `cmp`, through `isless(::Real,::Real)`;
base/operators.jl:505,526. -/
def cmp (lt : ∀ {t s : IntTy}, Rat t → Rat s → Bool) {t s} (x : Rat t) (y : Rat s) : JInt .i64 :=
  JInt.lit .i64 (if lt x y then -1 else if lt y x then 1 else 0)

end JuliaLean.IntArith.Rational

namespace JuliaLean.ArrayOps

open JuliaLean
open JuliaLean.Float

variable {α β : Type}

/-- `isgreater(x, y)`, `base/operators.jl:295`, with `isunordered = isnan` for floats. -/
def isgreater (x y : F64) : Bool :=
  if F64.isnan x || F64.isnan y then F64.isless x y else F64.isless y x

end JuliaLean.ArrayOps

namespace JuliaLean.IdDicts

/-- `isequal` on the universe (base/operators.jl; `isequal(1, 1.0)`,
`isequal([1], [1.0])`). -/
def isequal : JVal → JVal → Bool
  | .int a, .int b => a == b
  | .int a, .flt b => a == b
  | .flt a, .int b => a == b
  | .flt a, .flt b => a == b
  | .sym a, .sym b => a == b
  | .str a, .str b => a == b
  | .vec _ a, .vec _ b => a == b
  | .vec _ a, .fvec _ b => a == b
  | .fvec _ a, .vec _ b => a == b
  | .fvec _ a, .fvec _ b => a == b
  | .nothing, .nothing => true
  | _, _ => false

end JuliaLean.IdDicts
