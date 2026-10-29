import JuliaLean.Core
import JuliaLean.base.tuple
import JuliaLean.src.julia_h
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
def mod1 (mod : α → α → Jl α) (iszero : α → Jl Bool) (x y : α) : Jl α := do
  let m ← mod x y
  if ← iszero m then pure y else pure m

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
def returnsTyped (typeParam : τ) (value : α) : Returns τ α := ⟨typeParam, value⟩

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
def composedTyped (outer : α) (inner : β) : ComposedFunction α β := ⟨outer, inner⟩

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
