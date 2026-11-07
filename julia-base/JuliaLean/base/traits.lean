import JuliaLean.Core

/-!
# Model of `base/traits.jl`

`JTypeModel` captures the type categories used by these traits. Tuple types carry the result
of Julia's `isconcretetype`; their fields are structural, so `OrderStyle` recursively checks
field types. Type lookup and `RangeStepStyle` methods added by other Base files remain explicit
parameters.
-/

namespace JuliaLean.base.traits

inductive JTypeModel where
  | bottom
  | integer
  | abstractInteger
  | bool
  | float
  | abstractFloat
  | real
  | abstractReal
  | rational
  | complex
  | abstractString
  | string
  | symbol
  | tuple (concrete : Bool) (fields : List JTypeModel)
  | variableTuple
  | other
  deriving Repr, Inhabited

def JTypeModel.isInteger : JTypeModel → Bool
  | .integer | .abstractInteger | .bool => true
  | _ => false

def JTypeModel.isAbstractFloat : JTypeModel → Bool
  | .float | .abstractFloat => true
  | _ => false

def JTypeModel.isReal (t : JTypeModel) : Bool :=
  t.isInteger || t.isAbstractFloat || (match t with | .real | .abstractReal | .rational => true | _ => false)

def JTypeModel.isString : JTypeModel → Bool
  | .string | .abstractString => true
  | _ => false


inductive TraitError where
  | methodError (functionName : String)
  deriving BEq, DecidableEq, Repr

/--
Julia source: base/traits.jl:5-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type OrderStyle end
struct Ordered <: OrderStyle end
struct Unordered <: OrderStyle end
```
-/

inductive OrderStyle where
  | ordered
  | unordered
  deriving BEq, DecidableEq, Repr, Inhabited

/--
Julia source: base/traits.jl:17-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function OrderStyle(T::Type{<:Tuple})
    isconcretetype(T) || return Unordered()
    all(map(S -> OrderStyle(S) === Ordered(), fieldtypes(T))) ? Ordered() : Unordered()
end
```
-/

def orderStyleTuple (concrete : Bool) (styles : List OrderStyle) : OrderStyle :=
  if !concrete then .unordered
  else if styles.all (· == .ordered) then .ordered else .unordered

/--
Julia source: base/traits.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OrderStyle(instance) = OrderStyle(typeof(instance))
OrderStyle(::Type{<:Real}) = Ordered()
OrderStyle(::Type{<:AbstractString}) = Ordered()
OrderStyle(::Type{Symbol}) = Ordered()
OrderStyle(::Type{<:Any}) = Unordered()
OrderStyle(::Type{Union{}}) = Ordered()
OrderStyle(::Type{Union{}}, slurp...) = throw(MethodError(OrderStyle, (Union{}, slurp...)))
```
-/

def orderStyleType : JTypeModel → OrderStyle
  | .bottom => .ordered
  | .tuple concrete fields =>
      orderStyleTuple concrete (fields.attach.map fun ⟨field, _⟩ => orderStyleType field)
  | .variableTuple => .unordered
  | t => if t.isReal then .ordered else if t.isString then .ordered
      else match t with | .symbol => .ordered | _ => .unordered
termination_by typeModel => sizeOf typeModel
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem ‹_ ∈ fields›)
  all_goals omega

def orderStyleInstance {X : Type} (typeOf : X → JTypeModel) (x : X) : OrderStyle :=
  orderStyleType (typeOf x)

def orderStyleBottomExtra {X : Type} (_firstExtra : X) (_rest : List X) :
    Except TraitError OrderStyle := .error (.methodError "OrderStyle")

/--
Julia source: base/traits.jl:23-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type ArithmeticStyle end
struct ArithmeticRounds <: ArithmeticStyle end     # least significant bits can be lost
struct ArithmeticWraps <: ArithmeticStyle end      #  most significant bits can be lost
struct ArithmeticUnknown <: ArithmeticStyle end
```
-/

inductive ArithmeticStyle where
  | rounds
  | wraps
  | unknown
  deriving BEq, DecidableEq, Repr, Inhabited

/--
Julia source: base/traits.jl:28-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ArithmeticStyle(instance) = ArithmeticStyle(typeof(instance))
ArithmeticStyle(::Type{<:AbstractFloat}) = ArithmeticRounds()
ArithmeticStyle(::Type{<:Integer}) = ArithmeticWraps()
ArithmeticStyle(::Type{<:Any}) = ArithmeticUnknown()
ArithmeticStyle(::Type{Union{}}) = ArithmeticUnknown()
ArithmeticStyle(::Type{Union{}}, slurp...) = throw(MethodError(ArithmeticStyle, (Union{}, slurp...)))
```
-/

def arithmeticStyleType (t : JTypeModel) : ArithmeticStyle :=
  if t.isAbstractFloat then .rounds else if t.isInteger then .wraps else .unknown

def arithmeticStyleInstance {X : Type} (typeOf : X → JTypeModel) (x : X) : ArithmeticStyle :=
  arithmeticStyleType (typeOf x)

def arithmeticStyleBottomExtra {X : Type} (_firstExtra : X) (_rest : List X) :
    Except TraitError ArithmeticStyle := .error (.methodError "ArithmeticStyle")

/--
Julia source: base/traits.jl:66-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type RangeStepStyle end
struct RangeStepRegular   <: RangeStepStyle end # range with regular step
struct RangeStepIrregular <: RangeStepStyle end # range with rounding error
```
-/

inductive RangeStepStyle where
  | regular
  | irregular
  deriving BEq, DecidableEq, Repr, Inhabited

/--
Julia source: base/traits.jl:69-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RangeStepStyle(::Type{Union{}}) = RangeStepIrregular()
RangeStepStyle(::Type{Union{}}, slurp...) = throw(MethodError(RangeStepStyle, (Union{}, slurp...)))
```
-/

def rangeStepStyleBottom : RangeStepStyle := .irregular

def rangeStepStyleBottomExtra {X : Type} (_firstExtra : X) (_rest : List X) :
    Except TraitError RangeStepStyle := .error (.methodError "RangeStepStyle")

/--
Julia source: base/traits.jl:72-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RangeStepStyle(instance) = RangeStepStyle(typeof(instance))
```
-/

def rangeStepStyleInstance {X : Type} (typeOf : X → JTypeModel)
    (dispatch : JTypeModel → Except TraitError RangeStepStyle) (x : X) :
    Except TraitError RangeStepStyle := dispatch (typeOf x)

end JuliaLean.base.traits


/-!
# Type traits: `base/traits.jl` and the `IndexStyle` methods of `base/indices.jl`

Master `bbfa0ce4150`. A Julia type is a `JT`; a call argument is either a type
`T` itself (`TArg.ty T`, the argument `Int` in `OrderStyle(Int)`) or an instance
of the concrete type `T` (`TArg.inst T`, the argument `1`). The typeof of any
type in this universe is `DataType`.
-/

namespace JuliaLean.ReduceCov

/-- The modelled Julia types. -/
inductive JT where
  | int (t : IntTy)
  | bool
  | bigInt
  | f64
  | f32
  | f16
  | bigFloat
  /-- `Rational{Int}`. -/
  | rational
  /-- `Complex{Float64}`. -/
  | complex
  | string
  | symbol
  | char
  | missing
  | nothing
  /-- `Tuple{fs...}`. -/
  | tuple (fs : List JT)
  /-- `Tuple{Vararg{t}}`, not a concrete type. -/
  | vtuple (t : JT)
  /-- `Vector{t}`. -/
  | vec (t : JT)
  /-- A concrete `AbstractRange{t}` such as `UnitRange{t}`. -/
  | range (t : JT)
  /-- The abstract types `Integer`, `AbstractFloat`, `Real`, `Number`, `Any`. -/
  | absInteger
  | absFloat
  | absReal
  | number
  | any
  /-- `DataType`, the type of every other type here. -/
  | dataType
  /-- `Union{}`. -/
  | bottom
  deriving Repr, Inhabited

namespace JT

/-- `T <: Integer` for `T ≠ Union{}`. -/
def isInteger : JT → Bool
  | .int _ | .bool | .bigInt | .absInteger => true
  | _ => false

/-- `T <: AbstractFloat` for `T ≠ Union{}`. -/
def isAbstractFloat : JT → Bool
  | .f64 | .f32 | .f16 | .bigFloat | .absFloat => true
  | _ => false

/-- `T <: Real` for `T ≠ Union{}`. -/
def isReal (t : JT) : Bool :=
  t.isInteger || t.isAbstractFloat || (match t with | .rational | .absReal => true | _ => false)

/-- `T <: AbstractString`. -/
def isString : JT → Bool
  | .string => true
  | _ => false

/-- `T <: Tuple` for `T ≠ Union{}`. -/
def isTuple : JT → Bool
  | .tuple _ | .vtuple _ => true
  | _ => false

/-- `isconcretetype(T)`. -/
def isConcrete : JT → Bool
  | .tuple fs => fs.attach.all fun ⟨f, _⟩ => f.isConcrete
  | .vtuple _ | .absInteger | .absFloat | .absReal | .number | .any | .bottom => false
  | _ => true

/-- `fieldtypes(T)` of a tuple type. -/
def fieldtypes : JT → List JT
  | .tuple fs => fs
  | _ => []

end JT

/-- A call argument: a type, or an instance of a concrete type. -/
inductive TArg where
  | ty (t : JT)
  | inst (t : JT)
  deriving Inhabited

/-! ## `OrderStyle`, `base/traits.jl:4-20` -/

inductive OrderStyleV where
  | ordered
  | unordered
  deriving DecidableEq, Repr

/-- `OrderStyle(::Type{<:Real}) = Ordered()`, `base/traits.jl:10`. -/
def orderStyleReal : OrderStyleV := .ordered

/-- `OrderStyle(::Type{<:AbstractString}) = Ordered()`, `base/traits.jl:11`. -/
def orderStyleString : OrderStyleV := .ordered

/-- `OrderStyle(::Type{Symbol}) = Ordered()`, `base/traits.jl:12`. -/
def orderStyleSymbol : OrderStyleV := .ordered

/-- `OrderStyle(::Type{<:Any}) = Unordered()`, `base/traits.jl:13`. -/
def orderStyleAny : OrderStyleV := .unordered

/-- `OrderStyle(::Type{Union{}}) = Ordered()`, `base/traits.jl:14`. -/
def orderStyleBottom : OrderStyleV := .ordered

/-- `OrderStyle(T::Type{<:Tuple})`, `base/traits.jl:17-20`:
`isconcretetype(T) || return Unordered()`, then
`all(map(S -> OrderStyle(S) === Ordered(), fieldtypes(T))) ? Ordered() : Unordered()`;
`styles` are the `OrderStyle`s of the field types. -/
def orderStyleTuple (concrete : Bool) (styles : List OrderStyleV) : OrderStyleV :=
  if !concrete then .unordered
  else if styles.all (· == .ordered) then .ordered else .unordered

/-- `OrderStyle(T::Type)`, dispatching to the most specific method: `Union{}`, tuples,
`OrderStyle(::Type{<:AbstractVector{T}}) = OrderStyle(T)` (`base/abstractarray.jl:3147`,
ranges are vectors), `Real`, `AbstractString`, `Symbol` and the `Type{<:Any}` fallback. -/
def orderStyleTy : JT → OrderStyleV
  | .bottom => orderStyleBottom
  | .tuple fs =>
    orderStyleTuple (JT.tuple fs).isConcrete (fs.attach.map fun ⟨f, _⟩ => orderStyleTy f)
  | .vtuple _ => orderStyleTuple false []
  | .vec t => orderStyleTy t
  | .range t => orderStyleTy t
  | t => if t.isReal then orderStyleReal else if t.isString then orderStyleString
    else match t with
      | .symbol => orderStyleSymbol
      | _ => orderStyleAny

/-- `OrderStyle(instance) = OrderStyle(typeof(instance))`, `base/traits.jl:9`. -/
def orderStyle : TArg → OrderStyleV
  | .ty t => orderStyleTy t
  | .inst t => orderStyleTy t

/-- `OrderStyle(::Type{Union{}}, slurp...)`, `base/traits.jl:15`. -/
def orderStyleBottomSlurp : Jl OrderStyleV := .error (.methodError "OrderStyle")

/-! ## `ArithmeticStyle`, `base/traits.jl:22-33` -/

inductive ArithmeticStyleV where
  | rounds
  | wraps
  | unknown
  deriving DecidableEq, Repr

/-- `ArithmeticStyle(::Type{<:AbstractFloat}) = ArithmeticRounds()`, `base/traits.jl:29`. -/
def arithmeticStyleFloat : ArithmeticStyleV := .rounds

/-- `ArithmeticStyle(::Type{<:Integer}) = ArithmeticWraps()`, `base/traits.jl:30`. -/
def arithmeticStyleInteger : ArithmeticStyleV := .wraps

/-- `ArithmeticStyle(::Type{<:Any}) = ArithmeticUnknown()`, `base/traits.jl:31`. -/
def arithmeticStyleAny : ArithmeticStyleV := .unknown

/-- `ArithmeticStyle(::Type{Union{}}) = ArithmeticUnknown()`, `base/traits.jl:32`. -/
def arithmeticStyleBottom : ArithmeticStyleV := .unknown

/-- `ArithmeticStyle(T::Type)`, dispatching to the most specific method. -/
def arithmeticStyleTy (t : JT) : ArithmeticStyleV :=
  match t with
  | .bottom => arithmeticStyleBottom
  | t => if t.isAbstractFloat then arithmeticStyleFloat
    else if t.isInteger then arithmeticStyleInteger else arithmeticStyleAny

/-- `ArithmeticStyle(instance) = ArithmeticStyle(typeof(instance))`, `base/traits.jl:28`. -/
def arithmeticStyle : TArg → ArithmeticStyleV
  | .ty t => arithmeticStyleTy t
  | .inst t => arithmeticStyleTy t

/-- `ArithmeticStyle(::Type{Union{}}, slurp...)`, `base/traits.jl:33`. -/
def arithmeticStyleBottomSlurp : Jl ArithmeticStyleV := .error (.methodError "ArithmeticStyle")

/-! ## `RangeStepStyle`, `base/traits.jl:35-72`, `base/range.jl:285-286` -/

inductive RangeStepStyleV where
  | regular
  | irregular
  deriving DecidableEq, Repr

/-- One dispatch step of `RangeStepStyle(x)`: a result, or the argument of the next
call. Methods: `RangeStepStyle(::Type{Union{}})` (`base/traits.jl:69`),
`RangeStepStyle(::Type{<:AbstractRange})` and
`RangeStepStyle(::Type{<:AbstractRange{<:Integer}})` (`base/range.jl:285-286`), and
`RangeStepStyle(instance) = RangeStepStyle(typeof(instance))` (`base/traits.jl:72`),
which every other argument reaches; a type is an instance of `DataType`. -/
def rangeStepStyleStep : TArg → RangeStepStyleV ⊕ TArg
  | .ty .bottom => .inl .irregular
  | .ty (.range t) => .inl (if t.isInteger then .regular else .irregular)
  | .ty _ => .inr (.ty .dataType)
  | .inst t => .inr (.ty t)

/-- `RangeStepStyle(x)` run for at most `fuel` calls; `none` when it has not returned. -/
def rangeStepStyle : Nat → TArg → Option RangeStepStyleV
  | 0, _ => none
  | fuel + 1, a =>
    match rangeStepStyleStep a with
    | .inl r => some r
    | .inr a' => rangeStepStyle fuel a'

/-- `RangeStepStyle(::Type{Union{}}, slurp...)`, `base/traits.jl:70`. -/
def rangeStepStyleBottomSlurp : Jl RangeStepStyleV := .error (.methodError "RangeStepStyle")

end JuliaLean.ReduceCov
