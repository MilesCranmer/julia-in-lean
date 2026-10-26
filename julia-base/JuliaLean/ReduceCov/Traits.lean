import JuliaLean.Core

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

/-- Types whose values `isless` totally orders: real numbers, strings, symbols,
concrete tuples and vectors of such values, and (vacuously) `Union{}`. -/
def totallyOrdered : JT → Bool
  | .bottom => true
  | .tuple fs => (JT.tuple fs).isConcrete && fs.attach.all fun ⟨f, _⟩ => totallyOrdered f
  | .vec t | .range t => totallyOrdered t
  | .int _ | .bool | .bigInt | .f64 | .f32 | .f16 | .bigFloat | .rational | .absInteger
  | .absFloat | .absReal | .string | .symbol => true
  | _ => false

/-- The `OrderStyle` trait, `base/traits.jl:4-20`: an instance has the style of its
type; a type is `Ordered` exactly when its values are totally ordered by `isless`
(real numbers, strings, symbols, and concrete tuples and vectors of those);
`OrderStyle(Union{}, x...)` throws `MethodError`. -/
def OrderStyleSpec : Prop :=
  (∀ t : JT, orderStyle (.inst t) = orderStyle (.ty t)) ∧
  (∀ t : JT, orderStyle (.ty t) = .ordered ↔ totallyOrdered t = true) ∧
  (∃ f, orderStyleBottomSlurp = .error (.methodError f))

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

/-- The comments at `base/traits.jl:24-26`: floating-point arithmetic rounds ("least
significant bits can be lost"), integer arithmetic wraps ("most significant bits
can be lost"), and every other type is unknown; instances follow their type. -/
def ArithmeticStyleSpec : Prop :=
  (∀ t : JT, arithmeticStyle (.inst t) = arithmeticStyle (.ty t)) ∧
  (∀ t : JT, arithmeticStyle (.ty t) =
    match t with
    | .bottom => .unknown
    | t => if t.isAbstractFloat then .rounds else if t.isInteger then .wraps else .unknown) ∧
  (∀ t, t.isInteger = true → arithmeticStyle (.inst t) = .wraps) ∧
  (∀ t, t.isAbstractFloat = true → arithmeticStyle (.inst t) = .rounds) ∧
  (∃ f, arithmeticStyleBottomSlurp = .error (.methodError f))

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

/-- The `RangeStepStyle` docstring, `base/traits.jl:35-65`: ranges with an integer
element type have regular steps, other ranges are irregular, and an instance
has the style of its type. -/
def RangeStepStyleRanges : Prop :=
  (∀ t : JT, rangeStepStyle 1 (.ty (.range t)) = some (if t.isInteger then .regular else .irregular)) ∧
  (∀ t : JT, rangeStepStyle 2 (.inst (.range t)) = rangeStepStyle 1 (.ty (.range t))) ∧
  rangeStepStyle 1 (.ty .bottom) = some .irregular ∧
  (∃ f, rangeStepStyleBottomSlurp = .error (.methodError f))

/-- A trait query terminates: every call `RangeStepStyle(x)` returns after
finitely many dispatch steps. -/
def RangeStepStyleTerminates : Prop :=
  ∀ a : TArg, ∃ n r, rangeStepStyle n a = some r

/-! ## `IndexStyle`, `base/indices.jl:94-104, 505` -/

inductive IndexStyleV where
  | linear
  | cartesian
  deriving DecidableEq, Repr

/-- Array types for `IndexStyle`: `Array`, ranges, `LinearIndices`, a type with
the `AbstractArray` default, a type that defines its own style, `Union{}`. -/
inductive ArrTy where
  | array
  | range
  | linearIndices
  | plain
  | custom (s : IndexStyleV)
  | bottom
  deriving DecidableEq, Repr

/-- `IndexStyle(::Type{Union{}}) = IndexLinear()`, `base/indices.jl:95`. -/
def indexStyleBottom : IndexStyleV := .linear

/-- `IndexStyle(::Type{<:AbstractArray}) = IndexCartesian()`, `base/indices.jl:97`. -/
def indexStyleAbstractArray : IndexStyleV := .cartesian

/-- `IndexStyle(::Type{<:Array}) = IndexLinear()`, `base/indices.jl:98`. -/
def indexStyleArray : IndexStyleV := .linear

/-- `IndexStyle(::Type{<:AbstractRange}) = IndexLinear()`, `base/indices.jl:99`. -/
def indexStyleRange : IndexStyleV := .linear

/-- `IndexStyle(::Type{<:LinearIndices}) = IndexLinear()`, `base/indices.jl:505`. -/
def indexStyleLinearIndices : IndexStyleV := .linear

/-- `IndexStyle(T)`, dispatching to the most specific method; a custom array type
defines its own method. -/
def indexStyleTy : ArrTy → IndexStyleV
  | .bottom => indexStyleBottom
  | .plain => indexStyleAbstractArray
  | .array => indexStyleArray
  | .range => indexStyleRange
  | .linearIndices => indexStyleLinearIndices
  | .custom s => s

/-- `IndexStyle(A::AbstractArray) = IndexStyle(typeof(A))`, `base/indices.jl:94`. -/
def indexStyle1 (a : ArrTy) : IndexStyleV := indexStyleTy a

/-- `IndexStyle(::IndexLinear, ::IndexLinear) = IndexLinear()` and
`IndexStyle(::IndexStyle, ::IndexStyle) = IndexCartesian()`, `base/indices.jl:103-104`. -/
def indexStyleCombine : IndexStyleV → IndexStyleV → IndexStyleV
  | .linear, .linear => .linear
  | _, _ => .cartesian

/-- `IndexStyle(A, B...)`, `base/indices.jl:101-102`:
`IndexStyle(A, B) = IndexStyle(IndexStyle(A), IndexStyle(B))` and
`IndexStyle(A, B...) = IndexStyle(IndexStyle(A), IndexStyle(B...))`. -/
def indexStyleN : ArrTy → List ArrTy → IndexStyleV
  | a, [] => indexStyle1 a
  | a, b :: rest => indexStyleCombine (indexStyle1 a) (indexStyleN b rest)

/-- `IndexStyle(::Type{Union{}}, slurp...)`, `base/indices.jl:96`. -/
def indexStyleBottomSlurp : Jl IndexStyleV := .error (.methodError "IndexStyle")

/-- The `IndexStyle` docstring, `base/indices.jl:66-93`: the default is
`IndexCartesian()`, `Array`s and ranges are `IndexLinear`, an array has the style of
its type, and several arrays share `IndexLinear` exactly when every one of them is
`IndexLinear` (otherwise the common style is `IndexCartesian`). -/
def IndexStyleSpec : Prop :=
  indexStyle1 .plain = .cartesian ∧ indexStyle1 .array = .linear ∧ indexStyle1 .range = .linear ∧
  indexStyle1 .linearIndices = .linear ∧ indexStyle1 .bottom = .linear ∧
  (∀ s, indexStyle1 (.custom s) = s) ∧
  (∀ a rest, indexStyleN a rest = if (a :: rest).all (fun b => indexStyle1 b == .linear)
    then .linear else .cartesian) ∧
  (∃ f, indexStyleBottomSlurp = .error (.methodError f))

end JuliaLean.ReduceCov
