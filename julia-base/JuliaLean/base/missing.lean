import JuliaLean.Core

/-!
# Model of `base/missing.jl`

Typed models of the methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
`MissingValue` represents the Julia singleton `missing`; `Option α` represents a value in
`Union{Missing, α}`. Methods are generic in their non-missing values. Operations from other Base
files are typed parameters, while methods defined in this file call their own model definitions.
-/

namespace JuliaLean.base.missing

open JuliaLean

inductive MissingValue where
  | missing
  deriving Repr, DecidableEq

inductive JuliaValue where
  | missing
  | value {α : Type} (value : α)


abbrev MayMissing (α : Type) := Option α

structure MissingException (Message : Type) where
  msg : Message

structure TypeRef (α : Type) where
  token : Unit := ()

inductive JuliaType (α : Type) where
  | any
  | bottom
  | missing
  | named (value : α)
  | union (members : List (Option α))
  deriving Repr

inductive PrintArgument (Message : Type) where
  | text (value : String)
  | message (value : Message)
  | character (value : Char)

/--
Julia source: base/missing.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, x::Missing) = print(io, "missing")
```
-/
def showMissing {IO : Type} (print : IO → String → IO) (io : IO) (_x : MissingValue) : IO :=
  print io "missing"

/--
Julia source: base/missing.jl:18-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::MissingException) =
    print(io, "MissingException: ", ex.msg)
```
-/
def showMissingException {IO Message : Type}
    (print : IO → String → Message → IO) (io : IO) (ex : MissingException Message) : IO :=
  print io "MissingException: " ex.msg

/--
Julia source: base/missing.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nonmissingtype(@nospecialize(T::Type)) = typesplit(T, Missing)
```
-/
def nonmissingtype {α : Type} (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (T : JuliaType α) : JuliaType α :=
  typesplit T .missing

/--
Julia source: base/missing.jl:41-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nonmissingtype_checked(T::Type)
    R = nonmissingtype(T)
    R >: T && error("could not compute non-missing type")
    R <: Union{} && error("cannot convert a value to missing for assignment")
    return R
end
```
-/
def nonmissingtypeChecked {α ε : Type}
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool)
    (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α)) (T : JuliaType α) : Except ε (JuliaType α) := do
  let R := nonmissingtype typesplit T
  if isSupertype R T then
    error "could not compute non-missing type"
  else if isBottom R then
    error "cannot convert a value to missing for assignment"
  else
    pure R

/--
Julia source: base/missing.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(T::Type{Missing}, S::Type) = Union{S, Missing}
```
-/
def promoteRuleMissing {α : Type} (unionMissing : JuliaType α → JuliaType α)
    (_T : TypeRef MissingValue) (S : JuliaType α) : JuliaType α :=
  unionMissing S

/--
Julia source: base/missing.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(T::Type{Union{Nothing, Missing}}, S::Type) = Union{S, Nothing, Missing}
```
-/
def promoteRuleNothingMissing {α : Type}
    (unionNothingMissing : JuliaType α → JuliaType α) (_T : TypeRef Unit)
    (S : JuliaType α) : JuliaType α :=
  unionNothingMissing S

/--
Julia source: base/missing.jl:50-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_rule(T::Type{>:Union{Nothing, Missing}}, S::Type)
    R = nonnothingtype(T)
    R >: T && return Any
    T = R
    R = nonmissingtype(T)
    R >: T && return Any
    T = R
    R = promote_type(T, S)
    return Union{R, Nothing, Missing}
end
```
-/
def promoteRuleSuperNothingMissing {α : Type}
    (nonnothing : JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (promoteType : JuliaType α → JuliaType α → JuliaType α)
    (unionNothingMissing : JuliaType α → JuliaType α)
    (anyType : JuliaType α) (T S : JuliaType α) : JuliaType α := Id.run do
  let Rn := nonnothing T
  if isSupertype Rn T then
    return anyType
  let T := Rn
  let R := nonmissingtype typesplit T
  if isSupertype R T then
    return anyType
  let T := R
  let R := promoteType T S
  return unionNothingMissing R

/--
Julia source: base/missing.jl:60-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_rule(T::Type{>:Missing}, S::Type)
    R = nonmissingtype(T)
    R >: T && return Any
    T = R
    R = promote_type(T, S)
    return Union{R, Missing}
end
```
-/
def promoteRuleSuperMissing {α : Type}
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool)
    (promoteType : JuliaType α → JuliaType α → JuliaType α)
    (unionMissing : JuliaType α → JuliaType α)
    (anyType : JuliaType α) (T S : JuliaType α) : JuliaType α := Id.run do
  let R := nonmissingtype typesplit T
  if isSupertype R T then
    return anyType
  let T := R
  let R := promoteType T S
  return unionMissing R

/--
Julia source: base/missing.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T) where {T>:Missing} = x
```
-/
def convertSameMissingType {α : Type} (x : α) : α := x

/--
Julia source: base/missing.jl:69-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T) where {T>:Union{Missing, Nothing}} = x
```
-/
def convertSameNothingMissingType {α : Type} (x : α) : α := x

/--
Julia source: base/missing.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x) where {T>:Missing} = convert(nonmissingtype_checked(T), x)
```
-/
def convertIntoMissingType {α β γ ε : Type}
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool)
    (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (convert : JuliaType α → β → Except ε γ) (T : JuliaType α) (x : β) : Except ε γ := do
  let R ← nonmissingtypeChecked typesplit isSupertype isBottom error T
  convert R x


/--
Julia source: base/missing.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x) where {T>:Union{Missing, Nothing}} = convert(nonmissingtype_checked(nonnothingtype_checked(T)), x)
```
-/
def convertIntoNothingMissingType {α β γ ε : Type}
    (nonnothingChecked : JuliaType α → Except ε (JuliaType α))
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool)
    (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (convert : JuliaType α → β → Except ε γ) (T : JuliaType α) (x : β) : Except ε γ := do
  let R ← nonnothingChecked T
  let S ← nonmissingtypeChecked typesplit isSupertype isBottom error R
  convert S x

/--
Julia source: base/missing.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(::Missing, ::Missing) = missing
```
-/
def equalMissingMissing : Option Bool := none

/--
Julia source: base/missing.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(::Missing, ::Any) = missing
```
-/
def equalMissingAny {α : Type} (_x : α) : Option Bool := none

/--
Julia source: base/missing.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(::Any, ::Missing) = missing
```
-/
def equalAnyMissing {α : Type} (_x : α) : Option Bool := none

/--
Julia source: base/missing.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(::Missing, ::WeakRef) = missing
```
-/
def equalMissingWeakRef {WeakRef : Type} (_x : WeakRef) : Option Bool := none

/--
Julia source: base/missing.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(::WeakRef, ::Missing) = missing
```
-/
def equalWeakRefMissing {WeakRef : Type} (_x : WeakRef) : Option Bool := none

/--
Julia source: base/missing.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(::Missing, ::Missing) = true
```
-/
def isequalMissingMissing : Bool := true

/--
Julia source: base/missing.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(::Missing, ::Any) = false
```
-/
def isequalMissingAny {α : Type} (_x : α) : Bool := false

/--
Julia source: base/missing.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(::Any, ::Missing) = false
```
-/
def isequalAnyMissing {α : Type} (_x : α) : Bool := false

/--
Julia source: base/missing.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(::Missing, ::Missing) = missing
```
-/
def lessMissingMissing : Option Bool := none

/--
Julia source: base/missing.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(::Missing, ::Any) = missing
```
-/
def lessMissingAny {α : Type} (_x : α) : Option Bool := none

/--
Julia source: base/missing.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(::Any, ::Missing) = missing
```
-/
def lessAnyMissing {α : Type} (_x : α) : Option Bool := none

/--
Julia source: base/missing.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(::Missing, ::Missing) = false
```
-/
def islessMissingMissing : Bool := false

/--
Julia source: base/missing.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(::Missing, ::Any) = false
```
-/
def islessMissingAny {α : Type} (_x : α) : Bool := false

/--
Julia source: base/missing.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(::Any, ::Missing) = true
```
-/
def islessAnyMissing {α : Type} (_x : α) : Bool := true

/--
Julia source: base/missing.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispositive(::Missing) = missing
```
-/
def ispositiveMissing : Option Bool := none

/--
Julia source: base/missing.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnegative(::Missing) = missing
```
-/
def isnegativeMissing : Option Bool := none

/--
Julia source: base/missing.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isapprox(::Missing, ::Missing; kwargs...) = missing
```
-/
def isapproxMissingMissing {K : Type} (_kwargs : List K) : Option Bool := none

/--
Julia source: base/missing.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isapprox(::Missing, ::Any; kwargs...) = missing
```
-/
def isapproxMissingAny {α K : Type} (_x : α) (_kwargs : List K) : Option Bool := none

/--
Julia source: base/missing.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isapprox(::Any, ::Missing; kwargs...) = missing
```
-/
def isapproxAnyMissing {α K : Type} (_x : α) (_kwargs : List K) : Option Bool := none

/--
Julia source: base/missing.jl:96-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:(!), :(~), :(+), :(-), :(*), :(&), :(|), :(xor),
          :(zero), :(one), :(oneunit),
          :(isfinite), :(isinf), :(isodd),
          :(isinteger), :(isreal), :(isnan),
          :(iszero), :(transpose), :(adjoint), :(float), :(complex), :(conj),
          :(abs), :(abs2), :(iseven), :(ispow2),
          :(real), :(imag), :(sign), :(inv))
    @eval ($f)(::Missing) = missing
end
```
-/
def generatedUnaryMissing {α : Type} (_x : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval ($f)(::Type{Any}) = throw(MethodError($f, (Any,)))  # To prevent StackOverflowError
```
-/
inductive UnaryTypeFunction where
  | zero
  | one
  | oneunit
  deriving Repr, DecidableEq

def UnaryTypeFunction.juliaName : UnaryTypeFunction → String
  | .zero => "zero"
  | .one => "one"
  | .oneunit => "oneunit"

def unaryTypeAnyError {α : Type} (f : UnaryTypeFunction) : Except JlError α :=
  .error (.methodError f.juliaName)

/--
Julia source: base/missing.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval ($f)(::Type{Missing}) = missing
```
-/
def unaryTypeMissing {α : Type} (_f : UnaryTypeFunction) (_T : TypeRef MissingValue) : Option α := none

/--
Julia source: base/missing.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval ($f)(::Type{T}) where {T>:Missing} = $f(nonmissingtype_checked(T))
```
-/
def unaryTypeWithMissing {α β ε : Type} (f : UnaryTypeFunction)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool)
    (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (apply : UnaryTypeFunction → JuliaType α → Except ε β)
    (T : JuliaType α) : Except ε β := do
  let R ← nonmissingtypeChecked typesplit isSupertype isBottom error T
  apply f R

/--
Julia source: base/missing.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval ($f)(::Type{Any}) = throw(MethodError($f, (Any,)))  # To prevent StackOverflowError
```
-/
inductive FloatTypeFunction where
  | float
  | real
  | complex
  deriving Repr, DecidableEq

def FloatTypeFunction.juliaName : FloatTypeFunction → String
  | .float => "float"
  | .real => "real"
  | .complex => "complex"

def floatTypeAnyError {α : Type} (f : FloatTypeFunction) : Except JlError α :=
  .error (.methodError f.juliaName)

/--
Julia source: base/missing.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval ($f)(::Type{T}) where {T>:Missing} = Union{$f(nonmissingtype(T)), Missing}
```
-/
def floatTypeWithMissing {α : Type} (unionMissing : JuliaType α → JuliaType α)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (apply : FloatTypeFunction → JuliaType α → JuliaType α)
    (f : FloatTypeFunction) (T : JuliaType α) : JuliaType α :=
  unionMissing (apply f (nonmissingtype typesplit T))

/--
Julia source: base/missing.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($f)(::Missing, ::Missing) = missing
```
-/
def generatedBinaryMissingBoth {α : Type} (_x _y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($f)(::Missing, ::Number)  = missing
```
-/
def generatedBinaryMissingNumber {α β : Type} (_x : MissingValue) (_y : β) : Option α := none

/--
Julia source: base/missing.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($f)(::Number,  ::Missing) = missing
```
-/
def generatedBinaryNumberMissing {α β : Type} (_x : β) (_y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(::Missing, ::Missing, r::RoundingMode) = missing
```
-/
def divMissingMissing {α Mode : Type} (_x _y : MissingValue) (_r : Mode) : Option α := none

/--
Julia source: base/missing.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(::Missing, ::Number, r::RoundingMode) = missing
```
-/
def divMissingNumber {α β Mode : Type} (_x : MissingValue) (_y : β) (_r : Mode) : Option α := none

/--
Julia source: base/missing.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(::Number, ::Missing, r::RoundingMode) = missing
```
-/
def divNumberMissing {α β Mode : Type} (_x : β) (_y : MissingValue) (_r : Mode) : Option α := none

/--
Julia source: base/missing.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Missing, ::Missing) = $result
```
-/
def minmaxBinaryBothMissing {α : Type} (_x _y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Missing, ::Missing) = $result
```
-/
def minmaxPairBothMissing {α β : Type} (_x _y : MissingValue) :
    Option α × Option β :=
  (none, none)


/--
Julia source: base/missing.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Missing, ::Any)     = $result
```
-/
def minmaxBinaryMissingAny {α β : Type} (_x : MissingValue) (_y : β) : Option α := none

/--
Julia source: base/missing.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Missing, ::Any)     = $result
```
-/
def minmaxPairMissingAny {α β γ : Type} (_x : MissingValue) (_y : γ) :
    Option α × Option β :=
  (none, none)


/--
Julia source: base/missing.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Any,     ::Missing) = $result
```
-/
def minmaxBinaryAnyMissing {α β : Type} (_x : β) (_y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Any,     ::Missing) = $result
```
-/
def minmaxPairAnyMissing {α β γ : Type} (_x : γ) (_y : MissingValue) :
    Option α × Option β :=
  (none, none)


/--
Julia source: base/missing.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Missing) = $result
```
-/
def minmaxUnaryMissing {α : Type} (_x : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(::Missing) = $result
```
-/
def minmaxPairUnaryMissing {α β : Type} (_x : MissingValue) :
    Option α × Option β :=
  (none, none)


/--
Julia source: base/missing.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clamp(::Missing, lo, hi) = missing
```
-/
def clampMissing {α β γ : Type} (_x : MissingValue) (_lo : β) (_hi : γ) : Option α := none

/--
Julia source: base/missing.jl:139-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
missing_conversion_msg(@nospecialize T) =
    LazyString("cannot convert a missing value to type ", T, ": use Union{", T, ", Missing} instead")
```
-/
def missingConversionMessage {α Message : Type}
    (lazyString : List (Sum String α) → Message) (T : α) : Message :=
  lazyString [.inl "cannot convert a missing value to type ", .inr T,
    .inl ": use Union{", .inr T, .inl ", Missing} instead"]

/--
Julia source: base/missing.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Missing, ::RoundingMode=RoundNearest; sigdigits::Integer=0, digits::Integer=0, base::Integer=0) = missing
```
-/
def roundMissing {α Mode Integer : Type} (_x : MissingValue) (_r : Mode)
    (_sigdigits _digits _base : Integer) : Option α := none

/--
Julia source: base/missing.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{>:Missing}, ::Missing, ::RoundingMode=RoundNearest) = missing
```
-/
def roundMissingToSupertype {α Mode : Type} (_T : JuliaType α) (_x : MissingValue)
    (_r : Mode) : Option α := none

/--
Julia source: base/missing.jl:145-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, ::Missing, ::RoundingMode=RoundNearest) where {T} =
    throw(MissingException(missing_conversion_msg(T)))
```
-/
def roundMissingToType {α Message Mode : Type} (missingException : Message → MissingException Message)
    (lazyString : List (Sum String α) → Message) (T : α) (_x : MissingValue)
    (_r : Mode) : Except (MissingException Message) α :=
  .error (missingException (missingConversionMessage lazyString T))

/--
Julia source: base/missing.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, x::Any, r::RoundingMode=RoundNearest) where {T>:Missing} = round(nonmissingtype_checked(T), x, r)
```
-/
def roundToMissingSupertype {α β ε Mode γ : Type} (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool) (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (round : JuliaType α → β → Mode → Except ε γ) (T : JuliaType α) (x : β) (r : Mode) : Except ε γ := do
  let R ← nonmissingtypeChecked typesplit isSupertype isBottom error T
  round R x r

/--
Julia source: base/missing.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, x::Real, r::RoundingMode=RoundNearest) where {T>:Missing} = round(nonmissingtype_checked(T), x, r)
```
-/
def roundRealToMissingSupertype {α Real ε Mode γ : Type} (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool) (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (round : JuliaType α → Real → Mode → Except ε γ) (T : JuliaType α) (x : Real) (r : Mode) : Except ε γ := do
  let R ← nonmissingtypeChecked typesplit isSupertype isBottom error T
  round R x r

/--
Julia source: base/missing.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, x::Rational{Tr}, r::RoundingMode=RoundNearest) where {T>:Missing,Tr} = round(nonmissingtype_checked(T), x, r)
```
-/
def roundRationalToMissingSupertype {α ε Mode γ : Type}
    {Rational : Type → Type} {Tr : Type}
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool) (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (round : JuliaType α → Rational Tr → Mode → Except ε γ) (T : JuliaType α)
    (_x : Rational Tr) (r : Mode) : Except ε γ := do
  let R ← nonmissingtypeChecked typesplit isSupertype isBottom error T
  round R _x r

/--
Julia source: base/missing.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, x::Rational{Bool}, r::RoundingMode=RoundNearest) where {T>:Missing} = round(nonmissingtype_checked(T), x, r)
```
-/
def roundBoolRationalToMissingSupertype {α ε Mode γ : Type}
    {Rational : Type → Type}
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (isSupertype : JuliaType α → JuliaType α → Bool) (isBottom : JuliaType α → Bool)
    (error : String → Except ε (JuliaType α))
    (round : JuliaType α → Rational Bool → Mode → Except ε γ) (T : JuliaType α)
    (_x : Rational Bool) (r : Mode) : Except ε γ := do
  let R ← nonmissingtypeChecked typesplit isSupertype isBottom error T
  round R _x r

/--
Julia source: base/missing.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(^)(::Missing, ::Integer) = missing
```
-/
def powerMissingInteger {α Integer : Type} (_x : MissingValue) (_y : Integer) : Option α := none

/--
Julia source: base/missing.jl:157-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(::Missing, ::Missing) = missing
```
-/
def andMissingMissing : Option Bool := none

/--
Julia source: base/missing.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(a::Missing, b::Bool) = ifelse(b, missing, false)
```
-/
def andMissingBool (ifelse : Bool → Option Bool → Option Bool → Option Bool)
    (_a : MissingValue) (b : Bool) : Option Bool :=
  ifelse b none (some false)

/--
Julia source: base/missing.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(b::Bool, a::Missing) = ifelse(b, missing, false)
```
-/
def andBoolMissing (ifelse : Bool → Option Bool → Option Bool → Option Bool)
    (b : Bool) (_a : MissingValue) : Option Bool :=
  ifelse b none (some false)

/--
Julia source: base/missing.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(::Missing, ::Integer) = missing
```
-/
def andMissingInteger {α Integer : Type} (_x : MissingValue) (_y : Integer) : Option α := none

/--
Julia source: base/missing.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(::Integer, ::Missing) = missing
```
-/
def andIntegerMissing {α Integer : Type} (_x : Integer) (_y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(::Missing, ::Missing) = missing
```
-/
def orMissingMissing : Option Bool := none

/--
Julia source: base/missing.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(a::Missing, b::Bool) = ifelse(b, true, missing)
```
-/
def orMissingBool (ifelse : Bool → Option Bool → Option Bool → Option Bool)
    (_a : MissingValue) (b : Bool) : Option Bool :=
  ifelse b (some true) none

/--
Julia source: base/missing.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(b::Bool, a::Missing) = ifelse(b, true, missing)
```
-/
def orBoolMissing (ifelse : Bool → Option Bool → Option Bool → Option Bool)
    (b : Bool) (_a : MissingValue) : Option Bool :=
  ifelse b (some true) none

/--
Julia source: base/missing.jl:165-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(::Missing, ::Integer) = missing
```
-/
def orMissingInteger {α Integer : Type} (_x : MissingValue) (_y : Integer) : Option α := none

/--
Julia source: base/missing.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(::Integer, ::Missing) = missing
```
-/
def orIntegerMissing {α Integer : Type} (_x : Integer) (_y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(::Missing, ::Missing) = missing
```
-/
def xorMissingMissing : Option Bool := none

/--
Julia source: base/missing.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(a::Missing, b::Bool) = missing
```
-/
def xorMissingBool (_a : MissingValue) (_b : Bool) : Option Bool := none

/--
Julia source: base/missing.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(b::Bool, a::Missing) = missing
```
-/
def xorBoolMissing (_a : Bool) (_b : MissingValue) : Option Bool := none

/--
Julia source: base/missing.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(::Missing, ::Integer) = missing
```
-/
def xorMissingInteger {α Integer : Type} (_x : MissingValue) (_y : Integer) : Option α := none

/--
Julia source: base/missing.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(::Integer, ::Missing) = missing
```
-/
def xorIntegerMissing {α Integer : Type} (_x : Integer) (_y : MissingValue) : Option α := none

/--
Julia source: base/missing.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(d::Missing, x::Union{AbstractString,AbstractChar}) = missing
```
-/
def multiplyMissingText {α AbstractString AbstractChar : Type} (_d : MissingValue)
    (_x : Sum AbstractString AbstractChar) : Option α := none

/--
Julia source: base/missing.jl:174-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(d::Union{AbstractString,AbstractChar}, x::Missing) = missing
```
-/
def multiplyTextMissing {α AbstractString AbstractChar : Type}
    (_x : Sum AbstractString AbstractChar) (_d : MissingValue) : Option α := none

/-! ## Arrays and `SkipMissing` -/

/--
Julia source: base/missing.jl:176-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function float(A::AbstractArray{Union{T, Missing}}) where {T}
    U = typeof(float(zero(T)))
    convert(AbstractArray{Union{U, Missing}}, A)
end
```
-/
def floatArrayMissing {ArrayLike : Type → Type} {T U : Type} (zero : TypeRef T → T) (float : T → U)
    (typeof : U → TypeRef U)
    (convert : ArrayLike (Option T) → ArrayLike (Option U))
    (A : ArrayLike (Option T)) : ArrayLike (Option U) := Id.run do
  let _U := typeof (float (zero ⟨()⟩))
  convert A

/--
Julia source: base/missing.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(A::AbstractArray{Missing}) = A
```
-/
def floatArrayOnlyMissing {ArrayLike : Type → Type} (A : ArrayLike MissingValue) :
    ArrayLike MissingValue :=
  A

/-- The wrapper stored by Julia's `SkipMissing{T}`. -/
structure SkipMissing (Itr : Type) where
  x : Itr

/--
Julia source: base/missing.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
skipmissing(itr) = SkipMissing(itr)
```
-/
def skipmissing {Itr : Type} (itr : Itr) : SkipMissing Itr :=
  ⟨itr⟩

inductive IteratorSizeModel where
  | sizeUnknown
  deriving Repr, DecidableEq

/--
Julia source: base/missing.jl:236-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:SkipMissing}) = SizeUnknown()
```
-/
def iteratorSizeSkipMissing {Itr : Type} (_T : TypeRef (SkipMissing Itr)) :
    IteratorSizeModel :=
  .sizeUnknown

/--
Julia source: base/missing.jl:237-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{SkipMissing{T}}) where {T} = IteratorEltype(T)
```
-/
def iteratorEltypeSkipMissing {Itr R : Type}
    (iteratorEltype : TypeRef Itr → R) (T : TypeRef (SkipMissing Itr)) : R :=
  iteratorEltype ⟨T.token⟩

/--
Julia source: base/missing.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{SkipMissing{T}}) where {T} = nonmissingtype(eltype(T))
```
-/
def eltypeSkipMissing {Itr α : Type}
    (eltype : TypeRef Itr → JuliaType α)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (T : TypeRef (SkipMissing Itr)) : JuliaType α :=
  nonmissingtype typesplit (eltype ⟨T.token⟩)

/--
Julia source: base/missing.jl:240-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::SkipMissing, state...)
    y = iterate(itr.x, state...)
    y === nothing && return nothing
    item, state = y
    while ismissing(item)
        y = iterate(itr.x, state)
        y === nothing && return nothing
        item, state = y
    end
    item, state
end
```
-/
partial def iterateSkipMissingLoop {Itr α State : Type}
    (iterate : Itr → State → Option (Option α × State))
    (ismissing : Option α → Bool) (itr : Itr) (item : Option α) (state : State) :
    Option (Option α × State) :=
  if ismissing item then
    match iterate itr state with
    | none => none
    | some (item, state) => iterateSkipMissingLoop iterate ismissing itr item state
  else
    some (item, state)

def iterateSkipMissing {Itr α State : Type}
    (iterate : Itr → List State → Option (Option α × State))
    (iterateNext : Itr → State → Option (Option α × State))
    (ismissing : Option α → Bool) (itr : SkipMissing Itr) (state : List State) :
    Option (Option α × State) :=
  match iterate itr.x state with
  | none => none
  | some (item, state) => iterateSkipMissingLoop iterateNext ismissing itr.x item state

inductive IndexStyleModel where
  | linear
  | cartesian
  deriving Repr, DecidableEq

/--
Julia source: base/missing.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:SkipMissing{T}}) where {T} = IndexStyle(T)
```
-/
def indexStyleSkipMissing {Itr : Type}
    (indexStyle : TypeRef Itr → IndexStyleModel)
    (T : TypeRef (SkipMissing Itr)) : IndexStyleModel :=
  indexStyle ⟨T.token⟩

/--
Julia source: base/missing.jl:253-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(itr::SkipMissing) =
    Iterators.filter(i -> !ismissing(@inbounds(itr.x[i])), eachindex(itr.x))
```
-/
def eachindexSkipMissing {Itr Ix IndexIterator α : Type}
    (filter : (Ix → Bool) → IndexIterator → IndexIterator)
    (eachindex : Itr → IndexIterator)
    (getindex : Itr → Ix → Option α) (ismissing : Option α → Bool)
    (itr : SkipMissing Itr) : IndexIterator :=
  filter (fun i => !ismissing (getindex itr.x i)) (eachindex itr.x)

/--
Julia source: base/missing.jl:255-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(itr::SkipMissing) =
    Iterators.filter(i -> !ismissing(@inbounds(itr.x[i])), keys(itr.x))
```
-/
def keysSkipMissing {Itr K IndexIterator α : Type}
    (filter : (K → Bool) → IndexIterator → IndexIterator)
    (keys : Itr → IndexIterator)
    (getindex : Itr → K → Option α) (ismissing : Option α → Bool)
    (itr : SkipMissing Itr) : IndexIterator :=
  filter (fun i => !ismissing (getindex itr.x i)) (keys itr.x)

inductive MissingIndexError (ParentError Message : Type) where
  | parent (error : ParentError)
  | missing (exception : MissingException Message)

/--
Julia source: base/missing.jl:257-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(itr::SkipMissing, I...)
    v = itr.x[I...]
    ismissing(v) && throw(MissingException(LazyString("the value at index ", I, " is missing")))
    v
end
```
-/
def getindexSkipMissing {Itr Ix α ParentError Message : Type}
    (getindex : Itr → List Ix → Except ParentError (Option α))
    (ismissing : Option α → Bool) (missingMessage : List Ix → Message)
    (itr : SkipMissing Itr) (I : List Ix) :
    Except (MissingIndexError ParentError Message) (Option α) :=
  match getindex itr.x I with
  | .error e => .error (.parent e)
  | .ok v =>
    if ismissing v then
      .error (.missing ⟨missingMessage I⟩)
    else
      .ok v

/--
Julia source: base/missing.jl:263-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, s::SkipMissing)
    print(io, "skipmissing(")
    show(io, s.x)
    print(io, ')')
end
```
-/
def showSkipMissing {IO Itr Message : Type} (print : IO → PrintArgument Message → IO)
    (showValue : IO → Itr → IO) (initialIO : IO) (s : SkipMissing Itr) : IO := Id.run do
  let io := print initialIO (.text "skipmissing(")
  let io := showValue io s.x
  print io (.character ')')

/--
Julia source: base/missing.jl:385-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, itr::SkipMissing{<:AbstractArray})
    y = similar(itr.x, eltype(itr), 0)
    for xi in itr.x
        if !ismissing(xi) && f(xi)
            push!(y, xi)
        end
    end
    y
end
```
-/
def filterSkipMissing {Itr α Y : Type}
    (elements : Itr → List (Option α))
    (similar : Itr → JuliaType α → Nat → Y)
    (push : Y → α → Y)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (eltype : TypeRef Itr → JuliaType α)
    (ismissing : Option α → Bool) (f : α → Bool)
    (itr : SkipMissing Itr) : Y :=
  (elements itr.x).foldl (fun y xi =>
    if !ismissing xi then
      match xi with
      | none => y
      | some x => if f x then push y x else y
    else y) (similar itr.x (eltypeSkipMissing eltype typesplit ⟨()⟩) 0)

/-- Typed expression nodes built by `@coalesce`; `choose` evaluates its argument once. -/
inductive CoalesceExpr (Arg : Type) where
  | missing
  | choose (arg : Arg) (rest : CoalesceExpr Arg)
  | letValue (body : CoalesceExpr Arg)
  deriving Repr

def evalCoalesceExpr {Arg : Type} (evaluate : Arg → JuliaValue) :
    CoalesceExpr Arg → JuliaValue
  | .missing => .missing
  | .choose arg rest =>
    match evaluate arg with
    | .missing => evalCoalesceExpr evaluate rest
    | value => value
  | .letValue body => evalCoalesceExpr evaluate body

/-- The variable-argument dispatcher represented by the three `coalesce` methods. -/
def coalesce : List JuliaValue → JuliaValue
  | [] => .missing
  | .missing :: ys => coalesce ys
  | value :: _ => value

/--
Julia source: base/missing.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
coalesce() = missing
```
-/
def coalesceEmpty : JuliaValue := .missing

/--
Julia source: base/missing.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
coalesce(x::Missing, y...) = coalesce(y...)
```
-/
def coalesceMissingHead (_x : MissingValue) (ys : List JuliaValue) : JuliaValue :=
  coalesce ys

/--
Julia source: base/missing.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
coalesce(x::Any, y...) = x
```
-/
def coalesceAnyHead (x : JuliaValue) (_ys : List JuliaValue) : JuliaValue :=
  x


/--
Julia source: base/missing.jl:451-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro coalesce(args...)
    expr = :(missing)
    for arg in reverse(args)
        expr = :(!ismissing((val = $(esc(arg));)) ? val : $expr)
    end
    return :(let val; $expr; end)
end
```
-/
def coalesceMacro {Arg : Type} (args : List Arg) : CoalesceExpr Arg :=
  let expr := args.reverse.foldl (fun expr arg => .choose arg expr) .missing
  .letValue expr
/-- Index operations supplied by the generic `Integer` interface of an array's linear indices. -/
structure IntegerIndexOps (Index : Type) where
  greater : Index → Index → Bool
  equal : Index → Index → Bool
  successor : Index → Index
  maximum : Index
  spanLessThan : Index → Index → JInt64 → Bool
  midpoint : Index → Index → Index
  range : Index → Index → List Index

/-- Linear access to an `AbstractArray`; `Index` stays generic over Julia `Integer`. -/
structure AbstractArrayModel (Index α : Type) where
  firstIndex : Index
  lastIndex : Index
  get : Index → Option α

inductive SkipReduceInput (Array : Type) where
  | filtered (itr : SkipMissing Array)
  | raw (array : Array)





/--
Julia source: base/missing.jl:306-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _mapreduce_impl_skipmissing(f, op, itr::SkipMissing{<:AbstractArray},
                                               ifirst::Integer, ilast::Integer, blksize::Int)
    A = itr.x
    if ifirst > ilast
        return nothing
    elseif ifirst == ilast
        @inbounds a1 = A[ifirst]
        if ismissing(a1)
            return nothing
        else
            return Some(mapreduce_first(f, op, a1))
        end
    elseif ilast - ifirst < blksize
        # sequential portion
        ai = missing
        i = ifirst
        for outer i in i:ilast
            @inbounds ai = A[i]
            !ismissing(ai) && break
        end
        ismissing(ai) && return nothing
        a1 = ai::eltype(itr)
        i == typemax(typeof(i)) && return Some(mapreduce_first(f, op, a1))
        i += 1
        ai = missing
        for outer i in i:ilast
            @inbounds ai = A[i]
            !ismissing(ai) && break
        end
        ismissing(ai) && return Some(mapreduce_first(f, op, a1))
        a2 = ai::eltype(itr)
        i == typemax(typeof(i)) && return Some(op(f(a1), f(a2)))
        i += 1
        v = op(f(a1), f(a2))
        @simd for i = i:ilast
            @inbounds ai = A[i]
            if !ismissing(ai)
                v = op(v, f(ai))
            end
        end
        return Some(v)
    else
        # pairwise portion
        imid = ifirst + (ilast - ifirst) >> 1
        v1 = _mapreduce_impl_skipmissing(f, op, itr, ifirst, imid, blksize)
        v2 = _mapreduce_impl_skipmissing(f, op, itr, imid+1, ilast, blksize)
        if v1 === nothing && v2 === nothing
            return nothing
        elseif v1 === nothing
            return v2
        elseif v2 === nothing
            return v1
        else
            return Some(op(something(v1), something(v2)))
        end
    end
end
```
-/
partial def mapreduceImplSkipMissingKernel {Index α β : Type}
    (indexOps : IntegerIndexOps Index) (ismissing : Option α → Bool)
    (assertNonmissing : Option α → α)
    (mapreduceFirst : (α → β) → (β → β → β) → α → β)
    (something : Option β → β)
    (f : α → β) (op : β → β → β)
    (itr : SkipMissing (AbstractArrayModel Index α)) (ifirst ilast : Index)
    (blksize : JInt64) : Option β := Id.run do
  let A := itr.x
  if indexOps.greater ifirst ilast then
    return none
  else if indexOps.equal ifirst ilast then
    let a1 := A.get ifirst
    if ismissing a1 then
      return none
    else
      return some (mapreduceFirst f op (assertNonmissing a1))
  else if indexOps.spanLessThan ifirst ilast blksize then
    let mut ai : Option α := none
    let mut i := ifirst
    for j in indexOps.range i ilast do
      i := j
      ai := A.get i
      if !ismissing ai then
        break
    if ismissing ai then
      return none
    let a1 := assertNonmissing ai
    if indexOps.equal i indexOps.maximum then
      return some (mapreduceFirst f op a1)
    i := indexOps.successor i
    ai := none
    for j in indexOps.range i ilast do
      i := j
      ai := A.get i
      if !ismissing ai then
        break
    if ismissing ai then
      return some (mapreduceFirst f op a1)
    let a2 := assertNonmissing ai
    if indexOps.equal i indexOps.maximum then
      return some (op (f a1) (f a2))
    i := indexOps.successor i
    let mut v := op (f a1) (f a2)
    for j in indexOps.range i ilast do
      ai := A.get j
      if !ismissing ai then
        v := op v (f (assertNonmissing ai))
    return some v
  else
    let imid := indexOps.midpoint ifirst ilast
    let v1 := mapreduceImplSkipMissingKernel indexOps ismissing assertNonmissing mapreduceFirst something
      f op itr ifirst imid blksize
    let v2 := mapreduceImplSkipMissingKernel indexOps ismissing assertNonmissing mapreduceFirst something
      f op itr (indexOps.successor imid) ilast blksize
    match v1, v2 with
    | none, none => return none
    | none, some value => return some value
    | some value, none => return some value
    | some left, some right =>
      return some (op (something (some left)) (something (some right)))
/--
Julia source: base/missing.jl:303-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce_impl_skipmissing(f, op, A::SkipMissing, ifirst::Integer, ilast::Integer) =
    _mapreduce_impl_skipmissing(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
```
-/
def mapreduceImplSkipMissing {Index α β : Type}
    (indexOps : IntegerIndexOps Index) (ismissing : Option α → Bool)
    (assertNonmissing : Option α → α)
    (mapreduceFirst : (α → β) → (β → β → β) → α → β)
    (something : Option β → β)
    (pairwiseBlocksize : (α → β) → (β → β → β) → JInt64)
    (f : α → β) (op : β → β → β)
    (itr : SkipMissing (AbstractArrayModel Index α)) (ifirst ilast : Index) : Option β :=
  mapreduceImplSkipMissingKernel indexOps ismissing assertNonmissing mapreduceFirst something
    f op itr ifirst ilast (pairwiseBlocksize f op)
/--
Julia source: base/missing.jl:275-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mapreduce(f, op, ::IndexLinear, itr::SkipMissing{<:AbstractArray})
    A = itr.x
    ai = missing
    inds = LinearIndices(A)
    i = first(inds)
    ilast = last(inds)
    for outer i in i:ilast
        @inbounds ai = A[i]
        !ismissing(ai) && break
    end
    ismissing(ai) && return mapreduce_empty(f, op, eltype(itr))
    a1::eltype(itr) = ai
    i == typemax(typeof(i)) && return mapreduce_first(f, op, a1)
    i += 1
    ai = missing
    for outer i in i:ilast
        @inbounds ai = A[i]
        !ismissing(ai) && break
    end
    ismissing(ai) && return mapreduce_first(f, op, a1)
    # We know A contains at least two non-missing entries: the result cannot be nothing
    something(_mapreduce_impl_skipmissing(f, op, itr, first(inds), last(inds)))
end
```
-/
def mapreduceIndexLinear {Index α β : Type}
    (indexOps : IntegerIndexOps Index)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (eltype : TypeRef (AbstractArrayModel Index α) → JuliaType α)
    (ismissing : Option α → Bool) (assertNonmissing : Option α → α)
    (mapreduceEmpty : (α → β) → (β → β → β) → JuliaType α → β)
    (mapreduceFirst : (α → β) → (β → β → β) → α → β)
    (pairwiseBlocksize : (α → β) → (β → β → β) → JInt64)
    (something : Option β → β) (f : α → β) (op : β → β → β)
    (itr : SkipMissing (AbstractArrayModel Index α)) : β := Id.run do
  let A := itr.x
  let mut ai : Option α := none
  let mut i := A.firstIndex
  let ilast := A.lastIndex
  for j in indexOps.range i ilast do
    i := j
    ai := A.get i
    if !ismissing ai then
      break
  if ismissing ai then
    return mapreduceEmpty f op
      (eltypeSkipMissing eltype typesplit ⟨()⟩)
  let a1 := assertNonmissing ai
  if indexOps.equal i indexOps.maximum then
    return mapreduceFirst f op a1
  i := indexOps.successor i
  ai := none
  for j in indexOps.range i ilast do
    i := j
    ai := A.get i
    if !ismissing ai then
      break
  if ismissing ai then
    return mapreduceFirst f op a1
  return something (mapreduceImplSkipMissing indexOps ismissing assertNonmissing
    mapreduceFirst something pairwiseBlocksize f op itr A.firstIndex A.lastIndex)
/--
Julia source: base/missing.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mapreduce(f, op, ::IndexCartesian, itr::SkipMissing) = mapfoldl(f, op, itr)
```
-/
def mapreduceIndexCartesian {Itr α β : Type}
    (mapfoldl : (α → β) → (β → β → β) → SkipMissing Itr → β)
    (f : α → β) (op : β → β → β) (itr : SkipMissing Itr) : β :=
  mapfoldl f op itr
/--
Julia source: base/missing.jl:272-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce(f, op, itr::SkipMissing{<:AbstractArray}) =
    _mapreduce(f, op, IndexStyle(itr.x), eltype(itr.x) >: Missing ? itr : itr.x)
```
-/
def mapreduceSkipMissing {Index α β : Type}
    (indexStyle : TypeRef (AbstractArrayModel Index α) → IndexStyleModel)
    (eltypeIncludesMissing : AbstractArrayModel Index α → Bool)
    (mapreduceRaw : (α → β) → (β → β → β) → AbstractArrayModel Index α → β)
    (mapfoldl : (α → β) → (β → β → β) → SkipMissing (AbstractArrayModel Index α) → β)
    (indexOps : IntegerIndexOps Index)
    (typesplit : JuliaType α → JuliaType α → JuliaType α)
    (eltype : TypeRef (AbstractArrayModel Index α) → JuliaType α)
    (ismissing : Option α → Bool)
    (assertNonmissing : Option α → α)
    (mapreduceEmpty : (α → β) → (β → β → β) → JuliaType α → β)
    (mapreduceFirst : (α → β) → (β → β → β) → α → β)
    (pairwiseBlocksize : (α → β) → (β → β → β) → JInt64)
    (something : Option β → β) (f : α → β) (op : β → β → β)
    (itr : SkipMissing (AbstractArrayModel Index α)) : β :=
  let array := itr.x
  let input :=
    if eltypeIncludesMissing array then
      SkipReduceInput.filtered itr
    else
      SkipReduceInput.raw array
  match input with
  | .raw array => mapreduceRaw f op array
  | .filtered itr =>
    match indexStyle ⟨()⟩ with
    | .linear =>
      mapreduceIndexLinear indexOps typesplit eltype ismissing assertNonmissing
        mapreduceEmpty mapreduceFirst pairwiseBlocksize something f op itr
    | .cartesian =>
      mapreduceIndexCartesian mapfoldl f op itr
end JuliaLean.base.missing
