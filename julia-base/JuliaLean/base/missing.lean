import JuliaLean.Core
import JuliaLean.Runtime.Collections
import JuliaLean.base.operators
import JuliaLean.base.essentials

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

inductive MissingMethodError where
  | methodError (functionName : String) (arguments : List (JuliaType String))
  deriving Repr
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

def unaryTypeAnyError {α : Type} (f : UnaryTypeFunction) : Except MissingMethodError α :=
  .error (.methodError f.juliaName [.any])

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

def floatTypeAnyError {α : Type} (f : FloatTypeFunction) : Except MissingMethodError α :=
  .error (.methodError f.juliaName [.any])

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


/- The terminating results of Julia's `iterate(::SkipMissing)` loop. -/
inductive iterateSkipMissingLoopReturns {Itr α State : Type}
    (iterateNext : Itr → State → Option (Option α × State))
    (ismissing : Option α → Bool) (itr : Itr) :
    Option α → State → Option (Option α × State) → Prop where
  | returned {item state} (h : ismissing item = false) :
      iterateSkipMissingLoopReturns iterateNext ismissing itr item state
        (some (item, state))
  | exhausted {item state} (h : ismissing item = true)
      (hnext : iterateNext itr state = none) :
      iterateSkipMissingLoopReturns iterateNext ismissing itr item state none
  | skipped {item state nextItem nextState result}
      (h : ismissing item = true)
      (hnext : iterateNext itr state = some (nextItem, nextState))
      (tail : iterateSkipMissingLoopReturns iterateNext ismissing itr
        nextItem nextState result) :
      iterateSkipMissingLoopReturns iterateNext ismissing itr item state result

/-- Relates a `SkipMissing` call to each result allowed by its source loop. -/
def iterateSkipMissingReturns {Itr α State : Type}
    (iterate : Itr → List State → Option (Option α × State))
    (iterateNext : Itr → State → Option (Option α × State))
    (ismissing : Option α → Bool) (itr : SkipMissing Itr) (state : List State)
    (result : Option (Option α × State)) : Prop :=
  match iterate itr.x state with
  | none => result = none
  | some (item, nextState) =>
      iterateSkipMissingLoopReturns iterateNext ismissing itr.x item nextState result

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

-- Source: base/missing.jl:253-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eachindexSkipMissingFilter {Itr Ix IndexIterator FilterResult α : Type}
    (filter : (Ix → Bool) → IndexIterator → FilterResult)
    (eachindex : Itr → IndexIterator)
    (getindex : Itr → Ix → Option α) (ismissing : Option α → Bool)
    (itr : SkipMissing Itr) : FilterResult :=
  filter (fun i => !ismissing (getindex itr.x i)) (eachindex itr.x)

-- Source: base/missing.jl:255-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def keysSkipMissingFilter {Itr K IndexIterator FilterResult α : Type}
    (filter : (K → Bool) → IndexIterator → FilterResult)
    (keys : Itr → IndexIterator)
    (getindex : Itr → K → Option α) (ismissing : Option α → Bool)
    (itr : SkipMissing Itr) : FilterResult :=
  filter (fun i => !ismissing (getindex itr.x i)) (keys itr.x)

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
  eachindexSkipMissingFilter filter eachindex getindex ismissing itr

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
  keysSkipMissingFilter filter keys getindex ismissing itr

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
  let initial := similar itr.x (eltypeSkipMissing eltype typesplit ⟨()⟩) 0
  let values := elements itr.x
  values.foldl (fun y xi =>
    if !ismissing xi then
      match xi with
      | none => y
      | some x => if f x then push y x else y
    else y) initial

/-- Typed syntax nodes for the escaped assignment, missing test, conditional, and let in `@coalesce`. -/
inductive CoalesceAssignment (Arg : Type) where
  | escapedAssignment (name : String) (arg : Arg)
  deriving Repr

inductive CoalesceCondition (Arg : Type) where
  | ismissing (assignment : CoalesceAssignment Arg)
  | not (condition : CoalesceCondition Arg)
  deriving Repr

inductive CoalesceExpr (Arg : Type) where
  | missing
  | variable (name : String)
  | conditional (condition : CoalesceCondition Arg)
      (whenTrue whenFalse : CoalesceExpr Arg)
  | letValue (body : CoalesceExpr Arg)
  deriving Repr

abbrev CoalesceRuntime (State : Type) := State × Option JuliaValue

def evalCoalesceAssignment {Arg State : Type}
    (evaluate : Arg → State → JuliaValue × State) :
    CoalesceAssignment Arg → CoalesceRuntime State → JuliaValue × CoalesceRuntime State
  | .escapedAssignment _ arg, (state, _) =>
    let (value, state) := evaluate arg state
    (value, (state, some value))

def evalCoalesceCondition {Arg State : Type}
    (evaluate : Arg → State → JuliaValue × State) :
    CoalesceCondition Arg → CoalesceRuntime State → Bool × CoalesceRuntime State
  | .ismissing assignment, state =>
    let (value, state) := evalCoalesceAssignment evaluate assignment state
    (match value with | .missing => true | .value _ => false, state)
  | .not condition, state =>
    let (value, state) := evalCoalesceCondition evaluate condition state
    (!value, state)

def evalCoalesceExprWithState {Arg State : Type}
    (evaluate : Arg → State → JuliaValue × State) :
    CoalesceExpr Arg → CoalesceRuntime State → JuliaValue × CoalesceRuntime State
  | .missing, state => (.missing, state)
  | .variable _, state => (state.2.getD .missing, state)
  | .conditional condition whenTrue whenFalse, state =>
    let (test, state) := evalCoalesceCondition evaluate condition state
    if test then evalCoalesceExprWithState evaluate whenTrue state
    else evalCoalesceExprWithState evaluate whenFalse state
  | .letValue body, (state, _) =>
    evalCoalesceExprWithState evaluate body (state, none)

def evalCoalesceExpr {Arg : Type} (evaluate : Arg → JuliaValue) :
    CoalesceExpr Arg → JuliaValue :=
  fun expr =>
    (evalCoalesceExprWithState (fun arg _ => (evaluate arg, ())) expr ((), none)).1

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
  let expr := args.reverse.foldl (fun rest arg =>
    .conditional (.not (.ismissing (.escapedAssignment "val" arg)))
      (.variable "val") rest) .missing
  .letValue expr
/-- Index operations supplied by the generic `Integer` interface of an array's linear indices. -/
structure IntegerIndexOps (Index : Type) where
  greater : Index → Index → Bool
  equal : Index → Index → Bool
  successor : Index → Index
  maximum : Index
  spanLessThan : Index → Index → JInt64 → Bool
  subtract : Index → Index → Index
  shiftRight : Index → JInt64 → Index
  add : Index → Index → Index
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
    let halfSpan := indexOps.shiftRight (indexOps.subtract ilast ifirst) (JInt.lit .i64 1)
    let imid := indexOps.add ifirst halfSpan
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
    (mapreduceRaw : IndexStyleModel → (α → β) → (β → β → β) →
      AbstractArrayModel Index α → β)
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
  let style := indexStyle ⟨()⟩
  let input :=
    if eltypeIncludesMissing array then
      SkipReduceInput.filtered itr
    else
      SkipReduceInput.raw array
  match style, input with
  | .linear, .raw array => mapreduceRaw .linear f op array
  | .cartesian, .raw array => mapreduceRaw .cartesian f op array
  | .linear, .filtered itr =>
    mapreduceIndexLinear indexOps typesplit eltype ismissing assertNonmissing
      mapreduceEmpty mapreduceFirst pairwiseBlocksize something f op itr
  | .cartesian, .filtered itr =>
    mapreduceIndexCartesian mapfoldl f op itr
/-- Dispatch Boolean operations over `Option` values through this file's missing methods. -/
def andOption : Option Bool → Option Bool → Option Bool
  | none, none => andMissingMissing
  | none, some right => andMissingBool JuliaLean.base.essentials.ifelse .missing right
  | some left, none => andBoolMissing JuliaLean.base.essentials.ifelse left .missing
  | some left, some right => some (left && right)

def orOption : Option Bool → Option Bool → Option Bool
  | none, none => orMissingMissing
  | none, some right => orMissingBool JuliaLean.base.essentials.ifelse .missing right
  | some left, none => orBoolMissing JuliaLean.base.essentials.ifelse left .missing
  | some left, some right => some (left || right)

def xorOption : Option Bool → Option Bool → Option Bool
  | none, none => xorMissingMissing
  | none, some right => xorMissingBool .missing right
  | some left, none => xorBoolMissing left .missing
  | some left, some right => some (left ^^ right)

def notOption : Option Bool → Option Bool
  | none => generatedUnaryMissing (α := Bool) .missing
  | some value => some (!value)

def nandOption (left right : Option Bool) : Option Bool :=
  notOption (andOption left right)

def norOption (left right : Option Bool) : Option Bool :=
  notOption (orOption left right)

def eqOption {α : Type} (eq : α → α → Bool) : Option α → Option α → Option Bool
  | none, none => equalMissingMissing
  | none, some right => equalMissingAny right
  | some left, none => equalAnyMissing left
  | some left, some right => some (eq left right)

def ltOption {α : Type} (lt : α → α → Bool) : Option α → Option α → Option Bool
  | none, none => lessMissingMissing
  | none, some right => lessMissingAny right
  | some left, none => lessAnyMissing left
  | some left, some right => some (lt left right)

def neOption {α : Type} (eq : α → α → Bool) (x y : Option α) : Option Bool :=
  JuliaLean.base.operators.notEqual (eqOption eq) notOption x y

def leOption {α : Type} (eq lt : α → α → Bool) (x y : Option α) : Option Bool :=
  JuliaLean.base.operators.lessEqual (ltOption lt) (eqOption eq) orOption x y

def gtOption {α : Type} (lt : α → α → Bool) (x y : Option α) : Option Bool :=
  JuliaLean.base.operators.greaterThan (ltOption lt) x y

def geOption {α : Type} (eq lt : α → α → Bool) (x y : Option α) : Option Bool :=
  JuliaLean.base.operators.greaterEqual (leOption eq lt) x y

def islessOption {α : Type} (lt : α → α → Bool) : Option α → Option α → Bool
  | none, none => islessMissingMissing
  | none, some right => islessMissingAny right
  | some left, none => islessAnyMissing left
  | some left, some right => lt left right

def isequalOption {α : Type} (eq : α → α → Bool) : Option α → Option α → Bool
  | none, none => isequalMissingMissing
  | none, some right => isequalMissingAny right
  | some left, none => isequalAnyMissing left
  | some left, some right => eq left right

def minOption {α : Type} (lt : α → α → Bool) : Option α → Option α → Option α
  | none, none => minmaxBinaryBothMissing MissingValue.missing MissingValue.missing
  | none, some right => minmaxBinaryMissingAny MissingValue.missing right
  | some left, none => minmaxBinaryAnyMissing left MissingValue.missing
  | some left, some right => if lt right left then some right else some left

def maxOption {α : Type} (lt : α → α → Bool) : Option α → Option α → Option α
  | none, none => minmaxBinaryBothMissing MissingValue.missing MissingValue.missing
  | none, some right => minmaxBinaryMissingAny MissingValue.missing right
  | some left, none => minmaxBinaryAnyMissing left MissingValue.missing
  | some left, some right => if lt right left then some left else some right

def minmaxOption {α : Type} (lt : α → α → Bool) :
    Option α → Option α → Option α × Option α
  | none, none => minmaxPairBothMissing MissingValue.missing MissingValue.missing
  | none, some right => minmaxPairMissingAny MissingValue.missing right
  | some left, none => minmaxPairAnyMissing left MissingValue.missing
  | some left, some right =>
      if lt right left then (some right, some left) else (some left, some right)

end JuliaLean.base.missing

namespace JuliaLean.MissingChar

/-- Errors of the skipmissing functions: a shared `JlError` or `MissingException`
(`base/missing.jl:14-16`). -/
inductive SMErr where
  | jl (e : JlError)
  | missingException
  deriving Repr, DecidableEq

abbrev SMJl (α : Type) := Except SMErr α

/-- `iterate(x::Vector, i)`, `base/array.jl`: `(x[i], i+1)` while `i ≤ length(x)`.
The state is the 1-based index of the next element. -/
def vecIterate (x : List (Option α)) (i : Nat) : Option (Option α × Nat) :=
  if 1 ≤ i ∧ i ≤ x.length then some (x.getD (i - 1) none, i + 1) else none

/-- The `while ismissing(item)` loop of `iterate(itr::SkipMissing, state...)`,
`base/missing.jl:244-248`. Bound: `fuel` = elements left after `s`. -/
def smWhile (x : List (Option α)) : Nat → Option α → Nat → Option (α × Nat)
  | _, some a, s => some (a, s)
  | 0, none, _ => none
  | fuel + 1, none, s =>
    match vecIterate x s with
    | none => none
    | some (item, s') => smWhile x fuel item s'

/-- `iterate(itr::SkipMissing, state...)`, `base/missing.jl:240-250`. -/
def smIterate (x : List (Option α)) (s : Nat) : Option (α × Nat) :=
  match vecIterate x s with
  | none => none
  | some (item, s') => smWhile x (x.length + 1 - s') item s'

/-- `collect(skipmissing(x))`: the values `iterate` yields from state 1.
Bound: `fuel`, at least the number of elements left. -/
def smCollectFrom (x : List (Option α)) : Nat → Nat → List α
  | 0, _ => []
  | fuel + 1, s =>
    match smIterate x s with
    | none => []
    | some (a, s') => a :: smCollectFrom x fuel s'

def smCollect (x : List (Option α)) : List α := smCollectFrom x (x.length + 1) 1

/-- `keys(itr::SkipMissing) = Iterators.filter(i -> !ismissing(itr.x[i]), keys(itr.x))`
and `eachindex` likewise, `base/missing.jl:253-256`. -/
def smKeys (x : List (Option α)) : List Nat :=
  (List.range x.length).map (· + 1) |>.filter fun i => (x.getD (i - 1) none).isSome

/-- `x[i]` for an `Int` index: `BoundsError` outside `1:length(x)`. -/
def vecGet (x : List (Option α)) (i : Int) : SMJl (Option α) :=
  if 1 ≤ i ∧ i ≤ x.length then .ok (x.getD (i.toNat - 1) none) else .error (.jl .boundsError)

/-- `getindex(itr::SkipMissing, i::Int)`, `base/missing.jl:257-261`. -/
def smGetindex (x : List (Option α)) (i : Int) : SMJl α := do
  let v ← vecGet x i
  match v with
  | none => .error .missingException
  | some a => .ok a

/-- `getindex(itr::SkipMissing, I::AbstractVector{Int})`, `base/missing.jl:257-261`:
`v = itr.x[I]` is a vector, and `ismissing(v)` is false for a vector. -/
def smGetindexVec (x : List (Option α)) (I : List Int) : SMJl (List (Option α)) :=
  I.mapM (vecGet x)

/-- `filter(f, itr::SkipMissing{<:AbstractArray})`, `base/missing.jl:385-393`. -/
def smFilter (f : α → Bool) (x : List (Option α)) : List α :=
  x.foldl (fun y xi => match xi with
    | some a => if f a then y ++ [a] else y
    | none => y) []

/-- `findfirst(testf, A)` for non-arrays, `base/array.jl:2523-2528`:
`for (i, a) in pairs(A)`; `pairs(A) = Generator(=>, keys(A), values(A))`
(`base/abstractdict.jl:178`) zips `keys(itr)` with the iteration of `itr`. -/
def smFindfirst (f : α → Bool) (x : List (Option α)) : Option Nat :=
  ((smKeys x).zip (smCollect x)).find? (fun p => f p.2) |>.map (·.1)

/-- `IteratorSize` of an iterator. -/
inductive ISize where
  | hasLength (n : Nat)
  | sizeUnknown
  | isInfinite
  deriving DecidableEq

/-- `first(_zip_lengths_finite_equal(is))`, `base/iterators.jl:401-411`. -/
def zipLengthsFiniteEqual : List ISize → Bool × Option Nat
  | [] => (true, none)
  | .hasLength m :: rest =>
    let (b, n) := zipLengthsFiniteEqual rest
    (b && (n.isNone || n == some m), some m)
  | _ :: _ => (false, none)

/-- `findlast(testf, A)` for non-arrays, `base/array.jl:2716-2721`:
`for (i, a) in Iterators.reverse(pairs(A))`. `reverse(G::Generator)` reverses the
zipped iterators (`base/iterators.jl:157`), and `reverse(z::Zip)` throws
`ArgumentError` unless all have finite equal lengths (`:521-526`).
`IteratorSize(::Type{<:Filter}) = SizeUnknown()` (`:596`) for `keys(itr)` and
`IteratorSize(::Type{<:SkipMissing}) = SizeUnknown()` (`base/missing.jl:236`). -/
def smFindlast (f : α → Bool) (x : List (Option α)) : SMJl (Option Nat) :=
  if !(zipLengthsFiniteEqual [.sizeUnknown, .sizeUnknown]).1 then
    .error (.jl (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths"))
  else
    .ok (((smKeys x).zip (smCollect x)).reverse.find? (fun p => f p.2) |>.map (·.1))

/-! ## `mapreduce` over `skipmissing` of an array, `base/missing.jl:272-362` -/

/-- The `for outer i in i:ilast; ai = A[i]; !ismissing(ai) && break; end` scans
(`base/missing.jl:281-284, 290-293, 322-325, 331-334`): the first non-missing value
at an index in `i:ilast` and that index. Bound: `fuel` = `ilast + 1 - i`. -/
def firstNonMissing (x : List (Option α)) : Nat → Nat → Nat → Option (α × Nat)
  | 0, _, _ => none
  | fuel + 1, i, ilast =>
    if i > ilast then none
    else match x.getD (i - 1) none with
      | some a => some (a, i)
      | none => firstNonMissing x fuel (i + 1) ilast

/-- The `@simd for i = i:ilast` accumulation, `base/missing.jl:340-345`, as a
left fold (`@simd` may reassociate `op`; the statements below assume `op`
associative). Bound: `fuel` = `ilast + 1 - i`. -/
def simdLoop (f : α → β) (op : β → β → β) (x : List (Option α)) : Nat → Nat → Nat → β → β
  | 0, _, _, v => v
  | fuel + 1, i, ilast, v =>
    if i > ilast then v
    else
      let v := match x.getD (i - 1) none with
        | some a => op v (f a)
        | none => v
      simdLoop f op x fuel (i + 1) ilast v

/-- `_mapreduce_impl_skipmissing(f, op, itr, ifirst, ilast, blksize)`,
`base/missing.jl:306-362`, returning `nothing` (`none`) or `Some(v)`.
`mapreduce_first(f, op, a) = reduce_first(op, f(a)) = f(a)` for a generic `op`
(`base/reduce.jl`). -/
def mrImpl (f : α → β) (op : β → β → β) (x : List (Option α)) (blk : Nat)
    (ifirst ilast : Nat) : Option β :=
  if ifirst > ilast then none
  else if ifirst = ilast then
    match x.getD (ifirst - 1) none with
    | none => none
    | some a1 => some (f a1)
  else if ilast - ifirst < blk then
    match firstNonMissing x (ilast + 1 - ifirst) ifirst ilast with
    | none => none
    | some (a1, i) =>
      match firstNonMissing x (ilast - i) (i + 1) ilast with
      | none => some (f a1)
      | some (a2, i) => some (simdLoop f op x (ilast - i) (i + 1) ilast (op (f a1) (f a2)))
  else
    let imid := ifirst + (ilast - ifirst) / 2
    let v1 := mrImpl f op x blk ifirst imid
    let v2 := mrImpl f op x blk (imid + 1) ilast
    match v1, v2 with
    | none, none => none
    | none, v2 => v2
    | v1, none => v1
    | some a, some b => some (op a b)
termination_by ilast + 1 - ifirst

/-- `mapreduce(f, op, skipmissing(A))` for `A::Vector{Union{Missing,T}}`:
`_mapreduce(f, op, IndexLinear(), itr)`, `base/missing.jl:272-297`. `empty` is
`mapreduce_empty(f, op, eltype(itr))` (an error for a generic `op`). -/
def mrSkip (f : α → β) (op : β → β → β) (empty : Jl β) (blk : Nat)
    (x : List (Option α)) : Jl β :=
  let ilast := x.length
  match firstNonMissing x ilast 1 ilast with
  | none => empty
  | some (a1, i) =>
    match firstNonMissing x (ilast - i) (i + 1) ilast with
    | none => .ok (f a1)
    | some _ =>
      match mrImpl f op x blk 1 ilast with
      | some v => .ok v
      | none => .error (.argumentError "something(nothing)")

end JuliaLean.MissingChar

namespace JuliaLean.MissingChar

/-- `ismissing(x) = x === missing`, `base/essentials.jl`. -/
def JV.isMissing : JV α → Bool
  | .missing => true
  | _ => false

/-- `coalesce(x...)`, `base/missing.jl:420-422`:
`coalesce() = missing`, `coalesce(x::Missing, y...) = coalesce(y...)`,
`coalesce(x::Any, y...) = x`. -/
def coalesce : List (JV α) → JV α
  | [] => .missing
  | .missing :: ys => coalesce ys
  | x :: _ => x

/-- `@coalesce(x...)`, `base/missing.jl:451-457`: arguments evaluated in turn,
`!ismissing(val) ? val : <rest>`, innermost `missing`. -/
def atCoalesce : List (JV α) → JV α
  | [] => .missing
  | v :: rest => if !v.isMissing then v else atCoalesce rest

end JuliaLean.MissingChar


/-! Method-specific models for `base/missing.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.MissingCov

open JuliaLean.MissingChar

def m5 (_ : Unit) : String := "missing"

def m18 (msg : String) : String := "MissingException: " ++ msg

def m39 (typesplit : α → α → α) (missing T : α) : α := typesplit T missing

def m41 (nonmissing : α → α) (supertype isBottom : α → α → Bool) (T bottom : α) : RJ α :=
  let R := nonmissing T
  if supertype R T then .error (.errorException "could not compute non-missing type")
  else if isBottom R bottom then .error (.errorException "cannot convert a value to missing for assignment")
  else .ok R

def m48 (unionMissing : α → α) (S : α) : α := unionMissing S

def m49 (unionNothingMissing : α → α) (S : α) : α := unionNothingMissing S

def m50 (nonnothing nonmissing : α → α) (supertype : α → α → Bool)
    (promote : α → α → α) (unionBoth : α → α) (any T S : α) : α :=
  let Rn := nonnothing T
  if supertype Rn T then any
  else
    let Rm := nonmissing Rn
    if supertype Rm Rn then any else unionBoth (promote Rm S)

def m60 (nonmissing : α → α) (supertype : α → α → Bool) (promote : α → α → α)
    (unionMissing : α → α) (any T S : α) : α :=
  let R := nonmissing T
  if supertype R T then any else unionMissing (promote R S)

def m68 (x : α) : α := x

def m69 (x : α) : α := x

def m70 (checked : τ → RJ σ) (convert : σ → α → RJ β) (T : τ) (x : α) : RJ β := do
  (checked T).bind (fun R => convert R x)

def m71 (nonnothing : τ → RJ σ) (nonmissing : σ → RJ ρ) (convert : ρ → α → RJ β)
    (T : τ) (x : α) : RJ β :=
  (nonnothing T).bind (fun R => (nonmissing R).bind (fun U => convert U x))

@[simp] def missingResult (α : Type) : Option α := none

def m74 := missingResult Bool
def m76 (α : Type) (_ : α) := missingResult Bool
def m78 (α : Type) (_ : α) := missingResult Bool
def m79 (α : Type) (_ : α) := missingResult Bool
def m82 (α : Type) (_ : α) : Bool := false
def m83 := missingResult Bool
def m85 (α : Type) (_ : α) := missingResult Bool
def m86 : Bool := false
def m89 := missingResult Bool
def m90 := missingResult Bool
def m91 := missingResult Bool
def m92 (α : Type) (_ : α) := missingResult Bool
def m93 (α : Type) (_ : α) := missingResult Bool

/-- Every generated unary method returns `missing`, `base/missing.jl:96-103`. -/
def m103 (α : Type) (_function : String) : Option α := none

def m106 (α : Type) (f : String) : Jl α := .error (.methodError f)
def m107 (α : Type) (_function : String) : Option α := none
def m108 (checked : τ → RJ σ) (f : σ → RJ α) (T : τ) : RJ α := (checked T).bind f
def m111 (α : Type) (f : String) : Jl α := .error (.methodError f)
def m112 (nonmissing : τ → σ) (f : σ → ρ) (unionMissing : ρ → α) (T : τ) : α :=
  unionMissing (f (nonmissing T))

def m119 (α : Type) (_function : String) : Option α := none
def m120 (α β : Type) (_function : String) (_ : β) : Option α := none
def m121 (α β : Type) (_function : String) (_ : β) : Option α := none
def m125 (α : Type) (_rounding : α) := missingResult Int
def m126 (α β : Type) (_number : α) (_rounding : β) := missingResult Int
def m127 (α β : Type) (_number : α) (_rounding : β) := missingResult Int

def m131 (result : α) : α := result
def m132 (result : α) (_ : β) : α := result
def m133 (result : α) (_ : β) : α := result
def m134 (result : α) : α := result
def m137 (α β γ : Type) (_lo : β) (_hi : γ) : Option α := none
def m139 (T : String) : String :=
  "cannot convert a missing value to type " ++ T ++ ": use Union{" ++ T ++ ", Missing} instead"

def m143 (α : Type) (_sigdigits _digits _base : Int) : Option α := none
def m144 (α : Type) (_rounding : α) := missingResult Int
def m145 (T : String) : RJ Unit := .error (.missingException (m139 T))
def m147 (checked : τ → RJ σ) (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ) : RJ β := do
  (checked T).bind (fun U => round U x r)
def m149 := @m147
def m150 := @m147
def m151 := @m147
def m154 (α : Type) (_exponent : Int) : Option α := none

def m157 := missingResult Bool
def m159 (b : Bool) : Option Bool := if b then none else some false
def m160 (α : Type) (_ : α) := missingResult α
def m161 (α : Type) (_ : α) := missingResult α
def m162 := missingResult Bool
def m164 (b : Bool) : Option Bool := if b then some true else none
def m165 (α : Type) (_ : α) := missingResult α
def m166 (α : Type) (_ : α) := missingResult α
def m167 := missingResult Bool
def m169 (_ : Bool) := missingResult Bool
def m170 (α : Type) (_ : α) := missingResult α
def m171 (α : Type) (_ : α) := missingResult α
def m173 (α : Type) (_ : α) := missingResult String
def m174 (α : Type) (_ : α) := missingResult String

inductive FloatKind where | abstractReal | concreteBigFloat deriving DecidableEq
inductive FloatValue where | missing | exactBig | roundedF64 deriving DecidableEq

/-- `float(A::AbstractArray{Union{T,Missing}})`, `base/missing.jl:176-179`. -/
def m176 (T : FloatKind) (A : List FloatValue) : List FloatValue :=
  let U : FloatValue := match T with | .abstractReal => .roundedF64 | .concreteBigFloat => .exactBig
  A.map fun x => match x, U with
    | .missing, _ => .missing
    | .exactBig, .roundedF64 => .roundedF64
    | value, _ => value

def m180 (A : List FloatValue) := A

structure Skip (α : Type) where x : List (Option α)

def m231 (x : List (Option α)) : Skip α := ⟨x⟩
def m236 : MissingChar.ISize := .sizeUnknown
def m237 (parentStyle : α → β) (T : α) : β := parentStyle T
def m238 (eltype : α → β) (nonmissing : β → γ) (T : α) : γ := nonmissing (eltype T)
def m252 (indexStyle : α → β) (T : α) : β := indexStyle T
def m263 (showParent : List (Option α) → String) (s : Skip α) : String :=
  "skipmissing(" ++ showParent s.x ++ ")"

def m275 (f : α → β) (op : β → β → β) (empty : Jl β) (blk : Nat) (s : Skip α) : Jl β :=
  mrSkip f op empty blk s.x
def m299 (mapfoldl : (α → β) → (β → β → β) → Skip α → γ)
    (f : α → β) (op : β → β → β) (s : Skip α) : γ := mapfoldl f op s
def m303 (pairwise : (α → β) → (β → β → β) → Nat)
    (f : α → β) (op : β → β → β) (s : Skip α) (first last : Nat) : Option β :=
  mrImpl f op s.x (pairwise f op) first last
def m306 (f : α → β) (op : β → β → β) (s : Skip α) (first last blk : Nat) : Option β :=
  mrImpl f op s.x blk first last

def m420 (α : Type) : JV α := .missing
def m421 (ys : List (JV α)) : JV α := coalesce ys
def m422 (x : JV α) (_ys : List (JV α)) : JV α := x

inductive CoalesceExpr (α : Type) where
  | missing
  | branch (value : JV α) (rest : CoalesceExpr α)

def m451 (args : List (JV α)) : CoalesceExpr α :=
  args.reverse.foldl (fun expr value => .branch value expr) .missing

end JuliaLean.ReduceCov.MissingCov

namespace JuliaLean.Reduce.Ty

/-- `nonmissingtype(T)`, `base/missing.jl:39`; `Missing` gives `Union{}`. -/
def nonmissing : Ty → Ty
  | .missing => .bottom
  | .union a b =>
    match nonmissing a, nonmissing b with
    | .bottom, y => y
    | x, .bottom => x
    | x, y => .union x y
  | t => t

end JuliaLean.Reduce.Ty
