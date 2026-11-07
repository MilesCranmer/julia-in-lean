import JuliaLean.Core
import JuliaLean.base.abstractarray
import JuliaLean.base.promotion
import JuliaLean.base.tuple

/-!
# Model of `base/some.jl`

Julia values of type `Some{T}` are `SomeValue T α`; the indexed `T` records the Julia type
parameter while `α` represents its Lean payload. Dynamic values used by `something`, `notnothing`
and `isnothing` use `Value α`, which preserves nested `Some(nothing)`. Julia's type operations use
the existing `PType` model. Calls into later-loaded or user-extensible functions remain typed
parameters; Julia dispatch is trusted.
-/

namespace JuliaLean.base.some

open JuliaLean
open JuliaLean.base.promotion

inductive SomeException where
  | errorException (message : String)
  | julia (error : JlError)
  deriving DecidableEq, Repr

/-! ## `Some` values and their Julia type tags -/

/--
Julia source: base/some.jl:11-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Some{T}
    value::T
end
```
-/
structure SomeValue (T : PType) (α : Type) where
  value : α

private def someTypeName : TypeName := ⟨"Base", "Some"⟩

def someValueType (T : PType) : PType :=
  .data someTypeName "Some" [T] (some .any)

def typeObjectType (T : PType) : PType := .typeEq T

/--
Julia source: base/some.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Some(::Type{T}) where {T} = Some{Type{T}}(T)
```
-/
def someTypeObject (T : PType) : SomeValue (typeObjectType T) PType := ⟨T⟩

/-! ## Removing `Nothing` from types and promotion rules -/

/--
Julia source: base/some.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nonnothingtype(@nospecialize(T::Type)) = typesplit(T, Nothing)
```
-/
def nonnothingtype (ops : PTypeOps) (T : PType) : PType :=
  typesplit ops T primitiveNothingType

/--
Julia source: base/some.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(T::Type{Nothing}, S::Type) = Union{S, Nothing}
```
-/
def promoteRuleNothing (S : PType) : PType := .union S primitiveNothingType

/--
Julia source: base/some.jl:19-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_rule(T::Type{>:Nothing}, S::Type)
    R = nonnothingtype(T)
    R >: T && return Any
    T = R
    R = promote_type(T, S)
    return Union{R, Nothing}
end
```
-/
def promoteRuleWithNothing (ops : PTypeOps)
    (promoteRule : PType → PType → Option PType) (T S : PType) : Option PType := do
  let mut R := nonnothingtype ops T
  if ops.subtype T R then return .any
  let mut T := R
  R ← promoteType promoteRule T S
  return .union R primitiveNothingType

/--
Julia source: base/some.jl:27-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nonnothingtype_checked(T::Type)
    R = nonnothingtype(T)
    R >: T && error("could not compute non-nothing type")
    R <: Union{} && error("cannot convert a value to nothing for assignment")
    return R
end
```
-/
def nonnothingtypeChecked {ε : Type} (ops : PTypeOps) (error : String → ε)
    (T : PType) : Except ε PType := do
  let R := nonnothingtype ops T
  if ops.subtype T R then throw (error "could not compute non-nothing type")
  if ops.subtype R .bottom then throw (error "cannot convert a value to nothing for assignment")
  pure R

/-! ## Conversion methods for `T>:Nothing` and `Some{T}` -/

/--
Julia source: base/some.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T) where {T>:Nothing} = x
```
-/
def convertNothingSame {α : Type} (ops : PTypeOps) (T : PType)
    (_acceptsNothing : ops.subtype primitiveNothingType T = true) (x : α) : α := x

/--
Julia source: base/some.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x) where {T>:Nothing} = convert(nonnothingtype_checked(T), x)
```
-/
def convertNothingOther {ε α β : Type} (ops : PTypeOps) (error : String → ε)
    (convert : PType → α → Except ε β) (T : PType)
    (_acceptsNothing : ops.subtype primitiveNothingType T = true) (x : α) : Except ε β := do
  let R ← nonnothingtypeChecked ops error T
  convert R x

/--
Julia source: base/some.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Some{T}}, x::Some{T}) where {T} = x
```
-/
def convertSomeSame {T : PType} {α : Type} (x : SomeValue T α) : SomeValue T α := x

/--
Julia source: base/some.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Some{T}}, x::Some) where {T} = Some{T}(convert(T, x.value))::Some{T}
```
-/
def convertSome {ε α β : Type} (convert : PType → α → Except ε β)
    (T S : PType) (x : SomeValue S α) : Except ε (SomeValue T β) := do
  let value ← convert T x.value
  pure ⟨value⟩

/-! ## Display -/

/-- State of an `IOContext` relevant to `show(::IO, ::Some)`. -/
structure ShowIO where
  typeinfo : Option PType
  output : String

/-- Operations supplied by Julia's `get`, `show` and `print` methods. -/
structure ShowOperations (α : Type) where
  get : ShowIO → String → PType → PType
  showValue : ShowIO → α → ShowIO
  printString : ShowIO → String → ShowIO
  printChar : ShowIO → Char → ShowIO

def someTypeOf {T : PType} {α : Type} (_x : SomeValue T α) : PType := someValueType T

/--
Julia source: base/some.jl:39-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, x::Some)
    if get(io, :typeinfo, Any) == typeof(x)
        show(io, x.value)
    else
        print(io, "Some(")
        show(io, x.value)
        print(io, ')')
    end
end
```
-/
def showSome {T : PType} {α : Type} (ops : ShowOperations α)
    (io : ShowIO) (x : SomeValue T α) : ShowIO :=
  if pEqual (ops.get io ":typeinfo" .any) (someTypeOf x) then
    ops.showValue io x.value
  else
    let io := ops.printString io "Some("
    let io := ops.showValue io x.value
    ops.printChar io ')'

/-! ## `notnothing`, `isnothing` and `something` -/

/-- Dynamic values for the methods accepting `Any`, `Some` and `Nothing`. -/
inductive Value (α : Type) : Type where
  | nothing
  | some (value : Value α)
  | scalar (value : α)

namespace Value

def isNothing : Value α → Bool
  | .nothing => true
  | _ => false

def unwrap : Value α → Value α
  | .some value => value
  | value => value

end Value

/--
Julia source: base/some.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
notnothing(x::Any) = x
```
-/
def notnothingAny {α : Type} (x : α) : Jl α := .ok x

/--
Julia source: base/some.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
notnothing(::Nothing) = throw(ArgumentError("nothing passed to notnothing"))
```
-/
def notnothingNothing {α : Type} (_nothing : Unit) : Jl (Value α) :=
  .error (.argumentError "nothing passed to notnothing")

def notnothing {α : Type} : Value α → Jl (Value α)
  | .nothing => notnothingNothing ()
  | x => notnothingAny x

/--
Julia source: base/some.jl:67-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnothing(x) = x === nothing
```
-/
def isnothing {α : Type} (x : Value α) : Bool := x.isNothing

/--
Julia source: base/some.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
something() = throw(ArgumentError("No value arguments present"))
```
-/
def somethingZero {α : Type} : Jl (Value α) :=
  .error (.argumentError "No value arguments present")

mutual
/--
Julia source: base/some.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
something(x::Nothing, y...) = something(y...)
```
-/
def somethingNothing {α : Type} : List (Value α) → Jl (Value α)
  | ys => something ys
termination_by ys => 2 * ys.length + 2
decreasing_by omega

/--
Julia source: base/some.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
something(x::Some, y...) = x.value
```
-/
def somethingSome {α : Type} (x : Value α) : Jl (Value α) := .ok x.unwrap

/--
Julia source: base/some.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
something(x::Any, y...) = x
```
-/
def somethingAny {α : Type} (x : Value α) : Jl (Value α) := .ok x

def something {α : Type} : List (Value α) → Jl (Value α)
  | [] => somethingZero
  | x@(.some _) :: _ => somethingSome x
  | .nothing :: ys => somethingNothing ys
  | x :: _ => somethingAny x
termination_by xs => 2 * xs.length + 1
decreasing_by all_goals simp_wf <;> omega
end

/-! ## Short-circuit macro model -/

/-- The expression tree required by Julia's macro expansion. -/
inductive JuliaExpr where
  | symbol (name : String)
  | globalRef (moduleName name : String)
  | call (fn : JuliaExpr) (args : List JuliaExpr)
  | escape (expr : JuliaExpr)
  | assign (left right : JuliaExpr)
  | ifThenElse (condition yes no : JuliaExpr)
  | block (expressions : List JuliaExpr)
  deriving Repr

private def tupleKeys (args : List JuliaExpr) : JuliaLean.base.abstractarray.Result (List Nat) :=
  .ok (JuliaLean.base.tuple.keysTuple args)

private def tupleErrorToArrayError : JuliaLean.base.tuple.TupleError →
    JuliaLean.base.abstractarray.ArrayError
  | .julia error => .julia error
  | .dimensionMismatch => .errorException "DimensionMismatch"
  | .typeError => .errorException "TypeError"
  | .fieldError => .errorException "FieldError"
  | .errorException => .errorException "ErrorException"

/--
Julia source: base/some.jl:138-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro something(args...)
    noth = GlobalRef(Base, :nothing)
    something = GlobalRef(Base, :something)

    # This preserves existing semantics of throwing on `nothing`
    expr = :($something($noth))

    #=
    We go through the arguments in reverse
    because we're building a nested if/else
    expression from the inside out.
    The innermost thing to check is the last argument,
    which is why we need the last argument first
    when building the final expression.
    =#
    for i in reverse(eachindex(args))
        arg  = args[i]
        val = Cartesian.inlineanonymous(:val, i)
        expr = quote
            $val = $(esc(arg))
            if !isnothing($val)
                # unwrap eagerly to help type inference
                $something($val)
            else
                $expr
            end
        end
    end
    return expr
end
```
-/
def macroSomething (reverse : List Nat → List Nat)
    (inlineanonymous : String → Nat → JuliaExpr) (esc : JuliaExpr → JuliaExpr)
    (args : List JuliaExpr) : JuliaLean.base.abstractarray.Result JuliaExpr := do
  let noth := JuliaExpr.globalRef "Base" "nothing"
  let something := JuliaExpr.globalRef "Base" "something"
  let mut expr := JuliaExpr.call something [noth]
  let indices ← JuliaLean.base.abstractarray.eachindexIterators tupleKeys args
  for i in reverse indices do
    let arg ← (JuliaLean.base.tuple.getindexInteger args (.big (Int.ofNat i)) :
      JuliaLean.base.tuple.R JuliaExpr).mapError tupleErrorToArrayError
    let val := inlineanonymous "val" i
    expr := .block [
      .assign val (esc arg),
      .ifThenElse (.call (.symbol "!") [.call (.symbol "isnothing") [val]])
        (.call something [val]) expr]
  return expr

/-- Effectful arguments expose the macro's short-circuit evaluation order. -/
abbrev ValueThunk (α : Type) := Nat → Jl (Value α) × Nat

def atSomething {α : Type} : List (ValueThunk α) → Nat → Jl (Value α) × Nat
  | [], state => (something [.nothing], state)
  | arg :: rest, state =>
      let (value, nextState) := arg state
      match value with
      | .error e => (.error e, nextState)
      | .ok value =>
          if isnothing value then atSomething rest nextState
          else (something [value], nextState)

/-! ## Comparisons and hashing -/

/--
Julia source: base/some.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::Some, b::Some) = a.value == b.value
```
-/
def eqSome {T S : PType} {α β γ : Type} (eq : α → β → γ)
    (a : SomeValue T α) (b : SomeValue S β) : γ := eq a.value b.value

/--
Julia source: base/some.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(a::Some, b::Some)::Bool = isequal(a.value, b.value)
```
-/
def isequalSome {T S : PType} {α β : Type} (isequal : α → β → Bool)
    (a : SomeValue T α) (b : SomeValue S β) : Bool := isequal a.value b.value

/-! ## Hash -/

inductive UIntWidth where
  | u32
  | u64
  deriving DecidableEq, Repr

def UIntWidth.intTy : UIntWidth → IntTy
  | .u32 => .u32
  | .u64 => .u64

/--
Julia source: base/some.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const hash_some_seed = UInt == UInt64 ? 0xde5c997007a4ca3a : 0x78c29c09
```
-/
def hash_some_seed (width : UIntWidth) : JInt width.intTy :=
  JInt.lit width.intTy
    (if width == .u64 then 0xde5c997007a4ca3a else 0x78c29c09)

/--
Julia source: base/some.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(s::Some, h::UInt) = hash(s.value, hash_some_seed +% h)
```
-/
def hashSome {T : PType} {α : Type} (width : UIntWidth)
    (hash : α → JInt width.intTy → JInt width.intTy)
    (s : SomeValue T α) (h : JInt width.intTy) : JInt width.intTy :=
  hash s.value (hash_some_seed width + h)

end JuliaLean.base.some

namespace JuliaLean.MissingChar

/-- `isnothing(x) = x === nothing`, `base/some.jl:67`. -/
def JV.isNothing : JV α → Bool
  | .nothing => true
  | _ => false

/-- `something(x...)`, `base/some.jl:99-102`. -/
def something : List (JV α) → Jl (JV α)
  | [] => .error (.argumentError "No value arguments present")
  | .nothing :: ys => something ys
  | .some v :: _ => .ok v
  | x :: _ => .ok x

/-- `@something(x...)`, `base/some.jl:138-167`: the first value that is not
`nothing` is passed to `something(val)`; the innermost expression is
`something(nothing)`. -/
def atSomething : List (JV α) → Jl (JV α)
  | [] => something [.nothing]
  | v :: rest => if !v.isNothing then something [v] else atSomething rest

/-- `notnothing(x)`, `base/some.jl:54-55`. -/
def notnothing : JV α → Jl (JV α)
  | .nothing => .error (.argumentError "nothing passed to notnothing")
  | x => .ok x

/-- `isequal(a::Some, b::Some) = isequal(a.value, b.value)`, `base/some.jl:170`. -/
def isequalSome (eqv : α → α → Bool) (a b : α) : Bool := eqv a b

/-- `hash(s::Some, h) = hash(s.value, hash_some_seed +% h)`, `base/some.jl:171-172`. -/
def hashSome (hash : α → UInt64 → UInt64) (a : α) (h : UInt64) : UInt64 :=
  hash a (0xde5c997007a4ca3a + h)

end JuliaLean.MissingChar

namespace JuliaLean.ReduceCov.SomeRows

open JuliaLean.MissingChar

structure SomeV (α : Type) where
  value : α
  deriving Repr, DecidableEq

/-- `Some(::Type{T}) where T`, `base/some.jl:15`. -/
def m15 (T : α) : SomeV α := ⟨T⟩

/-- `nonnothingtype(T) = typesplit(T, Nothing)`, `base/some.jl:17`. -/
def m17 (typesplit : α → α → α) (nothing T : α) : α := typesplit T nothing

/-- `promote_rule(::Type{Nothing}, S)`, `base/some.jl:18`. -/
def m18 (unionNothing : α → α) (S : α) : α := unionNothing S

/-- The general `Nothing` promotion rule, `base/some.jl:19-25`. -/
def m19 (nonnothing : α → α) (supertype : α → α → Bool) (promote : α → α → α)
    (unionNothing : α → α) (any T S : α) : α :=
  let R := nonnothing T
  if supertype R T then any else unionNothing (promote R S)

/-- `nonnothingtype_checked`, including both ordered checks, `base/some.jl:27-32`. -/
def m27 (nonnothing : α → α) (supertype isBottom : α → α → Bool) (T bottom : α) : RJ α :=
  let R := nonnothing T
  if supertype R T then .error (.errorException "could not compute non-nothing type")
  else if isBottom R bottom then .error (.errorException "cannot convert a value to nothing for assignment")
  else .ok R

/-- Same-type conversion, `base/some.jl:34`. -/
def m34 (x : α) : α := x

/-- General conversion to a type containing `Nothing`, `base/some.jl:35`. -/
def m35 (checked : τ → RJ σ) (convert : σ → α → RJ β) (T : τ) (x : α) : RJ β := do
  convert (← checked T) x

/-- Same-parameter `Some` conversion, `base/some.jl:36`. -/
def m36 (x : SomeV α) : SomeV α := x

/-- Converting between `Some` parameters, `base/some.jl:37`. -/
def m37 (convert : α → RJ β) (x : SomeV α) : RJ (SomeV β) := do
  pure ⟨← convert x.value⟩

/-- `notnothing(x::Any)`, `base/some.jl:54`. -/
def m54 (x : JV α) : Jl (JV α) := .ok x

/-- `notnothing(::Nothing)`, `base/some.jl:55`. -/
def m55 (α : Type) : Jl (JV α) := .error (.argumentError "nothing passed to notnothing")

/-- `isnothing(x) = x === nothing`, `base/some.jl:67`. -/
def m67 (x : JV α) : Bool := x.isNothing

/-- Zero-argument `something`, `base/some.jl:99`. -/
def m99 (α : Type) : Jl (JV α) := .error (.argumentError "No value arguments present")

/-- `something(x::Nothing, y...)`, `base/some.jl:100`. -/
def m100 (ys : List (JV α)) : Jl (JV α) := something ys

/-- `something(x::Some, y...)`, `base/some.jl:101`. -/
def m101 (x : JV α) (_ys : List (JV α)) : Jl (JV α) :=
  match x with | .some value => .ok value | other => .ok other

/-- `something(x::Any, y...)`, `base/some.jl:102`. -/
def m102 (x : JV α) (_ys : List (JV α)) : Jl (JV α) := .ok x

inductive SomethingExpr (α : Type) where
  | fail
  | branch (value : JV α) (rest : SomethingExpr α)

/-- The reverse loop that builds `@something`'s nested expression, `base/some.jl:138-167`. -/
def m138 (args : List (JV α)) : SomethingExpr α :=
  args.reverse.foldl (fun expr value => .branch value expr) .fail

/-- `==(a::Some, b::Some)`, `base/some.jl:169`. -/
def m169 (eq : α → α → β) (a b : SomeV α) : β := eq a.value b.value

end JuliaLean.ReduceCov.SomeRows
