import JuliaLean.Core
import JuliaLean.base.expr

/-!
# Model of `base/Enums.jl`

Typed enum values carry a nominal tag and their primitive integer payload. Calls into generated enum constructors, name maps, hashing, I/O, and display dispatch are explicit parameters; the macro and its syntax builder remain visible because they create caller-module types and Julia expressions during expansion.
-/

namespace JuliaLean.base.Enums

open JuliaLean
open JuliaLean.base.expr

/--
Julia source: base/Enums.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function namemap end
```
-/
structure EnumNameOps (Tag Base Map Sym Error : Type) where
  namemap : Tag → Except Error Map
  getindex : Map → Base → Except Error Sym
  get : Map → Base → (Unit → Except Error Sym) → Except Error Sym
  symbol : String → Except Error Sym
  string : Base → Except Error String

/--
Julia source: base/Enums.jl:10-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Enum{T<:Integer}

The abstract supertype of all enumerated types defined with [`@enum`](@ref).
"""
abstract type Enum{T<:Integer} end
```
-/
structure EnumValue (Tag Base : Type) where
  value : Base

/--
Julia source: base/Enums.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
basetype(::Type{<:Enum{T}}) where {T<:Integer} = T
```
-/
def enumBaseType (baseType : Type) : Type := baseType

/--
Julia source: base/Enums.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::Enum{T2}) where {T<:Integer,T2<:Integer} = T(bitcast(T2, x))::T
```
-/
def convertEnumBase {Tag Source Target Error : Type}
    (bitcast : EnumValue Tag Source → Source) (convert : Source → Except Error Target)
    (x : EnumValue Tag Source) : Except Error Target :=
  convert (bitcast x)

/--
Julia source: base/Enums.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.cconvert(::Type{T}, x::Enum{T2}) where {T<:Integer,T2<:Integer} = T(x)::T
```
-/
def cconvertEnum {Tag Source Target Error : Type}
    (construct : EnumValue Tag Source → Except Error Target)
    (x : EnumValue Tag Source) : Except Error Target :=
  construct x

/--
Julia source: base/Enums.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.write(io::IO, x::Enum{T}) where {T<:Integer} = write(io, T(x))
```
-/
def writeEnum {Tag Base Io Result Error : Type}
    (convert : EnumValue Tag Base → Except Error Base) (write : Io → Base → Except Error Result)
    (io : Io) (x : EnumValue Tag Base) : Except Error Result := do
  let value ← convert x
  write io value

/--
Julia source: base/Enums.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.read(io::IO, ::Type{T}) where {T<:Enum} = T(read(io, basetype(T)))
```
-/
def readEnum {Tag Base Io Error : Type}
    (read : Io → Except Error Base) (construct : Tag → Base → Except Error (EnumValue Tag Base))
    (enumType : Tag) (io : Io) : Except Error (EnumValue Tag Base) := do
  let value ← read io
  construct enumType value

/--
Julia source: base/Enums.jl:24-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    _enum_hash(x::Enum, h::UInt)

Compute hash for an enum value `x`. This internal method will be specialized
for every enum type created through [`@enum`](@ref).
"""
_enum_hash(x::Enum, h::UInt) = invoke(hash, Tuple{Any, UInt}, x, h)
```
-/
def enumHashFallback {Tag Base Error : Type}
    (invokeAnyHash : EnumValue Tag Base → JInt .u64 → Except Error (JInt .u64))
    (x : EnumValue Tag Base) (h : JInt .u64) : Except Error (JInt .u64) :=
  invokeAnyHash x h

/--
Julia source: base/Enums.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.hash(x::Enum, h::UInt) = _enum_hash(x, h)
```
-/
def hashEnum {Tag Base Error : Type}
    (enumHash : EnumValue Tag Base → JInt .u64 → Except Error (JInt .u64))
    (x : EnumValue Tag Base) (h : JInt .u64) : Except Error (JInt .u64) :=
  enumHash x h

/--
Julia source: base/Enums.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.isless(x::T, y::T) where {T<:Enum} = isless(basetype(T)(x), basetype(T)(y))
```
-/
def islessEnum {Tag Base Error : Type}
    (convert : EnumValue Tag Base → Except Error Base) (isless : Base → Base → Except Error Bool)
    (x y : EnumValue Tag Base) : Except Error Bool := do
  let left ← convert x
  let right ← convert y
  isless left right

/--
Julia source: base/Enums.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.Symbol(x::Enum) = namemap(typeof(x))[Integer(x)]::Symbol
```
-/
def enumSymbol {Tag Base Map Sym Error : Type} (ops : EnumNameOps Tag Base Map Sym Error)
    (enumType : Tag) (x : EnumValue Tag Base) : Except Error Sym := do
  let names ← ops.namemap enumType
  ops.getindex names x.value

/--
Julia source: base/Enums.jl:36-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _symbol(x::Enum)
    names = namemap(typeof(x))
    x = Integer(x)
    get(() -> Symbol("<invalid #$x>"), names, x)::Symbol
end
```
-/
def enumSymbolFallback {Tag Base Map Sym Error : Type} (ops : EnumNameOps Tag Base Map Sym Error)
    (enumType : Tag) (x : EnumValue Tag Base) : Except Error Sym := do
  let names ← ops.namemap enumType
  ops.get names x.value (fun _ => do
    let value ← ops.string x.value
    ops.symbol ("<invalid #" ++ value ++ ">"))

/--
Julia source: base/Enums.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::IO, x::Enum) = print(io, _symbol(x))
```
-/
def printEnum {Tag Base Map Sym Io Error : Type} (names : EnumNameOps Tag Base Map Sym Error)
    (printSymbol : Io → Sym → Except Error Unit) (enumType : Tag) (io : Io)
    (x : EnumValue Tag Base) : Except Error Unit := do
  let symbol ← enumSymbolFallback names enumType x
  printSymbol io symbol

/-- The later-loaded `show.jl` callees and the stream's own `print` methods. -/
structure EnumDisplayOps (Tag Base Map Sym Io Mod From Error Mime : Type) where
  names : EnumNameOps Tag Base Map Sym Error
  printString : Io → String → Except Error Unit
  printSymbol : Io → Sym → Except Error Unit
  printMany : Io → List (Io → Except Error Unit) → Except Error Unit
  getCompact : Io → Except Error Bool
  compactContext : Io → Except Error Io
  getModule : Io → From → Except Error From
  mainModule : From
  isNothing : From → Bool
  parentModule : Tag → Mod
  isVisible : Sym → Mod → From → Except Error Bool
  showModule : Io → Mod → Except Error Unit
  showType : Io → Tag → Except Error Unit
  showInteger : Io → Base → Except Error Unit
  isConcrete : Tag → Except Error Bool
  showDatatype : Io → Tag → Except Error Unit
  instances : Tag → Except Error (List (EnumValue Tag Base))
  invokeTypeShow : Io → Mime → Tag → Except Error Unit

/--
Julia source: base/Enums.jl:44-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, x::Enum)
    sym = _symbol(x)
    if !(get(io, :compact, false)::Bool)
        from = get(io, :module, Main)
        def = parentmodule(typeof(x))
        if from === nothing || !Base.isvisible(sym, def, from)
            show(io, def)
            print(io, ".")
        end
    end
    print(io, sym)
end
```
-/
def showEnum {Tag Base Map Sym Io Mod From Error Mime : Type}
    (ops : EnumDisplayOps Tag Base Map Sym Io Mod From Error Mime)
    (enumType : Tag) (io : Io) (x : EnumValue Tag Base) : Except Error Unit := do
  let symbol ← enumSymbolFallback ops.names enumType x
  if ← ops.getCompact io then
    ops.printSymbol io symbol
  else
    let origin ← ops.getModule io ops.mainModule
    let definingModule := ops.parentModule enumType
    if ops.isNothing origin then
      ops.showModule io definingModule
      ops.printString io "."
    else if !(← ops.isVisible symbol definingModule origin) then
      ops.showModule io definingModule
      ops.printString io "."
    ops.printSymbol io symbol

/--
Julia source: base/Enums.jl:57-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ::MIME"text/plain", x::Enum)
    print(io, x, "::")
    show(IOContext(io, :compact => true), typeof(x))
    print(io, " = ")
    show(io, Integer(x))
end
```
-/
def showEnumTextPlain {Tag Base Map Sym Io Mod From Error Mime : Type}
    (ops : EnumDisplayOps Tag Base Map Sym Io Mod From Error Mime)
    (enumType : Tag) (io : Io) (x : EnumValue Tag Base) : Except Error Unit := do
  ops.printMany io [
    fun stream => printEnum ops.names ops.printSymbol enumType stream x,
    fun stream => ops.printString stream "::"
  ]
  let compactStream ← ops.compactContext io
  ops.showType compactStream enumType
  ops.printString io " = "
  ops.showInteger io x.value

/--
Julia source: base/Enums.jl:64-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, m::MIME"text/plain", t::Type{<:Enum})
    if isconcretetype(t)
        print(io, "Enum ")
        Base.show_datatype(io, t)
        print(io, ":")
        for x in instances(t)
            print(io, "\n", Symbol(x), " = ")
            show(io, Integer(x))
        end
    else
        invoke(show, Tuple{IO, MIME"text/plain", Type}, io, m, t)
    end
end
```
-/
def showEnumTypeTextPlain {Tag Base Map Sym Io Mod From Error Mime : Type}
    (ops : EnumDisplayOps Tag Base Map Sym Io Mod From Error Mime)
    (mime : Mime) (enumType : Tag) (io : Io) : Except Error Unit := do
  if ← ops.isConcrete enumType then
    ops.printString io "Enum "
    ops.showDatatype io enumType
    ops.printString io ":"
    let values ← ops.instances enumType
    for value in values do
      let symbol ← enumSymbolFallback ops.names enumType value
      ops.printMany io [
        fun stream => ops.printString stream "\n",
        fun stream => ops.printSymbol stream symbol,
        fun stream => ops.printString stream " = "
      ]
      ops.showInteger io value.value
  else
    ops.invokeTypeShow io mime enumType

structure MembershipOps (L V I Error : Type) where
  extrema : List V → Except Error (V × V)
  length : List V → I
  subtract : V → V → V
  addOne : V → V
  lengthEquals : I → V → Bool
  lengthLessThan20 : I → Bool
  toValue : V → Value L
  setValue : List V → Value L
  emptyFirstError : Error

/--
Julia source: base/Enums.jl:78-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# generate code to test whether expr is in the given set of values
function membershiptest(expr, values)
    lo, hi = extrema(values)
    if length(values) == hi - lo + 1
        :($lo <= $expr <= $hi)
    elseif length(values) < 20
        foldl((x1,x2)->:($x1 || ($expr == $x2)), values[2:end]; init=:($expr == $(values[1])))
    else
        :($expr in $(Set(values)))
    end
end
```
-/
def membershiptest {L V I Error : Type} (ops : MembershipOps L V I Error)
    (expr : Value L) (values : List V) : Except Error (Value L) := do
  let (lo, hi) ← ops.extrema values
  if ops.lengthEquals (ops.length values) (ops.addOne (ops.subtract hi lo)) then
    pure (.expr "comparison" [ops.toValue lo, .symbol "<=", expr, .symbol "<=", ops.toValue hi])
  else if ops.lengthLessThan20 (ops.length values) then
    match values with
    | [] => throw ops.emptyFirstError
    | first :: rest =>
        let equals (value : V) := .expr "call" [.symbol "==", expr, ops.toValue value]
        pure (rest.foldl (fun lhs rhs => .expr "||" [lhs, equals rhs]) (equals first))
  else
    pure (.expr "call" [.symbol "in", expr, ops.setValue values])
/--
Julia source: base/Enums.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.broadcastable(x::Enum) = Ref(x)
```
-/
def broadcastableEnum {Tag Base Ref Error : Type}
    (makeRef : EnumValue Tag Base → Except Error Ref) (x : EnumValue Tag Base) : Except Error Ref :=
  makeRef x

/--
Julia source: base/Enums.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline enum_argument_error(typename, x) = throw(ArgumentError(LazyString("invalid value for Enum ", typename, ": ", x)))
```
-/
def enumArgumentError {Name X Error Result : Type}
    (argumentError : String → Name → String → X → Error) (typename : Name) (x : X) : Except Error Result :=
  .error (argumentError "invalid value for Enum " typename ": " x)

-- `@enum` uses `Core.eval` and emits caller-module types, bindings, and methods from Julia ASTs.
-- UNTRANSLATED
-- Source: base/Enums.jl:95-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @enum EnumName[::BaseType] value1[=x] value2[=y]
-- 
-- Create an `Enum{BaseType}` subtype with name `EnumName` and enum member values of
-- `value1` and `value2` with optional assigned values of `x` and `y`, respectively.
-- `EnumName` can be used just like other types and enum member values as regular values, such as
-- 
-- # Examples
-- ```jldoctest fruitenum
-- julia> @enum Fruit apple=1 orange=2 kiwi=3
-- 
-- julia> f(x::Fruit) = "I'm a Fruit with value: \$(Int(x))"
-- f (generic function with 1 method)
-- 
-- julia> f(apple)
-- "I'm a Fruit with value: 1"
-- 
-- julia> Fruit(1)
-- apple::Fruit = 1
-- ```
-- 
-- Values can also be specified inside a `begin` block, e.g.
-- 
-- ```julia
-- @enum EnumName begin
--     value1
--     value2
-- end
-- ```
-- 
-- `BaseType`, which defaults to [`Int32`](@ref), must be a primitive subtype of `Integer`.
-- Member values can be converted between the enum type and `BaseType`. `read` and `write`
-- perform these conversions automatically. In case the enum is created with a non-default
-- `BaseType`, `Integer(value1)` will return the integer `value1` with the type `BaseType`.
-- 
-- To list all the instances of an enum use `instances`, e.g.
-- 
-- ```jldoctest fruitenum
-- julia> instances(Fruit)
-- (apple, orange, kiwi)
-- ```
-- 
-- It is possible to construct a symbol from an enum instance:
-- 
-- ```jldoctest fruitenum
-- julia> Symbol(apple)
-- :apple
-- ```
-- """
-- macro enum(T::Union{Symbol,Expr}, syms...)
--     if isempty(syms)
--         throw(ArgumentError(LazyString("no arguments given for Enum ", T)))
--     end
--     basetype = Int32
--     typename = T
--     if isa(T, Expr) && T.head === :(::) && length(T.args) == 2 && isa(T.args[1], Symbol)
--         typename = T.args[1]
--         basetype = Core.eval(__module__, T.args[2])
--         if !isa(basetype, DataType) || !(basetype <: Integer) || !isbitstype(basetype)
--             throw(ArgumentError(
--                 LazyString("invalid base type for Enum ", typename, ", ", T, "=::", basetype, "; base type must be an integer primitive type")))
--         end
--     elseif !isa(T, Symbol)
--         throw(ArgumentError(LazyString("invalid type expression for enum ", T)))
--     end
--     values = Vector{basetype}()
--     seen = Set{Symbol}()
--     namemap = Dict{basetype,Symbol}()
--     lo = hi = i = zero(basetype)
--     hasexpr = false
--     docs = Dict{Symbol,Expr}()
-- 
--     if length(syms) == 1 && syms[1] isa Expr && syms[1].head === :block
--         syms = syms[1].args
--     end
--     for s in syms
--         s isa LineNumberNode && continue
--         if isa(s, Expr) && s.head === :macrocall && s.args[1] == GlobalRef(Core, Symbol("@doc"))
--             doc = s
--             s = s.args[4]
--         else
--             doc = nothing
--         end
--         if isa(s, Symbol)
--             if i == typemin(basetype) && !isempty(values)
--                 throw(ArgumentError(LazyString("overflow in value \"", s, "\" of Enum ", typename)))
--             end
--         elseif isa(s, Expr) &&
--                (s.head === :(=) || s.head === :kw) &&
--                length(s.args) == 2 && isa(s.args[1], Symbol)
--             i = Core.eval(__module__, s.args[2]) # allow exprs, e.g. uint128"1"
--             if !isa(i, Integer)
--                 throw(ArgumentError(LazyString("invalid value for Enum ", typename, ", ", s, "; values must be integers")))
--             end
--             i = convert(basetype, i)
--             s = s.args[1]
--             hasexpr = true
--         else
--             throw(ArgumentError(LazyString("invalid argument for Enum ", typename, ": ", s)))
--         end
--         s = s::Symbol
--         if !Base.isidentifier(s)
--             throw(ArgumentError(LazyString("invalid name for Enum ", typename, "; \"", s, "\" is not a valid identifier")))
--         end
--         if hasexpr && haskey(namemap, i)
--             throw(ArgumentError(LazyString("both ", s, " and ", namemap[i], " have value ", i, " in Enum ", typename, "; values must be unique")))
--         end
--         namemap[i] = s
--         push!(values, i)
--         if s in seen
--             throw(ArgumentError(LazyString("name \"", s, "\" in Enum ", typename, " is not unique")))
--         end
--         push!(seen, s)
--         if length(values) == 1
--             lo = hi = i
--         else
--             hi = max(hi, i)
--         end
--         if doc !== nothing
--             docs[s] = doc
--         end
--         i += oneunit(i)
--     end
--     blk = quote
--         # enum definition
--         Base.@__doc__(primitive type $(esc(typename)) <: Enum{$(basetype)} $(Core.bitsizeof(basetype)) end)
--         function $(esc(typename))(x::Integer)
--             $(membershiptest(:x, values)) || enum_argument_error($(Expr(:quote, typename)), x)
--             return bitcast($(esc(typename)), convert($(basetype), x))
--         end
--         Enums.namemap(::Type{$(esc(typename))}) = $(esc(namemap))
--         Base.typemin(x::Type{$(esc(typename))}) = $(esc(typename))($lo)
--         Base.typemax(x::Type{$(esc(typename))}) = $(esc(typename))($hi)
--         let type_hash = hash($(esc(typename)))
--             # Use internal `_enum_hash` to allow users to specialize
--             # `Base.hash` for their own enum types without overwriting the
--             # method we would define here. This avoids a warning for
--             # precompilation.
--             Enums._enum_hash(x::$(esc(typename)), h::UInt) = hash(type_hash, hash(Integer(x), h))
--         end
--         let insts = (Any[ $(esc(typename))(v) for v in $values ]...,)
--             Base.instances(::Type{$(esc(typename))}) = insts
--         end
--     end
--     if isa(typename, Symbol)
--         for (i, sym) in namemap
--             ex = :(const $(esc(sym)) = $(esc(typename))($i))
--             if haskey(docs, sym)
--                 docs[sym].args[4] = ex
--                 ex = docs[sym]
--             end
--             push!(blk.args, ex)
--         end
--     end
--     push!(blk.args, :nothing)
--     blk.head = :toplevel
--     return Base.replace_linenums!(blk, __source__)
-- end
-- /Source

end JuliaLean.base.Enums

namespace JuliaLean.ExprReflect

open JuliaLean

/-! ### `@enum` -/

/-- Bounds of a primitive enum base type. -/
structure EnumBounds where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq, Inhabited

structure EnumMember where
  name : String
  value : Option Int
  deriving Repr, DecidableEq, Inhabited

structure EnumState where
  next : Int
  names : List String
  values : List Int
  lo : Int
  hi : Int
  hasExplicit : Bool
  deriving Repr, DecidableEq, Inhabited

structure EnumResult where
  names : List String
  instances : List Int
  typeminValue : Int
  typemaxValue : Int
  deriving Repr, DecidableEq, Inhabited

def enumConvert (bounds : EnumBounds) (value : Int) : Jl Int :=
  if bounds.lo ≤ value && value ≤ bounds.hi then .ok value
  else .error (.inexactError "@enum")

def enumNext (bounds : EnumBounds) (value : Int) : Int :=
  if value = bounds.hi then bounds.lo else value + 1

/-- The validation and state update after a member's value is known. -/
def enumFinish (bounds : EnumBounds) (state : EnumState) (member : EnumMember)
    (value : Int) (explicit : Bool) : Jl EnumState :=
  let hasExplicit := state.hasExplicit || explicit
  if hasExplicit && state.values.contains value then
    .error (.argumentError "values must be unique")
  else
    let values := state.values ++ [value]
    if state.names.contains member.name then
      .error (.argumentError "name is not unique")
    else
      let first := state.values.isEmpty
      .ok {
        next := enumNext bounds value
        names := state.names ++ [member.name]
        values
        lo := if first then value else state.lo
        hi := if first then value else max state.hi value
        hasExplicit }

/-- One iteration of `@enum`; `base/Enums.jl:170-217`. -/
def enumStep (bounds : EnumBounds) (state : EnumState) (member : EnumMember) : Jl EnumState :=
  match member.value with
  | some raw =>
    match enumConvert bounds raw with
    | .error error => .error error
    | .ok value => enumFinish bounds state member value true
  | none =>
    if state.next = bounds.lo && !state.values.isEmpty then
      .error (.argumentError "overflow in value")
    else enumFinish bounds state member state.next false

def enumLoop (bounds : EnumBounds) : EnumState → List EnumMember → Jl EnumState
  | state, [] => .ok state
  | state, member :: rest =>
    match enumStep bounds state member with
    | .error error => .error error
    | .ok state => enumLoop bounds state rest

/-- `@enum` member assignment and generated extrema/instances;
`base/Enums.jl:144-251`. Identifier validation and `Core.eval` are preconditions
of this integer/member-list model. -/
def enumBuild (bounds : EnumBounds) (members : List EnumMember) : Jl EnumResult :=
  if members.isEmpty then
    .error (.argumentError "no arguments given for Enum")
  else
    match enumLoop bounds {
        next := 0, names := [], values := [], lo := 0, hi := 0, hasExplicit := false } members with
    | .error error => .error error
    | .ok state => .ok {
        names := state.names
        instances := state.values
        typeminValue := state.lo
        typemaxValue := state.hi }

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

def int8Bounds : EnumBounds := ⟨-128, 127⟩

def enumMinimum? : List Int → Option Int
  | [] => none
  | value :: rest => some (rest.foldl min value)

def enumMaximum? : List Int → Option Int
  | [] => none
  | value :: rest => some (rest.foldl max value)

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

structure EnumRuntime where
  names : List (Int × String)
  instances : List Int
  typeHash : Nat
  deriving Repr, DecidableEq, Inhabited

def enumName (definition : EnumRuntime) (value : Int) : String :=
  (definition.names.find? (·.1 == value)).map (·.2) |>.getD ("<invalid #" ++ toString value ++ ">")

def enumContains (definition : EnumRuntime) (value : Int) : Bool :=
  definition.instances.contains value

def enumIsless (left right : Int) : Bool := left < right

def enumBroadcast (value : Int) : List Int := [value]

def enumBaseType (baseType : String) : String := baseType

def enumBitcast (value : Int) : Int := value

def enumWriteRead (value : Int) : Int := enumBitcast value

def enumHashModel (hashType : Nat → Nat → Nat) (hashValue : Int → Nat → Nat)
    (typeHash : Nat) (value : Int) (seed : Nat) : Nat :=
  hashType typeHash (hashValue value seed)

def enumPrintModel (definition : EnumRuntime) (value : Int) : String := enumName definition value

def enumShowModel (definitionModule : String) (visible compact : Bool)
    (definition : EnumRuntime) (value : Int) : String :=
  let renderedPrefix := if compact || visible then "" else definitionModule ++ "."
  renderedPrefix ++ enumName definition value

inductive MembershipStrategy where | interval | disjunction | set
  deriving Repr, DecidableEq, Inhabited

def membershipStrategy (values : List Int) : MembershipStrategy :=
  match values with
  | [] => .disjunction
  | [_] => .interval
  | _ :: _ =>
    let lo := values.foldl min values.head!
    let hi := values.foldl max values.head!
    if values.length = (hi - lo + 1).toNat then .interval
    else if values.length < 20 then .disjunction else .set

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

structure EnumBox where
  base : IntTy
  value : Int
  deriving Repr, DecidableEq, Inhabited

def enumBoxInRange (box : EnumBox) : Bool :=
  box.base.min ≤ box.value && box.value ≤ box.base.max

/-- `basetype(::Type{<:Enum{T}})`; `base/Enums.jl:17`. -/

def enumRow17 (base : IntTy) : IntTy := base

def enumRow19 (target : IntTy) (x : EnumBox) : Jl Int := do
  match JInt.convert (target.name) target x.value with
  | .error error => .error error
  | .ok value => .ok value.val

def enumRow20 (target : IntTy) (x : EnumBox) : Jl Int := enumRow19 target x

def enumRow21 (writer : Int → Nat) (x : EnumBox) : Jl Nat := do
  match enumRow19 x.base x with
  | .error error => .error error
  | .ok value => .ok (writer value)

def enumConstruct (base : IntTy) (validValues : List Int) (value : Int) : Jl EnumBox := do
  if !validValues.contains value then .error (.argumentError "invalid value for Enum")
  else match JInt.convert (base.name) base value with
    | .error error => .error error
    | .ok converted => .ok ⟨base, converted.val⟩

/-- `Base.read(io, ::Type{T}) where T<:Enum`; `base/Enums.jl:22`. -/

def enumRow22 (reader : IntTy → Int) (base : IntTy) (validValues : List Int) : Jl EnumBox :=
  enumConstruct base validValues (reader base)

def enumRow30 (genericHash : EnumBox → Nat → Nat) (x : EnumBox) (seed : Nat) : Nat :=
  genericHash x seed

def enumRow31 (specializedHash : EnumBox → Nat → Nat) (x : EnumBox) (seed : Nat) : Nat :=
  specializedHash x seed

def enumRow32 (x y : EnumBox) : Bool := x.value < y.value

def enumNameLookup (names : List (Int × String)) (value : Int) : Option String :=
  (names.find? (·.1 == value)).map (·.2)

/-- `Base.Symbol(x::Enum)`; `base/Enums.jl:34`. -/

inductive EnumNameResult where
  | ok (name : String)
  | keyError (value : Int)
  deriving Repr, DecidableEq, Inhabited

def enumRow34 (names : List (Int × String)) (x : EnumBox) : EnumNameResult :=
  match enumNameLookup names x.value with
  | some name => .ok name
  | none => .keyError x.value

def enumRow36 (names : List (Int × String)) (x : EnumBox) : String :=
  (enumNameLookup names x.value).getD ("<invalid #" ++ toString x.value ++ ">")

def enumRow42 (names : List (Int × String)) (x : EnumBox) : String := enumRow36 names x

def enumRow44 (names : List (Int × String)) (definitionModule : String)
    (compact visible : Bool) (x : EnumBox) : String :=
  let renderedPrefix := if compact then "" else if visible then "" else definitionModule ++ "."
  renderedPrefix ++ enumRow36 names x

def enumRow57 (names : List (Int × String)) (typeName : String) (x : EnumBox) : String :=
  enumRow42 names x ++ "::" ++ typeName ++ " = " ++ toString x.value

def enumRow64 (concrete : Bool) (typeName : String) (names : List (Int × String)) : List String :=
  if concrete then ("Enum " ++ typeName ++ ":") :: names.map (fun pair => pair.2 ++ " = " ++ toString pair.1)
  else ["invoke(show, Type)"]

inductive EnumMembershipExpr where
  | interval (lo hi : Int)
  | disjunction (values : List Int)
  | setMembership (values : List Int)
  deriving Repr, DecidableEq, Inhabited

/-- `membershiptest(expr, values)`; `base/Enums.jl:79-88`. -/

def enumRow79 (base : IntTy) (values : List Int) : Jl EnumMembershipExpr :=
  match values with
  | [] => .error (.argumentError "extrema of empty enum values")
  | [value] => .ok (.interval value value)
  | first :: rest =>
    let lo := rest.foldl min first
    let hi := rest.foldl max first
    let span := wrapInt base (hi - lo + 1)
    if (values.length : Int) = span then .ok (.interval lo hi)
    else if values.length < 20 then .ok (.disjunction values) else .ok (.setMembership values)

def enumRow91 (x : EnumBox) : List EnumBox := [x]

def enumRow93 (typeName : String) (value : Int) : Jl Unit :=
  .error (.argumentError ("invalid value for Enum " ++ typeName ++ ": " ++ toString value))

inductive RawEnumMember where
  | line
  | implicit (name : String) (validIdentifier : Bool)
  | explicit (name : String) (validIdentifier : Bool) (value : Int)
  | documented (member : RawEnumMember)
  | invalid
  deriving Repr, DecidableEq, Inhabited

def prepareEnumMembers : List RawEnumMember → Jl (List EnumMember)
  | [] => .ok []
  | .line :: rest => prepareEnumMembers rest
  | .documented member :: rest => prepareEnumMembers (member :: rest)
  | .implicit name valid :: rest =>
    if !valid then .error (.argumentError "invalid enum identifier")
    else return ⟨name, none⟩ :: (← prepareEnumMembers rest)
  | .explicit name valid value :: rest =>
    if !valid then .error (.argumentError "invalid enum identifier")
    else return ⟨name, some value⟩ :: (← prepareEnumMembers rest)
  | .invalid :: _ => .error (.argumentError "invalid enum argument")

structure EnumMacroRequest where
  typeExpressionValid : Bool
  baseTypeValid : Bool
  rawMembers : List RawEnumMember
  deriving Repr, DecidableEq, Inhabited

/-- `@enum`; `base/Enums.jl:144-252`. -/

def enumRow144 (bounds : EnumBounds) (request : EnumMacroRequest) : Jl EnumResult :=
  if request.rawMembers.isEmpty then .error (.argumentError "no arguments given for Enum")
  else if !request.typeExpressionValid then .error (.argumentError "invalid type expression for enum")
  else if !request.baseTypeValid then .error (.argumentError "invalid base type for Enum")
  else match prepareEnumMembers request.rawMembers with
    | .error error => .error error
    | .ok members => enumBuild bounds members

def enumRow221 (base : IntTy) (values : List Int) (input : Int) : Jl EnumBox :=
  enumConstruct base values input

def enumRow225 (names : List (Int × String)) : List (Int × String) := names

def enumRow226 (result : EnumResult) : Int := result.typeminValue

def enumRow227 (result : EnumResult) : Int := result.typemaxValue

def enumRow233 (hashType : Nat → Nat → Nat) (hashValue : Int → Nat → Nat)
    (typeHash : Nat) (x : EnumBox) (seed : Nat) : Nat :=
  hashType typeHash (hashValue x.value seed)

def enumRow236 (result : EnumResult) : List Int := result.instances

end JuliaLean.ExprReflect
