import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.tuple

/-!
# Model of `base/namedtuple.jl`

The model keeps field names, declared field types, and existentially typed values separate. Julia
Core operations and functions from other Base files appear as typed parameters where this file only
calls them.
-/
namespace JuliaLean.base.namedtuple

open JuliaLean

inductive NTError where
  | argumentError (message : String)
  | errorException
  | fieldError (name : String)
  | boundsError
  | typeError (message : String)
  | methodError (name : String)
  | conversionError (name : String)
  deriving Repr, DecidableEq, Inhabited

universe u
abbrev Result (α : Type u) : Type u := Except NTError α

inductive TypeTag where
  | any
  | named (name : String)
  | tuple (fields : List TypeTag)
  | namedTuple (names : List String) (fields : List TypeTag)
  deriving Repr, Inhabited

inductive Value : Type 1 where
  | box {α : Type} (value : α) : Value

structure NTType where
  names : List String
  fieldTypes : List TypeTag
  deriving Repr, Inhabited

structure ModelNT where
  type : NTType
  values : List Value

inductive Key where
  | symbol (name : String)
  | nativeInteger (index : Int)
  | integer (index : Int)
  | other
  deriving Repr, DecidableEq, Inhabited

structure KV where
  key : Key
  value : Value

abbrev Pair := String × Value
def setAt {α : Type u} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: rest, 0, value => value :: rest
  | first :: rest, index + 1, value => first :: setAt rest index value

def pairFieldsLoop : List KV → List String → List Value → Result (List String × List Value)
  | [], names, values => .ok (names, values)
  | pair :: rest, names, values =>
      match pair.key with
      | .symbol name =>
          if names.contains name then
            pairFieldsLoop rest names (setAt values (names.idxOf name) pair.value)
          else
            pairFieldsLoop rest (names ++ [name]) (values ++ [pair.value])
      | _ => .error (.typeError "named tuple keys must be Symbols")

def pairFields (pairs : List KV) : Result (List String × List Value) :=
  pairFieldsLoop pairs [] []

def fieldType (t : NTType) (name : String) : TypeTag :=
  t.fieldTypes.getD (t.names.idxOf name) .any

def getfield (nt : ModelNT) (name : String) : Result Value :=
  match nt.values[(nt.type.names.idxOf name)]? with
  | some value => .ok value
  | none => .error (.fieldError name)

def getfieldIndex (nt : ModelNT) (index : Int) : Result Value :=
  if index ≤ 0 then .error .boundsError
  else match nt.values[(index - 1).toNat]? with
    | some value => .ok value
    | none => .error .boundsError

def newNamedTuple (t : NTType) (args : List Value) : ModelNT := ⟨t, args⟩

def namedTupleFromNames (nt : ModelNT) (names : List String) : Result ModelNT := do
  if !decide names.Nodup then throw .errorException
  let values ← names.mapM (getfield nt)
  let types := names.map (fieldType nt.type)
  pure (newNamedTuple ⟨names, types⟩ values)

def convertTupleFields (convert : TypeTag → Value → Result Value)
    (types : List TypeTag) (values : List Value) : Result (List Value) :=
  (types.zip values).mapM (fun (ty, value) => convert ty value)

/--
Julia source: base/namedtuple.jl:115-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function (NT::Type{NamedTuple{names,T}})(args::Tuple) where {names, T <: Tuple}
    if length(args) != length(names::Tuple)
        throw(ArgumentError("Wrong number of arguments to named tuple constructor."))
    end
    # Note T(args) might not return something of type T; e.g.
    # Tuple{Type{Float64}}((Float64,)) returns a Tuple{DataType}
    $(Expr(:splatnew, :NT, :(T(args))))
end
```
-/
def constructTyped (convert : TypeTag → Value → Result Value) (target : NTType)
    (args : List Value) : Result ModelNT := do
  if args.length != target.names.length then
    throw (.argumentError "Wrong number of arguments to named tuple constructor.")
  let values ← convertTupleFields convert target.fieldTypes args
  pure (newNamedTuple target values)

/--
Julia source: base/namedtuple.jl:124-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (NT::Type{NamedTuple{names, T}})(nt::NamedTuple) where {names, T <: Tuple}
    if @generated
        Expr(:new, :NT,
             Any[ :(let Tn = fieldtype(NT, $n),
                      ntn = getfield(nt, $(QuoteNode(names[n])))
                      ntn isa Tn ? ntn : convert(Tn, ntn)
                  end) for n in 1:length(names) ]...)
    else
        NT(map(Fix1(getfield, nt), names))
    end
end
```
-/
def constructFromNamedTuple (generated : Bool) (convert : TypeTag → Value → Result Value)
    (isA : Value → TypeTag → Bool) (target : NTType) (nt : ModelNT) : Result ModelNT := do
  if generated then
    let values ← target.names.mapM fun name => do
      let value ← getfield nt name
      let ty := fieldType target name
      if isA value ty then pure value else convert ty value
    pure (newNamedTuple target values)
  else
    let args ← target.names.mapM (getfield nt)
    constructTyped convert target args

/--
Julia source: base/namedtuple.jl:136-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function NamedTuple{names}(nt::NamedTuple) where {names}
    if @generated
        idx = Int[ fieldindex(nt, names[n]) for n in 1:length(names::Tuple) ]
        types = Tuple{(fieldtype(nt, idx[n]) for n in 1:length(idx))...}
        Expr(:new, :(NamedTuple{names, $types}), Any[ :(getfield(nt, $(idx[n]))) for n in 1:length(idx) ]...)
    else
        length_names = length(names::Tuple)
        types = Tuple{(fieldtype(typeof(nt), names[n]) for n in 1:length_names)...}
        _new_NamedTuple(NamedTuple{names, types}, map(Fix1(getfield, nt), names))
    end
end
```
-/
def constructNamesFromNamedTuple (generated : Bool) (nt : ModelNT) (names : List String)
    : Result ModelNT := do
  if generated then
    let indices := names.map (fun name => nt.type.names.idxOf name)
    let types := indices.map (fun index => nt.type.fieldTypes.getD index .any)
    let values ← names.mapM (getfield nt)
    pure (newNamedTuple ⟨names, types⟩ values)
  else
    let lengthNames := names.length
    let types := (List.range lengthNames).map (fun i => fieldType nt.type (names.getD i ""))
    let values ← names.mapM (getfield nt)
    pure (newNamedTuple ⟨names, types⟩ values)

/--
Julia source: base/namedtuple.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(NT::Type{NamedTuple{names, T}})(itr) where {names, T <: Tuple} = NT(T(itr))
```
-/
def constructTypedFromIterator {I : Type u} (toValues : I → Result (List Value))
    (convert : TypeTag → Value → Result Value) (target : NTType) (itr : I) : Result ModelNT := do
  let values ← toValues itr
  let converted ← convertTupleFields convert target.fieldTypes values
  constructTyped convert target converted

/--
Julia source: base/namedtuple.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(NT::Type{NamedTuple{names}})(itr) where {names} = NT(Tuple(itr))
```
-/
def constructNamesFromIterator {I : Type u} (toValues : I → Result (List Value))
    (fromTuple : NTType → List Value → Result ModelNT) (typeofValue : Value → TypeTag)
    (names : List String) (itr : I) : Result ModelNT := do
  let values ← toValues itr
  fromTuple ⟨names, values.map typeofValue⟩ values

/--
Julia source: base/namedtuple.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
NamedTuple(itr) = (; itr...)
```
-/
def namedTupleFromIterator {I : Type u} (toPairs : I → Result (List KV))
    (fromTuple : NTType → List Value → Result ModelNT) (typeofValue : Value → TypeTag)
    (itr : I) : Result ModelNT := do
  let pairs ← toPairs itr
  let (names, values) ← pairFields pairs
  fromTuple ⟨names, values.map typeofValue⟩ values

/--
Julia source: base/namedtuple.jl:155-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function _new_NamedTuple(T::Type{NamedTuple{NTN, NTT}} where {NTN, NTT}, args::Tuple)
    $(Expr(:splatnew, :T, :args))
end
```
-/
def new_NamedTuple (t : NTType) (args : List Value) : ModelNT := newNamedTuple t args

/--
Julia source: base/namedtuple.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::NamedTuple) = nfields(t)
```
-/
def length (nfields : ModelNT → JInt .i64) (t : ModelNT) : JInt .i64 := nfields t

/--
Julia source: base/namedtuple.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(t::NamedTuple, iter=1) = iter > nfields(t) ? nothing : (getfield(t, iter), iter + 1)
```
-/
def iterate {I : Type u} (nfields : ModelNT → JInt .i64)
    (greater : I → JInt .i64 → Bool) (getfieldAt : ModelNT → I → Result Value)
    (increment : I → I) (one : I) (t : ModelNT) (iter : I := one) :
    Option (Result (Value × I)) :=
  if greater iter (nfields t) then none
  else some ((getfieldAt t iter).map (fun value => (value, increment iter)))

/--
Julia source: base/namedtuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(t::NamedTuple) = t
```
-/
def restAll (t : ModelNT) : ModelNT := t

/--
Julia source: base/namedtuple.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline rest(t::NamedTuple{names}, i) where {names} = NamedTuple{rest(names,i::Int)}(t)
```
-/
def restAfter (namesAfter : List String → Int → Result (List String)) (t : ModelNT)
    (i : JInt .i64) : Result ModelNT :=
  match namesAfter t.type.names i.val with
  | .error e => .error e
  | .ok names => constructNamesFromNamedTuple false t names

/--
Julia source: base/namedtuple.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(t::NamedTuple) = 1
```
-/
def firstindex (_t : ModelNT) : JInt .i64 := JuliaLean.base.int.lit .i64 1

/--
Julia source: base/namedtuple.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(t::NamedTuple) = nfields(t)
```
-/
def lastindex (nfields : ModelNT → JInt .i64) (t : ModelNT) : JInt .i64 := nfields t

/--
Julia source: base/namedtuple.jl:165-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::NamedTuple, i::Int) = getfield(t, i)
```
-/
def getindexInt (t : ModelNT) (i : JInt .i64) : Result Value := getfieldIndex t i.val

/--
Julia source: base/namedtuple.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::NamedTuple, i::Symbol) = getfield(t, i)
```
-/
def getindexSymbol (t : ModelNT) (i : String) : Result Value := getfield t i

/--
Julia source: base/namedtuple.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::NamedTuple, ::Colon) = t
```
-/
def getindexColon (t : ModelNT) : ModelNT := t

/--
Julia source: base/namedtuple.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline getindex(t::NamedTuple, idxs::Tuple{Vararg{Symbol}}) = NamedTuple{idxs}(t)
```
-/
def getindexSymbols (generated : Bool) (t : ModelNT) (idxs : List String) : Result ModelNT :=
  constructNamesFromNamedTuple generated t idxs

/--
Julia source: base/namedtuple.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline getindex(t::NamedTuple, idxs::AbstractVector{Symbol}) = NamedTuple{Tuple(idxs)}(t)
```
-/
def getindexSymbolVector (generated : Bool) (t : ModelNT) (idxs : List String) : Result ModelNT :=
  constructNamesFromNamedTuple generated t idxs

/--
Julia source: base/namedtuple.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexed_iterate(t::NamedTuple, i::Int, state=1) = (getfield(t, i), i+1)
```
-/
def indexed_iterate (t : ModelNT) (i : JInt .i64)
    (_state : JInt .i64 := JuliaLean.base.int.lit .i64 1) : Result (Value × JInt .i64) := do
  let value ← getfieldIndex t i.val
  pure (value, JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1))

/--
Julia source: base/namedtuple.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(::NamedTuple{()}) = true
```
-/
def isEmptyEmpty (_t : ModelNT) : Bool := true

/--
Julia source: base/namedtuple.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(::NamedTuple) = false
```
-/
def isEmptyNamedTuple (_t : ModelNT) : Bool := false

/--
Julia source: base/namedtuple.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(::NamedTuple) = NamedTuple()
```
-/
def emptyNamedTuple : ModelNT := newNamedTuple ⟨[], []⟩ []

/--
Julia source: base/namedtuple.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(@nospecialize(t::NamedTuple), i::Integer) = Int(i)-1
```
-/
def prevind {I : Type} (_t : ModelNT) (convertInt : I → Result (JInt .i64)) (i : I) : Result (JInt .i64) := do
  let i ← convertInt i
  pure (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 1))

/--
Julia source: base/namedtuple.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(@nospecialize(t::NamedTuple), i::Integer) = Int(i)+1
```
-/
def nextind {I : Type} (_t : ModelNT) (convertInt : I → Result (JInt .i64)) (i : I) : Result (JInt .i64) := do
  let i ← convertInt i
  pure (JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1))

/--
Julia source: base/namedtuple.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{NT}, nt::NT) where {names, NT<:NamedTuple{names}} = nt
```
-/
def convertSameNames {NT : Type} (_target : NT) (nt : NT) : NT := nt

/--
Julia source: base/namedtuple.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{NT}, nt::NT) where {names, T<:Tuple, NT<:NamedTuple{names,T}} = nt
```
-/
def convertSameConcreteType {NT : Type} (_target : NT) (nt : NT) : NT := nt

/--
Julia source: base/namedtuple.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{NT}, t::Tuple) where {NT<:NamedTuple} = (@inline NT(t))::NT
```
-/
def convertTupleToNamedTuple (convert : TypeTag → Value → Result Value) (target : NTType)
    (values : List Value) : Result ModelNT := constructTyped convert target values

/--
Julia source: base/namedtuple.jl:182-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{NamedTuple{names,T}}, nt::NamedTuple{names}) where {names,T<:Tuple}
    NT = NamedTuple{names,T}
    (@inline NT(nt))::NT
end
```
-/
def convertMatchingNames (generated : Bool) (convert : TypeTag → Value → Result Value)
    (isA : Value → TypeTag → Bool) (target : NTType) (nt : ModelNT) : Result ModelNT :=
  constructFromNamedTuple generated convert isA target nt

/--
Julia source: base/namedtuple.jl:187-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{NT}, nt::NamedTuple{names}) where {names, NT<:NamedTuple{names}}
    # converting abstract NT to an abstract Tuple type, to a concrete NT1, is not straightforward, so this could just be an error, but we define it anyway
    # _tuple_error(NT, nt)
    T1 = Tuple{ntuple(i -> fieldtype(NT, i), Val(length(names)))...}
    NT1 = NamedTuple{names, T1}
    return NT1(T1(nt))::NT1::NT
end
```
-/
def convertAbstractTarget (convert : TypeTag → Value → Result Value) (target : NTType)
    (nt : ModelNT) : Result ModelNT := do
  let types := (List.range target.names.length).map (fun i => target.fieldTypes.getD i .any)
  let values ← convertTupleFields convert types nt.values
  constructTyped convert ⟨target.names, types⟩ values

/--
Julia source: base/namedtuple.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Tuple(nt::NamedTuple) = (nt...,)
```
-/
def Tuple (nt : ModelNT) : List Value := nt.values

/--
Julia source: base/namedtuple.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(nt::NamedTuple) where {T <: Tuple} = (t = Tuple(nt); t isa T ? t : convert(T, t)::T)
```
-/
def convertToTuple (isT : List Value → Bool) (convert : List Value → Result (List Value))
    (nt : ModelNT) : Result (List Value) := do
  let t := Tuple nt
  if isT t then pure t else convert t
/-- Operations supplied by Base's general display machinery. -/
structure ShowOps where
  nfields : ModelNT → JInt .i64
  typeOfValue : Value → TypeTag
  typeOfTuple : ModelNT → TypeTag
  fieldTypeAt : TypeTag → Nat → TypeTag
  sameType : TypeTag → TypeTag → Bool
  concrete : TypeTag → Bool
  showType : TypeTag → List String
  showTuple : List Value → List String
  typeinfo : TypeTag
  isNamedTupleSubtype : TypeTag → Bool
  fieldName : ModelNT → Nat → String
  showSymbol : String → List String
  showValue : TypeTag → Value → List String

def showScan (ops : ShowOps) (nt : ModelNT) : List Nat → Result Bool
  | [] => .ok true
  | i :: rest =>
      match getfieldIndex nt (Int.ofNat i) with
      | .error e => .error e
      | .ok value =>
          if ops.sameType (ops.typeOfValue value) (ops.fieldTypeAt (ops.typeOfTuple nt) i) then
            showScan ops nt rest
          else
            .ok false
def showFields (ops : ShowOps) (nt : ModelNT) (n : Nat) : List Nat → Result (List String)
  | [] => .ok []
  | i :: rest =>
      match getfieldIndex nt (Int.ofNat i) with
      | .error e => .error e
      | .ok value =>
          let typeinfo :=
            if ops.isNamedTupleSubtype ops.typeinfo then ops.fieldTypeAt ops.typeinfo i else .any
          let separator := if n == 1 then [","] else if i < n then [", "] else []
          match showFields ops nt n rest with
          | .error e => .error e
          | .ok later =>
              .ok (ops.showSymbol (ops.fieldName nt i) ++ [" = "] ++
                ops.showValue typeinfo value ++ separator ++ later)

/--
Julia source: base/namedtuple.jl:198-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, t::NamedTuple)
    n = nfields(t)
    for i = 1:n
        # if field types aren't concrete, show full type
        if typeof(getfield(t, i)) !== fieldtype(typeof(t), i)
            show(io, typeof(t))
            print(io, "(")
            show(io, Tuple(t))
            print(io, ")")
            return
        end
    end
    if n == 0
        print(io, "NamedTuple()")
    else
        typeinfo = get(io, :typeinfo, Any)
        print(io, "(")
        for i = 1:n
            show_sym(io, fieldname(typeof(t), i))
            print(io, " = ")
            show(IOContext(io, :typeinfo =>
                           t isa typeinfo <: NamedTuple ? fieldtype(typeinfo, i) : Any),
                 getfield(t, i))
            if n == 1
                print(io, ",")
            elseif i < n
                print(io, ", ")
            end
        end
        print(io, ")")
    end
end
```
-/
def showNamedTuple (ops : ShowOps) (t : ModelNT) : Result (List String) := do
  let n := (ops.nfields t).val.toNat
  let indices := (List.range n).map (· + 1)
  let allConcrete ← showScan ops t indices
  if !allConcrete then
    pure (ops.showType (ops.typeOfTuple t) ++ ["("] ++ ops.showTuple (Tuple t) ++ [")"])
  else if n == 0 then
    pure ["NamedTuple()"]
  else
    let fields ← showFields ops t n indices
    pure (["("] ++ fields ++ [")"])

/--
Julia source: base/namedtuple.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{T}) where T<:NamedTuple = nteltype(T)
```
-/
def eltypeNamedTuple (nteltype : TypeTag → TypeTag) (t : TypeTag) : TypeTag := nteltype t

/--
Julia source: base/namedtuple.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nteltype(::Type) = Any
```
-/
def nteltypeFallback (_t : TypeTag) : TypeTag := .any

/--
Julia source: base/namedtuple.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nteltype(::Type{NamedTuple{names,T}} where names) where {T} = eltype(T)
```
-/
def nteltypeNamedTuple (eltype : TypeTag → TypeTag) (tupleType : TypeTag) : TypeTag :=
  eltype tupleType

def nteltypeDispatch (eltype : TypeTag → TypeTag) (t : TypeTag) : TypeTag :=
  match t with
  | .namedTuple _ fields => nteltypeNamedTuple eltype (.tuple fields)
  | _ => nteltypeFallback t

/--
Julia source: base/namedtuple.jl:235-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(@nospecialize nt::NamedTuple) = keytype(typeof(nt))
```
-/
def keytypeValue (keytype : TypeTag → TypeTag) (nt : ModelNT) : TypeTag :=
  keytype (.namedTuple nt.type.names nt.type.fieldTypes)

/--
Julia source: base/namedtuple.jl:236-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(@nospecialize T::Type{<:NamedTuple}) = Symbol
```
-/
def keytypeType (_t : TypeTag) : TypeTag := .named "Symbol"

/--
Julia source: base/namedtuple.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(@nospecialize nt::NamedTuple) = valtype(typeof(nt))
```
-/
def valtypeValue (valtype : TypeTag → TypeTag) (nt : ModelNT) : TypeTag :=
  valtype (.namedTuple nt.type.names nt.type.fieldTypes)

/--
Julia source: base/namedtuple.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(@nospecialize T::Type{<:NamedTuple}) = eltype(T)
```
-/
def valtypeType (eltype : TypeTag → TypeTag) (t : TypeTag) : TypeTag :=
  match t with
  | .namedTuple _ fields => eltype (.tuple fields)
  | _ => .any

/--
Julia source: base/namedtuple.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::NamedTuple{n}, b::NamedTuple{n}) where {n} = Tuple(a) == Tuple(b)
```
-/
def equalSameNames (equalTuples : List Value → List Value → Bool)
    (a b : ModelNT) : Bool := equalTuples (Tuple a) (Tuple b)

/--
Julia source: base/namedtuple.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::NamedTuple, b::NamedTuple) = false
```
-/
def equalDifferentNames (_a _b : ModelNT) : Bool := false

/--
Julia source: base/namedtuple.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(a::NamedTuple{n}, b::NamedTuple{n}) where {n} = isequal(Tuple(a), Tuple(b))
```
-/
def isequalSameNames (isequalTuples : List Value → List Value → Bool)
    (a b : ModelNT) : Bool := isequalTuples (Tuple a) (Tuple b)

/--
Julia source: base/namedtuple.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(a::NamedTuple, b::NamedTuple) = false
```
-/
def isequalDifferentNames (_a _b : ModelNT) : Bool := false

/--
Julia source: base/namedtuple.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nt_names(::NamedTuple{names}) where {names} = names
```
-/
def nt_namesValue (nt : ModelNT) : List String := nt.type.names

/--
Julia source: base/namedtuple.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nt_names(::Type{T}) where {names,T<:NamedTuple{names}} = names
```
-/
def nt_namesType (t : NTType) : List String := t.names

/--
Julia source: base/namedtuple.jl:250-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::NamedTuple, h::UInt) = xor(objectid(_nt_names(x)), hash(Tuple(x), h))
```
-/
def hashNamedTuple (objectid : List String → Nat) (hash : List Value → Nat → Nat)
    (xor : Nat → Nat → Nat) (x : ModelNT) (h : Nat) : Nat :=
  xor (objectid (nt_namesValue x)) (hash (Tuple x) h)

/--
Julia source: base/namedtuple.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<)(a::NamedTuple{n}, b::NamedTuple{n}) where {n} = Tuple(a) < Tuple(b)
```
-/
def lessSameNames (lessTuples : List Value → List Value → Result Bool)
    (a b : ModelNT) : Result Bool := lessTuples (Tuple a) (Tuple b)

/--
Julia source: base/namedtuple.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::NamedTuple{n}, b::NamedTuple{n}) where {n} = isless(Tuple(a), Tuple(b))
```
-/
def islessSameNames (lessTuples : List Value → List Value → Result Bool)
    (a b : ModelNT) : Result Bool := lessTuples (Tuple a) (Tuple b)

/--
Julia source: base/namedtuple.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
same_names(::NamedTuple{names}...) where {names} = true
```
-/
def same_namesSpecialized (_nts : List ModelNT) : Bool := true

/--
Julia source: base/namedtuple.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
same_names(::NamedTuple...) = false
```
-/
def same_namesFallback (_nts : List ModelNT) : Bool := false

def sameNamesDispatch (nt : ModelNT) (nts : List ModelNT) : Bool :=
  if nts.all (fun other => other.type.names == nt.type.names) then
    same_namesSpecialized (nt :: nts)
  else
    same_namesFallback (nt :: nts)

/--
Julia source: base/namedtuple.jl:259-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f::F, nt::NamedTuple{names}, nts::NamedTuple...) where {names, F}
    if !same_names(nt, nts...)
        throw(ArgumentError("Named tuple names do not match."))
    end
    NamedTuple{names}(map(f, map(Tuple, (nt, nts...))...))
end
```
-/
def mapNamed (mapValues : (List Value → Value) → List (List Value) → List Value)
    (fromTuple : NTType → List Value → Result ModelNT) (typeofValue : Value → TypeTag)
    (f : List Value → Value) (nt : ModelNT) (nts : List ModelNT) : Result ModelNT := do
  if !sameNamesDispatch nt nts then
    throw (.argumentError "Named tuple names do not match.")
  let values := mapValues f ((nt :: nts).map Tuple)
  constructNamesFromIterator (fun (xs : List Value) => (Except.ok xs : Result (List Value)))
    fromTuple typeofValue nt.type.names values

/--
Julia source: base/namedtuple.jl:266-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter(f, xs::NamedTuple) = xs[filter(k -> f(xs[k]), keys(xs))]
```
-/
def filterNamed (keys : ModelNT → List String) (generated : Bool) (f : Value → Bool)
    (xs : ModelNT) : Result ModelNT :=
  let names := keys xs
  let selected := names.filter fun key =>
    match getfield xs key with
    | .ok value => f value
    | .error _ => false
  getindexSymbolVector generated xs selected

/--
Julia source: base/namedtuple.jl:268-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge_names(an::Tuple{Vararg{Symbol}}, bn::Tuple{Vararg{Symbol}})
    @nospecialize
    @_total_meta
    names = Symbol[an...]
    for n in bn
        if !sym_in(n, an)
            push!(names, n)
        end
    end
    (names...,)
end
```
-/
def merge_names (an bn : List String) : List String :=
  an ++ bn.filter (fun name => !an.contains name)

/--
Julia source: base/namedtuple.jl:280-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge_types(names::Tuple{Vararg{Symbol}}, a::Type{<:NamedTuple}, b::Type{<:NamedTuple})
    @nospecialize
    @_total_meta
    bn = _nt_names(b)
    return Tuple{Any[ fieldtype(sym_in(names[n], bn) ? b : a, names[n]) for n in 1:length(names) ]...}
end
```
-/
def merge_types (names : List String) (a b : NTType) : List TypeTag :=
  let bn := nt_namesType b
  names.map (fun name => fieldType (if bn.contains name then b else a) name)

def mergeValuesLoop (bn : List String) (a b : ModelNT) : List String → Result (List Value)
  | [] => .ok []
  | name :: rest => do
      let value ← getfield (if bn.contains name then b else a) name
      let later ← mergeValuesLoop bn a b rest
      pure (value :: later)

/--
Julia source: base/namedtuple.jl:287-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge_fallback(a::NamedTuple, b::NamedTuple,
                        an::Tuple{Vararg{Symbol}}, bn::Tuple{Vararg{Symbol}})
    @nospecialize
    @_foldable_meta
    names = merge_names(an, bn)
    types = merge_types(names, typeof(a), typeof(b))
    n = length(names)
    A = Memory{Any}(undef, n)
    for i=1:n
        n = names[i]
        A[i] = getfield(sym_in(n, bn) ? b : a, n)
    end
    _new_NamedTuple(NamedTuple{names, types}, (A...,))
end
```
-/
def merge_fallback (a b : ModelNT) (an bn : List String) : Result ModelNT := do
  let names := merge_names an bn
  let types := merge_types names a.type b.type
  let values ← mergeValuesLoop bn a b names
  pure (new_NamedTuple ⟨names, types⟩ values)

/-- The tuple-type constructor supplied by Julia Core. -/
def tupleToNamedTuple (target : NTType) (values : List Value) : Result ModelNT :=
  if target.names.Nodup then .ok (newNamedTuple target values) else .error .errorException

/--
Julia source: base/namedtuple.jl:331-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge(a::NamedTuple{an}, b::NamedTuple{bn}) where {an, bn}
    if @generated
        names = merge_names(an, bn)
        types = merge_types(names, a, b)
        vals = Any[ :(getfield($(sym_in(names[n], bn) ? :b : :a), $(QuoteNode(names[n])))) for n in 1:length(names) ]
        :( _new_NamedTuple(NamedTuple{$names,$types}, ($(vals...),)) )
    else
        merge_fallback(a, b, an, bn)
    end
end
```
-/
def mergeNamed (generated : Bool) (a b : ModelNT) : Result ModelNT := do
  let an := a.type.names
  let bn := b.type.names
  if generated then
    let names := merge_names an bn
    let types := merge_types names a.type b.type
    let values ← mergeValuesLoop bn a b names
    pure (new_NamedTuple ⟨names, types⟩ values)
  else
    merge_fallback a b an bn

/--
Julia source: base/namedtuple.jl:342-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple,     b::NamedTuple{()}) = a
```
-/
def mergeEmptyRight (a b : ModelNT) (_emptyNames : b.type.names = []) : ModelNT := a

/--
Julia source: base/namedtuple.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple{()}, b::NamedTuple{()}) = a
```
-/
def mergeEmptyBoth (a b : ModelNT) (_emptyA : a.type.names = []) (_emptyB : b.type.names = []) : ModelNT := a

/--
Julia source: base/namedtuple.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple{()}, b::NamedTuple)     = b
```
-/
def mergeEmptyLeft (a b : ModelNT) (_emptyA : a.type.names = []) : ModelNT := b

/--
Julia source: base/namedtuple.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple, b::Iterators.Pairs{<:Any,<:Any,Nothing,<:NamedTuple}) = merge(a, getfield(b, :data))
```
-/
def mergePairs (generated : Bool) (a bData : ModelNT) : Result ModelNT :=
  mergeNamed generated a bData

/--
Julia source: base/namedtuple.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple, b::Iterators.Zip{<:Tuple{Any,Any}}) = merge(a, NamedTuple{Tuple(b.is[1])}(b.is[2]))
```
-/
def mergeZip (generated : Bool) (typeofValue : Value → TypeTag) (a : ModelNT)
    (keys : List String) (values : List Value) : Result ModelNT := do
  let b ← constructNamesFromIterator (fun (xs : List Value) => (Except.ok xs : Result (List Value)))
    tupleToNamedTuple typeofValue keys values
  mergeNamed generated a b

def mergeManyLoop (generated : Bool) (a : ModelNT) : List ModelNT → Result ModelNT
  | [] => .ok a
  | b :: rest => do
      let merged ← mergeNamed generated a b
      mergeManyLoop generated merged rest

/--
Julia source: base/namedtuple.jl:350-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple, b::NamedTuple, cs::NamedTuple...) = merge(merge(a, b), cs...)
```
-/
def mergeMany (generated : Bool) (a b : ModelNT) (cs : List ModelNT) : Result ModelNT := do
  let first ← mergeNamed generated a b
  mergeManyLoop generated first cs

/--
Julia source: base/namedtuple.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(a::NamedTuple) = a
```
-/
def mergeOne (a : ModelNT) : ModelNT := a

/--
Julia source: base/namedtuple.jl:364-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge(a::NamedTuple, itr)
    names = Symbol[]
    vals = Any[]
    inds = IdDict{Symbol,Int}()
    for (k, v) in itr
        k = k::Symbol
        oldind = get(inds, k, 0)
        if oldind > 0
            vals[oldind] = v
        else
            push!(names, k)
            push!(vals, v)
            inds[k] = length(names)
        end
    end
    merge(a, NamedTuple{(names...,)}((vals...,)))
end
```
-/
def mergeIterator (generated : Bool) (fromTuple : NTType → List Value → Result ModelNT)
    (typeofValue : Value → TypeTag) (a : ModelNT) (itr : List KV) : Result ModelNT := do
  let (names, values) ← pairFields itr
  let b ← constructNamesFromIterator (fun (xs : List Value) => (Except.ok xs : Result (List Value)))
    fromTuple typeofValue names values
  mergeNamed generated a b

/--
Julia source: base/namedtuple.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(nt::NamedTuple{names}) where {names} = names::Tuple{Vararg{Symbol}}
```
-/
def keysNamedTuple (nt : ModelNT) : List String := nt.type.names

/--
Julia source: base/namedtuple.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
values(nt::NamedTuple) = Tuple(nt)
```
-/
def valuesNamedTuple (nt : ModelNT) : List Value := Tuple nt

/-- Core's `isdefined` primitive for this NamedTuple representation. -/
def isdefinedNamedTuple (nt : ModelNT) : Key → Result Bool
  | .symbol key => .ok (nt.type.names.contains key)
  | .nativeInteger index => .ok (decide (1 ≤ index ∧ index ≤ Int.ofNat nt.values.length))
  | .integer _ => .error (.typeError "isdefined does not accept integer NamedTuple fields")
  | .other => .error (.typeError "invalid NamedTuple field key")

/--
Julia source: base/namedtuple.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(nt::NamedTuple, key::Union{Integer, Symbol}) = isdefined(nt, key)
```
-/
def haskey (nt : ModelNT) (key : Key) : Result Bool := isdefinedNamedTuple nt key

/--
Julia source: base/namedtuple.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(nt::NamedTuple, key::Union{Integer, Symbol}, default) = isdefined(nt, key) ? getfield(nt, key) : default
```
-/
def getDefault (nt : ModelNT) (key : Key) (default : Value) : Result Value :=
  match isdefinedNamedTuple nt key with
  | .error e => .error e
  | .ok defined =>
      if defined then
        match key with
        | .symbol name => getfield nt name
        | .nativeInteger index => getfieldIndex nt index
        | .integer index => getfieldIndex nt index
        | .other => .error (.typeError "invalid NamedTuple field key")
      else
        .ok default

/--
Julia source: base/namedtuple.jl:386-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, nt::NamedTuple, key::Union{Integer, Symbol}) = isdefined(nt, key) ? getfield(nt, key) : f()
```
-/
def getDefaultFunction (f : Unit → Value) (nt : ModelNT) (key : Key) : Result Value :=
  match isdefinedNamedTuple nt key with
  | .error e => .error e
  | .ok defined =>
      if defined then
        match key with
        | .symbol name => getfield nt name
        | .nativeInteger index => getfieldIndex nt index
        | .integer index => getfieldIndex nt index
        | .other => .error (.typeError "invalid NamedTuple field key")
      else
        .ok (f ())

/--
Julia source: base/namedtuple.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(t::NamedTuple{names}) where names = NamedTuple{tail(names::Tuple)}(t)
```
-/
def tailNamed (tailNames : List String → Result (List String)) (t : ModelNT) : Result ModelNT :=
  match tailNames t.type.names with
  | .error e => .error e
  | .ok names => constructNamesFromNamedTuple false t names

/--
Julia source: base/namedtuple.jl:388-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
front(t::NamedTuple{names}) where names = NamedTuple{front(names::Tuple)}(t)
```
-/
def frontNamed (frontNames : List String → Result (List String)) (t : ModelNT) : Result ModelNT :=
  match frontNames t.type.names with
  | .error e => .error e
  | .ok names => constructNamesFromNamedTuple false t names

/--
Julia source: base/namedtuple.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(nt::NamedTuple) = NamedTuple{reverse(keys(nt))}(reverse(values(nt)))
```
-/
def reverseNamedTuple (fromTuple : NTType → List Value → Result ModelNT)
    (typeofValue : Value → TypeTag) (nt : ModelNT) : Result ModelNT := do
  let names := JuliaLean.base.tuple.reverseTuple (keysNamedTuple nt)
  let values := (valuesNamedTuple nt).reverse
  constructNamesFromIterator (fun (xs : List Value) => (Except.ok xs : Result (List Value)))
    fromTuple typeofValue names values

/--
Julia source: base/namedtuple.jl:391-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function diff_names(an::Tuple{Vararg{Symbol}}, bn::Tuple{Vararg{Symbol}})
    @nospecialize
    @_total_meta
    names = Symbol[]
    for n in an
        if !sym_in(n, bn)
            push!(names, n)
        end
    end
    (names...,)
end
```
-/
def diff_names (an bn : List String) : List String :=
  an.filter (fun name => !bn.contains name)

/--
Julia source: base/namedtuple.jl:403-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function diff_types(a::NamedTuple, names::Tuple{Vararg{Symbol}})
    @nospecialize
    @_foldable_meta
    return Tuple{Any[ fieldtype(typeof(a), names[n]) for n in 1:length(names) ]...}
end
```
-/
def diff_types (a : ModelNT) (names : List String) : List TypeTag :=
  names.map (fieldType a.type)

def diffValuesLoop (a : ModelNT) : List String → Result (List Value)
  | [] => .ok []
  | name :: rest => do
      let value ← getfield a name
      let later ← diffValuesLoop a rest
      pure (value :: later)

/--
Julia source: base/namedtuple.jl:409-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function diff_fallback(a::NamedTuple, an::Tuple{Vararg{Symbol}}, bn::Tuple{Vararg{Symbol}})
    @nospecialize
    @_foldable_meta
    names = diff_names(an, bn)
    isempty(names) && return (;)
    types = diff_types(a, names)
    n = length(names)
    A = Memory{Any}(undef, n)
    for i=1:n
        n = names[i]
        A[i] = getfield(a, n)
    end
    _new_NamedTuple(NamedTuple{names, types}, (A...,))
end
```
-/
def diff_fallback (a : ModelNT) (an bn : List String) : Result ModelNT := do
  let names := diff_names an bn
  if names.isEmpty then
    pure emptyNamedTuple
  else
    let types := diff_types a names
    let values ← diffValuesLoop a names
    pure (new_NamedTuple ⟨names, types⟩ values)

/--
Julia source: base/namedtuple.jl:437-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function delete(a::NamedTuple{an}, field::Symbol) where {an}
    names = diff_names(an, (field,))
    NamedTuple{names}(a)
end
```
-/
def deleteNamed (generated : Bool) (a : ModelNT) (field : String) : Result ModelNT :=
  constructNamesFromNamedTuple generated a (diff_names a.type.names [field])

/--
Julia source: base/namedtuple.jl:448-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function structdiff(a::NamedTuple{an}, b::Union{NamedTuple{bn}, Type{NamedTuple{bn}}}) where {an, bn}
    if @generated
        names = diff_names(an, bn)
        isempty(names) && return (;) # just a fast pass
        idx = Int[ fieldindex(a, names[n]) for n in 1:length(names::Tuple) ]
        types = Tuple{Any[ fieldtype(a, idx[n]) for n in 1:length(idx) ]...}
        vals = Any[ :(getfield(a, $(idx[n]))) for n in 1:length(idx) ]
        return :( _new_NamedTuple(NamedTuple{$names,$types}, ($(vals...),)) )
    else
        return diff_fallback(a, an, bn)
    end
end
```
-/
def structdiffNamed (generated : Bool) (a b : ModelNT) : Result ModelNT := do
  let an := a.type.names
  let bn := b.type.names
  if generated then
    let names := diff_names an bn
    if names.isEmpty then
      pure emptyNamedTuple
    else
      let types := diff_types a names
      let values ← diffValuesLoop a names
      pure (new_NamedTuple ⟨names, types⟩ values)
  else
    diff_fallback a an bn

/--
Julia source: base/namedtuple.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
structdiff(a::NamedTuple{an}, b::Union{NamedTuple{an}, Type{NamedTuple{an}}}) where {an} = (;)
```
-/
def structdiffSameNames (_a _b : ModelNT) : ModelNT := emptyNamedTuple

/--
Julia source: base/namedtuple.jl:483-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex(nt::NamedTuple, v, idx::Symbol)
    merge(nt, (; idx => v))
end
```
-/
def setindexNamed (generated : Bool) (typeofValue : Value → TypeTag)
    (nt : ModelNT) (value : Value) (index : String) : Result ModelNT := do
  let singleton := newNamedTuple ⟨[index], [typeofValue value]⟩ [value]
  mergeNamed generated nt singleton

inductive MacroExpr where
  | braces (args : List MacroExpr)
  | block (args : List MacroExpr)
  | symbol (name : String)
  | typed (name : String) (type : TypeTag)
  | line
  | other

structure MacroType where
  names : List String
  fieldTypes : List TypeTag
  deriving Repr, Inhabited

structure KwargsType where
  keyType : TypeTag
  valueType : TypeTag
  namedTuple : MacroType
  deriving Repr, Inhabited

def macroDeclaration (e : MacroExpr) : Option (String × TypeTag) :=
  match e with
  | .symbol name => some (name, .any)
  | .typed name ty => some (name, ty)
  | _ => none

def macroDeclarations (args : List MacroExpr) : List MacroExpr :=
  args.filter fun e => match e with | .line => false | _ => true

/--
Julia source: base/namedtuple.jl:514-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro NamedTuple(ex)
    Meta.isexpr(ex, :braces) || Meta.isexpr(ex, :block) ||
        throw(ArgumentError("@NamedTuple expects {...} or begin...end"))
    decls = filter(e -> !(e isa LineNumberNode), ex.args)
    all(e -> e isa Symbol || Meta.isexpr(e, :(::)), decls) ||
        throw(ArgumentError("@NamedTuple must contain a sequence of name or name::type expressions"))
    vars = [QuoteNode(e isa Symbol ? e : e.args[1]) for e in decls]
    types = [esc(e isa Symbol ? :Any : e.args[2]) for e in decls]
    return :(NamedTuple{($(vars...),), Tuple{$(types...)}})
end
```
-/
def namedTupleMacro (ex : MacroExpr) : Result MacroType := do
  let args ← match ex with
    | .braces args => pure args
    | .block args => pure args
    | _ => throw (.argumentError "@NamedTuple expects {...} or begin...end")
  let decls := macroDeclarations args
  if decls.all (fun e => (macroDeclaration e).isSome) then
    let fields := decls.filterMap macroDeclaration
    pure ⟨fields.map Prod.fst, fields.map Prod.snd⟩
  else
    throw (.argumentError "@NamedTuple must contain a sequence of name or name::type expressions")

/--
Julia source: base/namedtuple.jl:578-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro Kwargs(ex)
    return :(let
        NT = @NamedTuple $ex
        Base.Pairs{keytype(NT),eltype(NT),Nothing,NT}
    end)
end
```
-/
def kwargsMacro (tupleEltype : TypeTag → TypeTag) (ex : MacroExpr) : Result KwargsType := do
  let nt ← namedTupleMacro ex
  let ntType := TypeTag.namedTuple nt.names nt.fieldTypes
  let elementType := eltypeNamedTuple (nteltypeDispatch tupleEltype) ntType
  pure ⟨keytypeType ntType, elementType, nt⟩

/--
Julia source: base/namedtuple.jl:585-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function split_rest(t::NamedTuple{names}, n::Int, st...) where {names}
    _check_length_split_rest(length(t), n)
    names_front, names_last_n = split_rest(names, n, st...)
    return NamedTuple{names_front}(t), NamedTuple{names_last_n}(t)
end
```
-/
def split_rest (nfields : ModelNT → JInt .i64)
    (checkLength : Nat → Int → Result Unit)
    (splitNames : List String → Int → List Value → Result (List String × List String))
    (generated : Bool) (t : ModelNT) (n : JInt .i64) (st : List Value) :
    Result (ModelNT × ModelNT) :=
  match checkLength (length nfields t).val.toNat n.val with
  | .error e => .error e
  | .ok _ =>
      match splitNames t.type.names n.val st with
      | .error e => .error e
      | .ok (frontNames, lastNames) =>
          match constructNamesFromNamedTuple generated t frontNames with
          | .error e => .error e
          | .ok frontTuple =>
              match constructNamesFromNamedTuple generated t lastNames with
              | .error e => .error e
              | .ok lastTuple => .ok (frontTuple, lastTuple)

end JuliaLean.base.namedtuple
