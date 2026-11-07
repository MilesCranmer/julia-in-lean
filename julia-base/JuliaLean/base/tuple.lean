import JuliaLean.Core
import JuliaLean.base.ntuple

/-!
# Model of `base/tuple.jl`

Tuple values are represented by lists. Element operations, type reflection, iterators, and methods
loaded from other Base files are typed inputs where Julia dispatches to those interfaces. Each
source method below has its pinned Julia body in its docstring.
-/

namespace JuliaLean.base.tuple

open JuliaLean

inductive TupleError where
  | julia (error : JlError)
  | dimensionMismatch
  | typeError
  | fieldError
  | errorException
  deriving Repr, DecidableEq, Inhabited

namespace TupleError

def kind : TupleError → String
  | .julia (.overflowError _) => "OverflowError"
  | .julia (.argumentError _) => "ArgumentError"
  | .julia .boundsError => "BoundsError"
  | .julia (.inexactError _) => "InexactError"
  | .julia .divideError => "DivideError"
  | .julia (.domainError _) => "DomainError"
  | .julia (.methodError _) => "MethodError"
  | .julia .eofError => "EOFError"
  | .dimensionMismatch => "DimensionMismatch"
  | .typeError => "TypeError"
  | .fieldError => "FieldError"
  | .errorException => "ErrorException"

end TupleError

abbrev R (α : Type) := Except TupleError α

def bounds {α : Type} : R α := .error (.julia .boundsError)
def argErr {α : Type} (message : String) : R α := .error (.julia (.argumentError message))
def liftJ {α : Type} : Jl α → R α
  | .ok value => .ok value
  | .error error => .error (.julia error)

abbrev KeysResult := Except TupleError (List Nat)

def oneTo (n : Nat) : List Nat := (List.range n).map (· + 1)
def tupleLength {α : Type} (t : List α) : Nat := t.length

def getfield {α : Type} (t : List α) (i : Int) : R α :=
  if 1 ≤ i then
    match t[(i - 1).toNat]? with
    | some value => .ok value
    | none => bounds
  else bounds

def sliceList {α : Type} (t : List α) (first last : Int) : R (List α) :=
  if last < first then .ok []
  else if 1 ≤ first ∧ last ≤ t.length then
    .ok ((t.drop (first - 1).toNat).take (last - first + 1).toNat)
  else bounds

inductive Index where
  | integer (ty : IntTy) (value : JInt ty)
  | big (value : Int)
  | bool (value : Bool)

def Index.value : Index → Int
  | .integer _ value => value.val
  | .big value => value
  | .bool value => if value then 1 else 0

def convertIndex (i : Index) : R (JInt .i64) :=
  match i with
  | .integer .i64 value => .ok value
  | .integer _ value => liftJ (JInt.convert (IntTy.i64.name) .i64 value.val)
  | .big value => liftJ (JInt.convert (IntTy.i64.name) .i64 value)
  | .bool value => .ok (JInt.lit .i64 (if value then 1 else 0))

/-- Julia's `convert(Int, i)` for an `Integer` type `I`, run in the caller's effect monad `m`.
An instance is the conversion method of `I`: `convertIndex` for the built-in `Index` family in
`R`, or a user `Integer` type's own method, whose exceptions stay in `m`. -/
class ConvertInt (I : Type) (m : Type → Type) where
  convertInt : I → m (JInt .i64)

@[default_instance]
instance : ConvertInt Index R := ⟨convertIndex⟩

@[simp] theorem convertInt_index (i : Index) :
    ConvertInt.convertInt (m := R) i = convertIndex i := rfl

def assertInt (i : Index) : R Int :=
  match i with
  | .integer .i64 value => .ok value.val
  | _ => .error .typeError

mutual
  inductive TupleType : Type where
    | bottom
    | any
    | typeVar (name : String)
    | atom (name : String)
    | tuple (parameters : List TupleParam)
    | union (left right : TupleType)
    | unionAll (varName : String) (body : TupleType)

  inductive TupleParam : Type where
    | type (ty : TupleType)
    | value (value : Int)
    | vararg (ty : TupleType) (length : Option Int)
end

structure EltypeInterface where
  empty : TupleType → Bool
  signature : TupleType → Bool
  defined : TupleType → Bool
  isType : TupleType → Bool
  emptyNTuple : TupleType → Bool
  element : TupleType → TupleType
  free : TupleType → Bool
  join : TupleType → TupleType → TupleType

def unwrapVararg : TupleParam → TupleParam
  | .vararg ty _ => .type ty
  | parameter => parameter

def paramType : TupleParam → Option TupleType
  | .type ty | .vararg ty _ => some ty
  | .value _ => none

def typeParameters : TupleType → List TupleParam
  | .tuple parameters => parameters
  | _ => []

def isTupleDataType : TupleType → Bool
  | .tuple _ => true
  | _ => false

def isVatuple : TupleType → Bool
  | .tuple [.vararg _ _] => true
  | _ => false

def unwrapUnionAll : TupleType → TupleType
  | .unionAll _ body => unwrapUnionAll body
  | ty => ty

def rewrapUnionAll (ty environment : TupleType) : TupleType :=
  match environment with
  | .unionAll varName body => .unionAll varName (rewrapUnionAll ty body)
  | _ => ty

def argtail (parameters : List TupleParam) : List TupleParam := parameters.drop 1

def ntuplePattern (ty : TupleType) : Bool :=
  match ty with
  | .tuple [.vararg _ _] => true
  | _ => false

def tupleHashSeed : Nat := 0x77cfa1eef01bca90

structure Ops (α : Type) where
  isequal : α → α → Bool
  isless : α → α → Bool
  eq : α → α → Option Bool
  lt : α → α → Option Bool
  hash : α → Nat → Nat
  mismatchIndices : String → List (List Nat) → KeysResult

structure Iter (α σ : Type) where
  first : R (Option (α × σ))
  next : σ → R (Option (α × σ))

def iterAt {α σ : Type} (itr : Iter α σ) (state : Option σ) : R (Option (α × σ)) :=
  match state with
  | none => itr.first
  | some value => itr.next value

inductive ArgPack : List Type → Type 1 where
  | nil : ArgPack []
  | cons {α : Type} {types : List Type} : α → ArgPack types → ArgPack (α :: types)

@[reducible]
def CurriedArgs : List Type → Type → Type
  | [], result => result
  | α :: types, result => α → CurriedArgs types result

def splatArgs {types : List Type} {result : Type}
    (f : CurriedArgs types result) (args : ArgPack types) : result :=
  match args with
  | .nil => f
  | .cons value rest => splatArgs (f value) rest


def assertTupleType {α : Type} (hasType : List α → TupleType → Bool)
    (values : List α) (T : TupleType) : R (List α) :=
  if hasType values T then .ok values else .error .typeError


def mapOneLoop {α β : Type} (f : α → β) (t : List α) : Nat → Nat → List β
  | _, 0 => []
  | i, k + 1 => match t[i]? with
      | some value => f value :: mapOneLoop f t (i + 1) k
      | none => []

def mapTwoLoop {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) :
    Nat → Nat → List γ
  | _, 0 => []
  | i, k + 1 => match t[i]?, s[i]? with
      | some a, some b => f a b :: mapTwoLoop f t s (i + 1) k
      | _, _ => []
inductive NTupleArity : TupleType → Int → Prop where
  | vararg (E : TupleType) (N : Int) : NTupleArity (.tuple [.vararg E (some N)]) N
  | fields (types : List TupleType) :
      NTupleArity (.tuple (types.map .type)) (types.length : Int)
  | union {left right : TupleType} {N : Int} :
      NTupleArity left N → NTupleArity right N → NTupleArity (.union left right) N
  | unionAll (name : String) {body : TupleType} {N : Int} :
      NTupleArity body N → NTupleArity (.unionAll name body) N

/--
Julia source: base/tuple.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_counttuple(::Type{<:NTuple{N,Any}}) where {N} = N
```
-/
def countTupleSpecific (N : Int) (T : TupleType) (_dispatch : NTupleArity T N) : Int := N

/--
Julia source: base/tuple.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_counttuple(::Type) = nothing
```
-/
def countTupleFallback (_T : TupleType) : Option Int := none

/--
Julia source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(@nospecialize t::Tuple) = nfields(t)
```
-/
def lengthTuple {α : Type} (t : List α) : Nat := t.length

/--
Julia source: base/tuple.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(@nospecialize t::Tuple) = 1
```
-/
def firstindexTuple {α : Type} (_t : List α) : Int := 1

/--
Julia source: base/tuple.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(@nospecialize t::Tuple) = length(t)
```
-/
def lastindexTuple {α : Type} (t : List α) : Nat := lengthTuple t

/--
Julia source: base/tuple.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(@nospecialize(t::Tuple), d::Integer) = (d == 1) ? length(t) : throw(ArgumentError("invalid tuple dimension $d"))
```
-/
def sizeTuple {α : Type} (showIndex : Index → String) (t : List α) (d : Index) : R Nat :=
  if d.value = 1 then .ok (lengthTuple t) else argErr s!"invalid tuple dimension {showIndex d}"

/--
Julia source: base/tuple.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(@nospecialize t::Tuple) = (OneTo(length(t)),)
```
-/
def axesTuple {α : Type} (t : List α) : List (List Nat) := [oneTo (lengthTuple t)]

/--
Julia source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
```
-/
def getindexInt {α : Type} (t : List α) (i : JInt .i64) : R α := getfield t i.val

/--
Julia source: base/tuple.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(@nospecialize(t::Tuple), i::Integer) = getfield(t, convert(Int, i), @_boundscheck)
```
-/
def getindexInteger {m : Type → Type} [Monad m] {α I : Type} [convert : ConvertInt I m]
    (t : List α) (i : I) (liftR : {β : Type} → R β → m β := by exact fun r => r) : m α := do
  let j ← convert.convertInt i
  liftR (getfield t j.val)

/--
Julia source: base/tuple.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__safe_getindex(@nospecialize(t::Tuple), i::Int) = (@_nothrow_noub_meta; getfield(t, i, false))
```
-/
def safeGetindex {α : Type} (t : List α) (i : Int) : Option α :=
  if 1 ≤ i then t[(i - 1).toNat]? else none

/--
Julia source: base/tuple.jl:291-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _compute_eltype(@nospecialize t)
    @_total_meta
    has_free_typevars(t) && return Any
    t´ = unwrap_unionall(t)
    # Given t = Tuple{Vararg{S}} where S<:Real, the various
    # unwrapping/wrapping/va-handling here will return Real
    if t´ isa Union
        return promote_typejoin(_compute_eltype(rewrap_unionall(t´.a, t)),
                                _compute_eltype(rewrap_unionall(t´.b, t)))
    end
    p = (t´::DataType).parameters
    length(p) == 0 && return Union{}
    elt = rewrap_unionall(unwrapva(p[1]), t)
    elt isa Type || return Union{} # Tuple{2} is legal as a Type, but the eltype is Union{} since it is uninhabited
    r = elt
    for i in 2:length(p)
        r === Any && return r # if we've already reached Any, it can't widen any more
        elt = rewrap_unionall(unwrapva(p[i]), t)
        elt isa Type || return Union{} # Tuple{2} is legal as a Type, but the eltype is Union{} since it is uninhabited
        r = promote_typejoin(elt, r)
    end
    return r
end
```
-/
def computeEltype (hasFreeTypevars : TupleType → Bool)
    (promoteTypejoin : TupleType → TupleType → TupleType) (T : TupleType) : TupleType :=
  let rec combine (wrap : TupleType → TupleType) (result : TupleType) :
      List TupleParam → TupleType
    | [] => result
    | parameter :: parameters =>
      match result with
      | .any => .any
      | _ =>
        match paramType (unwrapVararg parameter) with
        | none => .bottom
        | some elementType => combine wrap (promoteTypejoin (wrap elementType) result) parameters
  let rec compute (t : TupleType) (wrap : TupleType → TupleType) : TupleType :=
    match t with
    | .unionAll varName body => compute body (fun ty => wrap (.unionAll varName ty))
    | .union a b =>
      if hasFreeTypevars (wrap (.union a b)) then .any
      else promoteTypejoin (compute a wrap) (compute b wrap)
    | .tuple parameters =>
      if hasFreeTypevars (wrap (.tuple parameters)) then .any else
      match parameters with
      | [] => .bottom
      | first :: parameters =>
        match paramType (unwrapVararg first) with
        | none => .bottom
        | some firstType => combine wrap (wrap firstType) parameters
    | other => if hasFreeTypevars (wrap other) then .any else .bottom
  compute T id
/--
Julia source: base/tuple.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eltype_ntuple(t::Type{<:Tuple{Vararg{E}}}) where {E} = @isdefined(E) ? (E isa Type ? E : Union{}) : (t <: Tuple{} ? Union{} : _compute_eltype(t))
```
-/
def eltypeNTuple (ops : EltypeInterface) (t : TupleType)
    (eDefined eIsType emptyTuple : Bool) (e : TupleType) : TupleType :=
  if eDefined then (if eIsType then e else .bottom)
  else if emptyTuple then .bottom else computeEltype ops.free ops.join t

/--
Julia source: base/tuple.jl:282-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eltype(t::Type{<:Tuple})
    if t <: Tuple{}
        Bottom
    elseif isa(t, _eltype_ntuple_sig_condition)
        _eltype_ntuple(t)
    else
        _compute_eltype(t)
    end
end
```
-/
def tupleEltype (ops : EltypeInterface) (t : TupleType) : TupleType :=
  if ops.empty t then .bottom
  else if ops.signature t then
    eltypeNTuple ops t (ops.defined t) (ops.isType t) (ops.emptyNTuple t) (ops.element t)
  else computeEltype ops.free ops.join t

structure TupleConversion (α : Type) where
  typeof : List α → TupleType
  eltypes : EltypeInterface
  convert : TupleType → α → R α

inductive TupleSubscript (ι : Type) where
  | integer (index : Index)
  | custom (index : ι)

def getindexSubscript {α ι : Type} (custom : List α → ι → R α)
    (t : List α) (i : TupleSubscript ι) : R α :=
  match i with
  | .integer index => getindexInteger t index
  | .custom index => custom t index

def noCustomIndex {α : Type} (_t : List α) (i : PEmpty) : R α := nomatch i

/--
Julia source: base/tuple.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::Tuple, r::AbstractArray{<:Any,1}) = (eltype(t)[t[ri] for ri in r]...,)
```
-/
def getindexVector {α ι : Type} (custom : List α → ι → R α)
    (typing : TupleConversion α) (t : List α) (r : List (TupleSubscript ι)) : R (List α) :=
  let E := tupleEltype typing.eltypes (typing.typeof t)
  r.mapM fun i => do
    let value ← getindexSubscript custom t i
    typing.convert E value

/--
Julia source: base/tuple.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::Tuple, b::AbstractArray{Bool,1}) = length(b) == length(t) ? getindex(t, findall(b)) : throw(BoundsError(t, b))
```
-/
def getindexBoolVector {α : Type} (findall : List Bool → List Index)
    (typing : TupleConversion α) (t : List α) (b : List Bool) : R (List α) :=
  if b.length = t.length then
    getindexVector noCustomIndex typing t ((findall b).map .integer)
  else bounds

def integerRange (first last : Int) : List Index :=
  (List.range (last - first + 1).toNat).map fun (offset : Nat) =>
    .integer .i64 (JInt.lit .i64 (first + (offset : Int)))

/--
Julia source: base/tuple.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::Tuple, c::Colon) = t
```
-/
def getindexColon {α : Type} (t : List α) : List α := t

/--
Julia source: base/tuple.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(t::Tuple, i::Integer, default) = i in 1:length(t) ? getindex(t, i) : default
```
-/
def getDefault {α : Type} (t : List α) (i : Index) (default : α) : R α :=
  if 1 ≤ i.value ∧ i.value ≤ t.length then getindexInteger t i else .ok default

/--
Julia source: base/tuple.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, t::Tuple, i::Integer) = i in 1:length(t) ? getindex(t, i) : f()
```
-/
def getThunk {α : Type} (f : Unit → R α) (t : List α) (i : Index) : R α :=
  if 1 ≤ i.value ∧ i.value ≤ t.length then getindexInteger t i else f ()


/--
Julia source: base/tuple.jl:61-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex(v, i::Integer, args::Vararg{Any,N}) where {N}
    @inline
    return ntuple(j -> ifelse(j == i, v, args[j]), Val{N}())::NTuple{N, Any}
end
```
-/
def setindexVarargs {α : Type} (ntuple : (Nat → α) → Nat → List α)
    (ifelse : Bool → α → α → α) (v : α) (i : Index) (args : List α) : List α :=
  ntuple (fun j => ifelse ((j : Int) = i.value) v (args.getD (j - 1) v)) args.length

/--
Julia source: base/tuple.jl:55-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex(x::Tuple, v, i::Integer)
    @boundscheck 1 <= i <= length(x) || throw(BoundsError(x, i))
    @inline
    _setindex(v, i, x...)
end
```
-/
def setindexTuple {α : Type} (ntuple : (Nat → α) → Nat → List α)
    (ifelse : Bool → α → α → α) (t : List α) (v : α) (i : Index) : R (List α) :=
  if 1 ≤ i.value ∧ i.value ≤ t.length then .ok (setindexVarargs ntuple ifelse v i t) else bounds

/--
Julia source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(@nospecialize(t::Tuple), i::Int=1)
    @inline
    @_nothrow_meta
    return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
end
```
-/
def iterateTuple {α : Type} (t : List α) (i : Int := 1) : Option (α × Int) :=
  if 1 ≤ i ∧ i ≤ t.length then
    (t[(i - 1).toNat]?).map (fun value => (value, i + 1))
  else none

/--
Julia source: base/tuple.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(@nospecialize t::Tuple) = OneTo(length(t))
```
-/
def keysTuple {α : Type} (t : List α) : List Nat := oneTo (lengthTuple t)

/--
Julia source: base/tuple.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(@nospecialize(t::Tuple), i::Integer) = Int(i)-1
```
-/
def previndTuple {α : Type} (t : List α) (i : Index) : R (JInt .i64) := do
  let j ← convertIndex i
  pure (j - JInt.lit .i64 1)

/--
Julia source: base/tuple.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(@nospecialize(t::Tuple), i::Integer) = Int(i)+1
```
-/
def nextindTuple {α : Type} (t : List α) (i : Index) : R (JInt .i64) := do
  let j ← convertIndex i
  pure (j + JInt.lit .i64 1)

/--
Julia source: base/tuple.jl:148-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function keys(t::Tuple, t2::Tuple...)
    @inline
    lent = length(t)
    if !all(==(lent) ∘ length, t2)
        let inds = map(only ∘ axes, (t, t2...))
            throw_eachindex_mismatch_indices("indices", inds...)
        end
    end
    Base.OneTo(lent)
end
```
-/
def keysMany {α : Type} (mismatch : String → List (List Nat) → KeysResult)
    (t : List α) (t2 : List (List α)) : KeysResult :=
  let lent := lengthTuple t
  if !(t2.all (fun other => lengthTuple other = lent)) then
    let inds := (t :: t2).map (fun tuple => (axesTuple tuple).headD [])
    mismatch "indices" inds
  else .ok (oneTo lent)

/--
Julia source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
```
-/
def indexedIterateTuple {α : Type} (t : List α) (i : Int) (_state : Int := 1) : R (α × Int) := do
  let value ← getfield t i
  pure (value, i + 1)

/--
Julia source: base/tuple.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexed_iterate(a::Union{Array,Memory}, i::Int, state=1) = (@inline; (a[i], i+1))
```
-/
def indexedIterateArray {α A : Type} (getindex : A → Int → R α)
    (a : A) (i : Int) (_state : Int := 1) : R (α × Int) := do
  let value ← getindex a i
  pure (value, i + 1)

/--
Julia source: base/tuple.jl:163-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indexed_iterate(I, i)
    x = iterate(I)
    x === nothing && throw(BoundsError(I, i))
    x
end
```
-/
def indexedIterateGeneric {α σ : Type} (itr : Iter α σ) (_i : Int) : R (α × σ) :=
  match itr.first with
  | .error e => .error e
  | .ok none => bounds
  | .ok (some result) => .ok result

/--
Julia source: base/tuple.jl:168-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indexed_iterate(I, i, state)
    x = iterate(I, state)
    x === nothing && throw(BoundsError(I, i))
    x
end
```
-/
def indexedIterateGenericState {α σ : Type} (itr : Iter α σ) (_i : Int) (state : σ) : R (α × σ) :=
  match itr.next state with
  | .error e => .error e
  | .ok none => bounds
  | .ok (some result) => .ok result

/--
Julia source: base/tuple.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(t::Tuple) = t
```
-/
def restTupleAll {α : Type} (t : List α) : List α := t

/--
Julia source: base/tuple.jl:207-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rest(t::Tuple, i)
    let i = i::Int
        ntuple(x -> getfield(t, x+i-1), length(t)-i+1)
    end
end
```
-/
def restTupleFrom {α : Type} (ntuple : (Nat → R α) → Int → R (List α))
    (t : List α) (i : Index) : R (List α) := do
  let i ← assertInt i
  ntuple (fun x => getfield t ((x : Int) + i - 1))
    ((t.length : Int) - i + 1)

/--
Julia source: base/tuple.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(a::Union{Array,Memory,Core.SimpleVector}, i=1) = a[(i::Int):end]
```
-/
def restArray {α : Type} (slice : List α → Int → Int → R (List α))
    (a : List α) (i : Index := .integer .i64 (JInt.lit .i64 1)) : R (List α) := do
  let i ← assertInt i
  slice a i a.length

/--
Julia source: base/tuple.jl:213-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(itr, state...) = Iterators.rest(itr, state...)
```
-/
def restGeneric {α σ States : Type} (iteratorsRest : Iter α σ → States → Iter α σ)
    (itr : Iter α σ) (states : States) : Iter α σ := iteratorsRest itr states


/--
Julia source: base/tuple.jl:255-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _check_length_split_rest(len, n)
    len < n && throw(ArgumentError(
        "The iterator only contains $len elements, but at least $n were requested."
    ))
end
```
-/
def checkLengthSplitRest (len : Nat) (n : Int) : R Unit :=
  if (len : Int) < n then
    argErr s!"The iterator only contains {len} elements, but at least {n} were requested."
  else .ok ()

/--
Julia source: base/tuple.jl:260-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _split_rest(a::Union{AbstractArray, Core.SimpleVector}, n::Int)
    _check_length_split_rest(length(a), n)
    return a[begin:end-n], a[end-n+1:end]
end
```
-/
def splitRestArray {α : Type} (slice : List α → Int → Int → R (List α))
    (a : List α) (n : Int) : R (List α × List α) := do
  checkLengthSplitRest a.length n
  let first ← slice a 1 (a.length - n)
  let last ← slice a (a.length - n + 1) a.length
  pure (first, last)

/--
Julia source: base/tuple.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_split_rest(itr, n::Int) = _split_rest(collect(itr), n)
```
-/
def splitRestCollected {α σ : Type} (collect : Iter α σ → List α)
    (slice : List α → Int → Int → R (List α)) (itr : Iter α σ) (n : Int) : R (List α × List α) :=
  splitRestArray slice (collect itr) n

/--
Julia source: base/tuple.jl:248-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function split_rest(itr, n::Int, state...)
    if IteratorSize(itr) == IsInfinite()
        throw(ArgumentError("Cannot split an infinite iterator in the middle."))
    end
    return _split_rest(rest(itr, state...), n)
end
```
-/
def splitRestGeneric {α σ States : Type} (isInfinite : Iter α σ → Bool)
    (iteratorsRest : Iter α σ → States → Iter α σ) (collect : Iter α σ → List α)
    (slice : List α → Int → Int → R (List α)) (itr : Iter α σ) (n : Int)
    (states : States) : R (List α × List α) :=
  if isInfinite itr then argErr "Cannot split an infinite iterator in the middle."
  else splitRestCollected collect slice (restGeneric iteratorsRest itr states) n

/--
Julia source: base/tuple.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval _split_tuple(t::Tuple, n::Int, i::Int=1) = ($(Expr(:meta, :aggressive_constprop)); (t[i:n], t[n+1:end]))
```
-/
def splitTupleSlice {α : Type} (typing : TupleConversion α)
    (t : List α) (n i : Int) : R (List α × List α) := do
  let first ← getindexVector noCustomIndex typing t ((integerRange i n).map .integer)
  let last ← getindexVector noCustomIndex typing t ((integerRange (n + 1) t.length).map .integer)
  pure (first, last)

/--
Julia source: base/tuple.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval split_rest(t::Tuple, n::Int, i=1) = ($(Expr(:meta, :aggressive_constprop)); _split_tuple(t, length(t)-n, Int(i)))
```
-/
def splitRestTupleState {α : Type} (typing : TupleConversion α)
    (t : List α) (n : Int) (i : Index := .integer .i64 (JInt.lit .i64 1)) : R (List α × List α) := do
  let i ← convertIndex i
  splitTupleSlice typing t (t.length - n) i.val

/--
Julia source: base/tuple.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(::Tuple{}) = throw(ArgumentError("tuple must be non-empty"))
```
-/
def firstEmpty {α : Type} : R α := argErr "tuple must be non-empty"

/--
Julia source: base/tuple.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(t::Tuple) = t[1]
```
-/
def firstTuple {α : Type} (t : List α) : R α := getfield t 1




/--
Julia source: base/tuple.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(@nospecialize T::Type{<:Tuple}) = Int
```
-/
def keytypeType (_T : TupleType) : TupleType := .atom "Int64"
/--
Julia source: base/tuple.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(@nospecialize t::Tuple) = keytype(typeof(t))
```
-/
def keytypeValue {α : Type} (typeof : List α → TupleType) (t : List α) : TupleType :=
  keytypeType (typeof t)


/--
Julia source: base/tuple.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(@nospecialize T::Type{<:Tuple}) = eltype(T)
```
-/
def valtypeType (ops : EltypeInterface) (T : TupleType) : TupleType := tupleEltype ops T

/--
Julia source: base/tuple.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(@nospecialize t::Tuple) = valtype(typeof(t))
```
-/
def valtypeValue {α : Type} (typeof : List α → TupleType)
    (ops : EltypeInterface) (t : List α) : TupleType := valtypeType ops (typeof t)


/--
Julia source: base/tuple.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
safe_tail(t::Tuple) = tail(t)
```
-/
def safeTail {α : Type} (tail : List α → R (List α)) (t : List α) : R (List α) := tail t

/--
Julia source: base/tuple.jl:324-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
safe_tail(t::Tuple{}) = ()
```
-/
def safeTailEmpty {α : Type} (_t : List α) : List α := []


/--
Julia source: base/tuple.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_front() = throw(ArgumentError("Cannot call front on an empty tuple."))
```
-/
def frontEmpty {α : Type} : R (List α) := argErr "Cannot call front on an empty tuple."

/--
Julia source: base/tuple.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_front(v) = ()
```
-/
def frontOne {α : Type} (_v : α) : List α := []

mutual
  def frontArgs {α : Type} : List α → R (List α)
    | [] => frontEmpty
    | [value] => .ok (frontOne value)
    | value :: next :: rest => frontMany value (next :: rest)
  termination_by t => 2 * t.length
  decreasing_by all_goals simp_wf <;> omega

/--
Julia source: base/tuple.jl:350-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _front(v, t...)
    @inline
    (v, _front(t...)...)
end
```
-/
  def frontMany {α : Type} (v : α) (t : List α) : R (List α) := do
    let rest ← frontArgs t
    pure (v :: rest)
  termination_by 2 * t.length + 1
  decreasing_by all_goals simp_wf <;> omega
end

/--
Julia source: base/tuple.jl:344-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function front(t::Tuple)
    @inline
    _front(t...)
end
```
-/
def frontTuple {α : Type} (t : List α) : R (List α) := frontArgs t

/--
Julia source: base/tuple.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{})              = ()
```
-/
def mapOneEmpty {α β : Type} (_f : α → β) : List β := []

/--
Julia source: base/tuple.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any,})          = (@inline; (f(t[1]),))
```
-/
def mapOneOne {α β : Type} (f : α → β) (t : List α) : List β :=
  match t with | [a] => [f a] | _ => []

/--
Julia source: base/tuple.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any, Any})      = (@inline; (f(t[1]), f(t[2])))
```
-/
def mapOneTwo {α β : Type} (f : α → β) (t : List α) : List β :=
  match t with | [a, b] => [f a, f b] | _ => []

/--
Julia source: base/tuple.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any, Any, Any}) = (@inline; (f(t[1]), f(t[2]), f(t[3])))
```
-/
def mapOneThree {α β : Type} (f : α → β) (t : List α) : List β :=
  match t with | [a, b, c] => [f a, f b, f c] | _ => []

mutual
  def mapOneRec {α β : Type} (f : α → β) : Nat → List α → List β
    | 0, _ => mapOneEmpty f
    | fuel + 1, t => mapOneGeneric f fuel t
  termination_by fuel _ => 2 * fuel + 1
  decreasing_by all_goals simp_wf <;> omega

/--
Julia source: base/tuple.jl:362-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple)                = (@inline; (f(t[1]), map(f,tail(t))...))
```
-/
  def mapOneGeneric {α β : Type} (f : α → β) (fuel : Nat) (t : List α) : List β :=
    match t with | [] => [] | a :: rest => f a :: mapOneRec f fuel rest
  termination_by 2 * fuel + 2
  decreasing_by all_goals simp_wf <;> omega
end

/--
Julia source: base/tuple.jl:375-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function front(t::NTuple{32, Any})
    @inline
    _front(t...)
end
```
-/
def front32 {α : Type} (t : List α) (_length : t.length = 32) : R (List α) := frontArgs t

/--
Julia source: base/tuple.jl:387-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _front_type(@nospecialize T::Type{<:Tuple})
    @_foldable_meta
    (T isa DataType && !isvatuple(T)) || return Tuple
    params = (T::DataType).parameters
    return Tuple{params[1:(length(params)::Int - 1)]...}
end
```
-/
def frontType (T : TupleType) : TupleType :=
  if !(isTupleDataType T && !isVatuple T) then .tuple [.vararg .any none]
  else
    let parameters := typeParameters T
    .tuple (parameters.take (parameters.length - 1))
/--
Julia source: base/tuple.jl:380-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function front(t::Any32)
    n = length(t) - 1
    r = ntuple(i -> getfield(t, i), n)::Tuple{Vararg{eltype(typeof(t))}}
    return r::_front_type(typeof(t))
end
```
-/
def frontAny32 {α : Type} (ntuple : (Nat → R α) → Nat → R (List α))
    (typeof : List α → TupleType) (eltypes : EltypeInterface)
    (hasType : List α → TupleType → Bool)
    (t : List α) (_length : 32 ≤ t.length) : R (List α) := do
  let n := t.length - 1
  let values ← ntuple (fun i => getfield t (i : Int)) n
  let r ← assertTupleType hasType values (.tuple [.vararg (tupleEltype eltypes (typeof t)) none])
  assertTupleType hasType r (frontType (typeof t))


/--
Julia source: base/tuple.jl:394-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f, t::Any32)
    n = length(t)
    A = Vector{Any}(undef, n)
    for i=1:n
        A[i] = f(t[i])
    end
    (A...,)
end
```
-/
def mapOneLong {α β : Type} (f : α → β) (t : List α) : List β :=
  let n := t.length
  mapOneLoop f t 0 n

/--
Julia source: base/tuple.jl:403-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{},        s::Tuple{})        = ()
```
-/
def mapTwoEmptyEmpty {α β γ : Type} (_f : α → β → γ) : List γ := []

/--
Julia source: base/tuple.jl:404-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple,          s::Tuple{})        = ()
```
-/
def mapTwoAnyEmpty {α β γ : Type} (_f : α → β → γ) (_t : List α) : List γ := []

/--
Julia source: base/tuple.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{},        s::Tuple)          = ()
```
-/
def mapTwoEmptyAny {α β γ : Type} (_f : α → β → γ) (_s : List β) : List γ := []

/--
Julia source: base/tuple.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any,},    s::Tuple{Any,})    = (@inline; (f(t[1],s[1]),))
```
-/
def mapTwoOne {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : List γ :=
  match t, s with | [a], [b] => [f a b] | _, _ => []

/--
Julia source: base/tuple.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any,Any}, s::Tuple{Any,Any}) = (@inline; (f(t[1],s[1]), f(t[2],s[2])))
```
-/
def mapTwoTwo {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : List γ :=
  match t, s with | [a, a'], [b, b'] => [f a b, f a' b'] | _, _ => []

mutual
  def mapTwoRec {α β γ : Type} (f : α → β → γ) : Nat → List α → List β → List γ
    | 0, _, _ => mapTwoEmptyEmpty f
    | fuel + 1, t, s => mapTwoGeneric f fuel t s
  termination_by fuel _ _ => 2 * fuel + 1
  decreasing_by all_goals simp_wf <;> omega

/--
Julia source: base/tuple.jl:408-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f, t::Tuple, s::Tuple)
    @inline
    (f(t[1],s[1]), map(f, tail(t), tail(s))...)
end
```
-/
  def mapTwoGeneric {α β γ : Type} (f : α → β → γ) (fuel : Nat)
      (t : List α) (s : List β) : List γ :=
    match t, s with
    | a :: restT, b :: restS => f a b :: mapTwoRec f fuel restT restS
    | _, _ => []
  termination_by 2 * fuel + 2
  decreasing_by all_goals simp_wf <;> omega
end

/--
Julia source: base/tuple.jl:412-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f, t::Any32, s::Any32)
    n = min(length(t), length(s))
    A = Vector{Any}(undef, n)
    for i = 1:n
        A[i] = f(t[i], s[i])
    end
    (A...,)
end
```
-/
def mapTwoLong {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : List γ :=
  let n := min t.length s.length
  mapTwoLoop f t s 0 n

def mapTuple {α β : Type} (f : α → R β) (t : List α) : R (List β) :=
  if 32 ≤ t.length then (mapOneLong f t).mapM id
  else match t with
  | [] => (mapOneEmpty f).mapM id
  | [a] => (mapOneOne f [a]).mapM id
  | [a, b] => (mapOneTwo f [a, b]).mapM id
  | [a, b, c] => (mapOneThree f [a, b, c]).mapM id
  | _ => (mapOneGeneric f t.length t).mapM id

/--
Julia source: base/tuple.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
heads(ts::Tuple...) = map(t -> t[1], ts)
```
-/
def heads {α : Type} (ts : List (List α)) : R (List α) :=
  mapTuple (fun t => getindexInt t (JInt.lit .i64 1)) ts

/--
Julia source: base/tuple.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tails(ts::Tuple...) = map(tail, ts)
```
-/
def tails {α : Type} (tail : List α → R (List α)) (ts : List (List α)) : R (List (List α)) :=
  mapTuple tail ts

/--
Julia source: base/tuple.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, ::Tuple{}, ::Tuple{}...) = ()
```
-/
def mapManyEmpty {α β : Type} (_f : List α → β) (_ts : List (List α)) : List β := []

/--
Julia source: base/tuple.jl:424-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
anyempty(x::Tuple{}, xs...) = true
```
-/
def anyemptyEmptyTuple {α : Type} (_xs : List (List α)) : Bool := true

/--
Julia source: base/tuple.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
anyempty() = false
```
-/
def anyemptyNone {α : Type} : Bool := false

mutual
  def anyemptyTuple {α : Type} : Nat → List (List α) → Bool
    | 0, _ => anyemptyNone (α := α)
    | _ + 1, [] => anyemptyNone (α := α)
    | _ + 1, [] :: ts => anyemptyEmptyTuple ts
    | fuel + 1, (a :: t) :: ts => anyemptyNonempty fuel (a :: t) ts
  termination_by fuel _ => 2 * fuel + 1
  decreasing_by all_goals simp_wf <;> omega

/--
Julia source: base/tuple.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
anyempty(x::Tuple, xs...) = anyempty(xs...)
```
-/
  def anyemptyNonempty {α : Type} (fuel : Nat) (_x : List α) (xs : List (List α)) : Bool :=
    anyemptyTuple fuel xs
  termination_by 2 * fuel + 2
  decreasing_by all_goals simp_wf <;> omega
end


mutual
  def mapManyRec {α β : Type} (tail : List α → R (List α)) (f : List α → β) :
      Nat → List (List α) → R (List β)
    | 0, ts => .ok (mapManyEmpty f ts)
    | fuel + 1, ts => mapManyLoop tail f fuel ts
  termination_by fuel _ => 2 * fuel + 1
  decreasing_by all_goals simp_wf <;> omega

  def mapManyLoop {α β : Type} (tail : List α → R (List α))
      (f : List α → β) (fuel : Nat) (ts : List (List α)) : R (List β) :=
    if anyemptyTuple ts.length ts then .ok [] else do
      let first ← heads ts
      let rest ← tails tail ts
      let suffix ← mapManyRec tail f fuel rest
      pure (f first :: suffix)
  termination_by 2 * fuel + 2
  decreasing_by all_goals simp_wf <;> omega
end
/--
Julia source: base/tuple.jl:427-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f, t1::Tuple, t2::Tuple, ts::Tuple...)
    @inline
    anyempty(t1, t2, ts...) && return ()
    (f(heads(t1, t2, ts...)...), map(f, tails(t1, t2, ts...)...)...)
end
```
-/
def mapMany {α β : Type} (tail : List α → R (List α))
    (f : List α → β) (first second : List α) (others : List (List α)) : R (List β) :=
  let ts := first :: second :: others
  if anyemptyTuple ts.length ts then .ok [] else do
    let values ← heads ts
    let rest ← tails tail ts
    let suffix ← mapManyRec tail f first.length rest
    pure (f values :: suffix)


def mapManyLongLoop {α β : Type} (f : List α → β) (first second : List α)
    (others : List (List α)) : Nat → Nat → R (List β)
  | _, 0 => .ok []
  | i, count + 1 => do
      let index := JInt.lit .i64 ((i : Int) + 1)
      let a ← getindexInt first index
      let b ← getindexInt second index
      let rest ← (mapOneRec (fun t => getindexInt t index) others.length others).mapM id
      let suffix ← mapManyLongLoop f first second others (i + 1) count
      pure (f (a :: b :: rest) :: suffix)

/--
Julia source: base/tuple.jl:432-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f, t1::Any32, t2::Any32, ts::Any32...)
    n = min(length(t1), length(t2), minimum(length, ts))
    A = Vector{Any}(undef, n)
    for i = 1:n
        A[i] = f(t1[i], t2[i], map(t -> t[i], ts)...)
    end
    (A...,)
end
```
-/
def mapManyLong {α β : Type}
    (minimum : (List α → Nat) → List (List α) → Nat)
    (f : List α → β) (first second : List α) (others : List (List α))
    (_atLeast32 : ∀ t ∈ first :: second :: others, 32 ≤ t.length) : R (List β) :=
  let n := min first.length (min second.length (minimum lengthTuple others))
  mapManyLongLoop f first second others 0 n

/--
Julia source: base/tuple.jl:442-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill_to_length(t::NTuple{N,Any}, val, ::Val{N}) where {N} = t
```
-/
def fillToLengthSame {α : Type} (t : List α) (_value : α) (_N : Nat)
    (_length : t.length = _N) : List α := t

/--
Julia source: base/tuple.jl:443-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill_to_length(t::Tuple{}, val, ::Val{1}) = (val,)
```
-/
def fillToLengthEmptyOne {α : Type} (value : α) : List α := [value]

/--
Julia source: base/tuple.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill_to_length(t::Tuple{Any}, val, ::Val{2}) = (t..., val)
```
-/
def fillToLengthOneTwo {α : Type} (t : List α) (value : α)
    (_length : t.length = 1) : List α := t ++ [value]

/--
Julia source: base/tuple.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill_to_length(t::Tuple{}, val, ::Val{2}) = (val, val)
```
-/
def fillToLengthEmptyTwo {α : Type} (value : α) : List α := [value, value]

/--
Julia source: base/tuple.jl:453-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tuple_type_tail(T::Type)
    @_foldable_meta # TODO: this method is wrong (and not :foldable)
    if isa(T, UnionAll)
        return UnionAll(T.var, tuple_type_tail(T.body))
    elseif isa(T, Union)
        return Union{tuple_type_tail(T.a), tuple_type_tail(T.b)}
    else
        T.name === Tuple.name || throw(MethodError(tuple_type_tail, (T,)))
        if isvatuple(T) && length(T.parameters) == 1
            va = unwrap_unionall(T.parameters[1])::Core.TypeofVararg
            (isdefined(va, :N) && isa(va.N, Int)) || return T
            return Tuple{Vararg{va.T, va.N-1}}
        end
        return Tuple{argtail(T.parameters...)...}
    end
end
```
-/
def tupleTypeTail : TupleType → R TupleType
  | .unionAll varName body => (tupleTypeTail body).map (.unionAll varName)
  | .union left right => do
      let left ← tupleTypeTail left
      let right ← tupleTypeTail right
      pure (.union left right)
  | .tuple [.vararg ty (some n)] => .ok (.tuple [.vararg ty (some (n - 1))])
  | ty@(.tuple [.vararg _ none]) => .ok ty
  | .tuple (parameter :: parameters) => .ok (.tuple (argtail (parameter :: parameters)))
  | .tuple [] => .ok (.tuple [])
  | _ => .error (.julia (.methodError "tuple_type_tail"))

/--
Julia source: base/tuple.jl:470-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::Tuple) where {T<:Tuple} = x isa T ? x : convert(T, x)  # still use `convert` for tuples
```
-/
def tupleTypeCall {α : Type} (isT : List α → Bool) (convert : List α → R (List α))
    (x : List α) : R (List α) := if isT x then .ok x else convert x

/--
Julia source: base/tuple.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Tuple(x::Ref) = tuple(getindex(x))  # faster than iterator for one element
```
-/
def tupleRef {α β : Type} (getindex : β → R α) (x : β) : R (List α) := do
  let value ← getindex x
  pure [value]

/--
Julia source: base/tuple.jl:473-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Tuple(x::Array{T,0}) where {T} = tuple(getindex(x))
```
-/
def tupleArray0 {α β : Type} (getindex : β → R α) (x : β) : R (List α) := do
  let value ← getindex x
  pure [value]


/--
Julia source: base/tuple.jl:477-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple{}}, itr, s...) = ()
```
-/
def totupleEmpty {α σ : Type} {types : List Type}
    (_itr : Iter α σ) (_states : ArgPack types) : List α := []

/--
Julia source: base/tuple.jl:479-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _totuple_err(@nospecialize T)
    @noinline
    throw(ArgumentError(LazyString("too few elements for tuple type ", T)))
end
```
-/
def totupleError {α : Type} [ToString TupleType] (T : TupleType) : R (List α) :=
  argErr s!"too few elements for tuple type {T}"

/--
Julia source: base/tuple.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple{Vararg{E}}}, itr, s...) where {E} = (collect(E, Iterators.rest(itr,s...))...,)
```
-/
def totupleVararg {α σ : Type} {types : List Type}
    (rest : Iter α σ → CurriedArgs types (Iter α σ))
    (collect : TupleType → Iter α σ → R (List α)) (E : TupleType) (itr : Iter α σ)
    (states : ArgPack types) : R (List α) := collect E (splatArgs (rest itr) states)

/--
Julia source: base/tuple.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple}, itr, s...) = (collect(Iterators.rest(itr,s...))...,)
```
-/
def totupleAny {α σ : Type} {types : List Type}
    (rest : Iter α σ → CurriedArgs types (Iter α σ))
    (collect : Iter α σ → R (List α)) (itr : Iter α σ) (states : ArgPack types) : R (List α) :=
  collect (splatArgs (rest itr) states)

mutual
  def totupleContinue {α σ : Type} [ToString TupleType]
      (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
      (fieldtype : TupleType → Nat → TupleType)
      (rest : Iter α σ → σ → Iter α σ)
      (collectTyped : TupleType → Iter α σ → R (List α))
      (collectAny : Iter α σ → R (List α))
      (count : Nat) (itr : Iter α σ) (T : TupleType) (state : σ) : R (List α) :=
    match T with
    | .tuple [] => .ok (totupleEmpty itr (.cons state .nil))
    | .tuple [.vararg .any none] => totupleAny (types := [σ]) rest collectAny itr (.cons state .nil)
    | .tuple [.vararg E none] => totupleVararg (types := [σ]) rest collectTyped E itr (.cons state .nil)
    | _ => totupleFixed (types := [σ]) hasType convert fieldtype rest collectTyped collectAny
        count (fun itr state => itr.next state) itr T (.cons state .nil)
  termination_by 2 * count + 2
  decreasing_by all_goals simp_wf <;> omega

/--
Julia source: base/tuple.jl:484-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _totuple(::Type{T}, itr, s::Vararg{Any,N}) where {T,N}
    @inline
    y = iterate(itr, s...)
    y === nothing && _totuple_err(T)
    T1 = fieldtype(T, 1)
    y1 = y[1]
    t1 = y1 isa T1 ? y1 : convert(T1, y1)::T1
    # inference may give up in recursive calls, so annotate here to force accurate return type to be propagated
    rT = tuple_type_tail(T)
    ts = _totuple(rT, itr, y[2])::rT
    return (t1, ts...)::T
end
```
-/
  def totupleFixed {α σ : Type} {types : List Type} [ToString TupleType]
      (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
      (fieldtype : TupleType → Nat → TupleType)
      (rest : Iter α σ → σ → Iter α σ)
      (collectTyped : TupleType → Iter α σ → R (List α))
      (collectAny : Iter α σ → R (List α)) (count : Nat)
      (iterate : Iter α σ → CurriedArgs types (R (Option (α × σ))))
      (itr : Iter α σ) (T : TupleType) (states : ArgPack types) : R (List α) :=
    match count with
    | 0 => .ok (totupleEmpty itr states)
    | count + 1 => do
        let y ← splatArgs (iterate itr) states
        match y with
        | none => totupleError T
        | some (value, nextState) =>
            let T1 := fieldtype T 1
            let y1 := if hasType value T1 then .ok value else convert T1 value
            let y1 ← y1
            let rT ← tupleTypeTail T
            let tail ← totupleContinue hasType convert fieldtype rest collectTyped collectAny count itr rT nextState
            pure (y1 :: tail)
  termination_by 2 * count + 1
  decreasing_by all_goals simp_wf <;> omega
end

/--
Julia source: base/tuple.jl:498-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _totuple(T::Type{All32{E,N}}, itr) where {E,N}
    len = N+32
    elts = collect(E, Iterators.take(itr,len))
    if length(elts) != len
        _totuple_err(T)
    end
    (elts...,)
end
```
-/
def totupleLong {α σ : Type} [ToString TupleType] (take : Iter α σ → Nat → Iter α σ)
    (collect : TupleType → Iter α σ → R (List α))
    (T E : TupleType) (N : Nat) (itr : Iter α σ) : R (List α) := do
  let len := N + 32
  let elts ← collect E (take itr len)
  if elts.length != len then totupleError T else .ok elts


/--
Julia source: base/tuple.jl:514-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple}, itr::Array) = (itr...,)
```
-/
def totupleArrayFast {α : Type} (itr : List α) : List α := itr

/--
Julia source: base/tuple.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple}, itr::SimpleVector) = (itr...,)
```
-/
def totupleSimpleVectorFast {α : Type} (itr : List α) : List α := itr

/--
Julia source: base/tuple.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple}, itr::NamedTuple) = (itr...,)
```
-/
def totupleNamedTupleFast {α : Type} (itr : List α) : List α := itr

/--
Julia source: base/tuple.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple}, p::Pair) = (p.first, p.second)
```
-/
def totuplePairFast {α : Type} (first second : α) : List α := [first, second]

/--
Julia source: base/tuple.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_totuple(::Type{Tuple}, x::Number) = (x,) # to make Tuple(x) inferable
```
-/
def totupleNumberFast {α : Type} (x : α) : List α := [x]

/--
Julia source: base/tuple.jl:522-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findfirst_rec(f, i::Int, ::Tuple{}) = nothing
```
-/
@[simp]
def findFirstRecEmpty {α : Type} (_f : α → Bool) (_i : Nat) : Option Nat := none

/--
Julia source: base/tuple.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_findfirst_rec(f, i::Int, t::Tuple) = (@inline; f(first(t)) ? i : _findfirst_rec(f, i+1, tail(t)))
```
-/
def findFirstRec {α : Type} (f : α → Bool) (i : Nat) : List α → Option Nat
  | [] => findFirstRecEmpty f i
  | first :: rest => if f first then some i else findFirstRec f (i + 1) rest

/-!
Julia source: base/tuple.jl:524-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findfirst_loop(f::Function, t)
    for i in eachindex(t)
        f(t[i]) && return i
    end
    return nothing
end
```
-/
def findFirstLoopLocal {α : Type} (f : α → Bool) (t : List α) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 =>
      match t[i]? with
      | some value => if f value then some (i + 1) else findFirstLoopLocal f t (i + 1) fuel
      | none => none
/--
Julia source: base/tuple.jl:524-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findfirst_loop(f::Function, t)
    for i in eachindex(t)
        f(t[i]) && return i
    end
    return nothing
end
```
-/
def findFirstLoop {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  findFirstLoopLocal f t 0 t.length

/--
Julia source: base/tuple.jl:530-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(f::Function, t::Tuple) = length(t) < 32 ? _findfirst_rec(f, 1, t) : _findfirst_loop(f, t)
```
-/
def findFirstTuple {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  if t.length < 32 then findFirstRec f 1 t else findFirstLoop f t


/--
Julia source: base/tuple.jl:668-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
revargs() = ()
```
-/
@[simp]
def revargsEmpty {α : Type} : List α := []

/--
Julia source: base/tuple.jl:669-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
revargs(x, r...) = (revargs(r...)..., x)
```
-/
def revargs {α : Type} : List α → List α
  | [] => revargsEmpty
  | x :: rest => revargs rest ++ [x]

/--
Julia source: base/tuple.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(t::Tuple) = revargs(t...)
```
-/
def reverseTuple {α : Type} (t : List α) : List α := revargs t
/--
Julia source: base/tuple.jl:533-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findlast_rec(f::Function, x::Tuple)
    r = findfirst(f, reverse(x))
    return isnothing(r) ? r : length(x) - r + 1
end
```
-/
def findLastRec {α : Type} (f : α → Bool) (x : List α) : Option Nat :=
  match findFirstTuple f (reverseTuple x) with
  | none => none
  | some r => some (x.length - r + 1)

/-!
Julia source: base/tuple.jl:537-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findlast_loop(f::Function, t)
    for i in reverse(1:length(t))
        f(t[i]) && return i
    end
    return nothing
end
```
-/
def findLastLoopLocal {α : Type} (f : α → Bool) (t : List α) : Nat → Option Nat
  | 0 => none
  | i + 1 =>
      let index := i + 1
      match t[i]? with
      | some value => if f value then some index else findLastLoopLocal f t i
      | none => findLastLoopLocal f t i
/--
Julia source: base/tuple.jl:537-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findlast_loop(f::Function, t)
    for i in reverse(1:length(t))
        f(t[i]) && return i
    end
    return nothing
end
```
-/
def findLastLoop {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  findLastLoopLocal f t t.length

/--
Julia source: base/tuple.jl:532-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(f::Function, t::Tuple) = length(t) < 32 ? _findlast_rec(f, t) : _findlast_loop(f, t)
```
-/
def findLastTuple {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  if t.length < 32 then findLastRec f t else findLastLoop f t

/--
Julia source: base/tuple.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter_rec(f, xs::Tuple) = afoldl((ys, x) -> f(x) ? (ys..., x) : ys, (), xs...)
```
-/
def filterRec {E : Type} {m : Type → Type} [Monad m]
    (afoldl : (List E → E → m (List E)) → List E → List E → m (List E))
    (predicate : E → m Bool) (xs : List E) : m (List E) :=
  afoldl (fun kept x => do
    if ← predicate x then pure (kept ++ [x]) else pure kept) [] xs

/--
Julia source: base/tuple.jl:549-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter(f, t::Tuple) = length(t) < 32 ? filter_rec(f, t) : Tuple(filter(f, collect(t)))
```
-/
def filterTuple {E V : Type} {m : Type → Type} [Monad m]
    (afoldl : (List E → E → m (List E)) → List E → List E → m (List E))
    (collectTuple : List E → m V) (filterVector : (E → m Bool) → V → m V)
    (tupleConstructor : V → m (List E)) (predicate : E → m Bool) (xs : List E) : m (List E) := do
  if xs.length < 32 then filterRec afoldl predicate xs
  else tupleConstructor (← filterVector predicate (← collectTuple xs))


/--
Julia source: base/tuple.jl:554-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isequal(::Tuple{}, ::Tuple{}) = true
```
-/
@[simp]
def isequalEmpty : Bool := true

/--
Julia source: base/tuple.jl:555-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _isequal(t1::Tuple{Any,Vararg{Any}}, t2::Tuple{Any,Vararg{Any}})
    return isequal(t1[1], t2[1]) && _isequal(tail(t1), tail(t2))
end
```
-/
def isequalRec {α : Type} (ops : Ops α) : List α → List α → R Bool
  | [], [] => .ok isequalEmpty
  | a :: t, b :: s => if ops.isequal a b then isequalRec ops t s else .ok false
  | _, _ => .error (.julia (.methodError "_isequal"))

def isequalLongLoop {α : Type} (ops : Ops α) (t1 t2 : List α) : Nat → Nat → R Bool
  | _, 0 => .ok true
  | i, k + 1 => match t1[i]?, t2[i]? with
      | some a, some b => if !ops.isequal a b then .ok false else isequalLongLoop ops t1 t2 (i + 1) k
      | _, _ => bounds

/--
Julia source: base/tuple.jl:558-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _isequal(t1::Any32, t2::Any32)
    for i in eachindex(t1, t2)
        if !isequal(t1[i], t2[i])
            return false
        end
    end
    return true
end
```
-/
def isequalLong {α : Type} (ops : Ops α) (t1 t2 : List α) (i k : Nat) : R Bool := do
  let _ ← keysMany ops.mismatchIndices t1 [t2]
  isequalLongLoop ops t1 t2 i k


/--
Julia source: base/tuple.jl:568-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eq(t1::Tuple{}, t2::Tuple{}) = true
```
-/
@[simp]
def eqEmpty : Option Bool := some true

/--
Julia source: base/tuple.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eq_missing(t1::Tuple{}, t2::Tuple{}) = missing
```
-/
@[simp]
def eqMissingEmpty : Option Bool := none

/--
Julia source: base/tuple.jl:580-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _eq_missing(t1::Tuple, t2::Tuple)
    eq = t1[1] == t2[1]
    if eq === false
        return false
    else
        return _eq_missing(tail(t1), tail(t2))
    end
end
```
-/
def eqMissing {α : Type} (ops : Ops α) : List α → List α → R (Option Bool)
  | [], [] => .ok eqMissingEmpty
  | a :: t, b :: s => if ops.eq a b = some false then .ok (some false) else eqMissing ops t s
  | _, _ => bounds
/--
Julia source: base/tuple.jl:570-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _eq(t1::Tuple, t2::Tuple)
    eq = t1[1] == t2[1]
    if eq === false
        return false
    elseif ismissing(eq)
        return _eq_missing(tail(t1), tail(t2))
    else
        return _eq(tail(t1), tail(t2))
    end
end
```
-/
def eqRec {α : Type} (ops : Ops α) : List α → List α → R (Option Bool)
  | [], [] => .ok eqEmpty
  | a :: t, b :: s =>
      match ops.eq a b with
      | some false => .ok (some false)
      | none => eqMissing ops t s
      | some true => eqRec ops t s
  | _, _ => bounds


def eqLongLoop {α : Type} (ops : Ops α) (t1 t2 : List α) : Nat → Nat → Bool → R (Option Bool)
  | _, 0, anymissing => .ok (if anymissing then none else some true)
  | i, k + 1, anymissing => match t1[i]?, t2[i]? with
      | some a, some b =>
          match ops.eq a b with
          | none => eqLongLoop ops t1 t2 (i + 1) k true
          | some false => .ok (some false)
          | some true => eqLongLoop ops t1 t2 (i + 1) k anymissing
      | _, _ => bounds

/--
Julia source: base/tuple.jl:588-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _eq(t1::Any32, t2::Any32)
    anymissing = false
    for i in eachindex(t1, t2)
        eq = (t1[i] == t2[i])
        if ismissing(eq)
            anymissing = true
        elseif !eq
           return false
       end
    end
    return anymissing ? missing : true
end
```
-/
def eqLong {α : Type} (ops : Ops α) (t1 t2 : List α) (i k : Nat) (anymissing : Bool) : R (Option Bool) := do
  let _ ← keysMany ops.mismatchIndices t1 [t2]
  eqLongLoop ops t1 t2 i k anymissing

/--
Julia source: base/tuple.jl:602-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(::Tuple{}, h::UInt) = h ⊻ tuplehash_seed
```
-/
def hashEmpty (h : Nat) : Nat := h ^^^ tupleHashSeed

/--
Julia source: base/tuple.jl:603-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(t::Tuple, h::UInt) = hash(t[1], hash(tail(t), h))
```
-/
def hashTuple {α : Type} (ops : Ops α) : List α → Nat → Nat
  | [], h => h ^^^ tupleHashSeed
  | value :: rest, h => ops.hash value (hashTuple ops rest h)

def hashLongLoop {α : Type} (ops : Ops α) (t : List α) : Nat → Nat → Nat
  | 0, out => out
  | k + 1, out =>
      match t[k]? with
      | some value => hashLongLoop ops t k (ops.hash value out)
      | none => out

/--
Julia source: base/tuple.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(t::Any32, h::UInt)
    out = h ⊻ tuplehash_seed
    for i = length(t):-1:1
        out = hash(t[i], out)
    end
    return out
end
```
-/
def hashLong {α : Type} (ops : Ops α) (t : List α) (h : Nat) : Nat :=
  hashLongLoop ops t t.length (h ^^^ tupleHashSeed)

/--
Julia source: base/tuple.jl:612-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(::Tuple{}, ::Tuple{}) = false
```
-/
@[simp]
def ltEmptyEmpty : Option Bool := some false

/--
Julia source: base/tuple.jl:613-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(::Tuple{}, ::Tuple) = true
```
-/
@[simp]
def ltEmptyNonempty {α : Type} (_t : List α) : Option Bool := some true

/--
Julia source: base/tuple.jl:614-614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(::Tuple, ::Tuple{}) = false
```
-/
@[simp]
def ltNonemptyEmpty {α : Type} (_t : List α) : Option Bool := some false

/--
Julia source: base/tuple.jl:615-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function <(t1::Tuple, t2::Tuple)
    a, b = t1[1], t2[1]
    eq = (a == b)
    if ismissing(eq)
        return missing
    elseif !eq
        return a < b
    end
    return tail(t1) < tail(t2)
end
```
-/
def ltShort {α : Type} (ops : Ops α) : List α → List α → Option Bool
  | [], [] => ltEmptyEmpty
  | [], b :: s => ltEmptyNonempty (b :: s)
  | a :: t, [] => ltNonemptyEmpty (a :: t)
  | a :: t, b :: s =>
      match ops.eq a b with
      | none => none
      | some false => ops.lt a b
      | some true => ltShort ops t s

/--
Julia source: base/tuple.jl:625-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function <(t1::Any32, t2::Any32)
    n1, n2 = length(t1), length(t2)
    for i = 1:min(n1, n2)
        a, b = t1[i], t2[i]
        eq = (a == b)
        if ismissing(eq)
            return missing
        elseif !eq
           return a < b
        end
    end
    return n1 < n2
end
```
-/
def ltLong {α : Type} (ops : Ops α) (t1 t2 : List α) : Nat → Nat → Option Bool
  | _, 0 => some (decide (t1.length < t2.length))
  | i, k + 1 => match t1[i]?, t2[i]? with
      | some a, some b =>
          match ops.eq a b with
          | none => none
          | some false => ops.lt a b
          | some true => ltLong ops t1 t2 (i + 1) k
      | _, _ => some (decide (t1.length < t2.length))

/--
Julia source: base/tuple.jl:639-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(::Tuple{}, ::Tuple{}) = false
```
-/
@[simp]
def islessEmptyEmpty : Bool := false

/--
Julia source: base/tuple.jl:640-640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(::Tuple{}, ::Tuple) = true
```
-/
@[simp]
def islessEmptyNonempty {α : Type} (_t : List α) : Bool := true

/--
Julia source: base/tuple.jl:641-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(::Tuple, ::Tuple{}) = false
```
-/
@[simp]
def islessNonemptyEmpty {α : Type} (_t : List α) : Bool := false

/--
Julia source: base/tuple.jl:648-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless(t1::Tuple, t2::Tuple)
    a, b = t1[1], t2[1]
    isless(a, b) || (isequal(a, b) && isless(tail(t1), tail(t2)))
end
```
-/
def islessShort {α : Type} (ops : Ops α) : List α → List α → Bool
  | [], [] => islessEmptyEmpty
  | [], b :: s => islessEmptyNonempty (b :: s)
  | a :: t, [] => islessNonemptyEmpty (a :: t)
  | a :: t, b :: s => ops.isless a b || (ops.isequal a b && islessShort ops t s)

/--
Julia source: base/tuple.jl:652-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless(t1::Any32, t2::Any32)
    n1, n2 = length(t1), length(t2)
    for i = 1:min(n1, n2)
        a, b = t1[i], t2[i]
        if !isequal(a, b)
            return isless(a, b)
        end
    end
    return n1 < n2
end
```
-/
def islessLong {α : Type} (ops : Ops α) (t1 t2 : List α) : Nat → Nat → Bool
  | _, 0 => decide (t1.length < t2.length)
  | i, k + 1 => match t1[i]?, t2[i]? with
      | some a, some b => if !ops.isequal a b then ops.isless a b else islessLong ops t1 t2 (i + 1) k
      | _, _ => decide (t1.length < t2.length)

/--
Julia source: base/tuple.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(x::Tuple{}) = true
```
-/
def isemptyEmpty : Bool := true

/--
Julia source: base/tuple.jl:666-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(@nospecialize x::Tuple) = false
```
-/
def isemptyNonempty {α : Type} (_t : List α) : Bool := false


/--
Julia source: base/tuple.jl:681-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(v::Tuple, i::Integer)
    @boundscheck 1 <= i <= length(v) || return false
    true
end
```
-/
def isassignedTuple {α : Type} (t : List α) (i : Index) : Bool :=
  decide (1 ≤ i.value ∧ i.value ≤ t.length)

/--
Julia source: base/tuple.jl:688-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod(x::Tuple{}) = 1
```
-/
def prodEmpty : JInt .i64 := JInt.lit .i64 1

/--
Julia source: base/tuple.jl:693-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod(x::Tuple{Int, Vararg{Int}}) = *(x...)
```
-/
def prodIntTuple (multiply : List (JInt .i64) → JInt .i64) (x : List (JInt .i64)) : JInt .i64 :=
  multiply x

/--
Julia source: base/tuple.jl:696-703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sym_in(x::Symbol, itr::Tuple{Vararg{Symbol}})
    @noinline
    @_total_meta
    for y in itr
        y === x && return true
    end
    return false
end
```
-/
def symIn (x : String) (itr : List String) : Bool :=
  let rec loop : List String → Bool
    | [] => false
    | y :: rest => if y = x then true else loop rest
  loop itr

/--
Julia source: base/tuple.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x::Symbol, itr::Tuple{Vararg{Symbol}}) = sym_in(x, itr)
```
-/
def inSym (x : String) (itr : List String) : Bool := Id.run do
  return symIn x itr

/--
Julia source: base/tuple.jl:712-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(@nospecialize x::Tuple) = ()
```
-/
def emptyTuple {α : Type} (_x : List α) : List α := []

/--
Julia source: base/tuple.jl:714-714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foreach(f, itr::Tuple) = foldl((_, x) -> (f(x); nothing), itr, init=nothing)
```
-/
def foreachTuple {α β : Type} (f : α → R β) (itr : List α) : R Unit :=
  itr.foldlM (fun _ x => do let _ ← f x; pure ()) ()

/--
Julia source: base/tuple.jl:715-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foreach(f, itr::Tuple, itrs::Tuple...) = foldl((_, xs) -> (f(xs...); nothing), zip(itr, itrs...), init=nothing)
```
-/
def foreachTupleN {α β : Type} (f : List α → R β) (itr : List α)
    (itrs : List (List α)) : R Unit :=
  let tuples := itr :: itrs
  let n := (tuples.map List.length).foldl min itr.length
  let zipped := (List.range n).map (fun i => tuples.filterMap fun t => t[i]?)
  zipped.foldlM (fun _ xs => do let _ ← f xs; pure ()) ()

/--
Julia source: base/tuple.jl:717-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift((@nospecialize t::Union{Tuple{},Tuple{Any}}), @nospecialize _::Integer) = t
```
-/
def circshiftTupleSmall {α : Type} (t : List α) (_shift : Int)
    (small : t.length ≤ 1) : List α := t

/--
Julia source: base/tuple.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift(t::Tuple{Any,Any}, shift::Integer) = iseven(shift) ? t : reverse(t)
```
-/
def circshiftTupleTwo {α : Type} (iseven : Int → Bool) (t : List α) (shift : Int)
    (_length : t.length = 2) : List α :=
  if iseven shift then t else reverseTuple t

/--
Julia source: base/tuple.jl:719-724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function circshift(x::Tuple{Any,Any,Any,Vararg{Any,N}}, shift::Integer) where {N}
    @inline
    len = N + 3
    j = mod1(shift, len)
    ntuple(k -> getindex(x, k-j+ifelse(k>j,0,len)), Val(len))::Tuple
end
```
-/
def circshiftTupleLong {α : Type} (mod1 : Int → Nat → Nat)
    (ntuple : (Nat → R α) → Nat → R (List α))
    (x : List α) (shift : Int) (_length : 3 ≤ x.length) : R (List α) := do
  let len := x.length
  let j := mod1 shift len
  ntuple (fun k => getindexInt x (JInt.lit .i64 ((k : Int) - (j : Int) +
    if k > j then 0 else (len : Int)))) len


/-! Dispatch helpers for methods with recursive and Any32 source overloads. -/

def isequalBody {α : Type} (ops : Ops α) (t s : List α) : R Bool :=
  if t.length ≥ 32 then isequalLong ops t s 0 t.length else isequalRec ops t s

/--
Julia source: base/tuple.jl:553-553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(t1::Tuple, t2::Tuple) = length(t1) == length(t2) && _isequal(t1, t2)
```
-/
def isequalTuple {α : Type} (ops : Ops α) (t1 t2 : List α) : R Bool :=
  if t1.length == t2.length then isequalBody ops t1 t2 else .ok false


def eqBody {α : Type} (ops : Ops α) (t s : List α) : R (Option Bool) :=
  if t.length ≥ 32 then eqLong ops t s 0 t.length false else eqRec ops t s

/--
Julia source: base/tuple.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(t1::Tuple, t2::Tuple) = (length(t1) == length(t2)) && _eq(t1, t2)
```
-/
def eqTuple {α : Type} (ops : Ops α) (t1 t2 : List α) : R (Option Bool) :=
  if t1.length = t2.length then eqBody ops t1 t2 else .ok (some false)


def ltTupleMethod {α : Type} (ops : Ops α) (t s : List α) : Option Bool :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then ltLong ops t s 0 (min t.length s.length)
  else ltShort ops t s

def islessTuple {α : Type} (ops : Ops α) (t s : List α) : Bool :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then islessLong ops t s 0 (min t.length s.length)
  else islessShort ops t s

def hashTupleMethod {α : Type} (ops : Ops α) (t : List α) (h : Nat) : Nat :=
  if t.length ≥ 32 then hashLong ops t h else hashTuple ops t h

/-! Dispatch and recursion helpers for the source overload families. -/


def prodTupleMethod (multiply : List (JInt .i64) → JInt .i64)
    (values : List (JInt .i64)) : R (JInt .i64) :=
  match values with
  | [] => .ok prodEmpty
  | _ :: _ => .ok (prodIntTuple multiply values)



def totupleDispatch {α σ : Type} [ToString TupleType]
    (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
    (fieldtype : TupleType → Nat → TupleType) (nfields : TupleType → Nat)
    (rest0 : Iter α σ → Iter α σ) (rest1 : Iter α σ → σ → Iter α σ)
    (take : Iter α σ → Nat → Iter α σ)
    (collectTyped : TupleType → Iter α σ → R (List α))
    (collectAny : Iter α σ → R (List α))
    (T : TupleType) (itr : Iter α σ) : R (List α) :=
  match T with
  | .tuple [] => .ok (totupleEmpty itr .nil)
  | .tuple [.vararg .any none] => totupleAny (types := []) rest0 collectAny itr .nil
  | .tuple [.vararg E none] => totupleVararg (types := []) rest0 collectTyped E itr .nil
  | .tuple [.vararg E (some n)] =>
      if 32 ≤ n then totupleLong take collectTyped T E (n.toNat - 32) itr
      else totupleFixed (types := []) hasType convert fieldtype rest1 collectTyped collectAny
        (nfields T) (fun itr => itr.first) itr T .nil
  | _ => totupleFixed (types := []) hasType convert fieldtype rest1 collectTyped collectAny
      (nfields T) (fun itr => itr.first) itr T .nil

/--
Julia source: base/tuple.jl:475-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(itr) where {T<:Tuple} = _totuple(T, itr)
```
-/
def tupleFromIterator {α σ : Type} [ToString TupleType]
    (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
    (fieldtype : TupleType → Nat → TupleType) (nfields : TupleType → Nat)
    (rest0 : Iter α σ → Iter α σ) (rest1 : Iter α σ → σ → Iter α σ)
    (take : Iter α σ → Nat → Iter α σ)
    (collectTyped : TupleType → Iter α σ → R (List α))
    (collectAny : Iter α σ → R (List α))
    (T : TupleType) (itr : Iter α σ) : R (List α) := do
  let values ← totupleDispatch hasType convert fieldtype nfields rest0 rest1 take collectTyped collectAny T itr
  pure values


end JuliaLean.base.tuple

namespace JuliaLean.Multidim

/-- `isless(t1::Tuple, t2::Tuple)`, `base/tuple.jl`: `isless(a, b) || (isequal(a, b) &&
isless(tail(t1), tail(t2)))`. -/
def tupleLess : List (JuliaLean.JInt .i64) → List (JuliaLean.JInt .i64) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a.val < b.val) || (decide (a.val = b.val) && tupleLess as bs)

end JuliaLean.Multidim

namespace JuliaLean.Multidim

/-- `fill_to_length(t, 0, Val(N))`: pads with zeros; a longer tuple is an
`ArgumentError` ("input tuple of length ..., requested ..."). -/
def fillToLength (t : List Int) (N : Nat) : R (List Int) :=
  if t.length > N then .error .argumentError else .ok (t ++ List.replicate (N - t.length) 0)

end JuliaLean.Multidim

/-!
Model of Julia tuples (`base/tuple.jl`, `base/ntuple.jl`, the tuple methods of
`base/range.jl`, `base/operators.jl`, `base/array.jl`, `base/bitarray.jl`).

A tuple is a `List α` of its elements. Methods whose body differs between short
tuples and `Any32` tuples (32 or more elements) are modelled by both bodies and
a dispatcher on the lengths. Loops over `1:n` are index recursions (`go i k`
visits `i+1, ..., i+k` in Julia's one-based numbering).

Exceptions: `Err.jl` wraps the shared `JlError`; `TypeError`, `FieldError` and
`ErrorException` have their own constructors because `Core` has none. Element
comparisons are abstract (`Ops`), with `none` for `missing`.
-/

namespace JuliaLean.Tuples



/-- `getindex(t, i::Int)` (`base/tuple.jl:33`) and `getindex(t, i::Integer) =
getfield(t, convert(Int, i))` (`base/tuple.jl:34`); `Bool <: Integer` takes the
second method. -/
def getindex {α : Type} (t : List α) : Idx → R α
  | .int ty v =>
    if ty = .i64 then getfield t v.val
    else do let j ← liftJ (JInt.convert (IntTy.i64.name) .i64 v.val); getfield t j.val
  | .bool b => do let j ← liftJ (JInt.convert (IntTy.i64.name) .i64 (if b then 1 else 0)); getfield t j.val

/-- `setindex(x, v, i::Integer)`, `base/tuple.jl:55-64`: `1 <= i <= length(x)`
(exact mixed-type comparison), then `_setindex` rebuilds the tuple with
`ifelse(j == i, v, args[j])`. -/
def setindex {α : Type} (t : List α) (v : α) (i : Idx) : R (List α) :=
  if 1 ≤ i.val ∧ i.val ≤ t.length then
    .ok ((List.range t.length).zipWith (fun (j : Nat) a => if ((j : Int) + 1) = i.val then v else a) t)
  else bounds

/-- `get(t, i::Integer, default)`, `base/tuple.jl:40`. -/
def get {α : Type} (t : List α) (i : Idx) (d : α) : R α :=
  if 1 ≤ i.val ∧ i.val ≤ t.length then getindex t i else .ok d

/-- `isassigned(v::Tuple, i::Integer)`, `base/tuple.jl:681-684`. -/
def isassigned {α : Type} (t : List α) (i : Idx) : R Bool :=
  .ok (decide (1 ≤ i.val ∧ i.val ≤ t.length))

/-- The `Vector` methods with a `Bool` scalar index: `to_index(i::Bool)` throws
(`base/indices.jl:259`); `get`/`isassigned` reject `Bool` the same way. -/
def vecBoolIndex {β : Type} : R β := argErr "invalid index: true of type Bool"

/-! ## Front, tail, first, last -/

/-- `_front`, `base/tuple.jl:348-353`. -/
def frontRec {α : Type} : List α → R (List α)
  | [] => argErr "Cannot call front on an empty tuple."
  | [_] => .ok []
  | v :: t => do let r ← frontRec t; pure (v :: r)

/-- `index loop` helper: `(t[i+1], ..., t[i+k])` (one-based), or `BoundsError`. -/
def readRange {α : Type} (t : List α) : Nat → Nat → R (List α)
  | _, 0 => .ok []
  | i, k + 1 => do
    let a ← getfield t (i + 1)
    let r ← readRange t (i + 1) k
    pure (a :: r)

/-- `front(t::Any32)`, `base/tuple.jl:380-384`: `ntuple(i -> getfield(t, i), n-1)`. -/
def frontAny32 {α : Type} (t : List α) : R (List α) := readRange t 0 (t.length - 1)

/-- `front(t)`: `base/tuple.jl:344-347`, `375-378` (exactly 32), `380-384` (longer). -/
def front {α : Type} (t : List α) : R (List α) :=
  if t.length > 32 then frontAny32 t else frontRec t

/-- `tail(x) = argtail(x...)`, `tail(()) = ArgumentError`, `base/essentials.jl:523,541-542`. -/
def tail {α : Type} : List α → R (List α)
  | [] => argErr "Cannot call tail on an empty tuple."
  | _ :: r => .ok r

/-- `first(()) = ArgumentError`, `first(t) = t[1]`, `base/tuple.jl:270-271`. -/
def first {α : Type} : List α → R α
  | [] => argErr "tuple must be non-empty"
  | t => getfield t 1

/-- `last(a) = a[end]` (`base/abstractarray.jl`), `lastindex(t) = length(t)`, `base/tuple.jl:30`. -/
def last {α : Type} (t : List α) : R α := getfield t t.length

/-! ## ntuple, fill_to_length, reverse -/


/-- `revargs`, `base/tuple.jl:668-671`. -/
def revargs {α : Type} : List α → List α
  | [] => []
  | x :: r => revargs r ++ [x]


/-! ## map -/

/-- One-argument `map`, `base/tuple.jl:358-362`. -/
def map1Rec {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | [a] => [f a]
  | [a, b] => [f a, f b]
  | [a, b, c] => [f a, f b, f c]
  | a :: r => f a :: map1Rec f r

/-- `map(f, t::Any32)`, `base/tuple.jl:394-401`: `A[i] = f(t[i])` for `i = 1:n`. -/
def map1Loop {α β : Type} (f : α → β) (t : List α) : Nat → Nat → List β
  | _, 0 => []
  | i, k + 1 => match t[i]? with
    | some a => f a :: map1Loop f t (i + 1) k
    | none => []

def map1 {α β : Type} (f : α → β) (t : List α) : List β :=
  if t.length ≥ 32 then map1Loop f t 0 t.length else map1Rec f t

/-- Two-argument `map`, `base/tuple.jl:403-411`. -/
def map2Rec {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | [a], [b] => [f a b]
  | [a, a'], [b, b'] => [f a b, f a' b']
  | a :: r, b :: s => f a b :: map2Rec f r s

/-- `map(f, t::Any32, s::Any32)`, `base/tuple.jl:412-419`, `n = min(length(t), length(s))`. -/
def map2Loop {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : Nat → Nat → List γ
  | _, 0 => []
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => f a b :: map2Loop f t s (i + 1) k
    | _, _ => []

def map2 {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : List γ :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then map2Loop f t s 0 (min t.length s.length)
  else map2Rec f t s

/-- Three-argument `map`, `base/tuple.jl:421-431` (`anyempty`, `heads`, `tails`). -/
def map3Rec {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | a :: r, b :: s, c :: u => f a b c :: map3Rec f r s u
  | _, _, _ => []

/-- `map(f, t1::Any32, t2::Any32, ts::Any32...)`, `base/tuple.jl:432-439`. -/
def map3Loop {α β γ δ : Type} (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) :
    Nat → Nat → List δ
  | _, 0 => []
  | i, k + 1 => match t[i]?, s[i]?, u[i]? with
    | some a, some b, some c => f a b c :: map3Loop f t s u (i + 1) k
    | _, _, _ => []

def map3 {α β γ δ : Type} (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) : List δ :=
  if t.length ≥ 32 ∧ s.length ≥ 32 ∧ u.length ≥ 32 then
    map3Loop f t s u 0 (min t.length (min s.length u.length))
  else map3Rec f t s u

/-! ## find, filter, in -/

/-- `_findfirst_rec`, `base/tuple.jl:522-523`. -/
def findfirstRec {α : Type} (f : α → Bool) (i : Nat) : List α → Option Nat
  | [] => none
  | a :: r => if f a then some i else findfirstRec f (i + 1) r

/-- `_findfirst_loop`, `base/tuple.jl:524-529`. -/
def findfirstLoop {α : Type} (f : α → Bool) (t : List α) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, k + 1 => match t[i]? with
    | some a => if f a then some (i + 1) else findfirstLoop f t (i + 1) k
    | none => none

/-- `findfirst(f::Function, t::Tuple)`, `base/tuple.jl:530`. -/
def findfirst {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  if t.length < 32 then findfirstRec f 1 t else findfirstLoop f t 0 t.length

/-- `_findlast_loop`, `base/tuple.jl:537-542`: `for i in reverse(1:length(t))`
(`i = k, k-1, ..., 1`). -/
def findlastLoop {α : Type} (f : α → Bool) (t : List α) : Nat → Option Nat
  | 0 => none
  | k + 1 => match t[k]? with
    | some a => if f a then some (k + 1) else findlastLoop f t k
    | none => none

/-- `findlast(f::Function, t::Tuple)`, `base/tuple.jl:532-536`: the short path
reverses the tuple and calls `findfirst` on it. -/
def findlast {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  if t.length < 32 then
    match findfirst f (revargs t) with
    | none => none
    | some r => some (t.length - r + 1)
  else findlastLoop f t t.length

/-- `filter_rec` (`afoldl`), `base/tuple.jl:546`. -/
def filterRec {α : Type} (f : α → Bool) (t : List α) : List α :=
  t.foldl (fun ys x => if f x then ys ++ [x] else ys) []

/-- `filter(f, t::Tuple)`, `base/tuple.jl:549`: long tuples use `filter` on `collect(t)`. -/
def filter {α : Type} (f : α → Bool) (t : List α) : List α :=
  if t.length < 32 then filterRec f t else t.filter f

/-- Three-valued `|`: `false | missing === missing`. -/
def or3 : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- `_in_tuple`, `base/operators.jl:1463-1471`; `eq` is three-valued `==`. -/
def inTupleRec {α : Type} (eq : α → α → Option Bool) (x : α) : List α → Option Bool → Option Bool
  | [], result => result
  | a :: r, result =>
    let v := eq a x
    if v = some true then some true else inTupleRec eq x r (or3 result v)

/-- `any(f, itr)` with three-valued logic (`base/reduce.jl`), used by
`in(x, itr::Any32)` through `invoke(in, Tuple{Any,Any}, ...)`, `base/operators.jl:1474`. -/
def anyGo {α : Type} (f : α → Option Bool) : List α → Bool → Option Bool
  | [], anymissing => if anymissing then none else some false
  | a :: r, anymissing => match f a with
    | none => anyGo f r true
    | some true => some true
    | some false => anyGo f r anymissing

/-- `in(x, itr::Tuple)`, `base/operators.jl:1459,1474`. -/
def inTuple {α : Type} (eq : α → α → Option Bool) (x : α) (t : List α) : Option Bool :=
  if t.length ≥ 32 then anyGo (fun y => eq y x) t false else inTupleRec eq x t (some false)

/-- `findall(pred::Fix2{typeof(in)}, x::Tuple) = _findin(x, pred.x)`,
`base/array.jl:2967`; `_findin(a, b) = _findin(a, Set(b))` and
`ai in b && push!(ind, i)` (`base/array.jl:2903-2910`). Membership in a `Set`
is `isequal` membership. -/
def findallIn {α : Type} (isequal : α → α → Bool) (t : List α) (b : List α) : List Nat :=
  ((List.range t.length).zip t).filterMap fun (i, a) =>
    if b.any (isequal a) then some (i + 1) else none

/-- `findall(x -> x in b, t)` for a `Vector` `b` with `Bool`-valued `==`:
`in(x, itr) = any(==(x), itr)`, `base/operators.jl:1456`. -/
def findallPred {α : Type} (eq : α → α → Bool) (t : List α) (b : List α) : List Nat :=
  ((List.range t.length).zip t).filterMap fun (i, a) =>
    if b.any (fun y => eq y a) then some (i + 1) else none

/-! ## Integer unit ranges -/

/-- `t[r]` for `r::UnitRange{Int}` with `first(r) = a` and `length(r) = len`
(`last(r) = a + len - 1` lies in `Int`), `base/range.jl:451-466`. -/
def getindexUnitRange {α : Type} (t : List α) (a : Int) (len : Nat) : R (List α) := do
  let generic := (List.range len).mapM fun (k : Nat) => getfield t (a + k)
  if len ≤ 10 then (List.range len).mapM fun (k : Nat) => getfield t (((k : Int) + 1) + a - 1)
  else if a = 1 then
    if a + len - 1 = t.length then pure t
    else if a + len - 1 = t.length - 1 then front t
    else if a + len - 1 = t.length - 2 then do let f ← front t; front f
    else generic
  else if a + len - 1 = t.length then
    if a = 2 then tail t
    else if a = 3 then do let r ← tail t; tail r
    else generic
  else generic

/-- `UnitRange(a, b)` for `Int` endpoints as `(first, length)` (`last` is
`a - 1` when `b < a`); assumes `b - a + 1` does not overflow. -/
def unitRange (a b : JInt .i64) : Int × Nat :=
  (a.val, if b.val ≥ a.val then (b.val - a.val + 1).toNat else 0)

/-- `t[a:b]` for `Int` endpoints. -/
def getindexColon {α : Type} (t : List α) (a b : JInt .i64) : R (List α) :=
  getindexUnitRange t (unitRange a b).1 (unitRange a b).2

/-- `t[b]` for a `UnitRange{Bool}` `b` (first value `lo`, length `len`): it
dispatches to the `AbstractUnitRange` method of `base/range.jl:451-466`, where
`i + first(r) - 1` computes with `first(r)` as an integer. -/
def getindexBoolRange {α : Type} (t : List α) (lo : Bool) (len : Nat) : R (List α) :=
  getindexUnitRange t (if lo then 1 else 0) len

/-- The values of a `UnitRange{Bool}` with first value `lo` and length `len ≤ 2`. -/
def boolRangeValues (lo : Bool) (len : Nat) : List Bool :=
  (List.range len).map fun k => if lo then true else k == 1

/-- Logical indexing `t[b::AbstractArray{Bool,1}]`, `base/tuple.jl:37`:
`length(b) == length(t) ? getindex(t, findall(b)) : BoundsError`. -/
def getindexLogical {α : Type} (t : List α) (b : List Bool) : R (List α) :=
  if b.length = t.length then
    ((List.range b.length).zip b).filterMap (fun (i, x) => if x then some (i + 1) else none)
      |>.mapM fun i => getfield t i
  else bounds

/-! ## split_rest and rest -/

/-- `_split_tuple(t, n, i) = (t[i:n], t[n+1:end])` and
`split_rest(t::Tuple, n, i) = _split_tuple(t, length(t)-n, Int(i))`,
`base/tuple.jl:265-267`. Both slices are `UnitRange{Int}` indexing. -/
def splitRestTuple {α : Type} (t : List α) (n i : JInt .i64) : R (List α × List α) := do
  let m : JInt .i64 := JInt.lit .i64 t.length - n
  let x ← getindexColon t i m
  let y ← getindexColon t (m + JInt.lit .i64 1) (JInt.lit .i64 t.length)
  pure (x, y)

/-- `_check_length_split_rest`, `base/tuple.jl:255-259`. -/
def checkLengthSplitRest (len : Nat) (n : JInt .i64) : R Unit :=
  if (len : Int) < n.val then argErr "The iterator only contains len elements, but at least n were requested."
  else .ok ()

/-- `split_rest(v::Vector, n, i)`: `rest(a, i) = a[i:end]` (`base/tuple.jl:212`),
then `_split_rest(a::Vector, n)` (`base/bitarray.jl:1932-1937`): check the
length, `last_n = a[end-n+1:end]`, `resize!(a, length(a) - n)`. Growing with
`resize!` leaves the new elements uninitialised (`none`). -/
def splitRestVector {α : Type} (v : List α) (n i : JInt .i64) : R (List (Option α) × List α) := do
  let r ← if i.val ≤ v.length then (if 1 ≤ i.val then pure (v.drop (i.val - 1).toNat) else bounds)
    else pure []
  checkLengthSplitRest r.length n
  let lastN := if n.val ≥ 0 then r.drop (r.length - n.val.toNat) else []
  let frontPart := if n.val ≥ 0 then (r.take (r.length - n.val.toNat)).map some
    else r.map some ++ List.replicate n.val.natAbs none
  pure (frontPart, lastN)

/-- `rest(t::Tuple, i)`, `base/tuple.jl:207-211`. -/
def restTuple {α : Type} (t : List α) (i : JInt .i64) : R (List α) :=
  ntupleInt (fun x => x) (JInt.lit .i64 t.length - i + JInt.lit .i64 1).val >>= fun ks =>
    ks.mapM fun (x : Nat) => getfield t (JInt.lit .i64 x + i - JInt.lit .i64 1).val

/-- `indexed_iterate(t::Tuple, i, state) = (getfield(t, i), i+1)`, `base/tuple.jl:161`. -/
def indexedIterate {α : Type} (t : List α) (i : Nat) : R (α × Nat) := do
  let a ← getfield t i
  pure (a, i + 1)

/-- Lowering of `a, b..., c = t`: `indexed_iterate`, then
`split_rest(t, 1, state)`, then `indexed_iterate(last_n, 1)`. -/
def destructureMid {α : Type} (t : List α) : R (α × List α × α) := do
  let (a, s) ← indexedIterate t 1
  let (b, l) ← splitRestTuple t (JInt.lit .i64 1) (JInt.lit .i64 s)
  let (c, _) ← indexedIterate l 1
  pure (a, b, c)

/-! ## prod -/

/-- `prod(x::Tuple{}) = 1` and `prod(x::Tuple{Int, Vararg{Int}}) = *(x...)`,
`base/tuple.jl:688,693`. -/
def prodTuple (t : List (JInt .i64)) : R (JInt .i64) :=
  match t with
  | [] => .ok (JInt.lit .i64 1)
  | a :: r => .ok (r.foldl (· * ·) a)

/-- `prod(f, t) = mapreduce(f, mul_prod, t)` for `Int` elements: an empty
tuple has element type `Union{}` and `reduce_empty(mul_prod, Union{})` throws
(`base/reduce.jl:389-390`). -/
def prodGeneric (t : List (JInt .i64)) : R (JInt .i64) :=
  match t with
  | [] => argErr "reducing over an empty collection is not allowed; consider supplying `init` to the reducer"
  | a :: r => .ok (r.foldl (· * ·) a)

/-! ## Comparison and hashing -/

/-- Element operations: `isequal`, `isless`, three-valued `==` and `<`
(`none` is `missing`), and `hash(x, h)`. -/
structure Ops (α : Type) where
  isequal : α → α → Bool
  isless : α → α → Bool
  eq : α → α → Option Bool
  lt : α → α → Option Bool
  hash : α → Nat → Nat

variable {α : Type}

/-- `_isequal`, `base/tuple.jl:554-557`. -/
def isequalRec (o : Ops α) : List α → List α → Bool
  | [], [] => true
  | a :: r, b :: s => o.isequal a b && isequalRec o r s
  | _, _ => false

/-- `_isequal(t1::Any32, t2::Any32)`, `base/tuple.jl:558-565`. -/
def isequalLoop (o : Ops α) (t s : List α) : Nat → Nat → Bool
  | _, 0 => true
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => if !o.isequal a b then false else isequalLoop o t s (i + 1) k
    | _, _ => true

/-- `isequal(t1::Tuple, t2::Tuple)`, `base/tuple.jl:553`. -/
def isequal (o : Ops α) (t s : List α) : Bool :=
  t.length == s.length &&
    (if t.length ≥ 32 then isequalLoop o t s 0 t.length else isequalRec o t s)

/-- `_eq_missing`, `base/tuple.jl:569,580-587`. -/
def eqMissing (o : Ops α) : List α → List α → Option Bool
  | a :: r, b :: s => if o.eq a b = some false then some false else eqMissing o r s
  | _, _ => none

/-- `_eq`, `base/tuple.jl:568-579`. -/
def eqRec (o : Ops α) : List α → List α → Option Bool
  | a :: r, b :: s => match o.eq a b with
    | some false => some false
    | none => eqMissing o r s
    | some true => eqRec o r s
  | _, _ => some true

/-- `_eq(t1::Any32, t2::Any32)`, `base/tuple.jl:588-599`. -/
def eqLoop (o : Ops α) (t s : List α) : Nat → Nat → Bool → Option Bool
  | _, 0, anymissing => if anymissing then none else some true
  | i, k + 1, anymissing => match t[i]?, s[i]? with
    | some a, some b => match o.eq a b with
      | none => eqLoop o t s (i + 1) k true
      | some false => some false
      | some true => eqLoop o t s (i + 1) k anymissing
    | _, _ => if anymissing then none else some true

/-- `==(t1::Tuple, t2::Tuple)`, `base/tuple.jl:567`. -/
def eq (o : Ops α) (t s : List α) : Option Bool :=
  if t.length = s.length then
    (if t.length ≥ 32 then eqLoop o t s 0 t.length false else eqRec o t s)
  else some false

/-- `<` on tuples, `base/tuple.jl:612-624`. -/
def ltRec (o : Ops α) : List α → List α → Option Bool
  | [], [] => some false
  | [], _ :: _ => some true
  | _ :: _, [] => some false
  | a :: r, b :: s => match o.eq a b with
    | none => none
    | some false => o.lt a b
    | some true => ltRec o r s

/-- `<(t1::Any32, t2::Any32)`, `base/tuple.jl:625-637`. -/
def ltLoop (o : Ops α) (t s : List α) : Nat → Nat → Option Bool
  | _, 0 => some (decide (t.length < s.length))
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => match o.eq a b with
      | none => none
      | some false => o.lt a b
      | some true => ltLoop o t s (i + 1) k
    | _, _ => some (decide (t.length < s.length))

def lt (o : Ops α) (t s : List α) : Option Bool :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then ltLoop o t s 0 (min t.length s.length) else ltRec o t s

/-- `isless` on tuples, `base/tuple.jl:639-651`. -/
def islessRec (o : Ops α) : List α → List α → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: r, b :: s => o.isless a b || (o.isequal a b && islessRec o r s)

/-- `isless(t1::Any32, t2::Any32)`, `base/tuple.jl:652-661`. -/
def islessLoop (o : Ops α) (t s : List α) : Nat → Nat → Bool
  | _, 0 => decide (t.length < s.length)
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => if !o.isequal a b then o.isless a b else islessLoop o t s (i + 1) k
    | _, _ => decide (t.length < s.length)

def isless (o : Ops α) (t s : List α) : Bool :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then islessLoop o t s 0 (min t.length s.length)
  else islessRec o t s

/-- `isless(a::Tuple{BitInteger,BitInteger}, b::Tuple{BitInteger,BitInteger})`,
`base/operators.jl:248-249` (non-short-circuit `|` and `&`). -/
def islessPair (o : Ops α) (a1 a2 b1 b2 : α) : Bool :=
  o.isless a1 b1 || (o.isequal a1 b1 && o.isless a2 b2)

/-- `cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)`, `base/operators.jl`. -/
def cmp (o : Ops α) (t s : List α) : Int :=
  if isless o t s then -1 else if isless o s t then 1 else 0

def tuplehashSeed : Nat := 0x77cfa1eef01bca90

/-- `hash(t::Tuple, h)`, `base/tuple.jl:602-603`. -/
def hashRec (o : Ops α) : List α → Nat → Nat
  | [], h => h ^^^ tuplehashSeed
  | a :: r, h => o.hash a (hashRec o r h)

/-- `hash(t::Any32, h)`, `base/tuple.jl:604-610`: `for i = length(t):-1:1`. -/
def hashLoop (o : Ops α) (t : List α) : Nat → Nat → Nat
  | 0, out => out
  | k + 1, out => match t[k]? with
    | some a => hashLoop o t k (o.hash a out)
    | none => out

def hash (o : Ops α) (t : List α) (h : Nat) : Nat :=
  if t.length ≥ 32 then hashLoop o t t.length (h ^^^ tuplehashSeed) else hashRec o t h

end JuliaLean.Tuples

namespace JuliaLean.Tuples

/-- `sym_in`, `base/tuple.jl:696-703`. -/
def symIn (x : String) (itr : List String) : Bool := itr.any (· == x)

end JuliaLean.Tuples

namespace JuliaLean.Tuples

variable {α : Type}

/-- `circshift(t::Tuple, shift::Integer)`, `base/tuple.jl:717-724`: tuples of length 0
and 1 are returned; length 2 gives `iseven(shift) ? t : reverse(t)` (`reverse(t::Tuple) =
revargs(t...)`, `base/tuple.jl:671`); longer tuples use `len = N + 3`,
`j = mod1(shift, len)` and `ntuple(k -> getindex(x, k-j+ifelse(k>j,0,len)), Val(len))`
(`base/ntuple.jl:65-72`), with `k::Int`, the exact mixed comparison `k > j`
(`base/int.jl:578`, `base/promotion.jl`) and the wrapping mixed `-` and `+`. -/
def circshiftTuple (t : List α) (ty : IntTy) (shift : JInt ty) : R (List α) :=
  match t with
  | [] => .ok []
  | [a] => .ok [a]
  | [a, b] => do
    let e ← iseven shift
    pure (if e then [a, b] else revargs [a, b])
  | t@(_ :: _ :: _ :: _) => do
    let len : JInt64 := JInt.lit .i64 t.length
    let j ← mod1 shift len
    (List.range len.val.toNat).mapM fun (k : Nat) =>
      let kI : JInt64 := JInt.lit .i64 ((k : Int) + 1)
      let off : JInt64 := if kI.val > j.val then JInt.lit .i64 0 else len
      getindex t (.int _ (addMixed (subMixed kI j) off))

end JuliaLean.Tuples


/-!
Value-level methods of `base/tuple.jl` (master `bbfa0ce4150`) that the `Tuples`
area does not model: indexing helpers, iteration, `rest` and `split_rest`,
`n`-argument `map`, `foreach`, `sym_in`. A tuple is the `List α` of its
elements (the `Tuples` convention). An iterator is a finite list of the values
it produces (with a flag for `IteratorSize(itr) == IsInfinite()`), a vector is
the `List α` of its elements indexed from 1.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds argErr liftJ Idx getindex getindexColon
  getindexLogical ntupleInt splitRestVector checkLengthSplitRest restTuple indexedIterate
  fillToLength)

namespace Tup

variable {α β : Type}

/-- `length(t) = nfields(t)`, `firstindex(t) = 1`, `lastindex(t) = length(t)`,
`base/tuple.jl:28-30`. -/
def length (t : List α) : Nat := t.length
def firstindex (_ : List α) : Int := 1
def lastindex (t : List α) : Int := t.length

/-- `d == 1` for an `Integer` `d` (exact mixed comparison; `true == 1`). -/
def idxIsOne : Idx → Bool
  | .int _ v => v.val == 1
  | .bool b => b

/-- `size(t, d::Integer) = (d == 1) ? length(t) : throw(ArgumentError(...))`,
`base/tuple.jl:31`. -/
def size (t : List α) (d : Idx) : R Nat :=
  if idxIsOne d then .ok t.length else argErr "invalid tuple dimension"

/-- `axes(t) = (OneTo(length(t)),)` (`base/tuple.jl:32`) and
`keys(t) = OneTo(length(t))` (`base/tuple.jl:75`): the length of the `OneTo`. -/
def axes (t : List α) : List Nat := [t.length]
def keys (t : List α) : Nat := t.length

/-- `__safe_getindex(t, i::Int) = getfield(t, i, false)`, `base/tuple.jl:35`: the
access is unchecked; `none` marks an out-of-bounds read (undefined behaviour). -/
def safeGetindex (t : List α) (i : Int) : Option α :=
  if 1 ≤ i then t[(i - 1).toNat]? else none

/-- `getindex(t, r::AbstractArray{<:Any,1}) = (eltype(t)[t[ri] for ri in r]...,)`,
`base/tuple.jl:36`, for an index vector `r` of `Integer` values (not `Bool`s,
whose vectors take the method of line 37). -/
def getindexVec (t : List α) (r : List Idx) : R (List α) := r.mapM (getindex t)

/-- `getindex(t, c::Colon) = t`, `base/tuple.jl:38`. -/
def getindexColonAll (t : List α) : List α := t

/-- `i in 1:length(t)` for an `Integer` `i`. -/
def idxInRange (i : Idx) (n : Nat) : Bool := decide (1 ≤ i.val ∧ i.val ≤ n)

/-- `get(f::Callable, t::Tuple, i::Integer) = i in 1:length(t) ? getindex(t, i) : f()`,
`base/tuple.jl:41`; `f()` is the thunk `f`. -/
def getF (f : Unit → R α) (t : List α) (i : Idx) : R α :=
  if idxInRange i t.length then getindex t i else f ()

/-- `iterate(t::Tuple, i::Int=1) = (1 <= i <= length(t)) ? (t[i], i + 1) : nothing`,
`base/tuple.jl:69-73`. -/
def iterate (t : List α) (i : Int := 1) : R (Option (α × Int)) :=
  if 1 ≤ i ∧ i ≤ t.length then do
    let x ← getfield t i
    pure (some (x, i + 1))
  else .ok none

/-- `Int(i)` for an `Integer` `i`: `InexactError` outside `Int`. -/
def idxToInt : Idx → R (JInt .i64)
  | .int _ v => liftJ (JInt.convert (IntTy.i64.name) .i64 v.val)
  | .bool b => .ok (JInt.lit .i64 (if b then 1 else 0))

/-- `prevind(t, i::Integer) = Int(i)-1` and `nextind(t, i::Integer) = Int(i)+1`,
`base/tuple.jl:145-146` (wrapping `Int` arithmetic). -/
def prevind (_ : List α) (i : Idx) : R (JInt .i64) := do
  let j ← idxToInt i
  pure (j - JInt.lit .i64 1)
def nextind (_ : List α) (i : Idx) : R (JInt .i64) := do
  let j ← idxToInt i
  pure (j + JInt.lit .i64 1)

/-- `keys(t::Tuple, t2::Tuple...)`, `base/tuple.jl:148-157`: `OneTo(length(t))`
when every `t2` has the length of `t`, else `DimensionMismatch` (`none`). The
tuples are given by their lengths. -/
def keysMany (lent : Nat) (lens : List Nat) : Option Nat :=
  if lens.all (· == lent) then some lent else none

/-- `indexed_iterate(a::Union{Array,Memory}, i::Int, state=1) = (a[i], i+1)`,
`base/tuple.jl:162` (checked `a[i]`). -/
def indexedIterateArray (a : List α) (i : Int) : R (α × Int) := do
  let x ← getfield a i
  pure (x, i + 1)

/-- A generic iterator: `iterate(I)` returns `first`, and `iterate(I, state)`
returns `next state`. -/
structure Iter (α σ : Type) where
  first : Option (α × σ)
  next : σ → Option (α × σ)

/-- `indexed_iterate(I, i)`, `base/tuple.jl:163-167`: `iterate(I)`, and
`BoundsError` when it returns `nothing`. -/
def indexedIterateGen {σ : Type} (I : Iter α σ) (_ : Int) : R (α × σ) :=
  match I.first with
  | none => bounds
  | some x => .ok x

/-- `indexed_iterate(I, i, state)`, `base/tuple.jl:168-172`. -/
def indexedIterateGenState {σ : Type} (I : Iter α σ) (_ : Int) (state : σ) : R (α × σ) :=
  match I.next state with
  | none => bounds
  | some x => .ok x

/-- `rest(t::Tuple) = t`, `base/tuple.jl:206`. -/
def restAll (t : List α) : List α := t

/-- `rest(a::Union{Array,Memory,Core.SimpleVector}, i=1) = a[(i::Int):end]`,
`base/tuple.jl:212`. -/
def restArray (a : List α) (i : JInt .i64) : R (List α) :=
  getindexColon a i (JInt.lit .i64 a.length)

/-- `rest(itr, state...) = Iterators.rest(itr, state...)`, `base/tuple.jl:213`:
the lazy iterator that starts from `state` (or from the beginning). -/
def restIter {σ : Type} (I : Iter α σ) (state : Option σ) : Iter α σ :=
  match state with
  | none => I
  | some s => { first := I.next s, next := I.next }

/-- The values an iterator produces from `start`, with at most `fuel` steps. -/
def Iter.collectFrom {σ : Type} (I : Iter α σ) : Nat → Option (α × σ) → List α
  | 0, _ => []
  | _ + 1, none => []
  | k + 1, some (x, s) => x :: I.collectFrom k (I.next s)

/-- `_split_rest(a::Union{AbstractArray, Core.SimpleVector}, n::Int)`,
`base/tuple.jl:260-263`: `_check_length_split_rest(length(a), n)`, then
`(a[begin:end-n], a[end-n+1:end])` with checked `UnitRange{Int}` slices. -/
def splitRestArray (a : List α) (n : JInt .i64) : R (List α × List α) := do
  checkLengthSplitRest a.length n
  let len : JInt .i64 := JInt.lit .i64 a.length
  let x ← getindexColon a (JInt.lit .i64 1) (len - n)
  let y ← getindexColon a (len - n + JInt.lit .i64 1) len
  pure (x, y)

/-- `split_rest(itr, n::Int, state...)`, `base/tuple.jl:248-254`: `ArgumentError`
for an infinite iterator; otherwise `_split_rest(rest(itr, state...), n)`, which
collects the remaining values `rest` into a `Vector` and splits that with the
`Vector` method of `base/bitarray.jl` (`splitRestVector`). -/
def splitRestIter (infinite : Bool) (rest : List α) (n : JInt .i64) :
    R (List (Option α) × List α) :=
  if infinite then argErr "Cannot split an infinite iterator in the middle."
  else splitRestVector rest n (JInt.lit .i64 1)

/-- `safe_tail(t::Tuple) = tail(t)`, `safe_tail(t::Tuple{}) = ()`, `base/tuple.jl:323-324`. -/
def safeTail : List α → List α
  | [] => []
  | _ :: r => r

/-! ### `map` with `n ≥ 3` tuples, `base/tuple.jl:421-439` -/

/-- `heads(ts::Tuple...) = map(t -> t[1], ts)`, `base/tuple.jl:421`. -/
def heads : List (List α) → R (List α)
  | [] => .ok []
  | t :: ts => do
    let x ← getfield t 1
    let r ← heads ts
    pure (x :: r)

/-- `tails(ts::Tuple...) = map(tail, ts)`, `base/tuple.jl:422`. -/
def tails : List (List α) → R (List (List α))
  | [] => .ok []
  | t :: ts => do
    let x ← JuliaLean.Tuples.tail t
    let r ← tails ts
    pure (x :: r)

/-- `anyempty(x::Tuple{}, xs...) = true`, `anyempty(x::Tuple, xs...) = anyempty(xs...)`,
`anyempty() = false`, `base/tuple.jl:424-426`. -/
def anyempty : List (List α) → Bool
  | [] => false
  | [] :: _ => true
  | (_ :: _) :: xs => anyempty xs

/-- `map(f, ::Tuple{}, ::Tuple{}...) = ()` (`base/tuple.jl:423`) and
`map(f, t1, t2, ts...)` (`base/tuple.jl:427-431`): stop when any tuple is
empty, else `f(heads...)` followed by the map of the tails. `fuel` is the
recursion depth (a tuple length bound). -/
def mapRec (f : List α → β) : Nat → List (List α) → R (List β)
  | 0, _ => .ok []
  | k + 1, ts =>
    if anyempty ts then .ok [] else do
      let h ← heads ts
      let tl ← tails ts
      let r ← mapRec f k tl
      pure (f h :: r)

/-- `map(f, t1::Any32, t2::Any32, ts::Any32...)`, `base/tuple.jl:432-439`:
`n = min(length(t1), length(t2), minimum(length, ts))`, then
`A[i] = f(t1[i], t2[i], map(t -> t[i], ts)...)` for `i = 1:n`. -/
def mapLoop (f : List α → β) (ts : List (List α)) : R (List β) :=
  let n := (ts.map List.length).foldl min (ts.headD []).length
  (List.range n).mapM fun (i : Nat) => do
    let xs ← ts.mapM fun t => getfield t ((i : Int) + 1)
    pure (f xs)

/-- `map` over `ts = [t1, t2, ...]` (at least 3 tuples): the `Any32` method when
every tuple has at least 32 elements, else the recursive one. -/
def mapN (f : List α → β) (ts : List (List α)) : R (List β) :=
  if ts.all (fun t => t.length ≥ 32) then mapLoop f ts
  else mapRec f ((ts.map List.length).foldl max 0) ts

/-! ### `foreach`, `sym_in`, `isempty`, `empty` -/

/-- `foreach(f, itr::Tuple) = foldl((_, x) -> (f(x); nothing), itr, init=nothing)`,
`base/tuple.jl:714`. The effect of `f(x)` is a state update `f s x`. -/
def foreach {σ : Type} (f : σ → α → σ) (s : σ) (t : List α) : σ :=
  t.foldl f s

/-- `zip(itr, itrs...)`: tuples of the `k`-th elements, up to the shortest. -/
def zipN : List (List α) → Nat → List (List α)
  | _, 0 => []
  | ts, k + 1 =>
    match ts.mapM List.head? with
    | some h => if ts.isEmpty then [] else h :: zipN (ts.map List.tail) k
    | none => []

/-- `foreach(f, itr::Tuple, itrs::Tuple...) = foldl((_, xs) -> (f(xs...); nothing),
zip(itr, itrs...), init=nothing)`, `base/tuple.jl:715`. -/
def foreachN {σ : Type} (f : σ → List α → σ) (s : σ) (t : List α) (ts : List (List α)) : σ :=
  (zipN (t :: ts) t.length).foldl f s

/-- `sym_in(x::Symbol, itr::Tuple{Vararg{Symbol}})`, `base/tuple.jl:696-703`:
the loop `for y in itr; y === x && return true; end; return false`. Symbols
are strings. -/
def symInLoop (x : String) : List String → Bool
  | [] => false
  | y :: r => if y == x then true else symInLoop x r

/-- `in(x::Symbol, itr::Tuple{Vararg{Symbol}}) = sym_in(x, itr)`, `base/tuple.jl:704`. -/
def inSym (x : String) (itr : List String) : Bool := symInLoop x itr

/-- `isempty(x::Tuple{}) = true`, `isempty(x::Tuple) = false`, `base/tuple.jl:665-666`. -/
def isempty : List α → Bool
  | [] => true
  | _ :: _ => false

/-- `empty(x::Tuple) = ()`, `base/tuple.jl:712`. -/
def empty (_ : List α) : List α := []

end Tup

open Tup

end JuliaLean.SortTuplesCov


/-! Faithful models for the remaining type and construction methods in
`base/tuple.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

mutual
  inductive TupleTy where
    | bottom | any | atom (name : String)
    | tuple (params : List TupleParam)
    | union (a b : TupleTy)
    | unionAll (body : TupleTy)

  /-- A tuple parameter is a type, a value parameter, or `Vararg{T,N}`. -/
  inductive TupleParam where
    | type (ty : TupleTy)
    | value
    | vararg (ty : TupleTy) (length : Option Int)
end

/-- `_counttuple(::Type{<:NTuple{N,Any}})`, `base/tuple.jl:23`. -/
def countTupleSpecific : TupleTy → Option Int
  | .tuple [.vararg .any (some n)] => some n
  | _ => none

/-- `_counttuple(::Type) = nothing`, `base/tuple.jl:24`. -/
def countTupleFallback (_ : TupleTy) : Option Int := none

def unwrapVararg : TupleParam → TupleParam
  | .vararg t _ => .type t
  | p => p

def paramType : TupleParam → Option TupleTy
  | .type t | .vararg t _ => some t
  | .value => none

/-- `_compute_eltype`, `base/tuple.jl:291-313`.  `free` models
`has_free_typevars`; `join` is Julia's `promote_typejoin`. -/
def computeTupleEltype (join : TupleTy → TupleTy → TupleTy) (free : TupleTy → Bool) :
    (t : TupleTy) → TupleTy
  | .union a b =>
    if free (.union a b) then .any else join a b
  | .tuple [] => if free (.tuple []) then .any else .bottom
  | .tuple (p :: ps) =>
    if free (.tuple (p :: ps)) then .any else
    match paramType (unwrapVararg p) with
    | none => .bottom
    | some first => ps.foldl (fun r p =>
        match r, paramType (unwrapVararg p) with
        | .any, _ => .any
        | _, none => .bottom
        | _, some e => join e r) first
  | .unionAll body =>
    if free (.unionAll body) then .any else body
  | t => if free t then .any else .bottom

/-- `_eltype_ntuple`, `base/tuple.jl:279`: a defined type parameter is used;
an empty vacuous match is Bottom; otherwise `_compute_eltype` recovers the join. -/
def eltypeNTuple (join : TupleTy → TupleTy → TupleTy) (free : TupleTy → Bool) :
    TupleTy → TupleTy
  | t@(.tuple [.vararg e _]) => e
  | t@(.tuple []) => .bottom
  | t => computeTupleEltype join free t

/-- `eltype(::Type{<:Tuple})`, `base/tuple.jl:282-290`. -/
def tupleEltype (join : TupleTy → TupleTy → TupleTy) (free : TupleTy → Bool)
    (ntupleSignature : TupleTy → Bool) (t : TupleTy) : TupleTy :=
  match t with
  | .tuple [] => .bottom
  | _ => if ntupleSignature t then eltypeNTuple join free t else computeTupleEltype join free t

/-- `keytype(t::Tuple)` and `keytype(::Type{<:Tuple})`,
`base/tuple.jl:316-317`. -/
def tupleKeytypeValue (_ : List TupleTy) : TupleTy := .atom "Int64"
def tupleKeytypeType (_ : TupleTy) : TupleTy := .atom "Int64"

/-- `valtype(t::Tuple)` and `valtype(::Type{<:Tuple})`,
`base/tuple.jl:319-320`. -/
def tupleValtypeValue (join : TupleTy → TupleTy → TupleTy) (ts : List TupleTy) : TupleTy :=
  computeTupleEltype join (fun _ => false) (.tuple (ts.map .type))
def tupleValtypeType (join : TupleTy → TupleTy → TupleTy) (t : TupleTy) : TupleTy :=
  computeTupleEltype join (fun _ => false) t

/-- `tuple_type_tail`, `base/tuple.jl:453-468`. -/
def tupleTypeTail : TupleTy → Jl TupleTy
  | .unionAll body => tupleTypeTail body |>.map .unionAll
  | .union a b => do pure (.union (← tupleTypeTail a) (← tupleTypeTail b))
  | .tuple [.vararg t (some n)] => .ok (.tuple [.vararg t (some (n - 1))])
  | .tuple (_ :: ps) => .ok (.tuple ps)
  | .tuple [] => .ok (.tuple [])
  | _ => .error (.methodError "tuple_type_tail")

/-! ### Tuple construction from iterators -/

/-- `(::Type{T})(x::Tuple)`, `base/tuple.jl:470`. -/
def tupleTypeCall {V : Type} (isT : List V → Bool) (convert : List V → Jl (List V))
    (x : List V) : Jl (List V) :=
  if isT x then .ok x else convert x

/-- `Tuple(x::Ref)` and `Tuple(x::Array{T,0})`, `base/tuple.jl:472-473`. -/
def tupleRef {V : Type} (x : V) : List V := [x]
def tupleArray0 {V : Type} (x : V) : List V := [x]

/-- `_totuple_err`, `base/tuple.jl:479-482`. -/
def toTupleError {V : Type} : Jl (List V) :=
  .error (.argumentError "too few elements for tuple type")

/-- Recursive `_totuple(::Type{T}, itr, state...)`, `base/tuple.jl:484-495`.
The target field types are processed left to right and conversion happens only
when the value is not already of the requested type. -/
def toTupleFixed {V : Type} (hasType : V → TupleTy → Bool)
    (convert : TupleTy → V → Jl V) : List TupleTy → List V → Jl (List V)
  | [], _ => .ok []
  | _ :: _, [] => toTupleError
  | t :: ts, x :: xs => do
    let y ← if hasType x t then .ok x else convert t x
    pure (y :: (← toTupleFixed hasType convert ts xs))

/-- Iterative `All32` method, `base/tuple.jl:498-505`. -/
def toTupleLong {V : Type} (convert : V → Jl V) (length : Nat) (xs : List V) : Jl (List V) := do
  let ys ← (xs.take length).mapM convert
  if ys.length = length then .ok ys else toTupleError

/-- Vararg and unparameterized methods, `base/tuple.jl:509-511`. -/
def toTupleVararg {V : Type} (convert : V → Jl V) (xs : List V) : Jl (List V) :=
  xs.mapM convert
def toTupleAny {V : Type} (xs : List V) : List V := xs

inductive TupleSource (V : Type) where
  | array (xs : List V) | simpleVector (xs : List V) | namedTuple (xs : List V)
  | pair (first second : V) | number (x : V)

/-- Fast `_totuple(::Type{Tuple}, ...)` methods, `base/tuple.jl:514-518`. -/
def toTupleFast {V : Type} : TupleSource V → List V
  | .array xs | .simpleVector xs | .namedTuple xs => xs
  | .pair a b => [a, b]
  | .number x => [x]

end JuliaLean.SortTuplesCov

namespace JuliaLean.SortTuplesCov.NTup

open JuliaLean
open JuliaLean.Tuples (R argErr)
variable {α T : Type}


/-- `T(itr)` for the fixed tuple type `Tuple{tys...}` (`_totuple`,
`base/tuple.jl:475-495`): the first `length(tys)` values, each converted;
`ArgumentError` when there are fewer. -/
def totupleFixed (conv : T → α → R α) : List T → List α → R (List α)
  | [], _ => .ok []
  | _ :: _, [] => argErr "too few elements for tuple type"
  | ty :: tys, x :: xs => do
    let y ← conv ty x
    let ys ← totupleFixed conv tys xs
    pure (y :: ys)

end JuliaLean.SortTuplesCov.NTup
