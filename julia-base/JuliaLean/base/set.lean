import JuliaLean.Core
import JuliaLean.base.dict
import JuliaLean.base.int
import JuliaLean.base.abstractset
import JuliaLean.base.array
import JuliaLean.base.iterators
import JuliaLean.base.tuple
import JuliaLean.Registry.Types

/-!
# Model of `base/set.jl`

Typed models of the methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Dictionary operations use the source-mirrored `JuliaLean.base.dict` model. Calls into iterator,
array, promotion, and user-extensible methods are typed interfaces. Methods requiring mutable
container aliasing or runtime Julia type joins remain visible untranslated with their reason.
-/

namespace JuliaLean.base.set

open JuliaLean

abbrev DictState (K V : Type) := JuliaLean.base.dict.DictState K V
abbrev DictError := JuliaLean.base.dict.DictError
abbrev DictResult := JuliaLean.base.dict.DictResult

inductive Error where
  | dictionary (error : DictError)
  | julia (error : JlError)
  | assertion (message : String)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure SetModel (K : Type) where
  dict : DictState K Unit

structure DictRuntime (K : Type) where
  hash : K → JInt .u64
  equal : K → K → Bool
  tablesz : Nat → Nat
  maxValues : Nat
  cld : JInt .i64 → JInt .i64
  fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat
  unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)
  unsetValue : Nat → (Nat → Option Unit) → Nat → (Nat → Option Unit)
  copySlots : Nat → (Nat → Nat) → Nat → Nat
  copyKeys : Nat → (Nat → Option K) → Nat → Option K
  copyValues : Nat → (Nat → Option Unit) → Nat → Option Unit

structure KeySetModel (K : Type) where
  dict : DictState K Unit


structure FiniteTrace (α : Type) where
  values : List α
  hasLength : Bool
  length : Nat
  hasEltype : Bool
  eltype : Nat
  defaultEltype : Nat

structure VectorModel (α : Type) where
  eltype : Nat
  firstIndex : Int
  values : List α

structure TypeOps (α : Type) where
  typeof : α → Nat
  isConcrete : Nat → Bool
  isBottom : Nat → Bool
  subtype : Nat → Nat → Bool
  typejoin : Nat → Nat → Nat
  convertSet : Nat → SetModel α → Result (SetModel α)
  convertVector : Nat → VectorModel α → Result (VectorModel α)

def uniqueListLoop {α : Type} (inBang : α → SetModel α → Result (Bool × SetModel α))
    (pushVector : VectorModel α → α → Result (VectorModel α)) :
    List α → VectorModel α → SetModel α → Result (VectorModel α)
  | [], out, _ => .ok out
  | x :: xs, out, seen => do
    let (present, seen) ← inBang x seen
    let out ← if present then .ok out else pushVector out x
    uniqueListLoop inBang pushVector xs out seen

def alluniqueInsertLoop {α : Type} (inBang : α → SetModel α → Result (Bool × SetModel α)) :
    List α → SetModel α → Result (Bool × SetModel α)
  | [], seen => .ok (true, seen)
  | x :: xs, seen => do
    let (present, seen) ← inBang x seen
    if present then .ok (false, seen) else alluniqueInsertLoop inBang xs seen

def fromDict {K : Type} (dict : DictState K Unit) : SetModel K := ⟨dict⟩

def emptySet {K : Type} : SetModel K := fromDict (JuliaLean.base.dict.dictEmpty K Unit)

def dictResult {α : Type} (r : DictResult α) : Result α := r.mapError Error.dictionary

def setIsEmpty {K : Type} (s : SetModel K) : Bool := JuliaLean.base.dict.isempty s.dict

def setLength {K : Type} (s : SetModel K) : JInt .i64 :=
  JInt.wrap .i64 (Int.ofNat (JuliaLean.base.dict.length s.dict))

def setIn {K : Type} (ops : DictRuntime K) (x : K) (s : SetModel K) : Result Bool :=
  dictResult (JuliaLean.base.dict.haskey ops.hash ops.equal s.dict x)

def setInBang {K Q : Type} (ops : DictRuntime K) (convert : Q → DictResult K)
    (x : Q) (s : SetModel K) : Result (Bool × SetModel K) := do
  let xT ← dictResult (convert x)
  let (index, shortHash, dict) ← dictResult
    (JuliaLean.base.dict.htKeyindex2 ops.hash ops.equal ops.tablesz s.dict xT)
  if index > 0 then .ok (true, fromDict dict)
  else
    let (_, dict) ← dictResult
      (JuliaLean.base.dict.setindexAt ops.hash ops.tablesz dict () xT (-index).toNat shortHash)
    .ok (false, fromDict dict)

def setPush {K Q : Type} (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv Q K)
    (x : Q) (s : SetModel K) : Result (SetModel K) := do
  let valueConv : JuliaLean.base.dict.ValueConv Unit Unit := ⟨some, fun _ => .ok ()⟩
  fromDict <$> dictResult (JuliaLean.base.dict.setindexConv ops.hash ops.equal ops.tablesz
    keyConv valueConv s.dict () x)

def setDelete {K : Type} (ops : DictRuntime K) (x : K) (s : SetModel K) : Result (SetModel K) :=
  fromDict <$> dictResult (JuliaLean.base.dict.deleteKey ops.hash ops.equal ops.unsetKey ops.unsetValue s.dict x)

def setTypedCopy {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K :=
  fromDict (JuliaLean.base.dict.dictCopy ops.copySlots ops.copyKeys ops.copyValues s.dict)

def setCopyMutable {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K := setTypedCopy ops s

def setCopy {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K := setCopyMutable ops s

def setEmptyBang {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K :=
  fromDict (JuliaLean.base.dict.emptyBang ops.fillSlots ops.unsetKey ops.unsetValue s.dict)

def setRehash {K : Type} (ops : DictRuntime K) (s : SetModel K) : Result (SetModel K) :=
  fromDict <$> dictResult (JuliaLean.base.dict.rehash ops.hash ops.tablesz s.dict s.dict.size)

def setSizehint {K : Type} (ops : DictRuntime K) (n : JInt .i64) (shrink : Bool)
    (s : SetModel K) : Result (SetModel K) :=
  fromDict <$> dictResult (JuliaLean.base.dict.sizehint ops.hash ops.tablesz ops.maxValues ops.cld s.dict n shrink)

def setIterate {K : Type} (s : SetModel K) (state : Option Nat) : DictResult (Option (K × Nat)) :=
  JuliaLean.base.dict.iteratePart s.dict .keys (state.getD s.dict.idxfloor)

def setEmptyTyped {K : Type} (_typeToken : Nat) : SetModel K := emptySet

def setEmptymutable {S K : Type} (_s : S) : SetModel K := emptySet

def setEmptyAbstract {S K : Type} (s : S) (_typeToken : Nat) : SetModel K := setEmptymutable s

def setSimilarFor {S K : Type} (c : S) (typeToken : Nat) : SetModel K := setEmptyAbstract c typeToken

def checkCount (count : Int) : Jl (JInt .i64) :=
  if count < 0 then
    .error (.domainError ("`count` must not be negative (got " ++ toString count ++ ")"))
  else JInt.convert .i64 (min count (IntTy.max .i64))



def setPopDefaultModel {K : Type} (ops : DictRuntime K) (x default : K) (s : SetModel K) :
    Result (K × SetModel K) := do
  let index ← dictResult (JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict x)
  if index > 0 then
    let key ← dictResult (JuliaLean.base.dict.keyAt s.dict index.toNat)
    let dict := JuliaLean.base.dict.deleteAt ops.unsetKey ops.unsetValue s.dict index.toNat
    .ok (key, fromDict dict)
  else .ok (default, s)

def setPopKeyModel {K : Type} (ops : DictRuntime K) (x : K) (s : SetModel K) :
    Result (K × SetModel K) := do
  let index ← dictResult (JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict x)
  if index < 1 then .error (.dictionary .keyError)
  else
    let key ← dictResult (JuliaLean.base.dict.keyAt s.dict index.toNat)
    let dict := JuliaLean.base.dict.deleteAt ops.unsetKey ops.unsetValue s.dict index.toNat
    .ok (key, fromDict dict)

def setPopAnyModel {K : Type} (isEmpty : SetModel K → Bool) (ops : DictRuntime K)
    (s : SetModel K) : Result (K × SetModel K) := do
  if isEmpty s then .error (.julia (.argumentError "set must be non-empty"))
  else
    let ((key, _), dict) ← dictResult
      (JuliaLean.base.dict.popAny ops.unsetKey ops.unsetValue s.dict)
    .ok (key, fromDict dict)

def setKeyTraceLoop {K : Type} (iterate : SetModel K → Option Nat → DictResult (Option (K × Nat)))
    (s : SetModel K) : Nat → Nat → Result (List K)
  | 0, _ => .ok []
  | n + 1, index => do
    match ← dictResult (iterate s (some index)) with
    | none => .ok []
    | some (key, next) => return key :: (← setKeyTraceLoop iterate s n next)

def setKeyTrace {K : Type} (iterate : SetModel K → Option Nat → DictResult (Option (K × Nat)))
    (s : SetModel K) : Result (List K) := do
  match ← dictResult (iterate s none) with
  | none => .ok []
  | some (key, next) => return key :: (← setKeyTraceLoop iterate s s.dict.size next)

def setDeleteMany {K : Type} (delete : K → SetModel K → Result (SetModel K)) :
    List K → SetModel K → Result (SetModel K)
  | [], s => .ok s
  | x :: xs, s => do
    let s ← delete x s
    setDeleteMany delete xs s

def setDiffFilterLoop {K : Type} (contains : K → SetModel K → Result Bool)
    (delete : K → SetModel K → Result (SetModel K)) (t : SetModel K) :
    List K → SetModel K → Result (SetModel K)
  | [], s => .ok s
  | x :: xs, s => do
    let s ← if ← contains x t then delete x s else .ok s
    setDiffFilterLoop contains delete t xs s

def setDiffModel {K : Type}
    (iterate : SetModel K → Option Nat → DictResult (Option (K × Nat)))
    (contains : K → SetModel K → Result Bool)
    (delete : K → SetModel K → Result (SetModel K)) (s t : SetModel K) : Result (SetModel K) := do
  if (JInt.wrap .i64 (2 * (Int.ofNat s.dict.count))).val < (setLength t).val then
    setDiffFilterLoop contains delete t (← setKeyTrace iterate s) s
  else
    setDeleteMany delete (← setKeyTrace iterate t) s

def setHashFold {K : Type} (hash : K → JInt .u64) (values : List K) : JInt .u64 :=
  values.foldl (fun acc x => JuliaLean.base.int.xor_int acc (hash x))
    (JInt.lit .u64 0x852ada37cfe8e0ce)

def vectorWriteAt {α : Type} (v : VectorModel α) (index : Int) (value : α) : VectorModel α :=
  let offset := (index - v.firstIndex).toNat
  { v with values := v.values.take offset ++ [value] ++ v.values.drop (offset + 1) }

def vectorResizeTo {α : Type} (v : VectorModel α) (length : Nat) : VectorModel α :=
  { v with values := v.values.take length }

def uniqueBangCompactList {A K : Type} (f : A → K) (contains : K → SetModel K → Result Bool)
    (insert : K → SetModel K → Result (SetModel K)) (isA : K → Nat → Bool)
    (typeOf : K → Nat) (typejoin : Nat → Nat → Nat) (convertSet : Nat → SetModel K → Result (SetModel K)) :
    List A → Int → VectorModel A → SetModel K → Nat → Result (VectorModel A)
  | [], current, a, _, _ => .ok (vectorResizeTo a ((current - a.firstIndex + 1).toNat))
  | x :: xs, current, a, seen, seenType => do
    let y := f x
    if ← contains y seen then uniqueBangCompactList f contains insert isA typeOf typejoin convertSet xs current a seen seenType
    else
      let current := current + 1
      let a := vectorWriteAt a current x
      if isA y seenType then
        let seen ← insert y seen
        uniqueBangCompactList f contains insert isA typeOf typejoin convertSet xs current a seen seenType
      else
        let seenType := typejoin (typeOf y) seenType
        let seen ← convertSet seenType seen
        let seen ← insert y seen
        uniqueBangCompactList f contains insert isA typeOf typejoin convertSet xs current a seen seenType

def uniqueBangCompactLoop {A K : Type} (f : A → K) (contains : K → SetModel K → Result Bool)
    (insert : K → SetModel K → Result (SetModel K)) (isA : K → Nat → Bool)
    (typeOf : K → Nat) (typejoin : Nat → Nat → Nat) (convertSet : Nat → SetModel K → Result (SetModel K))
    (a : VectorModel A) (current i : Int) (seen : SetModel K) (seenType : Nat) :
    Result (VectorModel A) :=
  uniqueBangCompactList f contains insert isA typeOf typejoin convertSet
    (a.values.drop (i - a.firstIndex).toNat) current a seen seenType

def groupedUniqueLoop {α : Type} (equal : α → α → Bool) (a : VectorModel α) :
    List α → Int → α → Nat → VectorModel α
  | [], _, _, count => vectorResizeTo a count
  | x :: xs, index, previous, count =>
    if equal x previous then groupedUniqueLoop equal a xs index previous count
    else
      let index := index + 1
      groupedUniqueLoop equal (vectorWriteAt a index x) xs index x (count + 1)


def replacePairsValue {α : Type} (equal : α → α → Bool) : List (α × α) → α → α
  | [], x => x
  | (old, new) :: rest, x => if equal old x then new else replacePairsValue equal rest x

def replaceArrayLoop {α : Type} (f : α → Result α) (same : α → α → Bool)
    (source : List α) (index first : Int) (destination : VectorModel α)
    (replaceAll : Bool) (limit changed : Nat) : Result (VectorModel α) := do
  match source with
  | [] => .ok destination
  | x :: xs =>
    if index < first then .error (.assertion "invalid vector index")
    else if !replaceAll && changed >= limit then
      let destination := vectorWriteAt destination index x
      replaceArrayLoop f same xs (index + 1) first destination false limit changed
    else
      let y ← f x
      let destination := vectorWriteAt destination index y
      let changed := changed + if same x y then 0 else 1
      replaceArrayLoop f same xs (index + 1) first destination replaceAll limit changed

structure DictReplaceRuntime (K V : Type) where
  hash : K → JInt .u64
  equal : K → K → Bool
  tablesz : Nat → Nat
  unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)
  unsetValue : Nat → (Nat → Option V) → Nat → (Nat → Option V)


def replaceDictLoop {K V : Type} (ops : DictReplaceRuntime K V)
    (new : (K × V) → DictResult (K × V)) (same : (K × V) → (K × V) → Bool)
    (count : Nat) : Nat → Nat → DictState K V → Nat → List (K × V) → DictResult (DictState K V × List (K × V))
  | 0, _, t, _, news => .ok (t, news)
  | _fuel + 1, 0, t, _changed, news => .ok (t, news)
  | fuel + 1, index, t, changed, news => do
    let key ← JuliaLean.base.dict.keyAt t index
    let value ← JuliaLean.base.dict.valAt t index
    let oldPair := (key, value)
    let newPair ← new oldPair
    let (t, changed, news) ←
      if same oldPair newPair then .ok (t, changed, news) else
        if ops.equal key newPair.1 then
          let t := JuliaLean.base.dict.DictState.mk t.size t.slots
            (JuliaLean.base.dict.updateAt t.keys index (some newPair.1))
            (JuliaLean.base.dict.updateAt t.vals index (some newPair.2))
            t.ndel t.count (JuliaLean.base.dict.bumpAge t.age) t.idxfloor t.maxprobe t.popcursor
          .ok (t, changed + 1, news)
        else
          .ok (JuliaLean.base.dict.deleteAt ops.unsetKey ops.unsetValue t index,
            changed + 1, news ++ [newPair])
    if changed == count then .ok (t, news)
    else
      let next := if index == 2 ^ 63 - 1 then 0 else JuliaLean.base.dict.skipDeleted t (index + 1)
      replaceDictLoop ops new same count fuel next t changed news

def replaceDictFinish {K V : Type} (ops : DictReplaceRuntime K V)
    (t : DictState K V) : List (K × V) → DictResult (DictState K V)
  | [] => .ok t
  | (key, value) :: rest => do
    let t ← JuliaLean.base.dict.setindexAny ops.hash ops.equal ops.tablesz t value key
    replaceDictFinish ops t rest

def replaceDictModel {K V A : Type} (ops : DictReplaceRuntime K V)
    (new : (K × V) → DictResult (K × V)) (same : (K × V) → (K × V) → Bool)
    (_source : A) (t : DictState K V) (count : Nat) : DictResult (DictState K V) := do
  if count == 0 then .ok t
  else
    let (index, t) := JuliaLean.base.dict.skipDeletedFloor t
    let (t, news) ← replaceDictLoop ops new same count (t.size + 1) index t 0 []
    replaceDictFinish ops t news
/--
Julia source: base/set.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global _Set(dict::Dict{T,Nothing}) where {T} = new{T}(dict)
```
-/
def setFromDict {K : Type} (dict : DictState K Unit) : SetModel K := fromDict dict

/--
Julia source: base/set.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Set{T}() where {T} = _Set(Dict{T,Nothing}())
```
-/
def setConstructorEmpty {K : Type} (_typeToken : Nat) : SetModel K := setEmptyTyped 0

/--
Julia source: base/set.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Set{T}(s::Set{T}) where {T} = _Set(Dict{T,Nothing}(s.dict))
```
-/
def setConstructorCopy {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K := setTypedCopy ops s

/--
Julia source: base/set.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Set{T}(itr) where {T} = union!(Set{T}(), itr)
```
-/
def setConstructorIterator {K Q : Type} (unionBang : SetModel K → List Q → Result (SetModel K))
    (elements : List Q) : Result (SetModel K) := unionBang emptySet elements

/--
Julia source: base/set.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Set() = Set{Any}()
```
-/
def setConstructorAny : SetModel Unit := emptySet

/--
Julia source: base/set.jl:50-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Set{T}(s::KeySet{T, <:Dict{T}}) where {T}
    d = s.dict
    slots = copy(d.slots)
    keys = copy(d.keys)
    vals = similar(d.vals, Nothing)
    _Set(Dict{T,Nothing}(slots, keys, vals, d.ndel, d.count, d.age, d.idxfloor, d.maxprobe, d.popcursor))
end
```
-/
def setConstructorKeySet {K : Type} (ops : DictRuntime K) (s : KeySetModel K) : SetModel K :=
  let d := s.dict
  let slots := ops.copySlots d.size d.slots
  let keys := ops.copyKeys d.size d.keys
  let vals : Nat → Option Unit := fun _ => none
  fromDict (JuliaLean.base.dict.dictRaw d.size slots keys vals d.ndel d.count d.age d.idxfloor d.maxprobe d.popcursor)

/--
Julia source: base/set.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Set(itr) = _Set(itr, IteratorEltype(itr))
```
-/
def setConstructorDispatch {K : Type} (hasEltype : Bool) (typed unknown : List K → Result (SetModel K))
    (elements : List K) : Result (SetModel K) := if hasEltype then typed elements else unknown elements

/--
Julia source: base/set.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_Set(itr, ::HasEltype) = Set{eltype(itr)}(itr)
```
-/
def setConstructorHasEltype {K : Type} (typed : List K → Result (SetModel K))
    (elements : List K) : Result (SetModel K) := typed elements

/--
Julia source: base/set.jl:61-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _Set(itr, ::EltypeUnknown)
    T = @default_eltype(itr)
    (isconcretetype(T) || T === Union{}) || return grow_to!(Set{T}(), itr)
    return Set{T}(itr)
end
```
-/
def setConstructorUnknown {K : Type} (isConcrete isBottom : Bool)
    (typed : List K → Result (SetModel K)) (grow : SetModel K → List K → Result (SetModel K))
    (elements : List K) : Result (SetModel K) :=
  if isConcrete || isBottom then typed elements else grow emptySet elements

/--
Julia source: base/set.jl:67-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(s::AbstractSet{T}, ::Type{U}=T) where {T,U} = emptymutable(s, U)
```
-/
def setEmptyMethod {S K : Type} (s : S) (typeToken : Nat) : SetModel K := setEmptyAbstract s typeToken

/--
Julia source: base/set.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(s::AbstractSet{T}, ::Type{U}=T) where {T,U} = Set{U}()
```
-/
def setEmptymutableMethod {S K : Type} (s : S) : SetModel K := setEmptymutable s

/--
Julia source: base/set.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractSet, ::Type{T}, itr, isz, len) where {T} = empty(c, T)
```
-/
def setSimilarForMethod {S K : Type} (c : S) (typeToken : Nat) : SetModel K := setEmptyMethod c typeToken

/--
Julia source: base/set.jl:75-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, s::Set)
    if isempty(s)
        if get(io, :typeinfo, Any) == typeof(s)
            print(io, "Set()")
        else
            show(io, typeof(s))
            print(io, "()")
        end
    else
        print(io, "Set(")
        show_vector(io, s)
        print(io, ')')
    end
end
```
-/
def setShowMethod {K IO : Type} (print : IO → String → IO) (showType : IO → Nat → IO)
    (showVector : IO → SetModel K → IO) (typeofSet : SetModel K → Nat)
    (matchesType : IO → Nat → Bool) (io : IO) (s : SetModel K) : IO :=
  if setIsEmpty s then
    if matchesType io (typeofSet s) then print io "Set()"
    else print (showType io (typeofSet s)) "()"
  else print (showVector (print io "Set(") s) ")"

/--
Julia source: base/set.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(s::Set) = isempty(s.dict)
```
-/
def setIsEmptyMethod {K : Type} (s : SetModel K) : Bool := setIsEmpty s

/--
Julia source: base/set.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(s::Set)  = length(s.dict)
```
-/
def setLengthMethod {K : Type} (s : SetModel K) : JInt .i64 := setLength s

/--
Julia source: base/set.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x, s::Set) = haskey(s.dict, x)
```
-/
def setInMethod {K : Type} (ops : DictRuntime K) (x : K) (s : SetModel K) : Result Bool := setIn ops x s

/--
Julia source: base/set.jl:125-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function in!(x, s::AbstractSet)
    x ∈ s ? true : (push!(s, x); false)
end
```
-/
def setInBangAbstractMethod {K S : Type} (contains : K → S → Result Bool)
    (push : S → K → Result S) (x : K) (s : S) : Result (Bool × S) := do
  if ← contains x s then .ok (true, s)
  else
    let s ← push s x
    .ok (false, s)

/--
Julia source: base/set.jl:129-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function in!(x, s::Set)
    xT = convert(eltype(s), x)
    idx, sh = ht_keyindex2_shorthash!(s.dict, xT)
    idx > 0 && return true
    _setindex!(s.dict, nothing, xT, -idx, sh)
    return false
end
```
-/
def setInBangMethod {K Q : Type} (ops : DictRuntime K) (convert : Q → DictResult K)
    (x : Q) (s : SetModel K) : Result (Bool × SetModel K) := setInBang ops convert x s

/--
Julia source: base/set.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(s::Set, x) = (s.dict[x] = nothing; s)
```
-/
def setPushMethod {K Q : Type} (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv Q K)
    (x : Q) (s : SetModel K) : Result (SetModel K) := setPush ops keyConv x s

/--
Julia source: base/set.jl:139-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(s::Set, x, default)
    dict = s.dict
    index = ht_keyindex(dict, x)
    if index > 0
        @inbounds key = dict.keys[index]
        _delete!(dict, index)
        return key
    else
        return default
    end
end
```
-/
def setPopDefaultMethod {K : Type} (ops : DictRuntime K) (x default : K) (s : SetModel K) :
    Result (K × SetModel K) := setPopDefaultModel ops x default s

/--
Julia source: base/set.jl:151-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(s::Set, x)
    index = ht_keyindex(s.dict, x)
    index < 1 && throw(KeyError(x))
    result = @inbounds s.dict.keys[index]
    _delete!(s.dict, index)
    result
end
```
-/
def setPopKeyMethod {K : Type} (ops : DictRuntime K) (x : K) (s : SetModel K) :
    Result (K × SetModel K) := setPopKeyModel ops x s

/--
Julia source: base/set.jl:159-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(s::Set)
    isempty(s) && throw(ArgumentError("set must be non-empty"))
    return pop!(s.dict)[1]
end
```
-/
def setPopAnyMethod {K : Type} (isEmpty : SetModel K → Bool) (ops : DictRuntime K)
    (s : SetModel K) : Result (K × SetModel K) := setPopAnyModel isEmpty ops s

/--
Julia source: base/set.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
delete!(s::Set, x) = (delete!(s.dict, x); s)
```
-/
def setDeleteMethod {K : Type} (ops : DictRuntime K) (x : K) (s : SetModel K) :
    Result (SetModel K) := setDelete ops x s

/--
Julia source: base/set.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(s::Set) = copymutable(s)
```
-/
def setCopyMethod {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K := setCopyMutable ops s

/--
Julia source: base/set.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(s::Set{T}) where {T} = Set{T}(s)
```
-/
def setCopyMutableTyped {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K := setTypedCopy ops s

/--
Julia source: base/set.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(s::AbstractSet{T}) where {T} = Set{T}(s)
```
-/
def setCopyMutableAbstract {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K :=
  setTypedCopy ops s

/--
Julia source: base/set.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizehint!(s::Set, newsz::Integer; shrink::Bool=true) = (sizehint!(s.dict, newsz; shrink); s)
```
-/
def setSizehintMethod {K : Type} {t : IntTy} (ops : DictRuntime K)
    (convert : JInt t → Jl (JInt .i64)) (shrink : Bool) (s : SetModel K) (newsize : JInt t) :
    Result (SetModel K) := do
  let n ← (convert newsize).mapError Error.julia
  setSizehint ops n shrink s

/--
Julia source: base/set.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty!(s::Set) = (empty!(s.dict); s)
```
-/
def setEmptyBangMethod {K : Type} (ops : DictRuntime K) (s : SetModel K) : SetModel K := setEmptyBang ops s

/--
Julia source: base/set.jl:174-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rehash!(s::Set) = (rehash!(s.dict); s)
```
-/
def setRehashMethod {K : Type} (ops : DictRuntime K) (s : SetModel K) : Result (SetModel K) := setRehash ops s

/--
Julia source: base/set.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(s::Set, i...)       = iterate(KeySet(s.dict), i...)
```
-/
def setIterateMethod {K : Type} (s : SetModel K) (state : Option Nat) : DictResult (Option (K × Nat)) :=
  setIterate s state

/--
Julia source: base/set.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds Iterators.only(s::Set) = Iterators._only(s, first)
```
-/
def setOnlyMethod {K : Type} (only : SetModel K → (SetModel K → Result K) → Result K)
    (first : SetModel K → Result K) (s : SetModel K) : Result K := only s first

/--
Julia source: base/set.jl:187-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setdiff!(s::Set, t::Set)
    if 2 * length(s) < length(t)
        for x in s
            x in t && delete!(s, x)
        end
    else
        for x in t
            delete!(s, x)
        end
    end
    return s
end
```
-/
def setdiffMethod {K : Type}
    (iterate : SetModel K → Option Nat → DictResult (Option (K × Nat)))
    (contains : K → SetModel K → Result Bool)
    (delete : K → SetModel K → Result (SetModel K)) (s t : SetModel K) : Result (SetModel K) :=
  setDiffModel iterate contains delete s t

/--
Julia source: base/set.jl:224-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unique(itr)
    if isa(IteratorEltype(itr), HasEltype)
        T = eltype(itr)
        out = Vector{T}()
        seen = Set{T}()
        for x in itr
            !in!(x, seen) && push!(out, x)
        end
        return out
    end
    T = @default_eltype(itr)
    y = iterate(itr)
    y === nothing && return T[]
    x, i = y
    S = typeof(x)
    R = isconcretetype(T) ? T : S
    return _unique_from(itr, R[x], Set{R}((x,)), i)
end
```
-/
def uniqueMethod {α : Type} (itr : FiniteTrace α) (types : TypeOps α)
    (vectorEmpty : Nat → VectorModel α) (vectorSingleton : Nat → α → VectorModel α)
    (newSet : Nat → SetModel α) (insert : α → SetModel α → Result (SetModel α))
    (inBang : α → SetModel α → Result (Bool × SetModel α))
    (pushVector : VectorModel α → α → Result (VectorModel α))
    (resume : FiniteTrace α → VectorModel α → SetModel α → Nat → Result (VectorModel α)) :
    Result (VectorModel α) := do
  if itr.hasEltype then
    let T := itr.eltype
    let out := vectorEmpty T
    let seen := newSet T
    uniqueListLoop inBang pushVector itr.values out seen
  else
    let T := itr.defaultEltype
    match itr.values with
    | [] => .ok (vectorEmpty T)
    | x :: _ =>
      let S := types.typeof x
      let R := if types.isConcrete T then T else S
      let seen ← insert x (newSet R)
      resume itr (vectorSingleton R x) seen 1

/--
Julia source: base/set.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unique_from(itr, out, seen, i) = unique_from(itr, out, seen, i)
```
-/
def uniqueFromDispatch {α : Type} (run : FiniteTrace α → VectorModel α → SetModel α → Nat → Result (VectorModel α))
    (itr : FiniteTrace α) (out : VectorModel α) (seen : SetModel α) (state : Nat) : Result (VectorModel α) :=
  run itr out seen state

/--
Julia source: base/set.jl:244-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function unique_from(itr, out::Vector{T}, seen, i) where T
    while true
        y = iterate(itr, i)
        y === nothing && break
        x, i = y
        S = typeof(x)
        if !(S === T || S <: T)
            R = promote_typejoin(S, T)
            seenR = convert(Set{R}, seen)
            outR = convert(Vector{R}, out)
            !in!(x, seenR) && push!(outR, x)
            return _unique_from(itr, outR, seenR, i)
        end
        !in!(x, seen) && push!(out, x)
    end
    return out
end
```
-/
def uniqueFromMethod {α : Type} (types : TypeOps α)
    (inBang : α → SetModel α → Result (Bool × SetModel α))
    (pushVector : VectorModel α → α → Result (VectorModel α))
    (itr : FiniteTrace α) (out : VectorModel α) (seen : SetModel α) (state : Nat) :
    Result (VectorModel α) := by
  let rec loop (xs : List α) (i : Nat) (out : VectorModel α) (seen : SetModel α) :
      Result (VectorModel α) := do
    match xs with
    | [] => .ok out
    | x :: rest =>
      let S := types.typeof x
      if S == out.eltype || types.subtype S out.eltype then
        let (present, seen) ← inBang x seen
        let out ← if present then .ok out else pushVector out x
        loop rest (i + 1) out seen
      else
        let R := types.typejoin S out.eltype
        let seen ← types.convertSet R seen
        let out ← types.convertVector R out
        let (_, seen) ← inBang x seen
        let out ← pushVector out x
        loop rest (i + 1) out seen
  exact loop (itr.values.drop state) state out seen

/--
Julia source: base/set.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unique(r::AbstractRange) = allunique(r) ? r : oftype(r, r[begin]:r[begin])
```
-/
def uniqueRangeMethod {α : Type} (allunique : α → Bool) (ofType : α → α → α)
    (singletonRange : α → α) (r first : α) : α :=
  if allunique r then r else ofType r (singletonRange first)

/--
Julia source: base/set.jl:301-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unique(f, C; seen::Union{Nothing,Set}=nothing)
    out = Vector{eltype(C)}()
    if seen !== nothing
        for x in C
            !in!(f(x), seen) && push!(out, x)
        end
        return out
    end

    s = iterate(C)
    if s === nothing
        return out
    end
    (x, i) = s
    y = f(x)
    seen = Set{typeof(y)}()
    push!(seen, y)
    push!(out, x)

    return _unique!(f, out, C, seen, i)
end
```
-/
def uniqueMapMethod {A K : Type} (f : A → K) (values : List A) (seen : Option (SetModel K))
    (newVector : Nat → VectorModel A) (vectorType : Nat) (newSet : Nat → SetModel K) (typeof : K → Nat)
    (insert : K → SetModel K → Result (SetModel K)) (inBang : K → SetModel K → Result (Bool × SetModel K))
    (pushVector : VectorModel A → A → Result (VectorModel A))
    (resume : (A → K) → VectorModel A → List A → SetModel K → Nat → Nat → Result (VectorModel A)) :
    Result (VectorModel A) := do
  let out := newVector vectorType
  match seen with
  | some seen =>
    (values.foldlM (fun (out, seen) x => do
      let (present, seen) ← inBang (f x) seen
      let out ← if present then .ok out else pushVector out x
      .ok (out, seen)) (out, seen)).map Prod.fst
  | none =>
    match values with
    | [] => .ok out
    | x :: rest =>
      let y := f x
      let seen ← insert y (newSet (typeof y))
      let out ← pushVector out x
      resume f out rest seen 1 (typeof y)

/--
Julia source: base/set.jl:323-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unique!(f, out::AbstractVector, C, seen::Set, i)
    s = iterate(C, i)
    while s !== nothing
        (x, i) = s
        y = f(x)
        if y ∉ seen
            push!(out, x)
            if y isa eltype(seen)
                push!(seen, y)
            else
                seen2 = convert(Set{promote_typejoin(eltype(seen), typeof(y))}, seen)
                push!(seen2, y)
                return _unique!(f, out, C, seen2, i)
            end
        end
        s = iterate(C, i)
    end

    return out
end
```
-/
def uniqueMapTail {A K : Type} (types : TypeOps K)
    (contains : K → SetModel K → Result Bool) (insert : K → SetModel K → Result (SetModel K))
    (pushVector : VectorModel A → A → Result (VectorModel A))
    (f : A → K) (out : VectorModel A) (values : List A) (seen : SetModel K)
    (state seenType : Nat) : Result (VectorModel A) := by
  let rec loop (xs : List A) (out : VectorModel A) (seen : SetModel K) (seenType : Nat) :
      Result (VectorModel A) := do
    match xs with
    | [] => .ok out
    | x :: rest =>
      let y := f x
      if ← contains y seen then loop rest out seen seenType
      else
        let out ← pushVector out x
        let newType := types.typeof y
        if types.subtype newType seenType then
          let seen ← insert y seen
          loop rest out seen seenType
        else
          let newType := types.typejoin newType seenType
          let seen ← types.convertSet newType seen
          let seen ← insert y seen
          loop rest out seen newType
  exact loop (values.drop state) out seen seenType

/--
Julia source: base/set.jl:373-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unique!(f, A::AbstractVector; seen::Union{Nothing,Set}=nothing)
    if length(A) <= 1
        return A
    end

    i = firstindex(A)::Int
    x = @inbounds A[i]
    y = f(x)
    if seen === nothing
        seen = Set{typeof(y)}()
    end
    push!(seen, y)
    return _unique!(f, A, seen, i, i+1)
end
```
-/
def uniqueBangMethod {A K : Type} (f : A → K) (a : VectorModel A) (seen : Option (SetModel K))
    (typeof : K → Nat) (newSet : Nat → SetModel K) (insert : K → SetModel K → Result (SetModel K))
    (compact : (A → K) → VectorModel A → SetModel K → Int → Int → Nat → Result (VectorModel A)) :
    Result (VectorModel A) := do
  if a.values.length <= 1 then .ok a
  else match a.values with
  | [] => .ok a
  | x :: _ =>
    let y := f x
    let seen := seen.getD (newSet (typeof y))
    let seen ← insert y seen
    compact f a seen a.firstIndex (a.firstIndex + 1) (typeof y)

/--
Julia source: base/set.jl:388-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unique!(f, A::AbstractVector, seen::Set, current::Integer, i::Integer)
    while i <= lastindex(A)
        x = @inbounds A[i]
        y = f(x)
        if y ∉ seen
            current += 1
            @inbounds A[current] = x
            if y isa eltype(seen)
                push!(seen, y)
            else
                seen2 = convert(Set{promote_typejoin(eltype(seen), typeof(y))}, seen)
                push!(seen2, y)
                return _unique!(f, A, seen2, current, i+1)
            end
        end
        i += 1
    end
    return resize!(A, current - firstindex(A)::Int + 1)::typeof(A)
end
```
-/
def uniqueBangCompactMethod {A K : Type}
    (contains : K → SetModel K → Result Bool) (insert : K → SetModel K → Result (SetModel K))
    (isA : K → Nat → Bool) (typeOf : K → Nat) (typejoin : Nat → Nat → Nat)
    (convertSet : Nat → SetModel K → Result (SetModel K))
    (f : A → K) (a : VectorModel A) (seen : SetModel K) (current i : Int) (seenType : Nat) :
    Result (VectorModel A) :=
  uniqueBangCompactLoop f contains insert isA typeOf typejoin convertSet a current i seen seenType

/--
Julia source: base/set.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unique!(A::AbstractVector) = unique!(identity, A::AbstractVector)
```
-/
def uniqueBangIdentity {A : Type} (uniqueBang : (A → A) → VectorModel A → Result (VectorModel A))
    (a : VectorModel A) : Result (VectorModel A) := uniqueBang id a

/--
Julia source: base/set.jl:417-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _groupedunique!(A::AbstractVector)
    isempty(A) && return A
    idxs = eachindex(A)
    y = first(A)
    # We always keep the first element
    T = NTuple{2,Any} # just to eliminate `iterate(idxs)::Nothing` candidate
    it = iterate(idxs, (iterate(idxs)::T)[2])
    count = 1
    for x in Iterators.drop(A, 1)
        if !isequal(x, y)
            it = it::T
            y = A[it[1]] = x
            count += 1
            it = iterate(idxs, it[2])
        end
    end
    resize!(A, count)::typeof(A)
end
```
-/
def groupedUniqueMethod {α : Type} (equal : α → α → Bool) (a : VectorModel α) : VectorModel α :=
  match a.values with
  | [] => a
  | y :: xs => groupedUniqueLoop equal a xs (a.firstIndex + 1) y 1

/--
Julia source: base/set.jl:470-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unique!(itr)
    if isa(itr, AbstractVector)
        if OrderStyle(eltype(itr)) === Ordered()
            (issorted(itr) || issorted(itr, rev=true)) && return _groupedunique!(itr)
        end
    end
    isempty(itr) && return itr
    return _unique!(itr)
end
```
-/
def uniqueBangDispatch {A : Type} (isVector ordered : Bool) (issorted issortedReverse : Bool)
    (grouped generic : VectorModel A → Result (VectorModel A)) (a : VectorModel A) : Result (VectorModel A) :=
  if isVector then
    if ordered && (issorted || issortedReverse) then grouped a else generic a
  else generic a

/--
Julia source: base/set.jl:515-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allunique(C)
    if haslength(C)
        length(C) < 2 && return true
        length(C) < 32 && return _indexed_allunique(collect(C))
    end
    return _hashed_allunique(C)
end
```
-/
def alluniqueGeneric {C α : Type} (hasLength : C → Bool) (length : C → Nat)
    (collect : C → Result (FiniteTrace α)) (indexed : FiniteTrace α → Result Bool)
    (hashed : C → Result Bool) (c : C) : Result Bool :=
  if hasLength c then
    if length c < 2 then .ok true
    else if length c < 32 then collect c >>= indexed
    else hashed c
  else hashed c

/--
Julia source: base/set.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allunique(f, xs) = allunique(Generator(f, xs))
```
-/
def alluniqueMapMethod {C G A B : Type} (generator : (A → B) → C → G)
    (allunique : G → Result Bool) (f : A → B) (xs : C) : Result Bool :=
  allunique (generator f xs)

/--
Julia source: base/set.jl:525-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hashed_allunique(C)
    seen = Set{@default_eltype(C)}()
    x = iterate(C)
    if haslength(C) && length(C) > 1000
        for _ in OneTo(1000)
            v, s = something(x)
            in!(v, seen) && return false
            x = iterate(C, s)
        end
        sizehint!(seen, length(C))
    end
    while x !== nothing
        v, s = x
        in!(v, seen) && return false
        x = iterate(C, s)
    end
    return true
end
```
-/
def hashedAlluniqueMethod {α : Type} (newSet : Nat → SetModel α)
    (inBang : α → SetModel α → Result (Bool × SetModel α))
    (sizehint : SetModel α → JInt .i64 → Result (SetModel α))
    (itr : FiniteTrace α) : Result Bool := do
  let seen := newSet 0
  let firstValues := if itr.hasLength && itr.length > 1000 then itr.values.take 1000 else []
  let (prefixUnique, seen) ← alluniqueInsertLoop inBang firstValues seen
  if !prefixUnique then .ok false
  else
    let seen ← if itr.hasLength && itr.length > 1000 then
      sizehint seen (JInt.wrap .i64 (Int.ofNat itr.length)) else .ok seen
    let rest := if itr.hasLength && itr.length > 1000 then itr.values.drop 1000 else itr.values
    (alluniqueInsertLoop inBang rest seen).map Prod.fst

/--
Julia source: base/set.jl:544-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allunique(::Union{AbstractSet,AbstractDict}) = true
```
-/
def alluniqueSetMethod {S : Type} (_s : S) : Bool := true

/--
Julia source: base/set.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allunique(r::AbstractRange) = !iszero(step(r)) || length(r) <= 1
```
-/
def alluniqueRangeMethod {R : Type} (stepIsZero : R → Bool) (step : R → R)
    (length : R → Nat) (r : R) : Bool := !stepIsZero (step r) || length r <= 1

/--
Julia source: base/set.jl:549-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allunique(s::AbstractString)
    ncodeunits(s) < 32 ? _indexed_allunique(s) : _hashed_allunique(s)
end
```
-/
def alluniqueStringMethod {S : Type} (ncodeunits : S → Nat) (indexed hashed : S → Result Bool)
    (s : S) : Result Bool := if ncodeunits s < 32 then indexed s else hashed s

/--
Julia source: base/set.jl:553-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allunique(A::StridedArray)
    if length(A) < 32
        _indexed_allunique(A)
    elseif OrderStyle(eltype(A)) === Ordered()
        a1, rest1 = Iterators.peel(A)::Tuple{Any,Any}
        a2, rest = Iterators.peel(rest1)::Tuple{Any,Any}
        if !isequal(a1, a2)
            compare = isless(a1, a2) ? isless : (a,b) -> isless(b,a)
            for a in rest
                if compare(a2, a)
                    a2 = a
                elseif isequal(a2, a)
                    return false
                else
                    return _hashed_allunique(A)
                end
            end
        else # isequal(a1, a2)
            return false
        end
        return true
    else
        _hashed_allunique(A)
    end
end
```
-/
def alluniqueStridedMethod {α : Type} (trace : FiniteTrace α) (ordered : Bool)
    (equal less : α → α → Bool) (indexed hashed : FiniteTrace α → Result Bool) : Result Bool := do
  if trace.values.length < 32 then indexed trace
  else if ordered then
    match trace.values with
    | a1 :: a2 :: rest =>
      if equal a1 a2 then .ok false
      else
        let compare := if less a1 a2 then less else fun a b => less b a
        let rec scan (current : α) : List α → Result Bool
          | [] => .ok true
          | a :: xs =>
            if compare current a then scan a xs
            else if equal current a then .ok false
            else hashed trace
        scan a2 rest
    | _ => hashed trace
  else hashed trace

/--
Julia source: base/set.jl:579-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _indexed_allunique(A)
    length(A) < 2 && return true
    iter = eachindex(A)
    I = iterate(iter)
    while I !== nothing
        i, s = I
        a = A[i]
        for j in Iterators.rest(iter, s)
            isequal(a, @inbounds A[j]) && return false
        end
        I = iterate(iter, s)
    end
    return true
end
```
-/
def indexedAlluniqueMethod {α : Type} (equal : α → α → Bool)
    (trace : FiniteTrace α) : Result Bool :=
  let rec loop : List α → Bool
    | [] => true
    | x :: xs => xs.all (fun y => !equal x y) && loop xs
  .ok (loop trace.values)

/--
Julia source: base/set.jl:594-600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allunique(t::Tuple)
    length(t) < 32 || return _hashed_allunique(t)
    a = afoldl(true, tail(t)...) do b, x
        b & !isequal(first(t), x)
    end
    return a && allunique(tail(t))
end
```
-/
def alluniqueTupleMethod {α : Type} (equal : α → α → Bool)
    (hashed : FiniteTrace α → Result Bool) (trace : FiniteTrace α) : Result Bool := do
  if trace.values.length >= 32 then hashed trace
  else
    let rec loop : List α → Result Bool
      | [] => .ok true
      | x :: xs => do
        let tailUnique ← loop xs
        .ok (xs.all (fun y => !equal x y) && tailUnique)
    loop trace.values

/--
Julia source: base/set.jl:601-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allunique(t::Tuple{}) = true
```
-/
def alluniqueEmptyTuple : Bool := true

/--
Julia source: base/set.jl:603-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allunique(f::F, t::Tuple) where {F}
    length(t) < 2 && return true
    length(t) < 32 || return _hashed_allunique(Generator(f, t))
    return allunique(map(f, t))
end
```
-/
def alluniqueMapTuple {α β : Type} (f : α → β) (equal : β → β → Bool)
    (hashed : FiniteTrace β → Result Bool) (trace : FiniteTrace α) : Result Bool := do
  if trace.values.length < 2 then .ok true
  else
    let mapped : FiniteTrace β := {
      values := trace.values.map f, hasLength := trace.hasLength, length := trace.values.length,
      hasEltype := trace.hasEltype, eltype := trace.eltype, defaultEltype := trace.defaultEltype }
    if trace.values.length >= 32 then hashed mapped
    else alluniqueTupleMethod equal hashed mapped

/--
Julia source: base/set.jl:648-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allequal(itr)
    if haslength(itr)
        length(itr) <= 1 && return true
    end
    pl = Iterators.peel(itr)
    isnothing(pl) && return true
    a, rest = pl
    return all(isequal(a), rest)
end
```
-/
def allequalGeneric {α : Type} (equal : α → α → Bool) (itr : FiniteTrace α) : Result Bool :=
  if itr.hasLength && itr.length <= 1 then .ok true else
    match itr.values with
    | [] => .ok true
    | x :: xs => .ok (xs.all (equal x))

/--
Julia source: base/set.jl:658-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allequal(c::Union{AbstractSet,AbstractDict}) = length(c) <= 1
```
-/
def allequalSetMethod {S : Type} (length : S → Nat) (s : S) : Bool := length s <= 1

/--
Julia source: base/set.jl:660-660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allequal(r::AbstractRange) = iszero(step(r)) || length(r) <= 1
```
-/
def allequalRangeMethod {R : Type} (stepIsZero : R → Bool) (step : R → R)
    (length : R → Nat) (r : R) : Bool := stepIsZero (step r) || length r <= 1

/--
Julia source: base/set.jl:662-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allequal(f, xs) = allequal(Generator(f, xs))
```
-/
def allequalMapMethod {C G A B : Type} (generator : (A → B) → C → G)
    (allequal : G → Result Bool) (f : A → B) (xs : C) : Result Bool := allequal (generator f xs)

/--
Julia source: base/set.jl:664-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _allequal_loop(f, xs::Tuple)
    val = f(xs[1])
    for i in 2:length(xs)
        isequal(val, f(xs[i])) || return false
    end
    return true
end
```
-/
def allequalLoopMethod {α β : Type} (f : α → Jl β) (equal : β → β → Bool) :
    List α → Jl Bool
  | [] => .error .boundsError
  | x :: xs => do
    let value ← f x
    let rec loop : List α → Jl Bool
      | [] => .ok true
      | y :: ys => do
        if equal value (← f y) then loop ys else .ok false
    loop xs

/--
Julia source: base/set.jl:672-690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allequal(f, xs::Tuple)
    if @generated
        n = fieldcount(xs)
        if n <= 32
            n <= 1 && return true
            checks = Expr[:(isequal(val, f(getfield(xs, $i)))) for i in 2:n]
            expr = foldr((a, b) -> :($a && $b), checks)
            return quote
                val = f(getfield(xs, 1))
                $expr
            end
        else
            return :(return _allequal_loop(f, xs))
        end
    else
        length(xs) <= 1 && return true
        return _allequal_loop(f, xs)
    end
end
```
-/
def allequalTupleMethod {α β : Type} (f : α → Jl β) (equal : β → β → Bool)
    (generated : Bool) (values : List α) (loop : List α → Jl Bool) : Jl Bool := do
  if generated then
    if values.length <= 32 then
      if values.length <= 1 then .ok true
      else
        match values with
        | [] => .ok true
        | x :: xs =>
          let first ← f x
          let rec checks : List α → Jl Bool
            | [] => .ok true
            | y :: ys => do
              if equal first (← f y) then checks ys else .ok false
          checks xs
    else loop values
  else if values.length <= 1 then .ok true else loop values

/--
Julia source: base/set.jl:692-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allequal(f, ::Tuple{}) = true
```
-/
def allequalEmptyTuple : Bool := true

/--
Julia source: base/set.jl:693-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
allequal(xs::Tuple) = allequal(identity, xs)
```
-/
def allequalTupleIdentity {α : Type} (allequal : (α → α) → List α → Bool)
    (values : List α) : Bool := allequal (fun x => x) values

/--
Julia source: base/set.jl:695-695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, s::Set) = unsafe_filter!(f, s)
```
-/
def setFilterBangMethod {K : Type} (unsafeFilter : (K → Result Bool) → SetModel K → Result (SetModel K))
    (f : K → Result Bool) (s : SetModel K) : Result (SetModel K) := unsafeFilter f s

/--
Julia source: base/set.jl:698-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(s::AbstractSet, h::UInt)
    hv = hashs_seed
    for x in s
        hv ⊻= hash(x)
    end
    hash(hv, h)
end
```
-/
def setHashMethod {K : Type} (hashKey : K → JInt .u64) (hash : JInt .u64 → JInt .u64 → JInt .u64)
    (elements : SetModel K → Result (List K)) (s : SetModel K) (seed : JInt .u64) : Result (JInt .u64) := do
  let mut hv := JInt.lit .u64 0x852ada37cfe8e0ce
  for x in (← elements s) do
    hv := JuliaLean.base.int.xor_int hv (hashKey x)
  .ok (hash hv seed)

/--
Julia source: base/set.jl:706-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, s::T) where {T<:AbstractSet} = s
```
-/
def setConvertSame {T : Type} (s : T) : T := s

/--
Julia source: base/set.jl:707-707 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, s::AbstractSet) where {T<:AbstractSet} = T(s)::T
```
-/
def setConvertAbstract {T S : Type} (construct : S → T) (s : S) : T := construct s

/--
Julia source: base/set.jl:712-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_count(count::Integer)
    count < 0 && throw(DomainError(count, "`count` must not be negative (got $count)"))
    return min(count, typemax(Int)) % Int
end
```
-/
def checkCountMethod (count : Int) : Jl (JInt .i64) := checkCount count

/--
Julia source: base/set.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_oftype(x, ::Type{T}) where {T} = copyto!(similar(x, T), x)
```
-/
def copyOfTypeMethod {A B T : Type} (similar : A → T → Result B) (copyto : B → A → Result B)
    (x : A) (ty : T) : Result B := do
  let out ← similar x ty
  copyto out x

/--
Julia source: base/set.jl:720-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_oftype(x::AbstractDict, ::Type{Pair{K,V}}) where {K,V} = merge!(empty(x, K, V), x)
```
-/
def copyOfTypeDictMethod {A B T : Type} (empty : A → T → Result B) (merge : B → A → Result B)
    (x : A) (ty : T) : Result B := do
  let out ← empty x ty
  merge out x

/--
Julia source: base/set.jl:721-721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_oftype(x::AbstractSet, ::Type{T}) where {T} = union!(empty(x, T), x)
```
-/
def copyOfTypeSetMethod {A B T : Type} (empty : A → T → Result B) (union : B → A → Result B)
    (x : A) (ty : T) : Result B := do
  let out ← empty x ty
  union out x

/--
Julia source: base/set.jl:723-723 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_oftype(x::AbstractArray{T}, ::Type{T}) where {T} = copy(x)
```
-/
def copyOfTypeArraySame {A : Type} (copy : A → A) (x : A) : A := copy x

/--
Julia source: base/set.jl:724-724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_oftype(x::AbstractDict{K,V}, ::Type{Pair{K,V}}) where {K,V} = copy(x)
```
-/
def copyOfTypeDictSame {A : Type} (copy : A → A) (x : A) : A := copy x

/--
Julia source: base/set.jl:725-725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_copy_oftype(x::AbstractSet{T}, ::Type{T}) where {T} = copy(x)
```
-/
def copyOfTypeSetSame {A : Type} (copy : A → A) (x : A) : A := copy x

/--
Julia source: base/set.jl:727-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_or_copy(x::Any) = similar(x)
```
-/
def similarOrCopyMethod {A : Type} (similar : A → Result A) (x : A) : Result A := similar x

/--
Julia source: base/set.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_or_copy(x::Any, ::Type{T}) where {T} = similar(x, T)
```
-/
def similarOrCopyTypedMethod {A T : Type} (similar : A → T → Result A) (x : A) (ty : T) : Result A := similar x ty

/--
Julia source: base/set.jl:730-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_or_copy(x::Union{AbstractDict,AbstractSet}) = copy(x)
```
-/
def similarOrCopyCollection {A : Type} (copy : A → Result A) (x : A) : Result A := copy x

/--
Julia source: base/set.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_or_copy(x::Union{AbstractDict,AbstractSet}, ::Type{T}) where {T} = _copy_oftype(x, T)
```
-/
def similarOrCopyCollectionTyped {A T : Type} (copy : A → T → Result A) (x : A) (ty : T) : Result A := copy x ty

/--
Julia source: base/set.jl:762-763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace!(A, old_new::Pair...; count::Integer=typemax(Int)) =
    replace_pairs!(A, A, check_count(count), old_new)
```
-/
def replacePairsBangWrapper {A α : Type} (pairs : List (α × α)) (count : Int)
    (check : Int → Jl (JInt .i64))
    (replacePairs : A → A → JInt .i64 → List (α × α) → Result A) (a : A) : Result A := do
  let n ← (check count).mapError Error.julia
  replacePairs a a n pairs

/--
Julia source: base/set.jl:765-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace_pairs!(res, A, count::Int, old_new::Tuple{Vararg{Pair}})
    @inline function new(x)
        for o_n in old_new
            isequal(first(o_n), x) && return last(o_n)
        end
        return x # no replace
    end
    _replace!(new, res, A, count)
end
```
-/
def replacePairsMethod {A α : Type} (new : α → α)
    (replaceInPlace : (α → Result α) → A → A → JInt .i64 → Result A)
    (res source : A) (count : JInt .i64) : Result A :=
  replaceInPlace (fun x => .ok (new x)) res source count

/--
Julia source: base/set.jl:766-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function new(x)
        for o_n in old_new
            isequal(first(o_n), x) && return last(o_n)
        end
        return x # no replace
    end
```
-/
def replacePairsNewMethod {α : Type} (equal : α → α → Bool)
    (pairs : List (α × α)) (x : α) : α := replacePairsValue equal pairs x

/--
Julia source: base/set.jl:804-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace!(new::Callable, A; count::Integer=typemax(Int)) =
    _replace!(new, A, A, check_count(count))
```
-/
def replaceCallableBangWrapper {A α : Type} (new : α → Result α) (a : A) (count : Int)
    (check : Int → Jl (JInt .i64))
    (replaceInPlace : (α → Result α) → A → A → JInt .i64 → Result A) : Result A := do
  let n ← (check count).mapError Error.julia
  replaceInPlace new a a n

/--
Julia source: base/set.jl:842-851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace(A, old_new::Pair...; count::Union{Integer,Nothing}=nothing)
    V = promote_valuetype(old_new...)
    if count isa Nothing
        T = promote_type(subtract_singletontype(eltype(A), old_new...), V)
        replace_pairs!(_similar_or_copy(A, T), A, typemax(Int), old_new)
    else
        U = promote_type(eltype(A), V)
        replace_pairs!(_similar_or_copy(A, U), A, check_count(count), old_new)
    end
end
```
-/
def replacePairsCopyMethod {A B P : Type} (pairs : List P) (count : Option Int)
    (elementType : A → Nat) (promoteValues : List P → Nat) (subtractSingletons : Nat → List P → Nat)
    (promote : Nat → Nat → Nat) (similarOrCopy : A → Nat → Result B)
    (check : Int → Jl (JInt .i64))
    (replacePairs : B → A → JInt .i64 → List P → Result B) (a : A) : Result B := do
  let V := promoteValues pairs
  match count with
  | none =>
    let T := promote (subtractSingletons (elementType a) pairs) V
    let out ← similarOrCopy a T
    replacePairs out a (JInt.lit .i64 (IntTy.max .i64)) pairs
  | some n =>
    let U := promote (elementType a) V
    let out ← similarOrCopy a U
    let n ← (check n).mapError Error.julia
    replacePairs out a n pairs

/--
Julia source: base/set.jl:853-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_valuetype(x::Pair{K, V}) where {K, V} = V
```
-/
def promoteValueTypeSingle (valueType : Nat) : Nat := valueType

/--
Julia source: base/set.jl:854-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_valuetype(x::Pair{K, V}, y::Pair...) where {K, V} =
    promote_type(V, promote_valuetype(y...))
```
-/
def promoteValueTypeMany (promote : Nat → Nat → Nat) (valueType restValueType : Nat) : Nat :=
  promote valueType restValueType

/--
Julia source: base/set.jl:858-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function subtract_singletontype(::Type{T}, x::Pair{K}) where {T, K}
    if issingletontype(K)
        typesplit(T, K)
    else
        T
    end
end
```
-/
def subtractSingletonType (isSingleton : Nat → Bool) (typeSplit : Nat → Nat → Nat)
    (sourceType keyType : Nat) : Nat :=
  if isSingleton keyType then typeSplit sourceType keyType else sourceType

/--
Julia source: base/set.jl:865-866 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
subtract_singletontype(::Type{T}, x::Pair{K}, y::Pair...) where {T, K} =
    subtract_singletontype(subtract_singletontype(T, y...), x)
```
-/
def subtractSingletonTypeMany (subtract : Nat → List Nat → Nat)
    (sourceType : Nat) (keyTypes : List Nat) : Nat := subtract sourceType keyTypes

/--
Julia source: base/set.jl:895-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(new::Callable, A; count::Integer=typemax(Int)) =
    _replace!(new, _similar_or_copy(A), A, check_count(count))
```
-/
def replaceCallableCopyWrapper {A B α : Type} (new : α → Result α) (a : A)
    (similarOrCopy : A → Result B) (count : Int)
    (check : Int → Jl (JInt .i64))
    (replaceInPlace : (α → Result α) → B → A → JInt .i64 → Result B) : Result B := do
  let out ← similarOrCopy a
  let n ← (check count).mapError Error.julia
  replaceInPlace new out a n

/--
Julia source: base/set.jl:899-899 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace!(a::Callable, b::Pair; count::Integer=-1) = throw(MethodError(replace!, (a, b)))
```
-/
def replaceAmbiguousBangOne : Jl Unit := .error (.methodError "replace!")

/--
Julia source: base/set.jl:900-900 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace!(a::Callable, b::Pair, c::Pair; count::Integer=-1) = throw(MethodError(replace!, (a, b, c)))
```
-/
def replaceAmbiguousBangTwo : Jl Unit := .error (.methodError "replace!")

/--
Julia source: base/set.jl:901-901 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(a::Callable, b::Pair; count::Integer=-1) = throw(MethodError(replace, (a, b)))
```
-/
def replaceAmbiguousOne : Jl Unit := .error (.methodError "replace")

/--
Julia source: base/set.jl:902-902 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(a::Callable, b::Pair, c::Pair; count::Integer=-1) = throw(MethodError(replace, (a, b, c)))
```
-/
def replaceAmbiguousTwo : Jl Unit := .error (.methodError "replace")

/--
Julia source: base/set.jl:906-906 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
askey(k, ::AbstractDict) = k.first
```
-/
def asKeyDict {C K V : Type} (pair : K × V) (_dict : C) : K := pair.1

/--
Julia source: base/set.jl:907-907 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
askey(k, ::AbstractSet) = k
```
-/
def asKeySet {C K : Type} (key : K) (_set : C) : K := key

/--
Julia source: base/set.jl:909-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace!(new::Callable, res::Union{AbstractDict,AbstractSet},
                   A::Union{AbstractDict,AbstractSet}, count::Int)
    @assert (res isa AbstractDict && A isa AbstractDict ||
             res isa AbstractSet && A isa AbstractSet) "type mismatch"
    count == 0 && return res
    c = 0
    if res === A # cannot replace elements while iterating over A
        repl = Pair{eltype(A),eltype(A)}[]
        for x in A
            y = new(x)
            if x !== y
                push!(repl, x => y)
                c += 1
                c == count && break
            end
        end
        for oldnew in repl
            pop!(res, askey(first(oldnew), res))
        end
        for oldnew in repl
            push!(res, last(oldnew))
        end
    else
        for x in A
            y = new(x)
            if x !== y
                pop!(res, askey(x, res))
                push!(res, y)
                c += 1
                c == count && break
            end
        end
    end
    res
end
```
-/
def replaceAbstractCollectionsMethod {C α : Type} (isDict isSet : C → Bool)
    (same : C → C → Bool) (elements : C → Result (List α)) (new : α → Result α)
    (identical : α → α → Bool) (asKey : α → C → α)
    (pop : α → C → Result (α × C)) (push : α → C → Result C)
    (res source : C) (count : Nat) : Result C := do
  if !((isDict res && isDict source) || (isSet res && isSet source)) then
    .error (.assertion "type mismatch")
  else if count == 0 then .ok res
  else if same res source then
    let xs ← elements source
    let rec replacements : List α → Nat → List (α × α) → Result (List (α × α))
      | [], _, out => .ok out
      | x :: rest, changed, out => do
        let y ← new x
        if identical x y then replacements rest changed out
        else if changed + 1 == count then .ok (out ++ [(x, y)])
        else replacements rest (changed + 1) (out ++ [(x, y)])
    let pairs ← replacements xs 0 []
    let res ← pairs.foldlM (fun r pair => (pop (asKey pair.1 r) r).map Prod.snd) res
    pairs.foldlM (fun r pair => push pair.2 r) res
  else
    let xs ← elements source
    let rec replaceLoop : List α → Nat → C → Result C
      | [], _, r => .ok r
      | x :: rest, changed, r => do
        if changed == count then .ok r
        else
          let y ← new x
          if identical x y then replaceLoop rest changed r
          else
            let (_, r) ← pop (asKey x r) r
            let r ← push y r
            replaceLoop rest (changed + 1) r
    replaceLoop xs 0 res

/--
Julia source: base/set.jl:947-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace!(new::Callable, res::AbstractArray, A::AbstractArray, count::Int)
    c = 0
    if count >= length(A) # simpler loop allows for SIMD
        if res === A # for optimization only
            for i in eachindex(A)
                @inbounds Ai = A[i]
                y = new(Ai)
                @inbounds A[i] = y
            end
        else
            for i in eachindex(A)
                @inbounds Ai = A[i]
                y = new(Ai)
                @inbounds res[i] = y
            end
        end
    else
        for i in eachindex(A)
            @inbounds Ai = A[i]
            if c < count
                y = new(Ai)
                @inbounds res[i] = y
                c += (Ai !== y)
            else
                @inbounds res[i] = Ai
            end
        end
    end
    res
end
```
-/
def replaceArrayMethod {α : Type} (new : α → Result α) (identical : α → α → Bool)
    (same : VectorModel α → VectorModel α → Bool) (res source : VectorModel α)
    (count : Nat) : Result (VectorModel α) := do
  if count >= source.values.length then
    if same res source then replaceArrayLoop new identical source.values source.firstIndex source.firstIndex res true count 0
    else replaceArrayLoop new identical source.values source.firstIndex source.firstIndex res true count 0
  else replaceArrayLoop new identical source.values source.firstIndex source.firstIndex res false count 0

/--
Julia source: base/set.jl:980-1010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace!(new::Callable, t::Dict{K,V}, A::AbstractDict, count::Int) where {K,V}
    # we ignore A, which is supposed to be equal to the destination t,
    # as it can generally be faster to just replace inline
    count == 0 && return t
    c = 0
    news = Pair{K,V}[]
    i = skip_deleted_floor!(t)
    @inbounds while i != 0
        k1, v1 = t.keys[i], t.vals[i]
        x1 = Pair{K,V}(k1, v1)
        x2 = new(x1)
        if x1 !== x2
            k2, v2 = first(x2), last(x2)
            if isequal(k1, k2)
                t.keys[i] = k2
                t.vals[i] = v2
                t.age += 1
            else
                _delete!(t, i)
                push!(news, x2)
            end
            c += 1
            c == count && break
        end
        i = i == typemax(Int) ? 0 : skip_deleted(t, i+1)
    end
    for n in news
        push!(t, n)
    end
    t
end
```
-/
def replaceDictMethod {K V A : Type} (ops : DictReplaceRuntime K V)
    (new : (K × V) → DictResult (K × V)) (identical : (K × V) → (K × V) → Bool)
    (source : A) (t : DictState K V) (count : Nat) : DictResult (DictState K V) :=
  replaceDictModel ops new identical source t count

/--
Julia source: base/set.jl:1012-1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace!(new::Callable, t::Set{T}, ::AbstractSet, count::Int) where {T}
    _replace!(t.dict, t.dict, count) do kv
        k = first(kv)
        k2 = new(k)
        k2 === k ? kv : k2 => nothing
    end
    t
end
```
-/
def replaceSetMethod {K : Type} (ops : DictReplaceRuntime K Unit)
    (new : K → DictResult K) (identical : K → K → Bool) (t : SetModel K) (count : Nat) :
    DictResult (SetModel K) := do
  let newPair : (K × Unit) → DictResult (K × Unit) := fun kv => do
    let k := kv.1
    let k2 ← new k
    if identical k2 k then .ok kv else .ok (k2, ())
  let dict ← replaceDictMethod ops newPair (fun a b => identical a.1 b.1 && a.2 == b.2) t t.dict count
  .ok (fromDict dict)

/--
Julia source: base/set.jl:1023-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace(f::Callable, t::Tuple, count::Int)
    if count == 0 || isempty(t)
        t
    else
        x = f(t[1])
        (x, _replace(f, tail(t), count - !==(x, t[1]))...)
    end
end
```
-/
def replaceTupleMethod {α : Type} (f : α → Result α) (identical : α → α → Bool)
    (values : List α) (count : Nat) : Result (List α) :=
  let rec loop : List α → Nat → Result (List α)
    | [], _ => .ok []
    | xs, 0 => .ok xs
    | x :: xs, n + 1 => do
      let y ← f x
      let remaining := n - if identical y x then 0 else 1
      return y :: (← loop xs remaining)
  loop values count

/--
Julia source: base/set.jl:1032-1033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(f::Callable, t::Tuple; count::Integer=typemax(Int)) =
    _replace(f, t, check_count(count))
```
-/
def replaceTupleCallableMethod {α : Type} (f : α → Result α) (identical : α → α → Bool)
    (values : List α) (count : Int) (check : Int → Jl (JInt .i64)) :
    Result (List α) := do
  let n ← (check count).mapError Error.julia
  replaceTupleMethod f identical values n.val.toNat

/--
Julia source: base/set.jl:1035-1043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace(t::Tuple, count::Int, old_new::Tuple{Vararg{Pair}})
    _replace(t, count) do x
        @inline
        for o_n in old_new
            isequal(first(o_n), x) && return last(o_n)
        end
        return x
    end
end
```
-/
def replaceTuplePairsMethod {α : Type} (equal identical : α → α → Bool)
    (values : List α) (count : Nat) (pairs : List (α × α)) : Result (List α) :=
  replaceTupleMethod (fun x => .ok (replacePairsValue equal pairs x)) identical values count

/--
Julia source: base/set.jl:1045-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(t::Tuple, old_new::Pair...; count::Integer=typemax(Int)) =
    _replace(t, check_count(count), old_new)
```
-/
def replaceTuplePairsWrapper {α : Type} (equal identical : α → α → Bool)
    (values : List α) (pairs : List (α × α)) (count : Int)
    (check : Int → Jl (JInt .i64)) : Result (List α) := do
  let n ← (check count).mapError Error.julia
  replaceTuplePairsMethod equal identical values n.val.toNat pairs

end JuliaLean.base.set
