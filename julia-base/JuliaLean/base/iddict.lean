import JuliaLean.Core
import JuliaLean.base.abstractdict
import JuliaLean.base.int
import JuliaLean.Registry.Types

/-!
# Model of `base/iddict.jl`

Typed model of the Julia source at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Julia `Any` values use a generic carrier, typed keys and values use `K` and
`V`, and C table and memory operations are typed interfaces.
-/

namespace JuliaLean.base.iddict

open JuliaLean

structure IdDict (K V A HT : Type) where
  ht : HT
  count : JInt .i64
  ndel : JInt .i64

structure CallResult (E S R : Type) where
  result : Except E R
  state : S
structure TableSlot (A : Type) where
  index : JInt .u64
  key : A
  value : A

def slotsIncreasing {A : Type} : List (TableSlot A) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.index.val < second.index.val ∧ slotsIncreasing (second :: rest)

structure RuntimeOps (K V A HT E Ptr Preserve : Type) where
  allocate : Nat → Except E HT
  sameMemory : HT → HT → Bool
  copyMemory : HT → Except E HT
  memoryLength : HT → JInt .i64
  rehashMemory : {N : Type} → HT → N → Except E HT
  eqtableGet : HT → A → A → A
  eqtablePut : HT → A → A → Except E (HT × JInt .i32)
  eqtablePop : HT → A → A → Except E (HT × A × JInt .i32)
  eqtableNextind : HT → JInt .u64 → JInt .u64
  reinterpretInt : JInt .u64 → JInt .i64
  memoryAt : HT → JInt .i64 → Except E A
  toUInt : {I : Type} → I → Except E (JInt .u64)
  isKey : A → Bool
  isValue : A → Bool
  convertValue : A → Except E A
  castKey : A → Except E K
  castValue : A → Except E V
  keyToAny : K → A
  valueToAny : V → A
  keyTypeError : A → E
  keyError : A → E
  secretToken : A
  sameIdentity : A → A → Bool
  doubleInteger : {N : Type} → N → Except E N
  tablesz : {N : Type} → N → Except E (JInt .i64)
  preserveBegin : HT → Preserve
  unsafeConvert : HT → Ptr
  sizeofMemory : HT → JInt .u64
  memsetZero : HT → Ptr → JInt .u64 → HT
  preserveEnd : Preserve → Unit
  tableSlots : HT → List (TableSlot A)
  tablePairs : HT → List (A × A)

inductive IteratorSize where
  | hasLength
  | hasShape
  | unknown
  deriving Repr, DecidableEq

structure IteratorOps (A I E : Type) where
  size : I → IteratorSize
  length : I → JInt .i64
  elements : I → List (A × A)
  forPairs : {S : Type} → I → (A → A → S → CallResult E S S) → S → CallResult E S S

namespace IteratorOps

def Lawful {A I E : Type} (iterator : IteratorOps A I E) : Prop :=
  ∀ itr,
    let trace := iterator.forPairs itr
      (fun key value seen =>
        ⟨.ok (seen ++ [(key, value)]), seen ++ [(key, value)]⟩) []
    trace.result = .ok (iterator.elements itr) ∧ trace.state = iterator.elements itr

end IteratorOps

structure TypePair where
  key : Type
  value : Type

structure RuntimeFamily (A HT E Ptr Preserve : Type) where
  forTypes : (K V : Type) → RuntimeOps K V A HT E Ptr Preserve

abbrev PackedIdDict (A HT : Type) := Σ K : Type, Σ V : Type, IdDict K V A HT
structure IdKeySet (K V A HT : Type) where
  dict : IdDict K V A HT

/-- Reference lookup uses object identity, the equality relation of `IdDict`. -/
def referenceLookup {A : Type} (sameIdentity : A → A → Bool) :
    List (A × A) → A → Option A
  | [], _ => none
  | (key, value) :: rest, query =>
      if sameIdentity query key then some value else referenceLookup sameIdentity rest query

/-- Replace an identity-equal key without changing its stored representative. -/
def referenceSet {A : Type} (sameIdentity : A → A → Bool) :
    List (A × A) → A → A → List (A × A)
  | [], key, value => [(key, value)]
  | (storedKey, storedValue) :: rest, key, value =>
      if sameIdentity key storedKey then (storedKey, value) :: rest
      else (storedKey, storedValue) :: referenceSet sameIdentity rest key value

/-- Remove the first identity-equal key. -/
def referenceDelete {A : Type} (sameIdentity : A → A → Bool) :
    List (A × A) → A → List (A × A)
  | [], _ => []
  | (storedKey, storedValue) :: rest, key =>
      if sameIdentity key storedKey then rest
      else (storedKey, storedValue) :: referenceDelete sameIdentity rest key

def resultWithState {E S R : Type} (result : Except E R) (state : S) : CallResult E S R :=
  ⟨result, state⟩


mutual
/--
Julia source: base/iddict.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdDict{K,V}() where {K, V} = new{K,V}(Memory{Any}(undef, 32), 0, 0)
```
-/
  def emptyTyped {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) : Except E (IdDict K V A HT) := do
    let ht ← ops.allocate 32
    .ok ⟨ht, JInt.wrap .i64 0, JInt.wrap .i64 0⟩

/--
Julia source: base/iddict.jl:33-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function IdDict{K,V}(itr) where {K, V}
        d = IdDict{K,V}()
        if IteratorSize(itr) isa Union{HasLength, HasShape}
            sizehint!(d, length(itr))
        end
        for (k,v) in itr; d[k] = v; end
        d
    end
```
-/
  def fromIterator {K V A HT E Ptr Preserve I : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (iteratorOps : IteratorOps A I E)
      (itr : I) : Except E (IdDict K V A HT) := do
    let d ← emptyTyped ops
    let d ←
      if iteratorOps.size itr == .hasLength || iteratorOps.size itr == .hasShape then
        let hinted := sizehint! ops d (iteratorOps.length itr)
        match hinted.result with
        | .error e => .error e
        | .ok _ => .ok hinted.state
      else .ok d
    let iterated := iteratorOps.forPairs itr (fun key value state => setindex! ops state value key) d
    match iterated.result with
    | .error e => .error e
    | .ok _ => .ok iterated.state

/--
Julia source: base/iddict.jl:42-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function IdDict{K,V}(pairs::Pair...) where {K, V}
        d = IdDict{K,V}()
        sizehint!(d, length(pairs))
        for (k,v) in pairs; d[k] = v; end
        d
    end
```
-/
  def fromPairs {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (pairs : List (A × A)) :
      Except E (IdDict K V A HT) := do
    let d ← emptyTyped ops
    let hinted := sizehint! ops d (JInt.wrap .i64 pairs.length)
    let d ← match hinted.result with
      | .error e => .error e
      | .ok _ => .ok hinted.state
    insertPairs ops pairs d

/--
Julia source: base/iddict.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdDict{K,V}(d::IdDict{K,V}) where {K, V} = new{K,V}(copy(d.ht), d.count, d.ndel)
```
-/
  def copyConstruct {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
      Except E (IdDict K V A HT) := do
    let ht ← ops.copyMemory d.ht
    .ok ⟨ht, d.count, d.ndel⟩

/--
Julia source: base/iddict.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict() = IdDict{Any,Any}()
```
-/
  def emptyAny {A HT E Ptr Preserve : Type}
      (ops : RuntimeOps A A A HT E Ptr Preserve) : Except E (IdDict A A A HT) :=
    emptyTyped ops

/--
Julia source: base/iddict.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(kv::Tuple{}) = IdDict()
```
-/
  def emptyTuple {A HT E Ptr Preserve : Type}
      (ops : RuntimeOps A A A HT E Ptr Preserve) (_kv : Unit) :
      Except E (IdDict A A A HT) := emptyAny ops

/--
Julia source: base/iddict.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::Pair{K,V}...)           where {K,V} = IdDict{K,V}(ps)
```
-/
  def fromPairsKV {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (pairs : List (A × A)) :
      Except E (IdDict K V A HT) := fromPairs ops pairs

/--
Julia source: base/iddict.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::Pair{K}...)             where {K}   = IdDict{K,Any}(ps)
```
-/
  def fromPairsK {K A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K A A HT E Ptr Preserve) (pairs : List (A × A)) :
      Except E (IdDict K A A HT) := fromPairs ops pairs

/--
Julia source: base/iddict.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::(Pair{K,V} where K)...) where {V}   = IdDict{Any,V}(ps)
```
-/
  def fromPairsV {V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps A V A HT E Ptr Preserve) (pairs : List (A × A)) :
      Except E (IdDict A V A HT) := fromPairs ops pairs

/--
Julia source: base/iddict.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(ps::Pair...)                            = IdDict{Any,Any}(ps)
```
-/
  def fromPairsAny {A HT E Ptr Preserve : Type}
      (ops : RuntimeOps A A A HT E Ptr Preserve) (pairs : List (A × A)) :
      Except E (IdDict A A A HT) := fromPairs ops pairs

  def constructForType {I A HT E Ptr Preserve : Type}
      (family : RuntimeFamily A HT E Ptr Preserve) (iteratorOps : IteratorOps A I E)
      (types : TypePair) (itr : I) : Except E (PackedIdDict A HT) :=
    match fromIterator (family.forTypes types.key types.value) iteratorOps itr with
    | .error e => .error e
    | .ok dict => .ok ⟨types.key, types.value, dict⟩

/--
Julia source: base/iddict.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdDict(kv) = dict_with_eltype((K, V) -> IdDict{K, V}, kv, eltype(kv))
```
-/
  def fromEltype {I A HT E Ptr Preserve : Type}
      (family : RuntimeFamily A HT E Ptr Preserve) (iteratorOps : IteratorOps A I E)
      (dictWithEltype : (TypePair → I → Except E (PackedIdDict A HT)) → I → TypePair →
        Except E (PackedIdDict A HT)) (kv : I) (eltype : I → TypePair) :
      Except E (PackedIdDict A HT) :=
    dictWithEltype (fun types itr => constructForType family iteratorOps types itr) kv (eltype kv)

/--
Julia source: base/iddict.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(d::IdDict, ::Type{K}, ::Type{V}) where {K, V} = IdDict{K,V}()
```
-/
  def emptyOf {K V K0 V0 A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (_d : IdDict K0 V0 A HT) :
      Except E (IdDict K V A HT) := emptyTyped ops

/--
Julia source: base/iddict.jl:64-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rehash!(d::IdDict, newsz::Integer = length(d.ht)%UInt)
    d.ht = ccall(:jl_idtable_rehash, Memory{Any}, (Any, Csize_t), d.ht, newsz)
    d
end
```
-/
  def rehash {K V A HT E Ptr Preserve N : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) (newsz : N) :
      CallResult E (IdDict K V A HT) (IdDict K V A HT) :=
    match ops.rehashMemory d.ht newsz with
    | .error e => resultWithState (.error e) d
    | .ok ht =>
        let d := { d with ht := ht }
        resultWithState (.ok d) d

  def rehashDefault {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
      CallResult E (IdDict K V A HT) (IdDict K V A HT) :=
    rehash ops d (JuliaLean.base.int.remT .u64 (ops.memoryLength d.ht))

/--
Julia source: base/iddict.jl:69-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(d::IdDict, newsz::Integer)
    newsz = _tablesz(newsz*2)  # *2 for keys and values in same array
    oldsz = length(d.ht)
    # grow at least 25%
    if newsz < (oldsz*5)>>2
        return d
    end
    rehash!(d, newsz)
end
```
-/
  def sizehint! {K V A HT E Ptr Preserve N : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) (newsz : N) :
      CallResult E (IdDict K V A HT) (IdDict K V A HT) :=
    match ops.doubleInteger newsz with
    | .error e => resultWithState (.error e) d
    | .ok doubled =>
        match ops.tablesz doubled with
        | .error e => resultWithState (.error e) d
        | .ok newSize =>
            let oldSize := ops.memoryLength d.ht
            let minimumGrowth := JuliaLean.base.int.ashr_int
              (oldSize * JInt.wrap .i64 5) (JInt.wrap .i64 2)
            if newSize.val < minimumGrowth.val then resultWithState (.ok d) d
            else rehash ops d newSize

/--
Julia source: base/iddict.jl:79-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(d::IdDict{K,V}, @nospecialize(val), @nospecialize(key)) where {K, V}
    !isa(key, K) && throw(KeyTypeError(K, key))
    if !(val isa V) # avoid a dynamic call
        val = convert(V, val)::V
    end
    if d.ndel >= ((3*length(d.ht))>>2)
        rehash!(d, max((length(d.ht)%UInt)>>1, 32))
        d.ndel = 0
    end
    inserted = RefValue{Cint}(0)
    d.ht = ccall(:jl_eqtable_put, Memory{Any}, (Any, Any, Any, Ptr{Cint}), d.ht, key, val, inserted)
    d.count += inserted[]
    return d
end
```
-/
  def setindex! {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
      (val key : A) : CallResult E (IdDict K V A HT) (IdDict K V A HT) :=
    if !ops.isKey key then resultWithState (.error (ops.keyTypeError key)) d
    else
      match (do
        let val ← if ops.isValue val then Except.ok val else ops.convertValue val
        let val ← ops.castValue val
        .ok (ops.valueToAny val)) with
      | .error e => resultWithState (.error e) d
      | .ok val =>
          let threshold := JuliaLean.base.int.ashr_int
            (JInt.wrap .i64 3 * ops.memoryLength d.ht) (JInt.wrap .i64 2)
          let rehashed :=
            if d.ndel.val ≥ threshold.val then
              let half := JuliaLean.base.int.lshr_int
                (JuliaLean.base.int.remT .u64 (ops.memoryLength d.ht)) (JInt.wrap .u64 1)
              let newSize := if half.val < 32 then JInt.wrap .u64 32 else half
              let result := rehash ops d newSize
              match result.result with
              | .error e => resultWithState (.error e) result.state
              | .ok d =>
                  let d := { d with ndel := JInt.wrap .i64 0 }
                  resultWithState (.ok d) d
            else resultWithState (.ok d) d
          match rehashed.result with
          | .error e => resultWithState (.error e) rehashed.state
          | .ok d =>
              match ops.eqtablePut d.ht key val with
              | .error e => resultWithState (.error e) d
              | .ok (ht, inserted) =>
                  let d : IdDict K V A HT :=
                    ⟨ht, JInt.wrap .i64 (d.count.val + inserted.val), d.ndel⟩
                  resultWithState (.ok d) d

  def insertPairs {K V A HT E Ptr Preserve : Type}
      (ops : RuntimeOps K V A HT E Ptr Preserve) (pairs : List (A × A))
      (d : IdDict K V A HT) : Except E (IdDict K V A HT) := do
    let (_, d) ← pairs.foldlM (fun (_, d) (key, value) => do
      let inserted := setindex! ops d value key
      match inserted.result with
      | .error e => .error e
      | .ok _ => .ok ((), inserted.state)) ((), d)
    .ok d
end

/--
Julia source: base/iddict.jl:94-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, default)
    val === default ? default : val::V
end
```
-/
def get {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (key default : A) : Except E A := do
  let val := ops.eqtableGet d.ht key default
  if ops.sameIdentity val default then .ok default
  else
    let value ← ops.castValue val
    .ok (ops.valueToAny value)

/--
Julia source: base/iddict.jl:99-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    val === secret_table_token && throw(KeyError(key))
    return val::V
end
```
-/
def getindex {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) (key : A) :
    Except E A := do
  let val := ops.eqtableGet d.ht key ops.secretToken
  if ops.sameIdentity val ops.secretToken then throw (ops.keyError key)
  let value ← ops.castValue val
  .ok (ops.valueToAny value)

/--
Julia source: base/iddict.jl:105-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}
    found = RefValue{Cint}(0)
    val = ccall(:jl_eqtable_pop, Any, (Any, Any, Any, Ptr{Cint}), d.ht, key, default, found)
    if found[] === Cint(0)
        return default
    else
        d.count -= 1
        d.ndel += 1
        return val::V
    end
end
```
-/
def popDefault {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (key default : A) : CallResult E (IdDict K V A HT) A :=
  match ops.eqtablePop d.ht key default with
  | .error e => resultWithState (.error e) d
  | .ok (ht, value, found) =>
      let d := { d with ht := ht }
      if found.val == 0 then resultWithState (.ok default) d
      else
        let d : IdDict K V A HT :=
          ⟨ht, d.count - JInt.wrap .i64 1, d.ndel + JInt.wrap .i64 1⟩
        match ops.castValue value with
        | .error e => resultWithState (.error e) d
        | .ok value => resultWithState (.ok (ops.valueToAny value)) d

/--
Julia source: base/iddict.jl:117-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = pop!(d, key, secret_table_token)
    val === secret_table_token && throw(KeyError(key))
    return val::V
end
```
-/
def pop {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) (key : A) :
    CallResult E (IdDict K V A HT) A :=
  let removed := popDefault ops d key ops.secretToken
  match removed.result with
  | .error e => resultWithState (.error e) removed.state
  | .ok value =>
      if ops.sameIdentity value ops.secretToken then resultWithState (.error (ops.keyError key)) removed.state
      else
        match ops.castValue value with
        | .error e => resultWithState (.error e) removed.state
        | .ok value => resultWithState (.ok (ops.valueToAny value)) removed.state

/--
Julia source: base/iddict.jl:123-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete!(d::IdDict{K}, @nospecialize(key)) where K
    pop!(d, key, secret_table_token)
    d
end
```
-/
def deleteBang {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) (key : A) :
    CallResult E (IdDict K V A HT) (IdDict K V A HT) :=
  let removed := popDefault ops d key ops.secretToken
  match removed.result with
  | .error e => resultWithState (.error e) removed.state
  | .ok _ => resultWithState (.ok removed.state) removed.state

/--
Julia source: base/iddict.jl:128-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(d::IdDict)
    d.ht = Memory{Any}(undef, 32)
    ht = d.ht
    t = @_gc_preserve_begin ht
    memset(unsafe_convert(Ptr{Cvoid}, ht), 0, sizeof(ht) % UInt)
    @_gc_preserve_end t
    d.ndel = 0
    d.count = 0
    return d
end
```
-/
def emptyBang {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
    CallResult E (IdDict K V A HT) (IdDict K V A HT) :=
  match ops.allocate 32 with
  | .error e => resultWithState (.error e) d
  | .ok ht =>
      let d1 : IdDict K V A HT := ⟨ht, d.count, d.ndel⟩
      let token := ops.preserveBegin d1.ht
      let pointer := ops.unsafeConvert d1.ht
      let cleared := ops.memsetZero d1.ht pointer (ops.sizeofMemory d1.ht)
      let ended := ops.preserveEnd token
      let d2 : IdDict K V A HT := ⟨cleared, d1.count, JInt.wrap .i64 0⟩
      let d3 : IdDict K V A HT := ⟨d2.ht, JInt.wrap .i64 0, d2.ndel⟩
      let _ := cleared
      let _ := ended
      resultWithState (.ok d3) d3

/--
Julia source: base/iddict.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_oidd_nextind(a, i) = reinterpret(Int, ccall(:jl_eqtable_nextind, Csize_t, (Any, Csize_t), a, i))
```
-/
def oiddNextind {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (a : HT) (i : JInt .u64) : JInt .i64 :=
  ops.reinterpretInt (ops.eqtableNextind a i)

/--
Julia source: base/iddict.jl:141-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(d::IdDict{K,V}, idx=0) where {K, V}
    idx = _oidd_nextind(d.ht, idx%UInt)
    idx == -1 && return nothing
    return (Pair{K, V}(d.ht[idx + 1]::K, d.ht[idx + 2]::V), idx + 2)
end
```
-/
def iterate {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (cursor : Option (JInt .i64)) :
    Except E (Option ((K × V) × JInt .i64)) := do
  let rawIndex ← match cursor with
    | none => ops.toUInt (JInt.wrap .i64 0)
    | some index => ops.toUInt index
  let idx := oiddNextind ops d.ht rawIndex
  if idx.val == -1 then .ok none
  else do
    let rawKey ← ops.memoryAt d.ht (idx + JInt.wrap .i64 1)
    let key ← ops.castKey rawKey
    let rawValue ← ops.memoryAt d.ht (idx + JInt.wrap .i64 2)
    let value ← ops.castValue rawValue
    .ok (some ((key, value), idx + JInt.wrap .i64 2))

/--
Julia source: base/iddict.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(d::IdDict) = d.count
```
-/
def length {K V A HT : Type} (d : IdDict K V A HT) : JInt .i64 := d.count

/--
Julia source: base/iddict.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(d::IdDict) = typeof(d)(d)
```
-/
def copyDict {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
    Except E (IdDict K V A HT) := copyConstruct ops d

/--
Julia source: base/iddict.jl:151-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    if val === secret_table_token
        val = isa(default, V) ? default : convert(V, default)::V
        setindex!(d, val, key)
        return val
    else
        return val::V
    end
end
```
-/
def getBang {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (key default : A) : CallResult E (IdDict K V A HT) A :=
  let value := ops.eqtableGet d.ht key ops.secretToken
  if ops.sameIdentity value ops.secretToken then
    let stored :=
      if ops.isValue default then Except.ok default
      else do
        let converted ← ops.convertValue default
        let converted ← ops.castValue converted
        .ok (ops.valueToAny converted)
    match stored with
    | .error e => resultWithState (.error e) d
    | .ok value =>
        let inserted := setindex! ops d value key
        match inserted.result with
        | .error e => resultWithState (.error e) inserted.state
        | .ok _ => resultWithState (.ok value) inserted.state
  else
    match ops.castValue value with
    | .error e => resultWithState (.error e) d
    | .ok value => resultWithState (.ok (ops.valueToAny value)) d

/--
Julia source: base/iddict.jl:162-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    if val === secret_table_token
        return default()
    else
        return val::V
    end
end
```
-/
def getCallable {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (default : Unit → Except E A) (key : A) : Except E A := do
  let value := ops.eqtableGet d.ht key ops.secretToken
  if ops.sameIdentity value ops.secretToken then default ()
  else
    let value ← ops.castValue value
    .ok (ops.valueToAny value)

/--
Julia source: base/iddict.jl:171-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, d::IdDict{K,V}, @nospecialize(key)) where {K, V}
    val = ccall(:jl_eqtable_get, Any, (Any, Any, Any), d.ht, key, secret_table_token)
    if val === secret_table_token
        val = default()
        if !isa(val, V)
            val = convert(V, val)::V
        end
        setindex!(d, val, key)
        return val
    else
        return val::V
    end
end
```
-/
def getBangCallable {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (default : Unit → Except E A) (key : A) : CallResult E (IdDict K V A HT) A :=
  let value := ops.eqtableGet d.ht key ops.secretToken
  if ops.sameIdentity value ops.secretToken then
    match default () with
    | .error e => resultWithState (.error e) d
    | .ok value =>
        let value :=
          if ops.isValue value then Except.ok value
          else do
            let converted ← ops.convertValue value
            let converted ← ops.castValue converted
            .ok (ops.valueToAny converted)
        match value with
        | .error e => resultWithState (.error e) d
        | .ok value =>
            let inserted := setindex! ops d value key
            match inserted.result with
            | .error e => resultWithState (.error e) inserted.state
            | .ok _ => resultWithState (.ok value) inserted.state
  else
    match ops.castValue value with
    | .error e => resultWithState (.error e) d
    | .ok value => resultWithState (.ok (ops.valueToAny value)) d

/--
Julia source: base/iddict.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(@nospecialize(k), v::KeySet{<:Any,<:IdDict}) = get(v.dict, k, secret_table_token) !== secret_table_token
```
-/
def inKeySet {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (v : IdKeySet K V A HT) (key : A) :
    Except E Bool := do
  let value ← get ops v.dict key ops.secretToken
  .ok (!ops.sameIdentity value ops.secretToken)

/--
Julia source: base/iddict.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, d::IdDict) = filter_in_one_pass!(f, d)
```
-/
def filterBang {T K V A HT : Type}
    (ops : JuliaLean.base.abstractdict.DictOps T (IdDict K V A HT) K V)
    (predicate : K × V → Bool) (d : IdDict K V A HT) :
    JuliaLean.base.abstractdict.Result (IdDict K V A HT) :=
  JuliaLean.base.abstractdict.filterInOnePassAD ops predicate d

/-- Collect an iterator by repeatedly applying the model of `iterate`. -/
def iterateAllSteps {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
    Nat → Option (JInt .i64) → Except E (List (K × V))
  | 0, _ => .ok []
  | fuel + 1, cursor => do
      let stateArg : Option (JInt .i64) := cursor
      match ← iterate ops d stateArg with
      | none => .ok []
      | some (pair, next) =>
          let rest ← iterateAllSteps ops d fuel (some next)
          .ok (pair :: rest)

/-- Collect up to one more item than the live count, so an invalid count or iterator is visible. -/
def iterateAll {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
    Except E (List (K × V)) :=
  iterateAllSteps ops d (d.count.val.toNat + 1) none

inductive Operation (A : Type) where
  | set (key value : A)
  | delete (key : A)
  | pop (key : A)
  | popDefault (key default : A)
  | getBang (key default : A)
  | getBangCallable (key value : A)
  | empty
  | sizeHint (newSize : JInt .i64)
  deriving Repr

def applyOperation {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT) :
    Operation A → IdDict K V A HT
  | .set key value => (setindex! ops d value key).state
  | .delete key => (deleteBang ops d key).state
  | .pop key => (pop ops d key).state
  | .popDefault key default => (popDefault ops d key default).state
  | .getBang key default => (getBang ops d key default).state
  | .getBangCallable key value => (getBangCallable ops d (fun _ => .ok value) key).state
  | .empty => (emptyBang ops d).state
  | .sizeHint newSize => (sizehint! ops d newSize).state

def runOperations {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) :
    List (Operation A) → IdDict K V A HT → IdDict K V A HT
  | [], d => d
  | operation :: rest, d => runOperations ops rest (applyOperation ops d operation)

def referenceOperation {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (entries : List (A × A)) :
    Operation A → List (A × A)
  | .set key value =>
      if !ops.isKey key then entries
      else
        match (do
          let value ← if ops.isValue value then Except.ok value else ops.convertValue value
          ops.castValue value) with
        | .error _ => entries
        | .ok value => referenceSet ops.sameIdentity entries key (ops.valueToAny value)
  | .delete key => referenceDelete ops.sameIdentity entries key
  | .pop key => referenceDelete ops.sameIdentity entries key
  | .popDefault key _ => referenceDelete ops.sameIdentity entries key
  | .getBang key default =>
      if (referenceLookup ops.sameIdentity entries key).isSome then entries
      else if !ops.isKey key then entries
      else
        match (do
          let value ← if ops.isValue default then Except.ok default else ops.convertValue default
          ops.castValue value) with
        | .error _ => entries
        | .ok value => referenceSet ops.sameIdentity entries key (ops.valueToAny value)
  | .getBangCallable key value =>
      if (referenceLookup ops.sameIdentity entries key).isSome then entries
      else if !ops.isKey key then entries
      else
        match (do
          let value ← if ops.isValue value then Except.ok value else ops.convertValue value
          ops.castValue value) with
        | .error _ => entries
        | .ok value => referenceSet ops.sameIdentity entries key (ops.valueToAny value)
  | .empty => []
  | .sizeHint _ => entries

def runReference {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) :
    List (Operation A) → List (A × A) → List (A × A)
  | [], entries => entries
  | operation :: rest, entries => runReference ops rest (referenceOperation ops entries operation)

def mapsEquivalent {A : Type} (sameIdentity : A → A → Bool)
    (left right : List (A × A)) : Prop :=
  ∀ key, referenceLookup sameIdentity left key = referenceLookup sameIdentity right key

def identityKeysDistinct {A B : Type} (sameIdentity : A → A → Bool) :
    List (A × B) → Prop
  | [] => True
  | (key, _) :: rest =>
      (∀ pair ∈ rest, sameIdentity key pair.1 = false) ∧
        identityKeysDistinct sameIdentity rest

def iterateLookup {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) : List (K × V) → A → Option A
  | [], _ => none
  | (key, value) :: rest, query =>
      if ops.sameIdentity query (ops.keyToAny key) then some (ops.valueToAny value)
      else iterateLookup ops rest query

def iterateKeysDistinct {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) : List (K × V) → Prop
  | [] => True
  | (key, _) :: rest =>
      (∀ pair ∈ rest, ops.sameIdentity (ops.keyToAny key) (ops.keyToAny pair.1) = false) ∧
        iterateKeysDistinct ops rest

namespace RuntimeOps

/-- Contracts of Julia's identity-table C calls and memory operations. -/
structure Lawful {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) : Prop where
  identity_refl : ∀ value, ops.sameIdentity value value = true
  identity_symm : ∀ a b, ops.sameIdentity a b = ops.sameIdentity b a
  identity_trans : ∀ a b c, ops.sameIdentity a b = true →
    ops.sameIdentity b c = true → ops.sameIdentity a c = true
  table_pairs_distinct : ∀ (d : IdDict K V A HT),
    identityKeysDistinct ops.sameIdentity (ops.tablePairs d.ht)
  table_pairs_count : ∀ (d : IdDict K V A HT),
    d.count.val.toNat = (ops.tablePairs d.ht).length
  table_keys_typed : ∀ (d : IdDict K V A HT) pair, pair ∈ ops.tablePairs d.ht →
    ∃ key, ops.castKey pair.1 = .ok key ∧ ops.keyToAny key = pair.1
  table_values_typed : ∀ (d : IdDict K V A HT) pair, pair ∈ ops.tablePairs d.ht →
    ∃ value, ops.castValue pair.2 = .ok value ∧ ops.valueToAny value = pair.2
  value_roundtrip : ∀ value,
    ops.isValue (ops.valueToAny value) = true ∧
      ops.castValue (ops.valueToAny value) = .ok value
  eqtable_get : ∀ ht key default,
    ops.eqtableGet ht key default =
      (referenceLookup ops.sameIdentity (ops.tablePairs ht) key).getD default
  eqtable_put : ∀ ht key value ht' inserted,
    ops.eqtablePut ht key value = .ok (ht', inserted) →
    mapsEquivalent ops.sameIdentity (ops.tablePairs ht')
      (referenceSet ops.sameIdentity (ops.tablePairs ht) key value) ∧
    inserted.val = if (referenceLookup ops.sameIdentity (ops.tablePairs ht) key).isSome then 0 else 1
  eqtable_pop : ∀ ht key default ht' value found,
    ops.eqtablePop ht key default = .ok (ht', value, found) →
    match referenceLookup ops.sameIdentity (ops.tablePairs ht) key with
    | none =>
        value = default ∧ found.val = 0 ∧
          mapsEquivalent ops.sameIdentity (ops.tablePairs ht') (ops.tablePairs ht)
    | some stored =>
        value = stored ∧ found.val ≠ 0 ∧
          mapsEquivalent ops.sameIdentity (ops.tablePairs ht')
            (referenceDelete ops.sameIdentity (ops.tablePairs ht) key)
  allocate_empty : ∀ ht, ops.allocate 32 = .ok ht →
    ops.memoryLength ht = JInt.wrap .i64 32 ∧ ops.tablePairs ht = []
  allocate_fresh : ∀ ht (d : IdDict K V A HT),
    ops.allocate 32 = .ok ht → ops.sameMemory ht d.ht = false
  copy_preserves : ∀ ht ht', ops.copyMemory ht = .ok ht' →
    mapsEquivalent ops.sameIdentity (ops.tablePairs ht') (ops.tablePairs ht)
  copy_fresh : ∀ ht ht', ops.copyMemory ht = .ok ht' → ops.sameMemory ht' ht = false
  rehash_preserves : ∀ {N : Type} (ht : HT) (size : N) (ht' : HT),
    ops.rehashMemory ht size = .ok ht' →
      mapsEquivalent ops.sameIdentity (ops.tablePairs ht') (ops.tablePairs ht)
  rehash_length : ∀ {N : Type} (ht : HT) (size : N) (ht' : HT) (wordSize : JInt .u64),
    ops.rehashMemory ht size = .ok ht' → ops.toUInt size = .ok wordSize →
      ops.memoryLength ht' = JuliaLean.base.int.remT .i64 wordSize
  clear_memory : ∀ ht ptr size,
    ops.tablePairs (ops.memsetZero ht ptr size) = [] ∧
      ops.memoryLength (ops.memsetZero ht ptr size) = ops.memoryLength ht
  table_slots_ordered : ∀ ht, slotsIncreasing (ops.tableSlots ht)
  table_slots_pairs : ∀ ht,
    List.Perm ((ops.tableSlots ht).map fun slot => (slot.key, slot.value)) (ops.tablePairs ht)
  nextind_layout : ∀ ht start,
    let aligned := if start.val % 2 = 1 then start + JInt.wrap .u64 1 else start
    ops.eqtableNextind ht start =
      match (ops.tableSlots ht).find? (fun slot => decide (aligned.val ≤ slot.index.val)) with
      | none => JInt.wrap .u64 (-1)
      | some slot => slot.index
  slot_key_memory : ∀ ht slot, slot ∈ ops.tableSlots ht →
    ops.memoryAt ht (ops.reinterpretInt slot.index + JInt.wrap .i64 1) = .ok slot.key
  slot_value_memory : ∀ ht slot, slot ∈ ops.tableSlots ht →
    ops.memoryAt ht (ops.reinterpretInt slot.index + JInt.wrap .i64 2) = .ok slot.value

end RuntimeOps

end JuliaLean.base.iddict

