import JuliaLean.Core
import JuliaLean.base.dict
import JuliaLean.base.iddict
import JuliaLean.base.hashing
import JuliaLean.base.iterators
import JuliaLean.base.reduce
import JuliaLean.base.operators
import JuliaLean.base.gcutils

/-!
# Model of `base/weakdict.jl`

Typed models of `WeakKeyDict` and `WeakValueIdDict` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Each wrapper keeps a typed object handle; field access, dictionary operations, locks, garbage-collection callbacks, and generic iteration are typed interfaces. The methods below preserve source checks, call order, cleanup loops, and error branches.
-/

namespace JuliaLean.base.weakdict

open JuliaLean

abbrev I64 := JInt .i64
abbrev WeakKeyRef (K : Type) := JuliaLean.base.hashing.WeakRef (Option K)
abbrev WeakKeyTable (K V : Type) := JuliaLean.base.dict.DictState (WeakKeyRef K) V

-- UNTRANSLATED
-- Source: base/weakdict.jl:1-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # weak key and weak value dictionaries
-- /Source
-- Reason: The license and section heading define no callable methods.

/--
Julia source: base/weakdict.jl:5-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct WeakKeyDictFinalizer{T}
    const d::T
end
```
-/
structure WeakKeyDictFinalizer (O : Type) where
  d : O

/--
Julia source: base/weakdict.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(d::WeakKeyDictFinalizer)(k) = d.d.dirty = true
```
-/
def weakKeyFinalizer {O K E : Type} (setDirty : O → Bool → Except E Unit)
    (d : WeakKeyDictFinalizer O) (_key : K) : Except E Bool := do
  setDirty d.d true
  pure true

-- UNTRANSLATED
-- Source: base/weakdict.jl:11-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     WeakKeyDict([itr])
-- 
-- `WeakKeyDict()` constructs a hash table where the keys are weak
-- references to objects which may be garbage collected even when
-- referenced in a hash table.
-- 
-- See [`Dict`](@ref) for further help.  Note, unlike [`Dict`](@ref),
-- `WeakKeyDict` does not convert keys on insertion, as this would imply the key
-- object was unreferenced anywhere before insertion.
-- 
-- See also [`WeakRef`](@ref).
-- """
-- /Source
-- Reason: The WeakKeyDict API documentation defines no callable methods.

/--
Julia source: base/weakdict.jl:24-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct WeakKeyDict{K,V} <: AbstractDict{K,V}
    const ht::Dict{WeakRef,V}
    const lock::ReentrantLock
    dirty::Bool
    finalizer::WeakKeyDictFinalizer

```
-/
structure WeakKeyDict (K V O : Type) where
  object : O


structure WeakKeyDictOps (K V O L E : Type) where
  newTable : Except E (WeakKeyTable K V)
  newLock : Except E L
  newObject : WeakKeyTable K V → L → Bool → Except E O
  makeFinalizer : O → WeakKeyDictFinalizer O
  setFinalizer : O → WeakKeyDictFinalizer O → Except E Unit
  finalizer : O → WeakKeyDictFinalizer O
  table : O → WeakKeyTable K V
  setTable : O → WeakKeyTable K V → Except E Unit
  dirty : O → Bool
  setDirty : O → Bool → Except E Unit
  lock : O → L
  withLock : {A : Type} → O → (Unit → A) → A
  isLocked : L → Bool
  lockDirect : L → Except E Unit
  unlockDirect : L → Except E Unit
  lockFunction : {F A : Type} → F → L → Except E A
  trylockFunction : {F A : Type} → F → L → Except E A
  callFinalizer : WeakKeyDictFinalizer O → K → Except E Bool
  isKey : {Q : Type} → Q → Bool
  isNothing : {Q : Type} → Q → Bool
  castKey : {Q : Type} → Q → K
  castStoredKey : K → Except E K
  limitrepr : {Q : Type} → Q → String
  keyTypeName : String
  argumentError : String → E
  keyError : {Q : Type} → Q → E
  innerGetKey : {Q : Type} → WeakKeyTable K V → Q → Except E (Option (WeakKeyRef K))
  innerSetIndex : {A : Type} → WeakKeyTable K V → WeakKeyRef K → A → Except E (WeakKeyTable K V)
  innerHasKey : {Q : Type} → WeakKeyTable K V → Q → Except E Bool
  innerGetIndex : {Q : Type} → WeakKeyTable K V → Q → Except E V
  innerGet : {Q D : Type} → WeakKeyTable K V → Q → D → Except E (V ⊕ D)
  innerGetCallable : {Q D : Type} → WeakKeyTable K V → Q → (Unit → Except E D) → Except E (V ⊕ D)
  innerPop : {Q : Type} → WeakKeyTable K V → Q → Except E (V × WeakKeyTable K V)
  innerPopDefault : {Q D : Type} → WeakKeyTable K V → Q → D → Except E ((V ⊕ D) × WeakKeyTable K V)
  innerDelete : {Q : Type} → WeakKeyTable K V → Q → Except E (WeakKeyTable K V)
  innerEmpty : WeakKeyTable K V → Except E (WeakKeyTable K V)
  innerSizehint : {N : Type} → WeakKeyTable K V → N → Bool → Except E (WeakKeyTable K V)
  innerLength : WeakKeyTable K V → Except E I64
  skipDeletedFloor : WeakKeyTable K V → Except E (I64 × WeakKeyTable K V)
  skipDeleted : WeakKeyTable K V → I64 → Except E I64
  keyAt : WeakKeyTable K V → I64 → Except E (WeakKeyRef K)
  deleteAt : WeakKeyTable K V → I64 → Except E (WeakKeyTable K V)
  innerIterate : {S : Type} → WeakKeyTable K V → Option S → Except E (Option ((WeakKeyRef K × V) × S))
  gcSafepoint : Except E Unit

private def weakKeyPopulate {K V O E P Q A : Type}
    (forPairs : P → (Q → A → Option (Except E Unit)) → Option (Except E Unit))
    (setIndex : WeakKeyDict K V O → A → Q → Option (Except E (WeakKeyDict K V O)))
    (dict : WeakKeyDict K V O) (pairs : P) : Option (Except E (WeakKeyDict K V O)) :=
  match forPairs pairs (fun key value =>
    match setIndex dict value key with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok _) => some (.ok ())) with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok ()) => some (.ok dict)

/--
Julia source: base/weakdict.jl:30-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    # Constructors mirror Dict's
    function WeakKeyDict{K,V}() where {K, V}
        t = new{K,V}(Dict{WeakRef,V}(), ReentrantLock(), false)
        t.finalizer = WeakKeyDictFinalizer(t)
        return t
    end
end
```
-/
def weakKeyDictNew {K V O L E : Type} (ops : WeakKeyDictOps K V O L E) :
    Except E (WeakKeyDict K V O) := do
  let table ← ops.newTable
  let lock ← ops.newLock
  let object ← ops.newObject table lock false
  let _ ← ops.setFinalizer object (ops.makeFinalizer object)
  pure ⟨object⟩

/--
Julia source: base/weakdict.jl:37-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function WeakKeyDict{K,V}(kv) where V where K
    h = WeakKeyDict{K,V}()
    for (k,v) in kv
        h[k] = v
    end
    return h
end
```
-/
def weakKeyFromIterable {K V O L E P Q A : Type}
    (ops : WeakKeyDictOps K V O L E)
    (forPairs : P → (Q → A → Option (Except E Unit)) → Option (Except E Unit))
    (setIndex : WeakKeyDict K V O → A → Q → Option (Except E (WeakKeyDict K V O)))
    (kv : P) : Option (Except E (WeakKeyDict K V O)) :=
  match weakKeyDictNew ops with
  | .error error => some (.error error)
  | .ok dict => weakKeyPopulate forPairs setIndex dict kv
/--
Julia source: base/weakdict.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict{K,V}(p::Pair) where V where K = setindex!(WeakKeyDict{K,V}(), p.second, p.first)
```
-/
def weakKeyFromPair {K V O L E Q A : Type}
    (ops : WeakKeyDictOps K V O L E)
    (setIndex : WeakKeyDict K V O → A → Q → Option (Except E (WeakKeyDict K V O)))
    (pair : Q × A) : Option (Except E (WeakKeyDict K V O)) :=
  match weakKeyDictNew ops with
  | .error error => some (.error error)
  | .ok dict =>
      match setIndex dict pair.2 pair.1 with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok result) => some (.ok result)

/--
Julia source: base/weakdict.jl:45-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function WeakKeyDict{K,V}(ps::Pair...) where V where K
    h = WeakKeyDict{K,V}()
    sizehint!(h, length(ps))
    for p in ps
        h[p.first] = p.second
    end
    return h
end
```
-/
def weakKeyFromPairs {K V O L E P Q A : Type}
    (ops : WeakKeyDictOps K V O L E)
    (pairsLength : P → Except E I64)
    (sizehint : WeakKeyDict K V O → I64 → Bool → Except E Unit)
    (forPairs : P → (Q → A → Option (Except E Unit)) → Option (Except E Unit))
    (setIndex : WeakKeyDict K V O → A → Q → Option (Except E (WeakKeyDict K V O)))
    (pairs : P) : Option (Except E (WeakKeyDict K V O)) :=
  match weakKeyDictNew ops with
  | .error error => some (.error error)
  | .ok dict =>
      match pairsLength pairs with
      | .error error => some (.error error)
      | .ok count =>
          match sizehint dict count true with
          | .error error => some (.error error)
          | .ok () => weakKeyPopulate forPairs setIndex dict pairs

/--
Julia source: base/weakdict.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict() = WeakKeyDict{Any,Any}()
```
-/
def weakKeyDefault {K V O E : Type}
    (constructAnyAny : Except E (WeakKeyDict K V O)) : Except E (WeakKeyDict K V O) :=
  constructAnyAny

/--
Julia source: base/weakdict.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict(kv::Tuple{}) = WeakKeyDict()
```
-/
def weakKeyEmptyTuple {K V O E : Type}
    (constructDefault : Except E (WeakKeyDict K V O)) (_ : Unit) : Except E (WeakKeyDict K V O) :=
  constructDefault

/--
Julia source: base/weakdict.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(d::WeakKeyDict) = WeakKeyDict(d)
```
-/
def weakKeyCopy {K V O E : Type}
    (copyConstructor : WeakKeyDict K V O → Option (Except E (WeakKeyDict K V O)))
    (dict : WeakKeyDict K V O) : Option (Except E (WeakKeyDict K V O)) :=
  copyConstructor dict

/--
Julia source: base/weakdict.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict(ps::Pair{K,V}...)           where {K,V} = WeakKeyDict{K,V}(ps)
```
-/
def weakKeyPairsKV {P W E : Type}
    (constructTyped : P → Option (Except E W)) (pairs : P) : Option (Except E W) :=
  constructTyped pairs

/--
Julia source: base/weakdict.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict(ps::Pair{K}...)             where {K}   = WeakKeyDict{K,Any}(ps)
```
-/
def weakKeyPairsK {P W E : Type}
    (constructAnyValue : P → Option (Except E W)) (pairs : P) : Option (Except E W) :=
  constructAnyValue pairs

/--
Julia source: base/weakdict.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict(ps::(Pair{K,V} where K)...) where {V}   = WeakKeyDict{Any,V}(ps)
```
-/
def weakKeyPairsV {P W E : Type}
    (constructAnyKey : P → Option (Except E W)) (pairs : P) : Option (Except E W) :=
  constructAnyKey pairs

/--
Julia source: base/weakdict.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict(ps::Pair...)                            = WeakKeyDict{Any,Any}(ps)
```
-/
def weakKeyPairsAny {P W E : Type}
    (constructAnyAny : P → Option (Except E W)) (pairs : P) : Option (Except E W) :=
  constructAnyAny pairs

/--
Julia source: base/weakdict.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakKeyDict(kv) = Base.dict_with_eltype((K, V) -> WeakKeyDict{K, V}, kv, eltype(kv))
```
-/
def weakKeyDictWithEltype {I T W E : Type}
    (dictWithEltype : I → T → Option (Except E W))
    (eltype : I → T) (kv : I) : Option (Except E W) :=
  dictWithEltype kv (eltype kv)

/--
Julia source: base/weakdict.jl:65-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cleanup_locked(h::WeakKeyDict)
    if h.dirty
        h.dirty = false
        idx = skip_deleted_floor!(h.ht)
        while idx != 0
            if h.ht.keys[idx].value === nothing
                _delete!(h.ht, idx)
            end
            idx = skip_deleted(h.ht, idx + 1)
        end
    end
    return h
end
```
-/
def weakKeyCleanupLocked {K V O L E : Type}
    (ops : WeakKeyDictOps K V O L E) (dict : WeakKeyDict K V O) :
    Option (Except E (WeakKeyDict K V O)) :=
  if !ops.dirty dict.object then some (.ok dict) else
    match ops.setDirty dict.object false with
    | .error error => some (.error error)
    | .ok () =>
        match ops.skipDeletedFloor (ops.table dict.object) with
        | .error error => some (.error error)
        | .ok (index, table) =>
            match ops.setTable dict.object table with
            | .error error => some (.error error)
            | .ok () =>
                let step (index : I64) : Except E (Sum (WeakKeyDict K V O) I64) := do
                  if index.val == 0 then pure (.inl dict) else do
                    let table := ops.table dict.object
                    let key ← ops.keyAt table index
                    if key.value.isNone then do
                      let table ← ops.deleteAt table index
                      let _ ← ops.setTable dict.object table
                      pure ()
                    let table := ops.table dict.object
                    let next ← ops.skipDeleted table (JuliaLean.base.int.add_int index (JInt.lit .i64 1))
                    if next.val == 0 then pure (.inl dict) else pure (.inr next)
                JuliaLean.base.reduce.whileLoop step index

/--
Julia source: base/weakdict.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizehint!(d::WeakKeyDict, newsz::Integer; shrink::Bool = true) = @lock d sizehint!(d.ht, newsz; shrink = shrink)
```
-/
def weakKeySizehint {K V O L E N : Type}
    (ops : WeakKeyDictOps K V O L E) (dict : WeakKeyDict K V O)
    (newsize : N) (shrink : Bool := true) : Except E (WeakKeyTable K V) :=
  ops.withLock dict.object fun _ => do
    let table ← ops.innerSizehint (ops.table dict.object) newsize shrink
    let _ ← ops.setTable dict.object table
    pure table

/--
Julia source: base/weakdict.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(d::WeakKeyDict, ::Type{K}, ::Type{V}) where {K, V} = WeakKeyDict{K, V}()
```
-/
def weakKeyEmpty {K V O E : Type}
    (constructTyped : Except E (WeakKeyDict K V O))
    (_keyType _valueType : Unit) : Except E (WeakKeyDict K V O) :=
  constructTyped

/--
Julia source: base/weakdict.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:WeakKeyDict}) = SizeUnknown()
```
-/
def weakKeyIteratorSize : JuliaLean.base.iterators.IteratorSizeTag := .sizeUnknown

/--
Julia source: base/weakdict.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islocked(wkh::WeakKeyDict) = islocked(wkh.lock)
```
-/
def weakKeyIslocked {K V O L : Type} (getLock : O → L) (isLocked : L → Bool)
    (dict : WeakKeyDict K V O) : Bool :=
  isLocked (getLock dict.object)

/--
Julia source: base/weakdict.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(wkh::WeakKeyDict) = lock(wkh.lock)
```
-/
def weakKeyLock {K V O L E : Type} (getLock : O → L) (lock : L → Except E Unit)
    (dict : WeakKeyDict K V O) : Except E Unit :=
  lock (getLock dict.object)

/--
Julia source: base/weakdict.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(wkh::WeakKeyDict) = unlock(wkh.lock)
```
-/
def weakKeyUnlock {K V O L E : Type} (getLock : O → L) (unlock : L → Except E Unit)
    (dict : WeakKeyDict K V O) : Except E Unit :=
  unlock (getLock dict.object)

/--
Julia source: base/weakdict.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(f, wkh::WeakKeyDict) = lock(f, wkh.lock)
```
-/
def weakKeyLockFunction {K V O L E F A : Type}
    (getLock : O → L) (lock : F → L → Except E A) (f : F)
    (dict : WeakKeyDict K V O) : Except E A :=
  lock f (getLock dict.object)

/--
Julia source: base/weakdict.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trylock(f, wkh::WeakKeyDict) = trylock(f, wkh.lock)
```
-/
def weakKeyTrylockFunction {K V O L E F A : Type}
    (getLock : O → L) (trylock : F → L → Except E A) (f : F)
    (dict : WeakKeyDict K V O) : Except E A :=
  trylock f (getLock dict.object)

/--
Julia source: base/weakdict.jl:90-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(wkh::WeakKeyDict{K}, v, key) where K
    !isa(key, K) && throw(ArgumentError("$(limitrepr(key)) is not a valid key for type $K"))
    # 'nothing' is not valid both because 'finalizer' will reject it,
    # and because we therefore use it as a sentinel value
    key === nothing && throw(ArgumentError("`nothing` is not a valid WeakKeyDict key"))
    lock(wkh) do
        _cleanup_locked(wkh)
        k = getkey(wkh.ht, key, nothing)
        if k === nothing
            finalizer(wkh.finalizer, key)
            k = WeakRef(key)
        else
            k.value = key
        end
        wkh.ht[k] = v
    end
    return wkh
end
```
-/
def weakKeySetindex {K V O L E Q A : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (value : A) (key : Q) :
    Option (Except E (WeakKeyDict K V O)) :=
  if !ops.isKey key then
    some (.error (ops.argumentError (ops.limitrepr key ++ " is not a valid key for type " ++ ops.keyTypeName)))
  else if ops.isNothing key then
    some (.error (ops.argumentError "`nothing` is not a valid WeakKeyDict key"))
  else
    let key := ops.castKey key
    ops.withLock dict.object fun _ =>
      match weakKeyCleanupLocked ops dict with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok _) => some (do
          let table := ops.table dict.object
          let existing ← ops.innerGetKey table key
          let weak ← match existing with
            | none => do
                let _ ← ops.callFinalizer (ops.finalizer dict.object) key
                pure ⟨some key⟩
            | some weak => pure { weak with value := some key }
          let table ← ops.innerSetIndex table weak value
          let _ ← ops.setTable dict.object table
          pure dict)

/--
Julia source: base/weakdict.jl:108-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(wkh::WeakKeyDict{K}, key, default) where {K}
    v = lock(wkh) do
        if key !== nothing && haskey(wkh.ht, key)
            wkh.ht[key]
        else
            wkh[key] = default
        end
    end
    return v
end
```
-/
def weakKeyGetBang {K V O L E Q D : Type} (ops : WeakKeyDictOps K V O L E)
    (setIndex : WeakKeyDict K V O → D → Q → Option (Except E (WeakKeyDict K V O)))
    (dict : WeakKeyDict K V O) (key : Q) (default : D) : Option (Except E (V ⊕ D)) :=
  ops.withLock dict.object fun _ =>
    if ops.isNothing key then
      match setIndex dict default key with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok _) => some (.ok (.inr default))
    else
      match ops.innerHasKey (ops.table dict.object) key with
      | .error error => some (.error error)
      | .ok true => some ((fun value => .inl value) <$> ops.innerGetIndex (ops.table dict.object) key)
      | .ok false =>
          match setIndex dict default key with
          | none => none
          | some (.error error) => some (.error error)
          | some (.ok _) => some (.ok (.inr default))

/--
Julia source: base/weakdict.jl:118-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, wkh::WeakKeyDict{K}, key) where {K}
    v = lock(wkh) do
        if key !== nothing && haskey(wkh.ht, key)
            wkh.ht[key]
        else
            wkh[key] = default()
        end
    end
    return v
end
```
-/
def weakKeyGetBangCallable {K V O L E Q D : Type} (ops : WeakKeyDictOps K V O L E)
    (setIndex : WeakKeyDict K V O → D → Q → Option (Except E (WeakKeyDict K V O)))
    (dict : WeakKeyDict K V O) (key : Q) (default : Unit → Except E D) :
    Option (Except E (V ⊕ D)) :=
  ops.withLock dict.object fun _ =>
    if ops.isNothing key then
      match default () with
      | .error error => some (.error error)
      | .ok value =>
          match setIndex dict value key with
          | none => none
          | some (.error error) => some (.error error)
          | some (.ok _) => some (.ok (.inr value))
    else
      match ops.innerHasKey (ops.table dict.object) key with
      | .error error => some (.error error)
      | .ok true => some ((fun value => .inl value) <$> ops.innerGetIndex (ops.table dict.object) key)
      | .ok false =>
          match default () with
          | .error error => some (.error error)
          | .ok value =>
              match setIndex dict value key with
              | none => none
              | some (.error error) => some (.error error)
              | some (.ok _) => some (.ok (.inr value))

/--
Julia source: base/weakdict.jl:129-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getkey(wkh::WeakKeyDict{K}, kk, default) where K
    k = lock(wkh) do
        local k = getkey(wkh.ht, kk, nothing)
        k === nothing && return nothing
        return k.value
    end
    return k === nothing ? default : k::K
end
```
-/
def weakKeyGetkey {K V O L E Q D : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) (default : D) : Except E (K ⊕ D) := do
  let referent ← ops.withLock dict.object fun _ => do
    let weak ← ops.innerGetKey (ops.table dict.object) key
    pure (weak.bind (fun weak => weak.value))
  match referent with
  | none => pure (.inr default)
  | some key => .inl <$> ops.castStoredKey key

structure WeakKeyValueIterator (K V O : Type) where
  dict : WeakKeyDict K V O

/--
Julia source: base/weakdict.jl:138-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map!(f, iter::ValueIterator{<:WeakKeyDict})= map!(f, values(iter.dict.ht))
```
-/
def weakKeyMapValues {K V O L E F I R : Type}
    (ops : WeakKeyDictOps K V O L E)
    (values : WeakKeyTable K V → I) (mapBang : F → I → Except E R)
    (f : F) (iter : WeakKeyValueIterator K V O) : Except E R :=
  mapBang f (values (ops.table iter.dict.object))

/--
Julia source: base/weakdict.jl:140-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(wkh::WeakKeyDict{K}, key, default) where {K}
    key === nothing && throw(KeyError(nothing))
    lock(wkh) do
        return get(wkh.ht, key, default)
    end
end
```
-/
def weakKeyGetDefault {K V O L E Q D : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) (default : D) : Except E (V ⊕ D) :=
  if ops.isNothing key then .error (ops.keyError key)
  else ops.withLock dict.object fun _ => ops.innerGet (ops.table dict.object) key default

/--
Julia source: base/weakdict.jl:146-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, wkh::WeakKeyDict{K}, key) where {K}
    key === nothing && throw(KeyError(nothing))
    lock(wkh) do
        return get(default, wkh.ht, key)
    end
end
```
-/
def weakKeyGetCallable {K V O L E Q D : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) (default : Unit → Except E D) : Except E (V ⊕ D) :=
  if ops.isNothing key then .error (ops.keyError key)
  else ops.withLock dict.object fun _ => ops.innerGetCallable (ops.table dict.object) key default

/--
Julia source: base/weakdict.jl:152-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(wkh::WeakKeyDict{K}, key) where {K}
    key === nothing && throw(KeyError(nothing))
    lock(wkh) do
        return pop!(wkh.ht, key)
    end
end
```
-/
def weakKeyPop {K V O L E Q : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) : Except E V :=
  if ops.isNothing key then .error (ops.keyError key)
  else ops.withLock dict.object fun _ => do
    let (value, table) ← ops.innerPop (ops.table dict.object) key
    let _ ← ops.setTable dict.object table
    pure value

/--
Julia source: base/weakdict.jl:158-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(wkh::WeakKeyDict{K}, key, default) where {K}
    key === nothing && return default
    lock(wkh) do
        return pop!(wkh.ht, key, default)
    end
end
```
-/
def weakKeyPopDefault {K V O L E Q D : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) (default : D) : Except E (V ⊕ D) :=
  if ops.isNothing key then pure (.inr default)
  else ops.withLock dict.object fun _ => do
    let (value, table) ← ops.innerPopDefault (ops.table dict.object) key default
    let _ ← ops.setTable dict.object table
    pure value

/--
Julia source: base/weakdict.jl:164-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete!(wkh::WeakKeyDict, key)
    key === nothing && return wkh
    lock(wkh) do
        delete!(wkh.ht, key)
    end
    return wkh
```
-/
def weakKeyDelete {K V O L E Q : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) : Except E (WeakKeyDict K V O) :=
  if ops.isNothing key then pure dict
  else ops.withLock dict.object fun _ => do
    let table ← ops.innerDelete (ops.table dict.object) key
    let _ ← ops.setTable dict.object table
    pure dict

/--
Julia source: base/weakdict.jl:171-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(wkh::WeakKeyDict)
    lock(wkh) do
        empty!(wkh.ht)
    end
    return wkh
end
```
-/
def weakKeyEmptyBang {K V O L E : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) : Except E (WeakKeyDict K V O) :=
  ops.withLock dict.object fun _ => do
    let table ← ops.innerEmpty (ops.table dict.object)
    let _ ← ops.setTable dict.object table
    pure dict

/--
Julia source: base/weakdict.jl:177-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function haskey(wkh::WeakKeyDict{K}, key) where {K}
    key === nothing && return false
    lock(wkh) do
        return haskey(wkh.ht, key)
    end
end
```
-/
def weakKeyHaskey {K V O L E Q : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) : Except E Bool :=
  if ops.isNothing key then pure false
  else ops.withLock dict.object fun _ => ops.innerHasKey (ops.table dict.object) key

/--
Julia source: base/weakdict.jl:183-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(wkh::WeakKeyDict{K}, key) where {K}
    key === nothing && throw(KeyError(nothing))
    lock(wkh) do
        return getindex(wkh.ht, key)
    end
end
```
-/
def weakKeyGetindex {K V O L E Q : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (key : Q) : Except E V :=
  if ops.isNothing key then .error (ops.keyError key)
  else ops.withLock dict.object fun _ => ops.innerGetIndex (ops.table dict.object) key

/--
Julia source: base/weakdict.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(wkh::WeakKeyDict) = length(wkh) == 0
```
-/
def weakKeyIsempty {K V O E : Type}
    (length : WeakKeyDict K V O → Option (Except E I64)) (dict : WeakKeyDict K V O) :
    Option (Except E Bool) :=
  match length dict with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok count) => some (.ok (count.val == 0))

/--
Julia source: base/weakdict.jl:190-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(t::WeakKeyDict)
    lock(t) do
        _cleanup_locked(t)
        return length(t.ht)
    end
end
```
-/
def weakKeyLength {K V O L E : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) : Option (Except E I64) :=
  ops.withLock dict.object fun _ =>
    match weakKeyCleanupLocked ops dict with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok _) => some (ops.innerLength (ops.table dict.object))

/--
Julia source: base/weakdict.jl:197-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(t::WeakKeyDict{K,V}, state...) where {K, V}
    @lock t begin
        while true
            y = iterate(t.ht, state...)
            y === nothing && return nothing
            wkv, state = y
            k = wkv[1].value
            GC.safepoint() # ensure `k` is now gc-rooted
            k === nothing && continue # indicates `k` is scheduled for deletion
            kv = Pair{K,V}(k::K, wkv[2])
            return (kv, state)
        end
    end
end
```
-/
def weakKeyIterate {K V O L E S : Type} (ops : WeakKeyDictOps K V O L E)
    (dict : WeakKeyDict K V O) (state : Option S) :
    Option (Except E (Option ((K × V) × S))) :=
  ops.withLock dict.object fun _ =>
    let step (state : Option S) : Except E (Sum (Option ((K × V) × S)) (Option S)) := do
      let next ← ops.innerIterate (ops.table dict.object) state
      match next with
      | none => pure (.inl none)
      | some ((weak, value), nextState) => do
          let _ ← ops.gcSafepoint
          match weak.value with
          | none => pure (.inr (some nextState))
          | some key => do
              let key ← ops.castStoredKey key
              pure (.inl (some ((key, value), nextState)))
    JuliaLean.base.reduce.whileLoop step state

/--
Julia source: base/weakdict.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds Iterators.only(d::WeakKeyDict) = Iterators._only(d, first)
```
-/
def weakKeyOnly {K V O E : Type}
    (only : WeakKeyDict K V O → (WeakKeyDict K V O → Option (Except E (K × V))) →
      Option (Except E (K × V)))
    (first : WeakKeyDict K V O → Option (Except E (K × V)))
    (dict : WeakKeyDict K V O) : Option (Except E (K × V)) :=
  only dict first

/--
Julia source: base/weakdict.jl:214-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, d::WeakKeyDict) = filter_in_one_pass!(f, d)
```
-/
def weakKeyFilter {K V O E F : Type}
    (filterInOnePass : F → WeakKeyDict K V O → Option (Except E (WeakKeyDict K V O)))
    (f : F) (dict : WeakKeyDict K V O) : Option (Except E (WeakKeyDict K V O)) :=
  filterInOnePass f dict

-- UNTRANSLATED
-- Source: base/weakdict.jl:217-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # weak identity dictionaries
-- 
-- /Source
-- Reason: The section heading introduces the weak-identity dictionary methods.

/--
Julia source: base/weakdict.jl:219-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct WeakValueIdDictFinalizer{T}
    const d::T
end
```
-/
structure WeakValueIdDictFinalizer (O : Type) where
  d : O

/--
Julia source: base/weakdict.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(d::WeakValueIdDictFinalizer)(v) = d.d.dirty = true
```
-/
def weakValueIdFinalizer {O E : Type} (setDirty : O → Bool → Except E Unit)
    (finalizer : WeakValueIdDictFinalizer O) {Q : Type} (_value : Q) : Except E Bool := do
  let _ ← setDirty finalizer.d true
  pure true

-- UNTRANSLATED
-- Source: base/weakdict.jl:224-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     WeakValueIdDict
-- 
-- `WeakValueIdDict` is an identity-keyed dictionary like [`IdDict`](@ref).
-- However, unlike `IdDict`, the dictionary holds its values weakly.
-- 
-- See also [`WeakKeyDict`](@ref), which differs in two ways:
-- 1. `WeakKeyDict` holds its *keys* weakly, while `WeakValueIdDict` holds its *values* weakly.
-- 2. `WeakKeyDict` is equality-keyed, while `WeakValueIdDict` is identity-keyed.
-- 
-- See also [`WeakRef`](@ref).
-- """
-- /Source
-- Reason: The WeakValueIdDict API description contains no callable method.

/--
Julia source: base/weakdict.jl:236-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct WeakValueIdDict{K,V} <: AbstractDict{K,V}
    const ht::IdDict{K,WeakRef}
    const lock::ReentrantLock
    dirty::Bool
    # concretely typed (self-referentially) so that registering the finalizer
    # remains statically resolvable, e.g. under `--trim`
    finalizer::WeakValueIdDictFinalizer{WeakValueIdDict{K,V}}

```
-/
structure WeakValueIdDict (K V O : Type) where
  object : O

open JuliaLean.src.identity_runtime (Word M Error fail)

structure WeakValueIdDictOps (K V O L : Type) where
  inner : JuliaLean.base.iddict.Callees
  keyType : Word
  weakRefType : Word
  newLock : M L
  newObject : Word → L → Bool → M O
  makeFinalizer : O → WeakValueIdDictFinalizer O
  setFinalizer : O → WeakValueIdDictFinalizer O → M Unit
  finalizer : O → WeakValueIdDictFinalizer O
  table : O → Word
  dirty : O → M Bool
  setDirty : O → Bool → M Unit
  lock : O → L
  withLock : {R : Type} → O → (Unit → M R) → M R
  isLocked : L → Bool
  lockDirect : L → M Unit
  unlockDirect : L → M Unit
  callFinalizer : WeakValueIdDictFinalizer O → Word → M Bool
  isKey : {Q : Type} → Q → Bool
  isNothing : {Q : Type} → Q → Bool
  keyToAny : {Q : Type} → Q → Word
  valueToAny : {Q : Type} → Q → Word
  castKey : Word → M K
  castPayload : Word → M V
  newWeakRef : Word → M Word
  weakPayload : Word → M (Option Word)
  pairFields : Word → M (Word × Word)
  keyTypeName : String
  limitrepr : {Q : Type} → Q → String
  nothing : Word

private def weakValuePopulate {K V O P Q B : Type}
    (forPairs : P → (Q → B → M Unit) → M Unit)
    (setIndex : WeakValueIdDict K V O → B → Q → M (WeakValueIdDict K V O))
    (dict : WeakValueIdDict K V O) (pairs : P) : M (WeakValueIdDict K V O) := do
  forPairs pairs fun key value => do
    let _ ← setIndex dict value key
    pure ()
  pure dict


private def weakValueDeleteDead {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) : List K → M (WeakValueIdDict K V O)
  | [] => pure dict
  | key :: rest => do
      let _ ← JuliaLean.base.iddict.deleteBang ops.inner (ops.table dict.object) (ops.keyToAny key)
      weakValueDeleteDead ops dict rest

private def weakValueLiveCountLoop {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L) (table : Word) (cursor count : I64) : M I64 := do
  match ← JuliaLean.base.iddict.iterate ops.inner table cursor with
  | none => pure count
  | some (pair, next) =>
    let (_, rawWeak) ← ops.pairFields pair
    let weak ← JuliaLean.base.iddict.assertType ops.inner rawWeak ops.weakRefType
    let value ← ops.weakPayload weak
    weakValueLiveCountLoop ops table next
      (JuliaLean.base.int.add_int count (JInt.wrap .i64 (if value.isSome then 1 else 0)))
partial_fixpoint

private def weakValueLiveCount {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L) (table : Word) : M I64 :=
  weakValueLiveCountLoop ops table (JInt.wrap .i64 0) (JInt.wrap .i64 0)

private def weakValueLiveSnapshotLoop {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L) (table : Word) (cursor : I64)
    (pairsRev : List (K × V)) : M (List (K × V)) := do
  match ← JuliaLean.base.iddict.iterate ops.inner table cursor with
  | none => pure pairsRev.reverse
  | some (pair, next) =>
    let (rawKey, rawWeak) ← ops.pairFields pair
    let weak ← JuliaLean.base.iddict.assertType ops.inner rawWeak ops.weakRefType
    match ← ops.weakPayload weak with
    | none => weakValueLiveSnapshotLoop ops table next pairsRev
    | some raw =>
      let key ← ops.castKey rawKey
      let value ← ops.castPayload raw
      weakValueLiveSnapshotLoop ops table next ((key, value) :: pairsRev)
partial_fixpoint

private def weakValueLiveSnapshot {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L) (table : Word) : M (List (K × V)) :=
  weakValueLiveSnapshotLoop ops table (JInt.wrap .i64 0) []

/--
Julia source: base/weakdict.jl:244-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function WeakValueIdDict{K,V}() where {K, V}
        t = new{K,V}(IdDict{K,WeakRef}(), ReentrantLock(), false)
        t.finalizer = WeakValueIdDictFinalizer(t)
        return t
    end
end
```
-/
def weakValueDictNew {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L) : M (WeakValueIdDict K V O) := do
  let table ← JuliaLean.base.iddict.emptyTyped ops.inner ops.keyType ops.weakRefType
  let lock ← ops.newLock
  let object ← ops.newObject table lock false
  ops.setFinalizer object (ops.makeFinalizer object)
  pure ⟨object⟩

/--
Julia source: base/weakdict.jl:250-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function WeakValueIdDict{K,V}(kv) where V where K
    h = WeakValueIdDict{K,V}()
    for (k,v) in kv
        h[k] = v
    end
    return h
end
```
-/
def weakValueFromIterable {K V O L P Q B : Type}
    (ops : WeakValueIdDictOps K V O L)
    (forPairs : P → (Q → B → M Unit) → M Unit)
    (setIndex : WeakValueIdDict K V O → B → Q → M (WeakValueIdDict K V O))
    (kv : P) : M (WeakValueIdDict K V O) := do
  weakValuePopulate forPairs setIndex (← weakValueDictNew ops) kv

/--
Julia source: base/weakdict.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict{K,V}(p::Pair) where V where K = setindex!(WeakValueIdDict{K,V}(), p.second, p.first)
```
-/
def weakValueFromPair {K V O L Q B : Type}
    (ops : WeakValueIdDictOps K V O L)
    (setIndex : WeakValueIdDict K V O → B → Q → M (WeakValueIdDict K V O))
    (pair : Q × B) : M (WeakValueIdDict K V O) := do
  setIndex (← weakValueDictNew ops) pair.2 pair.1

/--
Julia source: base/weakdict.jl:258-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function WeakValueIdDict{K,V}(ps::Pair...) where V where K
    h = WeakValueIdDict{K,V}()
    for p in ps
        h[p.first] = p.second
    end
    return h
end
```
-/
def weakValueFromPairs {K V O L P Q B : Type}
    (ops : WeakValueIdDictOps K V O L)
    (forPairs : P → (Q → B → M Unit) → M Unit)
    (setIndex : WeakValueIdDict K V O → B → Q → M (WeakValueIdDict K V O))
    (pairs : P) : M (WeakValueIdDict K V O) := do
  weakValuePopulate forPairs setIndex (← weakValueDictNew ops) pairs

/--
Julia source: base/weakdict.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict() = WeakValueIdDict{Any,Any}()
```
-/
def weakValueDefault {K V O : Type}
    (constructAnyAny : M (WeakValueIdDict K V O)) : M (WeakValueIdDict K V O) :=
  constructAnyAny

/--
Julia source: base/weakdict.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict(kv::Tuple{}) = WeakValueIdDict()
```
-/
def weakValueEmptyTuple {K V O : Type}
    (constructDefault : M (WeakValueIdDict K V O)) (_kv : Unit) :
    M (WeakValueIdDict K V O) :=
  constructDefault

/--
Julia source: base/weakdict.jl:268-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(d::WeakValueIdDict) = WeakValueIdDict(d)
```
-/
def weakValueCopy {K V O : Type}
    (copyConstructor : WeakValueIdDict K V O → M (WeakValueIdDict K V O))
    (dict : WeakValueIdDict K V O) : M (WeakValueIdDict K V O) :=
  copyConstructor dict

/--
Julia source: base/weakdict.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict(ps::Pair{K,V}...)           where {K,V} = WeakValueIdDict{K,V}(ps...)
```
-/
def weakValuePairsKV {P W : Type}
    (constructTyped : P → M W) (pairs : P) : M W :=
  constructTyped pairs

/--
Julia source: base/weakdict.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict(ps::Pair{K}...)             where {K}   = WeakValueIdDict{K,Any}(ps...)
```
-/
def weakValuePairsK {P W : Type}
    (constructAnyValue : P → M W) (pairs : P) : M W :=
  constructAnyValue pairs

/--
Julia source: base/weakdict.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict(ps::(Pair{K,V} where K)...) where {V}   = WeakValueIdDict{Any,V}(ps...)
```
-/
def weakValuePairsV {P W : Type}
    (constructAnyKey : P → M W) (pairs : P) : M W :=
  constructAnyKey pairs

/--
Julia source: base/weakdict.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict(ps::Pair...)                            = WeakValueIdDict{Any,Any}(ps...)
```
-/
def weakValuePairsAny {P W : Type}
    (constructAnyAny : P → M W) (pairs : P) : M W :=
  constructAnyAny pairs

/--
Julia source: base/weakdict.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WeakValueIdDict(kv) = dict_with_eltype((K, V) -> WeakValueIdDict{K, V}, kv, eltype(kv))
```
-/
def weakValueDictWithEltype {I T W : Type}
    (dictWithEltype : I → T → M W)
    (eltype : I → T) (kv : I) : M W :=
  dictWithEltype kv (eltype kv)

-- UNTRANSLATED
-- Source: base/weakdict.jl:277-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # an entry is live iff its value is; a dead entry is indistinguishable from an
-- # absent one (its key stays pinned until the next sweep)
-- /Source
-- Reason: The comments describe weak-value liveness but define no Julia method.

/--
Julia source: base/weakdict.jl:279-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sweep_locked(h::WeakValueIdDict{K}) where {K}
    h.dirty = false
    dead = K[]
    for (k, wr) in h.ht
        (wr::WeakRef).value === nothing && push!(dead, k)
    end
    for k in dead
        delete!(h.ht, k)
    end
    return h
end
```
-/
private def weakValueDeadKeys {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L) (table : Word) (cursor : I64)
    (deadRev : List K) : M (List K) := do
  match ← JuliaLean.base.iddict.iterate ops.inner table cursor with
  | none => pure deadRev.reverse
  | some (pair, next) =>
    let (rawKey, rawWeak) ← ops.pairFields pair
    let weak ← JuliaLean.base.iddict.assertType ops.inner rawWeak ops.weakRefType
    match ← ops.weakPayload weak with
    | none =>
      let key ← ops.castKey rawKey
      weakValueDeadKeys ops table next (key :: deadRev)
    | some _ => weakValueDeadKeys ops table next deadRev
partial_fixpoint

def weakValueSweepLocked {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) : M (WeakValueIdDict K V O) := do
  ops.setDirty dict.object false
  let dead ← weakValueDeadKeys ops (ops.table dict.object) (JInt.wrap .i64 0) []
  weakValueDeleteDead ops dict dead

/--
Julia source: base/weakdict.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cleanup_locked(h::WeakValueIdDict) = h.dirty ? _sweep_locked(h) : h
```
-/
def weakValueCleanupLocked {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) : M (WeakValueIdDict K V O) := do
  if ← ops.dirty dict.object then weakValueSweepLocked ops dict else pure dict

/--
Julia source: base/weakdict.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(d::WeakValueIdDict, ::Type{K}, ::Type{V}) where {K, V} = WeakValueIdDict{K, V}()
```
-/
def weakValueEmpty {K V O : Type}
    (constructTyped : M (WeakValueIdDict K V O))
    (_keyType _valueType : Unit) : M (WeakValueIdDict K V O) :=
  constructTyped

/--
Julia source: base/weakdict.jl:294-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:WeakValueIdDict}) = SizeUnknown()
```
-/
def weakValueIteratorSize : JuliaLean.base.iterators.IteratorSizeTag := .sizeUnknown

/--
Julia source: base/weakdict.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islocked(h::WeakValueIdDict) = islocked(h.lock)
```
-/
def weakValueIslocked {K V O L : Type} (getLock : O → L) (isLocked : L → Bool)
    (dict : WeakValueIdDict K V O) : Bool :=
  isLocked (getLock dict.object)

/--
Julia source: base/weakdict.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(h::WeakValueIdDict) = lock(h.lock)
```
-/
def weakValueLock {K V O L : Type} (getLock : O → L) (lock : L → M Unit)
    (dict : WeakValueIdDict K V O) : M Unit :=
  lock (getLock dict.object)

/--
Julia source: base/weakdict.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(h::WeakValueIdDict) = unlock(h.lock)
```
-/
def weakValueUnlock {K V O L : Type} (getLock : O → L) (unlock : L → M Unit)
    (dict : WeakValueIdDict K V O) : M Unit :=
  unlock (getLock dict.object)

/--
Julia source: base/weakdict.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(f, h::WeakValueIdDict) = lock(f, h.lock)
```
-/
def weakValueLockFunction {K V O L F R : Type}
    (getLock : O → L) (lock : F → L → M R) (f : F)
    (dict : WeakValueIdDict K V O) : M R :=
  lock f (getLock dict.object)

/--
Julia source: base/weakdict.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trylock(f, h::WeakValueIdDict) = trylock(f, h.lock)
```
-/
def weakValueTrylockFunction {K V O L F R : Type}
    (getLock : O → L) (trylock : F → L → M R) (f : F)
    (dict : WeakValueIdDict K V O) : M R :=
  trylock f (getLock dict.object)

/--
Julia source: base/weakdict.jl:302-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(h::WeakValueIdDict{K,V}, v, key) where {K,V}
    !isa(key, K) && throw(ArgumentError("$(limitrepr(key)) is not a valid key for type $K"))
    # 'nothing' is not valid on either side: 'finalizer' would reject it as a
    # value (and it is the dead-reference sentinel), and a 'nothing' key is
    # reserved so that lookup errors stay consistent with WeakKeyDict
    key === nothing && throw(ArgumentError("`nothing` is not a valid WeakValueIdDict key"))
    v === nothing && throw(ArgumentError("`nothing` is not a valid WeakValueIdDict value"))
    lock(h) do
        _cleanup_locked(h)
        finalizer(h.finalizer, v)
        h.ht[key] = WeakRef(v)
    end
    return h
end
```
-/
def weakValueSetindex {K V O L Q B : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (value : B) (key : Q) : M (WeakValueIdDict K V O) := do
  if !ops.isKey key then
    fail (.julia (.argumentError (ops.limitrepr key ++ " is not a valid key for type " ++ ops.keyTypeName)))
  if ops.isNothing key then
    fail (.julia (.argumentError "`nothing` is not a valid WeakValueIdDict key"))
  if ops.isNothing value then
    fail (.julia (.argumentError "`nothing` is not a valid WeakValueIdDict value"))
  ops.withLock dict.object fun _ => do
    let _ ← weakValueCleanupLocked ops dict
    let _ ← ops.callFinalizer (ops.finalizer dict.object) (ops.valueToAny value)
    let weak ← ops.newWeakRef (ops.valueToAny value)
    let _ ← JuliaLean.base.iddict.setindex! ops.inner (ops.table dict.object) weak (ops.keyToAny key)
    pure dict

/--
Julia source: base/weakdict.jl:318-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getvalue(h::WeakValueIdDict, key)
    wr = get(h.ht, key, nothing)
    wr === nothing && return nothing
    return (wr::WeakRef).value
end
```
-/
def weakValueGetValue {K V O L Q : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) : M (Option Word) := do
  let raw ← JuliaLean.base.iddict.get ops.inner (ops.table dict.object) (ops.keyToAny key) ops.nothing
  if ← JuliaLean.src.builtins_identity_c.jl_egal_ raw ops.nothing then pure none
  else
    let weak ← JuliaLean.base.iddict.assertType ops.inner raw ops.weakRefType
    ops.weakPayload weak

/--
Julia source: base/weakdict.jl:324-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(h::WeakValueIdDict{K,V}, key, default) where {K,V}
    key === nothing && throw(KeyError(nothing))
    lock(h) do
        v = _getvalue(h, key)
        return v === nothing ? default : v::V
    end
end
```
-/
def weakValueGetDefault {K V O L Q D : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) (default : D) : M (V ⊕ D) := do
  if ops.isNothing key then fail (.keyError (ops.keyToAny key))
  ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | none => pure (.inr default)
    | some value => .inl <$> ops.castPayload value

/--
Julia source: base/weakdict.jl:331-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, h::WeakValueIdDict{K,V}, key) where {K,V}
    key === nothing && throw(KeyError(nothing))
    lock(h) do
        v = _getvalue(h, key)
        return v === nothing ? default() : v::V
    end
end
```
-/
def weakValueGetCallable {K V O L Q D : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) (default : Unit → M D) : M (V ⊕ D) := do
  if ops.isNothing key then fail (.keyError (ops.keyToAny key))
  ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | none => .inr <$> default ()
    | some value => .inl <$> ops.castPayload value

/--
Julia source: base/weakdict.jl:338-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(h::WeakValueIdDict{K,V}, key, default) where {K,V}
    lock(h) do
        v = _getvalue(h, key)
        v === nothing || return v::V
        h[key] = default
        return default::V
    end
end
```
-/
def weakValueGetBang {K V O L Q D : Type}
    (ops : WeakValueIdDictOps K V O L)
    (setIndex : WeakValueIdDict K V O → D → Q → M (WeakValueIdDict K V O))
    (dict : WeakValueIdDict K V O) (key : Q) (default : D) : M V :=
  ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | some value => ops.castPayload value
    | none =>
      let _ ← setIndex dict default key
      ops.castPayload (ops.valueToAny default)

/--
Julia source: base/weakdict.jl:346-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, h::WeakValueIdDict{K,V}, key) where {K,V}
    lock(h) do
        v = _getvalue(h, key)
        v === nothing || return v::V
        v = default()
        h[key] = v
        return v::V
    end
end
```
-/
def weakValueGetBangCallable {K V O L Q D : Type}
    (ops : WeakValueIdDictOps K V O L)
    (setIndex : WeakValueIdDict K V O → D → Q → M (WeakValueIdDict K V O))
    (dict : WeakValueIdDict K V O) (key : Q) (default : Unit → M D) : M V :=
  ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | some value => ops.castPayload value
    | none =>
      let value ← default ()
      let _ ← setIndex dict value key
      ops.castPayload (ops.valueToAny value)

/--
Julia source: base/weakdict.jl:356-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getkey(h::WeakValueIdDict{K}, kk, default) where {K}
    kk === nothing && return default
    lock(h) do
        v = _getvalue(h, kk)
        return v === nothing ? default : kk::K
    end
end
```
-/
def weakValueGetkey {K V O L Q D : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) (default : D) : M (K ⊕ D) := do
  if ops.isNothing key then pure (.inr default)
  else ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | none => pure (.inr default)
    | some _ => .inl <$> ops.castKey (ops.keyToAny key)

/--
Julia source: base/weakdict.jl:364-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(h::WeakValueIdDict{K,V}, key) where {K,V}
    key === nothing && throw(KeyError(key))
    lock(h) do
        v = _getvalue(h, key)
        v === nothing && throw(KeyError(key))
        return v::V
    end
end
```
-/
def weakValueGetindex {K V O L Q : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) : M V := do
  if ops.isNothing key then fail (.keyError (ops.keyToAny key))
  ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | none => fail (.keyError (ops.keyToAny key))
    | some value => ops.castPayload value

/--
Julia source: base/weakdict.jl:373-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function haskey(h::WeakValueIdDict, key)
    key === nothing && return false
    lock(h) do
        return _getvalue(h, key) !== nothing
    end
end
```
-/
def weakValueHaskey {K V O L Q : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) : M Bool :=
  if ops.isNothing key then pure false
  else ops.withLock dict.object fun _ => do
    return (← weakValueGetValue ops dict key).isSome

/--
Julia source: base/weakdict.jl:380-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete!(h::WeakValueIdDict, key)
    key === nothing && return h
    lock(h) do
        delete!(h.ht, key)
    end
    return h
end
```
-/
def weakValueDelete {K V O L Q : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) : M (WeakValueIdDict K V O) :=
  if ops.isNothing key then pure dict
  else ops.withLock dict.object fun _ => do
    let _ ← JuliaLean.base.iddict.deleteBang ops.inner (ops.table dict.object) (ops.keyToAny key)
    pure dict

/--
Julia source: base/weakdict.jl:388-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(h::WeakValueIdDict{K,V}, key) where {K,V}
    key === nothing && throw(KeyError(key))
    lock(h) do
        v = _getvalue(h, key)
        v === nothing && throw(KeyError(key))
        delete!(h.ht, key)
        return v::V
    end
```
-/
def weakValuePop {K V O L Q : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) : M V := do
  if ops.isNothing key then fail (.keyError (ops.keyToAny key))
  ops.withLock dict.object fun _ => do
    match ← weakValueGetValue ops dict key with
    | none => fail (.keyError (ops.keyToAny key))
    | some value =>
      let _ ← JuliaLean.base.iddict.deleteBang ops.inner (ops.table dict.object) (ops.keyToAny key)
      ops.castPayload value

/--
Julia source: base/weakdict.jl:397-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(h::WeakValueIdDict{K,V}, key, default) where {K,V}
    key === nothing && return default
    lock(h) do
        v = _getvalue(h, key)
        delete!(h.ht, key)
        return v === nothing ? default : v::V
    end
end
```
-/
def weakValuePopDefault {K V O L Q D : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) (key : Q) (default : D) : M (V ⊕ D) :=
  if ops.isNothing key then pure (.inr default)
  else ops.withLock dict.object fun _ => do
    let value ← weakValueGetValue ops dict key
    let _ ← JuliaLean.base.iddict.deleteBang ops.inner (ops.table dict.object) (ops.keyToAny key)
    match value with
    | none => pure (.inr default)
    | some value => .inl <$> ops.castPayload value

/--
Julia source: base/weakdict.jl:406-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(h::WeakValueIdDict)
    lock(h) do
        empty!(h.ht)
        h.dirty = false
    end
    return h
end
```
-/
def weakValueEmptyBang {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) : M (WeakValueIdDict K V O) :=
  ops.withLock dict.object fun _ => do
    let _ ← JuliaLean.base.iddict.emptyBang ops.inner (ops.table dict.object)
    ops.setDirty dict.object false
    pure dict

/--
Julia source: base/weakdict.jl:414-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(h::WeakValueIdDict)
    lock(h) do
        n = 0
        for (k, wr) in h.ht
            n += ((wr::WeakRef).value !== nothing)
        end
        return n
    end
end
```
-/
def weakValueLength {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O) : M I64 :=
  ops.withLock dict.object fun _ => weakValueLiveCount ops (ops.table dict.object)

/--
Julia source: base/weakdict.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(h::WeakValueIdDict) = length(h) == 0
```
-/
def weakValueIsempty {K V O : Type}
    (length : WeakValueIdDict K V O → M I64)
    (dict : WeakValueIdDict K V O) : M Bool := do
  return (← length dict).val == 0

/--
Julia source: base/weakdict.jl:425-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(h::WeakValueIdDict{K,V}, snapshot::Union{Nothing,Tuple{Vector{Pair{K,V}},Int}}=nothing) where {K,V}
    # iterate over a snapshot of the live entries, so that concurrent
    # collection of values (or mutation under the lock) cannot corrupt the
    # walk; the snapshot's strong references keep its entries alive
    if snapshot === nothing
        live = Pair{K,V}[]
        lock(h) do
            for (k, wr) in h.ht
                v = (wr::WeakRef).value
                v === nothing && continue
                push!(live, Pair{K,V}(k, v::V))
            end
        end
        snapshot = (live, 0)
    end
    pairs, i = snapshot
    i += 1
    i > length(pairs) && return nothing
    return pairs[i], (pairs, i)
end
```
-/
def weakValueIterate {K V O L : Type}
    (ops : WeakValueIdDictOps K V O L)
    (dict : WeakValueIdDict K V O)
    (snapshot : Option (List (K × V) × I64) := none) :
    M (Option ((K × V) × (List (K × V) × I64))) := do
  let (pairs, index) ← match snapshot with
    | some snapshot => pure snapshot
    | none => do
      let pairs ← ops.withLock dict.object fun _ => weakValueLiveSnapshot ops (ops.table dict.object)
      pure (pairs, JInt.wrap .i64 0)
  let nextIndex := JuliaLean.base.int.add_int index (JInt.wrap .i64 1)
  let length := JInt.wrap .i64 pairs.length
  if nextIndex.val > length.val then pure none
  else if nextIndex.val <= 0 then fail (.array .bounds)
  else
    match pairs.drop (nextIndex.val.toNat - 1) with
    | [] => fail (.array .bounds)
    | pair :: _ => pure (some (pair, (pairs, nextIndex)))

end JuliaLean.base.weakdict
/-!
# `WeakKeyDict` and `WeakValueIdDict`, base/weakdict.jl (master `bbfa0ce4150`)

`WeakKeyDict{K,V}` wraps `ht::Dict{WeakRef,V}`. A `Dict` key `WeakRef` hashes
and compares through its referent (`hash(w::WeakRef, h) = hash(w.value, h)`,
`isequal(w::WeakRef, v) = isequal(w.value, v)`, base/hashing.jl and
base/gcutils.jl), so the inner table is an `isequal`-keyed map from referents;
a collected referent is `nothing` and matches no key. The model keeps, per
entry, the referent (`none` once collected) and the value.

Garbage collection is an explicit event `gc dead`: every referent in `dead`
becomes `nothing`, and every object in `dead` with a pending finalizer runs
it (`WeakKeyDictFinalizer` sets `dirty`, base/weakdict.jl:8). The values
(`V` is `Any` in this model) are held strongly, so a realistic `dead` list
holds no stored value.

`WeakValueIdDict{K,V}` (master only) wraps `ht::IdDict{K,WeakRef}`. Its
properties here are about type checks, so its values are all alive and the
inner `IdDict{K,WeakRef}` is the eqtable map of `JuliaLean.IdDicts.IdDict`
holding the referents.
-/

namespace JuliaLean.IdDicts

/-! ## `WeakKeyDict{K,Any}` -/

structure WKD where
  K : JTy
  /-- inner `Dict{WeakRef,V}`: (referent or collected, value), insertion order -/
  ht : List (Option JVal × JVal)
  /-- objects on which `finalizer(wkh.finalizer, key)` is pending -/
  fins : List JVal
  dirty : Bool

def WKD.new (K : JTy) : WKD := ⟨K, [], [], false⟩

/-- `_cleanup_locked(h)`, base/weakdict.jl:65-77. -/
def WKD.cleanup (w : WKD) : WKD :=
  if w.dirty then { w with dirty := false, ht := w.ht.filter fun e => e.1.isSome } else w

/-- Inner-`Dict` key match of a lookup key against a stored `WeakRef`. -/
def wrMatch (key : JVal) (e : Option JVal × JVal) : Bool :=
  match e.1 with
  | some y => isequal y key
  | none => false

/-- `setindex!(wkh, v, key)`, base/weakdict.jl:90-107. -/
def WKD.setindex (w : WKD) (v key : JVal) : Out WKD Unit :=
  if !isa key w.K then (w, .error .argumentError)
  else if key == .nothing then (w, .error .argumentError)
  else
    let w := w.cleanup
    -- `k = getkey(wkh.ht, key, nothing)`
    if w.ht.any (wrMatch key) then
      -- `k.value = key; wkh.ht[k] = v`
      ({ w with ht := w.ht.map fun e => if wrMatch key e then (some key, v) else e }, .ok ())
    else if !finalizable key then (w, .error .errorException)
    else
      -- `finalizer(wkh.finalizer, key); k = WeakRef(key); wkh.ht[k] = v`
      ({ w with fins := key :: w.fins, ht := w.ht ++ [(some key, v)] }, .ok ())

/-- `delete!(wkh, key)`, base/weakdict.jl:164-170. -/
def WKD.delete (w : WKD) (key : JVal) : WKD :=
  if key == .nothing then w else
  match w.ht.findIdx? (wrMatch key) with
  | some i => { w with ht := w.ht.eraseIdx i }
  | none => w

/-- `haskey(wkh, key)`, base/weakdict.jl:177-182. -/
def WKD.haskey (w : WKD) (key : JVal) : Bool := key != .nothing && w.ht.any (wrMatch key)

/-- `length(t)`, base/weakdict.jl:190-195: sweeps when dirty. -/
def WKD.length (w : WKD) : Out WKD Nat := let w := w.cleanup; (w, .ok w.ht.length)

/-- `iterate(t)` to exhaustion, base/weakdict.jl:197-210: entries whose key
was collected are skipped. -/
def WKD.iterate (w : WKD) : List (JVal × JVal) :=
  w.ht.filterMap fun e => e.1.map fun k => (k, e.2)

/-- A garbage collection that frees the objects `dead`. -/
def WKD.gc (w : WKD) (dead : List JVal) : WKD :=
  let ran := w.fins.any (· ∈ dead)
  { w with
    ht := w.ht.map fun e => (e.1.bind fun k => if k ∈ dead then none else some k, e.2)
    fins := w.fins.filter (· ∉ dead)
    dirty := w.dirty || ran }
/-! ## `WeakValueIdDict{K,V}` -/

structure WVID where
  K : JTy
  V : JTy
  /-- inner `IdDict{K,WeakRef}`: keys and live referents -/
  ht : Tab
  dirty : Bool

def WVID.new (K V : JTy) : WVID := ⟨K, V, [], false⟩

/-- `setindex!(h, v, key)`, base/weakdict.jl:302-315 (with all values alive,
`_cleanup_locked` sweeps nothing). -/
def WVID.setindex (h : WVID) (v key : JVal) : Out WVID Unit :=
  if !isa key h.K then (h, .error .argumentError)
  else if key == .nothing then (h, .error .argumentError)
  else if v == .nothing then (h, .error .argumentError)
  else if !finalizable v then (h, .error .errorException)
  else ({ h with ht := (eqtablePut h.ht key v).1 }, .ok ())

/-- `_getvalue(h, key)`, base/weakdict.jl:318-322: `get(h.ht, key, nothing)`
then `.value`; `nothing` is never a stored referent. -/
def WVID.getvalue (h : WVID) (key : JVal) : JVal := eqtableGet h.ht key .nothing

/-- `getindex(h, key)`, base/weakdict.jl:364-371. -/
def WVID.getindex (h : WVID) (key : JVal) : Except IErr JVal :=
  if key == .nothing then .error .keyError else
  let v := h.getvalue key
  if v == .nothing then .error .keyError else cast v h.V

/-- `get(h, key, default)`, base/weakdict.jl:324-330. -/
def WVID.get (h : WVID) (key default : JVal) : Except IErr JVal :=
  if key == .nothing then .error .keyError else
  let v := h.getvalue key
  if v == .nothing then .ok default else cast v h.V

/-- `get!(h, key, default)`, base/weakdict.jl:338-345. -/
def WVID.getBang (h : WVID) (key default : JVal) : Out WVID JVal :=
  let v := h.getvalue key
  if v != .nothing then (h, cast v h.V) else
  let r := h.setindex default key
  match r.2 with
  | .error e => (r.1, .error e)
  | .ok () => (r.1, cast default h.V)

end JuliaLean.IdDicts

namespace JuliaLean.DictsCov.WeakDictRows


abbrev R (α : Type) := Except String α

structure WK (K V : Type) where
  entries : List (Option K × V)
  dirty : Bool
  deriving Repr

def wkEmpty : WK K V := ⟨[], false⟩

def method8 (d : WK K V) (_key : K) : WK K V := { d with dirty := true }

def method31 : WK K V := wkEmpty

def wkFold (setindex : WK K V → K → V → R (WK K V)) :
    WK K V → List (K × V) → R (WK K V)
  | dict, [] => .ok dict
  | dict, (key, value) :: rest => do
      let dict ← setindex dict key value
      wkFold setindex dict rest

def method37 (setindex : WK K V → K → V → R (WK K V))
    (pairs : List (K × V)) : R (WK K V) := wkFold setindex method31 pairs

def method44 (setindex : WK K V → K → V → R (WK K V)) (pair : K × V) :=
  setindex method31 pair.1 pair.2

def method45 (sizehint : WK K V → Nat → WK K V)
    (setindex : WK K V → K → V → R (WK K V)) (pairs : List (K × V)) :=
  wkFold setindex (sizehint method31 pairs.length) pairs

def method53 : WK K V := method31

def method55 (_emptyTuple : Unit) : WK K V := method53

def method56 (construct : WK K V → R (WK K V)) (d : WK K V) := construct d

def method58 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs

def method59 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs

def method60 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs

def method61 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs

def method63 (eltype : I → T) (dictWithEltype : I → T → R (WK K V)) (kv : I) :=
  dictWithEltype kv (eltype kv)

def method65 (h : WK K V) : WK K V :=
  if h.dirty then ⟨h.entries.filter (fun pair => pair.1.isSome), false⟩ else h

def method79 (sizehint : WK K V → Nat → Bool → WK K V)
    (d : WK K V) (newsz : Nat) (shrink : Bool) := sizehint d newsz shrink

def method80 : WK K V := method31

inductive IteratorSizeTag where | sizeUnknown deriving Repr, DecidableEq

def method82 : IteratorSizeTag := .sizeUnknown

def method84 (islocked : L → Bool) (lock : L) := islocked lock

def method85 (lockFn : L → A) (lock : L) := lockFn lock

def method86 (unlock : L → A) (lock : L) := unlock lock

def method87 (lockFn : (Unit → A) → L → A) (f : Unit → A) (lock : L) := lockFn f lock

def method88 (trylock : (Unit → A) → L → A) (f : Unit → A) (lock : L) := trylock f lock

structure WeakSlot (K : Type) where
  value : Option K
  registered : Bool
  deriving Repr

def method90 (isK : Q → Bool) (isNothing : Q → Bool)
    (cleanup : W → R W) (getkey : W → Q → Option (WeakSlot Q))
    (register : W → Q → W) (setWeakValue : WeakSlot Q → Q → WeakSlot Q)
    (newWeak : Q → WeakSlot Q) (setindex : W → WeakSlot Q → V → R W)
    (wkh : W) (value : V) (key : Q) : R W :=
  if !isK key then .error "invalid WeakKeyDict key type"
  else if isNothing key then .error "nothing is not a valid WeakKeyDict key"
  else do
    let wkh ← cleanup wkh
    match getkey wkh key with
    | none => setindex (register wkh key) (newWeak key) value
    | some weak => setindex wkh (setWeakValue weak key) value

def method108 (lookup : W → Q → Option V) (setindex : W → Q → V → R (V × W))
    (wkh : W) (key : Q) (default : V) : R (V × W) :=
  match lookup wkh key with | some value => .ok (value, wkh) | none => setindex wkh key default

def method118 (lookup : W → Q → Option V) (default : Unit → R V)
    (setindex : W → Q → V → R (V × W)) (wkh : W) (key : Q) : R (V × W) :=
  match lookup wkh key with
  | some value => .ok (value, wkh)
  | none => do let value ← default (); setindex wkh key value

def method129 (getWeak : W → Q → Option (WeakSlot K))
    (wkh : W) (key : Q) (default : K) : K :=
  match getWeak wkh key with | none => default | some weak => weak.value.getD default

def method138 (mapValues : (V → V) → W → W) (f : V → V) (dict : W) : W := mapValues f dict

def method140 (isNothing : Q → Bool) (get : W → Q → V → V)
    (wkh : W) (key : Q) (default : V) : R V :=
  if isNothing key then .error "KeyError" else .ok (get wkh key default)

def method146 (isNothing : Q → Bool) (get : (Unit → R V) → W → Q → R V)
    (default : Unit → R V) (wkh : W) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else get default wkh key

def method152 (isNothing : Q → Bool) (pop : W → Q → R (V × W))
    (wkh : W) (key : Q) : R (V × W) :=
  if isNothing key then .error "KeyError" else pop wkh key

def method158 (isNothing : Q → Bool) (pop : W → Q → V → V × W)
    (wkh : W) (key : Q) (default : V) : V × W :=
  if isNothing key then (default, wkh) else pop wkh key default

def method164 (isNothing : Q → Bool) (delete : W → Q → W) (wkh : W) (key : Q) : W :=
  if isNothing key then wkh else delete wkh key

def method171 (empty : W → W) (wkh : W) : W := empty wkh

def method177 (isNothing : Q → Bool) (haskey : W → Q → Bool) (wkh : W) (key : Q) : Bool :=
  if isNothing key then false else haskey wkh key

def method183 (isNothing : Q → Bool) (getindex : W → Q → R V) (wkh : W) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else getindex wkh key

def method189 (length : W → Nat) (wkh : W) : Bool := length wkh == 0

def wkIter : Nat → List (Option K × V) → Nat → Option ((K × V) × Nat)
  | 0, _, _ => none
  | fuel + 1, entries, index =>
      match entries[index]? with
      | none => none
      | some (none, _) => wkIter fuel entries (index + 1)
      | some (some key, value) => some ((key, value), index + 1)

def method197 (fuel : Nat) (entries : List (Option K × V)) (state : Nat) :=
  wkIter fuel entries state

def method212 (only : W → (W → Option P) → R P) (first : W → Option P) (dict : W) :=
  only dict first

def method214 (filterOnePass : (P → Bool) → W → W) (f : P → Bool) (dict : W) :=
  filterOnePass f dict

structure WV (K V : Type) where
  entries : List (K × Option V)
  dirty : Bool
  deriving Repr

def wvEmpty : WV K V := ⟨[], false⟩

def method222 (d : WV K V) (_value : V) : WV K V := { d with dirty := true }

def method244 : WV K V := wvEmpty

def wvFold (setindex : WV K V → K → V → R (WV K V)) :
    WV K V → List (K × V) → R (WV K V)
  | dict, [] => .ok dict
  | dict, (key, value) :: rest => do
      let dict ← setindex dict key value
      wvFold setindex dict rest

def method250 (setindex : WV K V → K → V → R (WV K V)) (pairs : List (K × V)) :=
  wvFold setindex method244 pairs

def method257 (setindex : WV K V → K → V → R (WV K V)) (pair : K × V) :=
  setindex method244 pair.1 pair.2

def method258 (setindex : WV K V → K → V → R (WV K V)) (pairs : List (K × V)) :=
  wvFold setindex method244 pairs

def method265 : WV K V := method244

def method267 (_emptyTuple : Unit) : WV K V := method265

def method268 (construct : WV K V → R (WV K V)) (d : WV K V) := construct d

def method270 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs

def method271 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs

def method272 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs

def method273 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs

def method275 (eltype : I → T) (dictWithEltype : I → T → R (WV K V)) (kv : I) :=
  dictWithEltype kv (eltype kv)

def method279 (h : WV K V) : WV K V :=
  ⟨h.entries.filter (fun pair => pair.2.isSome), false⟩

def method290 (sweep : WV K V → WV K V) (h : WV K V) : WV K V :=
  if h.dirty then sweep h else h

def method292 : WV K V := method244

def method294 : IteratorSizeTag := .sizeUnknown

def method296 (islocked : L → Bool) (lock : L) := islocked lock

def method297 (lockFn : L → A) (lock : L) := lockFn lock

def method298 (unlock : L → A) (lock : L) := unlock lock

def method299 (lockFn : (Unit → A) → L → A) (f : Unit → A) (lock : L) := lockFn f lock

def method300 (trylock : (Unit → A) → L → A) (f : Unit → A) (lock : L) := trylock f lock

def method302 (isK : Q → Bool) (isNothingKey : Q → Bool) (isNothingValue : W → Bool)
    (cleanup : D → D) (register : D → W → D) (setWeak : D → Q → W → R D)
    (dict : D) (value : W) (key : Q) : R D :=
  if !isK key then .error "invalid WeakValueIdDict key type"
  else if isNothingKey key then .error "nothing is not a valid WeakValueIdDict key"
  else if isNothingValue value then .error "nothing is not a valid WeakValueIdDict value"
  else setWeak (register (cleanup dict) value) key value

def method318 (getWeak : D → Q → Option (Option V)) (dict : D) (key : Q) : Option V :=
  match getWeak dict key with | none => none | some weakValue => weakValue

def method324 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (dict : D) (key : Q) (default : V) : R V :=
  if isNothing key then .error "KeyError" else .ok ((getValue dict key).getD default)

def method331 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (default : Unit → R V) (dict : D) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else
    match getValue dict key with | none => default () | some value => .ok value

def method338 (getValue : D → Q → Option V) (setindex : D → Q → W → R D)
    (cast : W → R V) (dict : D) (key : Q) (default : W) : R (V × D) :=
  match getValue dict key with
  | some value => .ok (value, dict)
  | none => do
      let dict ← setindex dict key default
      let value ← cast default
      return (value, dict)

def method346 (getValue : D → Q → Option V) (default : Unit → R W)
    (setindex : D → Q → W → R D) (cast : W → R V)
    (dict : D) (key : Q) : R (V × D) :=
  match getValue dict key with
  | some value => .ok (value, dict)
  | none => do
      let raw ← default ()
      let dict ← setindex dict key raw
      let value ← cast raw
      return (value, dict)

def method356 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (castKey : Q → R K) (dict : D) (key : Q) (default : K) : R K :=
  if isNothing key then .ok default
  else match getValue dict key with
    | none => .ok default
    | some _ => castKey key

def method364 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (dict : D) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else
    match getValue dict key with | none => .error "KeyError" | some value => .ok value

def method373 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (dict : D) (key : Q) : Bool :=
  if isNothing key then false else (getValue dict key).isSome

def method380 (isNothing : Q → Bool) (delete : D → Q → D) (dict : D) (key : Q) : D :=
  if isNothing key then dict else delete dict key

def method388 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (delete : D → Q → D) (dict : D) (key : Q) : R (V × D) :=
  if isNothing key then .error "KeyError" else
    match getValue dict key with
    | none => .error "KeyError"
    | some value => .ok (value, delete dict key)

def method397 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (delete : D → Q → D) (dict : D) (key : Q) (default : V) : V × D :=
  if isNothing key then (default, dict)
  else ((getValue dict key).getD default, delete dict key)

def method406 (empty : D → D) (clearDirty : D → D) (dict : D) : D :=
  clearDirty (empty dict)

def countLive : List (K × Option V) → Nat
  | [] => 0
  | (_, value) :: rest => (if value.isSome then 1 else 0) + countLive rest

def method414 (entries : List (K × Option V)) : Nat := countLive entries

def method423 (length : D → Nat) (dict : D) : Bool := length dict == 0

def livePairs : List (K × Option V) → List (K × V)
  | [] => []
  | (key, none) :: rest => livePairs rest
  | (key, some value) :: rest => (key, value) :: livePairs rest

def method425 (entries : List (K × Option V))
    (snapshot : Option (List (K × V) × Nat)) : Option ((K × V) × (List (K × V) × Nat)) :=
  let (pairs, index) := snapshot.getD (livePairs entries, 0)
  let index := index + 1
  match pairs[index - 1]? with
  | none => none
  | some pair => some (pair, (pairs, index))

end JuliaLean.DictsCov.WeakDictRows
