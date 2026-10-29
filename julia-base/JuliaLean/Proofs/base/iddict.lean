import JuliaLean.base.iddict
import JuliaLean.Registry.Types

/-!
# Properties of `base/iddict.jl`

The specifications below use identity-keyed reference maps. `RuntimeOps` keeps
allocation, memory, conversion, exception, and C table behavior explicit.
-/

namespace JuliaLean.Proofs.base.iddict

open JuliaLean JuliaLean.base.iddict JuliaLean.Registry

/-- Key uniqueness under the dictionary's `===` relation. -/
def keysDistinctAny {A : Type} (sameIdentity : A → A → Bool) :
    List (A × A) → Prop
  | [] => True
  | (key, _) :: rest =>
      (∀ pair ∈ rest, sameIdentity key pair.1 = false) ∧ keysDistinctAny sameIdentity rest

/-- Key uniqueness for the typed pairs returned by `iterate`. -/
def keysDistinct {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) : List (K × V) → Prop
  | [] => True
  | (key, _) :: rest =>
      (∀ pair ∈ rest, ops.sameIdentity (ops.keyToAny key) (ops.keyToAny pair.1) = false) ∧
        keysDistinct ops rest

/-- Lookup in the pairs that the typed `iterate` method yields. -/
def typedLookup {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) : List (K × V) → A → Option A
  | [], _ => none
  | (key, value) :: rest, query =>
      if ops.sameIdentity query (ops.keyToAny key) then some (ops.valueToAny value)
      else typedLookup ops rest query

/-- Extensional equality to a unique identity-keyed map, including its count. -/
def matchesReference {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (d : IdDict K V A HT)
    (expected : List (A × A)) : Prop :=
  d.count.val.toNat = expected.length ∧
  keysDistinctAny ops.sameIdentity (ops.tablePairs d.ht) ∧
  ∀ key, referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key =
    referenceLookup ops.sameIdentity expected key

/-- Sets, deletion, pops, rehash hints and emptying agree with `===` dictionary semantics. -/
def IdDictOpsAgree : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (initial : IdDict K V A HT)
    (calls : List (Operation A)),
    let actual := runOperations ops calls initial
    let expected := runReference ops calls (ops.tablePairs initial.ht)
    (∀ key default,
      get ops actual key default = .ok ((referenceLookup ops.sameIdentity expected key).getD default)) ∧
    matchesReference ops actual expected ∧
    ∃ pairs, iterateAll ops actual = .ok pairs ∧
      pairs.length = actual.count.val.toNat ∧ keysDistinct ops pairs ∧
      ∀ key, typedLookup ops pairs key = referenceLookup ops.sameIdentity expected key

/-- Iteration yields every live pair once, and its count equals `length`, including after get! and pop!. -/
def IdDictLengthLive : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (initial : IdDict K V A HT)
    (calls : List (Operation A)),
    let d := runOperations ops calls initial
    ∃ pairs, iterateAll ops d = .ok pairs ∧
      (length d).val = pairs.length ∧ keysDistinct ops pairs

/-- An absent get! inserts the converted value and increases the live count once. -/
def IdDictGetBangAbsent : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key default : A) (value : V),
    referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = none →
    ops.isKey key = true →
    (Except.bind (if ops.isValue default then Except.ok default else ops.convertValue default)
      ops.castValue) = .ok value →
    let result := getBang ops d key default
    result.result = .ok (ops.valueToAny value) ∧
    referenceLookup ops.sameIdentity (ops.tablePairs result.state.ht) key =
      some (ops.valueToAny value) ∧
    result.state.count.val = d.count.val + 1

/-- Haskey's KeySet test and indexing should find every key yielded by iteration. -/
def LookupFindsPresent : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key value : A),
    referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = some value →
    inKeySet ops ⟨d⟩ key = .ok true ∧ getindex ops d key = .ok value

/-- Indexing a missing identity key throws KeyError with that key. -/
def MissingGetindexKeyError : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT) (key : A),
    referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = none →
    getindex ops d key = .error (ops.keyError key)

/-- pop! returns the stored value for every present identity key. -/
def PopReturnsPresent : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key value : A),
    referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = some value →
    (pop ops d key).result = .ok value

/-- get! returns a present value without changing the dictionary or calling its default. -/
def GetBangKeepsPresent : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key value default : A) (fallback : Unit → Except E A),
    referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = some value →
    let ordinary := getBang ops d key default
    let callable := getBangCallable ops d fallback key
    ordinary.result = .ok value ∧
    ops.tablePairs ordinary.state.ht = ops.tablePairs d.ht ∧
    callable.result = .ok value ∧
    ops.tablePairs callable.state.ht = ops.tablePairs d.ht

/-- Empty constructors allocate 32 words and initialize both counters to zero. -/
def EmptyConstructors : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops)
    (anyOps : RuntimeOps A A A HT E Ptr Preserve)
    (_hAnyOps : RuntimeOps.Lawful anyOps)
    (d : IdDict K V A HT),
    (∀ empty, emptyTyped ops = .ok empty →
      ops.memoryLength empty.ht = JInt.wrap .i64 32 ∧
      empty.count.val = 0 ∧ empty.ndel.val = 0) ∧
    (∀ empty, emptyAny anyOps = .ok empty →
      anyOps.memoryLength empty.ht = JInt.wrap .i64 32 ∧
      empty.count.val = 0 ∧ empty.ndel.val = 0) ∧
    (∀ empty, emptyTuple anyOps () = .ok empty →
      anyOps.memoryLength empty.ht = JInt.wrap .i64 32 ∧
      empty.count.val = 0 ∧ empty.ndel.val = 0) ∧
    (∀ empty, emptyOf ops d = .ok empty →
      ops.memoryLength empty.ht = JInt.wrap .i64 32 ∧
      empty.count.val = 0 ∧ empty.ndel.val = 0)

/-- empty! replaces the old table with a cleared 32-word table and resets both counts. -/
def EmptyBangContents : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT),
    let result := emptyBang ops d
    result.result = .ok result.state ∧
    ops.sameMemory result.state.ht d.ht = false ∧
    ops.memoryLength result.state.ht = JInt.wrap .i64 32 ∧
    ops.tablePairs result.state.ht = [] ∧
    result.state.count.val = 0 ∧ result.state.ndel.val = 0


/-- Successful pair constructors preserve the last value for each `===` key. -/
def PairConstructors : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (_hops : RuntimeOps.Lawful ops)
    (opsK : RuntimeOps K A A HT E Ptr Preserve) (_hopsK : RuntimeOps.Lawful opsK)
    (opsV : RuntimeOps A V A HT E Ptr Preserve) (_hopsV : RuntimeOps.Lawful opsV)
    (opsAny : RuntimeOps A A A HT E Ptr Preserve) (_hopsAny : RuntimeOps.Lawful opsAny)
    (pairs : List (A × A)),
    let expected := runReference ops (pairs.map fun pair => Operation.set pair.1 pair.2) []
    let expectedK := runReference opsK (pairs.map fun pair => Operation.set pair.1 pair.2) []
    let expectedV := runReference opsV (pairs.map fun pair => Operation.set pair.1 pair.2) []
    let expectedAny := runReference opsAny (pairs.map fun pair => Operation.set pair.1 pair.2) []
    (∀ d, fromPairs ops pairs = .ok d → matchesReference ops d expected) ∧
    (∀ d, fromPairsKV ops pairs = .ok d → matchesReference ops d expected) ∧
    (∀ d, fromPairsAny opsAny pairs = .ok d → matchesReference opsAny d expectedAny) ∧
    (∀ d, fromPairsK opsK pairs = .ok d → matchesReference opsK d expectedK) ∧
    (∀ d, fromPairsV opsV pairs = .ok d → matchesReference opsV d expectedV)

/-- Iterator construction inserts every pair in its finite iteration order. -/
def IteratorConstructor : Prop :=
  ∀ {K V A HT E Ptr Preserve I : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve) (_hops : RuntimeOps.Lawful ops)
    (iterator : IteratorOps A I E) (_hiterator : IteratorOps.Lawful iterator) (itr : I),
    ∀ d, fromIterator ops iterator itr = .ok d →
      matchesReference ops d (runReference ops
        ((iterator.elements itr).map fun pair => Operation.set pair.1 pair.2) [])

/-- The generic constructor selects its result key and value types from `eltype(kv)`. -/
def EltypeConstructor : Prop :=
  ∀ {I A HT E Ptr Preserve : Type}
    (family : RuntimeFamily A HT E Ptr Preserve) (iterator : IteratorOps A I E)
    (dictWithEltype : (TypePair → I → Except E (PackedIdDict A HT)) → I → TypePair →
      Except E (PackedIdDict A HT)) (kv : I) (eltype : I → TypePair),
    (∀ (constructor : TypePair → I → Except E (PackedIdDict A HT))
      (itr : I) (types : TypePair) (result : PackedIdDict A HT),
      dictWithEltype constructor itr types = .ok result →
      result.1 = types.key ∧ result.2.1 = types.value) →
    ∀ result, fromEltype family iterator dictWithEltype kv eltype = .ok result →
      result.1 = (eltype kv).key ∧ result.2.1 = (eltype kv).value

/-- Copying duplicates the memory contents and preserves the dictionary counters. -/
def CopyPreservesContents : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT),
    (∀ copied, copyConstruct ops d = .ok copied →
      copied.count = d.count ∧ copied.ndel = d.ndel ∧
      ops.sameMemory copied.ht d.ht = false ∧
      mapsEquivalent ops.sameIdentity (ops.tablePairs copied.ht) (ops.tablePairs d.ht)) ∧
    (∀ copied, copyDict ops d = .ok copied →
      copied.count = d.count ∧ copied.ndel = d.ndel ∧
      ops.sameMemory copied.ht d.ht = false ∧
      mapsEquivalent ops.sameIdentity (ops.tablePairs copied.ht) (ops.tablePairs d.ht))

/-- Rehashing preserves entries and sizehint keeps capacity unless growth reaches 25 percent. -/
def RehashSizehintPreservesContents : Prop :=
  ∀ {K V A HT E Ptr Preserve N : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT) (newSize : N),
    (∀ result wordSize,
      (rehash ops d newSize).result = .ok result →
      ops.toUInt newSize = .ok wordSize →
      result.count = d.count ∧ result.ndel = d.ndel ∧
      mapsEquivalent ops.sameIdentity (ops.tablePairs result.ht) (ops.tablePairs d.ht) ∧
      ops.memoryLength result.ht = JuliaLean.base.int.remT .i64 wordSize) ∧
    (∀ doubled requested wordSize,
      ops.doubleInteger newSize = .ok doubled →
      ops.tablesz doubled = .ok requested →
      ops.toUInt requested = .ok wordSize →
      JuliaLean.base.int.remT .i64 wordSize = requested →
      let threshold := JuliaLean.base.int.ashr_int
        (ops.memoryLength d.ht * JInt.wrap .i64 5) (JInt.wrap .i64 2)
      ∀ result, (sizehint! ops d newSize).result = .ok result →
        result.count = d.count ∧ result.ndel = d.ndel ∧
        mapsEquivalent ops.sameIdentity (ops.tablePairs result.ht) (ops.tablePairs d.ht) ∧
        if requested.val < threshold.val then
          ops.sameMemory result.ht d.ht = true
        else ops.memoryLength result.ht = requested)

/-- setindex! rejects invalid key types, converts values, and stores the result under the key. -/
def SetindexTypeAndValue : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (value key : A) (stored : V),
    keysDistinctAny ops.sameIdentity (ops.tablePairs d.ht) →
    ops.isKey key = true →
    (Except.bind (if ops.isValue value then Except.ok value else ops.convertValue value)
      ops.castValue) = .ok stored →
    let result := setindex! ops d value key
    result.result = .ok result.state ∧
    referenceLookup ops.sameIdentity (ops.tablePairs result.state.ht) key =
      some (ops.valueToAny stored) ∧
    result.state.count.val = d.count.val +
      if (referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key).isSome then 0 else 1


/-- setindex! checks the key type before any insertion or rehashing. -/
def SetindexRejectsInvalidKey : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (value key : A),
    ops.isKey key = false →
    let result := setindex! ops d value key
    result.result = .error (ops.keyTypeError key) ∧
    result.state.count = d.count ∧ result.state.ndel = d.ndel ∧
    mapsEquivalent ops.sameIdentity (ops.tablePairs result.state.ht) (ops.tablePairs d.ht)
/-- Pops and deletion update the live and deleted counts as keys are removed. -/
def PopAndDeleteCounters : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key default : A),
    let before := referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key
    let popped := popDefault ops d key default
    let single := pop ops d key
    (before = none →
      popped.result = .ok default ∧ popped.state.count = d.count ∧
      popped.state.ndel = d.ndel ∧
      single.result = .error (ops.keyError key) ∧
      single.state.count = d.count ∧ single.state.ndel = d.ndel) ∧
    (∀ value, before = some value →
      popped.result = .ok value ∧
      popped.state.count.val = d.count.val - 1 ∧
      popped.state.ndel.val = d.ndel.val + 1 ∧
      mapsEquivalent ops.sameIdentity (ops.tablePairs popped.state.ht)
        (referenceDelete ops.sameIdentity (ops.tablePairs d.ht) key) ∧
      (if ops.sameIdentity value ops.secretToken then
        single.result = .error (ops.keyError key)
      else single.result = .ok value) ∧
      single.state.count.val = d.count.val - 1 ∧
      single.state.ndel.val = d.ndel.val + 1) ∧
    (let deleted := deleteBang ops d key
     deleted.result = .ok deleted.state ∧
       (before = none → deleted.state.count = d.count ∧ deleted.state.ndel = d.ndel) ∧
       (∀ value, before = some value →
         deleted.state.count.val = d.count.val - 1 ∧ deleted.state.ndel.val = d.ndel.val + 1 ∧
         mapsEquivalent ops.sameIdentity (ops.tablePairs deleted.state.ht)
           (referenceDelete ops.sameIdentity (ops.tablePairs d.ht) key)))

/-- Callable get returns a present value without invoking its default, or invokes the default on a miss. -/
def CallableGet : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key value : A) (fallback : Unit → Except E A),
    (referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = some value →
      getCallable ops d fallback key = .ok value) ∧
    (referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = none →
      getCallable ops d fallback key = fallback ())

/-- Callable get! converts and inserts a missing default, and leaves present keys unchanged. -/
def CallableGetBang : Prop :=
  ∀ {K V A HT E Ptr Preserve : Type}
    (ops : RuntimeOps K V A HT E Ptr Preserve)
    (_hops : RuntimeOps.Lawful ops) (d : IdDict K V A HT)
    (key : A) (fallback : Unit → Except E A),
    ops.isKey key = true →
    referenceLookup ops.sameIdentity (ops.tablePairs d.ht) key = none →
    ∀ value : V,
      fallback () = .ok (ops.valueToAny value) →
      let result := getBangCallable ops d fallback key
      result.result = .ok (ops.valueToAny value) ∧
      referenceLookup ops.sameIdentity (ops.tablePairs result.state.ht) key =
        some (ops.valueToAny value) ∧
      result.state.count.val = d.count.val + 1


private def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/iddict.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo, prop := prop }

def entries : List Entry := [
  entry "iddicts-ops-agree"
    ["setindex!(::IdDict,v,k)", "delete!(::IdDict,k)", "pop!(::IdDict,k)",
      "pop!(::IdDict,k,default)", "empty!(::IdDict)", "sizehint!(::IdDict,n)",
      "get(::IdDict,k,default)", "length(::IdDict)", "iterate(::IdDict)"]
    "After any sequence of IdDict mutations, get, length, and iteration agree with a reference map keyed by `===`; key and value types follow `K` and `V`."
    "IdDict docstring base/iddict.jl:6-8; setindex! base/iddict.jl:79-92"
    ``IdDictOpsAgree,
  entry "iddicts-length-live"
    ["length(::IdDict)", "iterate(::IdDict)", "get!(::IdDict,k,default)",
      "get!(f,::IdDict,k)", "pop!(::IdDict,k)"]
    "After any IdDict calls, including get! and pop! on stored sentinels, iteration yields exactly length(d) pairs with pairwise non-`===` keys."
    "Invariant; base/iddict.jl:90,111-112,147"
    ``IdDictLengthLive,
  entry "iddicts-getbang-absent"
    ["get!(::IdDict,k,default)"]
    "For an absent key of type `K`, get!(d,k,default) stores and returns `convert(V,default)` and increases length by one."
    "get! docstring base/dict.jl:393-394"
    ``IdDictGetBangAbsent,
  entry "iddicts-token-lookup"
    ["haskey(::IdDict,k)", "in(k,::KeySet{<:Any,<:IdDict})", "getindex(::IdDict,k)"]
    "For every identity-key present in iteration, haskey's KeySet test reports it present and indexing returns its stored value."
    "haskey docstring base/dict.jl:537; KeyError docstring base/abstractdict.jl:5-9"
    ``LookupFindsPresent,
  entry "iddicts-token-pop"
    ["pop!(::IdDict,k)"]
    "pop!(d,k) returns the stored value of every present key."
    "pop! docstring base/dict.jl:594-595"
    ``PopReturnsPresent,
  entry "iddicts-token-getbang"
    ["get!(::IdDict,k,default)", "get!(f,::IdDict,k)"]
    "get! on a present key returns its stored value and leaves the dictionary contents unchanged without calling a callable default."
    "get! docstring base/dict.jl:393-394"
    ``GetBangKeepsPresent,
  entry "iddict-empty-constructors"
    ["IdDict{K,V}()@31", "IdDict()@52", "IdDict(::Tuple{})@53",
      "empty(::IdDict,::Type{K},::Type{V})@62"]
    "Each empty IdDict constructor creates a 32-word table with zero live and deleted counts."
    "IdDict constructor and empty invariants; base/iddict.jl:31,52-53,62"
    ``EmptyConstructors,
  entry "iddict-empty-bang"
    ["empty!(::IdDict)@128"]
    "empty! clears all pairs, replaces the table with 32 words, resets both counts, and returns the dictionary."
    "IdDict table invariant; base/iddict.jl:128-137"
    ``EmptyBangContents,
  entry "iddict-pair-constructors"
    ["IdDict{K,V}(pairs::Pair...)@42", "IdDict(ps::Pair{K,V}...)@55",
      "IdDict(ps::Pair{K}...)@56", "IdDict(ps::(Pair{K,V} where K)...)@57",
      "IdDict(ps::Pair...)@58"]
    "Pair constructors retain the last value for each `===` key, converting each value to the selected `V` type."
    "IdDict constructor docstring base/iddict.jl:6-8; pair constructors base/iddict.jl:42-58"
    ``PairConstructors,
  entry "iddict-iterator-constructor"
    ["IdDict{K,V}(itr)@33"]
    "The iterator constructor optionally size-hints length or shape iterators and inserts every yielded pair in iteration order."
    "IdDict constructor docstring base/iddict.jl:6-8; base/iddict.jl:33-40"
    ``IteratorConstructor,
  entry "iddict-eltype-constructor"
    ["IdDict(kv)@60"]
    "The generic IdDict constructor selects key and value types from `eltype(kv)`."
    "IdDict constructor docstring base/iddict.jl:6-8; base/iddict.jl:60"
    ``EltypeConstructor,
  entry "iddict-copy-contents"
    ["IdDict{K,V}(d::IdDict{K,V})@49", "copy(d::IdDict)@149"]
    "Copying preserves every key-value association and both counts while creating independent table memory."
    "Copy invariant; base/iddict.jl:49,149"
    ``CopyPreservesContents,
  entry "iddict-rehash-sizehint-contents"
    ["rehash!(::IdDict,n)@64", "sizehint!(::IdDict,n)@69"]
    "Rehashing preserves all associations and counts at the requested capacity; sizehint keeps the current table below the 25 percent growth threshold and otherwise grows to the computed table size."
    "IdDict table invariants and sizehint comment; base/iddict.jl:64-77"
    ``RehashSizehintPreservesContents,
  entry "iddict-setindex-types"
    ["setindex!(::IdDict{K,V},v,k)@79"]
    "setindex! converts values to `V`, stores them under identity keys, and increments the live count only for a new key."
    "IdDict docstring base/iddict.jl:6-8; base/iddict.jl:79-92"
    ``SetindexTypeAndValue,
  entry "iddict-setindex-keytype"
    ["setindex!(::IdDict{K,V},v,k)@79"]
    "setindex! throws KeyTypeError before changing the table when the key is not of type `K`."
    "IdDict key type contract; base/iddict.jl:79-80"
    ``SetindexRejectsInvalidKey,
  entry "iddict-pop-counts"
    ["pop!(::IdDict,k,default)@105", "pop!(::IdDict,k)@117", "delete!(::IdDict,k)@123"]
    "Removing a present key decrements length and increments the deleted-slot count; missing pop! throws KeyError, while missing defaulted pop! and delete! leave counts unchanged."
    "pop! docstring base/dict.jl:594-595; table invariant base/iddict.jl:105-126"
    ``PopAndDeleteCounters,
  entry "iddict-index-missing"
    ["getindex(::IdDict,k)@99"]
    "Indexing a key absent by identity throws KeyError containing that key."
    "KeyError docstring base/abstractdict.jl:5-9; base/iddict.jl:99-103"
    ``MissingGetindexKeyError,
  entry "iddict-callable-get"
    ["get(default::Callable,::IdDict,k)@162"]
    "Callable get returns a present value without calling its default and calls the default for a missing key."
    "get docstring; base/iddict.jl:162-169"
    ``CallableGet,
  entry "iddict-callable-getbang"
    ["get!(default::Callable,::IdDict,k)@171"]
    "For an absent valid key, callable get! invokes its default, converts and stores the result, returns it, and increases length by one."
    "get! docstring base/dict.jl:393-394; base/iddict.jl:171-183"
    ``CallableGetBang
]

/-! Nothing to promise: `filter!@189` directly forwards to AbstractDict's shared one-pass filter method. -/

/-! ## Method -> property table

| Julia method | Property |
|---|---|
| `IdDict{K,V}()@31` | `iddict-empty-constructors` |
| `IdDict{K,V}(itr)@33` | `iddict-iterator-constructor` |
| `IdDict{K,V}(pairs::Pair...)@42` | `iddict-pair-constructors` |
| `IdDict{K,V}(d::IdDict{K,V})@49` | `iddict-copy-contents` |
| `IdDict()@52` | `iddict-empty-constructors` |
| `IdDict(::Tuple{})@53` | `iddict-empty-constructors` |
| `IdDict(ps::Pair{K,V}...)@55` | `iddict-pair-constructors` |
| `IdDict(ps::Pair{K}...)@56` | `iddict-pair-constructors` |
| `IdDict(ps::(Pair{K,V} where K)...)@57` | `iddict-pair-constructors` |
| `IdDict(ps::Pair...)@58` | `iddict-pair-constructors` |
| `IdDict(kv)@60` | `iddict-eltype-constructor` |
| `empty(::IdDict,::Type{K},::Type{V})@62` | `iddict-empty-constructors` |
| `rehash!(::IdDict,n)@64` | `iddict-rehash-sizehint-contents` |
| `sizehint!(::IdDict,n)@69` | `iddict-rehash-sizehint-contents` |
| `setindex!(::IdDict{K,V},v,k)@79` | `iddict-setindex-types`, `iddict-setindex-keytype`, `iddicts-ops-agree` |
| `get(::IdDict{K,V},k,default)@94` | `iddicts-ops-agree` |
| `getindex(::IdDict{K,V},k)@99` | `iddicts-token-lookup`, `iddict-index-missing` |
| `pop!(::IdDict{K,V},k,default)@105` | `iddict-pop-counts`, `iddicts-ops-agree` |
| `pop!(::IdDict{K,V},k)@117` | `iddicts-token-pop`, `iddict-pop-counts`, `iddicts-ops-agree` |
| `delete!(::IdDict{K},k)@123` | `iddict-pop-counts`, `iddicts-ops-agree` |
| `empty!(::IdDict)@128` | `iddict-empty-bang`, `iddicts-ops-agree` |
| `_oidd_nextind(a,i)@139` | `iddicts-length-live` |
| `iterate(::IdDict{K,V},idx=0)@141` | `iddicts-length-live`, `iddicts-ops-agree` |
| `length(::IdDict)@147` | `iddicts-length-live`, `iddicts-ops-agree` |
| `copy(::IdDict)@149` | `iddict-copy-contents` |
| `get!(::IdDict{K,V},k,default)@151` | `iddicts-getbang-absent`, `iddicts-token-getbang`, `iddicts-length-live` |
| `get(::Callable,::IdDict{K,V},k)@162` | `iddict-callable-get` |
| `get!(::Callable,::IdDict{K,V},k)@171` | `iddict-callable-getbang`, `iddicts-token-getbang`, `iddicts-length-live` |
| `in(k,::KeySet{<:Any,<:IdDict})@185` | `iddicts-token-lookup` |
| `filter!(f,::IdDict)@189` | Nothing to promise: it forwards to AbstractDict's shared one-pass filtering method. |
-/

end JuliaLean.Proofs.base.iddict
