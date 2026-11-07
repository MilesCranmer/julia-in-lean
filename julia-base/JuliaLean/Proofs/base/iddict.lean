import JuliaLean.base.iddict
import JuliaLean.Registry.Types

/-! Native IdDict statements. Remaining Core, allocation, conversion, iterator,
and Pair-access gaps are recorded per entry; no callee correctness laws are assumed. -/
namespace JuliaLean.Proofs.base.iddict
open JuliaLean JuliaLean.Registry
open JuliaLean.src.identity_runtime (Word World Memory M Error)
noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition
namespace D
export JuliaLean.base.iddict (Callees DictFields dictionary isa assertType secretToken
  emptyTyped emptyAny emptyTuple emptyOf copyConstruct copyDict rehash rehashCsize sizehint!
  setindex! get getindex popDefault pop deleteBang emptyBang iterate length getBang
  getCallable getBangCallable inKeySet IteratorCalls fromPairs fromPairsKV fromPairsK
  fromPairsV fromPairsAny fromIterator fromEltype)
end D
namespace N
export JuliaLean.src.identity_runtime (plainReadCell loadWord getWorld memoryOwner)
export JuliaLean.src.builtins_identity_c (jl_egal_ jl_object_id)
end N

def outcome {A : Type} (action : M A) (world : World) : Option (Except Error A) :=
  (action world).map Prod.fst

def succeeds {A : Type} (action : M A) (world : World) (value : A) : Prop :=
  ∃ final, action world = some (.ok value, final)

def returns {A : Type} (action : M A) (world : World) (post : A → World → Prop) : Prop :=
  ∀ value final, action world = some (.ok value, final) → post value final

def identical (world : World) (left right : Word) : Prop :=
  succeeds (N.jl_egal_ left right) world true

def validValue (world : World) (value : Word) : Prop :=
  value ≠ 0 ∧ ∃ hash, succeeds (N.jl_object_id value) world hash

def livePairs (memory : Memory) : M (List (Word × Word)) := do
  let mut pairs := []
  for index in List.range (memory.length / 2) do
    let value ← N.plainReadCell memory (UInt64.ofNat (2*index+1))
    if value != 0 then
      let key ← N.plainReadCell memory (UInt64.ofNat (2*index))
      pairs := pairs ++ [(key, value)]
  pure pairs

def contents (address : Word) : M (List (Word × Word)) := do
  livePairs (← D.dictionary address).ht

def referenceLookup : List (Word × Word) → Word → M (Option Word)
  | [], _ => pure none
  | (stored, value) :: rest, key => do
    if ← N.jl_egal_ key stored then pure (some value) else referenceLookup rest key

def referenceSet : List (Word × Word) → Word → Word → M (List (Word × Word))
  | [], key, value => pure [(key, value)]
  | (stored, old) :: rest, key, value => do
    if ← N.jl_egal_ key stored then pure ((stored, value) :: rest)
    else return (stored, old) :: (← referenceSet rest key value)

def referenceDelete : List (Word × Word) → Word → M (List (Word × Word))
  | [], _ => pure []
  | (stored, value) :: rest, key => do
    if ← N.jl_egal_ key stored then pure rest
    else return (stored, value) :: (← referenceDelete rest key)

def keysDistinct (world : World) : List (Word × Word) → Prop
  | [] => True
  | (key, _) :: rest =>
    (∀ pair ∈ rest, succeeds (N.jl_egal_ key pair.1) world false) ∧ keysDistinct world rest

def mapsEquivalent (world : World) (left right : List (Word × Word)) : Prop :=
  ∀ key, outcome (referenceLookup left key) world = outcome (referenceLookup right key) world

/-- Physical hash placement and occupied probe prefixes, independent of lookup. -/
def tablePlacement (world : World) (memory : Memory) : Prop :=
  ∀ index < memory.length/2, ∀ key value,
    succeeds (N.plainReadCell memory (UInt64.ofNat (2*index))) world key →
    succeeds (N.plainReadCell memory (UInt64.ofNat (2*index+1))) world value →
    (value = 0 → key = 0 ∨ key = world.globals.nothing) ∧
    (value ≠ 0 → ∃ hash distance,
      succeeds (N.jl_object_id key) world hash ∧
      distance < memory.length/2 ∧
      distance ≤ (JuliaLean.src.iddict_c.max_probe (UInt64.ofNat (memory.length/2))).toNat ∧
      (hash.toNat % (memory.length/2)+distance) % (memory.length/2) = index ∧
      ∀ step < distance, ∃ previous, previous ≠ 0 ∧
        succeeds (N.plainReadCell memory
          (UInt64.ofNat (2*((hash.toNat % (memory.length/2)+step) % (memory.length/2)))))
          world previous)

def dictInvariant (world : World) (address : Word) : Prop :=
  ∃ fields pairs,
    succeeds (D.dictionary address) world fields ∧ succeeds (contents address) world pairs ∧
    32 ≤ fields.ht.length ∧ fields.ht.length < 2^61 ∧
    (∃ exponent : Nat, fields.ht.length = 2^exponent) ∧
    fields.ht.metadata.memoryLayout.size.val = 8 ∧
    fields.ht.ptr + 8*fields.ht.length ≤ 2^64 ∧
    (∀ offset < 8*fields.ht.length, world.raw.heap.validByte (fields.ht.ptr+offset) = true) ∧
    0 ≤ fields.count.val ∧ 0 ≤ fields.ndel.val ∧
    fields.count.val + fields.ndel.val ≤ Int.ofNat (fields.ht.length/2) ∧
    fields.count.val = Int.ofNat pairs.length ∧ keysDistinct world pairs ∧
    (∀ pair ∈ pairs, validValue world pair.1 ∧ validValue world pair.2) ∧
    tablePlacement world fields.ht

def loadedToken (world : World) : Prop :=
  ∃ token, succeeds D.secretToken world token ∧ validValue world token

def lookupValue (world : World) (address key : Word) (value : Option Word) : Prop :=
  ∃ pairs, succeeds (contents address) world pairs ∧
    succeeds (referenceLookup pairs key) world value

def excludesSecretToken (world : World) (address token : Word) : Prop :=
  ∀ pairs, succeeds (contents address) world pairs → ∀ pair ∈ pairs, pair.2 ≠ token

def storedValueAssertions (calls : D.Callees) (world : World) (address : Word) : Prop :=
  ∀ fields pairs, succeeds (D.dictionary address) world fields →
    succeeds (contents address) world pairs → ∀ pair ∈ pairs,
      D.assertType calls pair.2 fields.valueType world = some (.ok pair.2, world)

def validSecretSymbol (world : World) (token : Word) : Prop :=
  validValue world token ∧ succeeds (JuliaLean.src.identity_runtime.typetag token) world (18 * 16)

def typeAssertionWorldIndependent (calls : D.Callees) : Prop :=
  ∀ value type first second,
    outcome (D.assertType calls value type) first = outcome (D.assertType calls value type) second

def returnedValueAndContents (address : Word) (action : M Word) (world : World) :
    Option (Except Error Word × Option (Except Error (List (Word × Word)))) :=
  (action world).map fun (result, final) => (result, outcome (contents address) final)

def matchesReference (world : World) (address : Word) (expected : List (Word × Word)) : Prop :=
  ∃ fields actual, succeeds (D.dictionary address) world fields ∧
    succeeds (contents address) world actual ∧
    fields.count.val = Int.ofNat expected.length ∧ keysDistinct world actual ∧
    mapsEquivalent world actual expected

def collectPairs (calls : D.Callees) (pairFields : Word → M (Word × Word))
    (address : Word) (cursor : JInt .i64 := JInt.wrap .i64 0) : M (List (Word × Word)) := do
  match ← D.iterate calls address cursor with
  | none => pure []
  | some (pair, next) =>
    let pair ← pairFields pair
    return pair :: (← collectPairs calls pairFields address next)
partial_fixpoint

def convertedValue (calls : D.Callees) (address value : Word) : M Word := do
  let fields ← D.dictionary address
  if ← D.isa calls value fields.valueType then pure value
  else D.assertType calls (← calls.convert fields.valueType value) fields.valueType

inductive Operation where
  | set (key value : Word)
  | erase (key : Word)
  | popDefault (key fallback : Word)
  | pop (key : Word)
  | getBang (key fallback : Word)
  | getBangCallable (key : Word) (fallback : Unit → M Word)
  | empty
  | sizehint (size : Word)

def runOperations (calls : D.Callees) (address : Word) : List Operation → M Unit
  | [] => pure ()
  | operation :: rest => do
    match operation with
    | .set key value => let _ ← D.setindex! calls address value key; pure ()
    | .erase key => let _ ← D.deleteBang calls address key; pure ()
    | .popDefault key fallback => let _ ← D.popDefault calls address key fallback; pure ()
    | .pop key => let _ ← D.pop calls address key; pure ()
    | .getBang key fallback => let _ ← D.getBang calls address key fallback; pure ()
    | .getBangCallable key fallback => let _ ← D.getBangCallable calls fallback address key; pure ()
    | .empty => let _ ← D.emptyBang calls address; pure ()
    | .sizehint size => let _ ← D.sizehint! calls address size; pure ()
    runOperations calls address rest

def referenceStep (calls : D.Callees) (address : Word) (operation : Operation)
    (pairs : List (Word × Word)) : M (List (Word × Word)) := do
  match operation with
  | .set key value => referenceSet pairs key (← convertedValue calls address value)
  | .erase key | .popDefault key _ | .pop key => referenceDelete pairs key
  | .empty => pure []
  | .sizehint _ => pure pairs
  | .getBang key fallback =>
    match ← referenceLookup pairs key with
    | some _ => pure pairs
    | none => referenceSet pairs key (← convertedValue calls address fallback)
  | .getBangCallable key fallback =>
    match ← referenceLookup pairs key with
    | some _ => pure pairs
    | none => referenceSet pairs key (← convertedValue calls address (← fallback ()))

def runReference (calls : D.Callees) (address : Word) :
    List Operation → List (Word × Word) → M (List (Word × Word))
  | [], pairs => pure pairs
  | operation :: rest, pairs => do
    runReference calls address rest (← referenceStep calls address operation pairs)

def IdDictOpsAgree : Prop :=
  ∀ calls pairFields world address operations initial,
    dictInvariant world address → loadedToken world → operations.length < 2^62 →
    succeeds (contents address) world initial →
    returns (runOperations calls address operations) world fun _ final =>
      ∃ expected pairs count,
        succeeds (runReference calls address operations initial) world expected ∧
        matchesReference final address expected ∧
        succeeds (collectPairs calls pairFields address) final pairs ∧
        succeeds (D.length address) final count ∧ count.val = Int.ofNat pairs.length ∧
        keysDistinct final pairs ∧ mapsEquivalent final pairs expected ∧
        ∀ key fallback, outcome (D.get calls address key fallback) final =
          outcome (do return (← referenceLookup expected key).getD fallback) final

def IdDictLengthLive : Prop :=
  ∀ calls pairFields world address operations,
    dictInvariant world address → loadedToken world → operations.length < 2^62 →
    returns (runOperations calls address operations) world fun _ final =>
      ∃ pairs count, succeeds (collectPairs calls pairFields address) final pairs ∧
        succeeds (D.length address) final count ∧ count.val = Int.ofNat pairs.length ∧
        keysDistinct final pairs

def IdDictGetBangAbsent : Prop :=
  ∀ calls world address key fallback before,
    dictInvariant world address → loadedToken world →
    succeeds (D.length address) world before → lookupValue world address key none →
    returns (D.getBang calls address key fallback) world fun value final =>
      succeeds (convertedValue calls address fallback) world value ∧
      lookupValue final address key (some value) ∧
      succeeds (D.length address) final (before+JInt.wrap .i64 1)

def LookupFindsPresent : Prop :=
  ∀ calls world address key value token,
    dictInvariant world address → succeeds D.secretToken world token →
    excludesSecretToken world address token → storedValueAssertions calls world address →
    validSecretSymbol world token → typeAssertionWorldIndependent calls →
    lookupValue world address key (some value) →
    succeeds (D.inKeySet calls address key) world true ∧
    succeeds (D.getindex calls address key) world value

/-- Absence is checked in actual table cells using native identity, not assumed
from the result of jl_eqtable_get. No allocation, conversion or iterator law is needed. -/
def MissingGetindexKeyError : Prop :=
  ∀ calls world address key,
    dictInvariant world address → loadedToken world → validValue world key →
    lookupValue world address key none →
    outcome (D.getindex calls address key) world = some (.error (.keyError key))

def PopReturnsPresent : Prop :=
  ∀ calls world address key value token before,
    dictInvariant world address → succeeds D.secretToken world token →
    excludesSecretToken world address token → storedValueAssertions calls world address →
    validSecretSymbol world token → typeAssertionWorldIndependent calls →
    succeeds (D.length address) world before → lookupValue world address key (some value) →
    ∃ final, D.pop calls address key world =
      some (.ok value, final) ∧
      lookupValue final address key none ∧
      succeeds (D.length address) final (before-JInt.wrap .i64 1)

def GetBangKeepsPresent : Prop :=
  ∀ calls world address key value token fallback callable before,
    dictInvariant world address → succeeds D.secretToken world token →
    excludesSecretToken world address token → storedValueAssertions calls world address →
    validSecretSymbol world token → typeAssertionWorldIndependent calls →
    lookupValue world address key (some value) → succeeds (D.length address) world before →
    succeeds (D.getBang calls address key fallback) world value ∧
    succeeds (D.getBangCallable calls callable address key) world value ∧
    (∀ final, D.getBang calls address key fallback world = some (.ok value, final) →
      outcome (contents address) final = outcome (contents address) world) ∧
    (∀ final, D.getBangCallable calls callable address key world = some (.ok value, final) →
      outcome (contents address) final = outcome (contents address) world)

def emptyShape (world : World) (address : Word) : Prop :=
  ∃ fields, succeeds (D.dictionary address) world fields ∧
    fields.ht.length = 32 ∧ fields.count.val = 0 ∧ fields.ndel.val = 0 ∧
    succeeds (contents address) world []

def EmptyConstructors : Prop :=
  ∀ calls world keyType valueType address,
    returns (D.emptyTyped calls keyType valueType) world (fun result final => emptyShape final result) ∧
    returns (D.emptyAny calls) world (fun result final => emptyShape final result) ∧
    returns (D.emptyTuple calls ()) world (fun result final => emptyShape final result) ∧
    returns (D.emptyOf calls address keyType valueType) world (fun result final => emptyShape final result)

def EmptyBangContents : Prop :=
  ∀ calls world address before,
    dictInvariant world address → succeeds (D.dictionary address) world before →
    returns (D.emptyBang calls address) world fun result final =>
      result = address ∧ emptyShape final address ∧
      ∃ after, succeeds (D.dictionary address) final after ∧ after.ht.ptr ≠ before.ht.ptr

def pairReferenceLoop (calls : D.Callees) (address : Word) :
    List (Word × Word) → List (Word × Word) → M (List (Word × Word))
  | [], expected => pure expected
  | (key, value) :: rest, expected => do
    let updated ← referenceSet expected key (← convertedValue calls address value)
    pairReferenceLoop calls address rest updated

def pairReference (calls : D.Callees) (address : Word) (pairs : List (Word × Word)) :
    M (List (Word × Word)) := pairReferenceLoop calls address pairs []

def iteratorPairs {I S : Type} (iter : D.IteratorCalls I S) (input : I)
    (state : Option S := none) : M (List (Word × Word)) := do
  match ← iter.iterate input state with
  | none => pure []
  | some (value, next) =>
    let pair ← iter.destructure value
    return pair :: (← iteratorPairs iter input (some next))
partial_fixpoint
def PairConstructors : Prop :=
  ∀ {I S : Type} (calls : D.Callees) (iter : D.IteratorCalls I S)
    world keyType valueType (input : I) pairs,
    pairs.length < 2^62 →
    let post := fun result final =>
      ∃ expected, succeeds (pairReference calls result pairs) final expected ∧
        matchesReference final result expected
    returns (D.fromPairs calls keyType valueType pairs) world post ∧
    (succeeds (iteratorPairs iter input) world pairs →
      returns (D.fromPairsKV calls iter keyType valueType input) world post ∧
      returns (D.fromPairsK calls iter keyType input) world post ∧
      returns (D.fromPairsV calls iter valueType input) world post ∧
      returns (D.fromPairsAny calls iter input) world post)


def IteratorConstructor : Prop :=
  ∀ {I S : Type} calls (iter : D.IteratorCalls I S) world keyType valueType input pairs,
    succeeds (iteratorPairs iter input) world pairs → pairs.length < 2^62 →
    returns (D.fromIterator calls iter keyType valueType input) world fun result final =>
      ∃ expected, succeeds (pairReference calls result pairs) final expected ∧
        matchesReference final result expected

def EltypeConstructor : Prop :=
  ∀ {I S : Type} calls (iter : D.IteratorCalls I S) dispatch eltype
    (types : Word → Word × Word) world input,
    (∀ constructor argument typeTag state,
      returns (dispatch constructor argument typeTag) state fun result final =>
        ∃ fields, succeeds (D.dictionary result) final fields ∧
          fields.keyType = (types typeTag).1 ∧ fields.valueType = (types typeTag).2) →
    returns (D.fromEltype calls iter dispatch input eltype) world fun result final =>
      ∃ fields, succeeds (D.dictionary result) final fields ∧
        fields.keyType = (types (eltype input)).1 ∧ fields.valueType = (types (eltype input)).2

def CopyPreservesContents : Prop :=
  ∀ calls world address before pairs,
    dictInvariant world address → succeeds (D.dictionary address) world before →
    succeeds (contents address) world pairs →
    let post := fun result final =>
      matchesReference final result pairs ∧ ∃ after,
        succeeds (D.dictionary result) final after ∧ after.count = before.count ∧
        after.ndel = before.ndel ∧ after.ht.ptr ≠ before.ht.ptr
    returns (D.copyConstruct calls address) world post ∧ returns (D.copyDict calls address) world post

def RehashSizehintPreservesContents : Prop :=
  ∀ calls world address request before pairs,
    dictInvariant world address → succeeds (D.dictionary address) world before →
    succeeds (contents address) world pairs →
    let post := fun result final => result = address ∧ matchesReference final address pairs ∧
      ∃ after, succeeds (D.dictionary address) final after ∧
        after.count = before.count ∧ after.ndel = before.ndel
    (∀ wordSize, succeeds (calls.toCsize request) world wordSize →
      returns (D.rehash calls address request) world fun result final =>
        post result final ∧ ∃ after, succeeds (D.dictionary address) final after ∧
          after.ht.length = wordSize.toNat) ∧
    (∀ doubled requested wordSize belowThreshold,
      succeeds (calls.doubleInteger request) world doubled →
      succeeds (calls.tableSize doubled) world requested →
      succeeds (calls.toCsize requested) world wordSize →
      let oldSize := JInt.wrap .i64 (Int.ofNat before.ht.length)
      let threshold := JuliaLean.base.int.ashr_int (oldSize * JInt.wrap .i64 5) (JInt.wrap .i64 2)
      succeeds (calls.lessThanInt requested threshold) world belowThreshold →
      returns (D.sizehint! calls address request) world fun result final =>
        post result final ∧ ∃ after, succeeds (D.dictionary address) final after ∧
          if belowThreshold then after.ht.ptr = before.ht.ptr else after.ht.length = wordSize.toNat)

def SetindexTypeAndValue : Prop :=
  ∀ calls world address value key before,
    dictInvariant world address → succeeds (D.dictionary address) world before →
    returns (D.setindex! calls address value key) world fun result final =>
      result = address ∧ ∃ stored,
        succeeds (convertedValue calls address value) world stored ∧
        lookupValue final address key (some stored) ∧
        succeeds (D.length address) final
          (before.count+JInt.wrap .i64 (if lookupValue world address key none then 1 else 0))

def SetindexRejectsInvalidKey : Prop :=
  ∀ calls world address value key before,
    dictInvariant world address → succeeds (D.dictionary address) world before →
    succeeds (D.isa calls key before.keyType) world false →
    ∃ final, D.setindex! calls address value key world =
      some (.error (.keyTypeError before.keyType key), final) ∧
      ∃ after, succeeds (D.dictionary address) final after ∧
        after.count = before.count ∧ after.ndel = before.ndel ∧
        outcome (contents address) final = outcome (contents address) world

def PopAndDeleteCounters : Prop :=
  ∀ calls world address key fallback token before pairs,
    dictInvariant world address → succeeds D.secretToken world token → validValue world key →
    succeeds (D.dictionary address) world before → succeeds (contents address) world pairs →
    let post := fun final removed =>
      lookupValue final address key none ∧
      (∃ remaining, succeeds (referenceDelete pairs key) world remaining ∧
        matchesReference final address remaining) ∧
      ∃ after, succeeds (D.dictionary address) final after ∧
        after.count.val = before.count.val-removed ∧ after.ndel.val = before.ndel.val+removed
    (lookupValue world address key none →
      (∃ final, D.popDefault calls address key fallback world = some (.ok fallback, final) ∧ post final 0) ∧
      (∃ final, D.pop calls address key world = some (.error (.keyError key), final) ∧ post final 0) ∧
      (∃ final, D.deleteBang calls address key world = some (.ok address, final) ∧ post final 0)) ∧
    (∀ value, lookupValue world address key (some value) →
      (∃ final, D.popDefault calls address key fallback world = some (.ok value, final) ∧ post final 1) ∧
      (∃ final, D.pop calls address key world =
        some ((if identical world value token then .error (.keyError key) else .ok value), final) ∧
        post final 1) ∧
      (∃ final, D.deleteBang calls address key world = some (.ok address, final) ∧ post final 1))

def CallableGet : Prop :=
  ∀ calls world address key token (fallback : Unit → M Word),
    dictInvariant world address → succeeds D.secretToken world token →
    excludesSecretToken world address token → storedValueAssertions calls world address →
    validSecretSymbol world token →
    (lookupValue world address key none →
      returnedValueAndContents address (D.getCallable calls fallback address key) world =
        returnedValueAndContents address (fallback ()) world) ∧
    ∀ value, lookupValue world address key (some value) →
      succeeds (D.getCallable calls fallback address key) world value

def CallableGetBang : Prop :=
  ∀ calls world address key token (fallback : Unit → M Word) before,
    dictInvariant world address → succeeds D.secretToken world token →
    succeeds (D.length address) world before →
    returns (D.getBangCallable calls fallback address key) world fun result final =>
      (lookupValue world address key none →
        succeeds (do convertedValue calls address (← fallback ())) world result) ∧
      lookupValue final address key (some result) ∧
      succeeds (D.length address) final
        (before+JInt.wrap .i64 (if lookupValue world address key none then 1 else 0))

private def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/iddict.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo, prop := prop,
    notes := "Native restatement for review; no callback correctness law. " ++
      match id with
      | "iddict-index-missing" => "Requires a valid native heap; no remaining callee gap is reached."
      | "iddict-empty-constructors" => "Blocked: G1 allocateBoxedMemory and G2 newObject."
      | "iddict-empty-bang" => "Blocked: G1 allocateBoxedMemory."
      | "iddict-pair-constructors" => "Blocked: G1 allocateBoxedMemory, G2 newObject, G3 isa/convert, G4 lengthArgument, G6 IteratorCalls, G8 newPair."
      | "iddict-iterator-constructor" => "Blocked: G1 allocateBoxedMemory, G2 newObject, G3 isa/convert, G4 lengthArgument, G6 IteratorCalls."
      | "iddict-eltype-constructor" => "Blocked: G1 allocateBoxedMemory, G2 newObject, G3 isa/convert, G4 lengthArgument, G6 IteratorCalls/dictWithEltype."
      | "iddict-copy-contents" => "Blocked: G2 newObject, G5 copyMemory."
      | "iddict-rehash-sizehint-contents" => "Blocked: G1 allocateBoxedMemory, G4 doubleInteger/tableSize/lessThanInt/toCsize."
      | "iddict-setindex-keytype" => "Blocked: G3 isa."
      | "iddict-pop-counts" | "iddicts-token-lookup" | "iddicts-token-pop"
        | "iddicts-token-getbang" | "iddict-callable-get" => "Blocked: G3 isa/convert and native value assertions."
      | "iddicts-getbang-absent" | "iddict-setindex-types" | "iddict-callable-getbang" =>
        "Blocked: G1 allocateBoxedMemory, G3 isa/convert."
      | "iddicts-ops-agree" | "iddicts-length-live" =>
        "Blocked: G1 allocateBoxedMemory, G3 isa/convert, G4 Integer size calls, G8 newPair/pair fields."
      | _ => "See the declaration-specific gap inventory in iddict.model-adapt.md." }

end
end JuliaLean.Proofs.base.iddict

namespace JuliaLean.Proofs.base.iddict

open JuliaLean JuliaLean.base.iddict JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World)

/-- Physical native representation facts omitted by the existing invariant:
nonempty backing memory has a nonnull data pointer, and the runtime Nothing
global has the actual readable Nothing tag. These constrain heap/type encoding,
not any dictionary lookup or comparison result.
Julia source: src/julia.h:1110-1171,1175-1179; src/iddict.c:99-136
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def NativeRepresentation (world : World) (address : Word) : Prop :=
  (∃ fields, succeeds (JuliaLean.base.iddict.dictionary address) world fields ∧
    0 < fields.ht.ptr) ∧
  succeeds (JuliaLean.src.identity_runtime.typetag world.globals.nothing)
    world (26 * 16)

end JuliaLean.Proofs.base.iddict

namespace JuliaLean.Proofs.base.iddict.Round1

open JuliaLean JuliaLean.base.iddict JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World)

/-- Indexing an identity key absent from a valid native IdDict throws KeyError carrying that key.
Julia source: base/iddict.jl:99-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractdict.jl:5-9; doc/src/base/collections.md:197,211-214,219
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

Absence is determined independently by scanning the occupied native memory cells
and comparing keys with the installed native identity operation. It is not a
hypothesis about jl_eqtable_get or getindex. The representation predicate states
physical placement, valid bytes, count/occupancy and identity-distinct keys,
plus nonnull backing storage and the actual native Nothing tag;
its byte/address bounds exclude machine-arithmetic wrap rather than requiring a
particular amount of RAM. Callees is universally quantified without correctness
laws because this missing-key path reaches none of its unresolved fields.
-/
def MissingIdentityKeyError : Prop :=
  ∀ (calls : Callees) (world : World) (address key : Word),
    dictInvariant world address →
    NativeRepresentation world address →
    loadedToken world →
    validValue world key →
    lookupValue world address key none →
    outcome (JuliaLean.base.iddict.getindex calls address key) world =
      some (.error (.keyError key))

end JuliaLean.Proofs.base.iddict.Round1

namespace JuliaLean.Proofs.base.iddict

open JuliaLean.Registry

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

end
end JuliaLean.Proofs.base.iddict

namespace JuliaLean.ChatGPT.Batch4.Group16
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)

theorem iddict_succeeds_unique {A : Type} (action : M A) (world : World)
    {first second : A} (hfirst : succeeds action world first)
    (hsecond : succeeds action world second) : first = second := by
  obtain ⟨w₁, h₁⟩ := hfirst
  obtain ⟨w₂, h₂⟩ := hsecond
  rw [h₁] at h₂
  cases h₂
  rfl

theorem iddict_initial_count_and_keys (world : World) (address : Word)
    (h : dictInvariant world address) :
    ∃ fields pairs, succeeds (D.dictionary address) world fields ∧
      succeeds (contents address) world pairs ∧
      fields.count.val = Int.ofNat pairs.length ∧ keysDistinct world pairs := by
  obtain ⟨fields, pairs, hd, hc, _, _, _, _, _, _, _, _, _, hcount, hkeys, _, _⟩ := h
  exact ⟨fields, pairs, hd, hc, hcount, hkeys⟩

theorem iddict_identical_self (world : World) (value : Word) :
    JuliaLean.src.builtins_identity_c.jl_egal_ value value world =
      some (.ok true, world) := by
  rw [JuliaLean.src.builtins_identity_c.jl_egal_]
  simp only [BEq.rfl, Bool.true_eq, ↓reduceIte]
  rfl

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch4.Group16

open JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World M Error)

theorem iddictConstructor_bind_success {A B : Type} (action : M A)
    (next : A → M B) (world final : World) (result : B)
    (h : (action >>= next) world = some (.ok result, final)) :
    ∃ value middle, action world = some (.ok value, middle) ∧
      next value middle = some (.ok result, final) := by
  change JuliaLean.base.iterators.bind action next world = _ at h
  cases run : action world with
  | none =>
    simp only [JuliaLean.base.iterators.bind, run] at h
    cases h
  | some entry =>
    rcases entry with ⟨outcome, middle⟩
    cases outcome with
    | error error =>
      simp only [JuliaLean.base.iterators.bind, run] at h
      cases h
    | ok value =>
      exact ⟨value, middle, rfl, by
        simpa only [JuliaLean.base.iterators.bind, run] using h⟩

theorem iddictConstructor_returns_bind {A B : Type} (action : M A)
    (next : A → M B) (world : World) (post : B → World → Prop)
    (h : ∀ value middle, returns (next value) middle post) :
    returns (action >>= next) world post := by
  intro result final run
  obtain ⟨value, middle, _, continuation⟩ :=
    iddictConstructor_bind_success action next world final result run
  exact h value middle result final continuation

theorem iddictConstructor_returns_pure {A : Type} (value : A) (world : World) :
    returns (pure value : M A) world (fun result _ => result = value) := by
  intro result final run
  change (some (Except.ok value, world) : Option (Except Error A × World)) =
    some (Except.ok result, final) at run
  cases run
  rfl

theorem IddictEltypeConstructor_proven : JuliaLean.Proofs.base.iddict.EltypeConstructor := by
  intro I S calls iter dispatch eltype types world input dispatchLaw
  exact dispatchLaw
    (fun keyType valueType value =>
      JuliaLean.base.iddict.fromIterator calls iter keyType valueType value)
    input (eltype input) world

theorem iddictConstructor_rehashCsize_returns_address
    (calls : JuliaLean.base.iddict.Callees) (address size : Word) (world : World) :
    returns (JuliaLean.base.iddict.rehashCsize calls address size) world
      (fun result _ => result = address) := by
  unfold JuliaLean.base.iddict.rehashCsize
  apply iddictConstructor_returns_bind
  intro fields middle
  apply iddictConstructor_returns_bind
  intro memory afterRehash
  apply iddictConstructor_returns_bind
  intro ignored afterStore
  exact iddictConstructor_returns_pure address afterStore

theorem iddictConstructor_rehash_returns_address
    (calls : JuliaLean.base.iddict.Callees) (address request : Word) (world : World) :
    returns (JuliaLean.base.iddict.rehash calls address request) world
      (fun result _ => result = address) := by
  unfold JuliaLean.base.iddict.rehash
  apply iddictConstructor_returns_bind
  intro size middle
  exact iddictConstructor_rehashCsize_returns_address calls address size middle

theorem iddictConstructor_sizehint_returns_address
    (calls : JuliaLean.base.iddict.Callees) (address request : Word) (world : World) :
    returns (JuliaLean.base.iddict.sizehint! calls address request) world
      (fun result _ => result = address) := by
  unfold JuliaLean.base.iddict.sizehint!
  apply iddictConstructor_returns_bind
  intro doubled afterDouble
  apply iddictConstructor_returns_bind
  intro size afterSize
  apply iddictConstructor_returns_bind
  intro fields afterRead
  apply iddictConstructor_returns_bind
  intro below afterComparison
  cases below with
  | false => exact iddictConstructor_rehash_returns_address calls address size afterComparison
  | true => exact iddictConstructor_returns_pure address afterComparison

theorem iddictConstructor_emptyBang_returns_address
    (calls : JuliaLean.base.iddict.Callees) (address : Word) (world : World) :
    returns (JuliaLean.base.iddict.emptyBang calls address) world
      (fun result _ => result = address) := by
  unfold JuliaLean.base.iddict.emptyBang
  apply iddictConstructor_returns_bind
  intro memory afterAllocation
  apply iddictConstructor_returns_bind
  intro ignored afterTable
  apply iddictConstructor_returns_bind
  intro ignored afterClearing
  apply iddictConstructor_returns_bind
  intro ignored afterDeletedCount
  apply iddictConstructor_returns_bind
  intro ignored afterLiveCount
  apply iddictConstructor_returns_bind
  intro ignored afterWrite
  apply iddictConstructor_returns_bind
  intro ignored afterRoots
  apply iddictConstructor_returns_bind
  intro ignored afterNdel
  apply iddictConstructor_returns_bind
  intro ignored afterCount
  exact iddictConstructor_returns_pure address afterCount

theorem iddictConstructor_copyDict_eq
    (calls : JuliaLean.base.iddict.Callees) (address : Word) :
    JuliaLean.base.iddict.copyDict calls address =
      JuliaLean.base.iddict.copyConstruct calls address := rfl

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch4.Group16
open JuliaLean
open JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World M)

theorem iddictLate_setindex_rejected_run
    (calls : JuliaLean.base.iddict.Callees) (world checked : World)
    (address value key : Word) (fields : JuliaLean.base.iddict.DictFields)
    (hdict : JuliaLean.base.iddict.dictionary address world = some (.ok fields, world))
    (hcheck : JuliaLean.base.iddict.isa calls key fields.keyType world =
      some (.ok false, checked)) :
    JuliaLean.base.iddict.setindex! calls address value key world =
      some (.error (.keyTypeError fields.keyType key), checked) := by
  simp only [JuliaLean.base.iddict.setindex!, Bind.bind,
    JuliaLean.base.iterators.bind, hdict, hcheck, Bool.not_false,
    ↓reduceIte, JuliaLean.src.identity_runtime.fail,
    JuliaLean.base.iterators.fail]

theorem iddictLate_setindex_rejected_preserves
    (calls : JuliaLean.base.iddict.Callees) (world : World)
    (address value key : Word) (before : JuliaLean.base.iddict.DictFields)
    (hdict : JuliaLean.base.iddict.dictionary address world = some (.ok before, world))
    (hcheck : JuliaLean.base.iddict.isa calls key before.keyType world =
      some (.ok false, world)) :
    ∃ final, JuliaLean.base.iddict.setindex! calls address value key world =
      some (.error (.keyTypeError before.keyType key), final) ∧
      ∃ after, succeeds (JuliaLean.base.iddict.dictionary address) final after ∧
        after.count = before.count ∧ after.ndel = before.ndel ∧
        outcome (contents address) final = outcome (contents address) world := by
  exact ⟨world, iddictLate_setindex_rejected_run calls world world address value key
    before hdict hcheck, before, ⟨world, hdict⟩, rfl, rfl, rfl⟩

theorem iddictLate_getindex_token_run
    (calls : JuliaLean.base.iddict.Callees) (world probed compared : World)
    (address key token : Word) (fields : JuliaLean.base.iddict.DictFields)
    (hdict : JuliaLean.base.iddict.dictionary address world = some (.ok fields, world))
    (htoken : JuliaLean.base.iddict.secretToken world = some (.ok token, world))
    (hget : JuliaLean.src.iddict_c.jl_eqtable_get fields.ht key token world =
      some (.ok token, probed))
    (heq : JuliaLean.src.builtins_identity_c.jl_egal_ token token probed =
      some (.ok true, compared)) :
    JuliaLean.base.iddict.getindex calls address key world =
      some (.error (.keyError key), compared) := by
  simp only [JuliaLean.base.iddict.getindex, Bind.bind,
    JuliaLean.base.iterators.bind, hdict, htoken, hget, heq,
    ↓reduceIte, JuliaLean.src.identity_runtime.fail,
    JuliaLean.base.iterators.fail]

theorem iddictLate_callable_token_run
    (calls : JuliaLean.base.iddict.Callees) (world probed compared : World)
    (address key token : Word) (fallback : Unit → M Word)
    (fields : JuliaLean.base.iddict.DictFields)
    (hdict : JuliaLean.base.iddict.dictionary address world = some (.ok fields, world))
    (htoken : JuliaLean.base.iddict.secretToken world = some (.ok token, world))
    (hget : JuliaLean.src.iddict_c.jl_eqtable_get fields.ht key token world =
      some (.ok token, probed))
    (heq : JuliaLean.src.builtins_identity_c.jl_egal_ token token probed =
      some (.ok true, compared)) :
    JuliaLean.base.iddict.getCallable calls fallback address key world =
      fallback () compared := by
  simp only [JuliaLean.base.iddict.getCallable, Bind.bind,
    JuliaLean.base.iterators.bind, hdict, htoken, hget, heq,
    ↓reduceIte]

theorem iddictLate_callable_getbang_present_run
    (calls : JuliaLean.base.iddict.Callees) (world probed compared final : World)
    (address key token value : Word) (fallback : Unit → M Word)
    (fields : JuliaLean.base.iddict.DictFields)
    (hdict : JuliaLean.base.iddict.dictionary address world = some (.ok fields, world))
    (htoken : JuliaLean.base.iddict.secretToken world = some (.ok token, world))
    (hget : JuliaLean.src.iddict_c.jl_eqtable_get fields.ht key token world =
      some (.ok value, probed))
    (heq : JuliaLean.src.builtins_identity_c.jl_egal_ value token probed =
      some (.ok false, compared))
    (htype : JuliaLean.base.iddict.assertType calls value fields.valueType compared =
      some (.ok value, final)) :
    JuliaLean.base.iddict.getBangCallable calls fallback address key world =
      some (.ok value, final) := by
  simp only [JuliaLean.base.iddict.getBangCallable, Bind.bind,
    JuliaLean.base.iterators.bind, hdict, htoken, hget, heq,
    Bool.false_eq_true, ↓reduceIte, htype]

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch4.Group16.IdProbeArithmetic

theorem masked_le (value mask : UInt64) : (value &&& mask).toNat ≤ mask.toNat := by
  rw [UInt64.toNat_and]
  exact Nat.and_le_right

theorem sub_one_toNat (size : UInt64) (hpos : 0 < size.toNat) :
    (size - 1).toNat = size.toNat - 1 := by
  have hle : (1 : UInt64) ≤ size := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ size.toNat
    omega
  simpa only [show (1 : UInt64).toNat = 1 from rfl] using
    UInt64.toNat_sub_of_le size 1 hle

theorem masked_index_lt (value size : UInt64) (hpos : 0 < size.toNat) :
    (value &&& (size - 1)).toNat < size.toNat := by
  have hm := masked_le value (size - 1)
  rw [sub_one_toNat size hpos] at hm
  omega

theorem initial_bucket_bounds_arithmetic (hash size : UInt64) (hpos : 0 < size.toNat)
    (hsmall : 2 * size.toNat < 2 ^ 64) :
    (((hash &&& (size - 1)) * 2)).toNat + 1 < 2 * size.toNat ∧
      (((hash &&& (size - 1)) * 2)).toNat % 2 = 0 := by
  have hm := masked_le hash (size - 1)
  rw [sub_one_toNat size hpos] at hm
  have hmul : (hash &&& (size - 1)).toNat * 2 < 2 ^ 64 := by omega
  have hi : (((hash &&& (size - 1)) * 2)).toNat = (hash &&& (size - 1)).toNat * 2 := by
    rw [UInt64.toNat_mul]
    change ((hash &&& (size - 1)).toNat * 2) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt hmul
  rw [hi]
  constructor <;> omega

theorem add_one_toNat (value : UInt64) (h : value.toNat + 1 < 2 ^ 64) :
    (value + 1).toNat = value.toNat + 1 := by
  rw [UInt64.toNat_add]
  change (value.toNat + 1) % 2 ^ 64 = value.toNat + 1
  exact Nat.mod_eq_of_lt h

theorem add_two_toNat (value : UInt64) (h : value.toNat + 2 < 2 ^ 64) :
    (value + 2).toNat = value.toNat + 2 := by
  rw [UInt64.toNat_add]
  change (value.toNat + 2) % 2 ^ 64 = value.toNat + 2
  exact Nat.mod_eq_of_lt h

theorem next_cells_in_bounds (index size : UInt64)
    (hpos : 0 < size.toNat) (hsmall : size.toNat < 2 ^ 61)
    (hindex : index.toNat < size.toNat)
    (heven : index.toNat % 2 = 0) (hsizeEven : size.toNat % 2 = 0) :
    (((index + 2) &&& (size - 1)).toNat + 1 < size.toNat) ∧
      (((index + 2) &&& (size - 1)).toNat % 2 = 0) := by
  have hbound := masked_index_lt (index + 2) size hpos
  have hsum : (index + 2).toNat = index.toNat + 2 :=
    add_two_toNat index (by omega)
  have hsumEven : (index + 2).toNat % 2 = 0 := by rw [hsum]; omega
  have hnextEven : ((index + 2) &&& (size - 1)).toNat % 2 = 0 := by
    rw [UInt64.toNat_and]
    have hm := Nat.and_mod_two_pow
      (a := (index + 2).toNat) (b := (size - 1).toNat) (n := 1)
    change ((index + 2).toNat &&& (size - 1).toNat) % 2 =
      ((index + 2).toNat % 2) &&& ((size - 1).toNat % 2) at hm
    rw [hm, hsumEven, Nat.zero_and]
  exact ⟨by omega, hnextEven⟩

theorem power_length_even (length : Nat) (hlower : 32 ≤ length)
    (hpower : ∃ exponent : Nat, length = 2 ^ exponent) : length % 2 = 0 := by
  obtain ⟨exponent, hexponent⟩ := hpower
  cases exponent with
  | zero => simp only [Nat.pow_zero] at hexponent; omega
  | succ exponent => rw [hexponent, Nat.pow_succ]; omega

theorem empirical_probe_bound (size : UInt64) (hsize : 16 ≤ size.toNat) :
    (if size ≤ 1024 then (16 : UInt64) else size >>> 6).toNat ≤ size.toNat := by
  split
  · exact hsize
  · rw [UInt64.toNat_shiftRight]
    exact Nat.shiftRight_le _ _

def probeFuel (limit iteration : UInt64) : Nat := limit.toNat + 1 - iteration.toNat

theorem probe_fuel_decreases (limit iteration : UInt64)
    (hlimit : limit.toNat + 1 < 2 ^ 64)
    (hiteration : iteration.toNat ≤ limit.toNat)
    (hcontinue : iteration + 1 ≤ limit) :
    probeFuel limit (iteration + 1) < probeFuel limit iteration := by
  have hi := add_one_toNat iteration (by omega)
  have hc := UInt64.le_iff_toNat_le.mp hcontinue
  rw [hi] at hc
  unfold probeFuel
  rw [hi]
  omega

theorem last_probe_cannot_continue (limit : UInt64)
    (hlimit : limit.toNat + 1 < 2 ^ 64) : ¬ limit + 1 ≤ limit := by
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  rw [add_one_toNat limit hlimit] at hn
  omega

end JuliaLean.ChatGPT.Batch4.Group16.IdProbeArithmetic

namespace JuliaLean.ChatGPT.Batch4.Group16.PureNativeFrames

abbrev Action (State Result : Type) := State → Option (Result × State)

def Frame {State Result Events : Type} (replace : State → Events → State)
    (action : Action State Result) : Prop :=
  ∀ world result final, action world = some (result, final) →
    final = world ∧ ∀ events,
      action (replace world events) = some (result, replace world events)

theorem completed_member {State Result : Type} (chain : Action State Result → Prop)
    (hchain : Lean.Order.chain chain) (world : State)
    (result : Result) (final : State)
    (hrun : Lean.Order.CCPO.csup hchain world = some (result, final)) :
    ∃ member, chain member ∧ member world = some (result, final) := by
  have hadmissible : Lean.Order.admissible (fun action : Action State Result =>
      action world = some (result, final) →
        ∃ member, chain member ∧ member world = some (result, final)) :=
    Lean.Order.admissible_apply
      (P := fun (_ : State) (output : Option (Result × State)) =>
        output = some (result, final) →
          ∃ member, chain member ∧ member world = some (result, final))
      world (Lean.Order.Option.admissible_eq_some _ (result, final))
  exact hadmissible chain hchain
    (fun member hmember hrunMember => ⟨member, hmember, hrunMember⟩) hrun

theorem frame_admissible {State Result Events : Type}
    (replace : State → Events → State) :
    Lean.Order.admissible (Frame (Result := Result) replace) := by
  intro chain hchain hmembers world result final hrun
  obtain ⟨member, hmember, hrunMember⟩ :=
    completed_member chain hchain world result final hrun
  obtain ⟨hfinal, hframed⟩ := hmembers member hmember world result final hrunMember
  refine ⟨hfinal, ?_⟩
  intro events
  have hbelow := Lean.Order.le_csup hchain hmember (replace world events)
  change Lean.Order.FlatOrder.rel (b := none)
    (member (replace world events))
    (Lean.Order.CCPO.csup hchain (replace world events)) at hbelow
  rw [hframed events] at hbelow
  have finish {output : Option (Result × State)}
      (h : Lean.Order.FlatOrder.rel (b := none)
        (some (result, replace world events)) output) :
      output = some (result, replace world events) := by
    cases h
    rfl
  exact finish hbelow

end JuliaLean.ChatGPT.Batch4.Group16.PureNativeFrames

/-! Read-only native field decoding and a conditional completion of the invalid-key
contract. These helpers expose the one missing state-preservation obligation
without strengthening or replacing any frozen proposition. -/

namespace JuliaLean.ChatGPT.Batch8.Group5.ReadState
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime

/-- Successful and exceptional completed reads leave the world unchanged. -/
def PreservesWorld {A : Type} (action : M A) : Prop :=
  ∀ world result final, action world = some (result, final) → final = world

theorem preserves_pure {A : Type} (value : A) : PreservesWorld (pure value : M A) := by
  intro world result final h
  change some (.ok value, world) = some (result, final) at h
  cases h
  rfl

theorem preserves_fail {A : Type} (error : Error) : PreservesWorld (fail error : M A) := by
  intro world result final h
  change some (.error error, world) = some (result, final) at h
  cases h
  rfl

theorem preserves_getWorld : PreservesWorld getWorld := by
  intro world result final h
  change some (.ok world, world) = some (result, final) at h
  cases h
  rfl

theorem preserves_bind {A B : Type} (first : M A) (next : A → M B)
    (hf : PreservesWorld first) (hn : ∀ value, PreservesWorld (next value)) :
    PreservesWorld (first >>= next) := by
  intro world result final h
  cases hr : first world with
  | none =>
    simp only [Bind.bind, JuliaLean.base.iterators.bind, hr] at h
    cases h
  | some answer =>
    rcases answer with ⟨answer, middle⟩
    cases answer with
    | error error =>
      simp only [Bind.bind, JuliaLean.base.iterators.bind, hr] at h
      have hm := hf world (.error error) middle hr
      cases h
      exact hm
    | ok value =>
      have hnext : next value middle = some (result, final) := by
        simpa only [Bind.bind, JuliaLean.base.iterators.bind, hr] using h
      exact (hn value middle result final hnext).trans (hf world (.ok value) middle hr)

theorem preserves_requireReadable (address : Word) (size : Nat) :
    PreservesWorld (requireReadable address size) := by
  unfold requireReadable
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  dsimp only
  split
  · exact preserves_fail _
  · exact preserves_pure _

theorem preserves_loadWord (address : Word) : PreservesWorld (loadWord address) := by
  unfold loadWord
  apply preserves_bind _ _ (preserves_requireReadable address 8)
  intro ignored
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  exact preserves_pure _

theorem preserves_typetag (value : Word) : PreservesWorld (typetag value) := by
  unfold typetag
  split
  · exact preserves_fail _
  · apply preserves_bind _ _ (preserves_loadWord (value - 8))
    intro header
    exact preserves_pure _

/-- The dictionary field decoder contains only readonly native operations. -/
theorem preserves_datatypeAt (address : Word) : PreservesWorld (datatypeAt address) := by
  unfold datatypeAt
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split
  · exact preserves_pure _
  · exact preserves_fail _

theorem preserves_toTypeof (tag : Word) : PreservesWorld (toTypeof tag) := by
  unfold toTypeof
  split
  · apply preserves_bind _ _ preserves_getWorld
    intro snapshot
    split
    · exact preserves_pure _
    · exact preserves_fail _
  · exact preserves_pure _

theorem preserves_typeof (address : Word) : PreservesWorld (typeof address) := by
  unfold typeof
  apply preserves_bind _ _ (preserves_typetag address)
  intro tag
  exact preserves_toTypeof tag

theorem preserves_dictionary (address : Word) :
    PreservesWorld (JuliaLean.base.iddict.dictionary address) := by
  unfold JuliaLean.base.iddict.dictionary
  apply preserves_bind _ _ (preserves_loadWord address)
  intro memoryAddress
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  dsimp only
  split
  all_goals
    apply preserves_bind
    · first | exact preserves_fail _ | exact preserves_pure _
    · intro memory
      apply preserves_bind _ _ (preserves_typeof address)
      intro datatypeAddress
      apply preserves_bind _ _ (preserves_datatypeAt datatypeAddress)
      intro datatype
      apply preserves_bind _ _ (preserves_loadWord (datatype.parameters + 8))
      intro keyType
      apply preserves_bind _ _ (preserves_loadWord (datatype.parameters + 16))
      intro valueType
      apply preserves_bind _ _ (preserves_loadWord (address + 8))
      intro count
      apply preserves_bind _ _ (preserves_loadWord (address + 16))
      intro ndel
      exact preserves_pure _

/-- A successful read-only operation can be replayed in its original world. -/
theorem succeeds_exact {A : Type} (action : M A) (hread : PreservesWorld action)
    (world : World) (value : A) (h : succeeds action world value) :
    action world = some (.ok value, world) := by
  obtain ⟨final, hrun⟩ := h
  have hf := hread world (.ok value) final hrun
  subst final
  exact hrun

/-- The builtin Any fast path is read-only; other types require only the
state-preservation contract of the unresolved type-test callback. -/
theorem preserves_isa (calls : JuliaLean.base.iddict.Callees)
    (hisa : ∀ value type, PreservesWorld (calls.isa value type)) (value type : Word) :
    PreservesWorld (JuliaLean.base.iddict.isa calls value type) := by
  unfold JuliaLean.base.iddict.isa
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split
  · exact preserves_pure _
  · exact hisa value type

/-- Type assertions preserve state whenever their type test does. -/
theorem preserves_assertType (calls : JuliaLean.base.iddict.Callees)
    (hisa : ∀ value type, PreservesWorld (calls.isa value type)) (value type : Word) :
    PreservesWorld (JuliaLean.base.iddict.assertType calls value type) := by
  unfold JuliaLean.base.iddict.assertType
  apply preserves_bind _ _ (preserves_isa calls hisa value type)
  intro accepted
  cases accepted
  · exact preserves_fail _
  · exact preserves_pure _

/-- Full frozen invalid-key postcondition for a fixed callback record, under
only the missing read-only type-test contract. The physical table invariant
is not needed for this early branch. -/
theorem rejected_key_with_readonly_isa
    (calls : JuliaLean.base.iddict.Callees)
    (hisa : ∀ value type, PreservesWorld (calls.isa value type))
    (world : World) (address value key : Word)
    (before : JuliaLean.base.iddict.DictFields)
    (hdict : succeeds (JuliaLean.base.iddict.dictionary address) world before)
    (hcheck : succeeds (JuliaLean.base.iddict.isa calls key before.keyType) world false) :
    ∃ final, JuliaLean.base.iddict.setindex! calls address value key world =
      some (.error (.keyTypeError before.keyType key), final) ∧
      ∃ after, succeeds (JuliaLean.base.iddict.dictionary address) final after ∧
        after.count = before.count ∧ after.ndel = before.ndel ∧
        outcome (contents address) final = outcome (contents address) world := by
  have hd := succeeds_exact _ (preserves_dictionary address) world before hdict
  have hc := succeeds_exact _ (preserves_isa calls hisa key before.keyType) world false hcheck
  refine ⟨world, ?_, before, hdict, rfl, rfl, rfl⟩
  simp only [JuliaLean.base.iddict.setindex!, Bind.bind,
    JuliaLean.base.iterators.bind, hd, hc, Bool.not_false,
    ↓reduceIte, JuliaLean.src.identity_runtime.fail,
    JuliaLean.base.iterators.fail]

/-- A successful type assertion returns precisely its input value, independently
of any changes made by the selected type-test callback. -/
theorem assertType_success_value (calls : JuliaLean.base.iddict.Callees)
    (value type : Word) (world final : World) (result : Word)
    (h : JuliaLean.base.iddict.assertType calls value type world = some (.ok result, final)) :
    result = value := by
  unfold JuliaLean.base.iddict.assertType at h
  obtain ⟨accepted, checked, _, htail⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  cases accepted with
  | false =>
    change (some (.error (.typeAssertion type value), checked) : Option (Except Error Word × World)) =
      some (.ok result, final) at htail
    cases htail
  | true =>
    change (some (Except.ok value, checked) : Option (Except Error Word × World)) =
      some (Except.ok result, final) at htail
    cases htail
    rfl

end JuliaLean.ChatGPT.Batch8.Group5.ReadState


/-! Success traces for the first five queued IdDict contracts.  These statements
retain the actual sequence of worlds, including callback effects. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.Early
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)

/-- Successful composition exposes the real intermediate state. -/
theorem bind_success_iff {A B : Type} (action : M A) (next : A → M B)
    (world final : World) (result : B) :
    (action >>= next) world = some (.ok result, final) ↔
      ∃ value middle, action world = some (.ok value, middle) ∧
        next value middle = some (.ok result, final) := by
  change JuliaLean.base.iterators.bind action next world = _ ↔ _
  cases run : action world with
  | none => simp only [JuliaLean.base.iterators.bind, run, reduceCtorEq, false_and,
      exists_false]
  | some entry =>
    rcases entry with ⟨outcome, middle⟩
    cases outcome with
    | error error =>
      constructor
      · intro h
        simp only [JuliaLean.base.iterators.bind, run] at h
        cases h
      · rintro ⟨value, middle, h, _⟩
        cases h
    | ok value =>
      constructor
      · intro continuation
        exact ⟨value, middle, rfl, by
          simpa only [JuliaLean.base.iterators.bind, run] using continuation⟩
      · rintro ⟨other, otherMiddle, h, continuation⟩
        cases h
        simpa only [JuliaLean.base.iterators.bind, run] using continuation

/-- A pure return fixes both the returned value and the final state. -/
theorem pure_success_iff {A : Type} (value result : A) (world final : World) :
    (pure value : M A) world = some (.ok result, final) ↔
      result = value ∧ final = world := by
  change some (Except.ok value, world) = some (Except.ok result, final) ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The 32-cell request passes the native size checks and delegates to the
selected allocator. The wrapper registers its answer without enforcing shape. -/
theorem allocMemoryAny32_delegates (gc : JuliaLean.src.identity_runtime.GC) :
    JuliaLean.src.identity_runtime.allocMemoryAny gc 32 =
      (do
        let memory ← gc.allocateBoxedMemory 32
        let owner := JuliaLean.src.identity_runtime.memoryOwner memory
        JuliaLean.src.identity_runtime.modifyWorld fun world => { world with
          memories := fun address =>
            if address == owner then some memory else world.memories address }
        pure memory) := by
  rfl

/-- The clearing block occurs after the allocated table has been stored. -/
def clearAllocatedMemory (memory : Memory) : M Unit := do
  let root ← JuliaLean.src.identity_runtime.newLocal (some memory)
  JuliaLean.src.identity_runtime.pushRoots [root]
  let bytes := memory.length * 8
  JuliaLean.src.identity_runtime.requireReadable (UInt64.ofNat memory.ptr) bytes
  JuliaLean.src.identity_runtime.modifyWorld fun world => { world with
    raw := { world.raw with
      heap := world.raw.heap.writeBytes memory.ptr (List.replicate bytes (JInt.wrap .u8 0)) } }
  JuliaLean.src.identity_runtime.popRoots

/-- Exact effect of the clearing block: zero bytes, one retained local handle,
a balanced root frame, and the two corresponding events. -/
def afterClear (memory : Memory) (world : World) : World :=
  { world with
    raw := { world.raw with
      heap := world.raw.heap.writeBytes memory.ptr (List.replicate (memory.length * 8) (JInt.wrap .u8 0)) }
    locals := world.locals ++ [some memory]
    events := (world.events ++ [.pushRoots [world.locals.length]]) ++ [.popRoots] }

/-- The byte-clearing stage is fully determined when its native read-range
check succeeds; allocation and dictionary layout are not assumed. -/
theorem clearAllocatedMemory_run (memory : Memory) (world : World)
    (hptr : UInt64.ofNat memory.ptr ≠ 0)
    (hread : JuliaLean.src.identity_runtime.readableRange world.raw.heap
      (UInt64.ofNat memory.ptr).toNat (memory.length * 8) = true) :
    clearAllocatedMemory memory world = some (.ok (), afterClear memory world) := by
  simp only [clearAllocatedMemory, afterClear,
    JuliaLean.src.identity_runtime.newLocal, JuliaLean.src.identity_runtime.getWorld,
    JuliaLean.src.identity_runtime.modifyWorld, JuliaLean.src.identity_runtime.pushRoots,
    JuliaLean.src.identity_runtime.requireReadable, JuliaLean.src.identity_runtime.popRoots,
    Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret,
    hptr, hread, decide_false, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

/-- Emptying exposes the allocator result and all four ordered mutation stages.
No returned-memory shape, disjointness or freshness is postulated here. -/
theorem emptyBang_success_trace (calls : D.Callees) (address result : Word)
    (world final : World)
    (h : D.emptyBang calls address world = some (.ok result, final)) :
    result = address ∧ ∃ memory allocated stored cleared deleted,
      JuliaLean.src.identity_runtime.allocMemoryAny calls.gc 32 world =
        some (.ok memory, allocated) ∧
      JuliaLean.base.iddict.storeHT address memory allocated = some (.ok (), stored) ∧
      clearAllocatedMemory memory stored = some (.ok (), cleared) ∧
      JuliaLean.base.iddict.storeIntField address 16 (JInt.wrap .i64 0) cleared =
        some (.ok (), deleted) ∧
      JuliaLean.base.iddict.storeIntField address 8 (JInt.wrap .i64 0) deleted =
        some (.ok (), final) := by
  unfold JuliaLean.base.iddict.emptyBang at h
  obtain ⟨memory, allocated, ha, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, stored, hs, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨root, rooted, hr, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, pushed, hp, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, checked, hk, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, zeroed, hz, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, cleared, hc, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, deleted, hd, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, counted, hn, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨hresult, hf⟩ := (pure_success_iff _ _ _ _).mp h
  subst counted
  refine ⟨hresult, memory, allocated, stored, cleared, deleted, ha, hs, ?_, hd, hn⟩
  simp only [clearAllocatedMemory, Bind.bind, JuliaLean.base.iterators.bind,
    hr, hp, hk, hz, hc]

/-- An insertion trace records each callback-dependent state rather than
re-evaluating conversions in the eventual final state. -/
inductive PairInsertionTrace (calls : D.Callees) (address : Word) :
    List (Word × Word) → World → World → Prop where
  | nil (world : World) : PairInsertionTrace calls address [] world world
  | cons {key value : Word} {rest : List (Word × Word)}
      {world middle final : World} {result : Word}
      (step : D.setindex! calls address value key world = some (.ok result, middle))
      (tail : PairInsertionTrace calls address rest middle final) :
      PairInsertionTrace calls address ((key, value) :: rest) world final

/-- The copied pair loop is equivalent to its finite, ordered execution trace. -/
theorem insertPairList_success_iff (calls : D.Callees) (address : Word)
    (pairs : List (Word × Word)) (world final : World) :
    JuliaLean.base.iddict.insertPairList calls address pairs world = some (.ok (), final) ↔
      PairInsertionTrace calls address pairs world final := by
  induction pairs generalizing world with
  | nil =>
    constructor
    · intro h
      obtain ⟨_, hf⟩ := (pure_success_iff () () world final).mp h
      subst final
      exact .nil world
    · intro h
      cases h
      rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    constructor
    · intro h
      change (D.setindex! calls address value key >>= fun _ =>
        JuliaLean.base.iddict.insertPairList calls address rest) world =
          some (.ok (), final) at h
      obtain ⟨result, middle, hs, ht⟩ := (bind_success_iff _ _ _ _ _).mp h
      exact .cons hs ((ih middle).mp ht)
    · intro h
      cases h with
      | cons hs ht =>
        change (D.setindex! calls address value key >>= fun _ =>
          JuliaLean.base.iddict.insertPairList calls address rest) world =
            some (.ok (), final)
        exact (bind_success_iff _ _ _ _ _).mpr ⟨_, _, hs, (ih _).mpr ht⟩

/-- Any invariant preserved by successful single insertions is preserved by the
whole pair loop, including all intermediate callback effects. -/
theorem pairInsertionTrace_preserves {calls : D.Callees} {address : Word}
    {pairs : List (Word × Word)} {world final : World}
    (invariant : World → Prop)
    (step : ∀ key value initial middle result, invariant initial →
      D.setindex! calls address value key initial = some (.ok result, middle) →
      invariant middle)
    (trace : PairInsertionTrace calls address pairs world final)
    (initial : invariant world) : invariant final := by
  revert initial
  induction trace with
  | nil => intro initial; exact initial
  | cons run tail ih =>
    intro initial
    exact ih (step _ _ _ _ _ initial run)

/-- A successful pair constructor first allocates, computes its hint, size-hints,
then executes precisely the supplied list in order. -/
theorem fromPairs_success_trace (calls : D.Callees) (keyType valueType : Word)
    (pairs : List (Word × Word)) (world final : World) (result : Word)
    (h : D.fromPairs calls keyType valueType pairs world = some (.ok result, final)) :
    ∃ allocated count measured hinted,
      D.emptyTyped calls keyType valueType world = some (.ok result, allocated) ∧
      calls.lengthArgument pairs.length allocated = some (.ok count, measured) ∧
      (∃ hintResult, D.sizehint! calls result count measured = some (.ok hintResult, hinted)) ∧
      PairInsertionTrace calls result pairs hinted final := by
  unfold JuliaLean.base.iddict.fromPairs at h
  obtain ⟨address, allocated, ha, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨count, measured, hm, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨hintResult, hinted, hh, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨⟨⟩, inserted, hi, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨hr, hf⟩ := (pure_success_iff _ _ _ _).mp h
  subst result
  subst inserted
  exact ⟨allocated, count, measured, hinted, ha, hm, ⟨hintResult, hh⟩,
    (insertPairList_success_iff _ _ _ _ _).mp hi⟩

/-- A finite iterator trace retains the actual outcomes of iteration,
destructuring and insertion, in that order. -/
inductive IteratorInsertionTrace {I S : Type} (calls : D.Callees)
    (iter : D.IteratorCalls I S) (address : Word) (input : I) :
    Option S → World → World → Prop where
  | done {state : Option S} {world final : World}
      (stop : iter.iterate input state world = some (.ok none, final)) :
      IteratorInsertionTrace calls iter address input state world final
  | next {state : Option S} {item key value result : Word} {nextState : S}
      {world yielded destructured inserted final : World}
      (yield : iter.iterate input state world = some (.ok (some (item, nextState)), yielded))
      (pair : iter.destructure item yielded = some (.ok (key, value), destructured))
      (insert : D.setindex! calls address value key destructured = some (.ok result, inserted))
      (tail : IteratorInsertionTrace calls iter address input (some nextState) inserted final) :
      IteratorInsertionTrace calls iter address input state world final

/-- Every finite callback trace executes exactly in the native iterator loop. -/
theorem iteratorInsertionTrace_run {I S : Type} {calls : D.Callees}
    {iter : D.IteratorCalls I S} {address : Word} {input : I}
    {state : Option S} {world final : World}
    (trace : IteratorInsertionTrace calls iter address input state world final) :
    JuliaLean.base.iddict.insertIterator calls iter address input state world =
      some (.ok (), final) := by
  induction trace with
  | done stop =>
    rw [JuliaLean.base.iddict.insertIterator]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, stop]
    rfl
  | next yield pair insert tail ih =>
    rw [JuliaLean.base.iddict.insertIterator]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, yield, pair, insert]
    exact ih

/-- The iterator's size protocol is evaluated after allocation. -/
def iteratorHint {I S : Type} (calls : D.Callees) (iter : D.IteratorCalls I S)
    (address : Word) (input : I) (size : JuliaLean.base.iddict.IteratorSize) : M Unit := do
  if size == .hasLength || size == .hasShape then
    let _ ← D.sizehint! calls address (← iter.length input)
  pure ()

/-- Constructor success exposes the state in which iteration really starts.
A separately sampled stream in the original world need not be this stream. -/
theorem fromIterator_success_trace {I S : Type} (calls : D.Callees)
    (iter : D.IteratorCalls I S) (keyType valueType : Word) (input : I)
    (world final : World) (result : Word)
    (h : D.fromIterator calls iter keyType valueType input world = some (.ok result, final)) :
    ∃ allocated size sized prepared,
      D.emptyTyped calls keyType valueType world = some (.ok result, allocated) ∧
      iter.size input allocated = some (.ok size, sized) ∧
      iteratorHint calls iter result input size sized = some (.ok (), prepared) ∧
      JuliaLean.base.iddict.insertIterator calls iter result input none prepared =
        some (.ok (), final) := by
  unfold JuliaLean.base.iddict.fromIterator at h
  obtain ⟨address, allocated, ha, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨size, sized, hs, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  cases guard : (size == .hasLength || size == .hasShape) with
  | false =>
    simp only [guard, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨⟩, inserted, hi, h⟩ := (bind_success_iff _ _ _ _ _).mp h
    obtain ⟨hr, hf⟩ := (pure_success_iff _ _ _ _).mp h
    subst result
    subst inserted
    refine ⟨allocated, size, sized, sized, ha, hs, ?_, hi⟩
    unfold iteratorHint
    rw [guard]
    rfl
  | true =>
    simp only [guard, ↓reduceIte] at h
    obtain ⟨count, counted, hc, h⟩ := (bind_success_iff _ _ _ _ _).mp h
    obtain ⟨hintResult, prepared, hp, h⟩ := (bind_success_iff _ _ _ _ _).mp h
    obtain ⟨⟨⟩, inserted, hi, h⟩ := (bind_success_iff _ _ _ _ _).mp h
    obtain ⟨hr, hf⟩ := (pure_success_iff _ _ _ _).mp h
    subst result
    subst inserted
    refine ⟨allocated, size, sized, prepared, ha, hs, ?_, hi⟩
    unfold iteratorHint
    rw [guard]
    exact (bind_success_iff _ _ _ _ _).mpr ⟨count, counted, hc,
      (bind_success_iff _ _ _ _ _).mpr ⟨hintResult, prepared, hp, rfl⟩⟩

/-- Copy re-reads source fields after the copy callback. The resulting key/value
parameter tags and counters therefore come from that later world. -/
theorem copyConstruct_success_trace (calls : D.Callees) (address result : Word)
    (world final : World)
    (h : D.copyConstruct calls address world = some (.ok result, final)) :
    ∃ before readWorld memory copied after reread,
      D.dictionary address world = some (.ok before, readWorld) ∧
      calls.copyMemory before.ht readWorld = some (.ok memory, copied) ∧
      D.dictionary address copied = some (.ok after, reread) ∧
      JuliaLean.base.iddict.construct calls after.keyType after.valueType memory
        after.count after.ndel reread = some (.ok result, final) := by
  unfold JuliaLean.base.iddict.copyConstruct at h
  obtain ⟨before, readWorld, hb, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨memory, copied, hm, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  obtain ⟨after, reread, ha, h⟩ := (bind_success_iff _ _ _ _ _).mp h
  exact ⟨before, readWorld, memory, copied, after, reread, hb, hm, ha, h⟩

/-- When all size callbacks retain the input state and request no growth,
sizehint returns with exactly that state, not merely the same address. -/
theorem sizehint_no_growth_run (calls : D.Callees) (address request doubled requested : Word)
    (world : World) (fields : JuliaLean.base.iddict.DictFields)
    (hd : calls.doubleInteger request world = some (.ok doubled, world))
    (ht : calls.tableSize doubled world = some (.ok requested, world))
    (hf : D.dictionary address world = some (.ok fields, world))
    (hc : calls.lessThanInt requested
      (JuliaLean.base.int.ashr_int
        (JInt.wrap .i64 (Int.ofNat fields.ht.length) * JInt.wrap .i64 5)
        (JInt.wrap .i64 2)) world = some (.ok true, world)) :
    D.sizehint! calls address request world = some (.ok address, world) := by
  simp only [JuliaLean.base.iddict.sizehint!, Bind.bind,
    JuliaLean.base.iterators.bind, hd, ht, hf, hc, ↓reduceIte]
  rfl

end JuliaLean.ChatGPT.Batch8.Group5.Early


/-! Exact wrapper laws for callback-sensitive paths. These retain the states
actually reached by native lookup, defaults, conversion and insertion. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.Late
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)

/-- The value-conversion expression with the type captured by the wrapper. -/
def convertAtType (calls : D.Callees) (type value : Word) : M Word := do
  if ← D.isa calls value type then pure value
  else D.assertType calls (← calls.convert type value) type

/-- The reference conversion is this expression after decoding the dictionary. -/
theorem convertedValue_eq (calls : D.Callees) (address value : Word) :
    convertedValue calls address value =
      (do let fields ← D.dictionary address; convertAtType calls fields.valueType value) := rfl

/-- On the already-typed branch no conversion callback runs. -/
theorem convertAtType_typed_run (calls : D.Callees) (type value : Word)
    (world checked : World)
    (h : D.isa calls value type world = some (.ok true, checked)) :
    convertAtType calls type value world = some (.ok value, checked) := by
  simp only [convertAtType, Bind.bind, JuliaLean.base.iterators.bind, h,
    Bool.true_eq, ↓reduceIte]
  rfl

/-- On the conversion branch the assertion runs in the conversion's returned
world, and its returned value is the stored candidate. -/
theorem convertAtType_converted_run (calls : D.Callees) (type value converted : Word)
    (world checked convertedWorld final : World)
    (htype : D.isa calls value type world = some (.ok false, checked))
    (hconvert : calls.convert type value checked = some (.ok converted, convertedWorld))
    (hassert : D.assertType calls converted type convertedWorld = some (.ok converted, final)) :
    convertAtType calls type value world = some (.ok converted, final) := by
  simp only [convertAtType, Bind.bind, JuliaLean.base.iterators.bind,
    htype, Bool.false_eq_true, ↓reduceIte, hconvert, hassert]

/-- A defaulted pop that reports no native deletion returns its fallback in the
native operation's actual final state. It does not call any type assertion. -/
theorem popDefault_missing_run (calls : D.Callees) (address key fallback : Word)
    (world probed : World) (fields : JuliaLean.base.iddict.DictFields) (ignored : Word)
    (hfields : D.dictionary address world = some (.ok fields, world))
    (hpop : JuliaLean.src.iddict_c.jl_eqtable_pop fields.ht key fallback true world =
      some (.ok (ignored, some false), probed)) :
    D.popDefault calls address key fallback world = some (.ok fallback, probed) := by
  simp only [JuliaLean.base.iddict.popDefault, Bind.bind,
    JuliaLean.base.iterators.bind, hfields, hpop]
  rfl

/-- A reported native deletion writes the decremented count, then the increased
deleted-slot count, then checks the returned value's type. -/
theorem popDefault_present_run (calls : D.Callees) (address key fallback value result : Word)
    (world removed counted deleted final : World)
    (fields : JuliaLean.base.iddict.DictFields)
    (hfields : D.dictionary address world = some (.ok fields, world))
    (hpop : JuliaLean.src.iddict_c.jl_eqtable_pop fields.ht key fallback true world =
      some (.ok (value, some true), removed))
    (hcount : JuliaLean.base.iddict.storeIntField address 8
      (fields.count - JInt.wrap .i64 1) removed = some (.ok (), counted))
    (hdeleted : JuliaLean.base.iddict.storeIntField address 16
      (fields.ndel + JInt.wrap .i64 1) counted = some (.ok (), deleted))
    (htype : D.assertType calls value fields.valueType deleted = some (.ok result, final)) :
    D.popDefault calls address key fallback world = some (.ok result, final) := by
  simp only [JuliaLean.base.iddict.popDefault, Bind.bind,
    JuliaLean.base.iterators.bind, hfields, hpop, hcount, hdeleted, htype]

/-- The token branch of pop throws after the defaulted pop, so its state
includes any deletion already performed by that operation. -/
theorem pop_token_run (calls : D.Callees) (address key token : Word)
    (world removed : World)
    (htoken : D.secretToken world = some (.ok token, world))
    (hpop : D.popDefault calls address key token world = some (.ok token, removed)) :
    D.pop calls address key world = some (.error (.keyError key), removed) := by
  simp only [JuliaLean.base.iddict.pop, Bind.bind,
    JuliaLean.base.iterators.bind, htoken, hpop,
    JuliaLean.ChatGPT.Batch4.Group16.iddict_identical_self,
    Bool.true_eq, ↓reduceIte]
  rfl

/-- Successful delete returns the dictionary in precisely the defaulted pop's
final state, whether or not native deletion found an entry. -/
theorem deleteBang_success_run (calls : D.Callees) (address key token value : Word)
    (world deleted : World)
    (htoken : D.secretToken world = some (.ok token, world))
    (hpop : D.popDefault calls address key token world = some (.ok value, deleted)) :
    D.deleteBang calls address key world = some (.ok address, deleted) := by
  simp only [JuliaLean.base.iddict.deleteBang, Bind.bind,
    JuliaLean.base.iterators.bind, htoken, hpop]
  rfl

/-- The inserting branch runs the default after native lookup and inserts only
after conversion. This exposes the worlds omitted by the frozen initial-count
formula without assuming that callbacks retain their input state. -/
theorem callable_getbang_default_run (calls : D.Callees)
    (fallback : Unit → M Word) (address key token rawValue value insertionResult : Word)
    (world probed called converted final : World)
    (fields : JuliaLean.base.iddict.DictFields)
    (hfields : D.dictionary address world = some (.ok fields, world))
    (htoken : D.secretToken world = some (.ok token, world))
    (hget : JuliaLean.src.iddict_c.jl_eqtable_get fields.ht key token world =
      some (.ok token, probed))
    (hdefault : fallback () probed = some (.ok rawValue, called))
    (hconverted : convertAtType calls fields.valueType rawValue called =
      some (.ok value, converted))
    (hinsert : D.setindex! calls address value key converted =
      some (.ok insertionResult, final)) :
    D.getBangCallable calls fallback address key world = some (.ok value, final) := by
  have hc := hconverted
  unfold convertAtType at hc
  obtain ⟨typed, tested, ht, hc⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ called converted value hc
  cases typed with
  | true =>
    change (some (.ok rawValue, tested) : Option (Except Error Word × World)) =
      some (.ok value, converted) at hc
    cases hc
    simp only [JuliaLean.base.iddict.getBangCallable, Bind.bind,
      JuliaLean.base.iterators.bind, hfields, htoken, hget,
      JuliaLean.ChatGPT.Batch4.Group16.iddict_identical_self,
      Bool.true_eq, ↓reduceIte, hdefault, ht, hinsert,
      Pure.pure, JuliaLean.base.iterators.ret]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    obtain ⟨candidate, produced, hproduce, hassert⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ tested converted value hc
    simp only [JuliaLean.base.iddict.getBangCallable, Bind.bind,
      JuliaLean.base.iterators.bind, hfields, htoken, hget,
      JuliaLean.ChatGPT.Batch4.Group16.iddict_identical_self,
      Bool.true_eq, Bool.false_eq_true, ↓reduceIte, hdefault, ht,
      hproduce, hassert, hinsert, Pure.pure, JuliaLean.base.iterators.ret]

end JuliaLean.ChatGPT.Batch8.Group5.Late


/-! Successful insertion traces. These expose the worlds after the key check,
conversion, native insertion, and table publication. They do not replace the
frozen initial-world conversion or counter specification. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.Setindex
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)

/-- The original insertion suffix, entered with the already converted value. -/
def afterConversion (calls : D.Callees) (address key value : Word) : M Word := do
  let fields ← D.dictionary address
  let threshold := JuliaLean.base.int.ashr_int
    (JInt.wrap .i64 3 * JInt.wrap .i64 (Int.ofNat fields.ht.length)) (JInt.wrap .i64 2)
  if fields.ndel.val ≥ threshold.val then
    let half := UInt64.ofNat fields.ht.length >>> 1
    let _ ← D.rehashCsize calls address (if half < 32 then 32 else half)
    JuliaLean.base.iddict.storeIntField address 16 (JInt.wrap .i64 0)
  let fields ← D.dictionary address
  let (memory, inserted) ← JuliaLean.src.iddict_c.jl_eqtable_put calls.gc fields.ht key value true
  match inserted with
  | none => JuliaLean.src.identity_runtime.fail (.abort "jl_eqtable_put omitted requested Cint output")
  | some inserted =>
    JuliaLean.base.iddict.storeHT address memory
    let fields ← D.dictionary address
    JuliaLean.base.iddict.storeIntField address 8
      (fields.count + JInt.wrap .i64 (if inserted then 1 else 0))
    pure address

/-- The final native insertion and publication stages. -/
def nativeInsertion (calls : D.Callees) (address key value : Word) : M Word := do
  let fields ← D.dictionary address
  let (memory, inserted) ← JuliaLean.src.iddict_c.jl_eqtable_put calls.gc fields.ht key value true
  match inserted with
  | none => JuliaLean.src.identity_runtime.fail (.abort "jl_eqtable_put omitted requested Cint output")
  | some inserted =>
    JuliaLean.base.iddict.storeHT address memory
    let fields ← D.dictionary address
    JuliaLean.base.iddict.storeIntField address 8
      (fields.count + JInt.wrap .i64 (if inserted then 1 else 0))
    pure address

/-- The first action after conversion rereads the dictionary without changing
that conversion's returned world. -/
theorem afterConversion_success_reread (calls : D.Callees)
    (address key value result : Word) (world final : World)
    (h : afterConversion calls address key value world = some (.ok result, final)) :
    ∃ current, D.dictionary address world = some (.ok current, world) := by
  unfold afterConversion at h
  obtain ⟨current, reread, hr, _⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  have hrstate := ReadState.preserves_dictionary address world (.ok current) reread hr
  subst reread
  exact ⟨current, hr⟩

/-- Success certifies conversion in the key check's returned world, followed
by a dictionary reread in the conversion's returned world. Each value-type
branch is inspected directly, retaining its actual execution order. -/
theorem success_conversion_prefix (calls : D.Callees)
    (address value key result : Word) (world final : World)
    (h : D.setindex! calls address value key world = some (.ok result, final)) :
    ∃ initial checked stored converted current,
      D.dictionary address world = some (.ok initial, world) ∧
      D.isa calls key initial.keyType world = some (.ok true, checked) ∧
      Late.convertAtType calls initial.valueType value checked = some (.ok stored, converted) ∧
      D.dictionary address converted = some (.ok current, converted) ∧
      afterConversion calls address key stored converted = some (.ok result, final) := by
  unfold JuliaLean.base.iddict.setindex! at h
  obtain ⟨initial, decoded, hd, h⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  have hdstate := ReadState.preserves_dictionary address world (.ok initial) decoded hd
  subst decoded
  obtain ⟨accepted, checked, hk, h⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  cases accepted with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, JuliaLean.src.identity_runtime.fail,
      JuliaLean.base.iterators.fail, Bind.bind, JuliaLean.base.iterators.bind] at h
    cases h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨typed, tested, ht, h⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ checked final result h
    cases typed with
    | true =>
      simp only [Bool.true_eq, ↓reduceIte] at h
      change afterConversion calls address key value tested = some (.ok result, final) at h
      obtain ⟨current, hr⟩ := afterConversion_success_reread calls address key value result tested final h
      have hc := Late.convertAtType_typed_run calls initial.valueType value checked tested ht
      exact ⟨initial, checked, value, tested, current, hd, hk, hc, hr, h⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨convertedWord, convertedWorld, hc, h⟩ :=
        JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ tested final result h
      obtain ⟨stored, asserted, ha, h⟩ :=
        JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ convertedWorld final result h
      have hstored := ReadState.assertType_success_value calls convertedWord initial.valueType
        convertedWorld asserted stored ha
      subst stored
      change afterConversion calls address key convertedWord asserted = some (.ok result, final) at h
      obtain ⟨current, hr⟩ :=
        afterConversion_success_reread calls address key convertedWord result asserted final h
      have hconversion := Late.convertAtType_converted_run calls initial.valueType value convertedWord
        checked tested convertedWorld asserted ht hc ha
      exact ⟨initial, checked, convertedWord, asserted, current, hd, hk, hconversion, hr, h⟩

/-- Publication rereads the dictionary before computing the count update;
the native insertion flag is retained explicitly. -/
theorem nativeInsertion_success_count_trace (calls : D.Callees)
    (address key value result : Word) (world final : World)
    (h : nativeInsertion calls address key value world = some (.ok result, final)) :
    result = address ∧ ∃ nativeFields memory inserted putWorld published beforeCount,
      D.dictionary address world = some (.ok nativeFields, world) ∧
      JuliaLean.src.iddict_c.jl_eqtable_put calls.gc nativeFields.ht key value true world =
        some (.ok (memory, some inserted), putWorld) ∧
      JuliaLean.base.iddict.storeHT address memory putWorld = some (.ok (), published) ∧
      D.dictionary address published = some (.ok beforeCount, published) ∧
      JuliaLean.base.iddict.storeIntField address 8
        (beforeCount.count + JInt.wrap .i64 (if inserted then 1 else 0)) published =
          some (.ok (), final) := by
  unfold nativeInsertion at h
  obtain ⟨nativeFields, decoded, hn, h⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  have hnstate := ReadState.preserves_dictionary address world (.ok nativeFields) decoded hn
  subst decoded
  obtain ⟨⟨memory, reported⟩, putWorld, hp, h⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  cases reported with
  | none =>
    change (some (.error (.abort "jl_eqtable_put omitted requested Cint output"), putWorld) :
      Option (Except Error Word × World)) = some (.ok result, final) at h
    cases h
  | some inserted =>
    obtain ⟨⟨⟩, published, hs, h⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ putWorld final result h
    obtain ⟨beforeCount, counted, hc, h⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ published final result h
    have hcstate := ReadState.preserves_dictionary address published (.ok beforeCount) counted hc
    subst counted
    obtain ⟨⟨⟩, written, hw, h⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ published final result h
    change (some (.ok address, written) : Option (Except Error Word × World)) =
      some (.ok result, final) at h
    cases h
    exact ⟨rfl, nativeFields, memory, inserted, putWorld, published, beforeCount, hn, hp, hs, hc, hw⟩

/-- Both cleanup branches reach the same final insertion sequence. The final
count is computed from a post-publication reread, rather than an assumed
unchanged initial counter. -/
theorem afterConversion_success_count_trace (calls : D.Callees)
    (address key value result : Word) (world final : World)
    (h : afterConversion calls address key value world = some (.ok result, final)) :
    result = address ∧ ∃ nativeWorld nativeFields memory inserted putWorld published beforeCount,
      D.dictionary address nativeWorld = some (.ok nativeFields, nativeWorld) ∧
      JuliaLean.src.iddict_c.jl_eqtable_put calls.gc nativeFields.ht key value true nativeWorld =
        some (.ok (memory, some inserted), putWorld) ∧
      JuliaLean.base.iddict.storeHT address memory putWorld = some (.ok (), published) ∧
      D.dictionary address published = some (.ok beforeCount, published) ∧
      JuliaLean.base.iddict.storeIntField address 8
        (beforeCount.count + JInt.wrap .i64 (if inserted then 1 else 0)) published =
          some (.ok (), final) := by
  suffices handoff : ∃ nativeWorld,
      nativeInsertion calls address key value nativeWorld = some (.ok result, final) by
    obtain ⟨nativeWorld, hrun⟩ := handoff
    obtain ⟨hresult, nativeFields, memory, inserted, putWorld, published, beforeCount,
      hfields, hput, hstore, hreread, hcount⟩ :=
      nativeInsertion_success_count_trace calls address key value result nativeWorld final hrun
    exact ⟨hresult, nativeWorld, nativeFields, memory, inserted, putWorld, published,
      beforeCount, hfields, hput, hstore, hreread, hcount⟩
  unfold afterConversion at h
  obtain ⟨initial, readWorld, _, h⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ world final result h
  by_cases cleanup : initial.ndel.val ≥
      (JuliaLean.base.int.ashr_int
        (JInt.wrap .i64 3 * JInt.wrap .i64 (Int.ofNat initial.ht.length))
        (JInt.wrap .i64 2)).val
  · simp only [cleanup, ↓reduceIte] at h
    obtain ⟨ignored, rehashed, _, h⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ readWorld final result h
    obtain ⟨⟨⟩, cleared, _, h⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ rehashed final result h
    change nativeInsertion calls address key value cleared = some (.ok result, final) at h
    exact ⟨cleared, h⟩
  · simp only [cleanup, ↓reduceIte] at h
    change nativeInsertion calls address key value readWorld = some (.ok result, final) at h
    exact ⟨readWorld, h⟩

/-- The return-address conjunct of the frozen setindex contract holds without
any callback-state or native-table correctness premise. -/
theorem success_returns_address (calls : D.Callees)
    (address value key result : Word) (world final : World)
    (h : D.setindex! calls address value key world = some (.ok result, final)) :
    result = address := by
  obtain ⟨initial, checked, stored, converted, current, _, _, _, _, hsuffix⟩ :=
    success_conversion_prefix calls address value key result world final h
  exact (afterConversion_success_count_trace calls address key stored result converted final hsuffix).1

end JuliaLean.ChatGPT.Batch8.Group5.Setindex


/-! Counter facts obtained from the frozen physical invariant. These isolate the
bounded-integer part of the deletion contract from native table correspondence. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.Counters
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World M Error)

/-- A successful reference lookup returning a value requires a nonempty table. -/
theorem lookup_some_nonempty (pairs : List (Word × Word)) (key value : Word)
    (world : World) (h : succeeds (referenceLookup pairs key) world (some value)) :
    pairs ≠ [] := by
  intro hempty
  subst pairs
  obtain ⟨final, h⟩ := h
  change (some (.ok none, world) : Option (Except Error (Option Word) × World)) =
    some (.ok (some value), final) at h
  cases h

/-- The actual live counter is positive whenever the independent reference
lookup finds a key. No native-table lookup assumption is required. -/
theorem present_count_positive (world : World) (address key value : Word)
    (before : JuliaLean.base.iddict.DictFields)
    (hinvariant : dictInvariant world address)
    (hfields : succeeds (D.dictionary address) world before)
    (hlookup : lookupValue world address key (some value)) :
    0 < before.count.val := by
  obtain ⟨fields, pairs, hf, hp, _, _, _, _, _, _, _, _, _, hc, _, _, _⟩ := hinvariant
  have hfeq := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hf hfields
  subst fields
  obtain ⟨actual, ha, hr⟩ := hlookup
  have hpeq := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hp ha
  subst actual
  have hn := lookup_some_nonempty pairs key value world hr
  cases pairs with
  | nil => exact False.elim (hn rfl)
  | cons head tail =>
    rw [hc]
    apply Int.natCast_pos.mpr
    exact Nat.succ_pos tail.length

/-- Valid dictionary counters are nonnegative and together stay well below the
Int64 boundary, independently of whether the queried key is present. -/
theorem invariant_counter_bounds (world : World) (address : Word)
    (before : JuliaLean.base.iddict.DictFields)
    (hinvariant : dictInvariant world address)
    (hfields : succeeds (D.dictionary address) world before) :
    0 ≤ before.count.val ∧ 0 ≤ before.ndel.val ∧
      before.count.val + before.ndel.val < (2 ^ 61 : Int) := by
  obtain ⟨fields, pairs, hf, _, _, hlen, _, _, _, _, hc, hn, hsum, _⟩ := hinvariant
  have hfeq := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hf hfields
  subst fields
  refine ⟨hc, hn, ?_⟩
  have hhalf : before.ht.length / 2 ≤ before.ht.length := Nat.div_le_self _ _
  have hhalfInt : Int.ofNat (before.ht.length / 2) ≤ Int.ofNat before.ht.length :=
    Int.ofNat_le.mpr hhalf
  have hlenInt : Int.ofNat before.ht.length < (2 ^ 61 : Int) :=
    Int.ofNat_lt.mpr hlen
  exact Int.lt_of_le_of_lt (Int.le_trans hsum hhalfInt) hlenInt

/-- The model's two machine-integer counter updates agree with mathematical
subtraction/addition on a valid table from which a present key is removed. -/
theorem present_counter_updates (world : World) (address key value : Word)
    (before : JuliaLean.base.iddict.DictFields)
    (hinvariant : dictInvariant world address)
    (hfields : succeeds (D.dictionary address) world before)
    (hlookup : lookupValue world address key (some value)) :
    (before.count - JInt.wrap .i64 1).val = before.count.val - 1 ∧
      (before.ndel + JInt.wrap .i64 1).val = before.ndel.val + 1 := by
  have hc := present_count_positive world address key value before hinvariant hfields hlookup
  obtain ⟨_, hn, hsum⟩ := invariant_counter_bounds world address before hinvariant hfields
  have hone : (JInt.wrap .i64 1).val = 1 := rfl
  constructor
  · change wrapInt .i64 (before.count.val - (JInt.wrap .i64 1).val) = before.count.val - 1
    rw [hone]
    apply wrapInt_of_inRange
    change (-9223372036854775808 : Int) ≤ before.count.val - 1 ∧
      before.count.val - 1 ≤ 9223372036854775807
    omega
  · change wrapInt .i64 (before.ndel.val + (JInt.wrap .i64 1).val) = before.ndel.val + 1
    rw [hone]
    apply wrapInt_of_inRange
    change (-9223372036854775808 : Int) ≤ before.ndel.val + 1 ∧
      before.ndel.val + 1 ≤ 9223372036854775807
    omega

end JuliaLean.ChatGPT.Batch8.Group5.Counters


/-! Native one-entry IdDict witness and finite read/scan helpers. -/

namespace JuliaLean.ChatGPT.Batch8.Group5
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)

namespace IdToken
open JuliaLean.src.identity_runtime
open JuliaLean.base.iddict

/-- Addresses encode a finite one-entry IdDict; key and value denote the public
Symbol whose name is the table token. -/
def memory : Memory :=
  { ptr := 1024, length := 32,
    metadata := { JuliaLean.src.genericmemory_c.boxedDictLayout.metadata with owner := 512 } }

def datatype : Datatype :=
  { name := 2056, hash := 1, parameters := 1536, isMutable := true,
    isAbstract := false, isConcrete := true, size := 24, bits := 192,
    hasPadding := false, isBitsEgal := false, firstPointer := 0,
    fields := [], pointerOffsets := [0] }

def storedWord (slot : Nat) : Word :=
  if slot = 7 then 288 else
  if slot = 39 then 288 else
  if slot = 23 then 416 else
  if slot = 31 then 2048 else
  if slot = 32 then 512 else
  if slot = 33 then 1 else
  if slot = 150 then 64 else
  if slot = 151 then 64 else
  if slot = 193 then 4096 else
  if slot = 194 then 4096 else 0

def heap : JuliaLean.base.pointer.ByteHeap :=
  { byteAt := fun address =>
      JInt.wrap .u8 (((storedWord (address / 8)) >>> UInt64.ofNat (8 * (address % 8))).toNat % 256),
    validByte := fun address => decide (8 ≤ address ∧ address < 8192) }

def world : World :=
  { raw := { heap := heap },
    objects := fun address => if address == 64 then some { hash := 104215988381347979 }
      else if address == 320 then some { hash := 3099839820305488312 } else none,
    datatypes := fun address => if address == 2048 then some datatype else none,
    typenameHashes := fun _ => none,
    smallTypes := fun _ => none,
    internedSymbols := fun text =>
      if text == "__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__" then some 64 else none,
    globals :=
      { nothing := 192
        anyType := 4096
        tupleTypename := 0
        typenameType := 0
        emptyMemory := memory },
    memories := fun address => if address == 512 then some memory else none }

def fields : DictFields :=
  { ht := memory, count := JInt.wrap .i64 1, ndel := JInt.wrap .i64 0,
    keyType := 4096, valueType := 4096 }

def calls : Callees :=
  { gc := { allocateBoxedMemory := fun _ => fail (.abort "unused") },
    newObject := fun _ _ _ _ _ => fail (.abort "unused"),
    copyMemory := fun _ => fail (.abort "unused"),
    isa := fun _ _ => fail (.abort "unused"),
    convert := fun _ _ => fail (.abort "unused"),
    toCsize := fun _ => fail (.abort "unused"),
    doubleInteger := fun _ => fail (.abort "unused"),
    tableSize := fun _ => fail (.abort "unused"),
    lessThanInt := fun _ _ => fail (.abort "unused"),
    lengthArgument := fun _ => fail (.abort "unused"),
    newPair := fun _ _ _ _ => fail (.abort "unused"),
    filterInOnePass := fun _ _ => fail (.abort "unused") }


def withEvents (events : List Event) : World := { world with events := events }

theorem load_word_from_scalars (w : World) (address value : Word)
    (hnonzero : address ≠ 0)
    (hread : readableRange w.raw.heap address.toNat 8 = true)
    (hvalue : JuliaLean.src.support.hashing_c.load64 w.raw.heap address.toNat = value) :
    loadWord address w = some (.ok value, w) := by
  simp only [loadWord, requireReadable, getWorld, Bind.bind, JuliaLean.base.iterators.bind,
    hnonzero, hread, Bool.not_true, Bool.or_false, decide_false, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret, hvalue]

theorem load_dictionary_pointer (events : List Event) :
    loadWord 256 (withEvents events) = some (.ok 512, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_dictionary_tag (events : List Event) :
    loadWord 248 (withEvents events) = some (.ok 2048, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_keytype (events : List Event) :
    loadWord 1544 (withEvents events) = some (.ok 4096, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_valuetype (events : List Event) :
    loadWord 1552 (withEvents events) = some (.ok 4096, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_count (events : List Event) :
    loadWord 264 (withEvents events) = some (.ok 1, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_ndel (events : List Event) :
    loadWord 272 (withEvents events) = some (.ok 0, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_symbol_tag (events : List Event) :
    loadWord 56 (withEvents events) = some (.ok 288, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem load_nothing_tag (events : List Event) :
    loadWord 184 (withEvents events) = some (.ok 416, withEvents events) := by
  apply load_word_from_scalars
  · decide
  · change readableRange heap _ 8 = true
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · change JuliaLean.src.support.hashing_c.load64 heap _ = _
    simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide

theorem dictionary_run (events : List Event) :
    dictionary 256 (withEvents events) = some (.ok fields, withEvents events) := by
  have htag : typetag 256 (withEvents events) = some (.ok 2048, withEvents events) := by
    change (loadWord 248 >>= fun tag => pure (tag &&& ~~~(15 : Word)))
      (withEvents events) = _
    simp only [Bind.bind, JuliaLean.base.iterators.bind, load_dictionary_tag]
    rfl
  have htype : typeof 256 (withEvents events) = some (.ok 2048, withEvents events) := by
    simp only [typeof, Bind.bind, JuliaLean.base.iterators.bind, htag]
    rfl
  have hm : (withEvents events).memories 512 = some memory := rfl
  have hdt : datatypeAt 2048 (withEvents events) = some (.ok datatype, withEvents events) := by rfl
  simp only [dictionary, Bind.bind, JuliaLean.base.iterators.bind, load_dictionary_pointer,
    getWorld, hm, Pure.pure, JuliaLean.base.iterators.ret, htype, hdt,
    show datatype.parameters + 8 = (1544 : Word) from rfl,
    show datatype.parameters + 16 = (1552 : Word) from rfl,
    show (256 + 8 : Word) = 264 from rfl,
    show (256 + 16 : Word) = 272 from rfl,
    load_keytype, load_valuetype, load_count, load_ndel]
  rfl

theorem token_run (events : List Event) :
    secretToken (withEvents events) = some (.ok 64, withEvents events) := by
  rfl

theorem length_run (events : List Event) :
    JuliaLean.base.iddict.length 256 (withEvents events) =
      some (.ok (JInt.wrap .i64 1), withEvents events) := by
  simp only [JuliaLean.base.iddict.length, Bind.bind,
    JuliaLean.base.iterators.bind, dictionary_run]
  rfl

theorem hash_run (events : List Event) :
    JuliaLean.src.builtins_identity_c.jl_object_id 64 (withEvents events) =
      some (.ok 104215988381347979, withEvents events) := by
  rw [JuliaLean.src.builtins_identity_c.jl_object_id]
  have htag : typetag 64 (withEvents events) = some (.ok 288, withEvents events) := by
    change (loadWord 56 >>= fun tag => pure (tag &&& ~~~(15 : Word)))
      (withEvents events) = _
    simp only [Bind.bind, JuliaLean.base.iterators.bind, load_symbol_tag]
    rfl
  simp only [Bind.bind, JuliaLean.base.iterators.bind, htag]
  rw [JuliaLean.src.builtins_identity_c.jl_object_id_]
  rfl

theorem cell_run (events : List Event) (i : Nat) (hi : i < 32) :
    plainReadCell memory (UInt64.ofNat i) (withEvents events) =
      some (.ok (if i = 22 ∨ i = 23 then 64 else 0), withEvents events) := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases cases_i with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst i
    change loadWord _ _ = _
    apply load_word_from_scalars
    · decide
    · change readableRange heap _ 8 = true
      simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
      decide
    · change JuliaLean.src.support.hashing_c.load64 heap _ = _
      simp only [JuliaLean.src.support.hashing_c.load64,
        Std.Legacy.Range.forIn_eq_forIn_range']
      decide

end IdToken
end JuliaLean.ChatGPT.Batch8.Group5

/- The physical cell scan and invariant. -/

namespace JuliaLean.ChatGPT.Batch8.Group5.IdToken
open JuliaLean JuliaLean.Proofs.base.iddict JuliaLean.src.identity_runtime
open JuliaLean.base.iddict

/-- A finite loop whose body preserves the world can be checked one step at a time. -/
theorem forIn_yield_at {A B : Type} (step : A → B → M (ForInStep B))
    (update : A → B → B) (w : World) (items : List A) (initial : B)
    (hstep : ∀ item ∈ items, ∀ state,
      step item state w = some (.ok (.yield (update item state)), w)) :
    (forIn items initial step) w =
      some (.ok (items.foldl (fun state item => update item state) initial), w) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    have hhead := hstep item (show item ∈ item :: rest from List.mem_cons_self) initial
    rw [List.forIn_cons]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, hhead, List.foldl_cons]
    exact ih (update item initial) (fun next hnext state =>
      hstep next (List.mem_cons_of_mem item hnext) state)

def scanStep (index : Nat) (pairs : List (Word × Word)) : M (ForInStep (List (Word × Word))) := do
  let value ← plainReadCell memory (UInt64.ofNat (2*index+1))
  if value != 0 then
    let key ← plainReadCell memory (UInt64.ofNat (2*index))
    pure (.yield (pairs ++ [(key, value)]))
  else pure (.yield pairs)

def scanUpdate (index : Nat) (pairs : List (Word × Word)) : List (Word × Word) :=
  if index = 11 then pairs ++ [(64, 64)] else pairs

theorem scanStep_run (events : List Event) (index : Nat) (hindex : index < 16)
    (pairs : List (Word × Word)) :
    scanStep index pairs (withEvents events) =
      some (.ok (.yield (scanUpdate index pairs)), withEvents events) := by
  by_cases hit : index = 11
  · subst index
    have hv : plainReadCell memory 23 (withEvents events) =
        some (.ok 64, withEvents events) := cell_run events 23 (by decide)
    have hk : plainReadCell memory 22 (withEvents events) =
        some (.ok 64, withEvents events) := cell_run events 22 (by decide)
    simp only [scanStep, scanUpdate, Nat.reduceMul, Nat.reduceAdd, UInt64.reduceOfNat,
      Bind.bind, JuliaLean.base.iterators.bind, hv, hk,
      show ((64 : Word) != 0) = true from rfl, Bool.true_eq, ↓reduceIte]
    rfl
  · have hempty : ¬ (2 * index + 1 = 22 ∨ 2 * index + 1 = 23) := by omega
    have hv := cell_run events (2*index+1) (by omega)
    rw [if_neg hempty] at hv
    simp only [scanStep, scanUpdate, hit, Bind.bind, JuliaLean.base.iterators.bind, hv,
      show ((0 : Word) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem livePairs_run (events : List Event) :
    livePairs memory (withEvents events) = some (.ok [(64, 64)], withEvents events) := by
  have hsize : memory.length / 2 = 16 := by decide
  have hscan := forIn_yield_at scanStep scanUpdate (withEvents events)
    (List.range (memory.length / 2)) [] (fun index hindex pairs => by
      have hbound : index < memory.length / 2 :=
        (List.mem_range (m := index) (n := memory.length / 2)).mp hindex
      rw [hsize] at hbound
      exact scanStep_run events index hbound pairs)
  have hfold : (List.range (memory.length / 2)).foldl
      (fun state index => scanUpdate index state) [] = [(64, 64)] := by
    rw [hsize]
    decide
  rw [hfold] at hscan
  change ((forIn (List.range (memory.length / 2)) [] scanStep) >>= fun pairs => pure pairs)
    (withEvents events) = _
  simp only [Bind.bind, JuliaLean.base.iterators.bind, hscan]
  rfl

theorem contents_run (events : List Event) :
    contents 256 (withEvents events) = some (.ok [(64, 64)], withEvents events) := by
  simp only [contents, Bind.bind, JuliaLean.base.iterators.bind, dictionary_run]
  exact livePairs_run events

theorem reference_run (events : List Event) :
    referenceLookup [(64, 64)] 64 (withEvents events) =
      some (.ok (some 64), withEvents events) := by
  simp only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind,
    JuliaLean.ChatGPT.Batch4.Group16.iddict_identical_self, Bool.true_eq, ↓reduceIte]
  all_goals rfl

theorem present : lookupValue world 256 64 (some 64) := by
  exact ⟨[(64, 64)], ⟨world, contents_run []⟩, ⟨world, reference_run []⟩⟩

theorem token_valid : validValue world 64 := by
  exact ⟨by decide, 104215988381347979, world, hash_run []⟩

theorem token_loaded : loadedToken world := by
  exact ⟨64, ⟨world, token_run []⟩, token_valid⟩

theorem placement : tablePlacement world memory := by
  intro index hindex key value hkey hvalue
  change index < 16 at hindex
  by_cases hwhere : index = 11
  · subst index
    have hk : key = 64 := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hkey
      ⟨world, cell_run [] 22 (by decide)⟩
    have hv : value = 64 := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hvalue
      ⟨world, cell_run [] 23 (by decide)⟩
    subst key
    subst value
    constructor
    · intro hz
      exact False.elim ((by decide : (64 : Word) ≠ 0) hz)
    · intro _
      refine ⟨104215988381347979, 0, ⟨world, hash_run []⟩,
        by decide, by decide, by decide, ?_⟩
      intro step hstep
      omega
  · have hkempty : ¬ (2 * index = 22 ∨ 2 * index = 23) := by omega
    have hvempty : ¬ (2 * index + 1 = 22 ∨ 2 * index + 1 = 23) := by omega
    have hkrun := cell_run [] (2 * index) (by omega)
    have hvrun := cell_run [] (2 * index + 1) (by omega)
    rw [if_neg hkempty] at hkrun
    rw [if_neg hvempty] at hvrun
    have hk : key = 0 := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hkey ⟨world, hkrun⟩
    have hv : value = 0 := JuliaLean.ChatGPT.Batch4.Group16.iddict_succeeds_unique _ _ hvalue ⟨world, hvrun⟩
    subst key
    subst value
    exact ⟨fun _ => Or.inl rfl, fun h => False.elim (h rfl)⟩

theorem invariant : dictInvariant world 256 := by
  refine ⟨fields, [(64, 64)], ⟨world, dictionary_run []⟩,
    ⟨world, contents_run []⟩, by decide, by decide, ⟨5, rfl⟩,
    rfl, by decide, ?_, by decide, by decide, by decide, rfl, ?_, ?_, placement⟩
  · intro offset hoff
    change offset < 256 at hoff
    change decide (8 ≤ 1024 + offset ∧ 1024 + offset < 8192) = true
    simp only [decide_eq_true_eq]
    omega
  · constructor
    · intro pair hp
      cases hp
    · trivial
  · intro pair hp
    have heq : pair = (64, 64) := List.mem_singleton.mp hp
    subst pair
    exact ⟨token_valid, token_valid⟩


/-- The sentinel witness also satisfies the supplied stronger native
representation predicate: its table pointer is nonzero and Nothing has tag 26. -/
theorem native_representation : NativeRepresentation world 256 := by
  constructor
  · exact ⟨fields, ⟨world, dictionary_run []⟩, by decide⟩
  · refine ⟨world, ?_⟩
    change (loadWord 184 >>= fun tag => pure (tag &&& ~~~(15 : Word))) world = _
    simp only [Bind.bind, JuliaLean.base.iterators.bind, show world = withEvents [] from rfl,
      load_nothing_tag]
    rfl

end JuliaLean.ChatGPT.Batch8.Group5.IdToken

/- Native first-probe lookup trace. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.IdToken
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime
open JuliaLean.src.iddict_c

/-- The occupied key cell is the ordinary byte read at address 1200. -/
theorem load_key_run (events : List Event) :
    loadWord 1200 (withEvents events) = some (.ok 64, withEvents events) := by
  have h := cell_run events 22 (by decide)
  change loadWord 1200 (withEvents events) = some (.ok 64, withEvents events) at h
  exact h

/-- The occupied value cell is the ordinary byte read at address 1208. -/
theorem load_value_run (events : List Event) :
    loadWord 1208 (withEvents events) = some (.ok 64, withEvents events) := by
  have h := cell_run events 23 (by decide)
  change loadWord 1208 (withEvents events) = some (.ok 64, withEvents events) at h
  exact h

/-- Atomic key reads append exactly their native load event. -/
theorem atomic_key_run (events : List Event) :
    atomicLoad 1200 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1200 64])) := by
  simp only [atomicLoad, Bind.bind, JuliaLean.base.iterators.bind, load_key_run]
  rfl

/-- Atomic value reads append exactly their native load event. -/
theorem atomic_value_run (events : List Event) :
    atomicLoad 1208 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1208 64])) := by
  simp only [atomicLoad, Bind.bind, JuliaLean.base.iterators.bind, load_value_run]
  rfl

theorem read_key_run (events : List Event) :
    readCell memory 22 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1200 64])) := by
  change atomicLoad 1200 (withEvents events) = _
  exact atomic_key_run events

theorem read_value_run (events : List Event) :
    readCell memory 23 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1208 64])) := by
  change atomicLoad 1208 (withEvents events) = _
  exact atomic_value_run events

/-- The C keyhash wrapper has the same exact execution as native objectid. -/
theorem keyhash_run (events : List Event) :
    keyhash 64 (withEvents events) =
      some (.ok 104215988381347979, withEvents events) := by
  have h := hash_run events
  rw [JuliaLean.src.builtins_identity_c.jl_object_id] at h
  exact h

/-- The first probe sees the stored Symbol and returns its value-cell pointer. -/
theorem peek_loop_run (events : List Event) :
    peekLoop memory 64 32 16 22 22 0 (withEvents events) =
      some (.ok 1208, withEvents (events ++ [.load 1200 64, .load 1208 64])) := by
  rw [peekLoop]
  simp only [Bind.bind, JuliaLean.base.iterators.bind, read_key_run, show (22 + 1 : Word) = 23 from rfl,
    show ((64 : Word) == 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, JuliaLean.ChatGPT.Batch4.Group16.iddict_identical_self,
    read_value_run, show ((64 : Word) != 0) = true from rfl,
    Pure.pure, JuliaLean.base.iterators.ret, List.append_assoc]
  rfl

/-- The actual Symbol hash selects the occupied bucket at position 22. -/
theorem peek_run (events : List Event) :
    jl_table_peek_bp memory 64 (withEvents events) =
      some (.ok 1208, withEvents (events ++ [.load 1200 64, .load 1208 64])) := by
  unfold jl_table_peek_bp
  change (keyhash 64 >>= fun hash =>
    peekLoop memory 64 32 16 (h2index hash 16) (h2index hash 16) 0)
    (withEvents events) = _
  simp only [Bind.bind, JuliaLean.base.iterators.bind, keyhash_run]
  change peekLoop memory 64 32 16 22 22 0 (withEvents events) = _
  exact peek_loop_run events

/-- C lookup loads and returns the user-stored Symbol even when it equals its default. -/
theorem table_get_run (events : List Event) (fallback : Word) :
    jl_eqtable_get memory 64 fallback (withEvents events) =
      some (.ok 64, withEvents (events ++
        [.load 1200 64, .load 1208 64, .load 1208 64])) := by
  simp only [jl_eqtable_get, Bind.bind, JuliaLean.base.iterators.bind, peek_run,
    show ((1208 : Word) == 0) = false from rfl, Bool.false_eq_true,
    ↓reduceIte, atomic_value_run, List.append_assoc]
  rfl

end JuliaLean.ChatGPT.Batch8.Group5.IdToken


/-! Empty-table scans and read-only table frames. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.TableScan
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M)

/-- The actual cell-scan body, with backing memory left arbitrary. -/
def scanStep (memory : Memory) (index : Nat) (pairs : List (Word × Word)) :
    M (ForInStep (List (Word × Word))) := do
  let value ← N.plainReadCell memory (UInt64.ofNat (2 * index + 1))
  if value != 0 then
    let key ← N.plainReadCell memory (UInt64.ofNat (2 * index))
    pure (.yield (pairs ++ [(key, value)]))
  else pure (.yield pairs)

/-- A zero value cell skips its key cell and preserves the accumulated pairs. -/
theorem scanStep_zero (memory : Memory) (world : World) (index : Nat)
    (pairs : List (Word × Word))
    (hzero : N.plainReadCell memory (UInt64.ofNat (2 * index + 1)) world =
      some (.ok 0, world)) :
    scanStep memory index pairs world = some (.ok (.yield pairs), world) := by
  simp only [scanStep, Bind.bind, JuliaLean.base.iterators.bind, hzero,
    show ((0 : Word) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Zero value cells imply an empty scan. No key-cell assumptions, allocation
contracts or identity/hash assumptions are needed. -/
theorem livePairs_empty_of_zero (memory : Memory) (world : World)
    (hzero : ∀ index < memory.length / 2,
      N.plainReadCell memory (UInt64.ofNat (2 * index + 1)) world =
        some (.ok 0, world)) :
    livePairs memory world = some (.ok [], world) := by
  have hscan := IdToken.forIn_yield_at (scanStep memory)
    (fun _ pairs => pairs) world (List.range (memory.length / 2)) []
    (fun index hindex pairs =>
      scanStep_zero memory world index pairs (hzero index (List.mem_range.mp hindex)))
  have hfold : ∀ indices : List Nat,
      indices.foldl (fun (pairs : List (Word × Word)) _ => pairs) [] = [] := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index rest ih => exact ih
  rw [hfold] at hscan
  change ((forIn (List.range (memory.length / 2)) [] (scanStep memory)) >>=
    fun pairs => pure pairs) world = _
  simp only [Bind.bind, JuliaLean.base.iterators.bind, hscan]
  rfl

/-- A successful field decode plus zero value cells establishes actual empty
contents through the installed decoder and scan. -/
theorem contents_empty_of_zero (address : Word) (world : World)
    (fields : JuliaLean.base.iddict.DictFields)
    (hdecoded : D.dictionary address world = some (.ok fields, world))
    (hzero : ∀ index < fields.ht.length / 2,
      N.plainReadCell fields.ht (UInt64.ofNat (2 * index + 1)) world =
        some (.ok 0, world)) :
    contents address world = some (.ok [], world) := by
  simp only [contents, Bind.bind, JuliaLean.base.iterators.bind, hdecoded]
  exact livePairs_empty_of_zero fields.ht world hzero

/-- The complete semantic empty shape follows once the field-write frame and
allocator proofs provide the decoder, length and counter facts. -/
theorem emptyShape_of_zero (address : Word) (world : World)
    (fields : JuliaLean.base.iddict.DictFields)
    (hdecoded : D.dictionary address world = some (.ok fields, world))
    (hsize : fields.ht.length = 32) (hcount : fields.count.val = 0)
    (hdeleted : fields.ndel.val = 0)
    (hzero : ∀ index < fields.ht.length / 2,
      N.plainReadCell fields.ht (UInt64.ofNat (2 * index + 1)) world =
        some (.ok 0, world)) :
    emptyShape world address := by
  exact ⟨fields, ⟨world, hdecoded⟩, hsize, hcount, hdeleted,
    ⟨world, contents_empty_of_zero address world fields hdecoded hzero⟩⟩

/-- The empty scan establishes absence for every query key, without evaluating
native key identity or key hashes. -/
theorem lookupValue_none_of_zero (address key : Word) (world : World)
    (fields : JuliaLean.base.iddict.DictFields)
    (hdecoded : D.dictionary address world = some (.ok fields, world))
    (hzero : ∀ index < fields.ht.length / 2,
      N.plainReadCell fields.ht (UInt64.ofNat (2 * index + 1)) world =
        some (.ok 0, world)) :
    lookupValue world address key none := by
  exact ⟨[], ⟨world, contents_empty_of_zero address world fields hdecoded hzero⟩,
    ⟨world, rfl⟩⟩

/-- Plain cell reads preserve the world, including bounds/readability failures. -/
theorem preserves_plainReadCell (memory : Memory) (index : Word) :
    ReadState.PreservesWorld (N.plainReadCell memory index) := by
  unfold JuliaLean.src.identity_runtime.plainReadCell
  split
  · exact ReadState.preserves_fail _
  · exact ReadState.preserves_loadWord _

/-- Finite-loop world preservation handles both early termination and yielding,
as well as exceptions propagated from the body. -/
theorem preserves_forIn {A B : Type} (step : A → B → M (ForInStep B))
    (hstep : ∀ item state, ReadState.PreservesWorld (step item state))
    (items : List A) (initial : B) :
    ReadState.PreservesWorld (forIn items initial step) := by
  induction items generalizing initial with
  | nil => exact ReadState.preserves_pure initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply ReadState.preserves_bind _ _ (hstep item initial)
    intro next
    cases next with
    | done state => exact ReadState.preserves_pure state
    | yield state => exact ih state

/-- Each scan step is a composition of plain reads and pure returns. -/
theorem preserves_scanStep (memory : Memory) (index : Nat)
    (pairs : List (Word × Word)) :
    ReadState.PreservesWorld (scanStep memory index pairs) := by
  unfold scanStep
  apply ReadState.preserves_bind _ _
    (preserves_plainReadCell memory (UInt64.ofNat (2 * index + 1)))
  intro value
  split
  · apply ReadState.preserves_bind _ _
      (preserves_plainReadCell memory (UInt64.ofNat (2 * index)))
    intro key
    exact ReadState.preserves_pure _
  · exact ReadState.preserves_pure _

/-- The complete table scan preserves the world on every completed execution. -/
theorem preserves_livePairs (memory : Memory) :
    ReadState.PreservesWorld (livePairs memory) := by
  change ReadState.PreservesWorld
    ((forIn (List.range (memory.length / 2)) [] (scanStep memory)) >>=
      fun pairs => pure pairs)
  apply ReadState.preserves_bind _ _
    (preserves_forIn (scanStep memory) (preserves_scanStep memory) _ _)
  intro pairs
  exact ReadState.preserves_pure pairs

/-- Dictionary contents combine the already-checked decoder frame with the
finite table-scan frame; no callback law is needed. -/
theorem preserves_contents (address : Word) :
    ReadState.PreservesWorld (contents address) := by
  unfold contents
  apply ReadState.preserves_bind _ _ (ReadState.preserves_dictionary address)
  intro fields
  exact preserves_livePairs fields.ht

end JuliaLean.ChatGPT.Batch8.Group5.TableScan


/-! Byte-write frames and zero-fill decoding. No allocator law is used. -/
namespace JuliaLean.ChatGPT.Batch8.Group5.ByteWrite
open JuliaLean JuliaLean.base.pointer
open JuliaLean.src.identity_runtime (Word World Memory)

/-- The explicit bound prevents reduction modulo the address width. -/
theorem addressMod_lt (address : Nat) (h : address < 2 ^ 64) :
    addressMod address = address := Nat.mod_eq_of_lt h

/-- Byte stores preserve the accessibility predicate at every address. -/
theorem writeBytes_validByte (heap : ByteHeap) (base : Nat) (bytes : List Byte) :
    (heap.writeBytes base bytes).validByte = heap.validByte := by
  induction bytes generalizing heap base with
  | nil => rfl
  | cons value rest ih => exact ih (heap.writeByte base value) (base + 1)

theorem readableRange_writeBytes (heap : ByteHeap) (base address size : Nat)
    (bytes : List Byte) :
    JuliaLean.src.identity_runtime.readableRange (heap.writeBytes base bytes) address size =
      JuliaLean.src.identity_runtime.readableRange heap address size := by
  unfold JuliaLean.src.identity_runtime.readableRange
  rw [writeBytes_validByte]

/-- Raw byte locations are distinguished by their address residues. -/
theorem byteAt_writeByte_ne (heap : ByteHeap) (base target : Nat) (value : Byte)
    (hne : addressMod target ≠ addressMod base) :
    (heap.writeByte base value).byteAt target = heap.byteAt target := by
  have hb : (addressMod target == addressMod base) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [ByteHeap.writeByte, hb, Bool.false_eq_true, ↓reduceIte]

theorem byteAt_writeByte_self (heap : ByteHeap) (base : Nat) (value : Byte) :
    (heap.writeByte base value).byteAt base = value := by
  simp only [ByteHeap.writeByte, BEq.rfl, Bool.true_eq, ↓reduceIte]

/-- A write with no address wrap preserves every bounded location outside its
half-open byte interval. Both bounds matter because writeByte uses residues. -/
theorem byteAt_writeBytes_outside (heap : ByteHeap) (base target : Nat)
    (bytes : List Byte) (hwrite : base + bytes.length ≤ 2 ^ 64)
    (htarget : target < 2 ^ 64)
    (hout : target < base ∨ base + bytes.length ≤ target) :
    (heap.writeBytes base bytes).byteAt target = heap.byteAt target := by
  induction bytes generalizing heap base with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.length_cons] at hwrite hout
    have htail : base + 1 + rest.length ≤ 2 ^ 64 := by omega
    have htailOut : target < base + 1 ∨ base + 1 + rest.length ≤ target := by omega
    change ((heap.writeByte base value).writeBytes (base + 1) rest).byteAt target = _
    rw [ih (heap.writeByte base value) (base + 1) htail htailOut]
    apply byteAt_writeByte_ne
    rw [addressMod_lt target htarget, addressMod_lt base (by omega)]
    omega

theorem readByte_writeBytes_outside (heap : ByteHeap) (base target : Nat)
    (bytes : List Byte) (hwrite : base + bytes.length ≤ 2 ^ 64)
    (htarget : target < 2 ^ 64)
    (hout : target < base ∨ base + bytes.length ≤ target) :
    (heap.writeBytes base bytes).readByte target = heap.readByte target := by
  unfold ByteHeap.readByte
  rw [addressMod_lt target htarget]
  exact byteAt_writeBytes_outside heap base target bytes hwrite htarget hout

/-- Every byte inside a bounded repeated-byte fill has the requested value. -/
theorem byteAt_writeReplicate_inside (heap : ByteHeap) (base count offset : Nat)
    (value : Byte) (hwrite : base + count ≤ 2 ^ 64) (hoffset : offset < count) :
    (heap.writeBytes base (List.replicate count value)).byteAt (base + offset) = value := by
  induction count generalizing heap base offset with
  | zero => omega
  | succ count ih =>
    simp only [List.replicate_succ, ByteHeap.writeBytes]
    cases offset with
    | zero =>
      simp only [Nat.add_zero]
      have htail : base + 1 + (List.replicate count value).length ≤ 2 ^ 64 := by
        simp only [List.length_replicate]
        omega
      rw [byteAt_writeBytes_outside (heap.writeByte base value) (base + 1) base
        (List.replicate count value) htail (by omega) (Or.inl (by omega))]
      exact byteAt_writeByte_self heap base value
    | succ offset =>
      have hadd : base + Nat.succ offset = (base + 1) + offset := by omega
      rw [hadd]
      exact ih (heap.writeByte base value) (base + 1) offset (by omega) (by omega)

theorem readByte_writeReplicate_inside (heap : ByteHeap) (base count offset : Nat)
    (value : Byte) (hwrite : base + count ≤ 2 ^ 64) (hoffset : offset < count) :
    (heap.writeBytes base (List.replicate count value)).readByte (base + offset) = value := by
  unfold ByteHeap.readByte
  rw [addressMod_lt (base + offset) (by omega)]
  exact byteAt_writeReplicate_inside heap base count offset value hwrite hoffset

/-- The installed little-endian loader is an eight-element fold. -/
theorem load64_eq_foldl (heap : ByteHeap) (address : Nat) :
    JuliaLean.src.support.hashing_c.load64 heap address =
      (List.range 8).foldl (fun value index => value |||
        ((JuliaLean.src.support.hashing_c.byteAt heap (address + index)).toUInt64 <<<
          UInt64.ofNat (8 * index))) (0 : UInt64) := by
  simp only [JuliaLean.src.support.hashing_c.load64,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl] <;> rfl

/-- Eight zero bytes are sufficient to establish a zero native word. -/
theorem load64_zero_of_bytes (heap : ByteHeap) (address : Nat)
    (hzero : ∀ offset < 8, heap.readByte (address + offset) = JInt.wrap .u8 0) :
    JuliaLean.src.support.hashing_c.load64 heap address = 0 := by
  have hb (offset : Nat) (hoffset : offset < 8) :
      JuliaLean.src.support.hashing_c.byteAt heap (address + offset) = 0 := by
    exact congrArg (fun byte : Byte => UInt8.ofNat byte.val.toNat) (hzero offset hoffset)
  rw [load64_eq_foldl]
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.foldl_cons, List.foldl_nil,
    hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide),
    hb 4 (by decide), hb 5 (by decide), hb 6 (by decide), hb 7 (by decide),
    show (0 : UInt8).toUInt64 = (0 : UInt64) from rfl,
    UInt64.zero_shiftLeft, UInt64.or_zero]

/-- Any complete word window inside a bounded zero fill decodes to zero. -/
theorem load64_zero_after_fill (heap : ByteHeap) (base count address : Nat)
    (hwrite : base + count ≤ 2 ^ 64)
    (hlower : base ≤ address) (hupper : address + 8 ≤ base + count) :
    JuliaLean.src.support.hashing_c.load64
      (heap.writeBytes base (List.replicate count (JInt.wrap .u8 0))) address = 0 := by
  apply load64_zero_of_bytes
  intro offset hoffset
  have hin : address + offset - base < count := by omega
  have heq : base + (address + offset - base) = address + offset := by omega
  simpa only [heq] using readByte_writeReplicate_inside heap base count
    (address + offset - base) (JInt.wrap .u8 0) hwrite hin

/-- The native read check is preserved by a fill, and a readable interior word
then returns zero in the same world. -/
theorem loadWord_zero_of_filled_heap (world : World) (original : ByteHeap)
    (base count : Nat) (address : Word)
    (hheap : world.raw.heap = original.writeBytes base
      (List.replicate count (JInt.wrap .u8 0)))
    (hwrite : base + count ≤ 2 ^ 64)
    (hlower : base ≤ address.toNat) (hupper : address.toNat + 8 ≤ base + count)
    (hnonzero : address ≠ 0)
    (hread : JuliaLean.src.identity_runtime.readableRange original address.toNat 8 = true) :
    JuliaLean.src.identity_runtime.loadWord address world = some (.ok 0, world) := by
  apply IdToken.load_word_from_scalars world address 0 hnonzero
  · rw [hheap, readableRange_writeBytes]
    exact hread
  · rw [hheap]
    exact load64_zero_after_fill original base count address.toNat hwrite hlower hupper

/-- This is the zero value-cell premise needed by TableScan: it keeps native
indexing, nonnull-pointer and readability checks explicit. -/
theorem plainReadCell_zero_of_filled_heap (memory : Memory) (index : Word)
    (world : World) (original : ByteHeap) (base count : Nat)
    (hheap : world.raw.heap = original.writeBytes base
      (List.replicate count (JInt.wrap .u8 0)))
    (hwrite : base + count ≤ 2 ^ 64)
    (hindex : index.toNat < memory.length)
    (hlower : base ≤ (JuliaLean.src.identity_runtime.cellAddress memory index).toNat)
    (hupper : (JuliaLean.src.identity_runtime.cellAddress memory index).toNat + 8 ≤ base + count)
    (hnonzero : JuliaLean.src.identity_runtime.cellAddress memory index ≠ 0)
    (hread : JuliaLean.src.identity_runtime.readableRange original
      (JuliaLean.src.identity_runtime.cellAddress memory index).toNat 8 = true) :
    JuliaLean.src.identity_runtime.plainReadCell memory index world = some (.ok 0, world) := by
  unfold JuliaLean.src.identity_runtime.plainReadCell
  rw [if_neg (show ¬ memory.length ≤ index.toNat from Nat.not_le.mpr hindex)]
  exact loadWord_zero_of_filled_heap world original base count
    (JuliaLean.src.identity_runtime.cellAddress memory index)
    hheap hwrite hlower hupper hnonzero hread

end JuliaLean.ChatGPT.Batch8.Group5.ByteWrite

section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-! Native IdDict witness and execution lemmas for the public sentinel collision.
The token is at 64, the throwing default value at 320, and Nothing at 192. -/

/- Source fragment: IddictEarly.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group4
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)

/-- A successful deterministic execution has a unique return value. -/
theorem iddictToken_succeeds_unique {A : Type} (action : M A) (world : World)
    {first second : A} (hfirst : succeeds action world first)
    (hsecond : succeeds action world second) : first = second := by
  obtain ⟨w₁, h₁⟩ := hfirst
  obtain ⟨w₂, h₂⟩ := hsecond
  rw [h₁] at h₂
  cases h₂
  rfl

/-- Equal pointers take the first native identity branch without reading memory. -/
theorem iddictToken_identical_self (world : World) (value : Word) :
    JuliaLean.src.builtins_identity_c.jl_egal_ value value world =
      some (.ok true, world) := by
  rw [JuliaLean.src.builtins_identity_c.jl_egal_]
  simp only [BEq.rfl, Bool.true_eq, ↓reduceIte]
  rfl

namespace IdToken
open JuliaLean.src.identity_runtime
open JuliaLean.base.iddict

/-- Addresses encode a finite one-entry IdDict; key and value denote the public
Symbol whose name is the table token. -/
def memory : Memory :=
  { ptr := 1024, length := 32,
    metadata := { JuliaLean.src.genericmemory_c.boxedDictLayout.metadata with owner := 512 } }

def datatype : Datatype :=
  { name := 2056, hash := 1, parameters := 1536, isMutable := true,
    isAbstract := false, isConcrete := true, size := 24, bits := 192,
    hasPadding := false, isBitsEgal := false, firstPointer := 0,
    fields := [], pointerOffsets := [0] }

def storedWord (slot : Nat) : Word :=
  if slot = 7 then 288 else
  if slot = 39 then 288 else
  if slot = 23 then 416 else
  if slot = 31 then 2048 else
  if slot = 32 then 512 else
  if slot = 33 then 1 else
  if slot = 150 then 64 else
  if slot = 151 then 64 else
  if slot = 193 then 4096 else
  if slot = 194 then 4096 else 0

def heap : JuliaLean.base.pointer.ByteHeap :=
  { byteAt := fun address =>
      JInt.wrap .u8 (((storedWord (address / 8)) >>> UInt64.ofNat (8 * (address % 8))).toNat % 256),
    validByte := fun address => decide (8 ≤ address ∧ address < 8192) }

def world : World :=
  { raw := { heap := heap },
    objects := fun address => if address == 64 then some { hash := 104215988381347979 }
      else if address == 320 then some { hash := 3099839820305488312 } else none,
    datatypes := fun address => if address == 2048 then some datatype else none,
    typenameHashes := fun _ => none,
    smallTypes := fun _ => none,
    internedSymbols := fun text =>
      if text == "__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__" then some 64 else none,
    globals :=
      { nothing := 192
        anyType := 4096
        tupleTypename := 0
        typenameType := 0
        emptyMemory := memory },
    memories := fun address => if address == 512 then some memory else none }

def fields : DictFields :=
  { ht := memory, count := JInt.wrap .i64 1, ndel := JInt.wrap .i64 0,
    keyType := 4096, valueType := 4096 }

def calls : Callees :=
  { gc := { allocateBoxedMemory := fun _ => fail (.abort "unused") },
    newObject := fun _ _ _ _ _ => fail (.abort "unused"),
    copyMemory := fun _ => fail (.abort "unused"),
    isa := fun _ _ => fail (.abort "unused"),
    convert := fun _ _ => fail (.abort "unused"),
    toCsize := fun _ => fail (.abort "unused"),
    doubleInteger := fun _ => fail (.abort "unused"),
    tableSize := fun _ => fail (.abort "unused"),
    lessThanInt := fun _ _ => fail (.abort "unused"),
    lengthArgument := fun _ => fail (.abort "unused"),
    newPair := fun _ _ _ _ => fail (.abort "unused"),
    filterInOnePass := fun _ _ => fail (.abort "unused") }


def withEvents (events : List Event) : World := { world with events := events }

theorem load_known (events : List Event) (address value : Word)
    (hn : address ≠ 0) (hr : readableRange heap address.toNat 8 = true)
    (hv : JuliaLean.src.support.hashing_c.load64 heap address.toNat = value) :
    loadWord address (withEvents events) = some (.ok value, withEvents events) := by
  have hw : (withEvents events).raw.heap = heap := rfl
  simp only [loadWord, requireReadable, getWorld, Bind.bind,
    JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret,
    hw, hn, decide_false, Bool.false_or, hr, Bool.not_true, Bool.false_eq_true,
    ite_false, hv]

theorem dictionary_run (events : List Event) :
    dictionary 256 (withEvents events) = some (.ok fields, withEvents events) := by
  have h256 := load_known events 256 512 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have h248 := load_known events 248 2048 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have h1544 := load_known events 1544 4096 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have h1552 := load_known events 1552 4096 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have h264 := load_known events 264 1 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have h272 := load_known events 272 0 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have htype : typeof 256 (withEvents events) =
      some (.ok 2048, withEvents events) := by
    simp only [typeof, typetag, toTypeof,
      show ((256 : Word).toNat < 8) = False from propext (by decide),
      show (256 : Word) - 8 = 248 from rfl,
      show ((2048 : Word) &&& (~~~(15 : Word))) = 2048 from rfl,
      show ((2048 : Word) < 1024) = False from propext (by decide),
      ite_false, Bind.bind, JuliaLean.base.iterators.bind, h248,
      Pure.pure, JuliaLean.base.iterators.ret]
  simp only [dictionary, datatypeAt, Bind.bind, JuliaLean.base.iterators.bind,
    getWorld, Pure.pure, JuliaLean.base.iterators.ret, h256, htype,
    show (withEvents events).memories 512 = some memory from rfl,
    show (withEvents events).datatypes 2048 = some datatype from rfl,
    show datatype.parameters = (1536 : Word) from rfl,
    show (1536 : Word) + 8 = 1544 from rfl,
    show (1536 : Word) + 16 = 1552 from rfl,
    show (256 : Word) + 8 = 264 from rfl,
    show (256 : Word) + 16 = 272 from rfl,
    h1544, h1552, h264, h272]
  rfl

theorem token_run (events : List Event) :
    secretToken (withEvents events) = some (.ok 64, withEvents events) := by
  rfl

theorem length_run (events : List Event) :
    JuliaLean.base.iddict.length 256 (withEvents events) =
      some (.ok (JInt.wrap .i64 1), withEvents events) := by
  simp only [JuliaLean.base.iddict.length, Bind.bind,
    JuliaLean.base.iterators.bind, dictionary_run]
  rfl

theorem hash_run (events : List Event) :
    JuliaLean.src.builtins_identity_c.jl_object_id 64 (withEvents events) =
      some (.ok 104215988381347979, withEvents events) := by
  rw [JuliaLean.src.builtins_identity_c.jl_object_id]
  have h56 := load_known events 56 288 (by decide)
    (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    (by simp only [JuliaLean.src.support.hashing_c.load64,
      Std.Legacy.Range.forIn_eq_forIn_range']; decide)
  have htag : typetag 64 (withEvents events) = some (.ok 288, withEvents events) := by
    simp only [typetag, show (64 : Word) - 8 = 56 from rfl,
      show ((64 : Word).toNat < 8) = False from propext (by decide),
      ite_false, Bind.bind, JuliaLean.base.iterators.bind, h56]
    rfl
  simp only [Bind.bind, JuliaLean.base.iterators.bind, htag]
  rw [JuliaLean.src.builtins_identity_c.jl_object_id_]
  rfl

theorem cell_run (events : List Event) (i : Nat) (hi : i < 32) :
    plainReadCell memory (UInt64.ofNat i) (withEvents events) =
      some (.ok (if i = 22 ∨ i = 23 then 64 else 0), withEvents events) := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases cases_i with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst i
    apply load_known events
    · decide
    · simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
      decide
    · simp only [JuliaLean.src.support.hashing_c.load64,
        Std.Legacy.Range.forIn_eq_forIn_range']
      decide

end IdToken
end JuliaLean.ChatGPT.Batch8.Group4

/- Source fragment: IddictEarlyNext.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group4.IdToken
open JuliaLean JuliaLean.Proofs.base.iddict JuliaLean.src.identity_runtime
open JuliaLean.base.iddict

theorem livePairs_run (events : List Event) :
    livePairs memory (withEvents events) = some (.ok [(64, 64)], withEvents events) := by
  have hr : List.range (memory.length / 2) =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  have h1 : plainReadCell memory (UInt64.ofNat 1) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 1 (by decide)
  have h3 : plainReadCell memory (UInt64.ofNat 3) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 3 (by decide)
  have h5 : plainReadCell memory (UInt64.ofNat 5) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 5 (by decide)
  have h7 : plainReadCell memory (UInt64.ofNat 7) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 7 (by decide)
  have h9 : plainReadCell memory (UInt64.ofNat 9) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 9 (by decide)
  have h11 : plainReadCell memory (UInt64.ofNat 11) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 11 (by decide)
  have h13 : plainReadCell memory (UInt64.ofNat 13) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 13 (by decide)
  have h15 : plainReadCell memory (UInt64.ofNat 15) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 15 (by decide)
  have h17 : plainReadCell memory (UInt64.ofNat 17) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 17 (by decide)
  have h19 : plainReadCell memory (UInt64.ofNat 19) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 19 (by decide)
  have h21 : plainReadCell memory (UInt64.ofNat 21) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 21 (by decide)
  have h23 : plainReadCell memory (UInt64.ofNat 23) (withEvents events) =
      some (.ok 64, withEvents events) := cell_run events 23 (by decide)
  have h25 : plainReadCell memory (UInt64.ofNat 25) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 25 (by decide)
  have h27 : plainReadCell memory (UInt64.ofNat 27) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 27 (by decide)
  have h29 : plainReadCell memory (UInt64.ofNat 29) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 29 (by decide)
  have h31 : plainReadCell memory (UInt64.ofNat 31) (withEvents events) =
      some (.ok 0, withEvents events) := cell_run events 31 (by decide)
  have h22 : plainReadCell memory (UInt64.ofNat 22) (withEvents events) =
      some (.ok 64, withEvents events) := cell_run events 22 (by decide)
  simp only [livePairs, hr, Nat.reduceAdd, Nat.reduceMul, List.forIn_cons, List.forIn_nil, Bind.bind,
    JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret,
    h1, h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h22,
    show ((0 : Word) != 0) = false from rfl,
    show ((64 : Word) != 0) = true from rfl,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

theorem contents_run (events : List Event) :
    contents 256 (withEvents events) = some (.ok [(64, 64)], withEvents events) := by
  simp only [contents, Bind.bind, JuliaLean.base.iterators.bind, dictionary_run]
  exact livePairs_run events

theorem reference_run (events : List Event) :
    referenceLookup [(64, 64)] 64 (withEvents events) =
      some (.ok (some 64), withEvents events) := by
  simp only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind,
    iddictToken_identical_self, Bool.true_eq, ↓reduceIte]
  all_goals rfl

theorem present : lookupValue world 256 64 (some 64) := by
  exact ⟨[(64, 64)], ⟨world, contents_run []⟩, ⟨world, reference_run []⟩⟩

theorem token_valid : validValue world 64 := by
  exact ⟨by decide, 104215988381347979, world, hash_run []⟩

theorem token_loaded : loadedToken world := by
  exact ⟨64, ⟨world, token_run []⟩, token_valid⟩

theorem placement : tablePlacement world memory := by
  intro index hindex key value hkey hvalue
  change index < 16 at hindex
  by_cases hwhere : index = 11
  · subst index
    have hk : key = 64 := iddictToken_succeeds_unique _ _ hkey
      ⟨world, cell_run [] 22 (by decide)⟩
    have hv : value = 64 := iddictToken_succeeds_unique _ _ hvalue
      ⟨world, cell_run [] 23 (by decide)⟩
    subst key
    subst value
    constructor
    · intro hz
      exact False.elim ((by decide : (64 : Word) ≠ 0) hz)
    · intro _
      refine ⟨104215988381347979, 0, ⟨world, hash_run []⟩,
        by decide, by decide, by decide, ?_⟩
      intro step hstep
      omega
  · have hkempty : ¬ (2 * index = 22 ∨ 2 * index = 23) := by omega
    have hvempty : ¬ (2 * index + 1 = 22 ∨ 2 * index + 1 = 23) := by omega
    have hkrun := cell_run [] (2 * index) (by omega)
    have hvrun := cell_run [] (2 * index + 1) (by omega)
    rw [if_neg hkempty] at hkrun
    rw [if_neg hvempty] at hvrun
    have hk : key = 0 := iddictToken_succeeds_unique _ _ hkey ⟨world, hkrun⟩
    have hv : value = 0 := iddictToken_succeeds_unique _ _ hvalue ⟨world, hvrun⟩
    subst key
    subst value
    exact ⟨fun _ => Or.inl rfl, fun h => False.elim (h rfl)⟩

theorem invariant : dictInvariant world 256 := by
  refine ⟨fields, [(64, 64)], ⟨world, dictionary_run []⟩,
    ⟨world, contents_run []⟩, by decide, by decide, ⟨5, rfl⟩,
    rfl, by decide, ?_, by decide, by decide, by decide, rfl, ?_, ?_, placement⟩
  · intro offset hoff
    change offset < 256 at hoff
    change decide (8 ≤ 1024 + offset ∧ 1024 + offset < 8192) = true
    simp only [decide_eq_true_eq]
    omega
  · constructor
    · intro pair hp
      cases hp
    · trivial
  · intro pair hp
    have heq : pair = (64, 64) := List.mem_singleton.mp hp
    subst pair
    exact ⟨token_valid, token_valid⟩


/-- The sentinel witness also satisfies the supplied stronger native
representation predicate: its table pointer is nonzero and Nothing has tag 26. -/
theorem native_representation : NativeRepresentation world 256 := by
  constructor
  · exact ⟨fields, ⟨world, dictionary_run []⟩, by decide⟩
  · refine ⟨world, ?_⟩
    have h184 := load_known [] 184 416 (by decide)
      (by simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']; decide)
      (by simp only [JuliaLean.src.support.hashing_c.load64,
        Std.Legacy.Range.forIn_eq_forIn_range']; decide)
    change typetag 192 (withEvents []) = some (.ok (26 * 16), withEvents [])
    simp only [typetag, show (192 : Word) - 8 = 184 from rfl,
      show ((192 : Word).toNat < 8) = False from propext (by decide),
      ite_false, Bind.bind, JuliaLean.base.iterators.bind, h184]
    rfl

end JuliaLean.ChatGPT.Batch8.Group4.IdToken

/- Source fragment: IddictPeekFragment.lean -/
-- Combine after IddictEarly.lean's primitive IdToken lemmas.
namespace JuliaLean.ChatGPT.Batch8.Group4.IdToken
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime
open JuliaLean.src.iddict_c

/-- The occupied key cell is the ordinary byte read at address 1200. -/
theorem load_key_run (events : List Event) :
    loadWord 1200 (withEvents events) = some (.ok 64, withEvents events) := by
  have h := cell_run events 22 (by decide)
  change loadWord 1200 (withEvents events) = some (.ok 64, withEvents events) at h
  exact h

/-- The occupied value cell is the ordinary byte read at address 1208. -/
theorem load_value_run (events : List Event) :
    loadWord 1208 (withEvents events) = some (.ok 64, withEvents events) := by
  have h := cell_run events 23 (by decide)
  change loadWord 1208 (withEvents events) = some (.ok 64, withEvents events) at h
  exact h

/-- Atomic key reads append exactly their native load event. -/
theorem atomic_key_run (events : List Event) :
    atomicLoad 1200 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1200 64])) := by
  simp only [atomicLoad, Bind.bind, JuliaLean.base.iterators.bind, load_key_run]
  rfl

/-- Atomic value reads append exactly their native load event. -/
theorem atomic_value_run (events : List Event) :
    atomicLoad 1208 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1208 64])) := by
  simp only [atomicLoad, Bind.bind, JuliaLean.base.iterators.bind, load_value_run]
  rfl

theorem read_key_run (events : List Event) :
    readCell memory 22 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1200 64])) := by
  change atomicLoad 1200 (withEvents events) = _
  exact atomic_key_run events

theorem read_value_run (events : List Event) :
    readCell memory 23 (withEvents events) =
      some (.ok 64, withEvents (events ++ [.load 1208 64])) := by
  change atomicLoad 1208 (withEvents events) = _
  exact atomic_value_run events

/-- The C keyhash wrapper has the same exact execution as native objectid. -/
theorem keyhash_run (events : List Event) :
    keyhash 64 (withEvents events) =
      some (.ok 104215988381347979, withEvents events) := by
  have h := hash_run events
  rw [JuliaLean.src.builtins_identity_c.jl_object_id] at h
  exact h

/-- The first probe sees the stored Symbol and returns its value-cell pointer. -/
theorem peek_loop_run (events : List Event) :
    peekLoop memory 64 32 16 22 22 0 (withEvents events) =
      some (.ok 1208, withEvents (events ++ [.load 1200 64, .load 1208 64])) := by
  rw [peekLoop]
  simp only [Bind.bind, JuliaLean.base.iterators.bind,
    show (22 : Word) + 1 = 23 from rfl, read_key_run,
    show ((64 : Word) == 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, iddictToken_identical_self,
    read_value_run, show ((64 : Word) != 0) = true from rfl,
    Pure.pure, JuliaLean.base.iterators.ret, List.append_assoc]
  rfl

/-- The actual Symbol hash selects the occupied bucket at position 22. -/
theorem peek_run (events : List Event) :
    jl_table_peek_bp memory 64 (withEvents events) =
      some (.ok 1208, withEvents (events ++ [.load 1200 64, .load 1208 64])) := by
  unfold jl_table_peek_bp
  change (keyhash 64 >>= fun hash =>
    peekLoop memory 64 32 16 (h2index hash 16) (h2index hash 16) 0)
    (withEvents events) = _
  simp only [Bind.bind, JuliaLean.base.iterators.bind, keyhash_run]
  change peekLoop memory 64 32 16 22 22 0 (withEvents events) = _
  exact peek_loop_run events

/-- C lookup loads and returns the user-stored Symbol even when it equals its default. -/
theorem table_get_run (events : List Event) (fallback : Word) :
    jl_eqtable_get memory 64 fallback (withEvents events) =
      some (.ok 64, withEvents (events ++
        [.load 1200 64, .load 1208 64, .load 1208 64])) := by
  simp only [jl_eqtable_get, Bind.bind, JuliaLean.base.iterators.bind, peek_run,
    show ((1208 : Word) == 0) = false from rfl, Bool.false_eq_true,
    ↓reduceIte, atomic_value_run, List.append_assoc]
  rfl

end JuliaLean.ChatGPT.Batch8.Group4.IdToken

/- Native pop execution and mutation frame lemmas. -/
namespace JuliaLean.ChatGPT.Batch8.Group4
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime

/-- Native writes preserve accessibility and the runtime globals. -/
def iddictToken_write_frame (before after : World) : Prop :=
  after.globals = before.globals ∧ after.raw.heap.validByte = before.raw.heap.validByte

theorem iddictToken_writeBytes_valid (heap : JuliaLean.base.pointer.ByteHeap)
    (address : Nat) (bytes : List JuliaLean.base.pointer.Byte) :
    (heap.writeBytes address bytes).validByte = heap.validByte := by
  induction bytes generalizing heap address with
  | nil => rfl
  | cons byte rest ih =>
    exact ih (heap.writeByte address byte) (address + 1)

theorem iddictToken_readableRange_valid_congr (first second : JuliaLean.base.pointer.ByteHeap)
    (h : first.validByte = second.validByte) (address count : Nat) :
    readableRange first address count = readableRange second address count := by
  unfold readableRange
  rw [h]

theorem iddictToken_loadWord_run (world : World) (address : Word)
    (hnonzero : address ≠ 0)
    (hread : readableRange world.raw.heap address.toNat 8 = true) :
    loadWord address world = some (.ok
      (JuliaLean.src.support.hashing_c.load64 world.raw.heap address.toNat), world) := by
  simp [loadWord, requireReadable, getWorld, Bind.bind,
    JuliaLean.base.iterators.bind, hnonzero, hread,
    Pure.pure, JuliaLean.base.iterators.ret]

theorem iddictToken_requireReadable_run (world : World) (address : Word)
    (hnonzero : address ≠ 0)
    (hread : readableRange world.raw.heap address.toNat 8 = true) :
    requireReadable address 8 world = some (.ok (), world) := by
  simp [requireReadable, getWorld, Bind.bind, JuliaLean.base.iterators.bind,
    hnonzero, hread, Pure.pure, JuliaLean.base.iterators.ret]

theorem iddictToken_atomic_write_exists (world : World) (owner address value : Word)
    (order : JuliaLean.base.genericmemory.MemoryOrder)
    (hnonzero : address ≠ 0)
    (hread : readableRange world.raw.heap address.toNat 8 = true) :
    ∃ final, gcWriteAtomic owner address value order world = some (.ok (), final) ∧
      iddictToken_write_frame world final := by
  let old := JuliaLean.src.support.hashing_c.load64 world.raw.heap address.toNat
  let raw := JuliaLean.src.genericmemory_c.interpretRawEffect world.raw
    (.deletionBarrier owner.toNat address.toNat)
  let final : World := { world with
    raw := { raw with heap := raw.heap.writeBytes address.toNat (encodeWord value) },
    events := world.events ++ [.writeBarrier owner address old value,
      .atomicStore address value order] }
  refine ⟨final, ?_, ?_⟩
  · simp only [gcWriteAtomic, Bind.bind, JuliaLean.base.iterators.bind,
      iddictToken_loadWord_run world address hnonzero hread, modifyWorld]
    rfl
  · constructor
    · rfl
    · change (world.raw.heap.writeBytes address.toNat (encodeWord value)).validByte = _
      exact iddictToken_writeBytes_valid _ _ _

theorem iddictToken_int_write_exists (world : World) (address : Word)
    (offset : Nat) (value : JInt .i64)
    (hnonzero : address + UInt64.ofNat offset ≠ 0)
    (hread : readableRange world.raw.heap (address + UInt64.ofNat offset).toNat 8 = true) :
    ∃ final, JuliaLean.base.iddict.storeIntField address offset value world =
      some (.ok (), final) ∧ iddictToken_write_frame world final := by
  let location := address + UInt64.ofNat offset
  let bytes := encodeWord (UInt64.ofNat (JuliaLean.base.int.remT .u64 value).val.toNat)
  let final : World := { world with
    raw := { world.raw with heap := world.raw.heap.writeBytes location.toNat bytes } }
  refine ⟨final, ?_, ?_⟩
  · simp only [JuliaLean.base.iddict.storeIntField, Bind.bind,
      JuliaLean.base.iterators.bind,
      iddictToken_requireReadable_run world (address + UInt64.ofNat offset) hnonzero hread,
      modifyWorld]
    rfl
  · constructor
    · rfl
    · exact iddictToken_writeBytes_valid _ _ _

theorem iddictToken_write_frame_trans {first middle final : World}
    (hfirst : iddictToken_write_frame first middle) (hsecond : iddictToken_write_frame middle final) :
    iddictToken_write_frame first final :=
  ⟨hsecond.1.trans hfirst.1, hsecond.2.trans hfirst.2⟩

theorem iddictToken_readable_after_frame {first final : World}
    (h : iddictToken_write_frame first final) (address count : Nat)
    (hread : readableRange first.raw.heap address count = true) :
    readableRange final.raw.heap address count = true := by
  rw [iddictToken_readableRange_valid_congr final.raw.heap first.raw.heap h.2]
  exact hread

end JuliaLean.ChatGPT.Batch8.Group4

namespace JuliaLean.ChatGPT.Batch8.Group4
open JuliaLean JuliaLean.src.identity_runtime

theorem iddictToken_assertType_any (calls : JuliaLean.base.iddict.Callees)
    (world : World) (value : Word) :
    JuliaLean.base.iddict.assertType calls value world.globals.anyType world =
      some (.ok value, world) := by
  simp [JuliaLean.base.iddict.assertType, JuliaLean.base.iddict.isa,
    getWorld, Bind.bind, JuliaLean.base.iterators.bind,
    Pure.pure, JuliaLean.base.iterators.ret]

end JuliaLean.ChatGPT.Batch8.Group4

namespace JuliaLean.ChatGPT.Batch8.Group4.IdToken
open JuliaLean JuliaLean.Proofs.base.iddict JuliaLean.src.identity_runtime
open JuliaLean.src.iddict_c

theorem readable_at (address : Nat)
    (h : address = 1200 ∨ address = 1208 ∨ address = 264 ∨ address = 272) :
    readableRange heap address 8 = true := by
  rcases h with h | h | h | h
  all_goals
    subst address
    simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
    decide

/-- Removing this concrete entry succeeds in C and retains accessibility and
runtime globals. No post-removal dictionary invariant is required below. -/
theorem native_pop_token :
    ∃ final, jl_eqtable_pop memory 64 64 true world =
      some (.ok (64, some true), final) ∧ iddictToken_write_frame world final := by
  let loaded := withEvents [.load 1200 64, .load 1208 64, .load 1208 64]
  have rkey : readableRange loaded.raw.heap 1200 8 = true :=
    readable_at 1200 (Or.inl rfl)
  have rvalue : readableRange loaded.raw.heap 1208 8 = true :=
    readable_at 1208 (Or.inr (Or.inl rfl))
  obtain ⟨clearedKey, hk, fk⟩ :=
    iddictToken_atomic_write_exists loaded 512 1200 192 .monotonic (by decide) rkey
  obtain ⟨clearedValue, hv, fv⟩ :=
    iddictToken_atomic_write_exists clearedKey 512 1208 0 .monotonic (by decide)
      (iddictToken_readable_after_frame fk 1208 8 rvalue)
  refine ⟨clearedValue, ?_, ?_⟩
  · change jl_eqtable_pop memory 64 64 true (withEvents []) = _
    simp only [jl_eqtable_pop, Bind.bind, JuliaLean.base.iterators.bind,
      peek_run, show ((1208 : Word) == 0) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, atomic_value_run, getWorld]
    change (do
      gcWriteAtomic 512 1200 192 .monotonic
      gcWriteAtomic 512 1208 0 .monotonic
      pure ((64 : Word), some true)) loaded = _
    simp only [Bind.bind, JuliaLean.base.iterators.bind, hk, hv,
      Pure.pure, JuliaLean.base.iterators.ret]
  · exact iddictToken_write_frame_trans (show iddictToken_write_frame world loaded from ⟨rfl, rfl⟩)
      (iddictToken_write_frame_trans fk fv)

/-- The defaulted Julia wrapper updates its two counters and returns the
stored token; its Any value assertion reaches the builtin universal-type branch. -/
theorem default_pop_token :
    ∃ final, JuliaLean.base.iddict.popDefault calls 256 64 64 world =
      some (.ok 64, final) := by
  obtain ⟨popped, hp, fp⟩ := native_pop_token
  obtain ⟨counted, hc, fc⟩ :=
    iddictToken_int_write_exists popped 256 8 (fields.count - JInt.wrap .i64 1)
      (by decide)
      (iddictToken_readable_after_frame fp 264 8
        (readable_at 264 (Or.inr (Or.inr (Or.inl rfl)))))
  have fcounted := iddictToken_write_frame_trans fp fc
  obtain ⟨final, hd, fd⟩ :=
    iddictToken_int_write_exists counted 256 16 (fields.ndel + JInt.wrap .i64 1)
      (by decide)
      (iddictToken_readable_after_frame fcounted 272 8
        (readable_at 272 (Or.inr (Or.inr (Or.inr rfl)))))
  have ffinal := iddictToken_write_frame_trans fcounted fd
  have ht : final.globals.anyType = fields.valueType :=
    congrArg Globals.anyType ffinal.1
  have ha : JuliaLean.base.iddict.assertType calls 64 fields.valueType final =
      some (.ok 64, final) := by
    rw [← ht]
    exact iddictToken_assertType_any calls final 64
  have hdictionary : JuliaLean.base.iddict.dictionary 256 world =
      some (.ok fields, world) := dictionary_run []
  refine ⟨final, ?_⟩
  simp only [JuliaLean.base.iddict.popDefault, Bind.bind,
    JuliaLean.base.iterators.bind, hdictionary,
    show fields.ht = memory from rfl, hp, hc, hd, ha]

end JuliaLean.ChatGPT.Batch8.Group4.IdToken

/-! Reduction of mutation/reference agreement to one public token collision.
The final observation alone contradicts the reference map, so no correctness law
for Pair construction or Pair decoding is used. The concrete native-world
premises are supplied separately. -/

namespace JuliaLean.ChatGPT.Batch8.Group4.IdOps
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World M)

/-- Pointer self-identity succeeds immediately and preserves the current world. -/
theorem identity_self (world : World) (key : Word) :
    JuliaLean.src.builtins_identity_c.jl_egal_ key key world =
      some (.ok true, world) := by
  rw [JuliaLean.src.builtins_identity_c.jl_egal_]
  simp only [BEq.rfl, Bool.true_eq, ↓reduceIte]
  rfl

/-- Reference lookup returns the sole entry when queried by that same identity. -/
theorem singleton_reference_lookup (world : World) (key value : Word) :
    referenceLookup [(key, value)] key world = some (.ok (some value), world) := by
  simp only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind,
    identity_self, Bool.true_eq, ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret]

/-- The reference execution keeps a present singleton without consulting its default. -/
theorem singleton_reference_getBang (calls : D.Callees) (world : World)
    (address key value fallback : Word) :
    runReference calls address [.getBang key fallback] [(key, value)] world =
      some (.ok [(key, value)], world) := by
  simp only [runReference, referenceStep, Bind.bind, JuliaLean.base.iterators.bind,
    singleton_reference_lookup, Pure.pure, JuliaLean.base.iterators.ret]

/-- The one-operation execution records exactly the successful mutation's final world. -/
theorem singleton_getBang_run (calls : D.Callees) (world final : World)
    (address key fallback result : Word)
    (mutation : D.getBang calls address key fallback world = some (.ok result, final)) :
    runOperations calls address [.getBang key fallback] world = some (.ok (), final) := by
  simp only [runOperations, Bind.bind, JuliaLean.base.iterators.bind, mutation,
    Pure.pure, JuliaLean.base.iterators.ret]

/-- Observing the reference singleton after the operation still returns its old value. -/
theorem singleton_reference_observation (world : World) (key value fallback : Word) :
    outcome (do return (← referenceLookup [(key, value)] key).getD fallback) world =
      some (.ok value) := by
  simp only [outcome, Bind.bind, JuliaLean.base.iterators.bind,
    singleton_reference_lookup, Pure.pure, JuliaLean.base.iterators.ret,
    Option.getD_some, Option.map_some]

/-- A changed observed value after get! on a present singleton refutes the exact
frozen operation-agreement property. This reduction works for every Pair decoder. -/
theorem ops_agreement_of_present_value_change
    (calls : D.Callees) (pairFields : Word → M (Word × Word))
    (world final : World) (address key token fallback result queryDefault : Word)
    (invariant : dictInvariant world address)
    (loaded : loadedToken world)
    (initial : succeeds (contents address) world [(key, token)])
    (mutation : D.getBang calls address key fallback world = some (.ok result, final))
    (changed : outcome (D.get calls address key queryDefault) final ≠ some (.ok token)) :
    ¬ IdDictOpsAgree := by
  intro agreement
  have run := singleton_getBang_run calls world final address key fallback result mutation
  have promised := agreement calls pairFields world address [.getBang key fallback]
    [(key, token)] invariant loaded (by change 1 < 2^62; decide) initial
  obtain ⟨expected, pairs, count, reference, _, _, _, _, _, _, observations⟩ :=
    promised () final run
  have expected_eq : expected = [(key, token)] := by
    obtain ⟨afterReference, referenceRun⟩ := reference
    rw [singleton_reference_getBang] at referenceRun
    cases referenceRun
    rfl
  subst expected
  apply changed
  exact (observations key queryDefault).trans
    (singleton_reference_observation final key token queryDefault)

end JuliaLean.ChatGPT.Batch8.Group4.IdOps

/- Concatenate after IddictNative.lean and IddictOpsReduction.lean.
This fragment executes a replacement
of the existing token value through the frozen native insertion path. -/
namespace JuliaLean.ChatGPT.Batch8.Group4.IdToken.Overwrite
open JuliaLean JuliaLean.Proofs.base.iddict JuliaLean.src.identity_runtime
open JuliaLean.src.iddict_c JuliaLean.base.iddict

/-- The single local cell allocated by the C put wrapper. -/
def owLocal (events : List Event) : World :=
  { world with locals := [some memory], events := events }

def owValueRaw : JuliaLean.src.genericmemory_c.RawState :=
  let raw := JuliaLean.src.genericmemory_c.interpretRawEffect world.raw (.deletionBarrier 512 1208)
  { raw with heap := raw.heap.writeBytes 1208 (encodeWord 320) }

def owHTRaw : JuliaLean.src.genericmemory_c.RawState :=
  let raw := JuliaLean.src.genericmemory_c.interpretRawEffect owValueRaw (.deletionBarrier 256 256)
  { raw with heap := raw.heap.writeBytes 256 (encodeWord 512) }

def owFinalRaw : JuliaLean.src.genericmemory_c.RawState :=
  { owHTRaw with heap := owHTRaw.heap.writeBytes 264 (encodeWord 1) }

def owValue (events : List Event) : World := { owLocal events with raw := owValueRaw }
def owHT (events : List Event) : World :=
  { owValue events with
    raw := owHTRaw
    memories := fun query => if query == 512 then some memory else world.memories query }
def owFinal (events : List Event) : World := { owHT events with raw := owFinalRaw }

def owStage (stage : Nat) (events : List Event) : World :=
  match stage with
  | 0 => owLocal events
  | 1 => owValue events
  | 2 => owHT events
  | _ => owFinal events

def owWords (stage : Nat) : List (Word × Word) :=
  [(56, 288), (248, 2048), (256, 512), (264, 1), (272, 0),
    (1544, 4096), (1552, 4096), (1200, 64), (1208, if stage = 0 then 64 else 320)]

/-- Every relevant fixed word remains readable; only the stored value changes. -/
theorem ow_known_words (stage : Nat) (small : stage < 4) (address value : Word)
    (known : (address, value) ∈ owWords stage) :
    readableRange (owStage stage []).raw.heap address.toNat 8 = true ∧
      JuliaLean.src.support.hashing_c.load64 (owStage stage []).raw.heap address.toNat = value := by
  have choices : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 := by omega
  rcases choices with h | h | h | h
  all_goals
    subst stage
    simp only [owWords, List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with h | h | h | h | h | h | h | h | h
    all_goals
      obtain ⟨ha, hv⟩ := Prod.mk.inj h
      subst address
      subst value
      constructor
      · simp only [readableRange, Std.Legacy.Range.forIn_eq_forIn_range']
        decide
      · simp only [JuliaLean.src.support.hashing_c.load64,
          Std.Legacy.Range.forIn_eq_forIn_range']
        decide

/-- Events do not change the byte heap of any stage. -/
theorem ow_heap_events (stage : Nat) (events : List Event) :
    (owStage stage events).raw.heap = (owStage stage []).raw.heap := by
  cases stage with
  | zero => rfl
  | succ stage =>
    cases stage with
    | zero => rfl
    | succ stage =>
      cases stage with
      | zero => rfl
      | succ stage => rfl

/-- The runtime metadata and local memory reference are retained at every stage. -/
theorem ow_metadata (stage : Nat) (events : List Event) :
    (owStage stage events).memories 512 = some memory ∧
    (owStage stage events).datatypes 2048 = some datatype ∧
    (owStage stage events).objects 64 = some { hash := 104215988381347979 } ∧
    (owStage stage events).globals.anyType = 4096 ∧
    (owStage stage events).locals = [some memory] ∧
    (owStage stage events).events = events := by
  cases stage with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ stage =>
    cases stage with
    | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | succ stage =>
      cases stage with
      | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | succ stage => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ow_set_events (stage : Nat) (events next : List Event) :
    { owStage stage events with events := next } = owStage stage next := by
  cases stage with
  | zero => rfl
  | succ stage =>
    cases stage with
    | zero => rfl
    | succ stage =>
      cases stage with
      | zero => rfl
      | succ stage => rfl

theorem ow_load (stage : Nat) (small : stage < 4) (events : List Event)
    (address value : Word) (nonzero : address ≠ 0)
    (known : (address, value) ∈ owWords stage) :
    loadWord address (owStage stage events) = some (.ok value, owStage stage events) := by
  obtain ⟨readable, bytes⟩ := ow_known_words stage small address value known
  rw [← ow_heap_events stage events] at readable bytes
  rw [iddictToken_loadWord_run _ _ nonzero readable, bytes]

theorem ow_atomic_load (stage : Nat) (small : stage < 4) (events : List Event)
    (address value : Word) (nonzero : address ≠ 0)
    (known : (address, value) ∈ owWords stage) :
    atomicLoad address (owStage stage events) =
      some (.ok value, owStage stage (events ++ [.load address value])) := by
  have load := ow_load stage small events address value nonzero known
  simp only [atomicLoad, Bind.bind, JuliaLean.base.iterators.bind, load,
    modifyWorld, Pure.pure, JuliaLean.base.iterators.ret,
    (ow_metadata stage events).2.2.2.2.2, ow_set_events]

theorem ow_read_key (stage : Nat) (small : stage < 4) (events : List Event) :
    readCell memory 22 (owStage stage events) =
      some (.ok 64, owStage stage (events ++ [.load 1200 64])) := by
  change atomicLoad 1200 (owStage stage events) = _
  exact ow_atomic_load stage small events 1200 64 (by decide) (by simp [owWords])

theorem ow_read_value (stage : Nat) (small : stage < 4) (events : List Event) :
    readCell memory 23 (owStage stage events) =
      some (.ok (if stage = 0 then 64 else 320),
        owStage stage (events ++ [.load 1208 (if stage = 0 then 64 else 320)])) := by
  change atomicLoad 1208 (owStage stage events) = _
  exact ow_atomic_load stage small events 1208 (if stage = 0 then 64 else 320)
    (by decide) (by simp [owWords])

theorem ow_hash (stage : Nat) (small : stage < 4) (events : List Event) :
    keyhash 64 (owStage stage events) =
      some (.ok 104215988381347979, owStage stage events) := by
  have h56 := ow_load stage small events 56 288 (by decide) (by simp [owWords])
  have htag : typetag 64 (owStage stage events) = some (.ok 288, owStage stage events) := by
    simp only [typetag, show (64 : Word) - 8 = 56 from rfl,
      show ((64 : Word).toNat < 8) = False from propext (by decide),
      ite_false, Bind.bind, JuliaLean.base.iterators.bind, h56]
    rfl
  simp only [keyhash, Bind.bind, JuliaLean.base.iterators.bind, htag]
  rw [JuliaLean.src.builtins_identity_c.jl_object_id_]
  simp only [show (tagKind 288 == Tag.symbol) = true from rfl,
    Bool.true_eq, ite_true, objectAt, getWorld, Bind.bind,
    JuliaLean.base.iterators.bind, (ow_metadata stage events).2.2.1,
    Pure.pure, JuliaLean.base.iterators.ret]

theorem ow_dictionary (stage : Nat) (small : stage < 4) (events : List Event) :
    dictionary 256 (owStage stage events) = some (.ok fields, owStage stage events) := by
  have h256 := ow_load stage small events 256 512 (by decide) (by simp [owWords])
  have h248 := ow_load stage small events 248 2048 (by decide) (by simp [owWords])
  have h1544 := ow_load stage small events 1544 4096 (by decide) (by simp [owWords])
  have h1552 := ow_load stage small events 1552 4096 (by decide) (by simp [owWords])
  have h264 := ow_load stage small events 264 1 (by decide) (by simp [owWords])
  have h272 := ow_load stage small events 272 0 (by decide) (by simp [owWords])
  have htype : typeof 256 (owStage stage events) =
      some (.ok 2048, owStage stage events) := by
    simp only [typeof, typetag, toTypeof,
      show ((256 : Word).toNat < 8) = False from propext (by decide),
      show (256 : Word) - 8 = 248 from rfl,
      show ((2048 : Word) &&& (~~~(15 : Word))) = 2048 from rfl,
      show ((2048 : Word) < 1024) = False from propext (by decide),
      ite_false, Bind.bind, JuliaLean.base.iterators.bind, h248,
      Pure.pure, JuliaLean.base.iterators.ret]
  simp only [dictionary, datatypeAt, Bind.bind, JuliaLean.base.iterators.bind,
    getWorld, Pure.pure, JuliaLean.base.iterators.ret,
    h256, htype, (ow_metadata stage events).1, (ow_metadata stage events).2.1,
    show datatype.parameters = (1536 : Word) from rfl,
    show (1536 : Word) + 8 = 1544 from rfl,
    show (1536 : Word) + 16 = 1552 from rfl,
    show (256 : Word) + 8 = 264 from rfl,
    show (256 : Word) + 16 = 272 from rfl,
    h1544, h1552, h264, h272]
  rfl

def owValueEvents : List Event :=
  [.writeBarrier 512 1208 64 320, .atomicStore 1208 320 .release]
def owHTEvents : List Event :=
  [.writeBarrier 256 256 512 512, .atomicStore 256 512 .notAtomic]
def owPutEvents : List Event := [.load 1200 64, .load 1208 64] ++ owValueEvents

theorem ow_value_write (events : List Event) :
    writeCell memory 23 320 .release (owLocal events) =
      some (.ok (), owValue (events ++ owValueEvents)) := by
  have load := ow_load 0 (by decide) events 1208 64 (by decide) (by simp [owWords])
  change gcWriteAtomic 512 1208 320 .release (owStage 0 events) = _
  simp only [gcWriteAtomic, Bind.bind, JuliaLean.base.iterators.bind, load, modifyWorld]
  rfl

theorem ow_assign_probe (events : List Event) :
    assignProbe memory 64 32 16 22 22 0 (~~~(0 : Word)) (owLocal events) =
      some (.ok (.existing 22), owLocal (events ++ [.load 1200 64, .load 1208 64])) := by
  change assignProbe memory 64 32 16 22 22 0 (~~~(0 : Word)) (owStage 0 events) = _
  rw [assignProbe]
  simp only [Bind.bind, JuliaLean.base.iterators.bind,
    show (22 : Word) + 1 = 23 from rfl,
    ow_read_key 0 (by decide), ow_read_value 0 (by decide),
    show ((64 : Word) == 0) = false from rfl,
    show ((64 : Word) != 0) = true from rfl,
    iddictToken_identical_self, Bool.true_eq, Bool.false_eq_true, ↓reduceIte,
    Pure.pure, JuliaLean.base.iterators.ret, List.append_assoc]
  rfl

theorem ow_assign_outer (events : List Event) :
    assignOuter calls.gc 0 memory 64 320 104215988381347979 (owLocal events) =
      some (.ok false, owValue (events ++ owPutEvents)) := by
  rw [assignOuter]
  simp only [show hash_size memory = 16 from rfl,
    show h2index 104215988381347979 16 = 22 from rfl,
    show (16 : Word) * 2 = 32 from rfl,
    show max_probe 16 = 16 from rfl,
    Bind.bind, JuliaLean.base.iterators.bind, ow_assign_probe,
    show (22 : Word) + 1 = 23 from rfl, ow_value_write,
    Pure.pure, JuliaLean.base.iterators.ret, owPutEvents, List.append_assoc]

theorem ow_table_put (events : List Event) :
    jl_eqtable_put calls.gc memory 64 320 true (withEvents events) =
      some (.ok (memory, some false), owValue (events ++ owPutEvents)) := by
  have new : newLocal (some memory) (withEvents events) = some (.ok 0, owLocal events) := by rfl
  have read (log : List Event) : readLocal 0 (owLocal log) = some (.ok memory, owLocal log) := by rfl
  have put : jl_table_assign_bp calls.gc 0 64 320 (owLocal events) =
      some (.ok false, owValue (events ++ owPutEvents)) := by
    rw [jl_table_assign_bp]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, read,
      show (hash_size memory == 0) = false from rfl, Bool.false_eq_true, ite_false]
    change (keyhash 64 >>= fun hash => assignOuter calls.gc 0 memory 64 320 hash) (owStage 0 events) = _
    simp only [Bind.bind, JuliaLean.base.iterators.bind, ow_hash 0 (by decide)]
    exact ow_assign_outer events
  simp only [jl_eqtable_put, Bind.bind, JuliaLean.base.iterators.bind, new, put]
  rfl

theorem ow_store_ht (events : List Event) :
    storeHT 256 memory (owValue events) = some (.ok (), owHT (events ++ owHTEvents)) := by
  have load : loadWord 256 (owValue events) = some (.ok 512, owValue events) :=
    ow_load 1 (by decide) events 256 512 (by decide) (by simp [owWords])
  simp only [storeHT, gcWriteAtomic, Bind.bind, JuliaLean.base.iterators.bind,
    show memoryOwner memory = 512 from rfl, load, modifyWorld]
  rfl

theorem ow_store_count (events : List Event) :
    storeIntField 256 8 (JInt.wrap .i64 1) (owHT events) = some (.ok (), owFinal events) := by
  have readable : readableRange (owHT events).raw.heap 264 8 = true := by
    have h := (ow_known_words 2 (by decide) 264 1 (by simp [owWords])).1
    rw [← ow_heap_events 2 events] at h
    exact h
  have hr := iddictToken_requireReadable_run (owHT events) 264 (by decide) readable
  simp only [storeIntField, show (256 : Word) + UInt64.ofNat 8 = 264 from rfl,
    Bind.bind, JuliaLean.base.iterators.bind, hr, modifyWorld]
  rfl

theorem ow_isa_any (events : List Event) (value : Word) :
    isa calls value 4096 (withEvents events) = some (.ok true, withEvents events) := by rfl

theorem ow_setindex (events : List Event) :
    setindex! calls 256 320 64 (withEvents events) =
      some (.ok 256, owFinal (events ++ owPutEvents ++ owHTEvents)) := by
  have low : ¬ (fields.ndel.val ≥ (JuliaLean.base.int.ashr_int
      (JInt.wrap .i64 3 * JInt.wrap .i64 (Int.ofNat memory.length)) (JInt.wrap .i64 2)).val) := by decide
  have sameCount : fields.count + JInt.wrap .i64 0 = JInt.wrap .i64 1 := by rfl
  have afterHT (log : List Event) : dictionary 256 (owHT log) = some (.ok fields, owHT log) :=
    ow_dictionary 2 (by decide) log
  simp only [setindex!, Bind.bind, JuliaLean.base.iterators.bind, dictionary_run,
    show fields.keyType = 4096 from rfl, show fields.valueType = 4096 from rfl,
    ow_isa_any, Bool.not_true, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
    show fields.ht = memory from rfl, low, ow_table_put, ow_store_ht,
    afterHT, sameCount, ow_store_count,
    Pure.pure, JuliaLean.base.iterators.ret]

/-- The public get! route overwrites the existing sentinel with the replacement Symbol. -/
theorem ow_getBang (events : List Event) :
    getBang calls 256 64 320 (withEvents events) =
      some (.ok 320, owFinal (events ++
        [.load 1200 64, .load 1208 64, .load 1208 64] ++ owPutEvents ++ owHTEvents)) := by
  simp only [getBang, Bind.bind, JuliaLean.base.iterators.bind, dictionary_run,
    show fields.ht = memory from rfl, show fields.valueType = 4096 from rfl,
    token_run, table_get_run, iddictToken_identical_self,
    Bool.true_eq, ite_true, ow_isa_any, ow_setindex,
    Pure.pure, JuliaLean.base.iterators.ret]

/-- The final C probe observes the newly written value. -/
theorem ow_final_peek_loop (events : List Event) :
    peekLoop memory 64 32 16 22 22 0 (owFinal events) =
      some (.ok 1208, owFinal (events ++ [.load 1200 64, .load 1208 320])) := by
  change peekLoop memory 64 32 16 22 22 0 (owStage 3 events) = _
  rw [peekLoop]
  simp only [Bind.bind, JuliaLean.base.iterators.bind,
    show (22 : Word) + 1 = 23 from rfl,
    ow_read_key 3 (by decide), ow_read_value 3 (by decide),
    show ((64 : Word) == 0) = false from rfl,
    show ((320 : Word) != 0) = true from rfl,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte,
    iddictToken_identical_self, Pure.pure, JuliaLean.base.iterators.ret,
    List.append_assoc]
  rfl

theorem ow_final_peek (events : List Event) :
    jl_table_peek_bp memory 64 (owFinal events) =
      some (.ok 1208, owFinal (events ++ [.load 1200 64, .load 1208 320])) := by
  unfold jl_table_peek_bp
  change (keyhash 64 >>= fun hash =>
    peekLoop memory 64 32 16 (h2index hash 16) (h2index hash 16) 0) (owStage 3 events) = _
  simp only [Bind.bind, JuliaLean.base.iterators.bind, ow_hash 3 (by decide)]
  change peekLoop memory 64 32 16 22 22 0 (owFinal events) = _
  exact ow_final_peek_loop events

theorem ow_final_table_get (events : List Event) :
    jl_eqtable_get memory 64 320 (owFinal events) =
      some (.ok 320, owFinal (events ++
        [.load 1200 64, .load 1208 320, .load 1208 320])) := by
  have read (log : List Event) : atomicLoad 1208 (owFinal log) =
      some (.ok 320, owFinal (log ++ [.load 1208 320])) :=
    ow_atomic_load 3 (by decide) log 1208 320 (by decide) (by simp [owWords])
  simp only [jl_eqtable_get, Bind.bind, JuliaLean.base.iterators.bind,
    ow_final_peek, show ((1208 : Word) == 0) = false from rfl,
    Bool.false_eq_true, ite_false, read, List.append_assoc]
  rfl

/-- A public final get observes the replacement rather than the preserved reference value. -/
theorem ow_final_get (events : List Event) :
    get calls 256 64 320 (owFinal events) =
      some (.ok 320, owFinal (events ++
        [.load 1200 64, .load 1208 320, .load 1208 320])) := by
  have dictionaryFinal : dictionary 256 (owFinal events) = some (.ok fields, owFinal events) :=
    ow_dictionary 3 (by decide) events
  simp only [JuliaLean.base.iddict.get, Bind.bind, JuliaLean.base.iterators.bind,
    dictionaryFinal, show fields.ht = memory from rfl,
    ow_final_table_get, iddictToken_identical_self, Bool.true_eq, ite_true,
    Pure.pure, JuliaLean.base.iterators.ret]

end JuliaLean.ChatGPT.Batch8.Group4.IdToken.Overwrite

namespace JuliaLean.ChatGPT.Batch8.Group4
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Event)
open IdToken IdToken.Overwrite

/-- One get! call overwrites the present public token, whereas the reference
execution retains it. The final get observation establishes the disagreement. -/
theorem IddictsOpsAgree_refuted : ¬ JuliaLean.Proofs.base.iddict.IdDictOpsAgree := by
  let events : List Event :=
    [.load 1200 64, .load 1208 64, .load 1208 64] ++ owPutEvents ++ owHTEvents
  let final : World := owFinal events
  have mutation : JuliaLean.base.iddict.getBang calls 256 64 320 world =
      some (.ok 320, final) := by
    change JuliaLean.base.iddict.getBang calls 256 64 320 (withEvents []) =
      some (.ok 320, owFinal
        ([.load 1200 64, .load 1208 64, .load 1208 64] ++ owPutEvents ++ owHTEvents))
    simpa only [List.nil_append] using ow_getBang []
  have observation : outcome (JuliaLean.base.iddict.get calls 256 64 320) final =
      some (.ok 320) := by
    change (JuliaLean.base.iddict.get calls 256 64 320 (owFinal events)).map Prod.fst = _
    rw [ow_final_get events]
    rfl
  apply IdOps.ops_agreement_of_present_value_change calls (fun _ => pure (64, 320))
    world final 256 64 64 320 320 320 invariant token_loaded
    ⟨world, contents_run []⟩ mutation
  intro equal
  rw [observation] at equal
  have wrong : (320 : Word) = 64 := Except.ok.inj (Option.some.inj equal)
  exact (by decide : (320 : Word) ≠ 64) wrong

end JuliaLean.ChatGPT.Batch8.Group4
end

section
/-! Additional progress for the IdDict mutation, iteration, and constructor targets.
All boundary assumptions below are explicit. No frozen target is replaced. -/

namespace JuliaLean.ChatGPT.Batch8.Group4.IdBoundary
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Memory M Error)
open JuliaLean.base.iddict (Callees DictFields)

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Successful reads give the advertised stored count, with the same final world. -/
theorem length_of_dictionary {address : Word} {world final : World} {fields : DictFields}
    (h : D.dictionary address world = some (.ok fields, final)) :
    D.length address world = some (.ok fields.count, final) := by
  simp only [JuliaLean.base.iddict.length, Bind.bind, JuliaLean.base.iterators.bind, h]
  rfl

/-- The actual reference contents agree with themselves for every query. -/
theorem reference_reflexive (world : World) (pairs : List (Word × Word)) :
    mapsEquivalent world pairs pairs := by
  intro key
  rfl

/-- The physical invariant implies reference agreement before any callback runs. -/
theorem initial_reference_match {world : World} {address : Word}
    (h : dictInvariant world address) :
    ∃ pairs count, succeeds (contents address) world pairs ∧
      matchesReference world address pairs ∧ succeeds (D.length address) world count ∧
      count.val = Int.ofNat pairs.length ∧ keysDistinct world pairs := by
  obtain ⟨fields, pairs, hd, hc, _, _, _, _, _, _, _, _, _, hn, hk, _, _⟩ := h
  refine ⟨pairs, fields.count, hc, ⟨fields, pairs, hd, hc, hn, hk,
    reference_reflexive world pairs⟩, ?_, hn, hk⟩
  obtain ⟨final, run⟩ := hd
  exact ⟨final, length_of_dictionary run⟩

/-- An empty mutation sequence preserves the world and the reference list exactly. -/
theorem empty_trace (calls : Callees) (world : World) (address : Word)
    (pairs : List (Word × Word)) :
    runOperations calls address [] world = some (.ok (), world) ∧
    runReference calls address [] pairs world = some (.ok pairs, world) := by
  constructor <;> rfl

/-- A finite iterator trace records each actual iterator result and pair decode,
including the state passed from one callback to the next. -/
inductive DecodedTrace (calls : Callees) (pairFields : Word → M (Word × Word))
    (address : Word) : World → JInt .i64 → List (Word × Word) → World → Prop where
  | done {world final cursor}
      (run : D.iterate calls address cursor world = some (.ok none, final)) :
      DecodedTrace calls pairFields address world cursor [] final
  | step {world iterated decoded final cursor next raw pair rest}
      (iterRun : D.iterate calls address cursor world =
        some (.ok (some (raw, next)), iterated))
      (decodeRun : pairFields raw iterated = some (.ok pair, decoded))
      (tail : DecodedTrace calls pairFields address decoded next rest final) :
      DecodedTrace calls pairFields address world cursor (pair :: rest) final

/-- Every finite decoded trace is executed by the uncapped collector. -/
theorem collect_of_decoded_trace {calls : Callees} {pairFields : Word → M (Word × Word)}
    {address : Word} {world final : World} {cursor : JInt .i64}
    {pairs : List (Word × Word)}
    (trace : DecodedTrace calls pairFields address world cursor pairs final) :
    collectPairs calls pairFields address cursor world = some (.ok pairs, final) := by
  induction trace with
  | done run =>
    rw [collectPairs]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, run]
    rfl
  | step iterRun decodeRun tail ih =>
    rw [collectPairs]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, iterRun, decodeRun, ih]
    rfl

/-- Iterator errors are propagated before any pair decoding is attempted. -/
theorem collect_iterator_error {calls : Callees} {pairFields : Word → M (Word × Word)}
    {address : Word} {world final : World} {cursor : JInt .i64} {error : Error}
    (run : D.iterate calls address cursor world = some (.error error, final)) :
    collectPairs calls pairFields address cursor world = some (.error error, final) := by
  rw [collectPairs]
  simp only [Bind.bind, JuliaLean.base.iterators.bind, run]

/-- A decoder error is propagated even if the native iterator succeeded. -/
theorem collect_decoder_error {calls : Callees} {pairFields : Word → M (Word × Word)}
    {address raw : Word} {world iterated final : World}
    {cursor next : JInt .i64} {error : Error}
    (iterRun : D.iterate calls address cursor world =
      some (.ok (some (raw, next)), iterated))
    (decodeRun : pairFields raw iterated = some (.error error, final)) :
    collectPairs calls pairFields address cursor world = some (.error error, final) := by
  rw [collectPairs]
  simp only [Bind.bind, JuliaLean.base.iterators.bind, iterRun, decodeRun]

/-- With a physical invariant and a trace of exactly the physical contents,
the length/iteration conclusion follows. The trace is a separate boundary obligation. -/
theorem length_live_of_physical_trace {calls : Callees} {pairFields : Word → M (Word × Word)}
    {address : Word} {world : World}
    (hinvariant : dictInvariant world address)
    (htrace : ∀ pairs, succeeds (contents address) world pairs →
      ∃ final, DecodedTrace calls pairFields address world (JInt.wrap .i64 0) pairs final) :
    ∃ pairs count, succeeds (collectPairs calls pairFields address) world pairs ∧
      succeeds (D.length address) world count ∧ count.val = Int.ofNat pairs.length ∧
      keysDistinct world pairs := by
  obtain ⟨pairs, count, hc, _, hn, heq, hk⟩ := initial_reference_match hinvariant
  obtain ⟨final, trace⟩ := htrace pairs hc
  exact ⟨pairs, count, ⟨final, collect_of_decoded_trace trace⟩, hn, heq, hk⟩

/-- The default conversion is isolated at the exact value-type tag read by get!.
This definition is a proof boundary, not a replacement for the frozen model. -/
def defaultConversion (calls : Callees) (valueType fallback : Word) : M Word := do
  if ← D.isa calls fallback valueType then pure fallback
  else D.assertType calls (← calls.convert valueType fallback) valueType

/-- Successful insertion is the last effect of the missing-token branch. -/
theorem getbang_insert_branch
    (calls : Callees) (address key fallback token value ignored : Word)
    (world probed compared converted final : World) (fields : DictFields)
    (hd : D.dictionary address world = some (.ok fields, world))
    (ht : D.secretToken world = some (.ok token, world))
    (hg : JuliaLean.src.iddict_c.jl_eqtable_get fields.ht key token world =
      some (.ok token, probed))
    (he : JuliaLean.src.builtins_identity_c.jl_egal_ token token probed =
      some (.ok true, compared))
    (hc : defaultConversion calls fields.valueType fallback compared =
      some (.ok value, converted))
    (hs : D.setindex! calls address value key converted = some (.ok ignored, final)) :
    D.getBang calls address key fallback world = some (.ok value, final) := by
  unfold defaultConversion at hc
  obtain ⟨accepted, checked, checkRun, conversionRun⟩ :=
    JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success _ _ _ _ _ hc
  simp only [JuliaLean.base.iddict.getBang, Bind.bind, JuliaLean.base.iterators.bind,
    hd, ht, hg, he, ↓reduceIte]
  cases accepted with
  | true =>
    change (some (.ok fallback, checked) : Option (Except Error Word × World)) =
      some (.ok value, converted) at conversionRun
    cases conversionRun
    simp only [checkRun, Bool.true_eq, ↓reduceIte, Pure.pure,
      JuliaLean.base.iterators.ret, JuliaLean.base.iterators.bind, hs]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at conversionRun
    obtain ⟨rawValue, afterConversion, convertRun, assertRun⟩ :=
      JuliaLean.ChatGPT.Batch4.Group16.iddictConstructor_bind_success
        _ _ _ _ _ conversionRun
    simp only [checkRun, Bool.false_eq_true, ↓reduceIte,
      JuliaLean.base.iterators.bind, convertRun, assertRun, hs,
      Pure.pure, JuliaLean.base.iterators.ret]

/-- If the dictionary's value tag is preserved, the reference conversion uses
exactly the same conversion action at that state. -/
theorem converted_value_of_dictionary (calls : Callees) (address fallback : Word)
    (world : World) (fields : DictFields)
    (hd : D.dictionary address world = some (.ok fields, world)) :
    convertedValue calls address fallback world =
      defaultConversion calls fields.valueType fallback world := by
  simp only [convertedValue, Bind.bind, JuliaLean.base.iterators.bind, hd]
  rfl

/-- Any accepts a default without invoking an unresolved type or conversion callback. -/
theorem default_conversion_any (calls : Callees) (world : World) (fallback : Word) :
    defaultConversion calls world.globals.anyType fallback world =
      some (.ok fallback, world) := by
  simp only [defaultConversion, JuliaLean.base.iddict.isa, Bind.bind,
    JuliaLean.base.iterators.bind, JuliaLean.src.identity_runtime.getWorld,
    BEq.rfl, Bool.true_eq, ↓reduceIte]
  rfl

/-- If typed empty construction satisfies the requested shape for every type
and input state, the three public wrappers inherit the same postcondition. -/
theorem empty_wrappers_of_typed
    (calls : Callees)
    (typed : ∀ world keyType valueType,
      returns (D.emptyTyped calls keyType valueType) world
        (fun result final => emptyShape final result)) :
    ∀ world keyType valueType address,
      returns (D.emptyTyped calls keyType valueType) world (fun result final => emptyShape final result) ∧
      returns (D.emptyAny calls) world (fun result final => emptyShape final result) ∧
      returns (D.emptyTuple calls ()) world (fun result final => emptyShape final result) ∧
      returns (D.emptyOf calls address keyType valueType) world
        (fun result final => emptyShape final result) := by
  intro world keyType valueType address
  have hany : returns (D.emptyAny calls) world (fun result final => emptyShape final result) := by
    intro result final run
    apply typed world world.globals.anyType world.globals.anyType result final
    simpa only [JuliaLean.base.iddict.emptyAny, Bind.bind, JuliaLean.base.iterators.bind,
      JuliaLean.src.identity_runtime.getWorld] using run
  exact ⟨typed world keyType valueType, hany, hany, typed world keyType valueType⟩

end JuliaLean.ChatGPT.Batch8.Group4.IdBoundary
end

section
/- Optional source fragment: concatenate after the IdToken execution lemmas.
It uses only the frozen IdDict proof module's existing import capabilities and
helpers already declared in the new group namespace. -/
namespace JuliaLean.ChatGPT.Batch8.Group4.IdToken
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime (Word World Event)

/-- A public get with the sentinel as default still reads and returns the
present sentinel. No unresolved Julia callback is reached, for any Callees. -/
theorem get_present_token_run (callees : JuliaLean.base.iddict.Callees)
    (events : List Event) :
    JuliaLean.base.iddict.get callees 256 64 64 (withEvents events) =
      some (.ok 64, withEvents (events ++
        [.load 1200 64, .load 1208 64, .load 1208 64])) := by
  simp only [JuliaLean.base.iddict.get, Bind.bind,
    JuliaLean.base.iterators.bind, dictionary_run,
    show fields.ht = memory from rfl, table_get_run,
    iddictToken_identical_self, Bool.true_eq, ite_true,
    Pure.pure, JuliaLean.base.iterators.ret]

/-- The KeySet membership wrapper reports false for this physically present
key because its value is the same ordinary Symbol as the table sentinel. -/
theorem in_key_set_false_run (callees : JuliaLean.base.iddict.Callees)
    (events : List Event) :
    JuliaLean.base.iddict.inKeySet callees 256 64 (withEvents events) =
      some (.ok false, withEvents (events ++
        [.load 1200 64, .load 1208 64, .load 1208 64])) := by
  simp only [JuliaLean.base.iddict.inKeySet, Bind.bind,
    JuliaLean.base.iterators.bind, token_run, get_present_token_run,
    iddictToken_identical_self, Bool.not_true,
    Pure.pure, JuliaLean.base.iterators.ret]


end JuliaLean.ChatGPT.Batch8.Group4.IdToken

/- Optional fragment. Concatenate after IddictNative.lean,
IddictOpsReduction.lean, and IddictOverwriteFragment.lean.
Every execution below holds for arbitrary completions of the callback fields.
No allocation, conversion, Pair construction, or Pair decoding is reached. -/

namespace JuliaLean.ChatGPT.Batch8.Group4.IdToken.OverwriteAny
open JuliaLean JuliaLean.Proofs.base.iddict JuliaLean.src.identity_runtime
open JuliaLean.src.iddict_c JuliaLean.base.iddict
open JuliaLean.ChatGPT.Batch8.Group4.IdToken.Overwrite

/-- Existing-slot assignment does not depend on the allocation callback. -/
theorem assign_outer_any (gc : GC) (events : List Event) :
    assignOuter gc 0 memory 64 320 104215988381347979 (owLocal events) =
      some (.ok false, owValue (events ++ owPutEvents)) := by
  rw [assignOuter]
  simp only [show hash_size memory = 16 from rfl,
    show h2index 104215988381347979 16 = 22 from rfl,
    show (16 : Word) * 2 = 32 from rfl,
    show max_probe 16 = 16 from rfl,
    Bind.bind, JuliaLean.base.iterators.bind, ow_assign_probe,
    show (22 : Word) + 1 = 23 from rfl, ow_value_write,
    Pure.pure, JuliaLean.base.iterators.ret, owPutEvents, List.append_assoc]

/-- The native put wrapper also remains independent of the allocation callback. -/
theorem table_put_any (gc : GC) (events : List Event) :
    jl_eqtable_put gc memory 64 320 true (withEvents events) =
      some (.ok (memory, some false), owValue (events ++ owPutEvents)) := by
  have new : newLocal (some memory) (withEvents events) =
      some (.ok 0, owLocal events) := by rfl
  have read (log : List Event) : readLocal 0 (owLocal log) =
      some (.ok memory, owLocal log) := by rfl
  have put : jl_table_assign_bp gc 0 64 320 (owLocal events) =
      some (.ok false, owValue (events ++ owPutEvents)) := by
    rw [jl_table_assign_bp]
    simp only [Bind.bind, JuliaLean.base.iterators.bind, read,
      show (hash_size memory == 0) = false from rfl, Bool.false_eq_true, ite_false]
    change (keyhash 64 >>= fun hash => assignOuter gc 0 memory 64 320 hash)
      (owStage 0 events) = _
    simp only [Bind.bind, JuliaLean.base.iterators.bind, ow_hash 0 (by decide)]
    exact assign_outer_any gc events
  simp only [jl_eqtable_put, Bind.bind, JuliaLean.base.iterators.bind, new, put]
  rfl

/-- The builtin Any branch does not consult the abstract type-checking field. -/
theorem isa_any_api (api : Callees) (events : List Event) (value : Word) :
    isa api value 4096 (withEvents events) = some (.ok true, withEvents events) := by
  rfl

/-- The public assignment has the same complete execution for every callback API. -/
theorem setindex_any (api : Callees) (events : List Event) :
    setindex! api 256 320 64 (withEvents events) =
      some (.ok 256, owFinal (events ++ owPutEvents ++ owHTEvents)) := by
  have low : ¬ (fields.ndel.val ≥ (JuliaLean.base.int.ashr_int
      (JInt.wrap .i64 3 * JInt.wrap .i64 (Int.ofNat memory.length))
      (JInt.wrap .i64 2)).val) := by decide
  have sameCount : fields.count + JInt.wrap .i64 0 =
      JInt.wrap .i64 1 := by rfl
  have afterHT (log : List Event) : dictionary 256 (owHT log) =
      some (.ok fields, owHT log) := ow_dictionary 2 (by decide) log
  simp only [setindex!, Bind.bind, JuliaLean.base.iterators.bind, dictionary_run,
    show fields.keyType = 4096 from rfl, show fields.valueType = 4096 from rfl,
    isa_any_api, Bool.not_true, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
    show fields.ht = memory from rfl, low, table_put_any, ow_store_ht,
    afterHT, sameCount, ow_store_count,
    Pure.pure, JuliaLean.base.iterators.ret]

/-- Token collision overwrites the present entry for every callback API. -/
theorem getBang_any (api : Callees) (events : List Event) :
    getBang api 256 64 320 (withEvents events) =
      some (.ok 320, owFinal (events ++
        [.load 1200 64, .load 1208 64, .load 1208 64] ++ owPutEvents ++ owHTEvents)) := by
  simp only [getBang, Bind.bind, JuliaLean.base.iterators.bind, dictionary_run,
    show fields.ht = memory from rfl, show fields.valueType = 4096 from rfl,
    token_run, table_get_run, iddictToken_identical_self,
    Bool.true_eq, ite_true, isa_any_api, setindex_any,
    Pure.pure, JuliaLean.base.iterators.ret]

/-- The final public observation uses no callback field. -/
theorem final_get_any (api : Callees) (events : List Event) :
    get api 256 64 320 (owFinal events) =
      some (.ok 320, owFinal (events ++
        [.load 1200 64, .load 1208 320, .load 1208 320])) := by
  have dictionaryFinal : dictionary 256 (owFinal events) =
      some (.ok fields, owFinal events) := ow_dictionary 3 (by decide) events
  simp only [JuliaLean.base.iddict.get, Bind.bind, JuliaLean.base.iterators.bind,
    dictionaryFinal, show fields.ht = memory from rfl,
    ow_final_table_get, iddictToken_identical_self, Bool.true_eq, ite_true,
    Pure.pure, JuliaLean.base.iterators.ret]

def anyMutationEvents : List Event :=
  [.load 1200 64, .load 1208 64, .load 1208 64] ++ owPutEvents ++ owHTEvents

def anyFinalWorld : World := owFinal anyMutationEvents

/-- All callback completions reach this same successful mutation and final world. -/
theorem mutation_any (api : Callees) :
    getBang api 256 64 320 world = some (.ok 320, anyFinalWorld) := by
  change getBang api 256 64 320 (withEvents []) =
    some (.ok 320, owFinal
      ([.load 1200 64, .load 1208 64, .load 1208 64] ++ owPutEvents ++ owHTEvents))
  simpa only [List.nil_append] using getBang_any api []

/-- All callback completions observe the replacement value in the resulting map. -/
theorem final_observation_any (api : Callees) :
    outcome (get api 256 64 320) anyFinalWorld = some (.ok 320) := by
  change (get api 256 64 320 (owFinal anyMutationEvents)).map Prod.fst = _
  rw [final_get_any api anyMutationEvents]
  rfl

/-- The exact target fails for the same public input regardless of every
callback completion and every Pair decoder; only the final get is used. -/
theorem ops_agreement_refuted_for_any_callees (api : Callees)
    (pairFields : Word → M (Word × Word)) : ¬ IdDictOpsAgree := by
  apply IdOps.ops_agreement_of_present_value_change api pairFields
    world anyFinalWorld 256 64 64 320 320 320 invariant token_loaded
    ⟨world, contents_run []⟩ (mutation_any api)
  intro equal
  rw [final_observation_any api] at equal
  have wrong : (320 : Word) = 64 := Except.ok.inj (Option.some.inj equal)
  exact (by decide : (320 : Word) ≠ 64) wrong

end JuliaLean.ChatGPT.Batch8.Group4.IdToken.OverwriteAny
end

namespace JuliaLean.ChatGPT.Batch8.Group6
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

namespace IdMissing
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime
open JuliaLean.src.iddict_c
open JuliaLean.src.builtins_identity_c (jl_egal_)

/-- A reference search returning none must have compared the head key and
received false; its exact next state is preserved in the conclusion. -/
theorem reference_none_cons
    (stored value query : Word) (rest : List (Word × Word)) (world final : World)
    (h : referenceLookup ((stored, value) :: rest) query world =
      some (.ok none, final)) :
    ∃ compared, jl_egal_ query stored world = some (.ok false, compared) ∧
      referenceLookup rest query compared = some (.ok none, final) := by
  cases hc : jl_egal_ query stored world with
  | none =>
    simp only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind, hc] at h
    cases h
  | some answer =>
    rcases answer with ⟨answer, compared⟩
    cases answer with
    | error error =>
      simp only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind, hc] at h
      cases h
    | ok equal =>
      cases equal with
      | false =>
        refine ⟨compared, rfl, ?_⟩
        simpa only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind, hc,
          Bool.false_eq_true, Bool.true_eq, ↓reduceIte] using h
      | true =>
        simp only [referenceLookup, Bind.bind, JuliaLean.base.iterators.bind, hc,
          Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret] at h
        all_goals cases h

/-- This trace is derived from the installed referenceLookup, with every
native identity comparison and intermediate state recorded. -/
inductive AbsentTrace (query : Word) : List (Word × Word) → World → World → Prop
  | nil (world : World) : AbsentTrace query [] world world
  | cons (stored value : Word) (rest : List (Word × Word))
      (world compared final : World)
      (head : jl_egal_ query stored world = some (.ok false, compared))
      (tail : AbsentTrace query rest compared final) :
      AbsentTrace query ((stored, value) :: rest) world final

theorem reference_none_trace (pairs : List (Word × Word)) (query : Word)
    (world final : World)
    (h : referenceLookup pairs query world = some (.ok none, final)) :
    AbsentTrace query pairs world final := by
  induction pairs generalizing world final with
  | nil =>
    simp only [referenceLookup, Pure.pure, JuliaLean.base.iterators.ret] at h
    cases h
    exact .nil world
  | cons pair rest ih =>
    rcases pair with ⟨stored, value⟩
    obtain ⟨compared, hc, hr⟩ := reference_none_cons stored value query rest world final h
    exact .cons stored value rest world compared final hc (ih compared final hr)

def PreservesWorld {A : Type} (action : M A) : Prop :=
  ∀ world result final, action world = some (result, final) → final = world

theorem absent_trace_same_world {query : Word} {pairs : List (Word × Word)}
    {world final : World} (h : AbsentTrace query pairs world final)
    (hpure : ∀ stored, PreservesWorld (jl_egal_ query stored)) :
    final = world ∧
      ∀ pair ∈ pairs, jl_egal_ query pair.1 world = some (.ok false, world) := by
  induction h with
  | nil world =>
    refine ⟨rfl, ?_⟩
    intro pair hp
    cases hp
  | cons stored value rest world compared final hc ht ih =>
    have hstate : compared = world := hpure stored world (.ok false) compared hc
    subst compared
    obtain ⟨hfinal, hall⟩ := ih
    refine ⟨hfinal, ?_⟩
    intro pair hp
    rcases List.mem_cons.mp hp with heq | hrest
    · subst pair
      exact hc
    · exact hall pair hrest

theorem reference_none_same_world (pairs : List (Word × Word)) (query : Word)
    (world final : World)
    (h : referenceLookup pairs query world = some (.ok none, final))
    (hpure : ∀ stored, PreservesWorld (jl_egal_ query stored)) :
    final = world ∧
      ∀ pair ∈ pairs, jl_egal_ query pair.1 world = some (.ok false, world) :=
  absent_trace_same_world (reference_none_trace pairs query world final h) hpure

/-- An occupied pair from the successful cell scan has a failed comparison
somewhere in the exact reference-search trace. No identity purity is assumed. -/
theorem native_pointer_positive (world : World) (address : Word)
    (fields : JuliaLean.base.iddict.DictFields)
    (hd : succeeds (JuliaLean.base.iddict.dictionary address) world fields)
    (hn : NativeRepresentation world address) : 0 < fields.ht.ptr := by
  obtain ⟨other, ⟨afterOther, hOther⟩, hptr⟩ := hn.1
  obtain ⟨afterFields, hFields⟩ := hd
  rw [hFields] at hOther
  cases hOther
  exact hptr

/-- Masking never increases the right operand's unsigned numeric value. -/
theorem masked_le (value mask : Word) : (value &&& mask).toNat ≤ mask.toNat := by
  rw [UInt64.toNat_and]
  exact Nat.and_le_right

theorem sub_one_toNat (size : Word) (hpos : 0 < size.toNat) :
    (size - 1).toNat = size.toNat - 1 := by
  have hle : (1 : Word) ≤ size := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ size.toNat
    omega
  simpa only [show (1 : Word).toNat = 1 from rfl] using
    UInt64.toNat_sub_of_le size 1 hle

theorem masked_index_lt (value size : Word) (hpos : 0 < size.toNat) :
    (value &&& (size - 1)).toNat < size.toNat := by
  have hm := masked_le value (size - 1)
  rw [sub_one_toNat size hpos] at hm
  omega

/-- The initial h2index and its adjacent value cell are in the two-word bucket
array, and h2index is even. This bound does not need hash-distribution facts. -/
theorem initial_bucket_bounds (hash size : Word) (hpos : 0 < size.toNat)
    (hsmall : 2 * size.toNat < 2 ^ 64) :
    (h2index hash size).toNat + 1 < 2 * size.toNat ∧
      (h2index hash size).toNat % 2 = 0 := by
  have hm := masked_le hash (size - 1)
  rw [sub_one_toNat size hpos] at hm
  have hmul : (hash &&& (size - 1)).toNat * 2 < 2 ^ 64 := by omega
  have hi : (h2index hash size).toNat = (hash &&& (size - 1)).toNat * 2 := by
    unfold h2index
    rw [UInt64.toNat_mul]
    change ((hash &&& (size - 1)).toNat * 2) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt hmul
  rw [hi]
  constructor <;> omega

/-- The table's length conversion and division do not wrap under the existing
invariant's length bound. -/
theorem hash_size_toNat (memory : Memory) (h : memory.length < 2 ^ 64) :
    (hash_size memory).toNat = memory.length / 2 := by
  unfold hash_size
  rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' h]
  all_goals rfl

theorem initial_cells_in_bounds (memory : Memory) (hash : Word)
    (hlower : 32 ≤ memory.length) (hupper : memory.length < 2 ^ 61) :
    (h2index hash (hash_size memory)).toNat + 1 < memory.length ∧
      (h2index hash (hash_size memory)).toNat % 2 = 0 := by
  have hs : (hash_size memory).toNat = memory.length / 2 :=
    hash_size_toNat memory (by omega)
  have hb := initial_bucket_bounds hash (hash_size memory) (by rw [hs]; omega)
    (by rw [hs]; omega)
  rw [hs] at hb
  exact ⟨by omega, hb.2⟩

theorem add_one_toNat (value : Word) (h : value.toNat + 1 < 2 ^ 64) :
    (value + 1).toNat = value.toNat + 1 := by
  rw [UInt64.toNat_add]
  change (value.toNat + 1) % 2 ^ 64 = value.toNat + 1
  exact Nat.mod_eq_of_lt h

theorem add_two_toNat (value : Word) (h : value.toNat + 2 < 2 ^ 64) :
    (value + 2).toNat = value.toNat + 2 := by
  rw [UInt64.toNat_add]
  change (value.toNat + 2) % 2 ^ 64 = value.toNat + 2
  exact Nat.mod_eq_of_lt h

/-- The C increment-and-mask step preserves the even key position and leaves
room for its adjacent value cell. -/
theorem next_cells_in_bounds (index size : Word)
    (hpos : 0 < size.toNat) (hsmall : size.toNat < 2 ^ 61)
    (hindex : index.toNat < size.toNat)
    (heven : index.toNat % 2 = 0) (hsizeEven : size.toNat % 2 = 0) :
    (((index + 2) &&& (size - 1)).toNat + 1 < size.toNat) ∧
      (((index + 2) &&& (size - 1)).toNat % 2 = 0) := by
  have hbound := masked_index_lt (index + 2) size hpos
  have hsum : (index + 2).toNat = index.toNat + 2 :=
    add_two_toNat index (by omega)
  have hsumEven : (index + 2).toNat % 2 = 0 := by rw [hsum]; omega
  have hnextEven : ((index + 2) &&& (size - 1)).toNat % 2 = 0 := by
    rw [UInt64.toNat_and]
    have hm := Nat.and_mod_two_pow
      (a := (index + 2).toNat) (b := (size - 1).toNat) (n := 1)
    change ((index + 2).toNat &&& (size - 1).toNat) % 2 =
      ((index + 2).toNat % 2) &&& ((size - 1).toNat % 2) at hm
    rw [hm, hsumEven, Nat.zero_and]
  exact ⟨by omega, hnextEven⟩

theorem power_length_even (length : Nat) (hlower : 32 ≤ length)
    (hpower : ∃ exponent : Nat, length = 2 ^ exponent) : length % 2 = 0 := by
  obtain ⟨exponent, hexponent⟩ := hpower
  cases exponent with
  | zero => simp only [Nat.pow_zero] at hexponent; omega
  | succ exponent => rw [hexponent, Nat.pow_succ]; omega

/-- Under the minimum 16-bucket invariant, the source's empirical maximum
probe count is bounded by the bucket count itself. -/
theorem max_probe_le_size (size : Word) (hsize : 16 ≤ size.toNat) :
    (max_probe size).toNat ≤ size.toNat := by
  unfold max_probe
  split
  · exact hsize
  · rw [UInt64.toNat_shiftRight]
    exact Nat.shiftRight_le _ _

def probeFuel (limit iteration : Word) : Nat := limit.toNat + 1 - iteration.toNat

/-- Every recursive branch consumes one unit of a natural measure; no Word
wrap can turn the final probe back into an earlier iteration. -/
theorem probe_fuel_decreases (limit iteration : Word)
    (hlimit : limit.toNat + 1 < 2 ^ 64)
    (hiteration : iteration.toNat ≤ limit.toNat)
    (hcontinue : iteration + 1 ≤ limit) :
    probeFuel limit (iteration + 1) < probeFuel limit iteration := by
  have hi := add_one_toNat iteration (by omega)
  have hc := UInt64.le_iff_toNat_le.mp hcontinue
  rw [hi] at hc
  unfold probeFuel
  rw [hi]
  omega

theorem cell_address_toNat (memory : Memory) (index : Word)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hindex : index.toNat < memory.length) :
    (cellAddress memory index).toNat = memory.ptr + 8 * index.toNat := by
  have hp : memory.ptr < 2 ^ 64 := by omega
  have hm : 8 * index.toNat < 2 ^ 64 := by omega
  have ha : memory.ptr + 8 * index.toNat < 2 ^ 64 := by omega
  unfold cellAddress
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hp, UInt64.toNat_mul]
  change (memory.ptr + (8 * index.toNat) % 2 ^ 64) % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha]

/-- Eight readable bytes are enough for the installed native Word load; this
lemma proves the source loop rather than assuming a load outcome. -/
theorem readable_eight (heap : JuliaLean.base.pointer.ByteHeap) (address : Nat)
    (hbound : address + 8 ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8, heap.validByte (address + offset) = true) :
    readableRange heap address 8 = true := by
  have h0 := hbytes 0 (by decide)
  have h1 := hbytes 1 (by decide)
  have h2 := hbytes 2 (by decide)
  have h3 := hbytes 3 (by decide)
  have h4 := hbytes 4 (by decide)
  have h5 := hbytes 5 (by decide)
  have h6 := hbytes 6 (by decide)
  have h7 := hbytes 7 (by decide)
  have hr : List.range' 0 8 1 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  have hnot : ¬ address + 8 > 2 ^ 64 := by omega
  simp only [readableRange, if_neg hnot, Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:8] : Std.Legacy.Range).size = 8 from rfl, hr,
    List.forIn_cons, List.forIn_nil, Bind.bind, Pure.pure,
    h0, h1, h2, h3, h4, h5, h6, h7,
    Bool.not_true, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  all_goals rfl

theorem cell_readable (world : World) (memory : Memory) (index : Word)
    (hptr : 0 < memory.ptr)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hindex : index.toNat < memory.length) :
    cellAddress memory index ≠ 0 ∧
      readableRange world.raw.heap (cellAddress memory index).toNat 8 = true := by
  have ha := cell_address_toNat memory index hallocation hindex
  constructor
  · intro hz
    have hn := congrArg UInt64.toNat hz
    rw [ha] at hn
    change memory.ptr + 8 * index.toNat = 0 at hn
    omega
  · apply readable_eight
    · rw [ha]
      omega
    · intro offset hoffset
      rw [ha]
      have hrelative : 8 * index.toNat + offset < 8 * memory.length := by omega
      have hv := hbytes (8 * index.toNat + offset) hrelative
      simpa only [Nat.add_assoc] using hv

/-- The physical invariant therefore justifies the actual native cell read. -/
theorem plain_cell_read (world : World) (memory : Memory) (index : Word)
    (hptr : 0 < memory.ptr)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hindex : index.toNat < memory.length) :
    plainReadCell memory index world = some (.ok
      (JuliaLean.src.support.hashing_c.load64 world.raw.heap
        (cellAddress memory index).toNat), world) := by
  obtain ⟨hnonzero, hread⟩ := cell_readable world memory index hptr hallocation hbytes hindex
  have houtside : ¬ index.toNat ≥ memory.length := by omega
  simp [plainReadCell, if_neg houtside, loadWord, requireReadable,
    getWorld, Bind.bind, JuliaLean.base.iterators.bind, hnonzero, hread,
    Pure.pure, JuliaLean.base.iterators.ret]


/-- A successful monadic bind exposes the exact intermediate state. -/
theorem bind_success {A B : Type} (first : M A) (next : A → M B)
    (world final : World) (result : B)
    (h : (first >>= next) world = some (.ok result, final)) :
    ∃ value middle, first world = some (.ok value, middle) ∧
      next value middle = some (.ok result, final) := by
  cases hf : first world with
  | none =>
    simp only [Bind.bind, JuliaLean.base.iterators.bind, hf] at h
    cases h
  | some answer =>
    rcases answer with ⟨answer, middle⟩
    cases answer with
    | error error =>
      simp only [Bind.bind, JuliaLean.base.iterators.bind, hf] at h
      cases h
    | ok value =>
      exact ⟨value, middle, rfl, by
        simpa only [Bind.bind, JuliaLean.base.iterators.bind, hf] using h⟩

theorem preserves_pure {A : Type} (value : A) : PreservesWorld (pure value : M A) := by
  intro world result final h
  change some (.ok value, world) = some (result, final) at h
  cases h
  rfl

theorem preserves_fail {A : Type} (error : Error) : PreservesWorld (fail error : M A) := by
  intro world result final h
  change some (.error error, world) = some (result, final) at h
  cases h
  rfl

theorem preserves_getWorld : PreservesWorld getWorld := by
  intro world result final h
  change some (.ok world, world) = some (result, final) at h
  cases h
  rfl

theorem preserves_bind {A B : Type} (first : M A) (next : A → M B)
    (hf : PreservesWorld first) (hn : ∀ value, PreservesWorld (next value)) :
    PreservesWorld (first >>= next) := by
  intro world result final h
  cases hr : first world with
  | none =>
    simp only [Bind.bind, JuliaLean.base.iterators.bind, hr] at h
    cases h
  | some answer =>
    rcases answer with ⟨answer, middle⟩
    cases answer with
    | error error =>
      simp only [Bind.bind, JuliaLean.base.iterators.bind, hr] at h
      have hfinal : middle = final := congrArg Prod.snd (Option.some.inj h)
      exact hfinal.symm.trans (hf world (.error error) middle hr)
    | ok value =>
      have hnext : next value middle = some (result, final) := by
        simpa only [Bind.bind, JuliaLean.base.iterators.bind, hr] using h
      exact (hn value middle result final hnext).trans (hf world (.ok value) middle hr)

theorem preserves_requireReadable (address : Word) (size : Nat) :
    PreservesWorld (requireReadable address size) := by
  unfold requireReadable
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  dsimp only
  split
  · exact preserves_fail _
  · exact preserves_pure _

theorem preserves_loadWord (address : Word) : PreservesWorld (loadWord address) := by
  unfold loadWord
  apply preserves_bind _ _ (preserves_requireReadable address 8)
  intro unit
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  exact preserves_pure _

theorem preserves_typetag (value : Word) : PreservesWorld (typetag value) := by
  unfold typetag
  split
  · exact preserves_fail _
  · apply preserves_bind _ _ (preserves_loadWord (value - 8))
    intro header
    exact preserves_pure _

/-- A successful native object hash necessarily began with a successful,
state-preserving load of that object's type tag. This does not require a
termination or frame theorem for recursive hashing. -/
theorem valid_typetag (world : World) (value : Word) (hv : validValue world value) :
    ∃ tag, typetag value world = some (.ok tag, world) := by
  obtain ⟨_, hash, final, hhash⟩ := hv
  rw [JuliaLean.src.builtins_identity_c.jl_object_id] at hhash
  obtain ⟨tag, middle, htag, _⟩ :=
    bind_success (typetag value)
      (fun tag => JuliaLean.src.builtins_identity_c.jl_object_id_ tag value)
      world final hash hhash
  have hs : middle = world := preserves_typetag value world (.ok tag) middle htag
  subst middle
  exact ⟨tag, htag⟩

/-- The Nothing comparison reaches only the pointer/tag fast paths. Thus its
native result is total even when the query's full recursive identity behaviour
has not been analysed. -/
theorem compare_nothing (world : World) (query tag : Word)
    (hq : typetag query world = some (.ok tag, world))
    (hn : typetag world.globals.nothing world = some (.ok (26 * 16), world)) :
    jl_egal_ query world.globals.nothing world =
      some (.ok (query == world.globals.nothing), world) := by
  by_cases hsame : query = world.globals.nothing
  · subst query
    rw [jl_egal_]
    simp only [BEq.rfl, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    all_goals rfl
  · have hsameBool : (query == world.globals.nothing) = false :=
      beq_eq_false_iff_ne.mpr hsame
    rw [jl_egal_]
    simp only [hsameBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
      Bind.bind, JuliaLean.base.iterators.bind, hq, hn]
    by_cases htag : tag = (26 * 16 : Word)
    · subst tag
      simp only [show (((26 * 16 : Word) != (26 * 16)) : Bool) = false from rfl,
        Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      rw [JuliaLean.src.builtins_identity_c.jl_egal__unboxed_]
      simp only [show (26 * 16 : Word) < 1024 from by decide, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      all_goals rfl
    · have htagBool : (tag != (26 * 16 : Word)) = true := bne_iff_ne.mpr htag
      simp only [htagBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      all_goals rfl

theorem native_nothing_comparison (world : World) (address query : Word)
    (hnative : NativeRepresentation world address) (hquery : validValue world query) :
    jl_egal_ query world.globals.nothing world =
      some (.ok (query == world.globals.nothing), world) := by
  obtain ⟨tag, htag⟩ := valid_typetag world query hquery
  obtain ⟨afterNothing, hNothing⟩ := hnative.2
  have hs : afterNothing = world :=
    preserves_typetag world.globals.nothing world (.ok (26 * 16)) afterNothing hNothing
  subst afterNothing
  exact compare_nothing world query tag htag hNothing

/-- The raw word at one physical native table cell. -/
def rawCell (world : World) (memory : Memory) (index : Word) : Word :=
  JuliaLean.src.support.hashing_c.load64 world.raw.heap (cellAddress memory index).toNat

/-- Changing the event log changes no heap or identity metadata. -/
def withEventLog (world : World) (events : List Event) : World := { world with events := events }

theorem withEventLog_globals (world : World) (events : List Event) :
    (withEventLog world events).globals = world.globals := rfl

/-- Native atomic reads append their exact load event and change no other
component of the world. -/
theorem read_cell_event (world : World) (memory : Memory) (index : Word)
    (hptr : 0 < memory.ptr)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hindex : index.toNat < memory.length) :
    readCell memory index world =
      some (.ok (rawCell world memory index),
        withEventLog world (world.events ++ [.load (cellAddress memory index)
          (rawCell world memory index)])) := by
  have hplain := plain_cell_read world memory index hptr hallocation hbytes hindex
  have houtside : ¬ index.toNat ≥ memory.length := by omega
  have hload : loadWord (cellAddress memory index) world =
      some (.ok (rawCell world memory index), world) := by
    simpa only [plainReadCell, if_neg houtside, rawCell] using hplain
  simp only [readCell, if_neg houtside, atomicLoad, Bind.bind,
    JuliaLean.base.iterators.bind, hload, modifyWorld,
    Pure.pure, JuliaLean.base.iterators.ret, withEventLog]


/-- Local facts sufficient for an absent-key probe. This predicate concerns
only the actual occupied cell words and individual native comparisons. It is
not a substitute assumption in the final target: deriving it from livePairs,
reference absence, and native identity's frame property remains an obligation. -/
def AbsentCellComparisons (world : World) (memory : Memory) (query : Word) : Prop :=
  ∀ index : Word, index.toNat + 1 < memory.length → index.toNat % 2 = 0 →
    rawCell world memory index ≠ 0 → ∀ events,
      ∃ matching : Bool,
        jl_egal_ query (rawCell world memory index) (withEventLog world events) =
          some (.ok matching, withEventLog world events) ∧
        (matching = true → rawCell world memory (index + 1) = 0)

/-- A finite induction justifies the installed partial recursive probe. The
word iteration counter cannot wrap under the source's maximum-probe bound,
and every continued probe stays inside an even key/value cell pair. -/
theorem peek_absent_with_fuel (world : World) (memory : Memory)
    (query size limit origin : Word)
    (hptr : 0 < memory.ptr)
    (hlower : 32 ≤ memory.length) (hupper : memory.length < 2 ^ 61)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hsize : size.toNat = memory.length)
    (hsizeEven : memory.length % 2 = 0)
    (hlimit : limit.toNat + 1 < 2 ^ 64)
    (hcomparisons : AbsentCellComparisons world memory query)
    (fuel : Nat) :
    ∀ (index iteration : Word) (events : List Event),
      index.toNat + 1 < memory.length → index.toNat % 2 = 0 →
      iteration.toNat ≤ limit.toNat → probeFuel limit iteration ≤ fuel →
      ∃ finalEvents,
        peekLoop memory query size limit origin index iteration (withEventLog world events) =
          some (.ok 0, withEventLog world finalEvents) := by
  induction fuel with
  | zero =>
    intro index iteration events hindex heven hiteration hfuel
    unfold probeFuel at hfuel
    omega
  | succ fuel ih =>
    intro index iteration events hindex heven hiteration hfuel
    let next : Word := (index + 2) &&& (size - 1)
    have hnext := next_cells_in_bounds index size
      (by rw [hsize]; omega) (by rw [hsize]; exact hupper)
      (by rw [hsize]; omega) heven (by rw [hsize]; exact hsizeEven)
    have hnextBound : next.toNat + 1 < memory.length := by
      simpa only [next, hsize] using hnext.1
    have hnextEven : next.toNat % 2 = 0 := hnext.2
    have htail : ∀ tailEvents : List Event, ∃ finalEvents,
        (if decide (iteration + 1 ≤ limit) && next != origin then
          peekLoop memory query size limit origin next (iteration + 1)
        else pure 0) (withEventLog world tailEvents) =
          some (.ok 0, withEventLog world finalEvents) := by
      intro tailEvents
      by_cases hc : (decide (iteration + 1 ≤ limit) && next != origin) = true
      · have hcontinue : iteration + 1 ≤ limit :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
        have hiterNext : (iteration + 1).toNat ≤ limit.toNat :=
          UInt64.le_iff_toNat_le.mp hcontinue
        have hdecrease := probe_fuel_decreases limit iteration hlimit hiteration hcontinue
        obtain ⟨finalEvents, hrec⟩ := ih next (iteration + 1) tailEvents
          hnextBound hnextEven hiterNext (by omega)
        exact ⟨finalEvents, by simpa only [if_pos hc] using hrec⟩
      · refine ⟨tailEvents, ?_⟩
        simp only [if_neg hc, Pure.pure, JuliaLean.base.iterators.ret]
    let stored := rawCell world memory index
    let keyEvents := events ++ [.load (cellAddress memory index) stored]
    have hreadKey := read_cell_event (withEventLog world events) memory index
      hptr hallocation hbytes (by omega)
    change readCell memory index (withEventLog world events) =
      some (.ok stored, withEventLog world keyEvents) at hreadKey
    by_cases hzero : stored = 0
    · refine ⟨keyEvents, ?_⟩
      rw [peekLoop]
      simp only [Bind.bind, JuliaLean.base.iterators.bind, hreadKey,
        hzero, BEq.rfl, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret]
    · have hzeroBool : (stored == 0) = false := beq_eq_false_iff_ne.mpr hzero
      obtain ⟨matching, hcompare, hmatchingValue⟩ :=
        hcomparisons index hindex heven hzero keyEvents
      change jl_egal_ query stored (withEventLog world keyEvents) =
        some (.ok matching, withEventLog world keyEvents) at hcompare
      cases matching with
      | false =>
        obtain ⟨finalEvents, hfinal⟩ := htail keyEvents
        refine ⟨finalEvents, ?_⟩
        rw [peekLoop]
        simp only [Bind.bind, JuliaLean.base.iterators.bind, hreadKey,
          hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, hcompare,
          Pure.pure, JuliaLean.base.iterators.ret]
        exact hfinal
      | true =>
        have hvalueZero : rawCell world memory (index + 1) = 0 := hmatchingValue rfl
        have hvalueIndex : (index + 1).toNat < memory.length := by
          rw [add_one_toNat index (by omega)]
          exact hindex
        let valueEvents := keyEvents ++ [.load (cellAddress memory (index + 1)) 0]
        have hreadValue := read_cell_event (withEventLog world keyEvents) memory (index + 1)
          hptr hallocation hbytes hvalueIndex
        change readCell memory (index + 1) (withEventLog world keyEvents) =
          some (.ok (rawCell world memory (index + 1)),
            withEventLog world (keyEvents ++ [.load (cellAddress memory (index + 1))
              (rawCell world memory (index + 1))])) at hreadValue
        rw [hvalueZero] at hreadValue
        by_cases hnotNothing : query ≠ world.globals.nothing
        · have hnBool : (query != world.globals.nothing) = true := bne_iff_ne.mpr hnotNothing
          refine ⟨valueEvents, ?_⟩
          rw [peekLoop]
          simp only [Bind.bind, JuliaLean.base.iterators.bind, hreadKey,
            hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, hcompare, hreadValue,
            show ((0 : Word) != 0) = false from rfl, getWorld, withEventLog_globals,
            hnBool, Pure.pure, JuliaLean.base.iterators.ret]
          rfl
        · have heqNothing : query = world.globals.nothing := Classical.byContradiction hnotNothing
          have hnBool : (query != world.globals.nothing) = false :=
            bne_eq_false_iff_eq.mpr heqNothing
          obtain ⟨finalEvents, hfinal⟩ := htail valueEvents
          refine ⟨finalEvents, ?_⟩
          rw [peekLoop]
          simp only [Bind.bind, JuliaLean.base.iterators.bind, hreadKey,
            hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, hcompare, hreadValue,
            show ((0 : Word) != 0) = false from rfl, getWorld, withEventLog_globals,
            hnBool, Pure.pure, JuliaLean.base.iterators.ret]
          exact hfinal

/-- A convenient entry point choosing precisely the remaining probe budget. -/
theorem peek_absent (world : World) (memory : Memory)
    (query size limit origin index iteration : Word) (events : List Event)
    (hptr : 0 < memory.ptr)
    (hlower : 32 ≤ memory.length) (hupper : memory.length < 2 ^ 61)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hsize : size.toNat = memory.length) (hsizeEven : memory.length % 2 = 0)
    (hlimit : limit.toNat + 1 < 2 ^ 64)
    (hcomparisons : AbsentCellComparisons world memory query)
    (hindex : index.toNat + 1 < memory.length) (heven : index.toNat % 2 = 0)
    (hiteration : iteration.toNat ≤ limit.toNat) :
    ∃ finalEvents,
      peekLoop memory query size limit origin index iteration (withEventLog world events) =
        some (.ok 0, withEventLog world finalEvents) :=
  peek_absent_with_fuel world memory query size limit origin hptr hlower hupper
    hallocation hbytes hsize hsizeEven hlimit hcomparisons (probeFuel limit iteration)
    index iteration events hindex heven hiteration (Nat.le_refl _)


/-- The dictionary field decoder contains only readonly native operations. -/
theorem preserves_datatypeAt (address : Word) : PreservesWorld (datatypeAt address) := by
  unfold datatypeAt
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split
  · exact preserves_pure _
  · exact preserves_fail _

theorem preserves_toTypeof (tag : Word) : PreservesWorld (toTypeof tag) := by
  unfold toTypeof
  split
  · apply preserves_bind _ _ preserves_getWorld
    intro snapshot
    split
    · exact preserves_pure _
    · exact preserves_fail _
  · exact preserves_pure _

theorem preserves_typeof (address : Word) : PreservesWorld (typeof address) := by
  unfold typeof
  apply preserves_bind _ _ (preserves_typetag address)
  intro tag
  exact preserves_toTypeof tag

theorem preserves_dictionary (address : Word) :
    PreservesWorld (JuliaLean.base.iddict.dictionary address) := by
  unfold JuliaLean.base.iddict.dictionary
  repeat first
    | exact preserves_pure _
    | exact preserves_fail _
    | exact preserves_getWorld
    | exact preserves_loadWord _
    | exact preserves_typeof _
    | exact preserves_datatypeAt _
    | apply preserves_bind
    | split
    | intro

/-- The installed for-loop's single scan step, named solely for list induction. -/
def scanStep (memory : Memory) (index : Nat) (pairs : List (Word × Word)) :
    M (ForInStep (List (Word × Word))) := do
  let value ← plainReadCell memory (UInt64.ofNat (2 * index + 1))
  if value != 0 then
    let key ← plainReadCell memory (UInt64.ofNat (2 * index))
    pure (.yield (pairs ++ [(key, value)]))
  else pure (.yield pairs)

/-- The direct physical pair at one bucket, omitted precisely when its value
cell is zero. This uses the frozen byte loader and no dictionary lookup. -/
def cellPair (world : World) (memory : Memory) (index : Nat) : Option (Word × Word) :=
  let value := rawCell world memory (UInt64.ofNat (2 * index + 1))
  if value != 0 then
    some (rawCell world memory (UInt64.ofNat (2 * index)), value)
  else none

def physicalPairs (world : World) (memory : Memory) : List (Word × Word) :=
  (List.range (memory.length / 2)).filterMap (cellPair world memory)

theorem plain_cell_nat (world : World) (memory : Memory) (index : Nat)
    (hptr : 0 < memory.ptr) (hupper : memory.length < 2 ^ 64)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hindex : index < memory.length) :
    plainReadCell memory (UInt64.ofNat index) world =
      some (.ok (rawCell world memory (UInt64.ofNat index)), world) := by
  apply plain_cell_read world memory (UInt64.ofNat index) hptr hallocation hbytes
  rw [UInt64.toNat_ofNat_of_lt' (by omega : index < 2 ^ 64)]
  exact hindex

/-- The native finite scan is exactly filtering the nonzero value cells, in
bucket order. Every successful load is justified by the physical allocation. -/
theorem scan_loop_run (world : World) (memory : Memory)
    (hptr : 0 < memory.ptr) (hupper : memory.length < 2 ^ 64)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (indices : List Nat) :
    ∀ (initial : List (Word × Word)),
      (∀ index ∈ indices, 2 * index + 1 < memory.length) →
      forIn indices initial (scanStep memory) world =
        some (.ok (initial ++ indices.filterMap (cellPair world memory)), world) := by
  induction indices with
  | nil =>
    intro initial hindices
    simp only [List.forIn_nil, Pure.pure, JuliaLean.base.iterators.ret,
      List.filterMap_nil, List.append_nil]
  | cons index rest ih =>
    intro initial hindices
    have hindex := hindices index List.mem_cons_self
    have hrest : ∀ index ∈ rest, 2 * index + 1 < memory.length :=
      fun index hi => hindices index (List.mem_cons_of_mem _ hi)
    let key := rawCell world memory (UInt64.ofNat (2 * index))
    let value := rawCell world memory (UInt64.ofNat (2 * index + 1))
    have hvalue : plainReadCell memory (UInt64.ofNat (2 * index + 1)) world =
        some (.ok value, world) :=
      plain_cell_nat world memory (2 * index + 1) hptr hupper hallocation hbytes hindex
    have hkey : plainReadCell memory (UInt64.ofNat (2 * index)) world =
        some (.ok key, world) :=
      plain_cell_nat world memory (2 * index) hptr hupper hallocation hbytes (by omega)
    by_cases hzero : value = 0
    · have hzeroBool : (value != 0) = false := bne_eq_false_iff_eq.mpr hzero
      have hpair : cellPair world memory index = none := by
        simp only [cellPair, show rawCell world memory (UInt64.ofNat (2 * index + 1)) =
          value from rfl, hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      rw [List.forIn_cons]
      simp only [scanStep, Bind.bind, JuliaLean.base.iterators.bind, hvalue,
        hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret,
        List.filterMap_cons, hpair]
      exact ih initial hrest
    · have hzeroBool : (value != 0) = true := bne_iff_ne.mpr hzero
      have hpair : cellPair world memory index = some (key, value) := by
        simp only [cellPair, show rawCell world memory (UInt64.ofNat (2 * index + 1)) =
          value from rfl, hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        all_goals rfl
      rw [List.forIn_cons]
      simp only [scanStep, Bind.bind, JuliaLean.base.iterators.bind, hvalue, hkey,
        hzeroBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret,
        List.filterMap_cons, hpair]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        ih (initial ++ [(key, value)]) hrest

/-- This equation is for the original livePairs definition, not a replacement
scan model. -/
theorem livePairs_physical_run (world : World) (memory : Memory)
    (hptr : 0 < memory.ptr) (hupper : memory.length < 2 ^ 64)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true) :
    livePairs memory world = some (.ok (physicalPairs world memory), world) := by
  have hloop := scan_loop_run world memory hptr hupper hallocation hbytes
    (List.range (memory.length / 2)) [] (by
      intro index hi
      have hi' := List.mem_range.mp hi
      omega)
  change ((forIn (List.range (memory.length / 2)) [] (scanStep memory)) >>=
    fun pairs => pure pairs) world = _
  simp only [Bind.bind, JuliaLean.base.iterators.bind, hloop,
    List.nil_append, Pure.pure, JuliaLean.base.iterators.ret, physicalPairs]

theorem contents_physical_run (world : World) (address : Word)
    (fields : JuliaLean.base.iddict.DictFields)
    (hd : succeeds (JuliaLean.base.iddict.dictionary address) world fields)
    (hptr : 0 < fields.ht.ptr) (hupper : fields.ht.length < 2 ^ 64)
    (hallocation : fields.ht.ptr + 8 * fields.ht.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * fields.ht.length,
      world.raw.heap.validByte (fields.ht.ptr + offset) = true) :
    contents address world = some (.ok (physicalPairs world fields.ht), world) := by
  obtain ⟨middle, hdict⟩ := hd
  have hs : middle = world := preserves_dictionary address world (.ok fields) middle hdict
  subst middle
  simp only [contents, Bind.bind, JuliaLean.base.iterators.bind, hdict]
  exact livePairs_physical_run world fields.ht hptr hupper hallocation hbytes

/-- Every occupied physical bucket occurs in the exact installed scan. -/
theorem occupied_pair_mem (world : World) (memory : Memory) (index : Nat)
    (hindex : index < memory.length / 2)
    (hvalue : rawCell world memory (UInt64.ofNat (2 * index + 1)) ≠ 0) :
    (rawCell world memory (UInt64.ofNat (2 * index)),
      rawCell world memory (UInt64.ofNat (2 * index + 1))) ∈ physicalPairs world memory := by
  apply List.mem_filterMap.mpr
  refine ⟨index, List.mem_range.mpr hindex, ?_⟩
  have hvalueBool : (rawCell world memory (UInt64.ofNat (2 * index + 1)) != 0) = true :=
    bne_iff_ne.mpr hvalue
  simp only [cellPair, hvalueBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]

/-- Reference absence forces a failed native comparison for each occupied
physical bucket. The exact reference intermediate worlds are retained here. -/
theorem lookup_absent_occupied (world : World) (address query : Word)
    (fields : JuliaLean.base.iddict.DictFields)
    (hd : succeeds (JuliaLean.base.iddict.dictionary address) world fields)
    (hptr : 0 < fields.ht.ptr) (hupper : fields.ht.length < 2 ^ 64)
    (hallocation : fields.ht.ptr + 8 * fields.ht.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * fields.ht.length,
      world.raw.heap.validByte (fields.ht.ptr + offset) = true)
    (habsent : lookupValue world address query none)
    (hpure : ∀ stored, PreservesWorld (jl_egal_ query stored))
    (index : Nat) (hindex : index < fields.ht.length / 2)
    (hvalue : rawCell world fields.ht (UInt64.ofNat (2 * index + 1)) ≠ 0) :
    jl_egal_ query (rawCell world fields.ht (UInt64.ofNat (2 * index))) world =
      some (.ok false, world) := by
  obtain ⟨pairs, ⟨afterContents, hcontents⟩, final, hlookup⟩ := habsent
  have hc := contents_physical_run world address fields hd hptr hupper hallocation hbytes
  rw [hc] at hcontents
  cases hcontents
  obtain ⟨_, hall⟩ := reference_none_same_world (physicalPairs world fields.ht)
    query world final hlookup hpure
  exact hall
    (rawCell world fields.ht (UInt64.ofNat (2 * index)),
      rawCell world fields.ht (UInt64.ofNat (2 * index + 1)))
    (occupied_pair_mem world fields.ht index hindex hvalue)


/-- Event independence is a property of the installed native computation. It
states no dictionary result or equality decision. -/
def EventStable {A : Type} (action : M A) : Prop :=
  ∀ world value, action world = some (.ok value, world) → ∀ events,
    action (withEventLog world events) = some (.ok value, withEventLog world events)

/-- All local comparison premises for the finite probe follow from physical
placement, reference absence, and the two native identity frame obligations.
The vacant-cell case uses the actual Nothing tag; occupied cells use the
independent physical scan. -/
theorem absent_cell_comparisons (world : World) (address query : Word)
    (fields : JuliaLean.base.iddict.DictFields)
    (hd : succeeds (JuliaLean.base.iddict.dictionary address) world fields)
    (hptr : 0 < fields.ht.ptr) (hupper : fields.ht.length < 2 ^ 64)
    (hallocation : fields.ht.ptr + 8 * fields.ht.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * fields.ht.length,
      world.raw.heap.validByte (fields.ht.ptr + offset) = true)
    (hplacement : tablePlacement world fields.ht)
    (hnative : NativeRepresentation world address)
    (hquery : validValue world query)
    (habsent : lookupValue world address query none)
    (hpure : ∀ stored, PreservesWorld (jl_egal_ query stored))
    (hevents : ∀ stored, EventStable (jl_egal_ query stored)) :
    AbsentCellComparisons world fields.ht query := by
  intro index hindex heven hnonzero events
  let bucket := index.toNat / 2
  have hbucket : bucket < fields.ht.length / 2 := by
    dsimp only [bucket]
    omega
  have hdouble : 2 * bucket = index.toNat := by dsimp only [bucket]; omega
  have hkeyWord : UInt64.ofNat (2 * bucket) = index := by
    rw [hdouble, UInt64.ofNat_toNat]
  have hvalueWord : UInt64.ofNat (2 * bucket + 1) = index + 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (by omega : 2 * bucket + 1 < 2 ^ 64),
      add_one_toNat index (by omega)]
    omega
  have hvalueIndex : (index + 1).toNat < fields.ht.length := by
    rw [add_one_toNat index (by omega)]
    exact hindex
  by_cases hvalueZero : rawCell world fields.ht (index + 1) = 0
  · have hk : succeeds (plainReadCell fields.ht (UInt64.ofNat (2 * bucket)))
        world (rawCell world fields.ht index) := by
      refine ⟨world, ?_⟩
      rw [hkeyWord]
      exact plain_cell_read world fields.ht index hptr hallocation hbytes (by omega)
    have hv : succeeds (plainReadCell fields.ht (UInt64.ofNat (2 * bucket + 1)))
        world (rawCell world fields.ht (index + 1)) := by
      refine ⟨world, ?_⟩
      rw [hvalueWord]
      exact plain_cell_read world fields.ht (index + 1) hptr hallocation hbytes hvalueIndex
    have hvacant := (hplacement bucket hbucket _ _ hk hv).1 hvalueZero
    have hNothing : rawCell world fields.ht index = world.globals.nothing := by
      rcases hvacant with hzero | hn
      · exact False.elim (hnonzero hzero)
      · exact hn
    have hn := native_nothing_comparison world address query hnative hquery
    have hcompare := hevents world.globals.nothing world
      (query == world.globals.nothing) hn events
    refine ⟨query == world.globals.nothing, ?_, fun _ => hvalueZero⟩
    simpa only [hNothing] using hcompare
  · have hv : rawCell world fields.ht (UInt64.ofNat (2 * bucket + 1)) ≠ 0 := by
      simpa only [hvalueWord] using hvalueZero
    have hcompare := lookup_absent_occupied world address query fields hd hptr hupper
      hallocation hbytes habsent hpure bucket hbucket hv
    rw [hkeyWord] at hcompare
    refine ⟨false, hevents (rawCell world fields.ht index) world false hcompare events, ?_⟩
    intro hfalse
    cases hfalse

theorem doubled_hash_size_toNat (memory : Memory)
    (hupper : memory.length < 2 ^ 61) (heven : memory.length % 2 = 0) :
    (hash_size memory * 2).toNat = memory.length := by
  rw [UInt64.toNat_mul, hash_size_toNat memory (by omega)]
  change ((memory.length / 2) * 2) % 2 ^ 64 = memory.length
  have hdouble : memory.length / 2 * 2 = memory.length := by omega
  rw [hdouble, Nat.mod_eq_of_lt (by omega : memory.length < 2 ^ 64)]

/-- The C keyhash macro and the native public object-id entry point execute
the same installed tag/hash computation. -/
theorem keyhash_object_id (query : Word) :
    keyhash query = JuliaLean.src.builtins_identity_c.jl_object_id query := by
  rw [JuliaLean.src.builtins_identity_c.jl_object_id]
  all_goals rfl

/-- The whole native peek reaches null after finitely many justified reads.
The remaining frame premises are explicit, separate obligations. -/
theorem table_peek_absent (world : World) (memory : Memory) (query hash : Word)
    (hptr : 0 < memory.ptr)
    (hlower : 32 ≤ memory.length) (hupper : memory.length < 2 ^ 61)
    (heven : memory.length % 2 = 0)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hhash : JuliaLean.src.builtins_identity_c.jl_object_id query world =
      some (.ok hash, world))
    (hcomparisons : AbsentCellComparisons world memory query) :
    ∃ finalEvents, jl_table_peek_bp memory query world =
      some (.ok 0, withEventLog world finalEvents) := by
  have hsizeNat : (hash_size memory).toNat = memory.length / 2 :=
    hash_size_toNat memory (by omega)
  have hsizeNonzero : hash_size memory ≠ 0 := by
    intro hz
    have hn := congrArg UInt64.toNat hz
    rw [hsizeNat] at hn
    change memory.length / 2 = 0 at hn
    omega
  have hsizeBool : (hash_size memory == 0) = false := beq_eq_false_iff_ne.mpr hsizeNonzero
  have hprobeBound := max_probe_le_size (hash_size memory) (by rw [hsizeNat]; omega)
  have hlimit : (max_probe (hash_size memory)).toNat + 1 < 2 ^ 64 := by
    rw [hsizeNat] at hprobeBound
    omega
  have hinitial := initial_cells_in_bounds memory hash hlower hupper
  obtain ⟨finalEvents, hpeek⟩ := peek_absent world memory query
    (hash_size memory * 2) (max_probe (hash_size memory))
    (h2index hash (hash_size memory)) (h2index hash (hash_size memory)) 0 world.events
    hptr hlower hupper hallocation hbytes
    (doubled_hash_size_toNat memory hupper heven) heven hlimit hcomparisons
    hinitial.1 hinitial.2 (by change 0 ≤ _; omega)
  have hkeyhash : keyhash query world = some (.ok hash, world) := by
    rw [keyhash_object_id]
    exact hhash
  refine ⟨finalEvents, ?_⟩
  simp only [jl_table_peek_bp, hsizeBool, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
    Bind.bind, JuliaLean.base.iterators.bind, hkeyhash]
  exact hpeek

theorem table_get_absent (world : World) (memory : Memory) (query hash fallback : Word)
    (hptr : 0 < memory.ptr)
    (hlower : 32 ≤ memory.length) (hupper : memory.length < 2 ^ 61)
    (heven : memory.length % 2 = 0)
    (hallocation : memory.ptr + 8 * memory.length ≤ 2 ^ 64)
    (hbytes : ∀ offset < 8 * memory.length,
      world.raw.heap.validByte (memory.ptr + offset) = true)
    (hhash : JuliaLean.src.builtins_identity_c.jl_object_id query world =
      some (.ok hash, world))
    (hcomparisons : AbsentCellComparisons world memory query) :
    ∃ finalEvents, jl_eqtable_get memory query fallback world =
      some (.ok fallback, withEventLog world finalEvents) := by
  obtain ⟨finalEvents, hpeek⟩ := table_peek_absent world memory query hash hptr
    hlower hupper heven hallocation hbytes hhash hcomparisons
  refine ⟨finalEvents, ?_⟩
  simp only [jl_eqtable_get, Bind.bind, JuliaLean.base.iterators.bind, hpeek,
    BEq.rfl, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Pure.pure, JuliaLean.base.iterators.ret]


theorem preserves_secretToken : PreservesWorld JuliaLean.base.iddict.secretToken := by
  unfold JuliaLean.base.iddict.secretToken
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split
  · exact preserves_pure _
  · exact preserves_fail _

theorem same_pointer_run (world : World) (value : Word) :
    jl_egal_ value value world = some (.ok true, world) := by
  rw [jl_egal_]
  simp only [BEq.rfl, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  all_goals rfl

/-- A precise reduction of the frozen Round1 target to three properties of the
installed native readonly code. These are remaining theorem obligations, not
new hypotheses added to the target or laws about dictionary lookup. No final
target theorem is declared until these native properties are proved. -/
theorem missing_index_reduction
    (identityPreserves : ∀ query stored, PreservesWorld (jl_egal_ query stored))
    (identityEvents : ∀ query stored, EventStable (jl_egal_ query stored))
    (hashPreserves : ∀ query,
      PreservesWorld (JuliaLean.src.builtins_identity_c.jl_object_id query)) :
    JuliaLean.Proofs.base.iddict.Round1.MissingIdentityKeyError := by
  intro calls world address query hinvariant hnative hloaded hquery habsent
  obtain ⟨fields, pairs, hd, hcontents, hlower, hupper, hpower, hwordSize,
    hallocation, hbytes, hcountNonneg, hdeletedNonneg, hcapacity, hcount,
    hdistinct, hvalidPairs, hplacement⟩ := hinvariant
  have hptr : 0 < fields.ht.ptr := native_pointer_positive world address fields hd hnative
  have hcomparisons := absent_cell_comparisons world address query fields hd hptr
    (by omega) hallocation hbytes hplacement hnative hquery habsent
    (identityPreserves query) (identityEvents query)
  obtain ⟨_, hash, afterHash, hhash⟩ := hquery
  have hhashState : afterHash = world :=
    hashPreserves query world (.ok hash) afterHash hhash
  subst afterHash
  have heven := power_length_even fields.ht.length hlower hpower
  obtain ⟨token, ⟨afterToken, htoken⟩, htokenValid⟩ := hloaded
  have htokenState : afterToken = world :=
    preserves_secretToken world (.ok token) afterToken htoken
  subst afterToken
  obtain ⟨finalEvents, hget⟩ := table_get_absent world fields.ht query hash token hptr
    hlower hupper heven hallocation hbytes hhash hcomparisons
  obtain ⟨afterDictionary, hdict⟩ := hd
  have hdictState : afterDictionary = world :=
    preserves_dictionary address world (.ok fields) afterDictionary hdict
  subst afterDictionary
  have hsame := same_pointer_run (withEventLog world finalEvents) token
  have hindex : JuliaLean.base.iddict.getindex calls address query world =
      some (.error (.keyError query), withEventLog world finalEvents) := by
    simp only [JuliaLean.base.iddict.getindex, Bind.bind,
      JuliaLean.base.iterators.bind, hdict, htoken, hget, hsame,
      Bool.false_eq_true, Bool.true_eq, ↓reduceIte, fail, JuliaLean.base.iterators.fail]
  unfold outcome
  rw [hindex]
  all_goals rfl

end IdMissing


set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false


namespace IdFrame
open JuliaLean JuliaLean.src.identity_runtime

/-- Replace only the observation log. -/
def replaceEvents (world : World) (events : List Event) : World :=
  { world with events := events }

/-- A one-sided induction predicate: the actual function on the right is fixed
while the approximation on the left varies through the native fixpoint. -/
def FrameApprox {A : Type} (actual approximation : M A) : Prop :=
  ∀ world result final, approximation world = some (result, final) →
    final = world ∧ ∀ events,
      actual (replaceEvents world events) =
        some (result, replaceEvents world events)

/-- The result-dependent conclusion is constant with respect to the current
approximation, so ordinary Option partial-correctness admissibility applies. -/
theorem frameApprox_admissible {A : Type} (actual : M A) :
    Lean.Order.admissible (FrameApprox actual) := by
  unfold FrameApprox
  exact Lean.Order.admissible_pi_apply
    (P := fun (world : World) (output : Option (Except Error A × World)) =>
      ∀ result final, output = some (result, final) →
        final = world ∧ ∀ events,
          actual (replaceEvents world events) = some (result, replaceEvents world events))
    (fun world => Lean.Order.admissible_pi
      (P := fun (output : Option (Except Error A × World)) (result : Except Error A) =>
        ∀ final, output = some (result, final) →
          final = world ∧ ∀ events,
            actual (replaceEvents world events) = some (result, replaceEvents world events))
      (fun result => Lean.Order.admissible_pi
        (P := fun (output : Option (Except Error A × World)) (final : World) =>
          output = some (result, final) →
            final = world ∧ ∀ events,
              actual (replaceEvents world events) = some (result, replaceEvents world events))
        (fun final => Lean.Order.Option.admissible_eq_some _ (result, final))))

/-- Add an ordinary source argument to an admissible frame motive. Repeat this
construction for each non-world argument of a native recursive function. -/
theorem frame_family_admissible {I A : Type} (actual : I → M A) :
    Lean.Order.admissible (fun approximation : I → M A =>
      ∀ input, FrameApprox (actual input) (approximation input)) :=
  Lean.Order.admissible_pi_apply
    (fun input action => FrameApprox (actual input) action)
    (fun input => frameApprox_admissible (actual input))

/-- Divergence contributes no completed execution to the induction predicate. -/
def readView {A : Type} (view : World → A) : M A :=
  fun world => some (.ok (view world), world)

theorem frame_readView {A : Type} (view : World → A)
    (hview : ∀ world events, view (replaceEvents world events) = view world) :
    FrameApprox (readView view) (readView view) := by
  intro world result final h
  change some (.ok (view world), world) = some (result, final) at h
  have hp := Option.some.inj h
  have hr : (Except.ok (view world) : Except Error A) = result := congrArg Prod.fst hp
  have hf : world = final := congrArg Prod.snd hp
  refine ⟨hf.symm, ?_⟩
  intro events
  change some ((Except.ok (view (replaceEvents world events)) : Except Error A), replaceEvents world events) = _
  rw [hview, hr]

theorem frame_return {A : Type} (value : A) :
    FrameApprox (pure value : M A) (pure value : M A) := by
  change FrameApprox (readView (fun _ => value)) (readView (fun _ => value))
  exact frame_readView (fun _ => value) (fun _ _ => rfl)

theorem frame_failure {A : Type} (error : Error) :
    FrameApprox (fail error : M A) (fail error : M A) := by
  intro world result final h
  change some (.error error, world) = some (result, final) at h
  have hp := Option.some.inj h
  have hr : (Except.error error : Except Error A) = result := congrArg Prod.fst hp
  have hf : world = final := congrArg Prod.snd hp
  refine ⟨hf.symm, ?_⟩
  intro events
  change some ((Except.error error : Except Error A), replaceEvents world events) = _
  rw [hr]

/-- Bind composes a fixed actual computation with its independently supplied
approximation. This is the closure rule used by native fixpoint body steps. -/
theorem frame_bind {A B : Type} (actual approximation : M A)
    (actualNext approximationNext : A → M B)
    (hfirst : FrameApprox actual approximation)
    (hnext : ∀ value, FrameApprox (actualNext value) (approximationNext value)) :
    FrameApprox (actual >>= actualNext) (approximation >>= approximationNext) := by
  intro world result final hrun
  cases hsource : approximation world with
  | none =>
    simp only [Bind.bind, JuliaLean.base.iterators.bind, hsource] at hrun
    cases hrun
  | some source =>
    rcases source with ⟨sourceResult, middle⟩
    obtain ⟨hstate, hsourceFrame⟩ := hfirst world sourceResult middle hsource
    subst middle
    cases sourceResult with
    | error error =>
      have he : (some (.error error, world) : Option (Except Error B × World)) =
          some (result, final) := by
        simpa only [Bind.bind, JuliaLean.base.iterators.bind, hsource] using hrun
      have hp := Option.some.inj he
      have hr : (Except.error error : Except Error B) = result := congrArg Prod.fst hp
      have hf : world = final := congrArg Prod.snd hp
      refine ⟨hf.symm, ?_⟩
      intro events
      rw [← hr]
      simp only [Bind.bind, JuliaLean.base.iterators.bind, hsourceFrame events]
    | ok value =>
      have htail : approximationNext value world = some (result, final) := by
        simpa only [Bind.bind, JuliaLean.base.iterators.bind, hsource] using hrun
      obtain ⟨hfinal, htailFrame⟩ := hnext value world result final htail
      refine ⟨hfinal, ?_⟩
      intro events
      simp only [Bind.bind, JuliaLean.base.iterators.bind, hsourceFrame events]
      exact htailFrame events

/-- The eventual self-instance gives ordinary state preservation. -/
def readOptionView {A : Type} (view : World → Option A) (error : Error) : M A := do
  let world ← getWorld
  match view world with
  | some value => pure value
  | none => fail error

theorem frame_readOptionView {A : Type} (view : World → Option A) (error : Error)
    (hview : ∀ world events, view (replaceEvents world events) = view world) :
    FrameApprox (readOptionView view error) (readOptionView view error) := by
  intro world result final h
  simp only [readOptionView, getWorld, Bind.bind, JuliaLean.base.iterators.bind] at h
  cases run : view world with
  | none =>
    simp only [run, fail, JuliaLean.base.iterators.fail] at h
    cases h
    refine ⟨rfl, ?_⟩
    intro events
    simp only [readOptionView, getWorld, Bind.bind, JuliaLean.base.iterators.bind,
      hview, run, fail, JuliaLean.base.iterators.fail]
  | some value =>
    simp only [run, Pure.pure, JuliaLean.base.iterators.ret] at h
    cases h
    refine ⟨rfl, ?_⟩
    intro events
    simp only [readOptionView, getWorld, Bind.bind, JuliaLean.base.iterators.bind,
      hview, run, Pure.pure, JuliaLean.base.iterators.ret]

theorem frame_getWorld_then {A : Type} (next : World → M A)
    (hevents : ∀ world events, next (replaceEvents world events) = next world)
    (hnext : ∀ world, FrameApprox (next world) (next world)) :
    FrameApprox (getWorld >>= next) (getWorld >>= next) := by
  intro world result final h
  simp only [getWorld, Bind.bind, JuliaLean.base.iterators.bind] at h
  obtain ⟨hfinal, hframe⟩ := hnext world world result final h
  refine ⟨hfinal, ?_⟩
  intro events
  simp only [getWorld, Bind.bind, JuliaLean.base.iterators.bind, hevents]
  exact hframe events

theorem frame_requireReadable (address : Word) (size : Nat) :
    FrameApprox (requireReadable address size) (requireReadable address size) := by
  let check : JuliaLean.base.pointer.ByteHeap → M Unit := fun heap =>
    if address = 0 || !(readableRange heap address.toNat size) then
      fail (.undefinedBehavior "native memory load" address)
    else pure ()
  change FrameApprox (readView (fun world => world.raw.heap) >>= check)
    (readView (fun world => world.raw.heap) >>= check)
  apply frame_bind _ _ _ _ (frame_readView _ (fun _ _ => rfl))
  intro heap
  dsimp only [check]
  split
  · exact frame_failure _
  · exact frame_return ()

theorem frame_loadWord (address : Word) :
    FrameApprox (loadWord address) (loadWord address) := by
  change FrameApprox
    (requireReadable address 8 >>= fun _ => readView
      (fun world => JuliaLean.src.support.hashing_c.load64 world.raw.heap address.toNat))
    (requireReadable address 8 >>= fun _ => readView
      (fun world => JuliaLean.src.support.hashing_c.load64 world.raw.heap address.toNat))
  apply frame_bind _ _ _ _ (frame_requireReadable address 8)
  intro unused
  exact frame_readView _ (fun _ _ => rfl)

theorem frame_loadByte (address : Word) :
    FrameApprox (loadByte address) (loadByte address) := by
  change FrameApprox
    (requireReadable address 1 >>= fun _ => readView
      (fun world => JuliaLean.src.support.hashing_c.byteAt world.raw.heap address.toNat))
    (requireReadable address 1 >>= fun _ => readView
      (fun world => JuliaLean.src.support.hashing_c.byteAt world.raw.heap address.toNat))
  apply frame_bind _ _ _ _ (frame_requireReadable address 1)
  intro unused
  exact frame_readView _ (fun _ _ => rfl)

theorem frame_typetag (value : Word) :
    FrameApprox (typetag value) (typetag value) := by
  by_cases hvalue : value.toNat < 8
  · simp only [typetag, hvalue, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    exact frame_failure _
  · simp only [typetag, hvalue, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    apply frame_bind _ _ _ _ (frame_loadWord (value - 8))
    intro header
    exact frame_return (header &&& (~~~(15 : Word)))

end IdFrame


namespace IdFrame
open JuliaLean JuliaLean.src.identity_runtime

/-- Finite source loops preserve the mutual frame relation whenever their
individual bodies do. The done/yield branch is the actual ForInStep semantics. -/
theorem frame_forIn {A B : Type} (values : List A) (initial : B)
    (actual approximation : A → B → M (ForInStep B))
    (hstep : ∀ value state,
      FrameApprox (actual value state) (approximation value state)) :
    FrameApprox (forIn values initial actual) (forIn values initial approximation) := by
  induction values generalizing initial with
  | nil =>
    simpa only [List.forIn_nil] using frame_return initial
  | cons value rest ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply frame_bind _ _ _ _ (hstep value initial)
    intro step
    cases step with
    | done result => exact frame_return result
    | yield state => exact ih state

/-- A getWorld followed immediately by an event-independent projection can be
analysed as a reader without asserting that the whole returned World ignores its
own event log. This is useful for native heap, object, datatype and global reads. -/
theorem frame_projected_getWorld {A B : Type} (view : World → A)
    (actualNext approximationNext : A → M B)
    (hview : ∀ world events, view (replaceEvents world events) = view world)
    (hnext : ∀ value, FrameApprox (actualNext value) (approximationNext value)) :
    FrameApprox
      (do let snapshot ← getWorld; actualNext (view snapshot))
      (do let snapshot ← getWorld; approximationNext (view snapshot)) := by
  change FrameApprox
    (readView view >>= actualNext) (readView view >>= approximationNext)
  exact frame_bind _ _ _ _ (frame_readView view hview) hnext

/-- Pure conditional branches compose without adding operational assumptions. -/
theorem frame_if {A : Type} (condition : Prop) [Decidable condition]
    (actualYes actualNo approximationYes approximationNo : M A)
    (hyes : FrameApprox actualYes approximationYes)
    (hno : FrameApprox actualNo approximationNo) :
    FrameApprox (if condition then actualYes else actualNo)
      (if condition then approximationYes else approximationNo) := by
  by_cases hcondition : condition
  · simpa only [if_pos hcondition] using hyes
  · simpa only [if_neg hcondition] using hno

end IdFrame


namespace IdFrame
open JuliaLean JuliaLean.src.identity_runtime
open JuliaLean.src.builtins_identity_c

/-- Byte comparison contains only bounded native reads and pure branch results. -/
theorem frame_bits_equal (a b : Word) (size : Nat) :
    FrameApprox (bits_equal a b size) (bits_equal a b size) := by
  unfold bits_equal
  apply frame_bind _ _ _ _ (frame_requireReadable a size)
  intro unitA
  apply frame_bind _ _ _ _ (frame_requireReadable b size)
  intro unitB
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply frame_bind
  · apply frame_forIn
    intro index state
    apply frame_bind _ _ _ _ (frame_loadByte (a + UInt64.ofNat index))
    intro x
    apply frame_bind _ _ _ _ (frame_loadByte (b + UInt64.ofNat index))
    intro y
    split <;> exact frame_return _
  · intro result
    rcases result with ⟨returned, unit⟩
    cases returned <;> exact frame_return _

/-- Padding-bit comparison inherits the same frame from the prefix comparison
and the two final native byte loads. -/
theorem frame_primitive_bits_equal (a b : Word) (dt : Datatype) :
    FrameApprox (primitive_bits_equal a b dt) (primitive_bits_equal a b dt) := by
  let nb := used_bytes dt
  have hlast : FrameApprox
      (do
        let x ← loadByte (a + UInt64.ofNat (nb - 1))
        let y ← loadByte (b + UInt64.ofNat (nb - 1))
        pure (((x ^^^ y) &&& last_byte_mask dt) == 0))
      (do
        let x ← loadByte (a + UInt64.ofNat (nb - 1))
        let y ← loadByte (b + UInt64.ofNat (nb - 1))
        pure (((x ^^^ y) &&& last_byte_mask dt) == 0)) := by
    apply frame_bind _ _ _ _ (frame_loadByte (a + UInt64.ofNat (nb - 1)))
    intro x
    apply frame_bind _ _ _ _ (frame_loadByte (b + UInt64.ofNat (nb - 1)))
    intro y
    exact frame_return _
  unfold primitive_bits_equal
  dsimp only
  split
  · exact frame_return _
  · split
    · apply frame_bind _ _ _ _ (frame_bits_equal a b (nb - 1))
      intro prefixEqual
      cases prefixEqual with
      | false =>
        simp only [Bool.not_false, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        exact frame_return _
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        exact hlast
    · exact hlast


end IdFrame


namespace IdFrame
open JuliaLean JuliaLean.src.identity_runtime

/-- A completed run of a chain supremum is already a completed run of a chain
member. The proof uses the existing pointwise Option admissibility theorem. -/
theorem frame_self_admissible {A : Type} :
    Lean.Order.admissible (fun action : M A => FrameApprox action action) := by
  exact JuliaLean.ChatGPT.Batch4.Group16.PureNativeFrames.frame_admissible replaceEvents

end IdFrame


namespace IdFrame
open JuliaLean JuliaLean.src.identity_runtime JuliaLean.src.builtins_identity_c

theorem frame_compare_svec_loop_self_body
    (egal : Word → Word → M Bool)
    (loop : Word → Word → Nat → Nat → M Bool)
    (hegal : ∀ a b, FrameApprox (egal a b) (egal a b))
    (hloop : ∀ a b length index,
      FrameApprox (loop a b length index) (loop a b length index))
    (a b : Word) (length index : Nat) :
    FrameApprox
      (do
        if index ≥ length then return true
        let x ← loadWord (a + 8 + UInt64.ofNat (8 * index))
        let y ← loadWord (b + 8 + UInt64.ofNat (8 * index))
        if !(← egal x y) then pure false
        else loop a b length (index + 1))
      (do
        if index ≥ length then return true
        let x ← loadWord (a + 8 + UInt64.ofNat (8 * index))
        let y ← loadWord (b + 8 + UInt64.ofNat (8 * index))
        if !(← egal x y) then pure false
        else loop a b length (index + 1)) := by
  by_cases hindex : index ≥ length
  · simp only [hindex, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    exact frame_return true
  · simp only [hindex, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    apply frame_bind _ _ _ _ (frame_loadWord (a + 8 + UInt64.ofNat (8 * index)))
    intro x
    apply frame_bind _ _ _ _ (frame_loadWord (b + 8 + UInt64.ofNat (8 * index)))
    intro y
    apply frame_bind _ _ _ _ (hegal x y)
    intro equal
    cases equal with
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      exact frame_return false
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      exact hloop a b length (index + 1)

theorem frame_egal_parameters_self_body
    (types : Word → Word → TypeEnv → Bool → M Bool)
    (parameters : Word → Word → Nat → Nat → TypeEnv → Bool → M Bool)
    (htypes : ∀ a b env names, FrameApprox (types a b env names) (types a b env names))
    (hparameters : ∀ a b length index env names,
      FrameApprox (parameters a b length index env names) (parameters a b length index env names))
    (a b : Word) (length index : Nat) (env : TypeEnv) (names : Bool) :
    FrameApprox
      (do
        if index ≥ length then return true
        let x ← loadWord (a + 8 + UInt64.ofNat (8 * index))
        let y ← loadWord (b + 8 + UInt64.ofNat (8 * index))
        if !(← types x y env names) then pure false
        else parameters a b length (index + 1) env names)
      (do
        if index ≥ length then return true
        let x ← loadWord (a + 8 + UInt64.ofNat (8 * index))
        let y ← loadWord (b + 8 + UInt64.ofNat (8 * index))
        if !(← types x y env names) then pure false
        else parameters a b length (index + 1) env names) := by
  by_cases hindex : index ≥ length
  · simp only [hindex, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    exact frame_return true
  · simp only [hindex, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    apply frame_bind _ _ _ _ (frame_loadWord (a + 8 + UInt64.ofNat (8 * index)))
    intro x
    apply frame_bind _ _ _ _ (frame_loadWord (b + 8 + UInt64.ofNat (8 * index)))
    intro y
    apply frame_bind _ _ _ _ (htypes x y env names)
    intro equal
    cases equal with
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      exact frame_return false
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      exact hparameters a b length (index + 1) env names

theorem frame_jl_egal_self_body
    (unboxed : Word → Word → Word → M Bool)
    (hunboxed : ∀ a b tag,
      FrameApprox (unboxed a b tag) (unboxed a b tag))
    (a b : Word) :
    FrameApprox
      (do
        if a == b then return true
        let tag ← typetag a
        if tag != (← typetag b) then return false
        unboxed a b tag)
      (do
        if a == b then return true
        let tag ← typetag a
        if tag != (← typetag b) then return false
        unboxed a b tag) := by
  by_cases hab : (a == b) = true
  · simp only [hab, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    exact frame_return true
  · simp only [hab, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    apply frame_bind _ _ _ _ (frame_typetag a)
    intro tag
    apply frame_bind _ _ _ _ (frame_typetag b)
    intro otherTag
    by_cases htags : (tag != otherTag) = true
    · simp only [htags, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      exact frame_return false
    · simp only [htags, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      exact hunboxed a b tag

theorem frame_jl_egal_bits_self_body
    (fields : Word → Word → Datatype → M Bool)
    (hfields : ∀ a b dt, FrameApprox (fields a b dt) (fields a b dt))
    (a b : Word) (dt : Datatype) :
    FrameApprox
      (do
        if dt.size = 0 then return true
        if dt.fields.isEmpty then
          if dt.hasPadding then primitive_bits_equal a b dt else bits_equal a b dt.size
        else if !dt.hasPadding && dt.isBitsEgal then bits_equal a b dt.size
        else fields a b dt)
      (do
        if dt.size = 0 then return true
        if dt.fields.isEmpty then
          if dt.hasPadding then primitive_bits_equal a b dt else bits_equal a b dt.size
        else if !dt.hasPadding && dt.isBitsEgal then bits_equal a b dt.size
        else fields a b dt) := by
  by_cases hsize : dt.size = 0
  · simp only [hsize, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    exact frame_return true
  · simp only [hsize, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    by_cases hempty : dt.fields.isEmpty = true
    · simp only [hempty, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      by_cases hpadding : dt.hasPadding = true
      · simp only [hpadding, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        exact frame_primitive_bits_equal a b dt
      · simp only [hpadding, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        exact frame_bits_equal a b dt.size
    · simp only [hempty, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      by_cases hbits : (!dt.hasPadding && dt.isBitsEgal) = true
      · simp only [hbits, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        exact frame_bits_equal a b dt.size
      · simp only [hbits, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        exact hfields a b dt

end IdFrame


set_option maxHeartbeats 2000000
set_option maxRecDepth 4096


namespace IdMissing
open JuliaLean JuliaLean.src.identity_runtime JuliaLean.src.builtins_identity_c

theorem preserves_forIn {A B : Type} (values : List A) (initial : B)
    (step : A → B → M (ForInStep B))
    (hstep : ∀ value state, PreservesWorld (step value state)) :
    PreservesWorld (forIn values initial step) := by
  induction values generalizing initial with
  | nil => simpa only [List.forIn_nil] using preserves_pure initial
  | cons value rest ih =>
    rw [List.forIn_cons]
    apply preserves_bind _ _ (hstep value initial)
    intro next
    cases next with
    | done result => exact preserves_pure result
    | yield state => exact ih state

theorem preserves_if {A : Type} (condition : Prop) [Decidable condition]
    (yes no : M A) (hyes : PreservesWorld yes) (hno : PreservesWorld no) :
    PreservesWorld (if condition then yes else no) := by
  by_cases hcondition : condition
  · simpa only [if_pos hcondition] using hyes
  · simpa only [if_neg hcondition] using hno

theorem preserves_divergent {A : Type} : PreservesWorld (fun _ => (none : Option (Except Error A × World))) := by
  intro world result final h
  cases h

theorem preserves_loadByte (address : Word) : PreservesWorld (loadByte address) := by
  unfold loadByte
  apply preserves_bind _ _ (preserves_requireReadable address 1)
  intro unit
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  exact preserves_pure _

theorem preserves_bits_hash (address : Word) (size : Nat) :
    PreservesWorld (bits_hash address size) := by
  unfold bits_hash
  apply preserves_bind _ _ (preserves_requireReadable address size)
  intro unit
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split <;> exact preserves_pure _

/-- The source invokes bits_hash on a private world and discards its resulting
state. Thus no assumption about private execution effects is needed to show
that the caller's caller world is unchanged. -/
theorem preserves_masked_bits_hash (address : Word) (dt : Datatype) :
    PreservesWorld (masked_bits_hash address dt) := by
  unfold masked_bits_hash
  apply preserves_bind _ _ (preserves_requireReadable address (used_bytes dt))
  intro unit
  split
  · first
    | exact preserves_bits_hash address 0
    | apply preserves_bind _ _ (preserves_bits_hash address 0)
      intro value
      exact preserves_pure value
  · apply preserves_bind _ _ preserves_getWorld
    intro snapshot
    dsimp only
    split
    all_goals first
      | with_reducible exact preserves_divergent
      | with_reducible exact preserves_fail _
      | with_reducible exact preserves_pure _

end IdMissing


namespace IdMissing
open JuliaLean JuliaLean.src.identity_runtime JuliaLean.src.builtins_identity_c

theorem preserves_admissible {A : Type} :
    Lean.Order.admissible (PreservesWorld (A := A)) := by
  unfold PreservesWorld
  exact Lean.Order.admissible_pi_apply
    (P := fun (world : World) (output : Option (Except Error A × World)) =>
      ∀ result final, output = some (result, final) → final = world)
    (fun world => Lean.Order.admissible_pi
      (P := fun (output : Option (Except Error A × World)) (result : Except Error A) =>
        ∀ final, output = some (result, final) → final = world)
      (fun result => Lean.Order.admissible_pi
        (P := fun (output : Option (Except Error A × World)) (final : World) =>
          output = some (result, final) → final = world)
        (fun final => Lean.Order.Option.admissible_eq_some _ (result, final))))

theorem preserves_family_admissible {I A : Type} :
    Lean.Order.admissible (fun approximation : I → M A =>
      ∀ input, PreservesWorld (approximation input)) :=
  Lean.Order.admissible_pi_apply
    (fun (_ : I) action => PreservesWorld action)
    (fun _ => preserves_admissible)

theorem preserves_bottom {A : Type} : PreservesWorld (fun _ => none : M A) := by
  intro world result final hrun
  cases hrun

theorem preserves_objectAt (address : Word) : PreservesWorld (objectAt address) := by
  unfold objectAt
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split
  · exact preserves_pure _
  · exact preserves_fail _

theorem preserves_typename_hash (name : Word) : PreservesWorld (typename_hash name) := by
  unfold typename_hash
  apply preserves_bind _ _ preserves_getWorld
  intro snapshot
  split
  · exact preserves_pure _
  · exact preserves_fail _

theorem preserves_hash_svec_body
    (loop : Word → Nat → Nat → Word → M Word)
    (hloop : ∀ value length index hash, PreservesWorld (loop value length index hash))
    (value : Word) :
    PreservesWorld (do
      let vector ← objectAt value
      loop value vector.length 0 0) := by
  apply preserves_bind _ _ (preserves_objectAt value)
  intro vector
  exact hloop value vector.length 0 0

theorem preserves_hash_svec_loop_body
    (objectId : Word → M Word) (loop : Word → Nat → Nat → Word → M Word)
    (hobjectId : ∀ value, PreservesWorld (objectId value))
    (hloop : ∀ value length index hash, PreservesWorld (loop value length index hash))
    (value : Word) (length index : Nat) (hash : Word) :
    PreservesWorld (do
      if index ≥ length then return hash
      let x ← loadWord (value + 8 + UInt64.ofNat (8 * index))
      let component ← if x == 0 then pure 0 else objectId x
      loop value length (index + 1) (H.bitmix hash component)) := by
  by_cases hindex : index ≥ length
  · simp only [hindex, ↓reduceIte]
    exact preserves_pure hash
  · simp only [hindex, ↓reduceIte]
    apply preserves_bind _ _ (preserves_loadWord (value + 8 + UInt64.ofNat (8 * index)))
    intro x
    by_cases hzero : (x == 0) = true
    · simp only [hzero, ↓reduceIte]
      first
        | exact hloop value length (index + 1) (H.bitmix hash 0)
        | apply preserves_bind _ _ (preserves_pure 0)
          intro component
          exact hloop value length (index + 1) (H.bitmix hash component)
    · simp only [hzero, ↓reduceIte]
      apply preserves_bind _ _ (hobjectId x)
      intro component
      exact hloop value length (index + 1) (H.bitmix hash component)

theorem preserves_hash_parameters_body
    (typeId : Word → VarIndices → M Word)
    (parameters : Word → Nat → Nat → Word → VarIndices → M Word)
    (htypeId : ∀ value env, PreservesWorld (typeId value env))
    (hparameters : ∀ address length index hash env,
      PreservesWorld (parameters address length index hash env))
    (address : Word) (length index : Nat) (hash : Word) (env : VarIndices) :
    PreservesWorld (do
      if index ≥ length then return hash
      let parameter ← loadWord (address + 8 + UInt64.ofNat (8 * index))
      let component ← typeId parameter env
      parameters address length (index + 1) (H.bitmix hash component) env) := by
  by_cases hindex : index ≥ length
  · simp only [hindex, ↓reduceIte]
    exact preserves_pure hash
  · simp only [hindex, ↓reduceIte]
    apply preserves_bind _ _ (preserves_loadWord (address + 8 + UInt64.ofNat (8 * index)))
    intro parameter
    apply preserves_bind _ _ (htypeId parameter env)
    intro component
    exact hparameters address length (index + 1) (H.bitmix hash component) env

theorem preserves_object_id_tag_body
    (cold : Word → Word → M Word)
    (hcold : ∀ tag value, PreservesWorld (cold tag value))
    (tag value : Word) :
    PreservesWorld (do
      if tagKind tag == .symbol then return (← objectAt value).hash
      if tagKind tag == .datatype then
        let dt ← datatypeAt value
        if dt.hash != 0 then return dt.hash
      if tag == (← getWorld).globals.typenameType then return ← typename_hash value
      cold tag value) := by
  have htail : PreservesWorld (do
      if tag == (← getWorld).globals.typenameType then return ← typename_hash value
      cold tag value) := by
    apply preserves_bind _ _ preserves_getWorld
    intro snapshot
    by_cases htypename : (tag == snapshot.globals.typenameType) = true
    · simp only [htypename, ↓reduceIte]
      first
        | with_reducible exact preserves_typename_hash value
        | (apply preserves_bind _ _ (preserves_typename_hash value)
           intro hash
           exact preserves_pure hash)
    · simp only [htypename, ↓reduceIte]
      exact hcold tag value
  by_cases hsymbol : (tagKind tag == .symbol) = true
  · simp only [hsymbol, ↓reduceIte]
    apply preserves_bind _ _ (preserves_objectAt value)
    intro object
    exact preserves_pure object.hash
  · simp only [hsymbol, ↓reduceIte]
    by_cases hdatatype : (tagKind tag == .datatype) = true
    · simp only [hdatatype, ↓reduceIte]
      apply preserves_bind _ _ (preserves_datatypeAt value)
      intro datatype
      by_cases hnonzero : (datatype.hash != 0) = true
      · simp only [hnonzero, ↓reduceIte]
        exact preserves_pure datatype.hash
      · simp only [hnonzero, ↓reduceIte]
        exact htail
    · simp only [hdatatype, ↓reduceIte]
      exact htail

theorem preserves_object_id_body
    (taggedId : Word → Word → M Word)
    (htaggedId : ∀ tag value, PreservesWorld (taggedId tag value))
    (value : Word) :
    PreservesWorld (do taggedId (← typetag value) value) := by
  apply preserves_bind _ _ (preserves_typetag value)
  intro tag
  exact htaggedId tag value

end IdMissing

end JuliaLean.ChatGPT.Batch8.Group6
namespace JuliaLean.ChatGPT.Batch9.Group17
open JuliaLean JuliaLean.Proofs.base.iddict
open JuliaLean.src.identity_runtime JuliaLean.src.builtins_identity_c
open JuliaLean.ChatGPT.Batch8.Group6.IdFrame

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem iddict_frame_objectAt (address : Word) :
    FrameApprox (objectAt address) (objectAt address) := by
  unfold objectAt
  apply frame_getWorld_then
  · intro world events; rfl
  · intro world
    split <;> first | exact frame_return _ | exact frame_failure _

theorem iddict_frame_datatypeAt (address : Word) :
    FrameApprox (datatypeAt address) (datatypeAt address) := by
  unfold datatypeAt
  apply frame_getWorld_then
  · intro world events; rfl
  · intro world
    split <;> first | exact frame_return _ | exact frame_failure _

theorem iddict_frame_toTypeof (tag : Word) :
    FrameApprox (toTypeof tag) (toTypeof tag) := by
  unfold toTypeof
  split
  · apply frame_getWorld_then
    · intro world events; rfl
    · intro world
      split
      · exact frame_return _
      · exact frame_failure _
  · exact frame_return _

theorem iddict_frame_admissible_pi {A B : Type}
    (P : B → Prop) [Lean.Order.CCPO B] (h : Lean.Order.admissible P) :
    Lean.Order.admissible (fun f : A → B => ∀ x, P (f x)) :=
  Lean.Order.admissible_pi_apply (fun _ value => P value) (fun _ => h)

theorem iddict_frame_nth_union_component :
    ∀ value index, FrameApprox (nth_union_component value index)
      (nth_union_component value index) := by
  apply nth_union_component.fixpoint_induct
    (fun f => ∀ value index, FrameApprox (f value index) (f value index))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ frame_self_admissible)
  · intro recurse ih value index
    apply frame_bind _ _ _ _ (frame_typetag value)
    intro tag
    apply frame_if
    · apply frame_bind _ _ _ _ (iddict_frame_objectAt value)
      intro union
      apply frame_bind _ _ _ _ (ih union.left index)
      intro pair
      rcases pair with ⟨found, nextIndex⟩
      apply frame_if
      · exact frame_return _
      · exact ih union.right nextIndex
    · apply frame_if
      · exact frame_return _
      · apply frame_if
        · exact frame_failure _
        · exact frame_return _

theorem iddict_frame_jl_nth_union_component (value : Word) (index : Int32) :
    FrameApprox (jl_nth_union_component value index) (jl_nth_union_component value index) := by
  unfold jl_nth_union_component
  apply frame_bind _ _ _ _ (iddict_frame_nth_union_component value index)
  intro pair
  exact frame_return pair.1


theorem iddict_frame_option {A B : Type} (option : Option A)
    (someCase : A → M B) (noneCase : M B)
    (hsome : ∀ value, FrameApprox (someCase value) (someCase value))
    (hnone : FrameApprox noneCase noneCase) :
    FrameApprox (match option with | some value => someCase value | none => noneCase)
      (match option with | some value => someCase value | none => noneCase) := by
  cases option
  · exact hnone
  · exact hsome _


theorem iddict_native_identity_frame :
    ∀ a b, FrameApprox (jl_egal_ a b) (jl_egal_ a b) := by
  apply jl_egal_.fixpoint_induct
    (fun f => ∀ a b, FrameApprox (f a b) (f a b))
    (fun f => ∀ a b l i, FrameApprox (f a b l i) (f a b l i))
    (fun f => ∀ a b, FrameApprox (f a b) (f a b))
    (fun f => ∀ a b tag, FrameApprox (f a b tag) (f a b tag))
    (fun f => ∀ a b tag, FrameApprox (f a b tag) (f a b tag))
    (fun f => ∀ a b dt, FrameApprox (f a b dt) (f a b dt))
    (fun f => ∀ a b dt, FrameApprox (f a b dt) (f a b dt))
    (fun f => ∀ a b env names, FrameApprox (f a b env names) (f a b env names))
    (fun f => ∀ a b l i env names, FrameApprox (f a b l i env names) (f a b l i env names))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible))))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible)))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible)))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible)))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible)))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible))))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (frame_self_admissible))))))
  · intro loop hloop a b
    apply frame_bind _ _ _ _ (iddict_frame_objectAt a)
    intro va
    apply frame_bind _ _ _ _ (iddict_frame_objectAt b)
    intro vb
    apply frame_if
    · exact frame_return false
    · exact hloop a b va.length 0
  · intro loop egal hloop hegal a b length index
    exact frame_compare_svec_loop_self_body egal loop hegal hloop a b length index
  · intro unboxed hunboxed a b
    exact frame_jl_egal_self_body unboxed hunboxed a b
  · intro bitstag hbitstag a b tag
    dsimp only
    apply frame_if
    · apply frame_if
      · exact frame_return false
      · exact hbitstag a b tag
    · apply frame_bind _ _ _ _ (iddict_frame_datatypeAt tag)
      intro dt
      apply frame_if
      · exact frame_return false
      · exact hbitstag a b tag
  · intro svec bits fields types hsvec hbits hfields htypes a b tag
    apply frame_if
    · cases tagKind tag <;>
        first
        | exact frame_bits_equal a b _
        | exact frame_return false
        | exact frame_failure _
        | exact hsvec a b
        | exact htypes a b [] true
        | skip
      all_goals
        repeat first
          | assumption
          | exact frame_return _
          | exact frame_failure _
          | exact frame_bits_equal _ _ _
          | exact iddict_frame_datatypeAt _
          | exact iddict_frame_objectAt _
          | exact iddict_frame_toTypeof _
          | exact hfields _ _ _
          | exact hsvec _ _
          | apply frame_if
          | apply frame_getWorld_then (hevents := by intro world events; rfl)
          | apply frame_bind
          | intro value
    · apply frame_bind _ _ _ _ (iddict_frame_datatypeAt tag)
      intro dt
      exact hbits a b dt
  · intro fields hfields a b dt
    exact frame_jl_egal_bits_self_body fields hfields a b dt
  · intro egal fields hegal hfields a b dt
    repeat first
      | assumption
      | exact frame_return _
      | exact frame_failure _
      | exact frame_bits_equal _ _ _
      | exact frame_primitive_bits_equal _ _ _
      | exact iddict_frame_datatypeAt _
      | exact iddict_frame_objectAt _
      | exact iddict_frame_toTypeof _
      | exact iddict_frame_jl_nth_union_component _ _
      | exact frame_typetag _
      | exact frame_loadWord _
      | exact frame_loadByte _
      | exact hegal _ _
      | exact hfields _ _ _
      | apply frame_if
      | apply iddict_frame_option
      | apply frame_forIn
      | apply frame_getWorld_then (hevents := by intro world events; rfl)
      | apply frame_bind
      | intro value
  · intro bitstag types parameters hbitstag htypes hparameters a b env names
    repeat first
      | assumption
      | exact frame_return _
      | exact frame_failure _
      | exact frame_bits_equal _ _ _
      | exact frame_primitive_bits_equal _ _ _
      | exact iddict_frame_datatypeAt _
      | exact iddict_frame_objectAt _
      | exact iddict_frame_toTypeof _
      | exact iddict_frame_jl_nth_union_component _ _
      | exact frame_typetag _
      | exact frame_loadWord _
      | exact frame_loadByte _
      | exact hbitstag _ _ _
      | exact htypes _ _ _ _
      | exact hparameters _ _ _ _ _ _
      | apply frame_if
      | apply iddict_frame_option
      | apply frame_forIn
      | apply frame_getWorld_then (hevents := by intro world events; rfl)
      | apply frame_bind
      | intro value
  · intro types parameters htypes hparameters a b length index env names
    exact frame_egal_parameters_self_body types parameters htypes hparameters a b length index env names


open JuliaLean.ChatGPT.Batch8.Group6.IdMissing

theorem iddict_preserves_jl_nth_union_component (value : Word) (index : Int32) :
    PreservesWorld (jl_nth_union_component value index) := by
  intro world result final run
  exact (iddict_frame_jl_nth_union_component value index world result final run).1

theorem iddict_preserves_option {A B : Type} (option : Option A)
    (someCase : A → M B) (noneCase : M B)
    (hsome : ∀ value, PreservesWorld (someCase value))
    (hnone : PreservesWorld noneCase) :
    PreservesWorld (match option with | some value => someCase value | none => noneCase) := by
  cases option
  · exact hnone
  · exact hsome _

set_option maxHeartbeats 100000 in
theorem iddict_native_hash_preserves :
    ∀ value, PreservesWorld (jl_object_id value) := by
  apply jl_object_id.fixpoint_induct
    (fun f => ∀ value, PreservesWorld (f value))
    (fun f => ∀ value length index hash, PreservesWorld (f value length index hash))
    (fun f => ∀ value, PreservesWorld (f value))
    (fun f => ∀ tag value, PreservesWorld (f tag value))
    (fun f => ∀ tag value, PreservesWorld (f tag value))
    (fun f => ∀ dt value hash, PreservesWorld (f dt value hash))
    (fun f => ∀ value env, PreservesWorld (f value env))
    (fun f => ∀ value length index hash env, PreservesWorld (f value length index hash env))
  · exact iddict_frame_admissible_pi _ (preserves_admissible)
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (preserves_admissible))))
  · exact iddict_frame_admissible_pi _ (preserves_admissible)
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (preserves_admissible))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (preserves_admissible))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (preserves_admissible)))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (preserves_admissible))
  · exact iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (iddict_frame_admissible_pi _ (preserves_admissible)))))
  · intro loop hloop value
    exact preserves_hash_svec_body loop hloop value
  · intro loop objectId hloop hobjectId value length index hash
    exact preserves_hash_svec_loop_body objectId loop hobjectId hloop value length index hash
  · intro tagged htagged value
    exact preserves_object_id_body tagged htagged value
  · intro cold hcold tag value
    exact preserves_object_id_tag_body cold hcold tag value
  · intro svec immut hsvec himmut tag value
    repeat first
      | with_reducible assumption
      | with_reducible exact preserves_pure _
      | with_reducible exact preserves_fail _
      | with_reducible exact preserves_bits_hash _ _
      | with_reducible exact preserves_masked_bits_hash _ _
      | with_reducible exact preserves_datatypeAt _
      | with_reducible exact preserves_objectAt _
      | with_reducible exact preserves_toTypeof _
      | with_reducible exact preserves_typeof _
      | with_reducible exact iddict_preserves_jl_nth_union_component _ _
      | with_reducible exact preserves_typetag _
      | with_reducible exact preserves_loadWord _
      | with_reducible exact preserves_loadByte _
      | with_reducible exact preserves_requireReadable _ _
      | with_reducible exact preserves_typename_hash _
      | with_reducible exact preserves_getWorld
      | with_reducible exact hsvec _
      | with_reducible exact himmut _ _ _
      | with_reducible apply preserves_if
      | apply iddict_preserves_option
      | with_reducible apply preserves_forIn
      | with_reducible apply preserves_bind
      | with_reducible intro value
  · intro objectId immut typeId hobjectId himmut htypeId dt value hash
    repeat first
      | with_reducible assumption
      | with_reducible exact preserves_pure _
      | with_reducible exact preserves_fail _
      | with_reducible exact preserves_bits_hash _ _
      | with_reducible exact preserves_masked_bits_hash _ _
      | with_reducible exact preserves_datatypeAt _
      | with_reducible exact preserves_objectAt _
      | with_reducible exact preserves_toTypeof _
      | with_reducible exact preserves_typeof _
      | with_reducible exact iddict_preserves_jl_nth_union_component _ _
      | with_reducible exact preserves_typetag _
      | with_reducible exact preserves_loadWord _
      | with_reducible exact preserves_loadByte _
      | with_reducible exact preserves_requireReadable _ _
      | with_reducible exact preserves_typename_hash _
      | with_reducible exact preserves_getWorld
      | with_reducible exact hobjectId _
      | with_reducible exact himmut _ _ _
      | with_reducible exact htypeId _ _
      | with_reducible apply preserves_if
      | apply iddict_preserves_option
      | with_reducible apply preserves_forIn
      | with_reducible apply preserves_bind
      | with_reducible intro value
  · intro objectId immut typeId parameters hobjectId himmut htypeId hparameters value env
    repeat first
      | with_reducible assumption
      | with_reducible exact preserves_pure _
      | with_reducible exact preserves_fail _
      | with_reducible exact preserves_bits_hash _ _
      | with_reducible exact preserves_masked_bits_hash _ _
      | with_reducible exact preserves_datatypeAt _
      | with_reducible exact preserves_objectAt _
      | with_reducible exact preserves_toTypeof _
      | with_reducible exact preserves_typeof _
      | with_reducible exact iddict_preserves_jl_nth_union_component _ _
      | with_reducible exact preserves_typetag _
      | with_reducible exact preserves_loadWord _
      | with_reducible exact preserves_loadByte _
      | with_reducible exact preserves_requireReadable _ _
      | with_reducible exact preserves_typename_hash _
      | with_reducible exact preserves_getWorld
      | with_reducible exact hobjectId _
      | with_reducible exact himmut _ _ _
      | with_reducible exact htypeId _ _
      | with_reducible exact hparameters _ _ _ _ _
      | with_reducible apply preserves_if
      | apply iddict_preserves_option
      | with_reducible apply preserves_forIn
      | with_reducible apply preserves_bind
      | with_reducible intro value
  · intro typeId parameters htypeId hparameters value length index hash env
    exact preserves_hash_parameters_body typeId parameters htypeId hparameters value length index hash env

theorem IddictIndexMissingV2_proven : JuliaLean.Proofs.base.iddict.Round1.MissingIdentityKeyError := by
  apply missing_index_reduction
  · intro query stored world result final run
    exact (iddict_native_identity_frame query stored world result final run).1
  · intro query stored world value run events
    exact (iddict_native_identity_frame query stored world (.ok value) world run).2 events
  · exact iddict_native_hash_preserves

end JuliaLean.ChatGPT.Batch9.Group17

namespace JuliaLean.Proofs.base.iddict
open JuliaLean.Registry

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

def entries : List Entry := [
  { (entry "iddicts-ops-agree"
    ["setindex!(::IdDict,v,k)", "delete!(::IdDict,k)", "pop!(::IdDict,k)",
      "pop!(::IdDict,k,default)", "empty!(::IdDict)", "sizehint!(::IdDict,n)",
      "get(::IdDict,k,default)", "length(::IdDict)", "iterate(::IdDict)"]
    "After any sequence of IdDict mutations, get, length, and iteration agree with a reference map keyed by `===`; key and value types follow `K` and `V`."
    "IdDict docstring base/iddict.jl:6-8; setindex! base/iddict.jl:79-92"
    ``IdDictOpsAgree) with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch8.Group4.IddictsOpsAgree_refuted, issue := "Related JuliaLang/julia#34821 (open PR) proposes removing secret_table_token; paced issue and PR searches found no exact duplicate.", notes := "" },
  { (entry "iddicts-length-live"
    ["length(::IdDict)", "iterate(::IdDict)", "get!(::IdDict,k,default)",
      "get!(f,::IdDict,k)", "pop!(::IdDict,k)"]
    "After any IdDict calls, including get! and pop! on stored sentinels, iteration yields exactly length(d) pairs with pairwise non-`===` keys."
    "Invariant; base/iddict.jl:90,111-112,147"
    ``IdDictLengthLive) with notes := "Statement gap: Pair construction and decoding callbacks need correct, nonmutating iteration contracts. The returned witness uses method piracy and an internal sentinel and is excluded; no Julia bug established." },
  { (entry "iddicts-getbang-absent"
    ["get!(::IdDict,k,default)"]
    "For an absent key of type `K`, get!(d,k,default) stores and returns `convert(V,default)` and increases length by one."
    "get! docstring base/dict.jl:393-394"
    ``IdDictGetBangAbsent) with notes := "Statement gap: a deliberately mutating conversion can delete another entry before insertion, invalidating the initial-count formula. Conversion correctness and noninterference laws are missing; the returned internal-token witness is excluded." },
  { (entry "iddicts-token-lookup"
    ["haskey(::IdDict,k)", "in(k,::KeySet{<:Any,<:IdDict})", "getindex(::IdDict,k)"]
    "If no stored value is the secret token, stored values pass their type assertions, the token is a valid native Symbol, and type-assertion outcomes depend only on value and type, every identity-key present in iteration is reported present by haskey's KeySet test and indexing returns its stored value."
    "haskey docstring base/dict.jl:537; KeyError docstring base/abstractdict.jl:5-9"
    ``LookupFindsPresent) with notes := "Restated 2026-11-03 per Miles: the internal secret_table_token sentinel is excluded; a token collision is not a Julia bug. Native identity/hash correspondence and present-key probe correctness remain unproved." },
  { (entry "iddicts-token-pop"
    ["pop!(::IdDict,k)"]
    "If no stored value is the secret token, stored values pass their type assertions, the token is a valid native Symbol, and type-assertion outcomes depend only on value and type, pop!(d,k) returns the stored value of every present key."
    "pop! docstring base/dict.jl:594-595"
    ``PopReturnsPresent) with notes := "Restated 2026-11-03 per Miles: the internal secret_table_token sentinel is excluded; a token collision is not a Julia bug. Native present-key lookup/deletion correspondence and type-assertion heap preservation remain unproved." },
  { (entry "iddicts-token-getbang"
    ["get!(::IdDict,k,default)", "get!(f,::IdDict,k)"]
    "If no stored value is the secret token, stored values pass their type assertions, the token is a valid native Symbol, and type-assertion outcomes depend only on value and type, get! on a present key returns its stored value and leaves the dictionary contents unchanged without calling a callable default."
    "get! docstring base/dict.jl:393-394"
    ``GetBangKeepsPresent) with notes := "Restated 2026-11-03 per Miles: the internal secret_table_token sentinel is excluded; a token collision is not a Julia bug. Native present-key lookup correspondence and type-assertion heap preservation remain unproved." },
  { (entry "iddict-empty-constructors"
    ["IdDict{K,V}()@31", "IdDict()@52", "IdDict(::Tuple{})@53",
      "empty(::IdDict,::Type{K},::Type{V})@62"]
    "Each empty IdDict constructor creates a 32-word table with zero live and deleted counts."
    "IdDict constructor and empty invariants; base/iddict.jl:31,52-53,62"
    ``EmptyConstructors) with notes := "Allocator and newObject callbacks lack the size, zero-initialization, field-correctness and freshness laws needed for the typed constructor; wrapper lemmas alone do not prove the universal claim." },
  { (entry "iddict-empty-bang"
    ["empty!(::IdDict)@128"]
    "empty! clears all pairs, replaces the table with 32 words, resets both counts, and returns the dictionary."
    "IdDict table invariant; base/iddict.jl:128-137"
    ``EmptyBangContents) with status := .todo, thm := none, notes := "The clearing trace needs a correctly sized, fresh, nonoverlapping allocation to establish the empty table and changed storage pointer; the allocator callback has no such contract." },
  { (entry "iddict-pair-constructors"
    ["IdDict{K,V}(pairs::Pair...)@42", "IdDict(ps::Pair{K,V}...)@55",
      "IdDict(ps::Pair{K}...)@56", "IdDict(ps::(Pair{K,V} where K)...)@57",
      "IdDict(ps::Pair...)@58"]
    "Pair constructors retain the last value for each `===` key, converting each value to the selected `V` type."
    "IdDict constructor docstring base/iddict.jl:6-8; pair constructors base/iddict.jl:42-58"
    ``PairConstructors) with status := .todo, thm := none, notes := "Statement/prose mismatch: pairReference replays conversion from the final world, so a stateful converter can disagree with its correctly stored earlier result. Record actual conversion outcomes or supply repeatability laws; no constructor bug claimed." },
  { (entry "iddict-iterator-constructor"
    ["IdDict{K,V}(itr)@33"]
    "The iterator constructor optionally size-hints length or shape iterators and inserts every yielded pair in iteration order."
    "IdDict constructor docstring base/iddict.jl:6-8; base/iddict.jl:33-40"
    ``IteratorConstructor) with status := .todo, thm := none, notes := "Statement/prose mismatch: pairReference replays conversion from the final world rather than recording conversion during insertion. Stateful conversion can change the replay without incorrect Julia storage; no constructor bug claimed." },
  { (entry "iddict-eltype-constructor"
    ["IdDict(kv)@60"]
    "The generic IdDict constructor selects key and value types from `eltype(kv)`."
    "IdDict constructor docstring base/iddict.jl:6-8; base/iddict.jl:60"
    ``EltypeConstructor) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group16.IddictEltypeConstructor_proven },
  { (entry "iddict-copy-contents"
    ["IdDict{K,V}(d::IdDict{K,V})@49", "copy(d::IdDict)@149"]
    "Copying preserves every key-value association and both counts while creating independent table memory."
    "Copy invariant; base/iddict.jl:49,149"
    ``CopyPreservesContents) with status := .todo, thm := none, notes := "The copy callback lacks correctness and noninterference laws. The returned witness pirates copy(::Memory{Any}) to mutate the source; this does not establish a bug in the ordinary Julia copy implementation." },
  { (entry "iddict-rehash-sizehint-contents"
    ["rehash!(::IdDict,n)@64", "sizehint!(::IdDict,n)@69"]
    "Rehashing preserves all associations and counts at the requested capacity; sizehint keeps the current table below the 25 percent growth threshold and otherwise grows to the computed table size."
    "IdDict table invariants and sizehint comment; base/iddict.jl:64-77"
    ``RehashSizehintPreservesContents) with status := .todo, thm := none, notes := "Custom Integer arithmetic callbacks lack correctness and noninterference laws. A deliberately mutating multiplication deletes the entry in the returned witness; this does not establish a sizehint! bug." },
  { (entry "iddict-setindex-types"
    ["setindex!(::IdDict{K,V},v,k)@79"]
    "setindex! converts values to `V`, stores them under identity keys, and increments the live count only for a new key."
    "IdDict docstring base/iddict.jl:6-8; base/iddict.jl:79-92"
    ``SetindexTypeAndValue) with status := .todo, thm := none, notes := "A deliberately mutating conversion changes the initial dictionary before insertion; the target needs conversion correctness/noninterference and an appropriate state-relative reference. The returned internal-token witness is excluded." },
  { (entry "iddict-setindex-keytype"
    ["setindex!(::IdDict{K,V},v,k)@79"]
    "setindex! throws KeyTypeError before changing the table when the key is not of type `K`."
    "IdDict key type contract; base/iddict.jl:79-80"
    ``SetindexRejectsInvalidKey) with status := .todo, thm := none, notes := "The isa callback may change the world while returning false; the target requires unchanged contents without a read-only isa law. Actual builtin isa is not a user-controlled mutation callback." },
  { (entry "iddict-pop-counts"
    ["pop!(::IdDict,k,default)@105", "pop!(::IdDict,k)@117", "delete!(::IdDict,k)@123"]
    "Removing a present key decrements length and increments the deleted-slot count; missing pop! throws KeyError, while missing defaulted pop! and delete! leave counts unchanged."
    "pop! docstring base/dict.jl:594-595; table invariant base/iddict.jl:105-126"
    ``PopAndDeleteCounters) with status := .todo, thm := none, notes := "Physical invariants do not establish stored-value type assertions or read-only isa behavior; native representation and lookup/reference deletion correspondence are also needed. Malformed callbacks are not Julia counterexamples." },
  { (entry "iddict-index-missing"
    ["getindex(::IdDict,k)@99"]
    "Indexing a key absent by identity throws KeyError containing that key."
    "KeyError docstring base/abstractdict.jl:5-9; base/iddict.jl:99-103"
    ``MissingGetindexKeyError) with notes := "The original proposition omits Round1.NativeRepresentation, including the nonnull table pointer and native nothing tag required by physical lookup. The strengthened missing-key-v2 target is settled separately." },
  { (entry "iddict-callable-get"
    ["get(default::Callable,::IdDict,k)@162"]
    "If no stored value is the secret token, stored values pass their type assertions, and the token is a valid native Symbol, callable get returns a present value without calling its default; for a missing key, it agrees with the default on the returned value and dictionary contents."
    "get docstring; base/iddict.jl:162-169"
    ``CallableGet) with notes := "Restated 2026-11-03 per Miles: the internal secret_table_token sentinel is excluded; a token collision is not a Julia bug. The default may inspect native load events and change its returned value; a callback interface that hides internal trace events is missing." },
  { (entry "iddict-callable-getbang"
    ["get!(default::Callable,::IdDict,k)@171"]
    "For an absent valid key, callable get! invokes its default, converts and stores the result, returns it, and increases length by one."
    "get! docstring base/dict.jl:393-394; base/iddict.jl:171-183"
    ``CallableGetBang) with status := .todo, thm := none, notes := "Statement/prose mismatch: CallableGetBang also quantifies over present keys, while the entry describes absent keys. The returned witness uses the internal secret_table_token sentinel and is excluded; missing callback laws remain." },
  { id := "iddict-index-missing-v2", juliaFile := "base/iddict.jl",
    juliaFns := ["getindex(::IdDict,k)"],
    statement := "Indexing an identity key absent from a physically valid native IdDict throws KeyError containing that key.",
    source := "base/iddict.jl:99-103; base/abstractdict.jl:5-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.iddict.Round1.MissingIdentityKeyError, thm := some ``JuliaLean.ChatGPT.Batch9.Group17.IddictIndexMissingV2_proven }
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

end
end JuliaLean.Proofs.base.iddict
