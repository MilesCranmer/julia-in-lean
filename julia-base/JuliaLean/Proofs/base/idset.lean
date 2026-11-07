import JuliaLean.Proofs.base.idset.collection_rows
import JuliaLean.base.idset
import JuliaLean.Proofs.base.iddict
import JuliaLean.Registry.Types

/-! Native IdSet restatements. S1 allocation, S2 boxed copying, S3 subtype
checking and S4 generic iteration/set dispatch remain explicit gaps. -/
namespace JuliaLean.Proofs.base.idset
open JuliaLean JuliaLean.Registry
open JuliaLean.src.identity_runtime (Word World Memory M Error)
namespace S
export JuliaLean.base.idset (Callees SetFields fields emptyTyped emptyAny copyConstruct
  copymutable emptymutable emptymutableAs copy fromIterator haskey «in» length isempty
  push! _pop! pop! popDefault delete! sizehint! _zero! empty! filter! iterate)
end S
namespace P
export JuliaLean.Proofs.base.iddict (outcome succeeds returns identical validValue keysDistinct)
end P
namespace N
export JuliaLean.src.identity_runtime (plainReadCell)
end N
noncomputable section

def members (address : Word) : M (List Word) := do
  let fields ← S.fields address
  let mut values := []
  for index in List.range fields.list.length do
    let value ← N.plainReadCell fields.list (UInt64.ofNat index)
    if value != 0 then values := values ++ [value]
  pure values

def containsIdentity : List Word → Word → M Bool
  | [], _ => pure false
  | value :: rest, query => do
    if ← JuliaLean.src.builtins_identity_c.jl_egal_ query value then pure true
    else containsIdentity rest query

def readableMemory (world : World) (memory : Memory) (width : Nat) : Prop :=
  memory.length < 2^63 ∧ memory.ptr+width*memory.length ≤ 2^64 ∧
  ∀ offset < width*memory.length, world.raw.heap.validByte (memory.ptr+offset) = true

def cacheCell (calls : S.Callees) (memory : Memory) (index : Nat) : M Word :=
  JuliaLean.src.smallintset_c.jl_intref_acquire calls.indices memory (UInt64.ofNat index)

/-- Cache entries hold one-based key-slot indices. Hash clusters have no
empty cell before an occupied slot within the C lookup probe limit. -/
def indexPlacement (calls : S.Callees) (world : World) (fields : S.SetFields) : Prop :=
  (∀ slot < fields.indices.length, ∃ stored,
    P.succeeds (cacheCell calls fields.indices slot) world stored ∧
    (stored = 0 ∨ stored = ~~~(0 : Word) ∨
      ∃ key, 0 < stored.toNat ∧ stored.toNat ≤ fields.list.length ∧ key ≠ 0 ∧
        P.succeeds (N.plainReadCell fields.list (stored-1)) world key)) ∧
  (∀ index < fields.list.length, ∀ key,
    P.succeeds (N.plainReadCell fields.list (UInt64.ofNat index)) world key →
    key ≠ 0 → ∃ hash distance,
      P.succeeds (JuliaLean.src.builtins_identity_c.jl_object_id key) world hash ∧
      0 < fields.indices.length ∧ distance < fields.indices.length ∧
      distance ≤ (JuliaLean.src.iddict_c.max_probe (UInt64.ofNat fields.indices.length)).toNat ∧
      P.succeeds (cacheCell calls fields.indices
        ((hash.toNat % fields.indices.length+distance) % fields.indices.length))
        world (UInt64.ofNat (index+1)) ∧
      (∀ step < distance, ∃ previous, previous ≠ 0 ∧
        P.succeeds (cacheCell calls fields.indices
          ((hash.toNat % fields.indices.length+step) % fields.indices.length)) world previous) ∧
      (∀ slot < fields.indices.length,
        P.succeeds (cacheCell calls fields.indices slot) world (UInt64.ofNat (index+1)) →
        slot = (hash.toNat % fields.indices.length+distance) % fields.indices.length))

def IdSetWellFormed (calls : S.Callees) (world : World) (address : Word) : Prop :=
  ∃ fields values width,
    P.succeeds (S.fields address) world fields ∧ P.succeeds (members address) world values ∧
    0 ≤ fields.count.val ∧ 0 ≤ fields.maximum.val ∧
    fields.maximum.val < 0x7fffffff ∧ fields.maximum.val ≤ Int.ofNat fields.list.length ∧
    fields.count.val = Int.ofNat values.length ∧ fields.count.val ≤ fields.maximum.val ∧
    fields.list.metadata.memoryLayout.size.val = 8 ∧ readableMemory world fields.list 8 ∧
    P.succeeds (JuliaLean.src.smallintset_c.elementWidth calls.indices fields.indices false) world width ∧
    JuliaLean.src.genericmemory_c.isBoxed fields.list.metadata = true ∧
    (width = 1 ∨ width = 2 ∨ width = 4) ∧ readableMemory world fields.indices width ∧
    (fields.indices.length = 0 ∨ ∃ exponent : Nat, fields.indices.length = 2^exponent) ∧
    P.keysDistinct world (values.map fun value => (value, (0 : Word))) ∧
    (∀ value ∈ values, P.validValue world value) ∧
    (∀ index, fields.maximum.val.toNat ≤ index → index < fields.list.length →
      P.succeeds (N.plainReadCell fields.list (UInt64.ofNat index)) world 0) ∧
    indexPlacement calls world fields

def IdSetEmpty (world : World) (address : Word) : Prop :=
  ∃ fields, P.succeeds (S.fields address) world fields ∧
    fields.count.val = 0 ∧ fields.maximum.val = 0 ∧ P.succeeds (members address) world []

def SameMembers (calls : S.Callees) (left right : World) (leftAddress rightAddress : Word) : Prop :=
  ∀ query, P.validValue left query →
    P.outcome (S.haskey calls leftAddress query) left =
      P.outcome (S.haskey calls rightAddress query) right

def collectIteration (calls : S.Callees) (address : Word)
    (state : JInt .i64 := JInt.wrap .i64 0) : M (List Word) := do
  match ← S.iterate calls address state with
  | none => pure []
  | some (value, next) => return value :: (← collectIteration calls address next)
partial_fixpoint

def IdSetBasicSpec : Prop :=
  ∀ calls world address elementType iterator (iteratorValues : Word → M (List Word)),
    (P.returns (S.emptyTyped calls elementType) world (fun result final => IdSetEmpty final result)) ∧
    (P.returns (S.emptyAny calls) world (fun result final => IdSetEmpty final result)) ∧
    (P.returns (S.emptymutable calls address) world (fun result final => IdSetEmpty final result)) ∧
    (P.returns (S.emptymutableAs calls address elementType) world
      (fun result final => IdSetEmpty final result)) ∧
    (IdSetWellFormed calls world address →
      P.returns (S.copyConstruct calls address) world
        (fun result final => SameMembers calls world final address result) ∧
      P.returns (S.copy calls address) world
        (fun result final => SameMembers calls world final address result) ∧
      P.returns (S.copymutable calls address) world
        (fun result final => SameMembers calls world final address result) ∧
      (∀ values, P.succeeds (members address) world values →
        (∀ query, P.validValue world query →
          P.outcome (S.haskey calls address query) world = P.outcome (containsIdentity values query) world ∧
          P.outcome (S.«in» calls query address) world = P.outcome (containsIdentity values query) world) ∧
        P.succeeds (S.length address) world (JInt.wrap .i64 (Int.ofNat values.length)) ∧
        P.succeeds (S.isempty address) world values.isEmpty)) ∧
    (∀ values, P.succeeds (iteratorValues iterator) world values →
      P.returns (S.fromIterator calls elementType iterator) world fun result final =>
        ∀ query, P.validValue final query →
          P.outcome (S.haskey calls result query) final = P.outcome (containsIdentity values query) final)

def removalPost (calls : S.Callees) (before final : World) (address key : Word)
    (initial : S.SetFields) (present : Bool) : Prop :=
  P.succeeds (S.haskey calls address key) final false ∧
  (∃ after, P.succeeds (S.fields address) final after ∧
    after.count.val = initial.count.val-(if present then 1 else 0) ∧
    0 ≤ after.maximum.val ∧ after.maximum.val ≤ initial.maximum.val) ∧
  (∀ query, P.validValue before query →
    P.succeeds (JuliaLean.src.builtins_identity_c.jl_egal_ query key) before false →
    P.outcome (S.haskey calls address query) final = P.outcome (S.haskey calls address query) before)

/-- The public pop/delete methods use the concrete C lookup, tombstone and
key-clearing code. None calls the remaining allocation, copy, subtype or set-dispatch gaps. -/
def IdSetPopSpec : Prop :=
  ∀ calls world address key fallback initial,
    IdSetWellFormed calls world address → P.validValue world key →
    P.succeeds (S.fields address) world initial →
    ∃ present, P.succeeds (S.haskey calls address key) world present ∧
      (∃ index final, S._pop! calls address key world = some (.ok index, final) ∧
        (if present then 0 ≤ index.val else index.val = -1) ∧
        removalPost calls world final address key initial present) ∧
      (∃ final, S.pop! calls address key world =
        some ((if present then .ok key else .error (.keyError key)), final) ∧
        removalPost calls world final address key initial present) ∧
      (∃ final, S.popDefault calls address key fallback world =
        some (.ok (if present then key else fallback), final) ∧
        removalPost calls world final address key initial present) ∧
      (∃ final, S.delete! calls address key world = some (.ok address, final) ∧
        removalPost calls world final address key initial present)

def IdSetOpsAgree : Prop :=
  ∀ calls world address key iterator (iteratorValues : Word → M (List Word)),
    IdSetWellFormed calls world address → P.validValue world key →
    (P.returns (S.push! calls address key) world fun result final =>
      result = address ∧ IdSetWellFormed calls final address ∧
      ∀ query, P.validValue final query →
        P.outcome (S.haskey calls address query) final =
          P.outcome (do return (← S.haskey calls address query) ||
            (← JuliaLean.src.builtins_identity_c.jl_egal_ query key)) world) ∧
    (P.returns (S.delete! calls address key) world fun result final =>
      result = address ∧ P.succeeds (S.haskey calls address key) final false) ∧
    (P.returns (S.empty! address) world fun result final => result = address ∧ IdSetEmpty final address) ∧
    (∀ size, P.returns (S.sizehint! address size) world
      (fun _ final => SameMembers calls world final address address)) ∧
    (∀ values, P.succeeds (iteratorValues iterator) world values →
      P.returns (calls.union address iterator) world (fun result final =>
        ∀ query, P.validValue final query →
          P.outcome (S.haskey calls result query) final =
            P.outcome (do return (← S.haskey calls address query) || (← containsIdentity values query)) world) ∧
      P.returns (calls.setdiff address iterator) world (fun result final =>
        ∀ query, P.validValue final query →
          P.outcome (S.haskey calls result query) final =
            P.outcome (do return (← S.haskey calls address query) && !(← containsIdentity values query)) world)) ∧
    (∀ values, P.succeeds (collectIteration calls address) world values →
      P.keysDistinct world (values.map fun value => (value, (0 : Word))) ∧
      ∀ query, P.validValue world query →
        P.outcome (containsIdentity values query) world = P.outcome (S.haskey calls address query) world)

def IdSetElemsHaveEltype : Prop :=
  ∀ calls world address,
    IdSetWellFormed calls world address →
    ∃ values, P.succeeds (collectIteration calls address) world values

def zeroBytes (world : World) (memory : Memory) : Prop :=
  ∀ offset < memory.metadata.memoryLayout.size.val.toNat*memory.length,
    (world.raw.heap.readByte (memory.ptr+offset)).val = 0

def IdSetZeroBytesSpec : Prop :=
  ∀ world memory,
    readableMemory world memory memory.metadata.memoryLayout.size.val.toNat →
    P.returns (S._zero! memory) world fun result final =>
      result = memory ∧ zeroBytes final memory ∧
      ∀ address, address < memory.ptr ∨
        memory.ptr+memory.metadata.memoryLayout.size.val.toNat*memory.length ≤ address →
        final.raw.heap.readByte address = world.raw.heap.readByte address

def IdSetMemorySpec : Prop :=
  IdSetZeroBytesSpec ∧
  (∀ calls world address predicate before,
    IdSetWellFormed calls world address → P.succeeds (members address) world before →
    P.returns (S.filter! calls predicate address) world fun result final =>
      ∀ query, P.validValue final query →
        P.outcome (S.haskey calls result query) final =
          P.outcome (do return (← S.haskey calls address query) && (← predicate query)) world) ∧
  (∀ calls world address before,
    IdSetWellFormed calls world address → P.succeeds (S.fields address) world before →
    P.returns (S.empty! address) world fun result final =>
      result = address ∧ IdSetEmpty final address ∧ zeroBytes final before.indices)

end

namespace EltypeCounterexample
open JuliaLean.src.identity_runtime

def keys : Memory :=
  ⟨520, 1, { JuliaLean.src.genericmemory_c.boxedDictLayout.metadata with owner := 512 }⟩

def indices : Memory :=
  let metadata := JuliaLean.src.genericmemory_c.boxedDictLayout.metadata
  ⟨776, 1, { metadata with
    owner := 768
    runtimeType := { metadata.runtimeType with
      identity := 30000
      layout := JuliaLean.src.genericmemory_c.genericMemoryHeader 1 1 0 (-1) } }⟩

def setFields : S.SetFields := ⟨keys, indices, JInt.wrap .i64 1, JInt.wrap .i64 1, 28672⟩

/-- A one-element Bool-typed set containing a Symbol, matching the saved
public push!/iterate TypeError reproducer. Its native index points to slot 1. -/
def world : World where
  raw := { heap := {
    byteAt := fun address => JInt.wrap .u8 (match address with
      | 249 => 16 | 257 => 2 | 265 => 3 | 272 => 1 | 280 => 1
      | 521 => 4 | 760 => 48 | 761 => 117 | 776 => 1
      | 1016 => 32 | 1017 => 1 | 1545 => 112 | _ => 0)
    validByte := fun _ => true }, events := [] }
  objects := fun address => if address == 1024 then some { hash := 7 } else none
  datatypes := fun address => if address == 4096 then
    some ⟨0, 42, 1536, true, false, true, 32, 256, false, true, -1, [], []⟩ else none
  typenameHashes := fun _ => none
  smallTypes := fun _ => none
  globals := ⟨8192, 65536, 0, 0, keys⟩
  memories := fun address => if address == 512 then some keys else
    if address == 768 then some indices else none

def calls : S.Callees where
  gc := ⟨fun _ => fail (.abort "unused counterexample allocation")⟩
  indices := {
    uint8Type := 30000, uint16Type := 30016, uint32Type := 30032, anyMemoryType := 30048
    empty8 := indices, empty16 := indices, empty32 := indices
    allocateBits := fun _ _ _ => fail (.abort "unused counterexample integer allocation") }
  newObject := fun _ _ _ _ _ => fail (.abort "unused counterexample construction")
  copyKeys := fun _ => fail (.abort "unused counterexample copy")
  isa := fun _ _ => pure false
  union := fun _ _ => fail (.abort "unused counterexample union")
  setdiff := fun _ _ => fail (.abort "unused counterexample setdiff")
  unsafeFilter := fun _ _ => fail (.abort "unused counterexample filter")

theorem fields_ok : P.succeeds (S.fields 256) world setFields := by
  refine ⟨world, ?_⟩
  cbv

theorem members_ok : P.succeeds (members 256) world [1024] := by
  refine ⟨world, ?_⟩
  cbv

theorem key_read : P.succeeds (N.plainReadCell keys 0) world 1024 := by
  refine ⟨world, ?_⟩
  cbv

theorem width_ok :
    P.succeeds (JuliaLean.src.smallintset_c.elementWidth calls.indices indices false) world 1 := by
  refine ⟨world, ?_⟩
  cbv

theorem cache_ok : P.succeeds (cacheCell calls indices 0) world 1 := by
  refine ⟨{ world with events := [.atomicIntegerLoad 776 1 1 .acquire] }, ?_⟩
  cbv

theorem hash_ok :
    P.succeeds (JuliaLean.src.builtins_identity_c.jl_object_id 1024) world 7 := by
  refine ⟨world, ?_⟩
  calc
    _ = JuliaLean.src.builtins_identity_c.jl_object_id_ 288 1024 world := by cbv
    _ = some (.ok 7, world) := by
      rw [JuliaLean.src.builtins_identity_c.jl_object_id_.eq_def]
      cbv

theorem valid_key : P.validValue world 1024 := ⟨by decide, 7, hash_ok⟩

theorem placement_ok : indexPlacement calls world setFields := by
  constructor
  · intro slot hslot
    have hzero : slot = 0 := by change slot < 1 at hslot; omega
    subst slot
    refine ⟨1, cache_ok, Or.inr (Or.inr ⟨1024, by decide, by decide, by decide, ?_⟩)⟩
    exact key_read
  · intro index hindex key hkey hnonzero
    have hzero : index = 0 := by change index < 1 at hindex; omega
    subst index
    have hread : ∃ final, N.plainReadCell keys 0 world = some (.ok key, final) := hkey
    rcases hread with ⟨final, hread⟩
    have hkeyValue : key = 1024 := by
      rcases key_read with ⟨known, hknown⟩
      rw [hknown] at hread
      cases hread
      rfl
    subst key
    refine ⟨7, 0, hash_ok, by decide, by decide, by decide, cache_ok, ?_, ?_⟩
    · intro step hstep
      omega
    · intro slot hslot _
      change slot < 1 at hslot
      have : slot = 0 := by omega
      exact this

theorem well_formed : IdSetWellFormed calls world 256 := by
  refine ⟨setFields, [1024], 1, fields_ok, members_ok, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_, width_ok, by decide, Or.inl rfl, ?_,
    Or.inr ⟨0, rfl⟩, ?_, ?_, ?_, placement_ok⟩
  · exact ⟨by decide, by decide, fun _ _ => rfl⟩
  · exact ⟨by decide, by decide, fun _ _ => rfl⟩
  · simp [JuliaLean.Proofs.base.iddict.keysDistinct]
  · intro value hvalue
    have : value = 1024 := by simpa using hvalue
    subst value
    exact valid_key
  · intro index hmin hmax
    change 1 ≤ index at hmin
    change index < 1 at hmax
    omega

theorem iteration_typeerror :
    collectIteration calls 256 (JInt.wrap .i64 0) world =
      some (.error (.typeAssertion 28672 1024),
        { world with events := [.load 520 1024] }) := by
  rw [collectIteration.eq_def, JuliaLean.base.idset.iterate.eq_def]
  cbv

end EltypeCounterexample

theorem idSetElemsHaveEltype_refuted : ¬ IdSetElemsHaveEltype := by
  intro claim
  obtain ⟨values, final, hresult⟩ :=
    claim EltypeCounterexample.calls EltypeCounterexample.world 256 EltypeCounterexample.well_formed
  rw [EltypeCounterexample.iteration_typeerror] at hresult
  cases hresult

/-! Nothing to promise:
No methods are plumbing-only in `base/idset.jl`; each has a constructor, membership, mutation,
iteration, or memory effect covered by the properties above.
-/

def entries : List Entry := [
  { id := "iddicts-idset-ops-agree", juliaFile := "base/idset.jl",
    juliaFns := ["push!(::IdSet, x)", "_pop!(::IdSet, x)", "pop!(::IdSet, x)",
      "pop!(::IdSet, x, default)", "delete!(::IdSet, x)", "empty!(::IdSet)",
      "sizehint!(::IdSet, newsz)", "union!(::IdSet, itr)", "setdiff!(::IdSet, itr)",
      "iterate(::IdSet)", "length(::IdSet)", "in(x, ::IdSet)", "jl_idset_put_key"],
    statement := "Identity membership stays correct through push!, keyed pop, delete!, empty!, sizehint!, union! and setdiff!; length counts members and iteration yields each identity once.",
    source := "IdSet docstring base/idset.jl:7-11; union!/setdiff! contracts base/abstractset.jl:62-84,225-243",
    status := .todo, prop := ``IdSetOpsAgree, thm := none,
    notes := "Statement defect: unconstrained union/setdiff/allocation callees and unrelated iteratorValues can return arbitrary successful states, which the public Julia operations do not permit; require callee correctness, iterator-dispatch correspondence, and coherent disjoint heap ownership (g13IdsetSizehint_members proves the complete sizehint clause)." },
  { id := "iddicts-idset-eltype", juliaFile := "base/idset.jl",
    juliaFns := ["push!(::IdSet, x)", "iterate(::IdSet)", "union!(::IdSet, itr)"],
    statement := "Every element stored in IdSet{T} can be produced by iteration as a T without a TypeError.",
    source := "IdSet docstring base/idset.jl:7-8; iterate type assertion base/idset.jl:121-127",
    status := .refuted, refutationEvidence := .runtime,
    prop := ``IdSetElemsHaveEltype, thm := some ``idSetElemsHaveEltype_refuted,
    notes := "The native counterexample contains a Symbol in a Bool-typed set; the source iteration assertion throws TypeError. The public Julia reproducer remains repro/iddicts-idset-eltype.jl.",
    issue := "none found (queries: IdSet push convert, IdSet eltype, IdSet TypeError, IdSet convert check, IdSet)" },
  { id := "bitsetscov-idset-basic", juliaFile := "base/idset.jl",
    juliaFns := ["IdSet{T}()", "IdSet{T}(s::IdSet{T})", "IdSet{T}(itr)", "IdSet()",
      "copymutable(::IdSet)", "emptymutable(::IdSet)", "emptymutable(::IdSet{T}, ::Type{U})",
      "copy(::IdSet)", "haskey(::IdSet, key)",
      "isempty(::IdSet)", "length(::IdSet)", "in(x, ::IdSet)"],
    statement := "Empty constructors and emptymutable produce empty identity sets, iterable construction includes each input identity, copies preserve membership, and lookup uses ===.",
    source := "IdSet docstring base/idset.jl:7-11; constructors and lookup base/idset.jl:34-45",
    status := .todo, prop := ``IdSetBasicSpec, thm := none,
    notes := "Statement defect: arbitrary constructor/copy/union callees and an unrelated iteratorValues function can return inconsistent contents, which public Julia constructors do not permit; require callee correctness and a relation tying iteratorValues to the actual iterator dispatch (count/emptiness consequences are preserved in g13IdsetWellformed_count)." },
  { id := "bitsetscov-idset-pop", juliaFile := "base/idset.jl",
    juliaFns := ["_pop!(::IdSet, x)", "pop!(::IdSet, x)", "pop!(::IdSet, x, default)", "delete!(::IdSet, x)"],
    statement := "Keyed pop removes and returns the identity-matching object, throws KeyError only when no default is given for a missing key, and delete! leaves that identity absent.",
    source := "pop! contract base/abstractset.jl; base/idset.jl:71-83",
    status := .todo, prop := ``IdSetPopSpec, thm := none,
    notes := "Statement defect: IdSetWellFormed permits a key-memory view whose metadata owner is absent from world.memories, although native identity lookup rereads that owner and can fail; require coherent owner-to-memory views and nonoverlapping live runtime objects (g13IdsetPopSpec_of_core proves all public wrappers from the remaining concrete-removal contract)." },
  { id := "bitsetscov-idset-memory", juliaFile := "base/idset.jl",
    juliaFns := ["_zero!(::Memory{<:BitInteger})", "empty!(::IdSet)", "filter!(::IdSet)"],
    statement := "_zero! clears every integer memory cell, empty! clears its slots and index memory, and filter! retains exactly values accepted by its predicate.",
    source := "memory and filter invariants base/idset.jl:99-119; filter! contract base/abstractset.jl:625-641",
    status := .todo, prop := ``IdSetMemorySpec, thm := none,
    notes := "Statement defect: the outside-address clause quantifies over Nat addresses beyond 2^64, so clearing a byte at p also changes readByte(p+2^64), which is the same machine address; require address < 2^64 or a reduced-address frame condition, plus correctness/stability laws for the filter callback (g13IdsetZero_bounded proves the corrected bounded clearing/frame claim from the exact native byte count)." }
]

end JuliaLean.Proofs.base.idset

namespace JuliaLean.ChatGPT.Batch4.Group23
open JuliaLean
open JuliaLean.src.identity_runtime (Word World Memory M Error)
open JuliaLean.Proofs.base.idset

theorem idset_bind_run {α β : Type} (first : M α) (next : α → M β)
    (world : World) :
    (first >>= next) world =
      match first world with
      | none => none
      | some (.error error, final) => some (.error error, final)
      | some (.ok value, middle) => next value middle := by
  change JuliaLean.base.iterators.bind first next world = _
  unfold JuliaLean.base.iterators.bind
  cases first world with
  | none => rfl
  | some result =>
    rcases result with ⟨result, final⟩
    cases result <;> rfl

theorem idset_pure_run {α : Type} (value : α) (world : World) :
    (pure value : M α) world = some (.ok value, world) := rfl

/-- Membership notation uses exactly the installed identity lookup. -/
theorem idset_membership_alias (calls : S.Callees) (address key : Word) :
    S.«in» calls key address = S.haskey calls address key := rfl

/-- All three public copy entry points use the same copy constructor. -/
theorem idset_copy_aliases (calls : S.Callees) (address : Word) :
    S.copy calls address = S.copyConstruct calls address ∧
    S.copymutable calls address = S.copyConstruct calls address := ⟨rfl, rfl⟩

/-- The explicit element-type empty constructor does not inspect its source. -/
theorem idset_empty_as_alias (calls : S.Callees) (address elementType : Word) :
    S.emptymutableAs calls address elementType = S.emptyTyped calls elementType := rfl

/-- The installed size hint performs no state change. -/
theorem idset_sizehint_run (address size : Word) (world : World) :
    S.sizehint! address size world = some (.ok (), world) := rfl

/-- In particular size hints preserve every membership outcome. -/
theorem idset_sizehint_same_members (calls : S.Callees) (address size : Word)
    (world : World) :
    P.returns (S.sizehint! address size) world
      (fun _ final => SameMembers calls world final address address) := by
  intro value final h
  change (some (Except.ok (ε := Error) (), world)) = some (.ok value, final) at h
  cases h
  intro query _
  rfl

/-- Once the concrete removal result is known, public pop has no additional effects. -/
theorem idset_pop_run (calls : S.Callees) (address key : Word) (world final : World)
    (index : JInt .i64)
    (h : S._pop! calls address key world = some (.ok index, final)) :
    S.pop! calls address key world =
      some ((if index.val = -1 then .error (.keyError key) else .ok key), final) := by
  unfold JuliaLean.base.idset.pop!
  rw [idset_bind_run, h]
  by_cases hi : index.val = -1
  · simp only [hi, beq_self_eq_true, ite_true]
    rfl
  · simp only [beq_eq_false_iff_ne.mpr hi, Bool.false_eq_true, ite_false, hi]
    rfl

/-- Defaulted pop returns the fallback precisely at the missing-key sentinel. -/
theorem idset_pop_default_run (calls : S.Callees) (address key fallback : Word)
    (world final : World) (index : JInt .i64)
    (h : S._pop! calls address key world = some (.ok index, final)) :
    S.popDefault calls address key fallback world =
      some (.ok (if index.val = -1 then fallback else key), final) := by
  unfold JuliaLean.base.idset.popDefault
  rw [idset_bind_run, h]
  by_cases hi : index.val = -1
  · simp only [hi, beq_self_eq_true, ite_true]
    rfl
  · simp only [beq_eq_false_iff_ne.mpr hi, Bool.false_eq_true, ite_false, hi]
    rfl

/-- Delete returns its source address and the concrete removal's final state. -/
theorem idset_delete_run (calls : S.Callees) (address key : Word) (world final : World)
    (index : JInt .i64)
    (h : S._pop! calls address key world = some (.ok index, final)) :
    S.delete! calls address key world = some (.ok address, final) := by
  unfold JuliaLean.base.idset.delete!
  rw [idset_bind_run, h]
  rfl



/-- A read-only native action may fail or diverge, but retains its input world. -/
def IdsetReadOnly {α : Type} (action : M α) : Prop :=
  ∀ world result final, action world = some (result, final) → final = world

theorem idset_readonly_pure {α : Type} (value : α) :
    IdsetReadOnly (pure value : M α) := by
  intro world result final h
  change some (.ok value, world) = some (result, final) at h
  cases h
  rfl

theorem idset_readonly_fail {α : Type} (error : Error) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.fail error : M α) := by
  intro world result final h
  change some (.error error, world) = some (result, final) at h
  cases h
  rfl

theorem idset_readonly_get : IdsetReadOnly JuliaLean.src.identity_runtime.getWorld := by
  intro world result final h
  change some (.ok world, world) = some (result, final) at h
  cases h
  rfl

theorem idset_readonly_bind {α β : Type} {first : M α} {next : α → M β}
    (hfirst : IdsetReadOnly first) (hnext : ∀ value, IdsetReadOnly (next value)) :
    IdsetReadOnly (first >>= next) := by
  intro world result final h
  rw [idset_bind_run] at h
  cases run : first world with
  | none => simp only [run] at h; cases h
  | some pair =>
    rcases pair with ⟨initial, middle⟩
    have hm := hfirst world initial middle run
    cases initial with
    | error error =>
      simp only [run] at h
      cases h
      exact hm
    | ok value =>
      simp only [run] at h
      exact (hnext value middle result final h).trans hm

theorem idset_readonly_require (address : Word) (size : Nat) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.requireReadable address size) := by
  unfold JuliaLean.src.identity_runtime.requireReadable
  apply idset_readonly_bind idset_readonly_get
  intro world
  dsimp only
  split
  · exact idset_readonly_fail _
  · exact idset_readonly_pure _

theorem idset_readonly_load (address : Word) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.loadWord address) := by
  unfold JuliaLean.src.identity_runtime.loadWord
  apply idset_readonly_bind (idset_readonly_require _ _)
  intro _
  apply idset_readonly_bind idset_readonly_get
  intro _
  exact idset_readonly_pure _

theorem idset_readonly_memory (address : Word) :
    IdsetReadOnly (JuliaLean.src.idset_c.memoryAtAddress address) := by
  unfold JuliaLean.src.idset_c.memoryAtAddress
  apply idset_readonly_bind idset_readonly_get
  intro world
  cases world.memories address
  · exact idset_readonly_fail _
  · exact idset_readonly_pure _

theorem idset_readonly_datatype (address : Word) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.datatypeAt address) := by
  unfold JuliaLean.src.identity_runtime.datatypeAt
  apply idset_readonly_bind idset_readonly_get
  intro world
  cases world.datatypes address
  · exact idset_readonly_fail _
  · exact idset_readonly_pure _

theorem idset_readonly_typetag (address : Word) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.typetag address) := by
  unfold JuliaLean.src.identity_runtime.typetag
  split
  · exact idset_readonly_fail _
  · apply idset_readonly_bind (idset_readonly_load _)
    intro _
    exact idset_readonly_pure _

theorem idset_readonly_to_typeof (tag : Word) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.toTypeof tag) := by
  unfold JuliaLean.src.identity_runtime.toTypeof
  split
  · apply idset_readonly_bind idset_readonly_get
    intro world
    cases world.smallTypes (tag.toNat / 8)
    · exact idset_readonly_fail _
    · exact idset_readonly_pure _
  · exact idset_readonly_pure _

theorem idset_readonly_typeof (address : Word) :
    IdsetReadOnly (JuliaLean.src.identity_runtime.typeof address) := by
  unfold JuliaLean.src.identity_runtime.typeof
  apply idset_readonly_bind (idset_readonly_typetag _)
  exact idset_readonly_to_typeof

/-- Reading the native set fields has no heap, root, or event effects. -/
theorem idset_fields_readonly (address : Word) : IdsetReadOnly (S.fields address) := by
  unfold JuliaLean.base.idset.fields
  apply idset_readonly_bind (idset_readonly_load _)
  intro _
  apply idset_readonly_bind (idset_readonly_memory _)
  intro _
  apply idset_readonly_bind (idset_readonly_load _)
  intro _
  apply idset_readonly_bind (idset_readonly_memory _)
  intro _
  apply idset_readonly_bind (idset_readonly_load _)
  intro _
  apply idset_readonly_bind (idset_readonly_load _)
  intro _
  apply idset_readonly_bind (idset_readonly_typeof _)
  intro _
  apply idset_readonly_bind (idset_readonly_datatype _)
  intro _
  apply idset_readonly_bind (idset_readonly_load _)
  intro _
  exact idset_readonly_pure _

/-- The stored count is returned whenever the native fields can be read. -/
theorem idset_length_from_fields (address : Word) (world : World) (fields : S.SetFields)
    (h : P.succeeds (S.fields address) world fields) :
    S.length address world = some (.ok fields.count, world) := by
  rcases h with ⟨final, h⟩
  have hf := idset_fields_readonly address world (.ok fields) final h
  subst final
  unfold JuliaLean.base.idset.length
  rw [idset_bind_run, h]
  rfl

/-- Emptiness tests the stored count without changing the state. -/
theorem idset_isempty_from_fields (address : Word) (world : World) (fields : S.SetFields)
    (h : P.succeeds (S.fields address) world fields) :
    S.isempty address world = some (.ok (fields.count.val == 0), world) := by
  rcases h with ⟨final, h⟩
  have hf := idset_fields_readonly address world (.ok fields) final h
  subst final
  unfold JuliaLean.base.idset.isempty
  rw [idset_bind_run, h]
  rfl



/-- The count and emptiness clauses of the basic target follow from the installed invariant. -/
theorem idset_wellformed_count (calls : S.Callees) (world : World) (address : Word)
    (values : List Word) (hw : IdSetWellFormed calls world address)
    (hm : P.succeeds (members address) world values) :
    P.succeeds (S.length address) world (JInt.wrap .i64 (Int.ofNat values.length)) ∧
    P.succeeds (S.isempty address) world values.isEmpty := by
  rcases hw with ⟨fields, expected, width, hf, he, rest⟩
  have hc : fields.count.val = Int.ofNat expected.length := rest.2.2.2.2.1
  have hv : expected = values := by
    rcases he with ⟨endExpected, he⟩
    rcases hm with ⟨endValues, hm⟩
    rw [he] at hm
    cases hm
    rfl
  subst expected
  have hcount : fields.count = JInt.wrap .i64 (Int.ofNat values.length) := by
    apply Subtype.ext
    change fields.count.val = wrapInt .i64 (Int.ofNat values.length)
    rw [← hc]
    exact (wrapInt_of_inRange _ _ fields.count.property).symm
  constructor
  · refine ⟨world, ?_⟩
    rw [idset_length_from_fields address world fields hf, hcount]
  · refine ⟨world, ?_⟩
    rw [idset_isempty_from_fields address world fields hf]
    have hempty : (fields.count.val == 0) = values.isEmpty := by
      rw [hc]
      cases values with
      | nil => rfl
      | cons value tail =>
        change (Int.ofNat (tail.length + 1) == 0) = false
        apply beq_eq_false_iff_ne.mpr
        intro hz
        exact Nat.noConfusion (Int.ofNat.inj hz)
    rw [hempty]



/-- The exact unsigned byte count passed to native clearing. -/
def idsetZeroCount (memory : Memory) : Word :=
  JuliaLean.src.idset_c.unsigned
    (JInt.wrap .i64 memory.metadata.memoryLayout.size.val *
      JInt.wrap .i64 (Int.ofNat memory.length))

/-- Exact state effect of a successful source-level memory clear. -/
def idsetZeroFinal (memory : Memory) (world : World) : World :=
  let address := UInt64.ofNat memory.ptr
  let count := idsetZeroCount memory
  { world with
    raw := { world.raw with
      heap := { world.raw.heap with byteAt := fun query =>
        if address.toNat ≤ query && query < address.toNat + count.toNat
        then (JInt.wrap IntTy.u8 0) else world.raw.heap.byteAt query } }
    locals := world.locals ++ [some memory]
    events := ((world.events ++ [.pushRoots [world.locals.length]]) ++
      [.memset address count]) ++ [.popRoots] }

/-- Clearing uses the native byte interval and restores the caller's root stack. -/
theorem idset_zero_run (memory : Memory) (world : World)
    (haddress : UInt64.ofNat memory.ptr ≠ 0)
    (hread : JuliaLean.src.identity_runtime.readableRange world.raw.heap
      (UInt64.ofNat memory.ptr).toNat (idsetZeroCount memory).toNat = true) :
    S._zero! memory world = some (.ok memory, idsetZeroFinal memory world) := by
  dsimp only [idsetZeroCount] at hread
  unfold JuliaLean.base.idset._zero!
  simp only [idset_bind_run, idset_pure_run, JuliaLean.src.identity_runtime.newLocal,
    JuliaLean.src.identity_runtime.getWorld, JuliaLean.src.identity_runtime.modifyWorld,
    JuliaLean.src.identity_runtime.pushRoots,
    JuliaLean.src.smallintset_c.zeroBytes, JuliaLean.src.identity_runtime.requireReadable,
    JuliaLean.src.identity_runtime.popRoots, haddress, decide_false, hread, Bool.not_true,
    Bool.false_or, Bool.false_eq_true, ite_false]
  rfl


/-- Byte clearing respects the address space's modulo operation. -/
theorem idset_zero_byte_at (memory : Memory) (world : World) (query : Nat) :
    (idsetZeroFinal memory world).raw.heap.readByte query =
      if (UInt64.ofNat memory.ptr).toNat ≤ query % 2^64 ∧
          query % 2^64 < (UInt64.ofNat memory.ptr).toNat + (idsetZeroCount memory).toNat
      then JInt.wrap .u8 0 else world.raw.heap.readByte query := by
  simp only [idsetZeroFinal, JuliaLean.base.pointer.ByteHeap.readByte,
    JuliaLean.base.pointer.addressMod, Bool.and_eq_true, decide_eq_true_eq]

/-- The corrected outside-range condition is stated on the reduced address. -/
theorem idset_zero_preserves_outside_modulo (memory : Memory) (world : World) (query : Nat)
    (hout : query % 2^64 < (UInt64.ofNat memory.ptr).toNat ∨
      (UInt64.ofNat memory.ptr).toNat + (idsetZeroCount memory).toNat ≤ query % 2^64) :
    (idsetZeroFinal memory world).raw.heap.readByte query = world.raw.heap.readByte query := by
  rw [idset_zero_byte_at]
  have hnot : ¬ ((UInt64.ofNat memory.ptr).toNat ≤ query % 2^64 ∧
      query % 2^64 < (UInt64.ofNat memory.ptr).toNat + (idsetZeroCount memory).toNat) := by
    omega
  exact ite_eq_right hnot

end JuliaLean.ChatGPT.Batch4.Group23
