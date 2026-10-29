import JuliaLean.base.idset
import JuliaLean.base.iddict
import JuliaLean.Proofs.base.cmem
import JuliaLean.Registry.Types

/-!
# Properties of `base/idset.jl`

Each statement concerns the typed methods in `JuliaLean.base.idset`. Runtime memory and C table
operations remain typed parameters; `sameIdentity` is the `===` relation supplied by the shared
IdDict runtime interface.
-/

namespace JuliaLean.Proofs.base.idset

open JuliaLean JuliaLean.Registry JuliaLean.base.iddict
open JuliaLean.base.pointer

/-- Assigned values in the source order of the `Memory{Any}` slot model. -/
def valuesInSlots {A : Type} : List (Option A) → List A
  | [] => []
  | none :: rest => valuesInSlots rest
  | some value :: rest => value :: valuesInSlots rest

/-- Membership by Julia object identity. -/
def containsIdentity {A : Type} (sameIdentity : A → A → Bool) (query : A) : List A → Bool
  | [] => false
  | value :: rest => sameIdentity query value || containsIdentity sameIdentity query rest

/-- No two listed values denote the same Julia identity. -/
def identityDistinct {A : Type} (sameIdentity : A → A → Bool) : List A → Prop
  | [] => True
  | value :: rest =>
      (∀ other, other ∈ rest → sameIdentity value other = false) ∧
      identityDistinct sameIdentity rest

/-- The public IdSet count, high-water mark and stored slots agree. -/
def IdSetWellFormed {A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s : JuliaLean.base.idset.IdSet A A I) : Prop :=
  0 ≤ s.count.val ∧ 0 ≤ s.max.val ∧
  s.max.val ≤ Int.ofNat s.list.length ∧
  s.count.val.toNat = (valuesInSlots s.list).length ∧
  identityDistinct ops.iddict.sameIdentity (valuesInSlots s.list)

def IdSetEmpty {K A I : Type} (s : JuliaLean.base.idset.IdSet K A I) : Prop :=
  s.count.val = 0 ∧ s.max.val = 0 ∧ valuesInSlots s.list = []

def SameMembers {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (left right : JuliaLean.base.idset.IdSet K A I) : Prop :=
  ∀ x, JuliaLean.base.idset.haskey ops left x = JuliaLean.base.idset.haskey ops right x

def collectIteration {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s : JuliaLean.base.idset.IdSet K A I) (state : JInt .i64) :
    Nat → Except E (List K)
  | 0 => .ok []
  | fuel + 1 =>
      let step := JuliaLean.base.idset.iterate ops s state
      match step.result with
      | .error e => .error e
      | .ok none => .ok []
      | .ok (some (value, next)) =>
          match collectIteration ops s next fuel with
          | .error e => .error e
          | .ok values => .ok (value :: values)

def IdSetBasicSpec {A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve) : Prop :=
  (∀ {K : Type} (s : JuliaLean.base.idset.IdSet K A I),
    JuliaLean.base.idset.emptyTyped ops = .ok s → IdSetEmpty s) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I),
    JuliaLean.base.idset.emptyAny ops = .ok s → IdSetEmpty s) ∧
  (∀ {K : Type} (s : JuliaLean.base.idset.IdSet K A I) (s' : JuliaLean.base.idset.IdSet K A I),
    JuliaLean.base.idset.emptymutable ops s = .ok s' → IdSetEmpty s') ∧
  (∀ {K : Type} (s : JuliaLean.base.idset.IdSet K A I) (U : Type)
      (s' : JuliaLean.base.idset.IdSet U A I),
    JuliaLean.base.idset.emptymutableAs ops s U = .ok s' → IdSetEmpty s') ∧
  (∀ {K : Type} (s s' : JuliaLean.base.idset.IdSet K A I),
    JuliaLean.base.idset.copyConstruct ops s = .ok s' → SameMembers ops s s') ∧
  (∀ {K : Type} (s s' : JuliaLean.base.idset.IdSet K A I),
    JuliaLean.base.idset.copy ops s = .ok s' → SameMembers ops s s') ∧
  (∀ {K : Type} (s s' : JuliaLean.base.idset.IdSet K A I),
    JuliaLean.base.idset.copymutable ops s = .ok s' → SameMembers ops s s') ∧
  (∀ (xs : List A) (s : JuliaLean.base.idset.IdSet A A I),
    JuliaLean.base.idset.fromIterator ops xs = .ok s →
      ∀ x, JuliaLean.base.idset.haskey ops s x =
        containsIdentity ops.iddict.sameIdentity x xs) ∧
  (∀ {K : Type} (s : JuliaLean.base.idset.IdSet K A I) x,
    JuliaLean.base.idset.haskey ops s x =
      containsIdentity ops.iddict.sameIdentity x (valuesInSlots s.list)) ∧
  (∀ {K : Type} (s : JuliaLean.base.idset.IdSet K A I) x,
    JuliaLean.base.idset.«in» ops x s =
      containsIdentity ops.iddict.sameIdentity x (valuesInSlots s.list)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I), IdSetWellFormed ops s →
    JuliaLean.base.idset.length s = JInt.wrap .i64 (Int.ofNat (valuesInSlots s.list).length) ∧
    JuliaLean.base.idset.isempty s = decide (valuesInSlots s.list = []))

def IdSetOpsAgree {A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve) : Prop :=
  (∀ (s : JuliaLean.base.idset.IdSet A A I), IdSetWellFormed ops s →
    ∀ x, JuliaLean.base.idset.haskey ops s x =
      containsIdentity ops.iddict.sameIdentity x (valuesInSlots s.list)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) x,
    IdSetWellFormed ops s →
    ∃ after, (JuliaLean.base.idset.push! ops s x).result = .ok after ∧
      IdSetWellFormed ops after ∧
      (∀ y, JuliaLean.base.idset.haskey ops after y =
        (containsIdentity ops.iddict.sameIdentity y (valuesInSlots s.list) ||
          ops.iddict.sameIdentity y x)) ∧
      after.count = s.count + JInt.wrap .i64
        (if JuliaLean.base.idset.haskey ops s x then 0 else 1)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) x,
    IdSetWellFormed ops s →
    let result := JuliaLean.base.idset.delete! ops s x
    ∃ after, result.result = .ok after ∧ SameMembers ops result.state after ∧
      ¬ JuliaLean.base.idset.haskey ops after x ∧
      ∀ y, ops.iddict.sameIdentity y x = false →
        JuliaLean.base.idset.haskey ops after y = JuliaLean.base.idset.haskey ops s y) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I), IdSetWellFormed ops s →
    let result := JuliaLean.base.idset.empty! ops s
    ∃ after, result.result = .ok after ∧ IdSetEmpty after) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) (newSize : Nat),
    let result : CallResult E (JuliaLean.base.idset.IdSet A A I) Unit :=
      JuliaLean.base.idset.sizehint! s newSize
    result.result = .ok () ∧ SameMembers ops s result.state) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) (xs : List A),
    IdSetWellFormed ops s →
    let result := ops.union s xs
    ∀ after, result.result = .ok after →
      ∀ x, JuliaLean.base.idset.haskey ops after x =
        (JuliaLean.base.idset.haskey ops s x ||
          containsIdentity ops.iddict.sameIdentity x xs)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) (xs : List A),
    IdSetWellFormed ops s →
    let result := ops.setdiff s xs
    ∀ after, result.result = .ok after →
      ∀ x, JuliaLean.base.idset.haskey ops after x =
        (JuliaLean.base.idset.haskey ops s x &&
          !(containsIdentity ops.iddict.sameIdentity x xs))) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) xs,
    IdSetWellFormed ops s →
    collectIteration ops s (JInt.wrap .i64 0) (s.max.val.toNat + 1) = .ok xs →
      identityDistinct ops.iddict.sameIdentity xs ∧
      ∀ x, containsIdentity ops.iddict.sameIdentity x xs =
        containsIdentity ops.iddict.sameIdentity x (valuesInSlots s.list))

def IdSetElemsHaveEltype : Prop :=
  ∀ {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s : JuliaLean.base.idset.IdSet K A I), 0 ≤ s.max.val →
    ∃ values : List K,
      collectIteration ops s (JInt.wrap .i64 0) (s.max.val.toNat + 1) = .ok values

def rejectingCastOps : JuliaLean.base.idset.Runtime Nat ByteHeap Unit (Ptr Unit) Unit where
  iddict := {
    allocate := fun n => .ok (List.replicate n none)
    sameMemory := fun _ _ => false
    copyMemory := fun memory => .ok memory
    memoryLength := fun memory => JInt.wrap .i64 (Int.ofNat memory.length)
    rehashMemory := fun {N} memory _ => .ok memory
    eqtableGet := fun _ _ default => default
    eqtablePut := fun memory _ _ => .ok (memory, JInt.wrap .i32 0)
    eqtablePop := fun memory _ default => .ok (memory, default, JInt.wrap .i32 0)
    eqtableNextind := fun _ _ => JInt.wrap .u64 (-1)
    reinterpretInt := fun index => JInt.wrap .i64 index.val
    memoryAt := fun _ _ => .ok 7
    toUInt := fun {I} _ => .ok (JInt.wrap .u64 0)
    isKey := fun _ => true
    isValue := fun _ => true
    convertValue := fun value => .ok value
    castKey := fun _ => .ok 0
    castValue := fun _ => .ok 0
    keyToAny := fun value => value
    valueToAny := fun value => value
    keyTypeError := fun _ => ()
    keyError := fun _ => ()
    secretToken := 0
    sameIdentity := fun left right => decide (left = right)
    doubleInteger := fun {N} value => .ok value
    tablesz := fun {N} _ => .ok (JInt.wrap .i64 0)
    preserveBegin := fun _ => ()
    unsafeConvert := fun _ => C_NULL
    sizeofMemory := fun _ => JInt.wrap .u64 0
    memsetZero := fun memory _ _ => memory
    preserveEnd := fun _ => ()
    tableSlots := fun _ => []
    tablePairs := fun _ => []
  }
  allocateIndices8 := fun _ => .ok JuliaLean.Proofs.base.cmem.StandardC.trivialHeap
  copyIndices := fun memory => .ok memory
  peekBucket := fun _ _ _ => JInt.wrap .i64 (-1)
  putKey := fun _ _ _ => .error ()
  putIndex := fun _ _ _ => .error ()
  popKey := fun _ _ _ => .error ()
  boundsError := ()
  assertionError := fun _ => ()
  keyError := fun _ => ()
  uintToInt := fun _ => .ok (JInt.wrap .i64 0)
  preserveBegin := fun _ => ()
  unsafeConvert := fun _ => C_NULL
  eltype := fun _ => .i64
  sizeof := fun _ => JInt.wrap .i64 8
  memoryLength := fun _ => JInt.wrap .i64 1
  indexHeap := id
  pointerView := id
  memset := JuliaLean.Proofs.base.cmem.StandardC.cMemset
  memsetStandard := JuliaLean.Proofs.base.cmem.StandardC.cMemsetLaw
  preserveEnd := fun _ => ()
  castTo := fun {_} _ => .error ()
  union := fun {K} {Itr} s _ => resultWithState (.error ()) s
  setdiff := fun {K} {Itr} s _ => resultWithState (.error ()) s
  unsafeFilter := fun {K} _ s => resultWithState (.error ()) s

theorem idSetElemsHaveEltype_refuted : ¬ IdSetElemsHaveEltype := by
  intro h
  let s : JuliaLean.base.idset.IdSet Bool Nat ByteHeap :=
    ⟨[some 7], JuliaLean.Proofs.base.cmem.StandardC.trivialHeap,
      JInt.wrap .i64 1, JInt.wrap .i64 1⟩
  have nextState : (JInt.wrap .i64 0 + JInt.wrap .i64 1).val = 1 := by decide
  have iter : JuliaLean.base.idset.iterate rejectingCastOps s (JInt.wrap .i64 0) =
      resultWithState (.error ()) s := by
    dsimp [JuliaLean.base.idset.iterate]
    rw [nextState]
    simp [JuliaLean.base.idset.findAssigned, rejectingCastOps, s, JInt.wrap,
      wrapInt, IntTy.signed, IntTy.bits]
  have result : collectIteration rejectingCastOps s (JInt.wrap .i64 0) 2 = .error () := by
    simp [collectIteration, iter, resultWithState]
  obtain ⟨values, hvalues⟩ := h (ops := rejectingCastOps) s (by decide)
  simp [s, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits] at hvalues
  cases hvalues

def IdSetPopSpec {A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve) : Prop :=
  (∀ (s : JuliaLean.base.idset.IdSet A A I) x, IdSetWellFormed ops s →
    let removed := JuliaLean.base.idset._pop! ops s x
    ∃ index, removed.result = .ok index ∧
      (JuliaLean.base.idset.haskey ops s x →
        index.val ≠ -1 ∧ ¬ JuliaLean.base.idset.haskey ops removed.state x) ∧
      (¬ JuliaLean.base.idset.haskey ops s x →
        index.val = -1 ∧ SameMembers ops s removed.state)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) x, IdSetWellFormed ops s →
    let result := JuliaLean.base.idset.pop! ops s x
    (JuliaLean.base.idset.haskey ops s x → result.result = .ok x) ∧
    (¬ JuliaLean.base.idset.haskey ops s x → result.result = .error (ops.keyError x))) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) x default, IdSetWellFormed ops s →
    let result := JuliaLean.base.idset.popDefault ops s x default
    (JuliaLean.base.idset.haskey ops s x → result.result = .ok x) ∧
    (¬ JuliaLean.base.idset.haskey ops s x →
      result.result = .ok default ∧ SameMembers ops s result.state)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) x, IdSetWellFormed ops s →
    let result := JuliaLean.base.idset.delete! ops s x
    ∃ after, result.result = .ok after ∧ SameMembers ops result.state after ∧
      ¬ JuliaLean.base.idset.haskey ops after x)

def IdSetMemorySpec {A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve) (allZero : I → Prop) : Prop :=
  (∀ memory, allZero (JuliaLean.base.idset._zero! ops memory)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) predicate after,
    (JuliaLean.base.idset.filter! ops predicate s).result = .ok after →
      ∀ x, JuliaLean.base.idset.haskey ops after x =
        (JuliaLean.base.idset.haskey ops s x && predicate x)) ∧
  (∀ (s : JuliaLean.base.idset.IdSet A A I) after,
    let result := JuliaLean.base.idset.empty! ops s
    result.result = .ok after → allZero after.idxs ∧ IdSetEmpty after)

/-- `_zero!` fills its entire valid byte range with zero and changes no other byte. -/
def IdSetZeroBytesSpec : Prop :=
  ∀ {A I E Ptr Preserve : Type} (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (memory : I),
    let p := ops.pointerView (ops.unsafeConvert memory)
    let size := (ops.sizeof (ops.eltype memory) * ops.memoryLength memory).rem .u64
    JuliaLean.base.cmem.validRange (ops.indexHeap memory) p size →
    JuliaLean.base.cmem.fillEffect (ops.indexHeap memory)
      (ops.indexHeap (JuliaLean.base.idset._zero! ops memory)) p size (JInt.wrap .u8 0)

theorem idSetZeroBytesSpec_proven : IdSetZeroBytesSpec := by
  intro A I E Ptr Preserve ops memory
  dsimp only
  intro hvalid
  have h := ops.memsetStandard memory (ops.unsafeConvert memory) (JInt.wrap .i32 0)
    ((ops.sizeof (ops.eltype memory) * ops.memoryLength memory).rem .u64) hvalid
  dsimp only [JuliaLean.base.idset._zero!]
  simpa only [show (JInt.wrap .i32 0).val = 0 from by decide] using h.2

theorem clearList_preserves_indices {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve) :
    ∀ (fuel index : Nat) (s : JuliaLean.base.idset.IdSet K A I),
      (JuliaLean.base.idset.clearList ops s index fuel).state.idxs = s.idxs := by
  intros
  rfl

theorem emptyBang_indices {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s : JuliaLean.base.idset.IdSet K A I) :
    (JuliaLean.base.idset.empty! ops s).state.idxs =
      JuliaLean.base.idset._zero! ops s.idxs := by
  simp only [JuliaLean.base.idset.empty!]
  split <;> rfl

/-- The index-byte clearing survives the subsequent slot loop, including its error exits. -/
theorem emptyBang_zero_bytes {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s : JuliaLean.base.idset.IdSet K A I)
    (hvalid : JuliaLean.base.cmem.validRange (ops.indexHeap s.idxs)
      (ops.pointerView (ops.unsafeConvert s.idxs))
      ((ops.sizeof (ops.eltype s.idxs) * ops.memoryLength s.idxs).rem .u64)) :
    JuliaLean.base.cmem.fillEffect (ops.indexHeap s.idxs)
      (ops.indexHeap (JuliaLean.base.idset.empty! ops s).state.idxs)
      (ops.pointerView (ops.unsafeConvert s.idxs))
      ((ops.sizeof (ops.eltype s.idxs) * ops.memoryLength s.idxs).rem .u64)
      (JInt.wrap .u8 0) := by
  rw [emptyBang_indices]
  exact idSetZeroBytesSpec_proven ops s.idxs hvalid

theorem emptyBang_counters {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s after : JuliaLean.base.idset.IdSet K A I)
    (h : (JuliaLean.base.idset.empty! ops s).result = .ok after) :
    after.count = JInt.wrap .i64 0 ∧ after.max = JInt.wrap .i64 0 := by
  simp only [JuliaLean.base.idset.empty!] at h
  split at h
  · cases h
  · cases Except.ok.inj h
    exact ⟨rfl, rfl⟩

theorem emptyBang_iteration {K A I E Ptr Preserve : Type}
    (ops : JuliaLean.base.idset.Runtime A I E Ptr Preserve)
    (s after : JuliaLean.base.idset.IdSet K A I)
    (h : (JuliaLean.base.idset.empty! ops s).result = .ok after) :
    (JuliaLean.base.idset.iterate ops after).result = .ok none := by
  have hm := (emptyBang_counters ops s after h).2
  simp only [JuliaLean.base.idset.iterate, hm]
  have hstop : (JInt.wrap .i64 0 + JInt.wrap .i64 1).val >
      (JInt.wrap .i64 0).val := by decide
  simp only [hstop, ↓reduceIte, resultWithState]

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
    status := .todo, prop := ``IdSetOpsAgree, thm := none },
  { id := "iddicts-idset-eltype", juliaFile := "base/idset.jl",
    juliaFns := ["push!(::IdSet, x)", "iterate(::IdSet)", "union!(::IdSet, itr)"],
    statement := "Every element stored in IdSet{T} can be produced by iteration as a T without a TypeError.",
    source := "IdSet docstring base/idset.jl:7-8; iterate type assertion base/idset.jl:121-127",
    status := .refuted, refutationEvidence := .runtime,
    prop := ``IdSetElemsHaveEltype, thm := some ``idSetElemsHaveEltype_refuted,
    notes := "The target Julia repro shows push! accepts a non-T element and iterate then throws TypeError; repro/iddicts-idset-eltype.jl.",
    issue := "none found (queries: IdSet push convert, IdSet eltype, IdSet TypeError, IdSet convert check, IdSet)" },
  { id := "bitsetscov-idset-basic", juliaFile := "base/idset.jl",
    juliaFns := ["IdSet{T}()", "IdSet{T}(s::IdSet{T})", "IdSet{T}(itr)", "IdSet()",
      "copymutable(::IdSet)", "emptymutable(::IdSet)", "emptymutable(::IdSet{T}, ::Type{U})",
      "copy(::IdSet)", "haskey(::IdSet, key)",
      "isempty(::IdSet)", "length(::IdSet)", "in(x, ::IdSet)"],
    statement := "Empty constructors and emptymutable produce empty identity sets, iterable construction includes each input identity, copies preserve membership, and lookup uses ===.",
    source := "IdSet docstring base/idset.jl:7-11; constructors and lookup base/idset.jl:34-45",
    status := .todo, prop := ``IdSetBasicSpec, thm := none },
  { id := "bitsetscov-idset-pop", juliaFile := "base/idset.jl",
    juliaFns := ["_pop!(::IdSet, x)", "pop!(::IdSet, x)", "pop!(::IdSet, x, default)", "delete!(::IdSet, x)"],
    statement := "Keyed pop removes and returns the identity-matching object, throws KeyError only when no default is given for a missing key, and delete! leaves that identity absent.",
    source := "pop! contract base/abstractset.jl; base/idset.jl:71-83",
    status := .todo, prop := ``IdSetPopSpec, thm := none },
  { id := "bitsetscov-idset-memory", juliaFile := "base/idset.jl",
    juliaFns := ["_zero!(::Memory{<:BitInteger})", "empty!(::IdSet)", "filter!(::IdSet)"],
    statement := "_zero! clears every integer memory cell, empty! clears its slots and index memory, and filter! retains exactly values accepted by its predicate.",
    source := "memory and filter invariants base/idset.jl:99-119; filter! contract base/abstractset.jl:625-641",
    status := .todo, prop := ``IdSetMemorySpec, thm := none }
]

end JuliaLean.Proofs.base.idset
