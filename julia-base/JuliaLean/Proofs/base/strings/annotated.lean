-- The supplied tree has no JuliaLean.Proofs.base.strings.annotated file.
-- Import the actual source-mirrored subject and its existing array callees directly.
import JuliaLean.base.array
import JuliaLean.base.strings.annotated
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.strings.annotated.hash

namespace JuliaLean.Proofs.base.strings.annotated.Round1

/-!
## Public methods with no independent nontrivial statement

The following eight source sites are recorded as `nothing-to-promise` in the
coverage table. Their isolated identity, projection, or constant equations would
hold by unfolding the current model and fail review check 3c. The linked broader
contracts retain their meaningful observable uses; none is replaced by a claim
that an unconstrained callback is correct.

* `String@125` (`toString:189`): projection of the stored `String`, specifically
  for `AnnotatedString{String}`. A separate no-copy/return equation is trivial.
  Broader text/conversion behavior: `stringscovb-ann-constructors`.
* `convert@129` (`convertAnnotatedString:197`): identity conversion of an already
  annotated string. Broader conversion behavior: `stringscovb-ann-constructors`.
* `convert@136` (`convertAnnotatedChar:234`): identity conversion of an already
  annotated character. Broader conversion behavior: `stringscovb-ann-constructors`.
* `promote_rule@146` (`promoteRule:291`): constant promotion-target plumbing; its
  model returns the supplied `AnnotatedString` type tag. An isolated equation
  would also pass the expected answer as a parameter. No general promotion law
  is claimed by this site; actual constructor/conversion behavior remains under
  `stringscovb-ann-constructors`.
* `unannotate@184` (`unannotate:371`): projection of the backing string. Its bare
  identity/no-copy equation is trivial. Broader interface and substring
  unwrapping behavior: `stringscovb-ann-interface`.
* `annotatedstring@308` (`annotatedstringIdentity:808`): identity specialization
  on an annotated string. Character/annotation conservation is retained under
  `stringutil-annotated-concat`.
* `annotations@418` (`annotations:392`): projection of the string metadata-vector
  reference. Broader ordered query and alias observations are retained under
  `stringscovb-ann-annotations` and `stringscovb-ann-annotate`.
* `annotations@458` (`charAnnotations:400`): projection of the character metadata
  reference. `annotated-char-append-order` observes this shared handle and its
  nontrivial content mutation; general query scope is `stringscovb-ann-annotations`.

Source sites: base/strings/annotated.jl, at the lines named above.
Model sites: JuliaLean/base/strings/annotated.lean, at the lines named above.
Pinned Julia: f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/

open JuliaLean JuliaLean.src.genericmemory_c

/-- The fixed 64-bit ABI layout of
`NamedTuple{(:label, :value), Tuple{Symbol, Any}}`, the Annotation type at
base/strings/annotated.jl:3. Both fields are pointer-bearing and stored inline,
with pointer offsets 0 and 1 in pointer-word units (byte offsets 0 and 8).
The element layout and Memory header are distinct runtime layout records.
These exact fields, flags, and byte offsets were checked with
`Base.DataTypeLayout`, `fieldoffset`, and `Base.allocatedinline` on the pinned
Julia commit f755f49a9e41380d7da126b3c1db9fe7f83dd027.
This is type metadata, not an assumed law of any storage operation. -/
def annotationElementLayout : Layout := nativeLayout 16 2 2 0 8 0

def annotationElementDatatype : Datatype :=
  ⟨annotationElementLayout, annotationElementLayout, fun i => i⟩

/-- `Memory{Annotation}` is inline, non-union, non-atomic, and unlocked.
The GenericMemory header has nfields=0, npointers=2, firstptr=0 and flags=1;
its pointer table is [0,1]. The installed native header constructor derives
these flags rather than treating Annotation as a boxed element. -/
def annotationRuntimeMetadata : Metadata :=
  { runtimeType :=
      { identity := 2
        layout := genericMemoryHeader 16 8 0 0 [1]
        elementType := .datatype annotationElementDatatype
        elementTag := .other
        kind := .notAtomic }
    typeofBottom := none
    owner := 0
    mutexBytes := 0 }

def annotationRuntimeLayout : DictLayout where
  metadata := annotationRuntimeMetadata
  nonAtomicKind := rfl
  nonAtomicFlag := rfl
  unlocked := rfl
  inlineDatatype := by
    intro _ _ _
    exact ⟨annotationElementDatatype, rfl⟩

def annotationMemoryLayout : JuliaLean.base.array.MemoryLayoutMetadata :=
  JuliaLean.base.array.MemoryLayoutMetadata.ofRuntime annotationRuntimeLayout


open JuliaLean.base.strings.annotated
open JuliaLean.base

/-- Error embedding only: no storage operation is replaced and mutations made before
an exception remain in the IO model's world. -/
def annotationArrayError : array.Error → io.Error
  | .argument message => .jl (.argumentError message)
  | .bounds => .jl .boundsError
  | .inexact => .jl (.inexactError "convert")
  | .overflow => .jl (.overflowError "checked arithmetic")
  | .divide => .jl .divideError
  | .typeError message => .foreignError "TypeError" message
  | .dimensionMismatch message => .foreignError "DimensionMismatch" message
  | .method name => .jl (.methodError name)
  | .assertion message => .foreignError "AssertionError" message
  | .concurrency message => .foreignError "ConcurrencyViolationError" message
  | .thrownNothing => .foreignError "Nothing" ""
  | .undefinedReference => .foreignError "UndefRefError" ""
  | .showError error => .showError error

def annotationArrayLift {Element Result : Type} (action : array.MutationM Element Result) :
    io.M (array.MutableMemory Element) Result := fun before =>
  let (outcome, after) := action.run before
  some (match outcome with
    | .ok value => .ok (value, after)
    | .error error => .error (annotationArrayError error, after))

/-- Adapter for a typed vector literal: actual allocation followed by typed writes.
This field is not invoked by `annotateChar`. -/
def annotationVectorNew {Element : Type} (layout : array.MemoryLayoutMetadata)
    (values : List Element) : array.MutationM Element Nat := do
  let handle ← array.mutableAllocate layout.allocation 0 (i values.length)
  array.writeValues array.mutableTypedSet handle values

/-- Materialize a vector by actual indexed reads, including UndefRefError.
This is suitable only for source operations that really read every element;
in particular it must not implement source `isempty` or `length`. -/
def annotationVectorRead {Element : Type} (handle : Nat) :
    array.MutationM Element (List Element) := do
  let length ← array.mutableLength handle
  (List.range length.val.toNat).mapM fun (index : Nat) => array.mutableGet handle (i ((index : Int) + 1))

/-- Source `resize!` with the installed vector storage and the actual bitwise-and
model, followed by typed indexed writes. This field is not invoked by annotateChar. -/
def annotationVectorWrite {Element : Type} (layout : array.MemoryLayoutMetadata)
    (handle : Nat) (values : List Element) : array.MutationM Element Unit := do
  let storage := array.mutableStorage (α := Element) layout
  let _ ← array.resize pure array.mutableLength JuliaLean.base.int.band
    (array.growbeg storage pure (array.growbegInternal storage))
    (array.growend storage pure (array.growendInternal storage))
    (array.deletebeg storage pure) (array.deleteend storage pure)
    handle (i values.length)
  let _ ← array.writeValues array.mutableTypedSet handle values
  pure ()

/-- Source `copy(::Array)` binds memory allocation, raw copying (preserving undef),
and the runtime array-header constructor. This field is not invoked by annotateChar. -/
def annotationVectorCopy {Element : Type} (layout : array.MemoryLayoutMetadata)
    (handle : Nat) : array.MutationM Element Nat :=
  JuliaLean.base.abstractarray.ArrayCallees.copyArray array.mutableRef array.mutableLength
    (fun _ count => array.memoryUndef layout.allocation (array.mutableFreshMemory 0)
      array.mutableFreshMemory count)
    (fun memory => pure (memory, array.one))
    (fun destination source count => array.memoryMove destination.1 destination.2
      source.1 source.2 count)
    array.mutableLength
    (fun reference count => do
      let heap : array.MutableMemory Element ← get
      let result := heap.arrays.length
      set { heap with arrays := heap.arrays ++ [array.MutableVector.mk reference count] }
      pure result)
    handle

/-- All Store fields use existing array models. In the property below the public
annotated.jl subject invokes only `push`; it is the actual `_push!`/`_growend!`
path in array.mutablePush, including allocation, shifts, raw copies and clearing. -/
def annotationVectorStore {Element : Type} (layout : array.MemoryLayoutMetadata) :
    Store (array.MutableMemory Element) Nat Element where
  new := fun values => annotationArrayLift (annotationVectorNew layout values)
  read := fun handle => annotationArrayLift (annotationVectorRead handle)
  push := fun handle value => annotationArrayLift (array.mutablePush layout handle value)
  write := fun handle values => annotationArrayLift (annotationVectorWrite layout handle values)
  copy := fun handle => annotationArrayLift (annotationVectorCopy layout handle)

/-- Runtime allocation invariants, without a small success-only size cutoff.
Each memory stores fixed 16-byte inline Annotation values and must have passed
genericmemory.c's native byte-size bound. Existing vector headers describe live
windows. The values of slots may be unassigned, and different headers may alias. -/
def NativeAnnotationHeap {Value : Type} (heap : array.MutableMemory (Annotation Value)) : Prop :=
  (∀ slots ∈ heap.memories, slots.length * 16 < array.maxIntVal - 1) ∧
  (∀ handle, handle < heap.arrays.length → heap.validVector handle)

/-- Mathematical byte-capacity plan for one appended Annotation. `none` means
the existing memory suffices, possibly after the source's permitted in-place slide.
The growth formula is the natural-number interpretation of array.jl:1102-1112;
its purpose is to retain the native allocation-error branch, not to assume any
content or frame property of push!. -/
def annotationAppendCapacity (capacity offset length : Nat) : Option Nat :=
  let nextLength := length + 1
  if offset - 1 + nextLength ≤ capacity then none
  else if nextLength < offset - 1 ∧ nextLength / 4 < offset - 1 - nextLength then none
  else
    let bitLength := if capacity = 0 then 0 else capacity.log2 + 1
    let extra := 3 * 2 ^ (7 * bitLength / 8) + capacity / 8
    let grown := min (2 ^ 63 - 1) (capacity + extra)
    some (max grown (offset - 1 + nextLength))

def annotationAppendFits (capacity offset length : Nat) : Bool :=
  match annotationAppendCapacity capacity offset length with
  | none => true
  | some requested => decide (requested * 16 < array.maxIntVal - 1)

/-- Appending an annotation preserves every existing metadata slot in order,
including unassigned slots, attaches the new value last, and returns the same
character and metadata-vector handle; disjoint memories and other headers are
unchanged. Native allocation-limit failures are retained and preserve the state.
Julia source: base/strings/annotated.jl:399-400; base/array.jl:1102-1112,1171-1223,1361-1365;
src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/strings/annotated.jl:69-93,394-398;
doc/src/manual/strings.md:1284-1286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AnnotateCharAppendsInOrder : Prop :=
  ∀ (C Value : Type) (before : array.MutableMemory (Annotation Value))
    (character : AnnotatedChar C Nat) (label : String) (value : Value)
    (vector : array.MutableVector) (slots : List (Option (Annotation Value))),
    NativeAnnotationHeap before →
    before.arrays[character.annotations]? = some vector →
    before.memories[vector.reference.1]? = some slots →
    let operation := annotateChar (annotationVectorStore annotationMemoryLayout)
      character label value before
    if annotationAppendFits slots.length vector.reference.2.val.toNat vector.size.val.toNat then
      ∃ after : array.MutableMemory (Annotation Value),
        operation = some (.ok (character, after)) ∧
        after.validVector character.annotations ∧
        after.contents character.annotations =
          before.contents character.annotations ++ [some ⟨label, value⟩] ∧
        after.arrays.length = before.arrays.length ∧
        (∀ other, other < before.arrays.length → other ≠ character.annotations →
          after.arrays[other]? = before.arrays[other]?) ∧
        (∀ memory, memory < before.memories.length → memory ≠ vector.reference.1 →
          after.memories[memory]? = before.memories[memory]?)
    else operation = some (.error
      (.jl (.argumentError array.genericMemorySizeMessage), before))

end JuliaLean.Proofs.base.strings.annotated.Round1

namespace JuliaLean.Proofs.base.strings.annotated

open JuliaLean.Registry

end JuliaLean.Proofs.base.strings.annotated

namespace JuliaLean.ChatGPT.Batch4.Group17
namespace AnnotationWork
open JuliaLean JuliaLean.base.array
variable {α β γ σ : Type}

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem stateExcept_pure (x : β) (old : σ) :
    (pure x : ExceptT Error (StateM σ) β).run old = (.ok x, old) := rfl

theorem stateExcept_bind (action : ExceptT Error (StateM σ) β)
    (next : β → ExceptT Error (StateM σ) γ) (old : σ) :
    (action >>= next).run old =
      match action.run old with
      | (.error e, state) => (.error e, state)
      | (.ok x, state) => (next x).run state := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action old with
  | mk r state =>
    cases r <;> rfl

theorem stateExcept_throw (e : Error) (old : σ) :
    (throw e : ExceptT Error (StateM σ) β).run old = (.error e, old) := rfl

theorem mutation_get_run (s : MutableMemory α) :
    (get : MutationM α (MutableMemory α)).run s = (.ok s, s) := rfl

theorem mutation_modify_run (f : MutableMemory α → MutableMemory α)
    (s : MutableMemory α) :
    (modify f : MutationM α Unit).run s = (.ok (), f s) := rfl

theorem mutableVector_run (s : MutableMemory α) (handle : Nat) :
    (mutableVector handle).run s =
      match s.arrays[handle]? with
      | none => (.error .bounds, s)
      | some a => (.ok a, s) := by
  simp only [mutableVector, stateExcept_bind, mutation_get_run]
  cases s.arrays[handle]? <;> rfl

theorem mutableLength_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) :
    (mutableLength handle).run s = (.ok a.size, s) := by
  simp only [mutableLength, stateExcept_bind, mutableVector_run, ha, stateExcept_pure]

theorem mutableRef_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) :
    (mutableRef handle).run s = (.ok a.reference, s) := by
  simp only [mutableRef, stateExcept_bind, mutableVector_run, ha, stateExcept_pure]

theorem memoryRead_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) :
    (memoryRead mem).run s = (.ok slots, s) := by
  simp only [memoryRead, stateExcept_bind, mutation_get_run, hm, stateExcept_pure]

theorem memoryWrite_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int)) (x : Option α) :
    (memoryWrite mem i x).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (i.val - 1).toNat x)}) := by
  simp only [memoryWrite, stateExcept_bind, memoryRead_run s mem slots hm, hi,
    and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    mutation_modify_run]

theorem mutableMemLength_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) :
    ((mutableStorage layout).memLength mem).run s = (.ok (JInt.wrap .i64 slots.length), s) := by
  change (do
    let xs ← memoryRead mem
    pure (JInt.wrap .i64 (xs.length : Int)) : MutationM α I).run s = _
  simp only [stateExcept_bind, memoryRead_run s mem slots hm, stateExcept_pure]

theorem mutableSet_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (slots : List (Option α))
    (hm : s.memories[a.reference.1]? = some slots) (i : I) (x : α)
    (hb : one ≤ i ∧ i ≤ a.size)
    (hr : 1 ≤ (a.reference.2 + i - one).val ∧
      (a.reference.2 + i - one).val ≤ (slots.length : Int)) :
    (mutableSet handle x i).run s =
      (.ok (), {s with memories := (s.memories.set a.reference.1
        (slots.set ((a.reference.2 + i - one).val - 1).toNat (some x)))}) := by
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds, stateExcept_bind,
    mutableLength_run s handle a ha, stateExcept_pure, hb, and_self, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false, mutableMemoryref,
    mutableRef_run s handle a ha, memoryWrite_run s a.reference.1 slots hm _ hr]

theorem ival_bounds (x : I) : -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 :=
  x.property

theorem ival_add (a b : I)
    (h : -9223372036854775808 ≤ a.val + b.val ∧ a.val + b.val ≤ 9223372036854775807) :
    (a + b).val = a.val + b.val := wrapInt_of_inRange .i64 _ h

theorem ival_sub (a b : I)
    (h : -9223372036854775808 ≤ a.val - b.val ∧ a.val - b.val ≤ 9223372036854775807) :
    (a - b).val = a.val - b.val := wrapInt_of_inRange .i64 _ h

theorem ival_wrap (x : Int) (h : -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807) :
    (JInt.wrap .i64 x).val = x := wrapInt_of_inRange .i64 _ h

theorem wrap64_eq (x : Int) :
    wrapInt .i64 x = (x + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 := rfl

theorem ival_add_sub (a b c : I)
    (h : -9223372036854775808 ≤ a.val + b.val - c.val ∧
      a.val + b.val - c.val ≤ 9223372036854775807) :
    (a + b - c).val = a.val + b.val - c.val := by
  change wrapInt .i64 (wrapInt .i64 (a.val + b.val) - c.val) = _
  rw [wrap64_eq, wrap64_eq]
  omega

theorem ival_one : one.val = 1 := rfl

theorem ival_zero : zero.val = 0 := rfl

theorem jlt_iff (a b : I) : a < b ↔ a.val < b.val := Iff.rfl

theorem jle_iff (a b : I) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

theorem ival_sub_one (x : I) (h : -9223372036854775807 ≤ x.val) : (x - one).val = x.val - 1 := by
  have hb := ival_bounds x
  rw [ival_sub x one (by rw [ival_one]; omega), ival_one]

theorem ival_add_one (x : I) (h : x.val ≤ 9223372036854775806) : (x + one).val = x.val + 1 := by
  have hb := ival_bounds x
  rw [ival_add x one (by rw [ival_one]; omega), ival_one]

theorem ival_add_sub_one (a b : I)
    (h : -9223372036854775808 ≤ a.val + b.val - 1 ∧ a.val + b.val - 1 ≤ 9223372036854775807) :
    (a + b - one).val = a.val + b.val - 1 := by
  rw [ival_add_sub a b one (by rw [ival_one]; exact h), ival_one]

def VecAt (s : MutableMemory α) (handle mem : Nat) (off n : I) (slots : List (Option α)) : Prop :=
  s.arrays[handle]? = some ⟨(mem, off), n⟩ ∧ s.memories[mem]? = some slots ∧
    1 ≤ off.val ∧ 0 ≤ n.val ∧ off.val - 1 + n.val ≤ (slots.length : Int) ∧ slots.length < 2 ^ 63

def vwWindow (slots : List (Option α)) (off n : I) : List (Option α) :=
  (slots.drop (off.val - 1).toNat).take n.val.toNat

theorem VecAt.contents {s : MutableMemory α} (h : VecAt s handle mem off n slots) :
    s.contents handle = vwWindow slots off n := by
  simp only [MutableMemory.contents, h.1, h.2.1, Option.getD_some, vwWindow]

theorem VecAt.valid {s : MutableMemory α} (h : VecAt s handle mem off n slots) :
    s.validVector handle := by
  obtain ⟨ha, hm, ho, hn, he, hc⟩ := h
  simp only [MutableMemory.validVector, ha, hm]
  exact ⟨hn, ho, he, hc⟩

theorem vwWindow_length (h : VecAt s handle mem off n slots) :
    (vwWindow slots off n).length = n.val.toNat := by
  obtain ⟨_, _, ho, hn, he, _⟩ := h
  simp only [vwWindow, List.length_take, List.length_drop]
  omega

theorem ms_length {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).length = mutableLength := rfl

theorem ms_ref {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).ref = mutableRef := rfl

theorem ms_memory {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).memory = Prod.fst := rfl

theorem ms_offset {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).offset = Prod.snd := rfl

theorem vwSetSize_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (n' : I) :
    ((mutableStorage layout).setSize handle n').run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨(mem, off), n'⟩}) := by
  change (do
    let v ← mutableVector handle
    modify fun s => { s with arrays := s.arrays.set handle { v with size := n' } } :
      MutationM α Unit).run s = _
  simp only [stateExcept_bind, mutableVector_run, h.1, mutation_modify_run]

attribute [local irreducible] JInt.wrap

theorem growend_fast {layout : MemoryLayoutMetadata} {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd : 0 ≤ delta.val) (hroom : delta.val ≤ (slots.length : Int) - (off.val - 1) - n.val) :
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) handle delta).run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨(mem, off), n + delta⟩}) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by omega)
  have hr1 : (JInt.wrap .i64 (slots.length : Int) - (off - one)).val =
      slots.length - (off.val - 1) := by
    rw [ival_sub _ _ (by rw [hL, hoff1]; omega), hL, hoff1]
  have hr2 : (JInt.wrap .i64 (slots.length : Int) - (off - one) - n).val =
      slots.length - (off.val - 1) - n.val := by
    rw [ival_sub _ _ (by rw [hr1]; omega), hr1]
  have hnlt : ¬ (JInt.wrap .i64 (slots.length : Int) - (off - one) - n < delta) := by
    rw [jlt_iff, hr2]; omega
  have hpos : delta ≥ zero := by rw [ge_iff_le, jle_iff, ival_zero]; exact hd
  have h' : VecAt s handle mem off n slots := ⟨ha, hm, ho, hn0, he, hc⟩
  simp only [growend, ms_ref, ms_length, ms_memory, ms_offset, stateExcept_bind, stateExcept_pure,
    hpos, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    mutableRef_run s handle _ ha, mutableLength_run s handle _ ha,
    mutableMemLength_run s mem slots hm, hnlt, vwSetSize_run s handle mem off n slots h']

theorem vwSet_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) (x : α) :
    (mutableSet handle x i).run s =
      (.ok (), { s with
        memories := s.memories.set mem (slots.set (off.val - 1 + i.val - 1).toNat (some x)) }) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hib := ival_bounds i
  have haddr : (off + i - one).val = off.val + i.val - 1 :=
    ival_add_sub_one _ _ (by omega)
  have hr := mutableSet_run s handle _ ha slots hm i x
    ⟨by rw [jle_iff, ival_one]; exact hi.1, hi.2⟩ (by simp only; rw [haddr]; omega)
  rw [hr]
  simp only [haddr]
  rw [show off.val + i.val - 1 - 1 = off.val - 1 + i.val - 1 by omega]

theorem VecAt.set {s : MutableMemory α} (h : VecAt s handle mem off n slots) (k : Nat)
    (v : Option α) :
    VecAt { s with memories := s.memories.set mem (slots.set k v) } handle mem off n
      (slots.set k v) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  exact ⟨ha, List.getElem?_set_self hlt, ho, hn0, by rw [List.length_set]; exact he,
    by rw [List.length_set]; exact hc⟩

theorem vwWindow_set (slots : List (Option α)) (off n i : I) (v : Option α)
    (ho : 1 ≤ off.val) (hi : 1 ≤ i.val) :
    vwWindow (slots.set (off.val - 1 + i.val - 1).toNat v) off n =
      (vwWindow slots off n).set (i.val - 1).toNat v := by
  simp only [vwWindow]
  rw [show (off.val - 1 + i.val - 1).toNat = (off.val - 1).toNat + (i.val - 1).toNat by omega,
    ← List.set_drop, List.take_set]

theorem list_set_last (l xs : List β) (k : Nat) (v : β) (hl : l.length = k + 1)
    (ht : l.take k = xs) : l.set k v = xs ++ [v] := by
  have hk : xs.length = k := by rw [← ht, List.length_take]; omega
  have hd : (l.drop k).length = 1 := by rw [List.length_drop]; omega
  obtain ⟨y, hy⟩ : ∃ y, l.drop k = [y] := by
    match h : l.drop k with
    | [y] => exact ⟨y, rfl⟩
    | [] => rw [h] at hd; simp at hd
    | _ :: _ :: _ => rw [h] at hd; simp at hd
  rw [← List.take_append_drop k l, ht, hy, List.set_append_right _ _ (by omega), hk]
  simp


end AnnotationWork

open JuliaLean JuliaLean.base JuliaLean.base.strings.annotated
open JuliaLean.Proofs.base.strings.annotated.Round1

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.Proofs.base.strings.annotated

open JuliaLean.Registry

def entries : List Entry := [
  { id := "annotated-char-append-order",
    juliaFile := "base/strings/annotated.jl",
    juliaFns := ["annotate!(::AnnotatedChar,::Symbol,::Any)"],
    statement := "annotate! on an AnnotatedChar appends the labeled value after every existing annotation, keeps undefined slots and earlier annotations in order, returns the same character and shared annotation vector, leaves every other vector and memory unchanged, and fails exactly when the grown vector exceeds the native allocation limit.",
    source := "base/strings/annotated.jl:69-93,394-400; base/array.jl:1102-1112,1171-1223,1361-1365; src/genericmemory.c:55-73",
    status := .todo,
    prop := ``Round1.AnnotateCharAppendsInOrder,
    thm := none }
]

end JuliaLean.Proofs.base.strings.annotated
