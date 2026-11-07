import JuliaLean.base.genericmemory
import JuliaLean.src.genericmemory_c
import JuliaLean.base.cmem
import JuliaLean.base.essentials
import JuliaLean.base.operators
import JuliaLean.base.tuple
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types

/-!
# Properties of `base/genericmemory.jl`

The statements below describe the public contracts and memory invariants of the typed methods in
`JuliaLean.base.genericmemory`. Runtime allocation, pointer, bounds, conversion, and atomic storage
operations remain typed callees supplied by their owning Base or runtime modules.
-/

namespace JuliaLean.Proofs.base.genericmemory

open JuliaLean JuliaLean.base.genericmemory JuliaLean.Registry
open JuliaLean.src.genericmemory_c (interpretSlots dictUnsetEffects boxedDictLayout)

abbrev I64 := JuliaLean.base.genericmemory.I64

/-- GenericMemory uses the linear indexing style of its DenseVector interface. -/
def MemoryLinearIndexing : Prop :=
  ∀ (memoryType : GenericMemoryType), indexStyle memoryType = .linear

/-- A valid reference's reported index is one-based and lies in its backing memory. -/
def MemoryIndexIsOneBased : Prop :=
  ∀ {M P : Type} (memoryrefoffset : GenericMemoryRef M P → I64) (length : I64)
    (ref : GenericMemoryRef M P),
    1 ≤ (memoryrefoffset ref).val → (memoryrefoffset ref).val ≤ length.val →
      1 ≤ (memoryindex memoryrefoffset ref).val ∧
        (memoryindex memoryrefoffset ref).val ≤ length.val

/-- An out-of-bounds checked assignment query returns false without reading a slot. -/
def MemoryIsassignedBounds : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V) (a : M) (i : I64),
    ops.checkboundsBool a i = some false → isassignedMemory ops true a i = some false) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P) (assigned : Bool),
    ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true = some assigned →
      isassignedRef ops true ref = some assigned)

/-- Checked memory-reference copies and range assignment stop when their bounds check fails. -/
def GenericMemoryCheckedAccessesInBounds : Prop :=
  (∀ {M P T D S N I Ptr Token : Type}
      (copy : MemoryCopyOps Option M P D S N I Ptr Token)
      (dest src : GenericMemoryRef M P) (n : N),
    copy.isZero n = false → copy.checkEnd dest n = none →
      unsafeCopytoRefs (T := T) copy true dest src n = none) ∧
  (∀ {M P T I : Type} (copy : MemoryCopyOps Option M P I64 I64 I64 I64 P Unit)
      (checkbounds : M → I → Option Unit) (rangeLength rangeFirst : I → Option I64)
      (shapeCheck : M → I64 → Option Unit) (a x : M) (indices : I),
    checkbounds a indices = none →
      setindexMemoryRange (T := T) copy checkbounds rangeLength rangeFirst shapeCheck true a x indices = none)

abbrev HeapM (T : Type) := StateM (Nat → Option T)

def heapCopiedElements {T : Type} (heap : Nat → Option T)
    (dest src count address : Nat) : Option T :=
  if dest ≤ address ∧ address < dest + count then
    heap (src + (address - dest))
  else heap address

def heapCopyWindow {T : Type} (dest src : Nat) (n : I64) : HeapM T Unit :=
  fun heap => ((), fun address => heapCopiedElements heap dest src n.val.toNat address)

def heapContents {T : Type} (mem : Nat) (offset n : I64) : HeapM T (List (Option T)) :=
  fun heap => ((List.range n.val.toNat).map fun i =>
    heap (mem + (offset.val - 1).toNat + i), heap)

def heapRefContents {T : Type} (ref : GenericMemoryRef Nat Nat) (n : I64) :
    HeapM T (List (Option T)) :=
  fun heap => ((List.range n.val.toNat).map fun i => heap (ref.ptr_or_offset + i), heap)

def heapCopyOps {T : Type} :
    MemoryCopyOps (HeapM T) Nat Nat I64 I64 I64 I64 Nat Unit :=
  { isZero := fun n => n == 0
    toInt := fun n => pure n
    byteCount := fun _ n => pure n
    checkEnd := fun ref _ => pure ref
    memoryrefDest := fun mem i => pure ⟨mem, mem + (i.val - 1).toNat⟩
    memoryrefSource := fun mem i => pure ⟨mem, mem + (i.val - 1).toNat⟩
    memoryrefoffset := fun ref => JInt.wrap .i64 (Int.ofNat (ref.ptr_or_offset - ref.mem + 1))
    isBitsType := fun _ => true
    gcPreserveBegin := fun _ => ()
    gcPreserveEnd := fun _ => pure ()
    unsafeConvert := fun ref => pure ref.ptr_or_offset
    memmove := fun dest src n => heapCopyWindow dest src n
    ccallCopy := fun _ dest _ src n => heapCopyWindow dest src n
    pointerDest := fun mem i => pure (mem + (i.val - 1).toNat)
    pointerSource := fun mem i => pure (mem + (i.val - 1).toNat)
    pointerLess := fun a b => a < b
    pointerGreater := fun a b => a > b
    sourceEnd := fun soffs n => pure (soffs + n - 1)
    forwardRange := fun n => pure ((List.range n.val.toNat).map fun i =>
      JInt.wrap .i64 (Int.ofNat i))
    backwardRange := fun n => pure (((List.range n.val.toNat).reverse).map fun i =>
      JInt.wrap .i64 (Int.ofNat i))
    destIndex := fun doffs i => pure (JInt.wrap .i64 (doffs.val + i.val))
    sourceIndex := fun soffs i => pure (JInt.wrap .i64 (soffs.val + i.val)) }

theorem heapCopiedElements_zero {T : Type} (heap : Nat → Option T) (dest src : Nat) :
    (fun address => heapCopiedElements heap dest src 0 address) = heap := by
  funext address
  simp [heapCopiedElements]
  omega

theorem heapCopiedElements_at {T : Type} (heap : Nat → Option T)
    (dest src count i : Nat) (hi : i < count) :
    heapCopiedElements heap dest src count (dest + i) = heap (src + i) := by
  simp [heapCopiedElements]
  omega

theorem heapCopyWindow_contents {T : Type} (heap : Nat → Option T)
    (dest src count : Nat) :
    (List.range count).map
      (fun i => heapCopiedElements heap dest src count (dest + i)) =
    (List.range count).map (fun i => heap (src + i)) := by
  apply List.map_congr_left
  intro i hi
  exact heapCopiedElements_at heap dest src count i (List.mem_range.mp hi)
theorem heapI64ZeroVal : (0 : I64).val = 0 := rfl
theorem heapI64OneVal : (1 : I64).val = 1 := rfl

theorem heapMemoryTypedCopy_state {T : Type} (heap : Nat → Option T)
    (dest src : Nat) (doffs soffs n : I64) :
    (unsafeCopytoMemoryTyped (T := T) (heapCopyOps (T := T)) false
      dest doffs src soffs n).run heap =
      (dest, fun address => heapCopiedElements heap
        (dest + (doffs.val - 1).toNat) (src + (soffs.val - 1).toNat)
        n.val.toNat address) := by
  by_cases hnzero : n.val = 0
  · simp [unsafeCopytoMemoryTyped, unsafeCopytoRefs, heapCopyOps, heapCopyWindow,
      hnzero, heapCopiedElements_zero, heapI64ZeroVal, ExceptT.run, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, StateT.run, StateT.bind,
      StateT.pure, Bind.bind, Pure.pure]
  · simp [unsafeCopytoMemoryTyped, unsafeCopytoRefs, heapCopyOps, heapCopyWindow,
      hnzero, heapI64ZeroVal, ExceptT.run, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, StateT.run, StateT.bind, StateT.pure,
      Bind.bind, Pure.pure]

theorem heapMemoryTypedCopy_contents {T : Type} (heap : Nat → Option T)
    (dest src : Nat) (doffs soffs n : I64) :
    (((do
      let _ ← unsafeCopytoMemoryTyped (T := T) (heapCopyOps (T := T)) false
        dest doffs src soffs n
      heapContents dest doffs n).run heap).1) =
    ((heapContents src soffs n).run heap).1 := by
  simp only [StateT.run_bind, heapMemoryTypedCopy_state]
  simp [heapContents, heapCopyWindow_contents, StateT.run, StateT.pure, Bind.bind, Pure.pure]

theorem heapMemoryRefsCopy_state {T : Type} (heap : Nat → Option T)
    (dest src : GenericMemoryRef Nat Nat) (n : I64) :
    (unsafeCopytoRefs (T := T) (heapCopyOps (T := T)) false dest src n).run heap =
      (dest, fun address => heapCopiedElements heap dest.ptr_or_offset
        src.ptr_or_offset n.val.toNat address) := by
  by_cases hnzero : n.val = 0
  · simp [unsafeCopytoRefs, heapCopyOps, heapCopyWindow, hnzero,
      heapCopiedElements_zero, heapI64ZeroVal, ExceptT.run, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, StateT.run, StateT.bind,
      StateT.pure, Bind.bind, Pure.pure]
  · simp [unsafeCopytoRefs, heapCopyOps, heapCopyWindow, hnzero, heapI64ZeroVal,
      ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
      StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]

theorem heapMemoryRefsCopy_contents {T : Type} (heap : Nat → Option T)
    (dest src : GenericMemoryRef Nat Nat) (n : I64) :
    ((do
      let _ ← unsafeCopytoRefs (T := T) (heapCopyOps (T := T)) false dest src n
      heapRefContents dest n).run heap).1 =
    (List.range n.val.toNat).map fun i => heap (src.ptr_or_offset + i) := by
  simp only [StateT.run_bind, heapMemoryRefsCopy_state]
  simp [heapRefContents, heapCopyWindow_contents, StateT.run, StateT.pure, Bind.bind, Pure.pure]

theorem heapMemoryCopy_state {T : Type} (heap : Nat → Option T)
    (src : Nat) (n : I64) :
    (copyMemory (T := T) (heapCopyOps (T := T))
      (fun _ => pure n) (fun _ => pure 1000) src).run heap =
      (1000, fun address => heapCopiedElements heap 1000 src n.val.toNat address) := by
  change (unsafeCopytoMemoryTyped (T := T) (heapCopyOps (T := T))
    false 1000 1 src 1 n).run heap = _
  simpa [heapI64ZeroVal, heapI64OneVal] using
    heapMemoryTypedCopy_state (T := T) heap 1000 src 1 1 n

theorem heapMemoryCopy_contents {T : Type} (heap : Nat → Option T)
    (src : Nat) (n : I64) :
    ((do
      let result ← copyMemory (T := T) (heapCopyOps (T := T))
        (fun _ => pure n) (fun _ => pure 1000) src
      heapContents result 1 n).run heap).1 =
    (List.range n.val.toNat).map fun i => heap (src + i) := by
  simp only [StateT.run_bind, heapMemoryCopy_state]
  simp [heapContents, heapI64OneVal, heapCopyWindow_contents, StateT.run,
    StateT.bind, StateT.pure, Bind.bind, Pure.pure]
abbrev SlotHeap (T : Type) := Nat → I64 → Option T
abbrev SlotM (T : Type) := StateM (SlotHeap T)

def slotIndex (i : Nat) : I64 := JInt.wrap .i64 (Int.ofNat (i + 1))
theorem slotIndex_cast (i : Nat) :
    slotIndex i = JInt.wrap .i64 ((i : Int) + 1) := by
  change JInt.wrap .i64 ((i + 1 : Nat) : Int) =
    JInt.wrap .i64 ((i : Nat) + 1)
  rw [Int.natCast_add, Int.natCast_one]
theorem slotI64ZeroVal : (0 : I64).val = 0 := by
  change wrapInt .i64 0 = 0
  exact wrapInt_of_inRange .i64 0 (by decide)

theorem slotI64EqZero (n : I64) : (n == 0) = true ↔ n.val = 0 := by
  change (n.val == (0 : I64).val) = true ↔ n.val = 0
  rw [slotI64ZeroVal]
  simp

def slotRead {T : Type} (mem : Nat) (index : I64) : SlotM T (Option T) :=
  fun heap => (heap mem index, heap)

def slotWrite {T : Type} (mem : Nat) (index : I64) (value : Option T) : SlotM T Unit :=
  fun heap => ((), fun other key => if other == mem && key == index then value else heap other key)

@[simp] theorem boxedSlotUnsetProjection {T : Type} (old : Option T) :
    (interpretSlots (dictUnsetEffects boxedDictLayout 0) 1 (fun _ => old)) 1 = none := by
  rfl

def slotAccessOps {T : Type} [Inhabited T] :
    MemoryAccessOps (JuliaLean.Proofs.base.genericmemory.SlotM T) Nat I64 T T :=
  { memoryref := fun mem => pure ⟨mem, 1⟩
    memoryrefAt := fun mem index => pure ⟨mem, index⟩
    memoryrefNew := fun ref index _ => pure ⟨ref.mem, index⟩
    memoryrefIsAssigned := fun ref _ _ => do
      let value ← JuliaLean.Proofs.base.genericmemory.slotRead ref.mem ref.ptr_or_offset
      pure value.isSome
    memoryrefUnset := fun ref _ _ => do
      let old ← JuliaLean.Proofs.base.genericmemory.slotRead ref.mem ref.ptr_or_offset
      let value := (interpretSlots (dictUnsetEffects boxedDictLayout 0) 1 (fun _ => old)) 1
      JuliaLean.Proofs.base.genericmemory.slotWrite ref.mem ref.ptr_or_offset value
    memoryrefSet := fun ref value _ _ =>
      JuliaLean.Proofs.base.genericmemory.slotWrite ref.mem ref.ptr_or_offset (some value)
    defaultOrderMemory := fun _ => .notAtomic
    defaultOrderRef := fun _ => .notAtomic
    checkboundsBool := fun _ _ => pure true
    checkbounds := fun _ _ => pure ()
    castElement := some
    convertElement := fun value => pure value
    getindex := fun mem index => do
      let value ← JuliaLean.Proofs.base.genericmemory.slotRead mem index
      pure (value.getD default) }

def slotConvertAccessOps {T : Type} [Inhabited T] (convert : T → T) :
    MemoryAccessOps (SlotM T) Nat I64 T T :=
  { slotAccessOps with
    castElement := fun _ => none
    convertElement := fun value => pure (convert value) }

def slotCopyOps {T : Type} (isBits : Bool) :
    MemoryCopyOps (SlotM T) Nat I64 I64 I64 I64 Nat (Nat × I64) Unit :=
  { isZero := fun n => n == 0
    toInt := fun n => pure n
    byteCount := fun _ n => pure n
    checkEnd := fun ref _ => pure ref
    memoryrefDest := fun mem offset => pure ⟨mem, offset⟩
    memoryrefSource := fun mem offset => pure ⟨mem, offset⟩
    memoryrefoffset := fun ref => ref.ptr_or_offset
    isBitsType := fun _ => isBits
    gcPreserveBegin := fun _ => ()
    gcPreserveEnd := fun _ => pure ()
    unsafeConvert := fun ref => pure (ref.mem, ref.ptr_or_offset)
    memmove := fun dest src n => fun heap =>
      ((), fun mem index =>
        if mem == dest.1 && dest.2.val ≤ index.val && index.val < dest.2.val + n.val
        then heap src.1 (JInt.wrap .i64 (src.2.val + (index.val - dest.2.val)))
        else heap mem index)
    ccallCopy := fun dest doffs src soffs n => fun heap =>
      ((), fun mem index =>
        if mem == dest && doffs.val ≤ index.val && index.val < doffs.val + n.val
        then heap src (JInt.wrap .i64 (soffs.val + (index.val - doffs.val)))
        else heap mem index)
    pointerDest := fun mem offset => pure (mem, offset)
    pointerSource := fun mem offset => pure (mem, offset)
    pointerLess := fun _ _ => true
    pointerGreater := fun _ _ => false
    sourceEnd := fun soffs n => pure (soffs + n - 1)
    forwardRange := fun n => pure (List.range n.val.toNat)
    backwardRange := fun n => pure (List.range n.val.toNat).reverse
    destIndex := fun _ i => pure (slotIndex i)
    sourceIndex := fun _ i => pure (slotIndex i) }

def memoryFallbackStep {m : Type → Type} [Monad m]
    {M P TD TS VS D S N I Ptr Token : Type}
    (destOps : MemoryAccessOps m M P TD VS) (srcOps : MemoryAccessOps m M P TS VS)
    (copy : MemoryCopyOps m M P D S N I Ptr Token)
    (dest : M) (doffs : D) (src : M) (soffs : S) (i : I) : m Unit := do
  let sourceIndex ← copy.sourceIndex soffs i
  if ← isassignedMemory srcOps false src sourceIndex then
    let destIndex ← copy.destIndex doffs i
    let value ← srcOps.getindex src sourceIndex
    let _ ← setindexMemory destOps destOps.convertElement pure false dest value destIndex
    pure ()
  else
    let destIndex ← copy.destIndex doffs i
    let _ ← unsetindexMemoryInt destOps false dest destIndex
    pure ()

def slotUpdatedHeap {T : Type} (heap : SlotHeap T) (convert : T → T)
    (dest src i : Nat) : SlotHeap T :=
  fun other key =>
    if other == dest && key == slotIndex i
    then (heap src (slotIndex i)).map convert
    else heap other key

def slotCopiedHeap {T : Type} (convert : T → T) (dest src : Nat) :
    SlotHeap T → List Nat → SlotHeap T
  | heap, [] => heap
  | heap, i :: is =>
      slotCopiedHeap convert dest src (slotUpdatedHeap heap convert dest src i) is

def slotFallbackStep {T : Type} [Inhabited T] (convert : T → T)
    (dest src : Nat) (i : Nat) : SlotM T (ForInStep PUnit) := do
  let sourceIndex ← (slotCopyOps (T := T) false).sourceIndex 1 i
  if ← isassignedMemory slotAccessOps false src sourceIndex then
    let destIndex ← (slotCopyOps (T := T) false).destIndex 1 i
    let value ← slotAccessOps.getindex src sourceIndex
    let _ ← setindexMemory (slotConvertAccessOps convert) (slotConvertAccessOps convert).convertElement pure false dest value destIndex
  else
    let destIndex ← (slotCopyOps (T := T) false).destIndex 1 i
    let _ ← unsetindexMemoryInt (slotConvertAccessOps convert) false dest destIndex
  pure (ForInStep.yield PUnit.unit)

theorem slotFallbackStep_state {T : Type} [Inhabited T] (heap : SlotHeap T)
    (convert : T → T) (dest src i : Nat) :
    (slotFallbackStep convert dest src i).run heap =
      (ForInStep.yield PUnit.unit, slotUpdatedHeap heap convert dest src i) := by
  cases hsource : heap src (slotIndex i) with
  | none =>
    have hsource' : heap src (JInt.wrap .i64 ((i : Int) + 1)) = none := by
      rw [← slotIndex_cast i]
      exact hsource
    simp [slotFallbackStep, slotCopyOps, slotAccessOps, slotConvertAccessOps,
      slotIndex, isassignedMemory, setindexMemory, setindexMemoryRaw,
      unsetindexMemoryInt, unsetindexRef, slotRead, slotWrite, hsource',
      StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    apply Prod.ext
    · rfl
    · funext other key
      simp [slotUpdatedHeap, slotIndex_cast, hsource']
  | some value =>
    have hsource' : heap src (JInt.wrap .i64 ((i : Int) + 1)) = some value := by
      rw [← slotIndex_cast i]
      exact hsource
    simp [slotFallbackStep, slotCopyOps, slotAccessOps, slotConvertAccessOps,
      slotIndex, isassignedMemory, setindexMemory, setindexMemoryRaw,
      unsetindexMemoryInt, unsetindexRef, slotRead, slotWrite, hsource',
      StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    apply Prod.ext
    · rfl
    · funext other key
      simp [slotUpdatedHeap, slotIndex_cast, hsource']

def slotFallbackLoopList {T : Type} [Inhabited T] (convert : T → T)
    (dest src : Nat) (indices : List Nat) : SlotM T PUnit :=
  forIn indices PUnit.unit (fun i _ => slotFallbackStep convert dest src i)

theorem slotFallbackLoopList_state {T : Type} [Inhabited T]
    (heap : SlotHeap T) (convert : T → T) (dest src : Nat)
    (indices : List Nat) :
    (slotFallbackLoopList convert dest src indices).run heap =
      (PUnit.unit, slotCopiedHeap convert dest src heap indices) := by
  induction indices generalizing heap with
  | nil => simp [slotFallbackLoopList, slotCopiedHeap, StateT.run, StateT.pure, Pure.pure]
  | cons i is ih =>
    simp only [slotFallbackLoopList, List.forIn_cons, StateT.run_bind]
    rw [slotFallbackStep_state]
    change (slotFallbackLoopList convert dest src is).run
        (slotUpdatedHeap heap convert dest src i) =
      (PUnit.unit, slotCopiedHeap convert dest src heap (i :: is))
    rw [ih]
    rfl

def slotContentsOnKeys {T : Type} (heap : SlotHeap T) (mem : Nat)
    (keys : List I64) : List (Option T) :=
  keys.map (heap mem)

def convertedSlots {T : Type} (xs : List (Option T)) (convert : T → T) : List (Option T) :=
  xs.map (Option.map convert)

theorem slotCopiedHeap_lookup {T : Type} (heap : SlotHeap T) (convert : T → T)
    (dest src : Nat) (keys : List Nat) (index : I64) (hds : src ≠ dest) :
    slotCopiedHeap convert dest src heap keys dest index =
      if index ∈ keys.map slotIndex then (heap src index).map convert else heap dest index := by
  induction keys generalizing heap with
  | nil => simp [slotCopiedHeap]
  | cons i is ih =>
    simp only [slotCopiedHeap, List.map_cons, List.mem_cons]
    rw [ih]
    have hs : slotUpdatedHeap heap convert dest src i src index = heap src index := by
      simp [slotUpdatedHeap, hds]
    by_cases hk : index = slotIndex i
    · subst index
      simp [slotUpdatedHeap, hds, hs]
    · have hindex : index.val ≠ (slotIndex i).val := by
        intro hval
        apply hk
        exact Subtype.ext hval
      by_cases ht : index ∈ List.map slotIndex is
      · simp [slotUpdatedHeap, hds, hk, ht, hs, hindex]
      · simp [slotUpdatedHeap, hds, hk, ht, hs, hindex]

theorem slotFallbackContentsOnKeys {T : Type} (heap : SlotHeap T)
    (convert : T → T) (n : I64) :
    slotContentsOnKeys
      (slotCopiedHeap convert 0 1 heap (List.range n.val.toNat)) 0
      ((List.range n.val.toNat).map slotIndex) =
    convertedSlots (slotContentsOnKeys heap 1 ((List.range n.val.toNat).map slotIndex)) convert := by
  have hright :
      convertedSlots (slotContentsOnKeys heap 1
        ((List.range n.val.toNat).map slotIndex)) convert =
      ((List.range n.val.toNat).map slotIndex).map
        (fun index => (heap 1 index).map convert) := by
    simp [convertedSlots, slotContentsOnKeys, List.map_map, Function.comp_def]
  rw [hright]
  change List.map
      (fun index => slotCopiedHeap convert 0 1 heap (List.range n.val.toNat) 0 index)
      ((List.range n.val.toNat).map slotIndex) =
    List.map (fun index => (heap 1 index).map convert)
      ((List.range n.val.toNat).map slotIndex)
  apply List.map_congr_left
  intro index hin
  rcases List.mem_map.mp hin with ⟨i, hi, rfl⟩
  have hkey : slotIndex i ∈ (List.range n.val.toNat).map slotIndex :=
    List.mem_map.mpr ⟨i, hi, rfl⟩
  rw [slotCopiedHeap_lookup heap convert 0 1 (List.range n.val.toNat)
    (slotIndex i) (by decide)]
  simp [hkey]

def slotFallbackExpected {T : Type} [Inhabited T]
    (convert : T → T) (n : I64) : SlotM T Nat := do
  if (slotCopyOps (T := T) false).isZero n then return 0
  let _ ← (slotCopyOps (T := T) false).pointerDest 0 1
  let _ ← (slotCopyOps (T := T) false).pointerSource 1 1
  let endOffset ← (slotCopyOps (T := T) false).sourceEnd 1 n
  let _ ← (slotCopyOps (T := T) false).pointerSource 1 endOffset
  let indices ← (slotCopyOps (T := T) false).forwardRange n
  let _ ← slotFallbackLoopList convert 0 1 indices
  return 0

theorem slotUnsafeCopyFallback_action {T : Type} [Inhabited T]
    (convert : T → T) (n : I64) :
    unsafeCopytoMemoryFallback (slotConvertAccessOps convert) slotAccessOps
      (slotCopyOps false) (slotConvertAccessOps convert).convertElement pure 0 1 1 1 n =
    slotFallbackExpected convert n := by
  by_cases hzero : n.val = 0
  · have hz : (n == 0) = true := (slotI64EqZero n).mpr hzero
    simp [unsafeCopytoMemoryFallback, slotFallbackExpected, slotCopyOps,
      slotAccessOps, slotConvertAccessOps, slotFallbackLoopList, slotFallbackStep,
      isassignedMemory, setindexMemory, setindexMemoryRaw,
      unsetindexMemoryInt, unsetindexRef, slotRead, slotWrite, slotIndex,
      slotI64ZeroVal, hzero, hz, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
  · have hz : (n == 0) = false := by
      cases heq : n == 0 with
      | false => rfl
      | true =>
          have hval : n.val = 0 := (slotI64EqZero n).mp heq
          omega
    simp [unsafeCopytoMemoryFallback, slotFallbackExpected, slotCopyOps,
      slotAccessOps, slotConvertAccessOps, slotFallbackLoopList, slotFallbackStep,
      isassignedMemory, setindexMemory, setindexMemoryRaw,
      unsetindexMemoryInt, unsetindexRef, slotRead, slotWrite, slotIndex,
      slotI64ZeroVal, hzero, hz, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
  all_goals rfl

theorem slotFallbackExpected_run {T : Type} [Inhabited T]
    (heap : SlotHeap T) (convert : T → T) (n : I64) (hpos : 0 < n.val) :
    (slotFallbackExpected convert n).run heap =
      (0, slotCopiedHeap convert 0 1 heap (List.range n.val.toNat)) := by
  have hz : (n == 0) = false := by
    cases heq : n == 0 with
    | false => rfl
    | true =>
        have hval : n.val = 0 := (slotI64EqZero n).mp heq
        omega
  have hnz : n.val ≠ 0 := by omega
  simp [slotFallbackExpected, slotCopyOps, hz, hnz, slotI64ZeroVal,
    StateT.run_bind, StateT.run_pure, StateT.run]
  change StateT.run
    ((fun _ : PUnit => 0) <$> slotFallbackLoopList convert 0 1
      (List.range n.val.toNat)) heap =
    (0, slotCopiedHeap convert 0 1 heap (List.range n.val.toNat))
  rw [StateT.run_map, slotFallbackLoopList_state heap convert 0 1
    (List.range n.val.toNat)]
  rfl

theorem slotUnsafeCopyFallback_contents {T : Type} [Inhabited T]
    (heap : SlotHeap T) (convert : T → T) (n : I64) (hn : 0 ≤ n.val) :
    slotContentsOnKeys
      ((unsafeCopytoMemoryFallback (slotConvertAccessOps convert) slotAccessOps
        (slotCopyOps false) (slotConvertAccessOps convert).convertElement pure 0 1 1 1 n).run heap).2 0
      ((List.range n.val.toNat).map slotIndex) =
    convertedSlots (slotContentsOnKeys heap 1
      ((List.range n.val.toNat).map slotIndex)) convert := by
  by_cases hzero : n.val = 0
  · have hz : (n == 0) = true := (slotI64EqZero n).mpr hzero
    have hrun :
        (unsafeCopytoMemoryFallback (slotConvertAccessOps convert) slotAccessOps
          (slotCopyOps false) (slotConvertAccessOps convert).convertElement pure 0 1 1 1 n).run heap = (0, heap) := by
      rw [slotUnsafeCopyFallback_action]
      simp [slotFallbackExpected, slotCopyOps, hz, hzero, slotI64ZeroVal,
        StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    rw [hrun]
    simp [slotContentsOnKeys, convertedSlots, hzero]
  · have hpos : 0 < n.val := by omega
    have hrun :
        (unsafeCopytoMemoryFallback (slotConvertAccessOps convert) slotAccessOps
          (slotCopyOps false) (slotConvertAccessOps convert).convertElement pure 0 1 1 1 n).run heap =
          (0, slotCopiedHeap convert 0 1 heap (List.range n.val.toNat)) := by
      rw [slotUnsafeCopyFallback_action,
        slotFallbackExpected_run heap convert n hpos]
    rw [hrun]
    exact slotFallbackContentsOnKeys heap convert n
/-- Concrete typed and fallback copy models preserve source contents and undefined slots. -/
def MemoryCopyPreservesContents : Prop :=
  (∀ {T : Type} (heap : Nat → Option T) (dest src : Nat) (doffs soffs n : I64),
    (((do
      let _ ← unsafeCopytoMemoryTyped (T := T) (heapCopyOps (T := T)) false
        dest doffs src soffs n
      heapContents dest doffs n).run heap).1) =
      ((heapContents src soffs n).run heap).1) ∧
  (∀ {T : Type} (heap : Nat → Option T)
      (dest src : GenericMemoryRef Nat Nat) (n : I64),
    ((do
      let _ ← unsafeCopytoRefs (T := T) (heapCopyOps (T := T)) false dest src n
      heapRefContents dest n).run heap).1 =
      (List.range n.val.toNat).map fun i => heap (src.ptr_or_offset + i)) ∧
  (∀ {T : Type} [Inhabited T] (heap : SlotHeap T) (convert : T → T) (n : I64),
    0 ≤ n.val →
      slotContentsOnKeys
        ((unsafeCopytoMemoryFallback (slotConvertAccessOps convert) slotAccessOps
          (slotCopyOps false) (slotConvertAccessOps convert).convertElement pure 0 1 1 1 n).run heap).2 0
        ((List.range n.val.toNat).map slotIndex) =
      convertedSlots (slotContentsOnKeys heap 1
        ((List.range n.val.toNat).map slotIndex)) convert) ∧
  (∀ {T : Type} (heap : Nat → Option T) (src : Nat) (n : I64),
    ((do
      let result ← copyMemory (T := T) (heapCopyOps (T := T))
        (fun _ => pure n) (fun _ => pure 1000) src
      heapContents result 1 n).run heap).1 =
      (List.range n.val.toNat).map fun i => heap (src + i))

theorem memoryCopyPreservesContents_proven : MemoryCopyPreservesContents := by
  exact ⟨heapMemoryTypedCopy_contents, heapMemoryRefsCopy_contents,
    slotUnsafeCopyFallback_contents, heapMemoryCopy_contents⟩

/-- Generic memory references select the typed or conversion-aware copy path by element type. -/
def MemoryCopyDispatchesByElementType : Prop :=
  (∀ {m : Type → Type} {M P TD TS VS N I Ptr Token : Type} [Monad m]
      (destOps : MemoryAccessOps m M P TD VS) (srcOps : MemoryAccessOps m M P TS VS)
      (copy : MemoryCopyOps m M P I64 I64 N I Ptr Token)
      (memoryrefoffset : GenericMemoryRef M P → I64)
      (dest src : GenericMemoryRef M P) (n : N) (same : TD = TS),
    copy.isZero n = false →
      unsafeCopytoGenericRefs destOps srcOps copy destOps.convertElement pure false memoryrefoffset
        (isTrue same) dest src n =
        (do
          let _ ← unsafeCopytoMemoryTyped (T := TD) copy false dest.mem
            (memoryrefoffset dest) src.mem (memoryrefoffset src) n
          return dest)) ∧
  (∀ {m : Type → Type} {M P TD TS VS N I Ptr Token : Type} [Monad m]
      (destOps : MemoryAccessOps m M P TD VS) (srcOps : MemoryAccessOps m M P TS VS)
      (copy : MemoryCopyOps m M P I64 I64 N I Ptr Token)
      (memoryrefoffset : GenericMemoryRef M P → I64)
      (dest src : GenericMemoryRef M P) (n : N) (different : TD ≠ TS),
    copy.isZero n = false →
      unsafeCopytoGenericRefs destOps srcOps copy destOps.convertElement pure false memoryrefoffset
        (isFalse different) dest src n =
        (do
          let _ ← unsafeCopytoMemoryFallback destOps srcOps copy destOps.convertElement pure dest.mem
            (memoryrefoffset dest) src.mem (memoryrefoffset src) n
          return dest))

theorem memoryCopyDispatchesByElementType_proven :
    MemoryCopyDispatchesByElementType := by
  constructor <;> intros <;> simp [unsafeCopytoGenericRefs, *]
/-- Unsetting a memory slot returns its original reference or memory object, and after a
successful runtime unset its reference reads unassigned. -/
def MemoryUnsetReturnsTarget : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P),
    ops.memoryrefUnset ref .notAtomic true = some () →
      unsetindexRef ops true ref = some ref) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (a : M) (i : I64) (ref : GenericMemoryRef M P),
    ops.memoryrefAt a i = some ref → ops.memoryrefUnset ref .notAtomic true = some () →
      unsetindexMemoryInt ops true a i = some a) ∧
  (∀ {M P T V I : Type} (ops : MemoryAccessOps Option M P T V)
      (toIndex : I → Option I64) (unsetArray : Unit → I64 → Option Unit)
      (a : M) (i : I) (index : I64) (ref : GenericMemoryRef M P),
    toIndex i = some index → ops.memoryrefAt a index = some ref →
      ops.memoryrefUnset ref .notAtomic true = some () →
        unsetindexUnionInteger ops true toIndex unsetArray (.memory a) i = some (.memory a)) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V) (ref : GenericMemoryRef M P),
    (do
      ops.memoryrefUnset ref .notAtomic true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let result ← unsetindexRef ops true ref
        let assigned ← ops.memoryrefIsAssigned result (ops.defaultOrderRef result) true
        pure (result, assigned)) = pure (ref, false)) ∧
  (∀ {M P T V : Type}
      (ops : MemoryAccessOps Option M P T V) (a : M) (i : I64),
    (do
      let ref ← ops.memoryrefAt a i
      ops.memoryrefUnset ref .notAtomic true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let _ ← unsetindexMemoryInt ops true a i
        let ref ← ops.memoryrefAt a i
        ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false) ∧
  (∀ {A I P T V : Type}
      (ops : MemoryAccessOps Option A P T V) (toIndex : I → Option I64)
      (unsetArray : A → I64 → Option Unit) (isassignedArray : A → I64 → Option Bool)
      (array : A) (i : I) (index : I64),
    toIndex i = pure index →
      (do unsetArray array index; isassignedArray array index) = pure false →
        (do
          let _ ← unsetindexUnionInteger ops false toIndex unsetArray (.array array) i
          isassignedArray array index) = pure false)

/-- Atomic unsetting forwards the requested order, returns the same reference or memory object,
and after a successful runtime atomic unset its reference reads unassigned. -/
def AtomicMemoryUnsetReturnsReference : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P) (order : MemoryOrder),
    ops.memoryrefUnset ref order true = some () →
      unsetindexAtomicRef ops true ref order = some ref) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (a : M) (i : I64) (ref : GenericMemoryRef M P) (order : MemoryOrder),
    ops.memoryrefAt a i = some ref → ops.memoryrefUnset ref order true = some () →
      unsetindexAtomicMemoryInt ops true a order i = some a) ∧
  (∀ {M P T V I : Type} (ops : MemoryAccessOps Option M P T V)
      (toIndex : I → Option I64) (a : M) (i : I) (index : I64)
      (ref : GenericMemoryRef M P) (order : MemoryOrder),
    toIndex i = some index → ops.memoryrefAt a index = some ref →
      ops.memoryrefUnset ref order true = some () →
        unsetindexAtomicMemoryInteger ops true toIndex a order i = some a) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P) (order : MemoryOrder),
    (do
      ops.memoryrefUnset ref order true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let result ← unsetindexAtomicRef ops true ref order
        let assigned ← ops.memoryrefIsAssigned result (ops.defaultOrderRef result) true
        pure (result, assigned)) = pure (ref, false)) ∧
  (∀ {M P T V : Type}
      (ops : MemoryAccessOps Option M P T V) (a : M) (i : I64) (order : MemoryOrder),
    (do
      let ref ← ops.memoryrefAt a i
      ops.memoryrefUnset ref order true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let _ ← unsetindexAtomicMemoryInt ops true a order i
        let ref ← ops.memoryrefAt a i
        ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false) ∧
  (∀ {M P T V I : Type}
      (ops : MemoryAccessOps Option M P T V) (toIndex : I → Option I64)
      (a : M) (i : I) (index : I64) (order : MemoryOrder),
    toIndex i = pure index →
      (do
        let ref ← ops.memoryrefAt a index
        ops.memoryrefUnset ref order true
        ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
          (do
            let _ ← unsetindexAtomicMemoryInteger ops true toIndex a order i
            let ref ← ops.memoryrefAt a index
            ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false)

/-- Copying a Memory allocates a distinct storage object with the original element count. -/
def MemoryCopyPreservesExtent : Prop :=
  ∀ {M P T Ptr Token : Type}
    (copy : MemoryCopyOps Option M P I64 I64 I64 I64 Ptr Token)
    (length : M → Option I64) (construct : I64 → Option M)
    (sameStorage : M → M → Bool) (a result : M) (n : I64),
    length a = some n →
    (∀ allocated, construct n = some allocated →
      length allocated = some n ∧ sameStorage a allocated = false) →
    copyMemory (T := T) copy length construct a = some result →
      length result = some n ∧ sameStorage a result = false

/-- Every `similar` overload preserves the requested element count. -/
def SimilarMemoryPreservesExtent : Prop :=
  (∀ {M : Type} (length : M → Option I64) (construct : I64 → Option M)
      (a result : M) (n : I64),
    length a = some n → construct n = some result → length result = some n →
      similarMemory length construct a = some result) ∧
  (∀ {M R : Type} (length : M → Option I64) (construct : Type → I64 → Option R)
      (a : M) (result : R) (elementType : Type) (n : I64),
    length a = some n → construct elementType n = some result →
      similarMemoryElementType (T := elementType) length construct a elementType = some result) ∧
  (∀ {M : Type} (construct : I64 → Option M) (a result : M) (n : I64),
    construct n = some result → similarMemoryLength construct a n = some result) ∧
  (∀ {M R D : Type} (construct : Type → I64 → Option R)
      (firstDim : D → Option I64) (a : M) (elementType : Type) (dims : D)
      (result : R) (n : I64),
    firstDim dims = some n → construct elementType n = some result →
      similarMemoryElementDims (T := elementType) construct firstDim a elementType dims = some result) ∧
  (∀ {M D : Type} (construct : I64 → Option M) (firstDim : D → Option I64)
      (a result : M) (dims : D) (n : I64),
    firstDim dims = some n → construct n = some result →
      similarMemoryDims construct firstDim a dims = some result)

/-- Byte-memory fill converts the integer to the element type before filling every byte. -/
def ByteMemoryFillUsesConvertedValue : Prop :=
  (∀ {M P X U USize Token : Type}
    (elementType : M → Type) (isInteger : X → Prop)
    (castElement : Type → X → Option U) (convert : Type → X → Option U) (preserveBegin : M → Token)
    (preserveEnd : Token → Option Unit) (unsafeConvert : M → Option P)
    (memset : P → U → USize → Option Unit) (lengthModUInt : M → Option USize)
    (a : M) (x : X) (integerProof : isInteger x) (value : U) (size : USize) (ptr : P) (token : Token),
    castElement (elementType a) x = some value → preserveBegin a = token →
      unsafeConvert a = some ptr → lengthModUInt a = some size →
        memset ptr value size = some () → preserveEnd token = some () →
          fillByteMemory elementType isInteger castElement convert preserveBegin preserveEnd
            unsafeConvert memset lengthModUInt a x integerProof = some a) ∧
  (∀ {M P X U USize Token : Type} (elementType : M → Type) (isInteger : X → Prop)
      (castElement : Type → X → Option U) (convert : Type → X → Option U)
      (preserveBegin : M → Token) (preserveEnd : Token → Option Unit)
      (unsafeConvert : M → Option P) (memset : P → U → USize → Option Unit)
      (lengthModUInt : M → Option USize) (a : M) (x : X) (integerProof : isInteger x)
      (value : U) (size : USize) (ptr : P) (token : Token),
    castElement (elementType a) x = none → convert (elementType a) x = some value →
      preserveBegin a = token → unsafeConvert a = some ptr → lengthModUInt a = some size →
        memset ptr value size = some () → preserveEnd token = some () →
          fillByteMemory elementType isInteger castElement convert preserveBegin preserveEnd
            unsafeConvert memset lengthModUInt a x integerProof = some a)

/-- Converting to a Memory type reuses an existing target value; promotion combines element types. -/
def MemoryConversionAndPromotion : Prop :=
  (∀ {M A : Type} (asTarget : A → Option M) (construct : A → Option M) (a : A) (memory : M),
    asTarget a = some memory → convertMemory asTarget construct a = some memory) ∧
  (∀ {M A : Type} (asTarget : A → Option M) (construct : A → Option M) (a : A) (memory : M),
    asTarget a = none → construct a = some memory → convertMemory asTarget construct a = some memory) ∧
  (∀ {R : Type} (promoteType : Type → Type → Type)
      (elSame : Type → Type → Type → R) (T S : Type),
    promoteRuleMemory promoteType elSame T S = elSame (promoteType T S) T S)

/-- Constructing `Memory{T}` from an array performs the checked axis-compatible copy. -/
def MemoryArrayConstructorCopies : Prop :=
  ∀ {M A D : Type} (size : A → Option D) (constructUndef : D → Option M)
    (copytoAxcheck : M → A → Option M) (x : A) (n : D) (destination : M),
    size x = some n → constructUndef n = some destination →
      memoryFromArray size constructUndef copytoAxcheck x = copytoAxcheck destination x

/-- Memory range indexing validates indices, creates the result shape, and copies a nonempty slice. -/
def MemoryRangeGetindexChecksBounds : Prop :=
  (∀ {M I : Type} (construct : I64 → Option M)
      (copyImpl : M → I64 → M → I64 → I64 → Option M)
      (checkbounds : M → I → Option Unit) (rangeLength rangeAxes rangeFirst : I → Option I64)
      (firstindex : M → Option I64) (a : M) (indices : I),
    checkbounds a indices = none →
      getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
        construct a indices true = none) ∧
  (∀ {M I : Type} (construct : I64 → Option M)
      (copyImpl : M → I64 → M → I64 → I64 → Option M)
      (checkbounds : M → I → Option Unit) (rangeLength rangeAxes rangeFirst : I → Option I64)
      (firstindex : M → Option I64) (a result : M) (indices : I)
      (start span dims first : I64),
    checkbounds a indices = some () → rangeLength indices = some span →
      0 < span.val → rangeAxes indices = some dims → construct dims = some result →
        firstindex result = some first → rangeFirst indices = some start →
          copyImpl result first a start span = some result →
            getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
              construct a indices true = some result) ∧
  (∀ {M I J : Type} (construct : I64 → Option M)
      (copyImpl : M → I64 → M → I64 → I64 → Option M)
      (checkbounds : M → J → Option Unit) (rangeLength rangeAxes rangeFirst : J → Option I64)
      (firstindex : M → Option I64) (toIndex : I → Option J) (a result : M)
      (range : I) (indices : J),
    toIndex range = some indices →
      getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
        construct a indices true = some result →
          getindexMemoryBoolRange construct copyImpl checkbounds rangeLength rangeAxes
            rangeFirst firstindex toIndex a range true = some result)

/-- Scalar Memory assignment returns its destination after writing the converted value. -/
def MemoryScalarSetindexReturnsTarget : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
    (a : M) (value : V) (i : I64) (stored : T) (base ref : GenericMemoryRef M P),
    ops.castElement value = some stored → ops.checkbounds a i = some () →
      ops.memoryref a = some base → ops.memoryrefNew base i false = some ref →
        ops.memoryrefSet ref stored .notAtomic false = some () →
          setindexMemory ops ops.convertElement pure true a value i = some a) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (throwBounds : M → I64 → I64 → List I64 → Option Unit)
      (a : M) (value : V) (i1 i2 : I64) (indices : List I64),
    i2 = 1 → indices.all (fun i => i == 1) = true →
      setindexMemoryCartesian ops ops.convertElement pure throwBounds true a value i1 i2 indices =
        setindexMemory ops ops.convertElement pure true a value i1)

/-- Range and colon assignment reject a source whose shape does not match the target span. -/
def MemoryBulkSetindexChecksShape : Prop :=
  (∀ {M P T I : Type} (copy : MemoryCopyOps Option M P I64 I64 I64 I64 P Unit)
      (checkbounds : M → I → Option Unit) (rangeLength rangeFirst : I → Option I64)
      (shapeCheck : M → I64 → Option Unit) (a x : M) (indices : I) (span : I64),
    rangeLength indices = some span → shapeCheck x span = none →
      setindexMemoryRange (T := T) copy checkbounds rangeLength rangeFirst shapeCheck true a x indices = none) ∧
  (∀ {M P T : Type} (copy : MemoryCopyOps Option M P I64 I64 I64 I64 P Unit)
      (length : M → Option I64) (shapeCheck : M → I64 → Option Unit) (a x : M)
      (span : I64), length a = some span → shapeCheck x span = none →
      setindexMemoryColon (T := T) copy length shapeCheck true a x = none)

/-- Byte-memory comparison is lexicographic, with length deciding equal prefixes. -/
def ByteMemoryComparisonOrdersPrefix : Prop :=
  ∀ {M Ptr Tok : Type} (length : M → Option I64) (gcPreserveBegin : M → Tok)
    (gcPreserveEnd : Tok → Option Unit) (unsafeConvert : M → Option Ptr)
    (memcmp : Ptr → Ptr → I64 → Option I64) (cmpLength : I64 → I64 → Option I64)
    (a b : M) (c : I64) (pa pb : Ptr) (la lb : I64) (ta tb : Tok),
    length a = some la → length b = some lb → gcPreserveBegin a = ta → gcPreserveBegin b = tb →
      unsafeConvert a = some pa → unsafeConvert b = some pb →
        gcPreserveEnd ta = some () → gcPreserveEnd tb = some () →
          memcmp pa pb (min la lb) = some c →
            (c < 0 → cmpByteMemory length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp
              cmpLength a b = some (-1)) ∧
            (0 < c → cmpByteMemory length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp
              cmpLength a b = some 1) ∧
            (c = 0 → cmpByteMemory length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp
              cmpLength a b = cmpLength la lb)

/-- Bit-integer Memory equality requires equal lengths and equal stored bytes. -/
def BitIntegerMemoryEqualityRequiresEqualLengths : Prop :=
  ∀ {M Ptr Tok : Type} (length : M → Option I64) (gcPreserveBegin : M → Tok)
    (gcPreserveEnd : Tok → Option Unit) (unsafeConvert : M → Option Ptr)
    (sizeofElement : Type → I64) (elementType : M → Type)
    (memcmp : Ptr → Ptr → I64 → Option I64) (a b : M) (la lb : I64),
    length a = some la → length b = some lb →
    (la ≠ lb →
      equalBitIntegerMemory length gcPreserveBegin gcPreserveEnd unsafeConvert sizeofElement
        elementType memcmp a b = some false)
    ∧ (∀ (c : I64) (pa pb : Ptr) (ta tb : Tok),
        la = lb → gcPreserveBegin a = ta → gcPreserveBegin b = tb →
          unsafeConvert a = some pa → unsafeConvert b = some pb →
          gcPreserveEnd ta = some () → gcPreserveEnd tb = some () →
          memcmp pa pb (sizeofElement (elementType a) * la) = some c →
            equalBitIntegerMemory length gcPreserveBegin gcPreserveEnd unsafeConvert sizeofElement
              elementType memcmp a b = some (c == 0))

/-- Sorted search routing agrees with general search; unsorted inputs use the general path. -/
def MemoryFindallUsesSortedSearch : Prop :=
  (∀ {M X R : Type} (issortedMemory : M → SortDirection → Option Bool)
    (issortedNeedle : X → SortDirection → Option Bool)
    (sortedFindin findin : M → X → Option R) (pred : Fix2In X) (x : M) (result : R),
    issortedMemory x .forward = some true → issortedNeedle pred.x .forward = some true →
      sortedFindin x pred.x = some result →
        findallMemory issortedMemory issortedNeedle
          sortedFindin findin pred x = some result) ∧
  (∀ {M X R : Type} (issortedMemory : M → SortDirection → Option Bool)
      (issortedNeedle : X → SortDirection → Option Bool)
      (sortedFindin findin : M → X → Option R) (pred : Fix2In X) (x : M) (result : R),
    issortedMemory x .forward = some false → findin x pred.x = some result →
      findallMemory issortedMemory issortedNeedle
        sortedFindin findin pred x = some result) ∧
  (∀ {M X R : Type} (issortedMemory : M → SortDirection → Option Bool)
      (issortedNeedle : X → SortDirection → Option Bool)
      (sortedFindin findin : M → X → Option R) (pred : Fix2In X) (x : M) (result : R),
    issortedMemory x .forward = some true → issortedNeedle pred.x .forward = some false →
      findin x pred.x = some result →
        findallMemory issortedMemory issortedNeedle
          sortedFindin findin pred x = some result)

/-- `indcopy` uses each dimension's subregion, with the trailing dimension scaled by its suffix. -/
def MemoryIndcopyKeepsDimensionRegions : Prop :=
  ∀ {M X Y Vector : Type} (sizeAt : List I64 → I64 → Option I64)
    (sizeLength : List I64 → I64) (rangeFromTo : I64 → I64 → Option (List I64))
    (oneRange : I64 → Option (List I64)) (addInt mulInt : I64 → I64 → Option I64)
    (length : M → Option I64) (getindex : M → I64 → Option X)
    (findin : X → List I64 → Option Y) (subindex : X → Y → Option Y)
    (toVector : List Y → Option Vector) (vectorLength : Vector → Nat)
    (sz : List I64) (indices : M) (dst src : Vector) (n : I64),
    length indices = some n →
    (∃ positions, rangeFromTo 1 n = some positions ∧ positions.length = n.val.toNat) →
    (∀ ys vector, toVector ys = some vector → vectorLength vector = ys.length) →
    indcopy sizeAt sizeLength rangeFromTo oneRange addInt mulInt length getindex
      findin subindex toVector sz indices = some (dst, src) →
        vectorLength dst = n.val.toNat ∧ vectorLength src = n.val.toNat

/-- Atomic get/set/modify/swap/replace operations pass their memory order to the runtime operation. -/
def AtomicMemoryOperationsPreserveOrdering : Prop :=
  (∀ {M P V : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (memoryrefGet : GenericMemoryRef M P → MemoryOrder → Bool → Option V)
      (mem : M) (order : MemoryOrder) (i : I64) (ref : GenericMemoryRef M P) (value : V),
    memoryrefAt mem i = some ref → memoryrefGet ref order true = some value →
      getindexAtomic memoryrefAt memoryrefGet true mem order i = some value) ∧
  (∀ {M P T V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefSet : GenericMemoryRef M P → T → MemoryOrder → Bool → Option R)
      (mem : M) (order : MemoryOrder) (input : V) (i : I64) (ref : GenericMemoryRef M P)
      (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefSet ref value order true = some result →
        setindexAtomic memoryrefAt castElement convert memoryrefSet true mem order input i = some result) ∧
  (∀ {M P Op V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (memoryrefModify : GenericMemoryRef M P → Op → V → MemoryOrder → Bool → Option R)
      (mem : M) (order : MemoryOrder) (op : Op) (value : V) (i : I64)
      (ref : GenericMemoryRef M P) (result : R),
    memoryrefAt mem i = some ref → memoryrefModify ref op value order true = some result →
      modifyindexAtomic memoryrefAt memoryrefModify true mem order op value i = some result) ∧
  (∀ {M P T V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefSetOnce : GenericMemoryRef M P → T → MemoryOrder → MemoryOrder → Bool → Option R)
      (mem : M) (successOrder failOrder : MemoryOrder) (input : V) (i : I64)
      (ref : GenericMemoryRef M P) (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefSetOnce ref value successOrder failOrder true = some result →
        setindexonceAtomic memoryrefAt castElement convert memoryrefSetOnce true mem
          successOrder failOrder input i = some result) ∧
  (∀ {M P T V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefSwap : GenericMemoryRef M P → T → MemoryOrder → Bool → Option R)
      (mem : M) (order : MemoryOrder) (input : V) (i : I64) (ref : GenericMemoryRef M P)
      (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefSwap ref value order true = some result →
        swapindexAtomic memoryrefAt castElement convert memoryrefSwap true mem order input i = some result) ∧
  (∀ {M P T E V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefReplace : GenericMemoryRef M P → E → T → MemoryOrder → MemoryOrder → Bool → Option R)
      (mem : M) (successOrder failOrder : MemoryOrder) (expected : E) (input : V) (i : I64)
      (ref : GenericMemoryRef M P) (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefReplace ref expected value successOrder failOrder true = some result →
        replaceindexAtomic memoryrefAt castElement convert memoryrefReplace true mem
          successOrder failOrder expected input i = some result)

/-! Nothing to promise:
- `parent@66`: pure projection of the `mem` field of a reference.
- `pointer@89`: direct `unsafe_convert` forwarding; pointer validity is the runtime callee's contract.
- `elsize@185`: direct `aligned_sizeof` forwarding.
- `sizeof@186`: direct `Core.sizeof` forwarding.
- `getindex@322`: direct forwarding to `copy(A)`; copy semantics are specified separately.
- `copyto!@265`: sets default offsets and delegates to the next `copyto!` method.
- `copyto!@266`: direct forwarding to `_copyto_impl!` in another Base file.
-/

/-! ## Proofs -/

/-- Bind of a `some` in the `Bind.bind` form produced by `do` notation. -/
theorem bind_some_shift {α β : Type} (f : α → Option β) (a : α) :
    (some a >>= f) = f a := rfl

/-- Bind of a `pure` in the `Bind.bind` form produced by `do` notation. -/
theorem bind_pure_shift {α β : Type} (f : α → Option β) (a : α) :
    ((pure a : Option α) >>= f) = f a := rfl

/-- Characterization of a successful `Option` bind. -/
theorem option_bind_eq_some {α β : Type} (x : Option α) (f : α → Option β) (b : β) :
    (x >>= f = some b) ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

theorem i64_beq_of_eq {a b : I64} (h : a = b) : (a == b) = true := by simp [h]

theorem i64_zero_val : (0 : I64).val = 0 := rfl

theorem memoryLinearIndexing_proven : MemoryLinearIndexing := fun _ => rfl

theorem memoryIndexIsOneBased_proven : MemoryIndexIsOneBased := by
  intro _M _P _memoryrefoffset _length _ref h1 h2
  exact ⟨h1, h2⟩

theorem memoryIsassignedBounds_proven : MemoryIsassignedBounds := by
  constructor
  · intro M P T V ops a i hcb
    simp [isassignedMemory, hcb]
  · intro M P T V ops ref assigned h
    simp [isassignedRef, h]

theorem genericMemoryCheckedAccessesInBounds_proven : GenericMemoryCheckedAccessesInBounds := by
  constructor
  · intro M P T D S N I Ptr Token copy dest src n hzero hcheck
    simp [unsafeCopytoRefs, hzero, hcheck]
  · intro M P T I copy checkbounds rangeLength rangeFirst shapeCheck a x indices hcb
    simp [setindexMemoryRange, hcb]

theorem memoryUnsetReturnsTarget_proven : MemoryUnsetReturnsTarget := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M P T V ops ref h
    simp [unsetindexRef, h]
  · intro M P T V ops a i ref h1 h2
    simp [unsetindexMemoryInt, unsetindexRef, h1, h2]
  · intro M P T V I ops toIndex unsetArray a i index ref h1 h2 h3
    simp [unsetindexUnionInteger, unsetindexMemoryInt, unsetindexRef, h1, h2, h3]
  · intro M P T V ops ref h
    cases hu : ops.memoryrefUnset ref MemoryOrder.notAtomic true with
    | none => rw [hu] at h; simp at h
    | some w =>
      rw [hu] at h
      simp only [unsetindexRef] at ⊢
      rw [hu] at ⊢
      simp only [bind_some_shift, bind_pure_shift] at h ⊢
      rw [h]
      rfl
  · intro M P T V ops a i h
    simp only [unsetindexMemoryInt]
    cases ha : ops.memoryrefAt a i with
    | none => rw [ha] at h; simp at h
    | some w =>
      rw [ha] at h
      simp only [bind_some_shift] at h ⊢
      simp only [unsetindexRef] at ⊢
      cases hu : ops.memoryrefUnset w MemoryOrder.notAtomic true with
      | none => rw [hu] at h; simp at h
      | some u =>
        rw [hu] at h
        simp only [bind_some_shift] at h
        simp only [bind_some_shift, bind_pure_shift]
        rw [h]
  · intro A I P T V ops toIndex unsetArray isassignedArray array i index h1 h2
    have h1' : toIndex i = some index := h1
    simp only [unsetindexUnionInteger]
    rw [h1']
    simp only [bind_some_shift]
    cases hu : unsetArray array index with
    | none => rw [hu] at h2; simp at h2
    | some u =>
      rw [hu] at h2
      simp only [bind_some_shift] at h2
      simp only [bind_some_shift, bind_pure_shift]
      rw [h2]

theorem atomicMemoryUnsetReturnsReference_proven : AtomicMemoryUnsetReturnsReference := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M P T V ops ref order h
    simp [unsetindexAtomicRef, h]
  · intro M P T V ops a i ref order h1 h2
    simp [unsetindexAtomicMemoryInt, unsetindexAtomicRef, h1, h2]
  · intro M P T V I ops toIndex a i index ref order h1 h2 h3
    simp [unsetindexAtomicMemoryInteger, unsetindexAtomicMemoryInt, unsetindexAtomicRef, h1, h2, h3]
  · intro M P T V ops ref order h
    cases hu : ops.memoryrefUnset ref order true with
    | none => rw [hu] at h; simp at h
    | some w =>
      rw [hu] at h
      simp only [unsetindexAtomicRef] at ⊢
      rw [hu] at ⊢
      simp only [bind_some_shift, bind_pure_shift] at h ⊢
      rw [h]
      rfl
  · intro M P T V ops a i order h
    simp only [unsetindexAtomicMemoryInt]
    cases ha : ops.memoryrefAt a i with
    | none => rw [ha] at h; simp at h
    | some w =>
      rw [ha] at h
      simp only [bind_some_shift] at h ⊢
      simp only [unsetindexAtomicRef] at ⊢
      cases hu : ops.memoryrefUnset w order true with
      | none => rw [hu] at h; simp at h
      | some u =>
        rw [hu] at h
        simp only [bind_some_shift] at h
        simp only [bind_some_shift, bind_pure_shift]
        rw [h]
  · intro M P T V I ops toIndex a i index order h1 h2
    have h1' : toIndex i = some index := h1
    simp only [unsetindexAtomicMemoryInteger, unsetindexAtomicMemoryInt]
    rw [h1']
    simp only [bind_some_shift]
    cases ha : ops.memoryrefAt a index with
    | none => rw [ha] at h2; simp at h2
    | some w =>
      rw [ha] at h2
      simp only [bind_some_shift] at h2 ⊢
      simp only [unsetindexAtomicRef] at ⊢
      cases hu : ops.memoryrefUnset w order true with
      | none => rw [hu] at h2; simp at h2
      | some u =>
        rw [hu] at h2
        simp only [bind_some_shift] at h2
        simp only [bind_some_shift, bind_pure_shift]
        rw [h2]

/-- The typed memory-copy route returns its destination argument whenever it succeeds. -/
theorem unsafeCopytoMemoryTyped_dest {M P T D S N I Ptr Token : Type}
    (copy : MemoryCopyOps Option M P D S N I Ptr Token) (boundsChecking : Bool)
    (dest : M) (doffs : D) (src : M) (soffs : S) (n : N) (x : M)
    (h : unsafeCopytoMemoryTyped (T := T) copy boundsChecking dest doffs src soffs n = some x) :
    x = dest := by
  unfold unsafeCopytoMemoryTyped at h
  split at h
  · simp at h
    exact h.symm
  · simp only [option_bind_eq_some] at h
    obtain ⟨d', -, h⟩ := h
    obtain ⟨s', -, h⟩ := h
    obtain ⟨c', -, h⟩ := h
    simp at h
    exact h.symm

theorem memoryCopyPreservesExtent_proven : MemoryCopyPreservesExtent := by
  intro M P T Ptr Token copy length construct sameStorage a result n hlen hlaw hcopy
  unfold copyMemory at hcopy
  rw [hlen] at hcopy
  simp only [bind_some_shift] at hcopy
  obtain ⟨nm, hnmc, hty⟩ := (option_bind_eq_some _ _ _).mp hcopy
  obtain ⟨hl, hs⟩ := hlaw nm hnmc
  rw [unsafeCopytoMemoryTyped_dest copy false nm 1 a 1 n result hty]
  exact ⟨hl, hs⟩

theorem similarMemoryPreservesExtent_proven : SimilarMemoryPreservesExtent := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M length construct a result n h1 h2 _
    simp [similarMemory, h1, h2]
  · intro M R length construct a result elementType n h1 h2
    simp [similarMemoryElementType, h1, h2]
  · intro M construct a result n h
    simp [similarMemoryLength, h]
  · intro M R D construct firstDim a elementType dims result n h1 h2
    simp [similarMemoryElementDims, h1, h2]
  · intro M D construct firstDim a result dims n h1 h2
    simp [similarMemoryDims, h1, h2]

theorem byteMemoryFillUsesConvertedValue_proven : ByteMemoryFillUsesConvertedValue := by
  constructor
  · intro M P X U USize Token elementType _isInteger castElement convert preserveBegin preserveEnd
      unsafeConvert memset lengthModUInt a x _iprf value size ptr token
      hcast hpb huc hlen hmemset hpe
    simp [fillByteMemory, hcast, hpb, huc, hlen, hmemset, hpe]
  · intro M P X U USize Token elementType _isInteger castElement convert preserveBegin preserveEnd
      unsafeConvert memset lengthModUInt a x _iprf value size ptr token
      hcast hconv hpb huc hlen hmemset hpe
    simp [fillByteMemory, hcast, hconv, hpb, huc, hlen, hmemset, hpe]

theorem memoryConversionAndPromotion_proven : MemoryConversionAndPromotion := by
  refine ⟨?_, ?_, ?_⟩
  · intro M A asTarget construct a memory h
    simp [convertMemory, h]
  · intro M A asTarget construct a memory h
    simp [convertMemory, h]
  · intro R promoteType elSame T S
    rfl

theorem memoryArrayConstructorCopies_proven : MemoryArrayConstructorCopies := by
  intro M A D size constructUndef copytoAxcheck x n destination hsize hcon
  simp [memoryFromArray, hsize, hcon]

theorem memoryRangeGetindexChecksBounds_proven : MemoryRangeGetindexChecksBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro M I construct copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex a indices hcb
    simp [getindexMemoryRange, hcb]
  · intro M I construct copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex a result
      indices start span dims first hcb hspan hpos haxes hcon hfi hfirst hcopy
    have hspanpos : (0 : I64) < span := hpos
    simp [getindexMemoryRange, similarMemoryDims, copytoMemoryOffsets, hcb, hspan, haxes, hcon,
      hfi, hfirst, hcopy, hspanpos]
  · intro M I J construct copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex toIndex
      a result range indices hto
    simp [getindexMemoryBoolRange, hto]

theorem memoryScalarSetindexReturnsTarget_proven : MemoryScalarSetindexReturnsTarget := by
  refine ⟨?_, ?_⟩
  · intro M P T V ops a value i stored base ref hcast hcb href hnew hset
    simp [setindexMemory, setindexMemoryRaw, hcast, hcb, href, hnew, hset]
  · intro M P T V ops throwBounds a value i1 i2 indices hi2 hall
    have hguard : (i2 == 1 && indices.all (fun i => i == 1)) = true := by
      rw [i64_beq_of_eq hi2, hall, Bool.and_self]
    simp only [setindexMemoryCartesian]
    rw [hguard]
    simp

theorem memoryBulkSetindexChecksShape_proven : MemoryBulkSetindexChecksShape := by
  refine ⟨?_, ?_⟩
  · intro M P T I copy checkbounds rangeLength rangeFirst shapeCheck a x indices span hrl hshape
    simp only [setindexMemoryRange]
    cases hc : checkbounds a indices with
    | none => simp
    | some _ => simp [hrl, hshape]
  · intro M P T copy length shapeCheck a x span hlen hshape
    simp [setindexMemoryColon, hlen, hshape]

theorem byteMemoryComparisonOrdersPrefix_proven : ByteMemoryComparisonOrdersPrefix := by
  intro M Ptr Tok length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp cmpLength a b c pa pb
    la lb ta tb hla hlb hta htb hpa hpb hpea hpeb hmem
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    simp [cmpByteMemory, hla, hlb, hta, htb, hpa, hpb, hpea, hpeb, hmem, hc]
  · intro hc
    have hcpos : 0 < c.val := hc
    have hneg : ¬(c < 0) := by
      show ¬(c.val < (0 : I64).val)
      rw [i64_zero_val]
      omega
    simp [cmpByteMemory, hla, hlb, hta, htb, hpa, hpb, hpea, hpeb, hmem, hc, hneg]
  · intro hc
    have hcval : c.val = 0 := by rw [hc, i64_zero_val]
    have hneg1 : ¬(c < 0) := by
      show ¬(c.val < (0 : I64).val)
      rw [i64_zero_val]
      omega
    have hneg2 : ¬(0 < c) := by
      show ¬((0 : I64).val < c.val)
      rw [i64_zero_val]
      omega
    simp [cmpByteMemory, hla, hlb, hta, htb, hpa, hpb, hpea, hpeb, hmem, hneg1, hneg2]

theorem bitIntegerMemoryEqualityRequiresEqualLengths_proven :
    BitIntegerMemoryEqualityRequiresEqualLengths := by
  intro M Ptr Tok length gcPreserveBegin gcPreserveEnd unsafeConvert sizeofElement elementType
    memcmp a b la lb hla hlb
  refine ⟨?_, ?_⟩
  · intro hne
    have hneval : ¬(la.val = lb.val) := fun h => hne (Subtype.ext h)
    simp [equalBitIntegerMemory, hla, hlb, hneval]
  · intro c pa pb ta tb hle hta htb hpa hpb hpea hpeb hmem
    rw [hle] at hmem
    simp [equalBitIntegerMemory, hla, hlb, hle, hta, htb, hpa, hpb, hpea, hpeb, hmem,
      i64_zero_val]

theorem memoryFindallUsesSortedSearch_proven : MemoryFindallUsesSortedSearch := by
  refine ⟨?_, ?_, ?_⟩
  · intro M X R issortedMemory issortedNeedle sortedFindin findin pred x result h1 h2 h3
    simp [findallMemory, h1, h2, h3]
  · intro M X R issortedMemory issortedNeedle sortedFindin findin pred x result h1 h2
    simp [findallMemory, h1, h2]
  · intro M X R issortedMemory issortedNeedle sortedFindin findin pred x result h1 h2 h3
    simp [findallMemory, h1, h2, h3]

theorem mapM_loop_nil {α β : Type} (f : α → Option β) (acc : List β) :
    List.mapM.loop f [] acc = pure acc.reverse := rfl

theorem mapM_loop_cons {α β : Type} (f : α → Option β) (x : α) (l : List α) (acc : List β) :
    List.mapM.loop f (x :: l) acc = (f x) >>= fun b => List.mapM.loop f l (b :: acc) := rfl

theorem mapM_cons {α β : Type} (f : α → Option β) (x : α) (l : List α) :
    List.mapM f (x :: l) = (f x) >>= fun b => List.mapM.loop f l [b] := rfl

theorem mapM_len_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ys.length = l.length := by
  have loop_len : ∀ (l : List α) (acc ys : List β), List.mapM.loop f l acc = some ys →
      ys.length = l.length + acc.length := by
    intro l
    induction l with
    | nil =>
      intro acc ys h
      rw [mapM_loop_nil] at h
      simp at h
      rw [← h]
      simp
    | cons x l ih =>
      intro acc ys h
      rw [mapM_loop_cons] at h
      obtain ⟨b, -, h⟩ := (option_bind_eq_some _ _ _).mp h
      have hprev := ih (b :: acc) ys h
      simp only [List.length_cons] at hprev ⊢
      omega
  intro l ys h
  cases l with
  | nil => simpa using h
  | cons x l =>
    rw [mapM_cons] at h
    obtain ⟨b, -, h⟩ := (option_bind_eq_some _ _ _).mp h
    have hres := loop_len l [b] ys h
    simp only [List.length_cons, List.length_nil] at hres ⊢
    omega

theorem memoryIndcopyKeepsDimensionRegions_proven : MemoryIndcopyKeepsDimensionRegions := by
  intro M X Y Vector sizeAt sizeLength rangeFromTo oneRange addInt mulInt length getindex findin
    subindex toVector vectorLength sz indices dst src n hlen hpos htov hrun
  obtain ⟨positions, hposr, hposlen⟩ := hpos
  simp only [indcopy] at hrun
  rw [hlen] at hrun
  simp only [bind_some_shift] at hrun
  obtain ⟨s₀, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨lo, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨ls, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨s₁, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  rw [hposr] at hrun
  simp only [bind_some_shift] at hrun
  obtain ⟨dstL, hdstL, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨srcL, hsrcL, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨dv, hdv, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨sv, hsv, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  simp at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  exact ⟨by rw [htov dstL dv hdv, mapM_len_some _ positions dstL hdstL, hposlen],
         by rw [htov srcL sv hsv, mapM_len_some _ positions srcL hsrcL, hposlen]⟩

theorem atomicMemoryOperationsPreserveOrdering_proven : AtomicMemoryOperationsPreserveOrdering := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M P V memoryrefAt memoryrefGet mem order i ref value
    intro href hget
    simp [getindexAtomic, href, hget]
  · intro M P T V R memoryrefAt castElement convert memoryrefSet mem order input i ref value result
    intro href hcast hset
    simp [setindexAtomic, href, hcast, hset]
  · intro M P Op V R memoryrefAt memoryrefModify mem order op value i ref result
    intro href hmod
    simp [modifyindexAtomic, href, hmod]
  · intro M P T V R memoryrefAt castElement convert memoryrefSetOnce mem successOrder failOrder
      input i ref value result
    intro href hcast hset
    simp [setindexonceAtomic, href, hcast, hset]
  · intro M P T V R memoryrefAt castElement convert memoryrefSwap mem order input i ref value result
    intro href hcast hset
    simp [swapindexAtomic, href, hcast, hset]
  · intro M P T E V R memoryrefAt castElement convert memoryrefReplace mem successOrder failOrder
      expected input i ref value result
    intro href hcast hset
    simp [replaceindexAtomic, href, hcast, hset]
namespace Round2

open JuliaLean JuliaLean.base.genericmemory JuliaLean.Proofs.base.genericmemory

namespace ByteComparisonBinding

/-- Pointer metadata and typed slot objects are two observations of the same UInt8 memory.
The mapping stores object fields, not operations or an expected comparison result. -/
abbrev Pointers := Nat → JuliaLean.base.pointer.PointerMemoryObject (JInt .u8)

/-- Concrete dispatch for the splatted native-Int multiplication used by tuple `prod`.
Only the singleton branch is reachable from `size(::GenericMemory)`, but all arities use
installed multiplication definitions rather than a callback returning a supplied length. -/
def multiplyDimensions (xs : List (JInt .i64)) : JInt .i64 :=
  match xs with
  | [] => JuliaLean.base.tuple.prodEmpty
  | [x] => JuliaLean.base.operators.unaryMulNumber x
  | [x, y] => JuliaLean.base.int.mul x y
  | x :: y :: z :: rest =>
    (JuliaLean.base.operators.naryOperator
      (τ := Unit) (σ := Unit) (Acc := fun _ => JInt .i64) (Elem := fun _ => JInt .i64)
      JuliaLean.base.int.mul
      (fun a b => ⟨(), JuliaLean.base.int.mul a b⟩)
      (fun a b => ⟨(), JuliaLean.base.int.mul a.2 b.2⟩)
      x y z (rest.map fun v => ⟨(), v⟩)).2

/-- Read `size(::GenericMemory)` through the installed heap model, then execute the
source-mirrored `length(::AbstractArray)` and tuple-product methods. The pure size callback
carries the result of that actual modeled read, not an assumed law. Failure remains `none`. -/
def lengthModel (objects : JuliaLean.base.essentials.Heap)
    (mem : JuliaLean.base.essentials.Mem) : Option (JInt .i64) := do
  let outcome ← (JuliaLean.base.essentials.sizeGenericMemory mem).run objects
  match outcome with
  | .ok (dims, _) => some (JuliaLean.base.essentials.lengthAbstract
      (fun _ => dims) (JuliaLean.base.tuple.prodIntTuple multiplyDimensions) mem)
  | .error _ => none

/-- Observable extent from the runtime object's stored slots; no comparison operation occurs. -/
def extent (objects : JuliaLean.base.essentials.Heap)
    (mem : JuliaLean.base.essentials.Mem) : Nat :=
  match objects[mem.handle]? with
  | some obj => obj.slots.length
  | none => 0

/-- Bytes of a memory object, read from the shared installed byte heap. Aliases share these bytes. -/
def contents (bytes : JuliaLean.base.pointer.ByteHeap)
    (objects : JuliaLean.base.essentials.Heap) (pointers : Pointers)
    (mem : JuliaLean.base.essentials.Mem) : List (JInt .u8) :=
  bytes.readBytes (pointers mem.handle).ptr.address.val.toNat (extent objects mem)

/-- A constructible live UInt8 memory object: one byte per element, non-atomic, in the shared
heap; its extent and address range do not wrap. Zero length and aliases are permitted. -/
def ValidMemory (bytes : JuliaLean.base.pointer.ByteHeap)
    (objects : JuliaLean.base.essentials.Heap) (pointers : Pointers)
    (mem : JuliaLean.base.essentials.Mem) : Prop :=
  ∃ obj, objects[mem.handle]? = some obj ∧
    obj.atomic = false ∧ obj.elsize = 1 ∧ obj.isunion = false ∧
    (pointers mem.handle).arrayElement = 0 ∧
    (pointers mem.handle).layoutBytes.val = 1 ∧
    obj.slots.length < 2 ^ 62 ∧
    (pointers mem.handle).ptr.address.val.toNat + obj.slots.length ≤ 2 ^ 64 ∧
    bytes.validRange (pointers mem.handle).ptr.address.val.toNat obj.slots.length ∧
    obj.slots = (contents bytes objects pointers mem).map
      (fun v => some (JuliaLean.BootCov.JVal.int v.val))

/-- Independent lexicographic order: a strict prefix, or the first differing byte after an
identical prefix, determines which byte sequence comes first. -/
def LexLess (xs ys : List (JInt .u8)) : Prop :=
  (∃ tail : List (JInt .u8), tail ≠ [] ∧ ys = xs ++ tail) ∨
  (∃ (sharedPrefix : List (JInt .u8)) (x y : JInt .u8) (xt yt : List (JInt .u8)),
    xs = sharedPrefix ++ x :: xt ∧ ys = sharedPrefix ++ y :: yt ∧ x.val < y.val)

/-- The ordinary native-Int comparison callee, bound to its source-mirrored definitions. -/
def compareLengths (x y : JInt .i64) : Option (JInt .i64) :=
  some (JInt.wrap .i64 (JuliaLean.base.operators.cmpInteger
    (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
    (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt) x y))

end ByteComparisonBinding

/-- Comparing any two valid UInt8 memories succeeds with -1, 0, or 1 exactly according to
lexicographic byte order, including empty memories, proper prefixes and overlapping storage.
Julia source: base/genericmemory.jl:367-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-526; base/genericmemory.jl:366-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ByteMemoryComparisonCorrect : Prop :=
  ∀ (bytes : JuliaLean.base.pointer.ByteHeap)
    (objects : JuliaLean.base.essentials.Heap)
    (pointers : ByteComparisonBinding.Pointers)
    (a b : JuliaLean.base.essentials.Mem),
    ByteComparisonBinding.ValidMemory bytes objects pointers a →
    ByteComparisonBinding.ValidMemory bytes objects pointers b →
    -- The read-only byte/object snapshot stays rooted throughout this observation.
    -- Unit callbacks erase compiler liveness metadata only. The installed
    -- essentials.gcPreserveBegin/End are macro AST builders, not runtime operations.
    let result := JuliaLean.base.genericmemory.cmpByteMemory
      (ByteComparisonBinding.lengthModel objects)
      (fun _ => ()) (fun _ => some ())
      (fun mem => some (JuliaLean.base.pointer.unsafeConvertMemoryCvoid
        (pointers mem.handle)))
      (fun pa pb n =>
        (JuliaLean.base.cmem.memcmp JuliaLean.base.cmem.StandardC.standardCMemoryOps
          (fun n : JInt .i64 => .ok (JuliaLean.base.int.remT .u64 n))
          bytes pa pb n).toOption)
      ByteComparisonBinding.compareLengths a b
    let left := ByteComparisonBinding.contents bytes objects pointers a
    let right := ByteComparisonBinding.contents bytes objects pointers b
    ∃ c : JInt .i64, result = some c ∧
      (c.val = -1 ∨ c.val = 0 ∨ c.val = 1) ∧
      (c.val = -1 ↔ ByteComparisonBinding.LexLess left right) ∧
      (c.val = 0 ↔ left = right) ∧
      (c.val = 1 ↔ ByteComparisonBinding.LexLess right left)

end Round2

namespace Round2

open JuliaLean JuliaLean.base.genericmemory JuliaLean.Proofs.base.genericmemory

namespace BitIntegerEqualityBinding

/-- Native pointer metadata for memories of the one chosen BitInteger type. -/
abbrev Pointers (t : IntTy) := Nat → JuliaLean.base.pointer.PointerMemoryObject (JInt t)

/-- Concrete dispatch for the splatted native-Int multiplication used by tuple `prod`.
Only the singleton branch is reachable from `size(::GenericMemory)`, but all arities use
installed multiplication definitions rather than a callback returning a supplied length. -/
def multiplyDimensions (xs : List (JInt .i64)) : JInt .i64 :=
  match xs with
  | [] => JuliaLean.base.tuple.prodEmpty
  | [x] => JuliaLean.base.operators.unaryMulNumber x
  | [x, y] => JuliaLean.base.int.mul x y
  | x :: y :: z :: rest =>
    (JuliaLean.base.operators.naryOperator
      (τ := Unit) (σ := Unit) (Acc := fun _ => JInt .i64) (Elem := fun _ => JInt .i64)
      JuliaLean.base.int.mul
      (fun a b => ⟨(), JuliaLean.base.int.mul a b⟩)
      (fun a b => ⟨(), JuliaLean.base.int.mul a.2 b.2⟩)
      x y z (rest.map fun v => ⟨(), v⟩)).2

/-- Read `size(::GenericMemory)` through the installed heap model, then execute the
source-mirrored `length(::AbstractArray)` and tuple-product methods. The pure size callback
carries the result of that actual modeled read, not an assumed law. Failure remains `none`. -/
def lengthModel (objects : JuliaLean.base.essentials.Heap)
    (mem : JuliaLean.base.essentials.Mem) : Option (JInt .i64) := do
  let outcome ← (JuliaLean.base.essentials.sizeGenericMemory mem).run objects
  match outcome with
  | .ok (dims, _) => some (JuliaLean.base.essentials.lengthAbstract
      (fun _ => dims) (JuliaLean.base.tuple.prodIntTuple multiplyDimensions) mem)
  | .error _ => none

/-- Observable extent from the runtime object's stored slots; no comparison operation occurs. -/
def extent (objects : JuliaLean.base.essentials.Heap)
    (mem : JuliaLean.base.essentials.Mem) : Nat :=
  match objects[mem.handle]? with
  | some obj => obj.slots.length
  | none => 0

/-- Stored abstract values of an object. No byte comparison is performed here. -/
def values (objects : JuliaLean.base.essentials.Heap)
    (mem : JuliaLean.base.essentials.Mem) : List (Option JuliaLean.BootCov.JVal) :=
  match objects[mem.handle]? with
  | some obj => obj.slots
  | none => []

/-- Byte-level representation of the installed runtime bit pattern, in native endian order.
This is a representation observation, not an equality implementation or an unconstrained codec.
The two endian cases are documented by base/io.jl:838-844; C.fromJInt is the existing
runtime-intrinsic bridge in JuliaLean/src/runtime_intrinsics_c.lean:18. -/
def nativeBytes (t : IntTy) (littleEndian : Bool) (value : JInt t) : List (JInt .u8) :=
  let bits := (JuliaLean.C.fromJInt value).toNat
  let little := (List.range (JuliaLean.base.int.sizeofT t)).map fun i =>
    JInt.wrap .u8 (Int.ofNat (bits / 2 ^ (8 * i)))
  if littleEndian then little else little.reverse

/-- Type/layout and shared-storage validity for a same-type BitInteger memory, with all
slots represented by their actual native bytes. The bounds exclude Int/pointer wraparound;
empty memories, arbitrary integer bit patterns and overlapping memory objects remain allowed. -/
def ValidMemory (t : IntTy) (littleEndian : Bool)
    (bytes : JuliaLean.base.pointer.ByteHeap)
    (objects : JuliaLean.base.essentials.Heap) (pointers : Pointers t)
    (mem : JuliaLean.base.essentials.Mem) : Prop :=
  ∃ obj, objects[mem.handle]? = some obj ∧
    obj.atomic = false ∧ obj.elsize = JuliaLean.base.int.sizeofT t ∧ obj.isunion = false ∧
    (pointers mem.handle).arrayElement = 0 ∧
    (pointers mem.handle).layoutBytes.val = Int.ofNat (JuliaLean.base.int.sizeofT t) ∧
    obj.slots.length < 2 ^ 62 ∧
    obj.slots.length * JuliaLean.base.int.sizeofT t < 2 ^ 63 ∧
    bytes.validRange (pointers mem.handle).ptr.address.val.toNat
      (obj.slots.length * JuliaLean.base.int.sizeofT t) ∧
    (∀ i, i < obj.slots.length → ∃ value : JInt t,
      obj.slots[i]? = some (some (JuliaLean.BootCov.JVal.int value.val)) ∧
      bytes.readBytes
        ((pointers mem.handle).ptr.address.val.toNat + i * JuliaLean.base.int.sizeofT t)
        (JuliaLean.base.int.sizeofT t) = nativeBytes t littleEndian value)

/-- Typed dispatch from the exact queried Lean carrier back to its fixed runtime IntTy tag.
The source caller's `M <: BitIntegerMemory` has one concrete element type `JInt t`, and its
installed `eltypeArray` call below returns that same carrier. This guard consumes the actual
queried type: it does not silently size a different type using captured `t`. The zero branch
is an unreachable adapter sentinel, not a claimed sizeof result for arbitrary Julia types.
The reachable branch executes the installed sizeof wrapper and Core BitInteger size model. -/
noncomputable def elementSize (t : IntTy) (queriedType : Type) : JInt .i64 :=
  @ite (JInt .i64) (queriedType = JInt t) (Classical.propDecidable _)
    (JuliaLean.base.essentials.sizeof
      (fun ty : IntTy => JInt.wrap .i64 (Int.ofNat (JuliaLean.base.int.sizeofT ty))) t)
    (JInt.wrap .i64 0)

end BitIntegerEqualityBinding

/-- Two same-type BitInteger memories compare equal exactly when their lengths and all
corresponding integer values agree, for every signed/unsigned width, including empty and aliased
memories; the comparison always returns a Bool.
Julia source: base/genericmemory.jl:378-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:109-128; base/int.jl:4-20; base/io.jl:838-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitIntegerMemoryEqualityCorrect : Prop :=
  ∀ (t : IntTy) (littleEndian : Bool)
    (bytes : JuliaLean.base.pointer.ByteHeap)
    (objects : JuliaLean.base.essentials.Heap)
    (pointers : BitIntegerEqualityBinding.Pointers t)
    (a b : JuliaLean.base.essentials.Mem),
    BitIntegerEqualityBinding.ValidMemory t littleEndian bytes objects pointers a →
    BitIntegerEqualityBinding.ValidMemory t littleEndian bytes objects pointers b →
    -- These callbacks erase only compiler liveness metadata in a rooted read-only snapshot;
    -- essentials.gcPreserveBegin/End construct macro AST, not runtime heap operations.
    let result := JuliaLean.base.genericmemory.equalBitIntegerMemory
      (BitIntegerEqualityBinding.lengthModel objects)
      (fun _ => ()) (fun _ => some ())
      (fun mem => some (JuliaLean.base.pointer.unsafeConvertMemoryCvoid
        (pointers mem.handle)))
      (BitIntegerEqualityBinding.elementSize t)
      (fun _ => JuliaLean.base.abstractarray.eltypeArray JuliaLean.BootCov.JVal (some (JInt t)))
      (fun pa pb n =>
        (JuliaLean.base.cmem.memcmp JuliaLean.base.cmem.StandardC.standardCMemoryOps
          (fun n : JInt .i64 => .ok (JuliaLean.base.int.remT .u64 n))
          bytes pa pb n).toOption) a b
    ∃ equal : Bool, result = some equal ∧
      (equal = true ↔
        BitIntegerEqualityBinding.values objects a = BitIntegerEqualityBinding.values objects b) ∧
      (equal = false ↔
        BitIntegerEqualityBinding.values objects a ≠ BitIntegerEqualityBinding.values objects b)

end Round2

end JuliaLean.Proofs.base.genericmemory

namespace JuliaLean.ChatGPT.Batch4.Group22
open JuliaLean JuliaLean.base.pointer JuliaLean.base.cmem
open JuliaLean.Proofs.base.genericmemory.Round2

theorem gmLex_nil (ys : List (JInt .u8)) :
    ByteComparisonBinding.LexLess [] ys ↔ ys ≠ [] := by
  constructor
  · intro h
    rcases h with ⟨tail, hn, h⟩ | ⟨pre, x, y, xt, yt, hx, hy, hlt⟩
    · simpa only [List.nil_append] using h.symm ▸ hn
    · have hlen := congrArg List.length hx
      simp only [List.length_nil, List.length_append, List.length_cons] at hlen
      omega
  · intro h
    exact Or.inl ⟨ys, h, rfl⟩

theorem gmLex_right_nil (xs : List (JInt .u8)) :
    ¬ ByteComparisonBinding.LexLess xs [] := by
  intro h
  rcases h with ⟨tail, hn, h⟩ | ⟨pre, x, y, xt, yt, hx, hy, hlt⟩
  · have hlen := congrArg List.length h
    simp only [List.length_nil, List.length_append] at hlen
    have : tail.length = 0 := by omega
    exact hn (List.length_eq_zero_iff.mp this)
  · have hlen := congrArg List.length hy
    simp only [List.length_nil, List.length_append, List.length_cons] at hlen
    omega

theorem gmLex_cons (x y : JInt .u8) (xs ys : List (JInt .u8)) :
    ByteComparisonBinding.LexLess (x :: xs) (y :: ys) ↔
      x.val < y.val ∨ (x = y ∧ ByteComparisonBinding.LexLess xs ys) := by
  constructor
  · intro h
    rcases h with ⟨tail, hn, h⟩ | ⟨pre, a, b, ats, bt, hx, hy, hlt⟩
    · simp only [List.cons_append, List.cons.injEq] at h
      exact Or.inr ⟨h.1.symm, Or.inl ⟨tail, hn, h.2⟩⟩
    · cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hx hy
        exact Or.inl (hx.1 ▸ hy.1 ▸ hlt)
      | cons z zs =>
        simp only [List.cons_append, List.cons.injEq] at hx hy
        exact Or.inr ⟨hx.1.trans hy.1.symm,
          Or.inr ⟨zs, a, b, ats, bt, hx.2, hy.2, hlt⟩⟩
  · intro h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inr ⟨[], x, y, xs, ys, rfl, rfl, h⟩
    · rcases h with ⟨tail, hn, h⟩ | ⟨pre, a, b, ats, bt, hx, hy, hlt⟩
      · exact Or.inl ⟨tail, hn, by rw [h]; rfl⟩
      · exact Or.inr ⟨x :: pre, a, b, ats, bt,
          by rw [hx]; rfl, by rw [hy]; rfl, hlt⟩

def gmListCmp : List (JInt .u8) → List (JInt .u8) → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
      if x = y then gmListCmp xs ys else if x.val < y.val then -1 else 1

theorem gmListCmp_spec (xs ys : List (JInt .u8)) :
    (gmListCmp xs ys = -1 ∨ gmListCmp xs ys = 0 ∨ gmListCmp xs ys = 1) ∧
    (gmListCmp xs ys = -1 ↔ ByteComparisonBinding.LexLess xs ys) ∧
    (gmListCmp xs ys = 0 ↔ xs = ys) ∧
    (gmListCmp xs ys = 1 ↔ ByteComparisonBinding.LexLess ys xs) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [gmListCmp, gmLex_nil, gmLex_right_nil]
    | cons y ys => simp [gmListCmp, gmLex_nil, gmLex_right_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp [gmListCmp, gmLex_nil, gmLex_right_nil]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        simpa [gmListCmp, gmLex_cons] using ih ys
      · have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
        by_cases hlt : x.val < y.val
        · have hn : ¬ y.val < x.val := by omega
          simp [gmListCmp, gmLex_cons, hxy, Ne.symm hxy, hlt, hn]
        · have hgt : y.val < x.val := by omega
          simp [gmListCmp, gmLex_cons, hxy, Ne.symm hxy, hlt, hgt]

def gmCompareCounts (n m : Nat) : Int :=
   if n < m then -1 else if m < n then 1 else 0

def gmFinish (c : Int) (n m : Nat) : Int :=
   if c < 0 then -1 else if 0 < c then 1 else gmCompareCounts n m

theorem gmFinish_succ (c : Int) (n m : Nat) :
     gmFinish c (n+1) (m+1) = gmFinish c n m := by
   simp only [gmFinish, gmCompareCounts, Nat.add_lt_add_iff_right]

theorem gmCmem_finish (heap : ByteHeap) (n m left right : Nat) :
    gmFinish (StandardC.cMemcmp heap left right (min n m)).val n m =
      gmListCmp (heap.readBytes left n) (heap.readBytes right m) := by
  induction n generalizing m left right with
  | zero =>
    cases m with
    | zero => simp [gmFinish, gmCompareCounts, StandardC.cMemcmp, ByteHeap.readBytes, gmListCmp, StandardC.i32Lit]
    | succ m => simp [gmFinish, gmCompareCounts, StandardC.cMemcmp, ByteHeap.readBytes, gmListCmp, StandardC.i32Lit]
  | succ n ih =>
    cases m with
    | zero => simp [gmFinish, gmCompareCounts, StandardC.cMemcmp, ByteHeap.readBytes, gmListCmp, StandardC.i32Lit]
    | succ m =>
      have hmin : min (n+1) (m+1) = min n m + 1 := by omega
      rw [hmin]
      simp only [StandardC.cMemcmp, ByteHeap.readBytes, gmListCmp]
      by_cases heq : heap.readByte left = heap.readByte right
      · simp only [heq, ite_true, gmFinish_succ]
        exact ih m (left+1) (right+1)
      · simp only [heq, ite_false]
        by_cases hlt : (heap.readByte left).val < (heap.readByte right).val
        · simp [hlt, gmFinish, StandardC.i32Lit]
        · simp [hlt, gmFinish, StandardC.i32Lit]

theorem gmLengthModel
    (objects : JuliaLean.base.essentials.Heap)
    (mem : JuliaLean.base.essentials.Mem)
    (obj : JuliaLean.base.essentials.MemObj)
    (h : objects[mem.handle]? = some obj) :
    ByteComparisonBinding.lengthModel objects mem =
      some (JInt.wrap .i64 (Int.ofNat obj.slots.length)) := by
  simp [ByteComparisonBinding.lengthModel, JuliaLean.base.essentials.sizeGenericMemory,
    JuliaLean.base.essentials.memLength, JuliaLean.base.essentials.memObj,
    StateT.run, StateT.bind, StateT.pure, StateT.get, get, getThe, MonadStateOf.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, Bind.bind, Pure.pure, h,
    JuliaLean.base.essentials.lengthAbstract, JuliaLean.base.tuple.prodIntTuple,
    ByteComparisonBinding.multiplyDimensions, JuliaLean.base.operators.unaryMulNumber]

theorem gmI64_wrap_val (x : Int) (hx : -(2^63 : Int) ≤ x ∧ x < 2^63) :
    (JInt.wrap .i64 x).val = x :=
  wrapInt_of_inRange .i64 x (by change -(2^63 : Int) ≤ x ∧ x ≤ 2^63 - 1; omega)

theorem gmU64_rem_val (x : JInt .i64) (hx : 0 ≤ x.val) :
    (JuliaLean.base.int.remT .u64 x).val = x.val := by
  have hb := x.property
  change -(2^63 : Int) ≤ x.val ∧ x.val ≤ 2^63-1 at hb
  change wrapInt .u64 (Int.ofNat (BitVec.ofInt 64 x.val).toNat) = x.val
  simp only [BitVec.toNat_ofInt, wrapInt, IntTy.signed, IntTy.bits]
  simp only [Bool.false_eq_true, ite_false]
  change (((x.val % 18446744073709551616).toNat : Nat) : Int) % 18446744073709551616 = x.val
  rw [Int.emod_eq_of_lt hx (by omega), Int.toNat_of_nonneg hx, Int.emod_eq_of_lt hx (by omega)]

theorem gmI64_toInt (x : JInt .i64) :
    (JuliaLean.C.fromJInt x).toInt = x.val := by
  have hb := x.property
  change -(2^63 : Int) ≤ x.val ∧ x.val ≤ 2^63-1 at hb
  simp only [JuliaLean.C.fromJInt, BitVec.toInt_ofInt, IntTy.bits, Int.bmod_def]
  split <;> omega

theorem gmI64_lt (x y : JInt .i64) :
    JuliaLean.base.int.lt x y = decide (x.val < y.val) := by
  have hx : JuliaLean.base.int.widenTo .i64 x = x := by
    apply Subtype.ext
    exact wrapInt_of_inRange .i64 x.val x.property
  have hy : JuliaLean.base.int.widenTo .i64 y = y := by
    apply Subtype.ext
    exact wrapInt_of_inRange .i64 y.val y.property
  change JuliaLean.base.int.slt_int (JuliaLean.base.int.widenTo .i64 x)
    (JuliaLean.base.int.widenTo .i64 y) = _
  rw [hx, hy]
  simp only [JuliaLean.base.int.slt_int, JuliaLean.C.jlSltInt, gmI64_toInt]

theorem gmCompareLengths (x y : JInt .i64) (n m : Nat)
    (hx : x.val = n) (hy : y.val = m) :
    ByteComparisonBinding.compareLengths x y =
      some (JInt.wrap .i64 (gmCompareCounts n m)) := by
  simp only [ByteComparisonBinding.compareLengths, JuliaLean.base.operators.cmpInteger,
    JuliaLean.base.operators.islessReal, gmI64_lt, hx, hy,
    JuliaLean.base.operators.ifelseValue, gmCompareCounts, Int.ofNat_lt,
    decide_eq_true_eq]
  by_cases hnm : n < m <;> by_cases hmn : m < n <;> simp [hnm, hmn]

theorem gmMin_val (x y : JInt .i64) (n m : Nat)
    (hx : x.val = n) (hy : y.val = m) :
    (min x y).val = (min n m : Nat) := by
  change (if x.val ≤ y.val then x else y).val = _
  by_cases h : x.val ≤ y.val
  · rw [if_pos h, hx]
    have hnm : n ≤ m := by omega
    rw [Nat.min_eq_left hnm]
  · rw [if_neg h, hy]
    have hmn : m ≤ n := by omega
    rw [Nat.min_eq_right hmn]

theorem gmMemcmp_evaluate (heap : ByteHeap) (pa pb : Ptr Unit)
    (n : JInt .i64) (hn : 0 ≤ n.val) :
    (JuliaLean.base.cmem.memcmp StandardC.standardCMemoryOps
      (fun n : JInt .i64 => .ok (JuliaLean.base.int.remT .u64 n))
      heap pa pb n).toOption =
    some (JInt.wrap .i64
      (StandardC.cMemcmp heap pa.address.val.toNat pb.address.val.toNat n.val.toNat).val) := by
  change some (JInt.wrap .i64
    (StandardC.cMemcmp heap pa.address.val.toNat pb.address.val.toNat
      (JuliaLean.base.int.remT .u64 n).val.toNat).val) = _
  rw [gmU64_rem_val n hn]


theorem gmCmem_val_range (heap : ByteHeap) (left right count : Nat) :
    (StandardC.cMemcmp heap left right count).val = -1 ∨
    (StandardC.cMemcmp heap left right count).val = 0 ∨
    (StandardC.cMemcmp heap left right count).val = 1 := by
  induction count generalizing left right with
  | zero => exact Or.inr (Or.inl rfl)
  | succ count ih =>
    simp only [StandardC.cMemcmp]
    split
    · exact ih (left+1) (right+1)
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)

theorem gmReadBytes_length (heap : ByteHeap) (address count : Nat) :
    (heap.readBytes address count).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
    simp only [ByteHeap.readBytes, List.length_cons, ih]

theorem gmSmall_wrap_val (z : Int) (h : z = -1 ∨ z = 0 ∨ z = 1) :
    (JInt.wrap .i64 z).val = z := by
  apply gmI64_wrap_val
  rcases h with h | h | h <;> rw [h] <;> decide

theorem gmNat_wrap_val (n : Nat) (h : n < 2^62) :
    (JInt.wrap .i64 (Int.ofNat n)).val = (n : Int) := by
  apply gmI64_wrap_val
  change n < 4611686018427387904 at h
  change -(2^63 : Int) ≤ (n : Int) ∧ (n : Int) < 2^63
  omega

theorem GenericmemoryByteComparisonV2_proven :
    JuliaLean.Proofs.base.genericmemory.Round2.ByteMemoryComparisonCorrect := by
  intro bytes objects pointers a b ha hb
  rcases ha with ⟨oa, hoa, haAtomic, haSize, haUnion, haArray,
    haLayout, haLen, haPtr, haValid, haSlots⟩
  rcases hb with ⟨ob, hob, hbAtomic, hbSize, hbUnion, hbArray,
    hbLayout, hbLen, hbPtr, hbValid, hbSlots⟩
  let na := oa.slots.length
  let nb := ob.slots.length
  let pa := (pointers a.handle).ptr
  let pb := (pointers b.handle).ptr
  let la := JInt.wrap .i64 (Int.ofNat na)
  let lb := JInt.wrap .i64 (Int.ofNat nb)
  let ca := StandardC.cMemcmp bytes pa.address.val.toNat pb.address.val.toNat (min na nb)
  have hla : ByteComparisonBinding.lengthModel objects a = some la :=
    gmLengthModel objects a oa hoa
  have hlb : ByteComparisonBinding.lengthModel objects b = some lb :=
    gmLengthModel objects b ob hob
  have hlav : la.val = (na : Int) := gmNat_wrap_val na haLen
  have hlbv : lb.val = (nb : Int) := gmNat_wrap_val nb hbLen
  have hmin : (min la lb).val = ((min na nb : Nat) : Int) :=
    gmMin_val la lb na nb hlav hlbv
  have hca := gmCmem_val_range bytes pa.address.val.toNat pb.address.val.toNat (min na nb)
  have hcaw : (JInt.wrap .i64 ca.val).val = ca.val := gmSmall_wrap_val ca.val hca
  have hmem := gmMemcmp_evaluate bytes pa pb (min la lb) (by rw [hmin]; exact Int.natCast_nonneg _)
  have hminNat : (min la lb).val.toNat = min na nb := by rw [hmin]; rfl
  rw [hminNat] at hmem
  have hcmp := gmCompareLengths la lb na nb hlav hlbv
  let left := bytes.readBytes pa.address.val.toNat na
  let right := bytes.readBytes pb.address.val.toNat nb
  let answer := gmListCmp left right
  have hfinish : gmFinish ca.val na nb = answer :=
    gmCmem_finish bytes na nb pa.address.val.toNat pb.address.val.toNat
  have hspec := gmListCmp_spec left right
  have hanswer : (JInt.wrap .i64 answer).val = answer := gmSmall_wrap_val answer hspec.1
  have hcall := JuliaLean.Proofs.base.genericmemory.byteMemoryComparisonOrdersPrefix_proven
    (ByteComparisonBinding.lengthModel objects)
    (fun _ => ()) (fun _ => some ())
    (fun mem => some (JuliaLean.base.pointer.unsafeConvertMemoryCvoid (pointers mem.handle)))
    (fun p q n =>
      (JuliaLean.base.cmem.memcmp StandardC.standardCMemoryOps
        (fun n : JInt .i64 => .ok (JuliaLean.base.int.remT .u64 n)) bytes p q n).toOption)
    ByteComparisonBinding.compareLengths a b (JInt.wrap .i64 ca.val) pa pb la lb () ()
    hla hlb rfl rfl rfl rfl rfl rfl hmem
  dsimp only
  refine ⟨JInt.wrap .i64 answer, ?_, ?_⟩
  · by_cases hneg : ca.val < 0
    · have hnegc : (JInt.wrap .i64 ca.val) < (0 : JInt .i64) := by
        change (JInt.wrap .i64 ca.val).val < 0
        rw [hcaw]
        exact hneg
      have heq : answer = -1 := by
        rw [← hfinish]
        simp only [gmFinish, hneg, ite_true]
      rw [heq]
      exact hcall.1 hnegc
    · by_cases hpos : 0 < ca.val
      · have hposc : (0 : JInt .i64) < (JInt.wrap .i64 ca.val) := by
          change 0 < (JInt.wrap .i64 ca.val).val
          rw [hcaw]
          exact hpos
        have heq : answer = 1 := by
          rw [← hfinish]
          simp only [gmFinish, hneg, hpos, ite_false, ite_true]
        rw [heq]
        exact hcall.2.1 hposc
      · have hz : ca.val = 0 := by omega
        have hzc : JInt.wrap .i64 ca.val = (0 : JInt .i64) := by
          apply Subtype.ext
          change (JInt.wrap .i64 ca.val).val = 0
          rw [hcaw, hz]
        have heq : answer = gmCompareCounts na nb := by
          rw [← hfinish]
          simp only [gmFinish, hneg, hpos, ite_false]
        rw [heq]
        exact (hcall.2.2 hzc).trans hcmp
  · rw [hanswer]
    simpa only [ByteComparisonBinding.contents, ByteComparisonBinding.extent,
      hoa, hob] using hspec

end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.Proofs.base.genericmemory

open JuliaLean.Registry
def entries : List Entry :=
  [ { id := "genericmemory-linear-indexing", juliaFile := "base/genericmemory.jl",
      juliaFns := ["IndexStyle(::Type{<:GenericMemory})"],
      statement := "GenericMemory uses the linear indexing style promised by its DenseVector interface.",
      source := "base/genericmemory.jl:6-8,64", status := .proven,
      prop := ``MemoryLinearIndexing, thm := some ``memoryLinearIndexing_proven }
  , { id := "genericmemory-memoryindex-one-based", juliaFile := "base/genericmemory.jl",
      juliaFns := ["memoryindex(::GenericMemoryRef)"],
      statement := "A valid GenericMemoryRef reports a one-based index within its backing memory.",
      source := "memoryindex docstring; base/genericmemory.jl:68-87", status := .proven,
      prop := ``MemoryIndexIsOneBased, thm := some ``memoryIndexIsOneBased_proven }
  , { id := "genericmemory-isassigned-bounds", juliaFile := "base/genericmemory.jl",
      juliaFns := ["isassigned(::GenericMemory, ::Int)", "isassigned(::GenericMemoryRef)"],
      statement := "A checked isassigned query returns false for an index outside the memory and queries initialization for an in-bounds reference.",
      source := "base/genericmemory.jl:188-195; uninitialized-memory manual", status := .proven,
      prop := ``MemoryIsassignedBounds, thm := some ``memoryIsassignedBounds_proven }
  , { id := "memsafety-genericmemory-checked-callers", juliaFile := "base/genericmemory.jl",
      juliaFns := ["isassigned(::GenericMemory, i)", "copy(::Memory)",
        "setindex!(::Memory, ::Memory, ::AbstractUnitRange)",
        "setindex!(::Memory, ::Memory, ::Colon)"],
      statement := "Checked assignment queries return false outside the memory, and bounds-checked copying and range assignment stop before an invalid access.",
      source := "computed checks and loop bounds; base/genericmemory.jl:188-192,257-262,345-363",
      status := .proven, prop := ``GenericMemoryCheckedAccessesInBounds, thm := some ``genericMemoryCheckedAccessesInBounds_proven }
  , { id := "genericmemory-unsetindex-semantics", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsetindex!(::MemoryRef)", "unsetindex!(::Memory, ::Int)",
        "unsetindex!(::Union{Array,Memory}, ::Integer)"],
      statement := "Unsetting a memory reference leaves its slot unassigned and returns the same reference or memory object.",
      source := "unsetindex! docstrings; base/genericmemory.jl:91-149", status := .proven,
      prop := ``MemoryUnsetReturnsTarget, thm := some ``memoryUnsetReturnsTarget_proven }
  , { id := "genericmemory-atomic-unset-order", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsetindex_atomic!(::AtomicMemoryRef)", "unsetindex_atomic!(::AtomicMemory, ::Symbol, ::Int)",
        "unsetindex_atomic!(::AtomicMemory, ::Symbol, ::Integer)"],
      statement := "Atomic unsetting leaves the slot unassigned, uses the requested ordering, and returns the same reference or memory object.",
      source := "unsetindex_atomic! docstrings; base/genericmemory.jl:151-183", status := .proven,
      prop := ``AtomicMemoryUnsetReturnsReference, thm := some ``atomicMemoryUnsetReturnsReference_proven }
  , { id := "genericmemory-copy-content", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsafe_copyto!(::MemoryRef{T}, ::MemoryRef{T}, n)",
        "unsafe_copyto!(::Memory{T}, doffs, ::Memory{T}, soffs, n)",
        "unsafe_copyto!(::Memory, doffs, ::Memory, soffs, n)", "copy(::Memory)"],
      statement := "Typed and reference copies preserve source contents, including undefined slots, across overlaps; in a concrete slot model, fallback copy converts defined values and preserves undefined slots; copy(::Memory) retains source contents.",
      source := "base/genericmemory.jl:197-263; copy semantics", status := .proven,
      prop := ``MemoryCopyPreservesContents, thm := some ``JuliaLean.Proofs.base.genericmemory.memoryCopyPreservesContents_proven }
  , { id := "genericmemory-copy-dispatch", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsafe_copyto!(::GenericMemoryRef, ::GenericMemoryRef, n)"],
      statement := "Generic memory references use typed copying when element types match and conversion-aware fallback copying otherwise.",
      source := "base/genericmemory.jl:216-221", status := .proven,
      prop := ``MemoryCopyDispatchesByElementType, thm := some ``JuliaLean.Proofs.base.genericmemory.memoryCopyDispatchesByElementType_proven }
  , { id := "genericmemory-copy-extent", juliaFile := "base/genericmemory.jl",
      juliaFns := ["copy(::Memory)"],
      statement := "copy(::Memory) creates independent storage with the source element count.",
      source := "copy docstring; base/genericmemory.jl:257-263", status := .proven,
      prop := ``MemoryCopyPreservesExtent, thm := some ``memoryCopyPreservesExtent_proven }
  , { id := "genericmemory-similar-extent", juliaFile := "base/genericmemory.jl",
      juliaFns := ["similar(::GenericMemory)", "similar(::GenericMemory, ::Type)",
        "similar(::GenericMemory, ::Int)", "similar(::GenericMemory, ::Type, ::Dims{1})",
        "similar(::GenericMemory, ::Dims{1})"],
      statement := "similar preserves the memory kind and address space and allocates the requested one-dimensional element count.",
      source := "similar docstrings and constructors; base/genericmemory.jl:270-281", status := .proven,
      prop := ``SimilarMemoryPreservesExtent, thm := some ``similarMemoryPreservesExtent_proven }
  , { id := "genericmemory-byte-fill", juliaFile := "base/genericmemory.jl",
      juliaFns := ["fill!(::Union{Memory{UInt8},Memory{Int8}}, ::Integer)"],
      statement := "Byte-memory fill converts the integer to the element type and fills every slot with that value.",
      source := "fill! contract; base/genericmemory.jl:283-291", status := .proven,
      prop := ``ByteMemoryFillUsesConvertedValue, thm := some ``byteMemoryFillUsesConvertedValue_proven }
  , { id := "genericmemory-convert-promote", juliaFile := "base/genericmemory.jl",
      juliaFns := ["convert(::Type{<:Memory}, ::AbstractArray)",
        "promote_rule(::Type{Memory{T}}, ::Type{Memory{S}})"],
      statement := "Conversion reuses an array already of the requested Memory type; promotion applies the element-type promotion rule to both Memory element types.",
      source := "base/genericmemory.jl:292-296", status := .proven,
      prop := ``MemoryConversionAndPromotion, thm := some ``memoryConversionAndPromotion_proven }
  , { id := "genericmemory-array-constructor-copy", juliaFile := "base/genericmemory.jl",
      juliaFns := ["Memory{T}(::AbstractArray{S,1})"],
      statement := "Constructing Memory from a one-dimensional array checks axes and copies its values.",
      source := "constructor comment; base/genericmemory.jl:298-301", status := .proven,
      prop := ``MemoryArrayConstructorCopies, thm := some ``memoryArrayConstructorCopies_proven }
  , { id := "genericmemory-range-getindex", juliaFile := "base/genericmemory.jl",
      juliaFns := ["getindex(::Memory, ::AbstractUnitRange{<:Integer})",
        "getindex(::Memory, ::AbstractUnitRange{Bool})"],
      statement := "Range indexing checks bounds and returns a copied slice; Bool ranges are converted to valid indices.",
      source := "base/genericmemory.jl:305-322", status := .proven,
      prop := ``MemoryRangeGetindexChecksBounds, thm := some ``memoryRangeGetindexChecksBounds_proven }
  , { id := "genericmemory-setindex-semantics", juliaFile := "base/genericmemory.jl",
      juliaFns := ["_setindex!(::Memory{T}, ::T, ::Int)", "setindex!(::Memory{T}, x, ::Int)",
        "setindex!(::Memory{T}, x, ::Int, ::Int, ::Int...)",
        "setindex!(::Memory{T}, ::Memory{T}, ::AbstractUnitRange{Int})",
        "setindex!(::Memory{T}, ::Memory{T}, ::Colon)"],
      statement := "Scalar setindex converts to the element type and checks bounds; Cartesian scalar and bulk assignments check their indices and source shape.",
      source := "base/genericmemory.jl:324-364", status := .proven,
      prop := ``MemoryScalarSetindexReturnsTarget, thm := some ``memoryScalarSetindexReturnsTarget_proven }
  , { id := "genericmemory-bulk-setindex-shape", juliaFile := "base/genericmemory.jl",
      juliaFns := ["setindex!(::Memory{T}, ::Memory{T}, ::AbstractUnitRange{Int})",
        "setindex!(::Memory{T}, ::Memory{T}, ::Colon)"],
      statement := "Range and colon assignment reject source memories whose lengths differ from the selected target shape.",
      source := "base/genericmemory.jl:345-364", status := .proven,
      prop := ``MemoryBulkSetindexChecksShape, thm := some ``memoryBulkSetindexChecksShape_proven }
  , { id := "genericmemory-byte-comparison", juliaFile := "base/genericmemory.jl",
      juliaFns := ["cmp(::Memory{UInt8}, ::Memory{UInt8})"],
      statement := "Byte-memory comparison follows lexicographic byte order, with memory length deciding ties after an equal prefix.",
      source := "base/genericmemory.jl:366-393", status := .proven,
      prop := ``ByteMemoryComparisonOrdersPrefix, thm := some ``byteMemoryComparisonOrdersPrefix_proven }
  , { id := "genericmemory-equal-bitinteger-memory", juliaFile := "base/genericmemory.jl",
      juliaFns := ["==(a::M, b::M) where {M <: BitIntegerMemory}"],
      statement := "BitIntegerMemory values of different lengths compare unequal; equal-length values compare all stored bytes.",
      source := "base/genericmemory.jl:378-393", status := .proven,
      prop := ``BitIntegerMemoryEqualityRequiresEqualLengths, thm := some ``bitIntegerMemoryEqualityRequiresEqualLengths_proven }
  , { id := "genericmemory-byte-comparison-v2", juliaFile := "base/genericmemory.jl",
      juliaFns := ["cmp(::Memory{UInt8}, ::Memory{UInt8})"],
      statement := "Byte-memory comparison follows lexicographic byte order, with memory length deciding ties after an equal prefix.",
      source := "base/genericmemory.jl:366-393", status := .proven,
      prop := ``Round2.ByteMemoryComparisonCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.GenericmemoryByteComparisonV2_proven }
  , { id := "genericmemory-equal-bitinteger-memory-v2", juliaFile := "base/genericmemory.jl",
      juliaFns := ["==(a::M, b::M) where {M <: BitIntegerMemory}"],
      statement := "BitIntegerMemory values of different lengths compare unequal; equal-length values compare all stored bytes.",
      source := "base/genericmemory.jl:378-393", status := .todo,
      prop := ``Round2.BitIntegerMemoryEqualityCorrect, thm := none }
  , { id := "genericmemory-sorted-findall", juliaFile := "base/genericmemory.jl",
      juliaFns := ["findall(::Fix2{typeof(in),<:Union{Memory{<:Real},Real}}, ::Memory{<:Real})"],
      statement := "Sorted values and sorted search values use the sorted-search path; other inputs use general membership search.",
      source := "base/genericmemory.jl:395-401", status := .proven,
      prop := ``MemoryFindallUsesSortedSearch, thm := some ``memoryFindallUsesSortedSearch_proven }
  ]

/-! Method -> property coverage. Pure forwarding/plumbing methods are listed above. -/
/-!
64 -> genericmemory-linear-indexing
66 -> Nothing to promise
87 -> genericmemory-memoryindex-one-based
89 -> Nothing to promise
119,148,149 -> genericmemory-unsetindex-semantics
160,175,181 -> genericmemory-atomic-unset-order
185,186 -> Nothing to promise
189,195 -> genericmemory-isassigned-bounds; memsafety-genericmemory-checked-callers
198,223,230,257 -> genericmemory-copy-content; genericmemory-copy-extent; memsafety-genericmemory-checked-callers
216 -> genericmemory-copy-dispatch
272,274,276,278,280 -> genericmemory-similar-extent
283 -> genericmemory-byte-fill
294,296 -> genericmemory-convert-promote
265,266 -> Nothing to promise
301 -> genericmemory-array-constructor-copy
308,320 -> genericmemory-range-getindex
322 -> Nothing to promise
326,333,339 -> genericmemory-setindex-semantics
346,356 -> genericmemory-setindex-semantics; genericmemory-bulk-setindex-shape;
          memsafety-genericmemory-checked-callers
367 -> genericmemory-byte-comparison
380 -> genericmemory-equal-bitinteger-memory
395 -> genericmemory-sorted-findall
404 -> genericmemory-indcopy-regions
416,422,434,453,459,471 -> genericmemory-atomic-ordering
-/

end JuliaLean.Proofs.base.genericmemory
