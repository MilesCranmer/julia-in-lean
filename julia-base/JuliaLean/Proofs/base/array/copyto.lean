import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy
import JuliaLean.Proofs.base.array.common.grow

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.round6e
open JuliaLean

def offsetRef (memory : Memory T) (index : Nat) : Ref T :=
  ⟨memory, if memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0 then
    JInt.wrap .u64 index
  else memory.ptr.address + JInt.wrap .u64 ((index : Int) * memory.layoutBytes.val)⟩

def tagAddress (reference : Ref T) (index : Nat) : Nat :=
  JuliaLean.base.pointer.addressMod (reference.mem.ptr.address.val.toNat +
    reference.mem.capacity * reference.mem.layoutBytes.val.toNat +
    reference.ptr_or_offset.val.toNat + index)

def selectors (heap : JuliaLean.base.pointer.ByteHeap) (reference : Ref T) (n : Nat) : List Byte :=
  if reference.mem.arrayElement = 2 then
    (List.range n).map (fun index => heap.readByte (tagAddress reference index))
  else []

def frame (before after : JuliaLean.base.pointer.ByteHeap) : Prop :=
  ∀ address, address < 2 ^ 64 → before.validByte address = true →
    after.validByte address = true ∧ after.readByte address = before.readByte address

def validMemory (heap : JuliaLean.base.pointer.ByteHeap) (memory : Memory T) : Prop :=
  0 ≤ memory.layoutBytes.val ∧ memory.capacity < 2 ^ 63 - 1 ∧
  memory.capacity * memory.layoutBytes.val.toNat +
    (if memory.arrayElement = 2 then memory.capacity else 0) < 2 ^ 63 - 1 ∧
  memory.ptr.address.val.toNat + memory.capacity * memory.layoutBytes.val.toNat +
    (if memory.arrayElement = 2 then memory.capacity else 0) ≤ 2 ^ 64 ∧
  (∀ byte, byte < memory.capacity * memory.layoutBytes.val.toNat →
    heap.validByte (JuliaLean.base.pointer.addressMod
      (memory.ptr.address.val.toNat + byte)) = true) ∧
  (memory.arrayElement = 2 → ∀ index, index < memory.capacity →
    heap.validByte (JuliaLean.base.pointer.addressMod
      (memory.ptr.address.val.toNat + memory.capacity * memory.layoutBytes.val.toNat + index)) = true)

def memoryRegion (memory : Memory T) (address : Nat) : Prop :=
  ∃ offset, offset < memory.capacity * memory.layoutBytes.val.toNat +
    (if memory.arrayElement = 2 then memory.capacity else 0) ∧
    address = JuliaLean.base.pointer.addressMod (memory.ptr.address.val.toNat + offset)

def separateMemory (dest src : Memory T) : Prop :=
  ∀ address, memoryRegion dest address → ¬memoryRegion src address

def validRef (heap : JuliaLean.base.pointer.ByteHeap) (reference : Ref T) (n : Nat) : Prop :=
  validMemory heap reference.mem ∧
  ∃ offset, offset + n ≤ reference.mem.capacity ∧ reference = offsetRef reference.mem offset

def validArray (world : World σ) (array : ArrayObject T) : Prop :=
  array.identity < world.nextArray ∧ array.ref.mem.identity < world.nextMemory ∧
  (∀ dimension ∈ array.dimensions, 0 ≤ dimension.val) ∧
  validRef world.bytes array.ref (array.dimensions.map (fun d => d.val.toNat)).prod

/-- The ordinary allocator uses MAXINTVAL-1; an unsafe-wrapped memory may be one larger. -/
def allocationFits (memory : Memory T) (n : Nat) : Prop :=
  n = 0 ∨ (n < 2 ^ 63 - 2 ∧
    n * memory.layoutBytes.val.toNat + (if memory.arrayElement = 2 then n else 0) < 2 ^ 63 - 2)

structure Runtime (ε σ T : Type) where
  isBits : Bool
  allocate : Memory T → I → M ε σ (Memory T)
  ccallCopy : Memory T → U → Memory T → U → I → M ε σ Unit
  preserveBegin : Ref T → Nat
  preserveEnd : Nat → M ε σ Unit

/-- Contracts of the runtime primitives, rather than a law for a Base copy wrapper. -/
def Runtime.Law (runtime : Runtime ε σ T) : Prop :=
  (∀ world : World σ, ∀ source : Memory T, ∀ n : I,
    validMemory world.bytes source → source.identity < world.nextMemory → 0 ≤ n.val →
    let run := (runtime.allocate source n).run world
    (allocationFits source n.val.toNat →
      (∃ failure after, run = (.error (.inr failure), after)) ∨ ∃ fresh after,
      run = (.ok fresh, after) ∧ fresh.capacity = n.val.toNat ∧
      fresh.layoutBytes = source.layoutBytes ∧ fresh.arrayElement = source.arrayElement ∧
      validMemory after.bytes fresh ∧ frame world.bytes after.bytes ∧
      after.nextArray = world.nextArray ∧ after.other = world.other ∧
      fresh.identity < after.nextMemory ∧
      (n.val = 0 → after.nextMemory = world.nextMemory) ∧
      (0 < n.val → fresh.identity = world.nextMemory ∧
        after.nextMemory = world.nextMemory + 1 ∧
        (∀ byte, byte < fresh.capacity * fresh.layoutBytes.val.toNat →
          world.bytes.validByte (payloadAddress (memoryref fresh) byte) = false) ∧
        (fresh.arrayElement = 2 → ∀ index, index < fresh.capacity →
          world.bytes.validByte (tagAddress (memoryref fresh) index) = false)) ∧
      (∀ address, after.bytes.validByte address = true →
        world.bytes.validByte address = true ∨
        (∃ byte, byte < fresh.capacity * fresh.layoutBytes.val.toNat ∧
          address = payloadAddress (memoryref fresh) byte) ∨
        (fresh.arrayElement = 2 ∧ ∃ index, index < fresh.capacity ∧
          address = tagAddress (memoryref fresh) index))) ∧
    (¬allocationFits source n.val.toNat → ∃ message,
      run = (.error (.inl (.argument message)), world))) ∧
  (∀ world : World σ, ∀ token,
    (runtime.preserveEnd token).run world = (.ok (), world)) ∧
  (∀ world : World σ, ∀ dest src : Ref T, ∀ n : I,
    0 ≤ n.val → validRef world.bytes dest n.val.toNat →
    validRef world.bytes src n.val.toNat →
    dest.mem.layoutBytes = src.mem.layoutBytes →
    dest.mem.arrayElement = src.mem.arrayElement →
    separateMemory dest.mem src.mem →
    let run := (runtime.ccallCopy dest.mem dest.ptr_or_offset
      src.mem src.ptr_or_offset n).run world
    ∃ after, run = (.ok (), after) ∧
      after.nextMemory = world.nextMemory ∧ after.nextArray = world.nextArray ∧
      after.other = world.other ∧ after.bytes.validByte = world.bytes.validByte ∧
      payload after.bytes dest n.val.toNat = payload world.bytes src n.val.toNat ∧
      selectors after.bytes dest n.val.toNat = selectors world.bytes src n.val.toNat ∧
      (∀ address, address < 2 ^ 64 →
        (¬∃ byte, byte < n.val.toNat * dest.mem.layoutBytes.val.toNat ∧
          address = payloadAddress dest byte) →
        (dest.mem.arrayElement ≠ 2 ∨ ¬∃ index, index < n.val.toNat ∧
          address = tagAddress dest index) →
        after.bytes.readByte address = world.bytes.readByte address))

def moveBytes (calls : JuliaLean.base.cmem.CMemoryOps)
    (dest src : JuliaLean.base.pointer.Ptr Unit) (n : I) : M ε σ Unit := do
  let old ← get
  match JuliaLean.base.cmem.memmove calls JuliaLean.base.cmem.csizeFromInt old.bytes dest src n.val with
  | .error _ => throw (Sum.inl JuliaLean.base.array.Error.inexact)
  | .ok (bytes, _) => set { old with bytes := bytes }

/-- Only fields reached by `unsafeCopytoRefs ... false` are supplied here. -/
def copyOps (runtime : Runtime ε σ T) (calls : JuliaLean.base.cmem.CMemoryOps)
    (layout : I)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) :=
  { unreached with
    isZero := fun n => JuliaLean.base.int.eq_int n (JInt.wrap .i64 0)
    toInt := fun n => match JuliaLean.base.int.convert .i64 n with
      | .ok value => pure value
      | .error _ => throw (Sum.inl JuliaLean.base.array.Error.inexact)
    byteCount := fun _ n => pure (JuliaLean.base.int.binop JuliaLean.base.int.mul layout n)
    isBitsType := fun _ => runtime.isBits
    gcPreserveBegin := runtime.preserveBegin
    gcPreserveEnd := runtime.preserveEnd
    unsafeConvert := fun reference => pure (pointer reference)
    memmove := moveBytes calls
    ccallCopy := runtime.ccallCopy }

def copyArray (runtime : Runtime ε σ T) (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (array : ArrayObject T) : M ε σ (ArrayObject T) :=
  JuliaLean.base.abstractarray.ArrayCallees.copyArray
    (fun a => pure a.ref) (fun a => pure (length a))
    (fun reference n => runtime.allocate reference.mem n)
    (fun memory => pure (memoryref memory))
    (fun dest src n => do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
        (copyOps runtime calls src.mem.layoutBytes unreached) false dest src n
      pure ())
    (fun a => pure (size a)) newArray array

/-- Shallow copying preserves every payload and selector byte and every old live byte.
Empty copies still have a fresh Array header; the zero-length Memory singleton may be shared.
Allocator failures retain their error and resulting state, without an allocation-success
precondition. The ordinary allocator's size error is distinguished from runtime failures. -/
def CopyArraySpec : Prop :=
  ∀ (ε σ T : Type) (runtime : Runtime ε σ T), runtime.Law →
  ∀ (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world : World σ) (array : ArrayObject T),
    validArray world array →
    (runtime.isBits = true → array.ref.mem.arrayElement ≠ 2) →
    let n := (array.dimensions.map (fun d => d.val.toNat)).prod
    let allocation := (runtime.allocate array.ref.mem (length array)).run world
    let run := (copyArray runtime calls unreached array).run world
    (match allocation.1 with
    | .error failure => run = (.error failure, allocation.2)
    | .ok _ => ∃ result after,
      run = (.ok result, after) ∧ result.identity = world.nextArray ∧
      result.identity ≠ array.identity ∧ result.dimensions = array.dimensions ∧
      result.ref.mem.capacity = n ∧
      result.ref.mem.layoutBytes = array.ref.mem.layoutBytes ∧
      result.ref.mem.arrayElement = array.ref.mem.arrayElement ∧
      validArray after result ∧
      (0 < n → result.ref.mem.identity ≥ world.nextMemory) ∧
      payload after.bytes result.ref n = payload world.bytes array.ref n ∧
      selectors after.bytes result.ref n = selectors world.bytes array.ref n ∧
      frame world.bytes after.bytes ∧ after.other = world.other ∧
      after.nextArray = world.nextArray + 1) ∧
    (¬allocationFits array.ref.mem n → ∃ message,
      run = (.error (.inl (.argument message)), world))
end JuliaLean.Proofs.base.array.round6e


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000


abbrev ByteMemory := Nat → JInt .u8

/-- The documented memmove interface reads overlapping source bytes before writing. -/
def ByteMoveLaw (move : Nat → Nat → I → StateM ByteMemory Unit) : Prop :=
  ∀ (old : ByteMemory) (dest src : Nat) (bytes : I), 0 ≤ bytes.val →
    ∀ address, ((move dest src bytes).run old).2 address =
      if dest ≤ address ∧ address < dest + bytes.val.toNat
      then old (src + (address - dest)) else old address

def PointerCopySpec : Prop :=
  ∀ (N : Type) (value : N → Int) (multiply : N → I → I),
    (∀ n stride, 0 ≤ value n → 0 ≤ stride.val →
      value n * stride.val ≤ IntTy.i64.max →
      (multiply n stride).val = value n * stride.val) →
    ∀ (move : Nat → Nat → I → StateM ByteMemory Unit), ByteMoveLaw move →
    ∀ (old : ByteMemory) (dest src : Nat) (n : N) (stride : I),
      0 ≤ value n → 0 ≤ stride.val → value n * stride.val ≤ IntTy.i64.max →
      let result := (unsafeCopyPtr stride multiply move dest src n).run old
      result.1 = dest ∧
      (∀ k, k < (value n).toNat → ∀ j, j < stride.val.toNat →
        result.2 (dest + k * stride.val.toNat + j) =
          old (src + k * stride.val.toNat + j)) ∧
      (∀ address, address < dest ∨ dest + (value n).toNat * stride.val.toNat ≤ address →
        result.2 address = old address)

theorem unsafeCopyPtr_state_run (stride : I) (multiply : N → I → Bytes)
    (move : P → P → Bytes → StateM σ Unit) (dest src : P) (n : N) (state : σ) :
    (unsafeCopyPtr stride multiply move dest src n).run state =
      (dest, ((move dest src (multiply n stride)).run state).2) := by
  rfl

/-- A window copy reads the old source even when the address ranges overlap. -/
def copiedElements (old : Nat → Option α) (dest src count : Nat) : Nat → Option α :=
  fun address => if dest ≤ address ∧ address < dest + count
    then old (src + (address - dest)) else old address

def UnsafeArrayCopySpec : Prop :=
  ∀ (α OffD OffS N : Type) (destValue : OffD → Int) (srcValue : OffS → Int)
    (countValue : N → Int)
    (destReference : (Nat × Nat) → OffD → StateM (Nat → Option α) Nat)
    (srcReference : (Nat × Nat) → OffS → StateM (Nat → Option α) Nat)
    (copy : Nat → Nat → N → StateM (Nat → Option α) Unit),
    (∀ old a i, 1 ≤ destValue i ∧ destValue i ≤ (a.2 : Int) →
      (destReference a i).run old = (a.1 + (destValue i - 1).toNat, old)) →
    (∀ old a i, 1 ≤ srcValue i ∧ srcValue i ≤ (a.2 : Int) →
      (srcReference a i).run old = (a.1 + (srcValue i - 1).toNat, old)) →
    (∀ old dest src n, 0 ≤ countValue n →
      (copy dest src n).run old = ((), copiedElements old dest src (countValue n).toNat)) →
    ∀ (old : Nat → Option α) (dest src : Nat × Nat) (di : OffD) (si : OffS) (n : N),
      0 ≤ countValue n →
      (countValue n ≠ 0 →
        1 ≤ destValue di ∧ destValue di + countValue n - 1 ≤ (dest.2 : Int) ∧
        1 ≤ srcValue si ∧ srcValue si + countValue n - 1 ≤ (src.2 : Int)) →
      (unsafeCopyArray (fun n => countValue n == 0) destReference srcReference copy
        dest di src si n).run old =
      (dest, copiedElements old (dest.1 + (destValue di - 1).toNat)
        (src.1 + (srcValue si - 1).toNat) (countValue n).toNat)

theorem unsafeCopyArray_state_run (isZero : N → Bool)
    (destRef : D → OffD → StateM σ R) (srcRef : S → OffS → StateM σ R)
    (copy : R → R → N → StateM σ Unit)
    (dest : D) (di : OffD) (src : S) (si : OffS) (n : N) (old : σ) :
    (unsafeCopyArray isZero destRef srcRef copy dest di src si n).run old =
      if isZero n then (dest, old)
      else
        let d := (destRef dest di).run old
        let s := (srcRef src si).run d.2
        (dest, ((copy d.1 s.1 n).run s.2).2) := by
  cases hz : isZero n <;> simp only [unsafeCopyArray, hz, Bool.false_eq_true,
    ↓reduceIte]
  all_goals rfl

/-- The memory.jl primitive copies a snapshot, including unassigned slots. -/
def MemoryCopyLaw (copy : Nat → Nat → I → CopyM α Unit) : Prop :=
  ∀ old dest src n, 0 ≤ n.val →
    (copy dest src n).run old =
      (.ok (), copiedElements old dest src n.val.toNat)

def copyBounds (value : Z → Int) (a : Nat × Nat) (i : Z) : CopyM α Unit :=
  fun old => (if 1 ≤ value i ∧ value i ≤ (a.2 : Int)
    then .ok () else .error .bounds, old)

def copyReference (a : Nat × Nat) (i : I) : CopyM α Nat :=
  fun old => (.ok (a.1 + (i.val - 1).toNat), old)

def copyInt (value : Z → Int) (i : Z) : CopyM α I :=
  fun old => (if IntTy.i64.min ≤ value i ∧ value i ≤ IntTy.i64.max
    then .ok (JInt.wrap .i64 (value i)) else .error .inexact, old)

def copyLength (a : Nat × Nat) : CopyM α I :=
  fun old => (.ok (JInt.wrap .i64 a.2), old)

@[simp] theorem copyBounds_run (value : Z → Int) (a : Nat × Nat) (i : Z)
    (old : Nat → Option α) :
    (copyBounds value a i).run old =
      (if 1 ≤ value i ∧ value i ≤ (a.2 : Int) then .ok () else .error .bounds, old) := rfl

@[simp] theorem copyReference_run (a : Nat × Nat) (i : I) (old : Nat → Option α) :
    (copyReference a i).run old = (.ok (a.1 + (i.val - 1).toNat), old) := rfl

@[simp] theorem copyInt_run (value : Z → Int) (i : Z) (old : Nat → Option α) :
    (copyInt value i).run old =
      (if IntTy.i64.min ≤ value i ∧ value i ≤ IntTy.i64.max
        then .ok (JInt.wrap .i64 (value i)) else .error .inexact, old) := rfl

@[simp] theorem copyLength_run (a : Nat × Nat) (old : Nat → Option α) :
    (copyLength a).run old = (.ok (JInt.wrap .i64 a.2), old) := rfl

/-- Independent window semantics: validation precedes every write. -/
def checkedCopyResult (old : Nat → Option α) (dest src : Nat × Nat)
    (di si n : Int) : Except Error (Nat × Nat) × (Nat → Option α) :=
  if n = 0 then (.ok dest, old)
  else if n < 0 then
    (.error (.argument "Number of elements to copy must be non-negative."), old)
  else if 1 ≤ di ∧ di + n - 1 ≤ (dest.2 : Int) ∧
      1 ≤ si ∧ si + n - 1 ≤ (src.2 : Int) then
    (.ok dest, copiedElements old (dest.1 + (di - 1).toNat)
      (src.1 + (si - 1).toNat) n.toNat)
  else (.error .bounds, old)

def CheckedCopySpec : Prop :=
  ∀ (α OffD OffS Count : Type) (dv : OffD → Int) (sv : OffS → Int) (nv : Count → Int)
    (copy : Nat → Nat → I → CopyM α Unit), MemoryCopyLaw copy →
    ∀ (old : Nat → Option α) (dest src : Nat × Nat) (di : OffD) (si : OffS) (n : Count),
    dest.2 < 2 ^ 63 → src.2 < 2 ^ 63 →
    let impl := copytoImpl
      (fun n => pure (decide (nv n = 0))) (fun n => pure (decide (nv n > 0)))
      copyLength copyLength (copyBounds dv) (copyBounds sv)
      (fun len i => pure (JInt.wrap .i64 (len.val - dv i)))
      (fun len i => pure (JInt.wrap .i64 (len.val - sv i)))
      (fun a b => pure (a + b)) (fun a b => pure (a + b))
      (fun n rem => pure (decide (nv n ≤ rem.val)))
      (fun n rem => pure (decide (nv n ≤ rem.val)))
      (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
      (copyInt dv) (copyInt sv) (copyInt nv) copyReference copyReference copy
    ∀ operation ∈ [impl, copyto288 impl, copyto290 impl, copyto292 impl, copyto296 impl],
      (operation dest di src si n).run old = checkedCopyResult old dest src (dv di) (sv si) (nv n)

def WholeCopySpec : Prop :=
  ∀ (α : Type) (copy : Nat → Nat → I → CopyM α Unit), MemoryCopyLaw copy →
    ∀ (old : Nat → Option α) (dest src : Nat × Nat),
    dest.2 < 2 ^ 63 → src.2 < 2 ^ 63 →
    let impl := copytoImpl
      (fun i : I => pure (decide (i.val = 0))) (fun i : I => pure (decide (i.val > 0)))
      copyLength copyLength
      (copyBounds (fun i : I => i.val)) (copyBounds (fun i : I => i.val))
      (fun len i => pure (JInt.wrap .i64 (len.val - i.val)))
      (fun len i => pure (JInt.wrap .i64 (len.val - i.val)))
      (fun a b => pure (a + b)) (fun a b => pure (a + b))
      (fun n rem => pure (decide (n.val ≤ rem.val)))
      (fun n rem => pure (decide (n.val ≤ rem.val)))
      (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
      (copyInt (fun i : I => i.val)) (copyInt (fun i : I => i.val))
      (copyInt (fun i : I => i.val)) copyReference copyReference copy
    let f1 := fun (_ : Nat × Nat) => (pure one : CopyM α I)
    let copy := copyto288 impl
    ∀ operation ∈ [copyto2arg f1 f1 copyLength copy,
        copyto325 f1 f1 copyLength copy, copyto326 f1 f1 copyLength copy,
        copyto327 f1 f1 copyLength copy, copyto330 f1 f1 copyLength copy,
        copyto331 f1 f1 copyLength copy, copyto332 f1 f1 copyLength copy],
      (operation dest src).run old =
        if src.2 ≤ dest.2 then (.ok dest, copiedElements old dest.1 src.1 src.2)
        else (.error .bounds, old)

def HeapCopyFrameSpec : Prop :=
  ∀ (α : Type) (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : Nat) (xs ys : List (Option α)),
    heap[src]? = some xs → heap[dest]? = some ys →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    (∀ e, xs.mapM convert = .error e → (heapWholeCopy convert dest src).run heap = .error e) ∧
    (∀ values, xs.mapM convert = .ok values →
      ∃ next, (heapWholeCopy convert dest src).run heap = .ok (dest, next) ∧
        next[dest]? = some values ∧ ∀ handle, handle ≠ dest → next[handle]? = heap[handle]?)

theorem heapCopyFrameSpec : HeapCopyFrameSpec := by
  intro α convert heap dest src xs ys hsrc hdest hlen hn
  have hc := heapWholeCopy_run convert heap dest src xs ys hsrc hdest hlen hn
  have hd : dest < heap.length := (List.getElem?_eq_some_iff.mp hdest).choose
  constructor
  · intro e he
    by_cases hz : xs = []
    · simp only [hz, List.mapM_nil, Pure.pure, Except.pure] at he
      cases he
    · simpa only [hz, ite_false, he, Except.map] using hc
  · intro values he
    by_cases hz : xs = []
    · have hv : values = [] := by
        simpa only [hz, List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using he.symm
      have hy : ys = [] := by
        apply List.length_eq_zero_iff.mp
        simpa only [hz, List.length_nil] using hlen
      refine ⟨heap, ?_, ?_, ?_⟩
      · simpa only [hz, ite_true] using hc
      · simpa only [hv, hy] using hdest
      · intro handle _; rfl
    · refine ⟨heap.set dest values, ?_, List.getElem?_set_self hd, ?_⟩
      · simpa only [hz, ite_false, he, Except.map] using hc
      · intro handle hne
        exact List.getElem?_set_ne (Ne.symm hne)

def CompleteCheckedCopySpec : Prop := CheckedCopySpec ∧ HeapCopyFrameSpec

/-- Core allocates a separate memory object; this operation has no source-array
parameter that could limit freshness to only one existing allocation. -/
def heapCopyAllocate (n : I) : VectorM α Nat :=
  if n.val < 0 then throw (.argument "invalid Memory dimensions")
  else heapAllocate n.val.toNat

/-- copy(::Array) with a shared heap of live memory objects. The memory copy
preserves unassigned slots, and the Core header constructor retains the type
and dimensions while referencing the newly allocated object. -/
abbrev heapFreshCopy {Tag α : Type} (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.ArrayCallees.copyArray (fun a => pure (a.handle, one))
    (fun a => pure (JInt.wrap .i64 (a.dimensions.prod : Int)))
    (fun _ n => heapCopyAllocate n) (fun handle => pure (handle, one))
    (heapCopyReferences (fun x => .ok x)) (fun a => pure a.dimensions)
    (fun ref dims => pure ⟨ref.1, src.elementType, dims, dims.map (fun n => (1, n))⟩) src

theorem heapFreshCopy_run {Tag α : Type} (heap : VectorHeap α) (src : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[src.handle]? = some xs)
    (hl : src.dimensions.prod = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapFreshCopy src).run heap =
      .ok (⟨heap.length, src.elementType, src.dimensions,
        src.dimensions.map (fun n => (1, n))⟩, heap ++ [xs]) := by
  have hv : (JInt.wrap .i64 (src.dimensions.prod : Int)).val = xs.length := by
    rw [hl]
    exact collectorLengthFits xs.length hn
  have hslt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  let allocated : VectorHeap α := heap ++ [List.replicate xs.length none]
  have hsrc : allocated[src.handle]? = some xs := by
    simpa [allocated, List.getElem?_append_left hslt] using hs
  have hdest : allocated[heap.length]? = some (List.replicate xs.length none) := by
    simp [allocated]
  have hm : ∀ ys : List (Option α),
      ys.mapM (fun x => Except.ok (ε := Error) x) = .ok ys := by
    intro ys
    induction ys with
    | nil => rfl
    | cons x ys ih =>
      simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]
  have hc :
      (heapCopyReferences (fun x => Except.ok (ε := Error) x)
        (heap.length, one) (src.handle, one)
        (JInt.wrap .i64 (src.dimensions.prod : Int))).run allocated =
      .ok ((), heap ++ [xs]) := by
    rw [hl, heapCopyReferences_whole_run (fun x => Except.ok (ε := Error) x)
      allocated heap.length src.handle xs (List.replicate xs.length none)
      hsrc hdest (by simp) hn, hm xs]
    simp [Except.map, allocated, List.set_append_right]
  simp only [heapFreshCopy, JuliaLean.base.abstractarray.ArrayCallees.copyArray, heapCopyAllocate, vector_bind_run, vector_pure_run,
    hv, Int.not_lt.mpr (Int.natCast_nonneg xs.length), ite_false]
  simp only [heapAllocate_run, Int.toNat_natCast]
  rw [hc]

def SharedHeapArrayCopySpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    ∃ dest next, (heapFreshCopy src).run heap = .ok (dest, next) ∧
      dest.elementType = src.elementType ∧ dest.dimensions = src.dimensions ∧
      next[dest.handle]? = some xs ∧
      (∀ handle, handle < heap.length → dest.handle ≠ handle ∧ next[handle]? = heap[handle]?)

theorem sharedHeapArrayCopySpec : SharedHeapArrayCopySpec := by
  intro Tag α heap src xs hs hl hn
  refine ⟨_, _, heapFreshCopy_run heap src xs hs hl hn, rfl, rfl, ?_, ?_⟩
  · simp
  · intro handle hh
    exact ⟨Nat.ne_of_gt hh, List.getElem?_append_left hh⟩
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorWindows

/- Wrapped `Int` values are compared through the `ival_*` lemmas; unfolding `JInt.wrap` inside
arithmetic decision procedures is exponential. -/
attribute [local irreducible] JInt.wrap

/-! ### Front growth -/

theorem window_drop (l : List β) (o d n : Int) (ho : 0 ≤ o) (hd : 0 ≤ d) (hn : 0 ≤ n) :
    ((l.drop o.toNat).take (n + d).toNat).drop d.toNat = (l.drop (o + d).toNat).take n.toNat := by
  have e1 : (n + d).toNat - d.toNat = n.toNat := by omega
  simp only [List.drop_take, List.drop_drop, e1]
  congr 2
  omega
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section HeapRanges

attribute [local irreducible] JInt.wrap wrapInt

theorem heapRemaining_val (xs : List (Option α)) (hn : xs.length < 4611686018427387904) (i : I)
    (h1 : 1 ≤ i.val) :
    (JInt.wrap .i64 (xs.length : Int) - i + one).val = xs.length - i.val + 1 := by
  have hb := ival_bounds i
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := ival_wrap _ (by omega)
  have hs : (JInt.wrap .i64 (xs.length : Int) - i).val = xs.length - i.val := by
    rw [ival_sub (JInt.wrap .i64 (xs.length : Int)) i (by rw [hv]; omega), hv]
  rw [ival_add (JInt.wrap .i64 (xs.length : Int) - i) one (by rw [hs, ival_one]; omega), hs,
    ival_one]

/-- The checked `copyto!(dest, di, src, si, n)` (array.jl:288) of a positive count whose windows
lie inside both arrays copies the source window into the destination window. -/
theorem heapCheckedCopy_window_run (heap : VectorHeap α) (dest src : Nat)
    (xs ys : List (Option α)) (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (hxn : xs.length < 2 ^ 62) (hyn : ys.length < 2 ^ 62) (di si n : I) (hn : 0 < n.val)
    (hdi : 1 ≤ di.val) (hde : di.val - 1 + n.val ≤ (ys.length : Int))
    (hsi : 1 ≤ si.val) (hse : si.val - 1 + n.val ≤ (xs.length : Int)) :
    (heapCheckedCopy (fun x => Except.ok (ε := Error) x) dest di src si n).run heap =
      .ok (dest, heap.set dest (ys.take (di.val - 1).toNat ++
        (xs.drop (si.val - 1).toNat).take n.val.toNat ++ ys.drop (di.val - 1 + n.val).toNat)) := by
  have hxn' : xs.length < 4611686018427387904 := hxn
  have hyn' : ys.length < 4611686018427387904 := hyn
  have hdy : di.val ≤ (ys.length : Int) := by clear hsrc hdest; omega
  have hsx : si.val ≤ (xs.length : Int) := by clear hsrc hdest; omega
  have hn0 : 0 ≤ n.val := Int.le_of_lt hn
  have hrd := heapRemaining_val ys hyn' di hdi
  have hrs := heapRemaining_val xs hxn' si hsi
  have hcd : (!decide (n.val ≤ (JInt.wrap .i64 (ys.length : Int) - di + one).val)) = false := by
    rw [hrd]; simp only [Bool.not_eq_false', decide_eq_true_eq]; clear hrs hsrc hdest; omega
  have hcs : (!decide (n.val ≤ (JInt.wrap .i64 (xs.length : Int) - si + one).val)) = false := by
    rw [hrs]; simp only [Bool.not_eq_false', decide_eq_true_eq]; clear hrd hcd hsrc hdest; omega
  obtain ⟨hld, _⟩ := heapLength_of_slots heap dest ys hdest hyn
  obtain ⟨hls, _⟩ := heapLength_of_slots heap src xs hsrc hxn
  have hwin := heapCopyReferences_window_run heap dest src xs ys hsrc hdest di si n
    hn0 hdi hde hsi hse
  rw [heapCheckedCopy_positive_eq _ _ _ _ _ _ hn]
  simp only [vector_bind_run, heapBounds_in heap dest ys hdest di hdi hdy,
    heapBounds_in heap src xs hsrc si hsi hsx, hld, hls, hcd, hcs,
    Bool.false_eq_true, ite_false, hwin, vector_pure_run]

theorem vcat_copy_loop {Tag α : Type} (heap : VectorHeap α) (arr : HeapArray Tag)
    (harr : arr.handle = heap.length) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (pre : List (Option α)) (total : Nat)
    (htotal : pre.length + (contents.map List.length).sum = total)
    (htb : total < 4611686018427387904) :
    (forIn arrays (JInt.wrap .i64 ((pre.length : Int) + 1)) (vcatCopyStep arr)).run
        (heap ++ [pre ++ List.replicate (total - pre.length) none]) =
      .ok (JInt.wrap .i64 ((total : Int) + 1), heap ++ [pre ++ contents.flatten]) := by
  induction arrays generalizing contents pre with
  | nil =>
    cases contents with
    | nil =>
      simp only [List.map_nil, List.sum_nil, Nat.add_zero] at htotal
      subst htotal
      simp only [List.forIn_nil, vector_pure_run, Nat.sub_self, List.replicate_zero,
        List.flatten_nil]
    | cons c cs => simp at hc
  | cons a as ih =>
    cases contents with
    | nil => simp at hc
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hc
      obtain ⟨ha, hcs⟩ := hc
      simp only [List.map_cons, List.sum_cons] at htotal
      have halt : a.handle < heap.length := (List.getElem?_eq_some_iff.mp ha).choose
      have hsrc : (heap ++ [pre ++ List.replicate (total - pre.length) none])[a.handle]? =
          some c := by rw [List.getElem?_append_left halt]; exact ha
      have hdst : (heap ++ [pre ++ List.replicate (total - pre.length) none])[arr.handle]? =
          some (pre ++ List.replicate (total - pre.length) none) := by rw [harr]; simp
      have hdlen : (pre ++ List.replicate (total - pre.length) (none : Option α)).length =
          total := by simp; omega
      have hct : c.length < 4611686018427387904 := by omega
      have hpt : pre.length + c.length ≤ total := by omega
      obtain ⟨hal, hav⟩ := heapLength_of_slots _ a.handle c hsrc hct
      obtain ⟨harl, harv⟩ := heapLength_of_slots _ arr.handle _ hdst (by
        rw [hdlen]; exact htb)
      rw [hdlen] at harl harv
      have hnd : (JInt.wrap .i64 ((pre.length : Int) + 1)).val = pre.length + 1 :=
        ival_wrap _ (by clear hav harv hal harl; omega)
      have hsum : (JInt.wrap .i64 ((pre.length : Int) + 1) + JInt.wrap .i64 (c.length : Int)).val =
          pre.length + 1 + c.length := by
        rw [ival_add (JInt.wrap .i64 ((pre.length : Int) + 1)) (JInt.wrap .i64 (c.length : Int))
          (by rw [hnd, hav]; clear hnd hav harv hal harl; omega), hnd, hav]
      have hlimit : (one + JInt.wrap .i64 (total : Int)).val = 1 + total := by
        rw [ival_add one (JInt.wrap .i64 (total : Int))
          (by rw [ival_one, harv]; clear hnd hav harv hsum hal harl; omega), ival_one, harv]
      have hcond : decide (JInt.wrap .i64 ((pre.length : Int) + 1) +
          JInt.wrap .i64 (c.length : Int) ≤ one + JInt.wrap .i64 (total : Int)) = true := by
        rw [decide_eq_true_eq, jle_iff, hsum, hlimit]
        clear hnd hav harv hsum hlimit hal harl
        omega
      have hnext : JInt.wrap .i64 ((pre.length : Int) + 1) + JInt.wrap .i64 (c.length : Int) =
          JInt.wrap .i64 (((pre ++ c).length : Int) + 1) := by
        apply Subtype.ext
        rw [hsum, ival_wrap (((pre ++ c).length : Int) + 1)
          (by simp; clear hnd hav harv hsum hlimit hcond hal harl; omega)]
        simp
        clear hnd hav harv hsum hlimit hcond hal harl
        omega
      have htotal' : (pre ++ c).length + (cs.map List.length).sum = total := by
        simp; clear hnd hav harv hsum hlimit hcond hal harl hnext; omega
      have hrest := ih cs hcs (pre ++ c) htotal'
      have hflat : pre ++ (c :: cs).flatten = (pre ++ c) ++ cs.flatten := by
        simp [List.append_assoc]
      by_cases hcz : c = []
      · subst hcz
        simp only [List.append_nil] at hnext hrest
        have hstep := vcatCopyStep_run arr a _ _ _ _ _ hal harl hcond
          (heapUnsafeCopy_zero_run _ _ _ _ _ _ (by rw [hav]; rfl))
        simp only [List.forIn_cons, vector_bind_run, hstep]
        rw [hnext, hrest, hflat, List.append_nil]
      · have hcp : 0 < c.length := List.length_pos_iff.mpr hcz
        have hcopy := heapUnsafeCopy_run _ arr a c _ hsrc hdst
          (JInt.wrap .i64 ((pre.length : Int) + 1)) one (JInt.wrap .i64 (c.length : Int))
          (by rw [hav]; exact_mod_cast hcp) (by rw [hnd]; clear hnd hav harv hsum hlimit; omega)
          (by rw [hnd, hav, hdlen]; clear hnd hav harv hsum hlimit; omega)
          (by rw [ival_one]; exact Int.le_refl 1)
          (by rw [ival_one, hav]; clear hnd hav harv hsum hlimit; omega)
        have hwin : (pre ++ List.replicate (total - pre.length) none).take
              ((JInt.wrap .i64 ((pre.length : Int) + 1)).val - 1).toNat ++
            (c.drop (one.val - 1).toNat).take (JInt.wrap .i64 (c.length : Int)).val.toNat ++
            (pre ++ List.replicate (total - pre.length) none).drop
              ((JInt.wrap .i64 ((pre.length : Int) + 1)).val - 1 +
                (JInt.wrap .i64 (c.length : Int)).val).toNat =
            (pre ++ c) ++ List.replicate (total - (pre ++ c).length) none := by
          rw [hnd, hav, ival_one]
          have h1 : ((pre.length : Int) + 1 - 1).toNat = pre.length := by
            clear hnd hav harv hsum hlimit hcopy; omega
          have h2 : ((pre.length : Int) + 1 - 1 + c.length).toNat = pre.length + c.length := by
            clear hnd hav harv hsum hlimit hcopy; omega
          rw [h1, h2, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero,
            Int.toNat_natCast, List.take_length, List.take_left' rfl, List.drop_append,
            List.drop_replicate]
          simp only [List.length_append, List.append_assoc, Nat.sub_sub]
          rw [List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append]
          congr 3
          clear hnd hav harv hsum hlimit hcopy hcond hnext
          omega
        rw [hwin] at hcopy
        have hset : (heap ++ [pre ++ List.replicate (total - pre.length) none]).set arr.handle
            ((pre ++ c) ++ List.replicate (total - (pre ++ c).length) none) =
            heap ++ [(pre ++ c) ++ List.replicate (total - (pre ++ c).length) none] := by
          rw [harr]; simp [List.set_append_right]
        rw [hset] at hcopy
        have hstep := vcatCopyStep_run arr a _ _ _ _ _ hal harl hcond hcopy
        simp only [List.forIn_cons, vector_bind_run, hstep]
        rw [hnext, hrest, hflat]
end HeapRanges
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section TypedCollect

attribute [local irreducible] JInt.wrap wrapInt

theorem heapRangeCopy_window_run {Tag α : Type} (heap : VectorHeap α) (x a : HeapArray Tag)
    (xs ys : List (Option α)) (hsrc : heap[a.handle]? = some xs) (hdest : heap[x.handle]? = some ys)
    (hxn : xs.length < 2 ^ 62) (hyn : ys.length < 2 ^ 62) (xi si n : I) (hn : 0 < n.val)
    (hdi : 1 ≤ xi.val) (hde : xi.val - 1 + n.val ≤ (ys.length : Int))
    (hsi : 1 ≤ si.val) (hse : si.val - 1 + n.val ≤ (xs.length : Int)) :
    (heapRangeCopy x xi a si n).run heap =
      .ok ((), heap.set x.handle (ys.take (xi.val - 1).toNat ++
        (xs.drop (si.val - 1).toNat).take n.val.toNat ++ ys.drop (xi.val - 1 + n.val).toNat)) := by
  simp only [heapRangeCopy, vector_bind_run,
    heapCheckedCopy_window_run heap x.handle a.handle xs ys hsrc hdest hxn hyn xi si n hn hdi hde
      hsi hse, vector_pure_run]
end TypedCollect
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A window copy reads the old source even when the address ranges overlap. -/
def copiedElements (old : Nat → Option α) (dest src count : Nat) : Nat → Option α :=
  fun address => if dest ≤ address ∧ address < dest + count
    then old (src + (address - dest)) else old address

/-- Heap addresses let distinct arrays share arbitrary overlapping storage. -/
abbrev CopyM (α : Type) := ExceptT Error (StateM (Nat → Option α))

def copyBounds (value : Z → Int) (a : Nat × Nat) (i : Z) : CopyM α Unit :=
  fun old => (if 1 ≤ value i ∧ value i ≤ (a.2 : Int)
    then .ok () else .error .bounds, old)

def copyReference (a : Nat × Nat) (i : I) : CopyM α Nat :=
  fun old => (.ok (a.1 + (i.val - 1).toNat), old)

def copyInt (value : Z → Int) (i : Z) : CopyM α I :=
  fun old => (if IntTy.i64.min ≤ value i ∧ value i ≤ IntTy.i64.max
    then .ok (JInt.wrap .i64 (value i)) else .error .inexact, old)

def copyLength (a : Nat × Nat) : CopyM α I :=
  fun old => (.ok (JInt.wrap .i64 a.2), old)

/-- Independent window semantics: validation precedes every write. -/
def checkedCopyResult (old : Nat → Option α) (dest src : Nat × Nat)
    (di si n : Int) : Except Error (Nat × Nat) × (Nat → Option α) :=
  if n = 0 then (.ok dest, old)
  else if n < 0 then
    (.error (.argument "Number of elements to copy must be non-negative."), old)
  else if 1 ≤ di ∧ di + n - 1 ≤ (dest.2 : Int) ∧
      1 ≤ si ∧ si + n - 1 ≤ (src.2 : Int) then
    (.ok dest, copiedElements old (dest.1 + (di - 1).toNat)
      (src.1 + (si - 1).toNat) n.toNat)
  else (.error .bounds, old)

/-- Core allocates a separate memory object; this operation has no source-array
parameter that could limit freshness to only one existing allocation. -/
def heapCopyAllocate (n : I) : VectorM α Nat :=
  if n.val < 0 then throw (.argument "invalid Memory dimensions")
  else heapAllocate n.val.toNat

/-- copy(::Array) with a shared heap of live memory objects. The memory copy
preserves unassigned slots, and the Core header constructor retains the type
and dimensions while referencing the newly allocated object. -/
abbrev heapFreshCopy {Tag α : Type} (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.ArrayCallees.copyArray (fun a => pure (a.handle, one))
    (fun a => pure (JInt.wrap .i64 (a.dimensions.prod : Int)))
    (fun _ n => heapCopyAllocate n) (fun handle => pure (handle, one))
    (heapCopyReferences (fun x => .ok x)) (fun a => pure a.dimensions)
    (fun ref dims => pure ⟨ref.1, src.elementType, dims, dims.map (fun n => (1, n))⟩) src
def heapColonLength {Tag α : Type} (a : HeapArray Tag) : VectorM α I :=
  pure (JInt.wrap .i64 (a.dimensions.prod : Int))

def heapColonSimilar {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (n : I) :
    VectorM α (HeapArray Tag) :=
  similar418 (fun n => heapAllocateIntDims layout a.elementType [n]) a n

/-- Colon indexing preserves the element type and uses the native vector allocator. -/
abbrev heapColonCopy {Tag α : Type} (layout : Tag → Option MemoryLayout) (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  getindexColon heapColonLength (heapColonSimilar layout) heapColonMemoryCopy src
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace IntegerValue

/-- `x * s` for an `Int` `s`: int.jl's promoted `*` for a BitInteger `x`, `Bool * Int` (int.jl's
`mulBool`), `BigInt` `*` otherwise. -/
def mulInt (ops : BigIntegerOps) (x : IntegerValue) (s : I) : IntegerValue :=
  match x with
  | .bit _ y => .bit _ (JuliaLean.base.int.binop JuliaLean.base.int.mul y s)
  | .bool b => .bit .i64 (JuliaLean.base.int.mulBool b s)
  | .big v => .big (ops.mul v s.val)
end IntegerValue
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `firstindex(a::AbstractArray) = first(eachindex(IndexLinear(), a))` (abstractarray.jl:452)
with range.jl's `first(::OneTo)`. -/
def heapFirstindex {Tag α : Type} (a : HeapArray Tag) : VectorM α I := do
  pure (JuliaLean.base.range.first_OneTo (← heapLinearIndices a))

/-- The documented result of a window copy into `xs` from `ys`: `n` slots of `ys` from `si` written
over `n` slots of `xs` from `di`. -/
def copiedWindow (xs ys : List (Option α)) (di si n : Int) : List (Option α) :=
  xs.take (di - 1).toNat ++ (ys.drop (si - 1).toNat).take n.toNat ++ xs.drop (di - 1 + n).toNat

/-- `copyto!(dest, doffs, src, soffs, n)` (array.jl:288-296 through `_copyto_impl!`; docstring at
array.jl:282-287: "Copy `n` elements from collection `src` starting at the linear index `soffs`,
to array `dest` starting at the index `doffs`. Return `dest`.") for the four Array/Memory method
pairs, operands of every shape, offsets and count of any `Integer` types, and a source that may
share memory with the destination: `n = 0` returns `dest` and changes nothing; a negative `n`
raises `ArgumentError`; a window outside either operand raises `BoundsError`; a failed element
copy raises its error; no error changes the heap. Otherwise `dest` is returned and its memory
holds the copied old source window in place of its own, every other heap object unchanged. -/
def CheckedCopySpec : Prop :=
  ∀ (α Tag : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (convert : Option α → Except Error (Option α)) (heap : VectorHeap α)
    (dest src : HeapArray Tag) (xs ys : List (Option α)) (di si n : IntegerValue),
    heap[dest.handle]? = some xs → heap[src.handle]? = some ys →
    xs.length < 2 ^ 63 → ys.length < 2 ^ 63 →
    let inside := 1 ≤ di.val ∧ di.val + n.val - 1 ≤ xs.length ∧ 1 ≤ si.val ∧
      si.val + n.val - 1 ≤ ys.length
    let window := (ys.drop (si.val - 1).toNat).take n.val.toNat
    ∀ operation ∈ [copyto288 (heapCopyImpl α Tag ops convert),
        copyto290 (heapCopyImpl α Tag ops convert), copyto292 (heapCopyImpl α Tag ops convert),
        copyto296 (heapCopyImpl α Tag ops convert)],
      let run := (operation dest di src si n).run heap
      (n.val = 0 → run = .ok (dest, heap)) ∧
      (n.val < 0 → run = .error (.argument "Number of elements to copy must be non-negative.")) ∧
      (0 < n.val → ¬ inside → run = .error .bounds) ∧
      (0 < n.val → inside → ∀ e, window.mapM convert = .error e → run = .error e) ∧
      (0 < n.val → inside → ∀ values, window.mapM convert = .ok values →
        run = .ok (dest, heap.set dest.handle
          (xs.take (di.val - 1).toNat ++ values ++ xs.drop (di.val - 1 + n.val).toNat)))

def WholeCopySpec : Prop :=
  ∀ (α Tag : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (convert : Option α → Except Error (Option α)) (heap : VectorHeap α)
    (dest src : HeapArray Tag) (xs ys : List (Option α)),
    heap[dest.handle]? = some xs → heap[src.handle]? = some ys →
    xs.length < 2 ^ 63 → ys.length < 2 ^ 63 →
    let copy := fun d i s j n => copyto288 (heapCopyImpl α Tag ops convert) d (.ofInt i) s (.ofInt j)
      (.ofInt n)
    ∀ operation ∈ [copyto2arg heapFirstindex heapFirstindex heapArrayLength copy,
        copyto325 heapFirstindex heapFirstindex heapArrayLength copy,
        copyto326 heapFirstindex heapFirstindex heapArrayLength copy,
        copyto327 heapFirstindex heapFirstindex heapArrayLength copy,
        copyto330 heapFirstindex heapFirstindex heapArrayLength copy,
        copyto331 heapFirstindex heapFirstindex heapArrayLength copy,
        copyto332 heapFirstindex heapFirstindex heapArrayLength copy],
      (ys.length ≤ xs.length → ∀ values, ys.mapM convert = .ok values →
        (operation dest src).run heap =
          .ok (dest, heap.set dest.handle (values ++ xs.drop ys.length))) ∧
      (ys.length ≤ xs.length → 0 < ys.length → ∀ e, ys.mapM convert = .error e →
        (operation dest src).run heap = .error e) ∧
      (xs.length < ys.length → (operation dest src).run heap = .error .bounds)

def CopyArraySpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (a : HeapArray Tag) (xs : List (Option α)),
    heap[a.handle]? = some xs → xs.length < 2 ^ 63 →
    (JuliaLean.base.abstractarray.ArrayCallees.copyArray (m := VectorM α) (fun a : HeapArray Tag => pure ((a.handle, one) : Nat × I))
      heapArrayLength (fun _ n => heapAllocate n.val.toNat) (fun mem => pure (mem, one))
      (fun d s n => heapCopyReferences Except.ok d s n) (fun a => pure a.dimensions)
      (fun ref dims => pure { a with handle := ref.1, dimensions := dims }) a).run heap =
      .ok ({ a with handle := heap.length }, heap ++ [xs])

def UnsafeArrayCopySpec : Prop :=
  ∀ (Tag α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (heap : VectorHeap α) (dest src : HeapArray Tag) (xs ys : List (Option α))
    (di si n : IntegerValue),
    heap[dest.handle]? = some xs → heap[src.handle]? = some ys →
    let run := (unsafeCopyArray (fun n : IntegerValue => n.val == 0)
      (fun (a : HeapArray Tag) (i : IntegerValue) => do
        heapReference (α := α) a.handle (← StateT.lift (i.toInt ops)))
      (fun (a : HeapArray Tag) (i : IntegerValue) => do
        heapReference (α := α) a.handle (← StateT.lift (i.toInt ops)))
      (fun d s (n : IntegerValue) => do heapCopyReferences Except.ok d s (← StateT.lift (n.toInt ops)))
      dest di src si n).run heap
    (n.val = 0 → run = .ok (dest, heap)) ∧
    (0 < n.val → 1 ≤ di.val → di.val + n.val - 1 ≤ xs.length → 1 ≤ si.val →
      si.val + n.val - 1 ≤ ys.length →
      run = .ok (dest, heap.set dest.handle (copiedWindow xs ys di.val si.val n.val)))

/-- `unsafe_copyto!(dest::Ptr{T}, src::Ptr{T}, n)` (array.jl:259; docstring at array.jl:247-258:
"Copy `n` elements from a source pointer to a destination, with no checking.") for a count of any
`Integer` type and an element stride `aligned_sizeof(T)` (a runtime layout query with no Lean
model): `n * aligned_sizeof(T)` is the promoted `*` (`IntegerValue.mulInt`), and `memmove` is
cmem.jl's wrapper (`ccall` with a `Csize_t` argument, `csizeFromInt`) over cmem.lean's C library.
For a byte count `n * stride` that is an `Int`: when it is negative the `Csize_t` conversion throws
`InexactError`; otherwise, for valid source and destination ranges of that many bytes, `dest` is
returned and the destination bytes become the old source bytes, no other byte changing
(`copyEffect`). -/
def PointerCopySpec : Prop :=
  ∀ (ops : BigIntegerOps), ops.Lawful →
  ∀ (stride : I) (n : IntegerValue) (heap : JuliaLean.base.pointer.ByteHeap) (dest src : Nat),
    0 < stride.val →
    IntTy.i64.min ≤ n.val * stride.val → n.val * stride.val ≤ IntTy.i64.max →
    let run := (unsafeCopyPtr stride (fun (n : IntegerValue) (s : I) => n.mulInt ops s)
      (fun d s (b : IntegerValue) => do
        let _ ← byteCall (fun heap => JuliaLean.base.cmem.memmove cLibrary
          (fun b : IntegerValue => JuliaLean.base.cmem.csizeFromInt b.val) heap d s b)
        pure ())
      (bytePtr dest) (bytePtr src) n).run heap
    (n.val < 0 → run = .error .inexact) ∧
    (0 ≤ n.val →
      let size : JInt .u64 := JInt.wrap .u64 (n.val * stride.val)
      JuliaLean.base.cmem.validRange heap (bytePtr dest) size →
      JuliaLean.base.cmem.validRange heap (bytePtr src) size →
      ∃ after, run = .ok (bytePtr dest, after) ∧
        JuliaLean.base.cmem.copyEffect heap after (bytePtr dest) (bytePtr src) size)
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6b
open JuliaLean JuliaLean.base.array

def multiplyInteger (ops : OpaqueIntegerOps) (n : IntegerArgument) (stride : I) :
    IntegerArgument :=
  match n with
  | .bit _ x => .bit _ (JuliaLean.base.int.binop JuliaLean.base.int.mul x stride)
  | .boolean b => .bit .i64 (JuliaLean.base.int.mulBool b stride)
  | .opaque v => .opaque (ops.multiply v stride.val)

/-- Byte copying uses the promoted, wrapping Integer product passed to memmove. -/
def PointerCopySpec : Prop :=
  ∀ (ops : OpaqueIntegerOps),
  ∀ (stride : I) (n : IntegerArgument) (heap : JuliaLean.base.pointer.ByteHeap)
    (dest src : Nat),
    0 ≤ stride.val →
    let bytes := (multiplyInteger ops n stride).value
    let run := (unsafeCopyPtr stride (multiplyInteger ops)
      (fun d s (b : IntegerArgument) => do
        let _ ← byteCall (fun heap => JuliaLean.base.cmem.memmove
          JuliaLean.base.cmem.StandardC.standardCMemoryOps
          (fun b : IntegerArgument => JuliaLean.base.cmem.csizeFromInt b.value)
          heap d s b)
        pure ())
      (bytePointer dest) (bytePointer src) n).run heap
    ((bytes < 0 ∨ IntTy.u64.max < bytes) → run = .error .inexact) ∧
    (0 ≤ bytes → bytes ≤ IntTy.u64.max →
      let size : JInt .u64 := JInt.wrap .u64 bytes
      JuliaLean.base.cmem.validRange heap (bytePointer dest) size →
      JuliaLean.base.cmem.validRange heap (bytePointer src) size →
      ∃ after, run = .ok (bytePointer dest, after) ∧
        JuliaLean.base.cmem.copyEffect heap after (bytePointer dest) (bytePointer src) size)
end round6b
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round10

open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
open JuliaLean.Proofs.base.array.round6b

/-- `unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)` (base/array.jl:276; docstring at
base/array.jl:266-275) accepts Integer offsets and a count without validating the requested window.
Array length values are Int-representable. A nonzero call that fails one of the source `Int`
conversions throws an error before copying; when the count is positive, all conversions succeed,
and both windows are in bounds, the destination receives the old source window and every other heap
object stays unchanged. -/
def UnsafeArrayCopyWindowSpec : Prop :=
  ∀ (Tag α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (heap : VectorHeap α) (dest src : HeapArray Tag) (xs ys : List (Option α))
    (di si n : IntegerValue),
    heap[dest.handle]? = some xs → heap[src.handle]? = some ys →
    xs.length ≤ maxIntVal → ys.length ≤ maxIntVal →
    let run := (unsafeCopyArray (fun n : IntegerValue => n.val == 0)
      (fun (a : HeapArray Tag) (i : IntegerValue) => do
        heapReference (α := α) a.handle (← StateT.lift (i.toInt ops)))
      (fun (a : HeapArray Tag) (i : IntegerValue) => do
        heapReference (α := α) a.handle (← StateT.lift (i.toInt ops)))
      (fun d s (n : IntegerValue) => do
        heapCopyReferences Except.ok d s (← StateT.lift (n.toInt ops)))
      dest di src si n).run heap
    (n.val = 0 → run = .ok (dest, heap)) ∧
    (n.val ≠ 0 → (¬ di.fits ∨ ¬ si.fits ∨ ¬ n.fits) → ∃ error, run = .error error) ∧
    (0 < n.val → di.fits → si.fits → n.fits →
      1 ≤ di.val → di.val + n.val - 1 ≤ xs.length → 1 ≤ si.val →
      si.val + n.val - 1 ≤ ys.length →
      run = .ok (dest, heap.set dest.handle (copiedWindow xs ys di.val si.val n.val)))

theorem unsafeArrayCopyWindowSpec_proven : UnsafeArrayCopyWindowSpec := by
  intro Tag α ops hops heap dest src xs ys di si n hdest hsrc hlenDest hlenSrc
  dsimp only
  have htoIntOk : ∀ x : IntegerValue, x.fits →
      x.toInt ops = .ok (JInt.wrap .i64 x.val) := by
    intro x hx
    have hfits : IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max := by
      simpa [round4.IntegerValue.fits] using hx
    rw [JuliaLean.Proofs.base.array.opusGrowth.integerValue_toInt hops x]
    simp [hfits]
  have htoIntError : ∀ x : IntegerValue, ¬ x.fits →
      x.toInt ops = .error .inexact := by
    intro x hx
    rw [JuliaLean.Proofs.base.array.opusGrowth.integerValue_toInt hops x]
    have hnot : ¬ (IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max) := by
      simpa [round4.IntegerValue.fits] using hx
    simp [hnot]
  have hdiVal : di.fits → (JInt.wrap .i64 di.val).val = di.val := by
    intro hf
    change wrapInt .i64 di.val = di.val
    exact JuliaLean.wrapInt_of_inRange .i64 di.val (by simpa [round4.IntegerValue.fits] using hf)
  have hsiVal : si.fits → (JInt.wrap .i64 si.val).val = si.val := by
    intro hf
    change wrapInt .i64 si.val = si.val
    exact JuliaLean.wrapInt_of_inRange .i64 si.val (by simpa [round4.IntegerValue.fits] using hf)
  have hnVal : n.fits → (JInt.wrap .i64 n.val).val = n.val := by
    intro hf
    change wrapInt .i64 n.val = n.val
    exact JuliaLean.wrapInt_of_inRange .i64 n.val (by simpa [round4.IntegerValue.fits] using hf)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    simp [unsafeCopyArray, hz] <;> rfl
  · intro hn hbad
    have hzero : (n.val == 0) = false := by simp [hn]
    by_cases hdi : di.fits
    · have hdiOk := htoIntOk di hdi
      by_cases hsi : si.fits
      · have hsiOk := htoIntOk si hsi
        have hnBad : ¬ n.fits := by
          intro hnf
          rcases hbad with h | h | h
          · exact h hdi
          · exact h hsi
          · exact h hnf
        refine ⟨.inexact, ?_⟩
        simp [unsafeCopyArray, hzero, hdiOk, hsiOk, htoIntError n hnBad,
          heapReference, vector_bind_run, vector_lift_run, vector_pure_run] <;>
          simp [Bind.bind, Except.bind]
      · refine ⟨.inexact, ?_⟩
        simp [unsafeCopyArray, hzero, hdiOk, htoIntError si hsi,
          heapReference, vector_bind_run, vector_lift_run, vector_pure_run] <;>
          simp [Bind.bind, Except.bind]
    · refine ⟨.inexact, ?_⟩
      simp [unsafeCopyArray, hzero, htoIntError di hdi,
        heapReference, vector_bind_run, vector_lift_run, vector_pure_run] <;>
        simp [Bind.bind, Except.bind]
  · intro hpos hdi hsi hn hdi1 hdiEnd hsi1 hsiEnd
    have hdiInt := hdiVal hdi
    have hsiInt := hsiVal hsi
    have hnInt := hnVal hn
    have hnonzero : n.val ≠ 0 := by omega
    have hzero : (n.val == 0) = false := by simp [hnonzero]
    have hcopy :
        (heapCopyReferences (fun x => Except.ok (ε := Error) x)
          (dest.handle, JInt.wrap .i64 di.val) (src.handle, JInt.wrap .i64 si.val)
          (JInt.wrap .i64 n.val)).run heap =
        .ok ((), heap.set dest.handle (copiedWindow xs ys di.val si.val n.val)) := by
      rw [heapCopyReferences_window_run heap dest.handle src.handle ys xs hsrc hdest
        (JInt.wrap .i64 di.val) (JInt.wrap .i64 si.val) (JInt.wrap .i64 n.val)
        (by rw [hnInt]; omega)
        (by rw [hdiInt]; omega)
        (by rw [hdiInt, hnInt]; omega)
        (by rw [hsiInt]; omega)
        (by rw [hsiInt, hnInt]; omega)]
      simp [copiedWindow, hdiInt, hsiInt, hnInt]
    simp [unsafeCopyArray, hzero, htoIntOk di hdi, htoIntOk si hsi,
      htoIntOk n hn, heapReference, vector_bind_run, vector_lift_run, vector_pure_run] <;>
      simp [Bind.bind, Except.bind, hcopy, Functor.map, Except.map]
end JuliaLean.Proofs.base.array.round10
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round12

open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
open JuliaLean.Proofs.base.array.round6b

/-- `unsafe_copyto!(dest::Ptr{T}, src::Ptr{T}, n)` (base/array.jl:259; docstring at
base/array.jl:247-258) multiplies `n` by `aligned_sizeof(T)` (base/runtime_internals.jl:667-688).
BitInteger and Bool products use the installed wrapping integer operations (base/int.jl:89,
1092-1100). For an unmodelled Integer type, multiplication can throw or return a native BitInteger
or opaque Integer; no law is imposed on that user-defined operation. Native results use the
installed `cmem` conversion to `Csize_t`, while opaque results use the type's conversion operation
(base/cmem.jl:26-29). -/
inductive PointerProductValue where
  | native {t : IntTy} (value : JInt t)
  | opaque (value : Int)

def pointerProductArgument : PointerProductValue → IntegerArgument
  | .native value => .bit _ value
  | .opaque value => .opaque value

def pointerIntegerProduct
    (multiplyOpaque : Int → Int → Except Error PointerProductValue)
    (n : IntegerArgument) (stride : I) : Except Error PointerProductValue :=
  match n with
  | .bit _ value => .ok (.native (JuliaLean.base.int.binop JuliaLean.base.int.mul value stride))
  | .boolean value => .ok (.native (JuliaLean.base.int.mulBool value stride))
  | .opaque value => multiplyOpaque value stride.val

def pointerCopyCSize (opaqueConvert : Int → Jl JuliaLean.base.cmem.CSizeT)
    (bytes : IntegerArgument) : Jl JuliaLean.base.cmem.CSizeT :=
  match bytes with
  | .bit _ value => JuliaLean.base.cmem.csizeFromInt value.val
  | .boolean value => JuliaLean.base.cmem.csizeFromInt (if value then 1 else 0)
  | .opaque value => opaqueConvert value

def pointerCopyAfterProduct (stride : I) (n bytes : IntegerArgument)
    (opaqueConvert : Int → Jl JuliaLean.base.cmem.CSizeT)
    (heap : JuliaLean.base.pointer.ByteHeap) (dest src : Nat) :
    Except Error (JuliaLean.base.pointer.Ptr Unit × JuliaLean.base.pointer.ByteHeap) :=
  (unsafeCopyPtr stride (fun _ _ => bytes)
    (fun d s (value : IntegerArgument) => do
      let _ ← JuliaLean.Proofs.base.array.round6b.byteCall
        (fun heap => JuliaLean.base.cmem.memmove
          JuliaLean.base.cmem.StandardC.standardCMemoryOps
          (pointerCopyCSize opaqueConvert) heap d s value)
      pure ())
    (bytePointer dest) (bytePointer src) n).run heap

def PointerCopySpec : Prop :=
  ∀ (multiplyOpaque : Int → Int → Except Error PointerProductValue)
    (opaqueConvert : Int → Jl JuliaLean.base.cmem.CSizeT)
    (stride : I) (n : IntegerArgument)
    (heap : JuliaLean.base.pointer.ByteHeap) (dest src : Nat),
    let product := pointerIntegerProduct multiplyOpaque n stride
    let run := match product with
      | .error error => Except.error error
      | .ok bytes => pointerCopyAfterProduct stride n (pointerProductArgument bytes)
          opaqueConvert heap dest src
    match product with
    | .error _ => ∃ error, run = .error error
    | .ok (.native value) =>
        match pointerCopyCSize opaqueConvert (.bit _ value) with
        | .error _ => ∃ error, run = .error error
        | .ok size =>
            JuliaLean.base.cmem.validRange heap (bytePointer dest) size →
            JuliaLean.base.cmem.validRange heap (bytePointer src) size →
            ∃ after, run = .ok (bytePointer dest, after) ∧
              JuliaLean.base.cmem.copyEffect heap after (bytePointer dest) (bytePointer src) size
    | .ok (.opaque value) =>
        match pointerCopyCSize opaqueConvert (.opaque value) with
        | .error _ => ∃ error, run = .error error
        | .ok size =>
            JuliaLean.base.cmem.validRange heap (bytePointer dest) size →
            JuliaLean.base.cmem.validRange heap (bytePointer src) size →
            ∃ after, run = .ok (bytePointer dest, after) ∧
              JuliaLean.base.cmem.copyEffect heap after (bytePointer dest) (bytePointer src) size
end JuliaLean.Proofs.base.array.round12
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6e
open JuliaLean
set_option maxHeartbeats 1000000

theorem copy_bind_run {β γ : Type} (x : M ε σ β) (f : β → M ε σ γ) (w : World σ) :
    (x >>= f).run w = match x.run w with
      | (.ok v, after) => (f v).run after
      | (.error e, after) => (.error e, after) := by
  change (x >>= f).run.run w = match x.run.run w with
    | (.ok v, after) => (f v).run.run after
    | (.error e, after) => (.error e, after)
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases h : x.run.run w with ⟨result, after⟩
  cases result <;> rfl

theorem copy_pure_run {β : Type} (x : β) (w : World σ) :
    (pure x : M ε σ β).run w = (.ok x, w) := rfl

 theorem copyArray_allocation_error (runtime : Runtime ε σ T)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world after : World σ)
    (array : ArrayObject T) (failure : Sum JuliaLean.base.array.Error ε)
    (h : (runtime.allocate array.ref.mem (length array)).run world = (.error failure, after)) :
    (copyArray runtime calls unreached array).run world = (.error failure, after) := by
  simp only [copyArray, JuliaLean.base.abstractarray.ArrayCallees.copyArray, copy_bind_run, copy_pure_run, h]

 theorem copyArray_allocated_run (runtime : Runtime ε σ T)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world after : World σ)
    (array : ArrayObject T) (fresh : Memory T)
    (h : (runtime.allocate array.ref.mem (length array)).run world = (.ok fresh, after)) :
    (copyArray runtime calls unreached array).run world =
    (do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
        (copyOps runtime calls array.ref.mem.layoutBytes unreached) false (memoryref fresh)
        array.ref (length array)
      newArray (memoryref fresh) (size array) : M ε σ (ArrayObject T)).run after := by
  simp only [copyArray, JuliaLean.base.abstractarray.ArrayCallees.copyArray, copy_bind_run, copy_pure_run, h]
  cases hcopy : (JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
    (copyOps runtime calls array.ref.mem.layoutBytes unreached) false (memoryref fresh)
    array.ref (length array)).run after with
  | mk result final => cases result <;> rfl

theorem newArray_run (reference : Ref T) (dimensions : List I) (world : World σ) :
    (newArray reference dimensions : M ε σ (ArrayObject T)).run world =
      (.ok ⟨world.nextArray,reference,dimensions⟩,{world with nextArray := world.nextArray+1}) := rfl

theorem copyArray_success_run (runtime : Runtime ε σ T)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world allocated copied : World σ)
    (array : ArrayObject T) (fresh : Memory T) (result : Ref T)
    (ha : (runtime.allocate array.ref.mem (length array)).run world = (.ok fresh,allocated))
    (hc : (JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
      (copyOps runtime calls array.ref.mem.layoutBytes unreached) false (memoryref fresh)
      array.ref (length array)).run allocated = (.ok result,copied)) :
    (copyArray runtime calls unreached array).run world =
      (.ok ⟨copied.nextArray,memoryref fresh,size array⟩,
        {copied with nextArray := copied.nextArray+1}) := by
  rw [copyArray_allocated_run runtime calls unreached world allocated array fresh ha]
  simp only [copy_bind_run,hc,newArray_run]
end round6e
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6e
open JuliaLean
set_option maxHeartbeats 1000000

open JuliaLean.Proofs.base.int

theorem copy_convert_same (n : I) : JuliaLean.base.int.convert .i64 n = .ok n := by
  simp only [JuliaLean.base.int.convert,JInt.convert,n.property,and_self,dite_true]

theorem copy_ref_zero_run (runtime : Runtime ε σ T)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world : World σ) (dest src : Ref T)
    (n : I) (hn : n.val = 0) :
    (JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
      (copyOps runtime calls src.mem.layoutBytes unreached) false dest src n).run world =
      (.ok dest,world) := by
  simp only [JuliaLean.base.genericmemory.unsafeCopytoRefs,copyOps,eq_int_eq,
    show (JInt.wrap .i64 0).val = 0 from rfl,hn,decide_true,ite_true,copy_pure_run]

theorem copy_ref_nonbits_run (runtime : Runtime ε σ T)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world after : World σ) (dest src : Ref T)
    (n : I) (hn : n.val ≠ 0) (hb : runtime.isBits = false)
    (hc : (runtime.ccallCopy dest.mem dest.ptr_or_offset src.mem src.ptr_or_offset n).run world =
      (.ok (),after)) :
    (JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
      (copyOps runtime calls src.mem.layoutBytes unreached) false dest src n).run world =
      (.ok dest,after) := by
  simp only [JuliaLean.base.genericmemory.unsafeCopytoRefs,copyOps,eq_int_eq,
    show (JInt.wrap .i64 0).val = 0 from rfl,hn,decide_false,Bool.false_eq_true,ite_false,
    hb,copy_bind_run,copy_convert_same,copy_pure_run,hc]

theorem copy_ref_bits_run (runtime : Runtime ε σ T) (law : runtime.Law)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world after : World σ) (dest src : Ref T)
    (n : I) (hn : n.val ≠ 0) (hb : runtime.isBits = true)
    (hc : (moveBytes (ε := ε) calls (pointer dest) (pointer src)
      (JuliaLean.base.int.binop JuliaLean.base.int.mul src.mem.layoutBytes n)).run world =
      (.ok (),after)) :
    (JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
      (copyOps runtime calls src.mem.layoutBytes unreached) false dest src n).run world =
      (.ok dest,after) := by
  simp only [JuliaLean.base.genericmemory.unsafeCopytoRefs,copyOps,eq_int_eq,
    show (JInt.wrap .i64 0).val = 0 from rfl,hn,decide_false,Bool.false_eq_true,ite_false,
    hb,ite_true,copy_bind_run,copy_pure_run,hc,law.2.1]
  erw [copy_pure_run]
  dsimp only
  erw [hc]
end round6e
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6e
open JuliaLean
set_option maxHeartbeats 1000000

open JuliaLean.Proofs.base.int


open JuliaLean JuliaLean.Proofs.base.int
open JuliaLean.base.pointer
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

 theorem copy_u_zero_mul (x : U) : JInt.wrap .u64 0 * x = JInt.wrap .u64 0 := by
  apply Subtype.ext
  change wrapInt .u64 (0 * x.val) = wrapInt .u64 0
  rw [Int.zero_mul]

 theorem copy_u_add_zero (x : U) : x + JInt.wrap .u64 0 = x := by
  apply Subtype.ext
  change wrapInt .u64 (x.val + 0) = x.val
  rw [Int.add_zero,wrapInt_val]

 theorem copy_pointer_memoryref (memory : Memory T) : pointer (memoryref memory) = memory.ptr := by
  by_cases hu : memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0
  · have hb : (memory.arrayElement == 2 || memory.layoutBytes.val == 0) = true := by
      simpa only [Bool.or_eq_true,beq_iff_eq] using hu
    simp only [pointer,memoryref,if_pos hu,unsafeConvertMemoryRefCvoid,hb,ite_true,
      unsafeConvertMemoryCvoid,copy_u_zero_mul,copy_u_add_zero]
  · have hb : (memory.arrayElement == 2 || memory.layoutBytes.val == 0) = false := by
      simp only [Bool.or_eq_false_iff,beq_eq_false_iff_ne]
      exact ⟨fun h => hu (Or.inl h),fun h => hu (Or.inr h)⟩
    simp only [pointer,memoryref,if_neg hu,unsafeConvertMemoryRefCvoid,hb,
      Bool.false_eq_true,ite_false]

 theorem copy_payload_memoryref (memory : Memory T) (byte : Nat) :
    payloadAddress (memoryref memory) byte =
      addressMod (memory.ptr.address.val.toNat + byte) := by
  rw [payloadAddress,copy_pointer_memoryref]

 theorem copy_tag_memoryref (memory : Memory T) (index : Nat)
    (hu : memory.arrayElement = 2) :
    tagAddress (memoryref memory) index =
      addressMod (memory.ptr.address.val.toNat +
        memory.capacity * memory.layoutBytes.val.toNat + index) := by
  simp only [tagAddress,memoryref,if_pos (Or.inl hu),show (JInt.wrap .u64 0).val = 0 from rfl,
    Int.toNat_zero,Nat.add_zero]

 theorem copy_memoryRegion_fresh (memory : Memory T) (heap : ByteHeap)
    (hp : ∀ byte, byte < memory.capacity * memory.layoutBytes.val.toNat →
      heap.validByte (payloadAddress (memoryref memory) byte) = false)
    (ht : memory.arrayElement = 2 → ∀ index, index < memory.capacity →
      heap.validByte (tagAddress (memoryref memory) index) = false) :
    ∀ address, memoryRegion memory address → heap.validByte address = false := by
  intro address hreg
  obtain ⟨offset,hoff,heq⟩ := hreg
  subst address
  by_cases hb : offset < memory.capacity * memory.layoutBytes.val.toNat
  · simpa only [copy_payload_memoryref] using hp offset hb
  · have hu : memory.arrayElement = 2 := by
      by_cases hu : memory.arrayElement = 2
      · exact hu
      · rw [if_neg hu] at hoff
        omega
    have hi : offset - memory.capacity * memory.layoutBytes.val.toNat < memory.capacity := by
      rw [if_pos hu] at hoff
      omega
    have htag := ht hu (offset-memory.capacity*memory.layoutBytes.val.toNat) hi
    rw [copy_tag_memoryref memory _ hu] at htag
    simpa only [Nat.add_assoc,Nat.add_sub_of_le (Nat.le_of_not_gt hb)] using htag

 theorem copy_memoryRegion_valid (memory : Memory T) (heap : ByteHeap)
    (h : validMemory heap memory) :
    ∀ address, memoryRegion memory address → heap.validByte address = true := by
  intro address hreg
  obtain ⟨offset,hoff,heq⟩ := hreg
  subst address
  by_cases hb : offset < memory.capacity * memory.layoutBytes.val.toNat
  · exact h.2.2.2.2.1 offset hb
  · have hu : memory.arrayElement = 2 := by
      by_cases hu : memory.arrayElement = 2
      · exact hu
      · rw [if_neg hu] at hoff
        omega
    have hi : offset - memory.capacity * memory.layoutBytes.val.toNat < memory.capacity := by
      rw [if_pos hu] at hoff
      omega
    have htag := h.2.2.2.2.2 hu (offset-memory.capacity*memory.layoutBytes.val.toNat) hi
    simpa only [Nat.add_assoc,Nat.add_sub_of_le (Nat.le_of_not_gt hb)] using htag

 theorem copy_separate_fresh (dest src : Memory T) (heap : ByteHeap)
    (hsrc : validMemory heap src)
    (hp : ∀ byte, byte < dest.capacity * dest.layoutBytes.val.toNat →
      heap.validByte (payloadAddress (memoryref dest) byte) = false)
    (ht : dest.arrayElement = 2 → ∀ index, index < dest.capacity →
      heap.validByte (tagAddress (memoryref dest) index) = false) : separateMemory dest src := by
  intro address hd hs
  have hf := copy_memoryRegion_fresh dest heap hp ht address hd
  have hv := copy_memoryRegion_valid src heap hsrc address hs
  rw [hv] at hf
  contradiction

theorem copy_u_mul_zero (x : U) : x * JInt.wrap .u64 0 = JInt.wrap .u64 0 := by
  apply Subtype.ext
  change wrapInt .u64 (x.val * 0) = wrapInt .u64 0
  rw [Int.mul_zero]

theorem copy_u_wrap_nat (n : Nat) (hn : n < 2 ^ 64) :
    (JInt.wrap .u64 (n : Int)).val = n := by
  change wrapInt .u64 (n : Int) = n
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ 18446744073709551615
  omega

theorem copy_u_wrap_mul (x y : Int) :
    JInt.wrap .u64 x * JInt.wrap .u64 y = JInt.wrap .u64 (x*y) := by
  apply Subtype.ext
  change wrapInt .u64 (wrapInt .u64 x * wrapInt .u64 y) = wrapInt .u64 (x*y)
  rw [wrapInt_mul_left,wrapInt_mul_right]

theorem copy_pointer_offset (heap : ByteHeap) (memory : Memory T) (k n : Nat)
    (hm : validMemory heap memory) (hkn : k + n ≤ memory.capacity) (hn : 0 < n) :
    (pointer (offsetRef memory k)).address.val.toNat =
      memory.ptr.address.val.toNat + k * memory.layoutBytes.val.toNat := by
  have hb : 0 ≤ memory.ptr.address.val ∧ memory.ptr.address.val < 18446744073709551616 := by
    have hp := memory.ptr.address.property
    change 0 ≤ memory.ptr.address.val ∧ memory.ptr.address.val ≤ 18446744073709551615 at hp
    omega
  have hw := hm.1
  by_cases hz : memory.layoutBytes.val = 0
  · have hc : memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0 := Or.inr hz
    have hbool : (memory.arrayElement == 2 || memory.layoutBytes.val == 0) = true := by
      simp only [hz,beq_self_eq_true,Bool.or_true]
    simp only [pointer,offsetRef,if_pos hc,unsafeConvertMemoryRefCvoid,hbool,ite_true,
      int64ToUInt64,hz,copy_u_mul_zero,unsafeConvertMemoryCvoid,copy_u_add_zero,
      Int.toNat_zero,Nat.mul_zero,Nat.add_zero,beq_self_eq_true,Bool.or_true,
      or_true,ite_true]
  · have hwidth : 0 < memory.layoutBytes.val.toNat := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right (show k < memory.capacity by omega) hwidth
    have hend := hm.2.2.2.1
    have hstart : memory.ptr.address.val.toNat + k * memory.layoutBytes.val.toNat < 2 ^ 64 := by omega
    have hmul64 : k * memory.layoutBytes.val.toNat < 2 ^ 64 := by omega
    have hcast : ((k * memory.layoutBytes.val.toNat : Nat) : Int) =
        (k : Int) * memory.layoutBytes.val := by
      rw [Int.natCast_mul,Int.toNat_of_nonneg hw]
    have hmv : (JInt.wrap .u64 ((k : Int) * memory.layoutBytes.val)).val =
        ((k * memory.layoutBytes.val.toNat : Nat) : Int) := by
      rw [←hcast]
      exact copy_u_wrap_nat _ hmul64
    have hs : ((memory.ptr.address.val.toNat + k * memory.layoutBytes.val.toNat : Nat) : Int) =
        memory.ptr.address.val + ((k * memory.layoutBytes.val.toNat : Nat) : Int) := by
      rw [Int.natCast_add,Int.toNat_of_nonneg hb.1]
    have ha : (memory.ptr.address + JInt.wrap .u64 ((k : Int)*memory.layoutBytes.val)).val =
        ((memory.ptr.address.val.toNat + k * memory.layoutBytes.val.toNat : Nat) : Int) := by
      change wrapInt .u64 (memory.ptr.address.val +
        (JInt.wrap .u64 ((k : Int)*memory.layoutBytes.val)).val) = _
      rw [hmv,←hs]
      exact copy_u_wrap_nat _ hstart
    by_cases hu : memory.arrayElement = 2
    · have hc : memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0 := Or.inl hu
      have hbool : (memory.arrayElement == 2 || memory.layoutBytes.val == 0) = true := by
        simp only [hu,beq_self_eq_true,Bool.true_or]
      simp only [pointer,offsetRef,if_pos hc,unsafeConvertMemoryRefCvoid,hbool,ite_true,
        int64ToUInt64,unsafeConvertMemoryCvoid,copy_u_wrap_mul,ha,Int.toNat_natCast]
    · have hc : ¬(memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0) := by
        intro h
        exact h.elim hu hz
      have hbool : (memory.arrayElement == 2 || memory.layoutBytes.val == 0) = false := by
        simp only [Bool.or_eq_false_iff,beq_eq_false_iff_ne]
        exact ⟨hu,hz⟩
      simp only [pointer,offsetRef,if_neg hc,unsafeConvertMemoryRefCvoid,hbool,
        Bool.false_eq_true,ite_false,ha,Int.toNat_natCast]

theorem copy_ref_validRange (heap : ByteHeap) (reference : Ref T) (n : Nat)
    (hv : validRef heap reference n) (hn : 0 < n) :
    JuliaLean.base.cmem.validRange heap (pointer reference)
      (JInt.wrap .u64 ((n : Int) * reference.mem.layoutBytes.val)) := by
  obtain ⟨hm,k,hkn,href⟩ := hv
  have hptr := copy_pointer_offset heap reference.mem k n hm hkn hn
  rw [←href] at hptr
  have hmul := Nat.mul_le_mul_right reference.mem.layoutBytes.val.toNat hkn
  rw [Nat.add_mul] at hmul
  have hcap := hm.2.2.1
  have hend := hm.2.2.2.1
  have hcount : (JInt.wrap .u64 ((n : Int) * reference.mem.layoutBytes.val)).val.toNat =
      n * reference.mem.layoutBytes.val.toNat := by
    have hcast : ((n * reference.mem.layoutBytes.val.toNat : Nat) : Int) =
        (n : Int) * reference.mem.layoutBytes.val := by
      rw [Int.natCast_mul,Int.toNat_of_nonneg hm.1]
    rw [←hcast,copy_u_wrap_nat _ (by omega),Int.toNat_natCast]
  change ByteHeap.validRange heap ((pointer reference).address.val.toNat) _
  rw [hptr,hcount]
  refine ⟨by omega,?_⟩
  intro byte hbyte
  have hh := hm.2.2.2.2.1 (k*reference.mem.layoutBytes.val.toNat+byte) (by omega)
  simpa only [Nat.add_assoc] using hh

theorem copy_count_value (heap : ByteHeap) (reference : Ref T) (n : Nat)
    (hv : validRef heap reference n) :
    (JInt.wrap .u64 ((n : Int) * reference.mem.layoutBytes.val)).val.toNat =
      n * reference.mem.layoutBytes.val.toNat := by
  have hm := hv.1
  obtain ⟨k,hkn,_⟩ := hv.2
  have hmul := Nat.mul_le_mul_right reference.mem.layoutBytes.val.toNat (show n ≤ reference.mem.capacity by omega)
  have hcap := hm.2.2.1
  have hcast : ((n * reference.mem.layoutBytes.val.toNat : Nat) : Int) =
      (n : Int) * reference.mem.layoutBytes.val := by
    rw [Int.natCast_mul,Int.toNat_of_nonneg hm.1]
  rw [←hcast,copy_u_wrap_nat _ (by omega),Int.toNat_natCast]

theorem copy_payload_frame (before after : ByteHeap) (reference : Ref T) (n : Nat)
    (hv : validRef before reference n) (hf : frame before after) :
    payload after reference n = payload before reference n := by
  by_cases hn : n = 0
  · simp only [hn,payload,Nat.zero_mul,List.range_zero,List.map_nil]
  · have hvalid := copy_ref_validRange before reference n hv (by omega)
    have hcount := copy_count_value before reference n hv
    change ByteHeap.validRange before ((pointer reference).address.val.toNat) _ at hvalid
    unfold payload
    apply List.map_congr_left
    intro byte hbyte
    have hb : before.validByte (payloadAddress reference byte) = true := by
      apply hvalid.2 byte
      rw [hcount]
      exact List.mem_range.mp hbyte
    exact (hf _ (Nat.mod_lt _ (by decide)) hb).2

theorem copy_selectors_frame (before after : ByteHeap) (reference : Ref T) (n : Nat)
    (hv : validRef before reference n) (hf : frame before after) :
    selectors after reference n = selectors before reference n := by
  by_cases hu : reference.mem.arrayElement = 2
  · simp only [selectors,if_pos hu]
    apply List.map_congr_left
    intro index hindex
    have hi := List.mem_range.mp hindex
    obtain ⟨hm,k,hkn,href⟩ := hv
    have hk63 := hm.2.1
    have hk64 : k < 2 ^ 64 := by omega
    have hoff : reference.ptr_or_offset.val.toNat = k := by
      rw [href]
      simp only [offsetRef,if_pos (Or.inl hu),copy_u_wrap_nat _ hk64,Int.toNat_natCast]
    have htag := hm.2.2.2.2.2 hu (k+index) (by omega)
    have hb : before.validByte (tagAddress reference index) = true := by
      simp only [tagAddress,hoff]
      simpa only [Nat.add_assoc] using htag
    exact (hf _ (Nat.mod_lt _ (by decide)) hb).2
  · simp only [selectors,if_neg hu]
end round6e
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6e
open JuliaLean
set_option maxHeartbeats 1000000

open JuliaLean.Proofs.base.int


open JuliaLean JuliaLean.Proofs.base.int
open JuliaLean.base.pointer
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

open JuliaLean

theorem copy_frame_trans (before middle after : JuliaLean.base.pointer.ByteHeap)
    (h₁ : frame before middle) (h₂ : frame middle after) : frame before after := by
  intro address haddr hvalid
  have hmid := h₁ address haddr hvalid
  have hafter := h₂ address haddr hmid.1
  exact ⟨hafter.1,hafter.2.trans hmid.2⟩

theorem copy_validMemory_frame (before after : JuliaLean.base.pointer.ByteHeap)
    (memory : Memory T) (h : validMemory before memory) (hf : frame before after) :
    validMemory after memory := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_,?_⟩
  · intro byte hbyte
    exact (hf _ (Nat.mod_lt _ (by decide)) (h.2.2.2.2.1 byte hbyte)).1
  · intro hu index hi
    exact (hf _ (Nat.mod_lt _ (by decide)) (h.2.2.2.2.2 hu index hi)).1

theorem copy_validRef_frame (before after : JuliaLean.base.pointer.ByteHeap)
    (reference : Ref T) (n : Nat) (h : validRef before reference n) (hf : frame before after) :
    validRef after reference n :=
  ⟨copy_validMemory_frame before after reference.mem h.1 hf,h.2⟩

theorem copy_get_run {ε σ : Type} (world : World σ) :
    (get : M ε σ (World σ)).run world = (.ok world,world) := rfl

theorem copy_set_run {ε σ : Type} (world after : World σ) :
    (set after : M ε σ Unit).run world = (.ok (),after) := rfl

theorem copy_moveBytes_run {ε σ : Type} (calls : JuliaLean.base.cmem.CMemoryOps)
    (world : World σ) (dest src : JuliaLean.base.pointer.Ptr Unit) (n : I)
    (size : U) (hsize : JuliaLean.base.cmem.csizeFromInt n.val = .ok size) :
    (moveBytes (ε := ε) calls dest src n).run world =
      (.ok (),{world with bytes := (calls.memmoveC world.bytes dest src size).1}) := by
  simp only [moveBytes,copy_bind_run,copy_get_run,JuliaLean.base.cmem.memmove,hsize,
    Bind.bind,Except.bind,Pure.pure,Except.pure,JuliaLean.base.pointer.convertPtrType,
    copy_set_run]
  rfl

theorem copy_validMemory_validByte_eq (before after : ByteHeap) (memory : Memory T)
    (h : validMemory before memory) (heq : after.validByte = before.validByte) :
    validMemory after memory := by
  unfold validMemory
  rw [heq]
  exact h

theorem copy_payload_effect (before after : ByteHeap) (dest src : Ref T) (n : Nat)
    (size : U) (hlayout : dest.mem.layoutBytes = src.mem.layoutBytes)
    (hsize : size.val.toNat = n * src.mem.layoutBytes.val.toNat)
    (heffect : JuliaLean.base.cmem.copyEffect before after (pointer dest) (pointer src) size) :
    payload after dest n = payload before src n := by
  unfold payload
  rw [hlayout]
  apply List.map_congr_left
  intro byte hbyte
  simpa only [payloadAddress,ByteHeap.readByte,addressMod,Nat.mod_mod,JuliaLean.base.cmem.pointerAddress] using
    heffect.1 byte (by rw [hsize]; exact List.mem_range.mp hbyte)

theorem copy_frame_of_copyEffect (before allocated after : ByteHeap) (dest src : Ref T)
    (n : Nat) (size : U)
    (hf : frame before allocated)
    (hsize : size.val.toNat = n * dest.mem.layoutBytes.val.toNat)
    (hnew : ∀ byte, byte < n * dest.mem.layoutBytes.val.toNat →
      before.validByte (payloadAddress dest byte) = false)
    (heffect : JuliaLean.base.cmem.copyEffect allocated after (pointer dest) (pointer src) size) :
    frame before after := by
  intro address haddr hvalid
  have hmiddle := hf address haddr hvalid
  refine ⟨?_,?_⟩
  · rw [heffect.2.2]
    exact hmiddle.1
  · have hout : ∀ offset, offset < size.val.toNat →
        addressMod address ≠ addressMod ((pointer dest).address.val.toNat + offset) := by
      intro offset hoff heq
      have hbad := hnew offset (by rw [←hsize]; exact hoff)
      change before.validByte (addressMod ((pointer dest).address.val.toNat + offset)) = false at hbad
      rw [←heq] at hbad
      change before.validByte (address % 2 ^ 64) = false at hbad
      rw [Nat.mod_eq_of_lt haddr,hvalid] at hbad
      contradiction
    exact (heffect.2.1 address hout).trans hmiddle.2
end round6e
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6e
open JuliaLean
set_option maxHeartbeats 1000000

open JuliaLean.Proofs.base.int


open JuliaLean JuliaLean.Proofs.base.int
open JuliaLean.base.pointer
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

open JuliaLean


open JuliaLean.base.operators
theorem copy_afoldlFrom_append {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (pre suffix : List (Σ s : σ, Elem s)) (y : Σ t : τ, Acc t) :
    afoldlFrom op (pre ++ suffix) (pre.length + 1) suffix.length y =
      suffix.foldl op y := by
  induction suffix generalizing pre y with
  | nil => rfl
  | cons b bs ih =>
    have hstep : afoldlAt op y (pre ++ b :: bs) (pre.length + 1) = op y b := by
      simp [afoldlAt]
    simp only [List.length_cons, afoldlFrom, hstep, List.foldl_cons]
    have h := ih (pre ++ [b]) (op y b)
    simpa [List.append_assoc, List.length_append, Nat.add_assoc] using h
theorem copy_afoldlMany_eq_foldl {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (a : Σ t : τ, Acc t) (bs : List (Σ s : σ, Elem s)) :
    afoldlMany op a bs = bs.foldl op a := by
  cases bs with
  | nil => rfl
  | cons b1 bs =>
    cases bs with
    | nil => rfl
    | cons b2 bs =>
      cases bs with
      | nil => rfl
      | cons b3 bs =>
        cases bs with
        | nil => rfl
        | cons b4 bs =>
          cases bs with
          | nil => rfl
          | cons b5 bs =>
            cases bs with
            | nil => rfl
            | cons b6 bs =>
              cases bs with
              | nil => rfl
              | cons b7 bs =>
                cases bs with
                | nil => rfl
                | cons b8 bs =>
                  cases bs with
                  | nil => rfl
                  | cons b9 bs =>
                    cases bs with
                    | nil => rfl
                    | cons b10 bs =>
                      cases bs with
                      | nil => rfl
                      | cons b11 bs =>
                        cases bs with
                        | nil => rfl
                        | cons b12 bs =>
                          cases bs with
                          | nil => rfl
                          | cons b13 bs =>
                            cases bs with
                            | nil => rfl
                            | cons b14 bs =>
                              cases bs with
                              | nil => rfl
                              | cons b15 bs =>
                                cases bs with
                                | nil => rfl
                                | cons b16 bs =>
                                  cases bs with
                                  | nil => rfl
                                  | cons b17 bs =>
                                    cases bs with
                                    | nil => rfl
                                    | cons b18 bs =>
                                      cases bs with
                                      | nil => rfl
                                      | cons b19 bs =>
                                        cases bs with
                                        | nil => rfl
                                        | cons b20 bs =>
                                          cases bs with
                                          | nil => rfl
                                          | cons b21 bs =>
                                            cases bs with
                                            | nil => rfl
                                            | cons b22 bs =>
                                              cases bs with
                                              | nil => rfl
                                              | cons b23 bs =>
                                                cases bs with
                                                | nil => rfl
                                                | cons b24 bs =>
                                                  cases bs with
                                                  | nil => rfl
                                                  | cons b25 bs =>
                                                    cases bs with
                                                    | nil => rfl
                                                    | cons b26 bs =>
                                                      cases bs with
                                                      | nil => rfl
                                                      | cons b27 bs =>
                                                        cases bs with
                                                        | nil => rfl
                                                        | cons b28 bs =>
                                                          cases bs with
                                                          | nil => rfl
                                                          | cons b29 bs =>
                                                            cases bs with
                                                            | nil => rfl
                                                            | cons b30 bs =>
                                                              cases bs with
                                                              | nil => rfl
                                                              | cons b31 bs =>
                                                                cases bs with
                                                                | nil => rfl
                                                                | cons b32 bs =>
                                                                  exact copy_afoldlFrom_append op [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] (b32 :: bs) (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op a b1) b2) b3) b4) b5) b6) b7) b8) b9) b10) b11) b12) b13) b14) b15) b16) b17) b18) b19) b20) b21) b22) b23) b24) b25) b26) b27) b28) b29) b30) b31)
end round6e
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6e
open JuliaLean
set_option maxHeartbeats 1000000

open JuliaLean.Proofs.base.int


open JuliaLean JuliaLean.Proofs.base.int
open JuliaLean.base.pointer
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

open JuliaLean


open JuliaLean.base.operators
open JuliaLean.Proofs.base.int

theorem copy_mul_val (x y : I) :
    (JuliaLean.base.int.binop JuliaLean.base.int.mul x y).val =
      wrapInt .i64 (x.val * y.val) := by
  rw [binop_eq,JuliaLean.base.int.mul,mul_int_val,remT_val,remT_val]
  change wrapInt .i64 (wrapInt .i64 x.val * wrapInt .i64 y.val) = _
  rw [wrapInt_mul_left,wrapInt_mul_right]

theorem copy_native_fold (xs : List I) (acc : I) :
    ((xs.map (fun value => (⟨(), value⟩ : Sigma (fun _ : Unit => I)))).foldl
      (fun a value => ⟨(), JuliaLean.base.int.binop JuliaLean.base.int.mul a.2 value.2⟩)
      (⟨(),acc⟩ : Sigma (fun _ : Unit => I))).2.val =
      wrapInt .i64 (acc.val * (xs.map Subtype.val).prod) := by
  induction xs generalizing acc with
  | nil =>
    simp only [List.map_nil,List.foldl_nil,List.prod_nil,Int.mul_one]
    exact (wrapInt_val acc).symm
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,List.prod_cons]
    have hi := ih (JuliaLean.base.int.binop JuliaLean.base.int.mul acc x)
    exact hi.trans (by rw [copy_mul_val,wrapInt_mul_left,Int.mul_assoc])

theorem copy_nativeMultiply (xs : List I) :
    (nativeMultiply xs).val = wrapInt .i64 (xs.map Subtype.val).prod := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil =>
      simpa only [nativeMultiply,JuliaLean.base.operators.unaryMulNumber,List.map_cons,
        List.map_nil,List.prod_cons,List.prod_nil,Int.mul_one] using (wrapInt_val x).symm
    | cons y ys =>
      cases ys with
      | nil =>
        simpa only [nativeMultiply,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Int.mul_one]
          using copy_mul_val x y
      | cons z zs =>
        simp only [nativeMultiply,JuliaLean.base.operators.naryOperator,
          copy_afoldlMany_eq_foldl]
        have hi := copy_native_fold zs
          (JuliaLean.base.int.binop JuliaLean.base.int.mul
            (JuliaLean.base.int.binop JuliaLean.base.int.mul x y) z)
        exact hi.trans (by
          erw [copy_mul_val (JuliaLean.base.int.binop JuliaLean.base.int.mul x y) z,
            copy_mul_val x y,wrapInt_mul_left]
          rw [Int.mul_assoc,wrapInt_mul_left]
          simp only [List.map_cons,List.prod_cons,Int.mul_assoc])

theorem copy_nativeProduct (xs : List I) :
    (nativeProduct xs).val = wrapInt .i64 (xs.map Subtype.val).prod := by
  cases xs with
  | nil => rfl
  | cons x xs => exact copy_nativeMultiply (x :: xs)

theorem copy_product_nonneg (xs : List I) (h : ∀ x ∈ xs, 0 ≤ x.val) :
    (xs.map Subtype.val).prod = (((xs.map (fun x => x.val.toNat)).prod : Nat) : Int) := by
  have hp := JuliaLean.Proofs.base.array.opusGrowth.prod_toNat_cast (xs.map Subtype.val)
    (by intro d hd; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd; exact h x hx)
  simpa only [List.map_map,Function.comp_def] using hp.1.symm

theorem copy_length_value (world : World σ) (array : ArrayObject T)
    (h : validArray world array) :
    (length array).val = (((array.dimensions.map (fun d => d.val.toNat)).prod : Nat) : Int) := by
  have hnonneg := h.2.2.1
  obtain ⟨hmem,offset,hoff,href⟩ := h.2.2.2
  have hcap := hmem.2.1
  have hproduct := copy_product_nonneg array.dimensions hnonneg
  have hprod : (array.dimensions.map (fun d => d.val.toNat)).prod < 2 ^ 63 := by omega
  have hp : wrapInt .i64 (array.dimensions.map Subtype.val).prod =
      (((array.dimensions.map (fun d => d.val.toNat)).prod : Nat) : Int) := by
    rw [hproduct]
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ (((array.dimensions.map (fun d => d.val.toNat)).prod : Nat) : Int) ∧
      (((array.dimensions.map (fun d => d.val.toNat)).prod : Nat) : Int) ≤ 9223372036854775807
    omega
  cases hd : array.dimensions with
  | nil =>
    simp only [length,hd,nativeProduct,JuliaLean.base.essentials.lengthAbstract,
      size,JuliaLean.base.essentials.sizeArray]
    rfl
  | cons d ds =>
    cases ds with
    | nil =>
      simp only [length,hd,JuliaLean.base.essentials.lengthArray1,List.map_cons,
        List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one]
      exact (Int.toNat_of_nonneg (hnonneg d (by simp [hd]))).symm
    | cons e es =>
      simp only [length,hd,JuliaLean.base.essentials.lengthAbstract,size,
        JuliaLean.base.essentials.sizeArray,copy_nativeProduct]
      simpa only [hd] using hp

theorem copyArray_allocator_rejection (runtime : Runtime ε σ T) (law : runtime.Law)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (world : World σ) (array : ArrayObject T)
    (h : validArray world array)
    (hnfit : ¬allocationFits array.ref.mem
      (array.dimensions.map (fun d => d.val.toNat)).prod) :
    ∃ message, (copyArray runtime calls unreached array).run world =
      (.error (.inl (.argument message)),world) := by
  have hn := copy_length_value world array h
  have ha := law.1 world array.ref.mem (length array) h.2.2.2.1 h.2.1 (by rw [hn]; omega)
  rw [hn,Int.toNat_natCast] at ha
  obtain ⟨message,hm⟩ := ha.2 hnfit
  exact ⟨message,copyArray_allocation_error runtime calls unreached world world array _ hm⟩

theorem copy_memoryref_valid (heap : ByteHeap) (memory : Memory T) (n : Nat)
    (hm : validMemory heap memory) (hn : n ≤ memory.capacity) :
    validRef heap (memoryref memory) n := by
  refine ⟨hm,0,?_,?_⟩
  · change 0 + n ≤ memory.capacity
    omega
  · unfold memoryref offsetRef
    split
    · rfl
    · simp only [Int.natCast_zero,Int.zero_mul,copy_u_add_zero]

theorem copy_ccall_frame (before allocated after : ByteHeap) (dest src : Ref T) (n : Nat)
    (hf : frame before allocated)
    (hnew : ∀ byte, byte < n * dest.mem.layoutBytes.val.toNat →
      before.validByte (payloadAddress dest byte) = false)
    (htags : dest.mem.arrayElement = 2 → ∀ index, index < n →
      before.validByte (tagAddress dest index) = false)
    (heq : after.validByte = allocated.validByte)
    (hout : ∀ address, address < 2 ^ 64 →
      (¬∃ byte, byte < n * dest.mem.layoutBytes.val.toNat ∧ address = payloadAddress dest byte) →
      (dest.mem.arrayElement ≠ 2 ∨ ¬∃ index, index < n ∧ address = tagAddress dest index) →
      after.readByte address = allocated.readByte address) : frame before after := by
  intro address haddr hvalid
  have hmiddle := hf address haddr hvalid
  refine ⟨by rw [heq]; exact hmiddle.1,?_⟩
  apply Eq.trans (hout address haddr ?_ ?_) hmiddle.2
  · rintro ⟨byte,hbyte,rfl⟩
    have hbad := hnew byte hbyte
    rw [hvalid] at hbad
    contradiction
  · by_cases hu : dest.mem.arrayElement = 2
    · right
      rintro ⟨index,hindex,rfl⟩
      have hbad := htags hu index hindex
      rw [hvalid] at hbad
      contradiction
    · exact Or.inl hu

theorem copy_nativeByteCount (heap : ByteHeap) (src : Ref T) (n : Nat) (ni : I)
    (hv : validRef heap src n) (hn : ni.val = (n : Int)) :
    (JuliaLean.base.int.binop JuliaLean.base.int.mul src.mem.layoutBytes ni).val =
      (n : Int) * src.mem.layoutBytes.val := by
  have hmul := Nat.mul_le_mul_right src.mem.layoutBytes.val.toNat
    (show n ≤ src.mem.capacity by obtain ⟨k,hk,_⟩ := hv.2; omega)
  have hcap := hv.1.2.2.1
  have hcast : ((n * src.mem.layoutBytes.val.toNat : Nat) : Int) =
      (n : Int) * src.mem.layoutBytes.val := by
    rw [Int.natCast_mul,Int.toNat_of_nonneg hv.1.1]
  rw [copy_mul_val,hn,Int.mul_comm]
  apply wrapInt_of_inRange
  change IntTy.i64.min ≤ (n : Int) * src.mem.layoutBytes.val ∧
    (n : Int) * src.mem.layoutBytes.val ≤ IntTy.i64.max
  rw [←hcast]
  change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
  omega

theorem copy_ref_spec (runtime : Runtime ε σ T) (law : runtime.Law)
    (calls : JuliaLean.base.cmem.CMemoryOps)
    (unreached : JuliaLean.base.genericmemory.MemoryCopyOps (M ε σ) (Memory T) U I I I I
      (JuliaLean.base.pointer.Ptr Unit) Nat) (before allocated : World σ)
    (src : Ref T) (fresh : Memory T) (n : Nat) (ni : I)
    (hnval : ni.val = (n : Int)) (hsrc : validRef before.bytes src n)
    (hcap : fresh.capacity = n) (hlayout : fresh.layoutBytes = src.mem.layoutBytes)
    (hkind : fresh.arrayElement = src.mem.arrayElement)
    (hfresh : validMemory allocated.bytes fresh) (hframe : frame before.bytes allocated.bytes)
    (hnew : 0 < n →
      (∀ byte, byte < fresh.capacity * fresh.layoutBytes.val.toNat →
        before.bytes.validByte (payloadAddress (memoryref fresh) byte) = false) ∧
      (fresh.arrayElement = 2 → ∀ index, index < fresh.capacity →
        before.bytes.validByte (tagAddress (memoryref fresh) index) = false))
    (hbits : runtime.isBits = true → src.mem.arrayElement ≠ 2) :
    ∃ after, (JuliaLean.base.genericmemory.unsafeCopytoRefs (T := T)
        (copyOps runtime calls src.mem.layoutBytes unreached) false (memoryref fresh) src ni).run
        allocated = (.ok (memoryref fresh),after) ∧
      after.nextMemory = allocated.nextMemory ∧ after.nextArray = allocated.nextArray ∧
      after.other = allocated.other ∧ validMemory after.bytes fresh ∧
      payload after.bytes (memoryref fresh) n = payload before.bytes src n ∧
      selectors after.bytes (memoryref fresh) n = selectors before.bytes src n ∧
      frame before.bytes after.bytes := by
  by_cases hz : n = 0
  · refine ⟨allocated,copy_ref_zero_run runtime calls unreached allocated (memoryref fresh) src ni
      (by omega),rfl,rfl,rfl,hfresh,?_,?_,hframe⟩
    · simp only [hz,payload,Nat.zero_mul,List.range_zero,List.map_nil]
    · simp [selectors,hz]
  have hn : 0 < n := by omega
  have hs := copy_validRef_frame before.bytes allocated.bytes src n hsrc hframe
  have hd := copy_memoryref_valid allocated.bytes fresh n hfresh (by omega)
  have hnew' := hnew hn
  cases hb : runtime.isBits with
  | false =>
    have hsep := copy_separate_fresh fresh src.mem before.bytes hsrc.1 hnew'.1 hnew'.2
    obtain ⟨after,hcall,hm,ha,ho,hv,hpay,htags,houtside⟩ :=
      law.2.2 allocated (memoryref fresh) src ni (by omega)
        (by simpa only [hnval,Int.toNat_natCast] using hd)
        (by simpa only [hnval,Int.toNat_natCast] using hs) hlayout hkind hsep
    refine ⟨after,copy_ref_nonbits_run runtime calls unreached allocated after
      (memoryref fresh) src ni (by omega) hb hcall,hm,ha,ho,
      copy_validMemory_validByte_eq allocated.bytes after.bytes fresh hfresh hv,?_,?_,?_⟩
    · rw [hnval,Int.toNat_natCast] at hpay
      exact hpay.trans (copy_payload_frame before.bytes allocated.bytes src n hsrc hframe)
    · rw [hnval,Int.toNat_natCast] at htags
      exact htags.trans (copy_selectors_frame before.bytes allocated.bytes src n hsrc hframe)
    · apply copy_ccall_frame before.bytes allocated.bytes after.bytes (memoryref fresh) src n hframe
      · simpa only [memoryref,hcap] using hnew'.1
      · simpa only [memoryref,hcap] using hnew'.2
      · exact hv
      · simpa only [hnval,Int.toNat_natCast] using houtside
  | true =>
    let size : U := JInt.wrap .u64 ((n : Int) * src.mem.layoutBytes.val)
    have hsizeval : size.val.toNat = n * src.mem.layoutBytes.val.toNat :=
      copy_count_value allocated.bytes src n hs
    have hsrcRange := copy_ref_validRange allocated.bytes src n hs hn
    have hdestRange : JuliaLean.base.cmem.validRange allocated.bytes (pointer (memoryref fresh)) size := by
      simpa only [size,memoryref,hlayout] using copy_ref_validRange allocated.bytes (memoryref fresh) n hd hn
    have hbyteval := copy_nativeByteCount allocated.bytes src n ni hs hnval
    have hcast : ((n * src.mem.layoutBytes.val.toNat : Nat) : Int) =
        (n : Int) * src.mem.layoutBytes.val := by
      rw [Int.natCast_mul,Int.toNat_of_nonneg hs.1.1]
    have hcountBound : n * src.mem.layoutBytes.val.toNat < 2 ^ 63 - 1 := by
      have hmul := Nat.mul_le_mul_right src.mem.layoutBytes.val.toNat
        (show n ≤ src.mem.capacity by obtain ⟨k,hk,_⟩ := hs.2; omega)
      have hc := hs.1.2.2.1
      omega
    have hconvert : JuliaLean.base.cmem.csizeFromInt
        (JuliaLean.base.int.binop JuliaLean.base.int.mul src.mem.layoutBytes ni).val = .ok size := by
      rw [hbyteval]
      unfold JuliaLean.base.cmem.csizeFromInt
      rw [if_pos (show 0 ≤ (n : Int) * src.mem.layoutBytes.val ∧
          (n : Int) * src.mem.layoutBytes.val < 2 ^ 64 by rw [←hcast]; omega)]
    let after : World σ := {allocated with bytes :=
      (calls.memmoveC allocated.bytes (pointer (memoryref fresh)) (pointer src) size).1}
    have heffect := (calls.memmoveStandard allocated.bytes (pointer (memoryref fresh))
      (pointer src) size hdestRange hsrcRange).2
    have hmove := copy_moveBytes_run (ε := ε) calls allocated (pointer (memoryref fresh))
      (pointer src) (JuliaLean.base.int.binop JuliaLean.base.int.mul src.mem.layoutBytes ni)
      size hconvert
    refine ⟨after,copy_ref_bits_run runtime law calls unreached allocated after
      (memoryref fresh) src ni (by omega) hb hmove,rfl,rfl,rfl,
      copy_validMemory_validByte_eq allocated.bytes after.bytes fresh hfresh heffect.2.2,?_,?_,?_⟩
    · exact (copy_payload_effect allocated.bytes after.bytes (memoryref fresh) src n size
        hlayout hsizeval heffect).trans
        (copy_payload_frame before.bytes allocated.bytes src n hsrc hframe)
    · simp only [selectors,memoryref,hkind,if_neg (hbits hb)]
    · apply copy_frame_of_copyEffect before.bytes allocated.bytes after.bytes
        (memoryref fresh) src n size hframe
      · simpa only [memoryref,hlayout] using hsizeval
      · simpa only [memoryref,hcap] using hnew'.1
      · exact heffect

theorem copyArraySpec : CopyArraySpec := by
  intro ε σ T runtime law calls unreached world array hvalid hbits
  have hlen := copy_length_value world array hvalid
  have hlenNat : (length array).val.toNat =
      (array.dimensions.map (fun d => d.val.toNat)).prod := by
    rw [hlen,Int.toNat_natCast]
  constructor
  · cases halloc : (runtime.allocate array.ref.mem (length array)).run world with
    | mk outcome allocated =>
      cases outcome with
      | error failure =>
        exact copyArray_allocation_error runtime calls unreached world allocated array failure halloc
      | ok fresh =>
        have hlaw := law.1 world array.ref.mem (length array)
          hvalid.2.2.2.1 hvalid.2.1 (by rw [hlen]; omega)
        have hfits : allocationFits array.ref.mem (length array).val.toNat := by
          apply Classical.byContradiction
          intro hbad
          obtain ⟨message,hm⟩ := hlaw.2 hbad
          rw [halloc] at hm
          cases hm
        rcases hlaw.1 hfits with ⟨failure,after,hfail⟩ |
          ⟨fresh',allocated',halloc',hcap,hlayout,hkind,hmem,hframe,
            harray,hother,hfid,hzero,hpos,hsupport⟩
        · rw [halloc] at hfail
          cases hfail
        · rw [halloc] at halloc'
          obtain ⟨hf,hw⟩ := Prod.mk.inj halloc'
          cases Except.ok.inj hf
          cases hw
          rw [hlenNat] at hcap
          obtain ⟨copied,hcopy,hcm,hca,hco,hcmem,hpay,htags,hcf⟩ :=
            copy_ref_spec runtime law calls unreached world allocated array.ref fresh
              (array.dimensions.map (fun d => d.val.toNat)).prod (length array)
              hlen hvalid.2.2.2 hcap hlayout hkind hmem hframe
              (by intro hn; exact (hpos (by rw [hlen]; omega)).2.2) hbits
          refine ⟨⟨copied.nextArray,memoryref fresh,size array⟩,
            {copied with nextArray := copied.nextArray+1},
            copyArray_success_run runtime calls unreached world allocated copied array fresh
              (memoryref fresh) halloc hcopy,?_,?_,rfl,hcap,hlayout,hkind,?_,?_,
            hpay,htags,hcf,?_,?_⟩
          · exact hca.trans harray
          · have h := hvalid.1
            change copied.nextArray ≠ array.identity
            rw [hca,harray]
            omega
          · refine ⟨by dsimp only; omega,?_,hvalid.2.2.1,?_⟩
            · change fresh.identity < copied.nextMemory
              rw [hcm]
              exact hfid
            · exact copy_memoryref_valid copied.bytes fresh
                (array.dimensions.map (fun d => d.val.toNat)).prod hcmem (Nat.le_of_eq hcap.symm)
          · intro hn
            change 0 < (array.dimensions.map (fun d => d.val.toNat)).prod at hn
            change world.nextMemory ≤ fresh.identity
            rw [(hpos (by rw [hlen]; omega)).1]
            exact Nat.le_refl _
          · exact hco.trans hother
          · dsimp only
            rw [hca,harray]
  · exact copyArray_allocator_rejection runtime law calls unreached world array hvalid
end round6e
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.Array

open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayFilter
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayRange




open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round12
open JuliaLean.Proofs.base.array.round6b (IntegerArgument bytePointer)

attribute [local irreducible] JInt.wrap wrapInt

theorem batch1_stateGet_run (s : σ) :
    (get : StateT σ (Except ε) σ).run s = .ok (s, s) := rfl

theorem batch1_byteCall_run (call : JuliaLean.base.pointer.ByteHeap →
    Jl (JuliaLean.base.pointer.ByteHeap × α)) (heap : JuliaLean.base.pointer.ByteHeap) :
    (round6b.byteCall call).run heap =
      match call heap with
      | .error _ => .error .inexact
      | .ok (after, value) => .ok (value, after) := by
  simp only [round6b.byteCall, batch1_stateBind_run, batch1_stateGet_run]
  cases call heap with
  | error e => rfl
  | ok pair => cases pair; rfl

/-- The pointer-copy wrapper returns the pointer and the memory produced by the C call. -/
theorem batch1_pointerCopyAfterProduct_run (stride : I) (n bytes : IntegerArgument)
    (convert : Int → Jl JuliaLean.base.cmem.CSizeT)
    (heap : JuliaLean.base.pointer.ByteHeap) (dest src : Nat) :
    pointerCopyAfterProduct stride n bytes convert heap dest src =
      match JuliaLean.base.cmem.memmove JuliaLean.base.cmem.StandardC.standardCMemoryOps
        (pointerCopyCSize convert) heap (bytePointer dest) (bytePointer src) bytes with
      | .error _ => .error .inexact
      | .ok (after, _) => .ok (bytePointer dest, after) := by
  simp only [pointerCopyAfterProduct, unsafeCopyPtr, batch1_stateBind_run,
    batch1_byteCall_run, batch1_statePure_run]
  cases JuliaLean.base.cmem.memmove JuliaLean.base.cmem.StandardC.standardCMemoryOps
    (pointerCopyCSize convert) heap (bytePointer dest) (bytePointer src) bytes <;> rfl

/-- Conversion failure occurs before any copying. -/
theorem batch1_pointerCopyAfterProduct_error (stride : I) (n bytes : IntegerArgument)
    (convert : Int → Jl JuliaLean.base.cmem.CSizeT)
    (heap : JuliaLean.base.pointer.ByteHeap) (dest src : Nat) (e : JlError)
    (h : pointerCopyCSize convert bytes = .error e) :
    pointerCopyAfterProduct stride n bytes convert heap dest src = .error .inexact := by
  rw [batch1_pointerCopyAfterProduct_run]
  simp only [JuliaLean.base.cmem.memmove, h] <;> rfl

/-- Valid converted ranges inherit the overlap-safe C byte-copy law. -/
theorem batch1_pointerCopyAfterProduct_ok (stride : I) (n bytes : IntegerArgument)
    (convert : Int → Jl JuliaLean.base.cmem.CSizeT)
    (heap : JuliaLean.base.pointer.ByteHeap) (dest src : Nat)
    (size : JuliaLean.base.cmem.CSizeT)
    (h : pointerCopyCSize convert bytes = .ok size)
    (hd : JuliaLean.base.cmem.validRange heap (bytePointer dest) size)
    (hs : JuliaLean.base.cmem.validRange heap (bytePointer src) size) :
    ∃ after, pointerCopyAfterProduct stride n bytes convert heap dest src =
      .ok (bytePointer dest, after) ∧
      JuliaLean.base.cmem.copyEffect heap after (bytePointer dest) (bytePointer src) size := by
  obtain ⟨after, result, hcall, _, heffect⟩ :=
    JuliaLean.Proofs.base.cmem.memmoveOverlapSafe_proven
      (pointerCopyCSize convert) heap (bytePointer dest) (bytePointer src) bytes size h hd hs
  refine ⟨after, ?_, heffect⟩
  rw [batch1_pointerCopyAfterProduct_run, hcall]

/-- All product outcomes and both native and opaque conversion paths. -/
theorem MultidimcovArrayV2UnsafeCopytoPtr_proven :
    JuliaLean.Proofs.base.array.round12.PointerCopySpec := by
  intro multiply convert stride n heap dest src
  dsimp only
  cases hp : pointerIntegerProduct multiply n stride with
  | error e => exact ⟨e, rfl⟩
  | ok p =>
    cases p with
    | native value =>
      dsimp only [pointerProductArgument]
      cases hc : pointerCopyCSize convert (.bit _ value) with
      | error e =>
        exact ⟨.inexact, batch1_pointerCopyAfterProduct_error _ _ _ _ _ _ _ e hc⟩
      | ok size =>
        intro hd hs
        exact batch1_pointerCopyAfterProduct_ok _ _ _ _ _ _ _ size hc hd hs
    | «opaque» value =>
      dsimp only [pointerProductArgument]
      cases hc : pointerCopyCSize convert (.opaque value) with
      | error e =>
        exact ⟨.inexact, batch1_pointerCopyAfterProduct_error _ _ _ _ _ _ _ e hc⟩
      | ok size =>
        intro hd hs
        exact batch1_pointerCopyAfterProduct_ok _ _ _ _ _ _ _ size hc hd hs
end ChatGPTBatch1.Array
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

abbrev groupCopyImplementation {α OffD OffS Count : Type}
    (dv : OffD → Int) (sv : OffS → Int) (nv : Count → Int)
    (copy : Nat → Nat → I → CopyM α Unit) :=
  copytoImpl
    (fun n => pure (decide (nv n = 0))) (fun n => pure (decide (nv n > 0)))
    copyLength copyLength (copyBounds dv) (copyBounds sv)
    (fun len i => pure (JInt.wrap .i64 (len.val - dv i)))
    (fun len i => pure (JInt.wrap .i64 (len.val - sv i)))
    (fun a b => pure (a + b)) (fun a b => pure (a + b))
    (fun n rem => pure (decide (nv n ≤ rem.val)))
    (fun n rem => pure (decide (nv n ≤ rem.val)))
    (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
    (copyInt dv) (copyInt sv) (copyInt nv) copyReference copyReference copy

theorem groupCopyImplementationRun {α OffD OffS Count : Type}
    (dv : OffD → Int) (sv : OffS → Int) (nv : Count → Int)
    (copy : Nat → Nat → I → CopyM α Unit) (hc : MemoryCopyLaw copy)
    (old : Nat → Option α) (dest src : Nat × Nat) (di : OffD) (si : OffS) (n : Count)
    (hd : dest.2 < 2 ^ 63) (hs : src.2 < 2 ^ 63) :
    (groupCopyImplementation dv sv nv copy dest di src si n).run old =
      checkedCopyResult old dest src (dv di) (sv si) (nv n) := by
  by_cases hz : nv n = 0
  · simp only [groupCopyImplementation, copytoImpl, stateExcept_bind, stateExcept_pure,
      hz, decide_true, ite_true, checkedCopyResult]
  · by_cases hp : 0 < nv n
    · have hn : ¬ nv n < 0 := by omega
      by_cases hdi : 1 ≤ dv di ∧ dv di ≤ (dest.2 : Int)
      · have hrd := copy_remaining dest.2 (dv di) hd hdi
        by_cases hdc : nv n ≤ (dest.2 : Int) - dv di + 1
        · by_cases hsi : 1 ≤ sv si ∧ sv si ≤ (src.2 : Int)
          · have hrs := copy_remaining src.2 (sv si) hs hsi
            by_cases hsc : nv n ≤ (src.2 : Int) - sv si + 1
            · have hdFit : IntTy.i64.min ≤ dv di ∧ dv di ≤ IntTy.i64.max := by
                change -9223372036854775808 ≤ dv di ∧ dv di ≤ 9223372036854775807
                omega
              have hsFit : IntTy.i64.min ≤ sv si ∧ sv si ≤ IntTy.i64.max := by
                change -9223372036854775808 ≤ sv si ∧ sv si ≤ 9223372036854775807
                omega
              have hnFit : IntTy.i64.min ≤ nv n ∧ nv n ≤ IntTy.i64.max := by
                change -9223372036854775808 ≤ nv n ∧ nv n ≤ 9223372036854775807
                omega
              have hdv : (JInt.wrap .i64 (dv di)).val = dv di := wrapInt_of_inRange .i64 _ hdFit
              have hsv : (JInt.wrap .i64 (sv si)).val = sv si := wrapInt_of_inRange .i64 _ hsFit
              have hnv : (JInt.wrap .i64 (nv n)).val = nv n := wrapInt_of_inRange .i64 _ hnFit
              have hcp := hc old (dest.1 + (dv di - 1).toNat)
                (src.1 + (sv si - 1).toNat) (JInt.wrap .i64 (nv n)) (by rw [hnv]; omega)
              have inside : 1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                  1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int) := by omega
              rw [checkedCopyResult, if_neg hz, if_neg hn, if_pos inside]
              simp only [groupCopyImplementation, copytoImpl, stateExcept_bind,
                stateExcept_pure, hz, hp, decide_false, decide_true,
                Bool.not_true, Bool.false_eq_true, ite_false, ite_true, and_self,
                copyBounds_run, hdi, hsi, copyLength_run, hrd, hrs, hdc, hsc,
                copyInt_run, hdFit, hsFit, hnFit, copyReference_run, hdv, hsv,
                hcp, hnv,
                checkedCopyResult, hn, inside]
            · have outside : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                  1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
              rw [checkedCopyResult, if_neg hz, if_neg hn, if_neg outside]
              simp only [groupCopyImplementation, copytoImpl, stateExcept_bind,
                stateExcept_pure, hz, hp, decide_false, decide_true,
                Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, and_self,
                copyBounds_run, hdi, hsi, copyLength_run, hrd, hrs, hdc, hsc,
                stateExcept_throw, checkedCopyResult, hn, outside]
          · have outside : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                  1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
            rw [checkedCopyResult, if_neg hz, if_neg hn, if_neg outside]
            simp only [groupCopyImplementation, copytoImpl, stateExcept_bind,
              stateExcept_pure, hz, hp, decide_false, decide_true,
              Bool.not_true, Bool.false_eq_true, ite_false, ite_true, and_self,
              copyBounds_run, hdi, hsi, copyLength_run, hrd, hdc,
              checkedCopyResult, hn, outside]
        · have outside : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                  1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
          rw [checkedCopyResult, if_neg hz, if_neg hn, if_neg outside]
          simp only [groupCopyImplementation, copytoImpl, stateExcept_bind,
            stateExcept_pure, hz, hp, decide_false, decide_true,
            Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, and_self,
            copyBounds_run, hdi, copyLength_run, hrd, hdc,
            stateExcept_throw, checkedCopyResult, hn, outside]
      · have outside : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                  1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
        rw [checkedCopyResult, if_neg hz, if_neg hn, if_neg outside]
        simp only [groupCopyImplementation, copytoImpl, stateExcept_bind,
          stateExcept_pure, hz, hp, decide_false, decide_true,
          Bool.not_true, Bool.false_eq_true, ite_false, ite_true, and_self,
          copyBounds_run, hdi, checkedCopyResult, hn, outside]
    · have hn : nv n < 0 := by omega
      simp only [groupCopyImplementation, copytoImpl, stateExcept_bind,
        stateExcept_pure, hz, hp, decide_false, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, and_self,
        throwArgument, stateExcept_throw, checkedCopyResult, hn]

theorem groupCheckedCopy : CheckedCopySpec := by
  intro α OffD OffS Count dv sv nv copy hc old dest src di si n hd hs
  dsimp only
  intro operation ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  have heq : operation = groupCopyImplementation dv sv nv copy := by
    rcases ho with ho | ho | ho | ho | ho <;> exact ho
  rw [heq]
  exact groupCopyImplementationRun dv sv nv copy hc old dest src di si n hd hs

theorem ArrayopsCopytoAlias_proven : JuliaLean.Proofs.base.array.CompleteCheckedCopySpec :=
  ⟨groupCheckedCopy, heapCopyFrameSpec⟩


theorem groupCopiedZero (old : Nat → Option α) (dest src : Nat) :
    copiedElements old dest src 0 = old := by
  funext address
  unfold copiedElements
  exact if_neg (by omega)

theorem ArrayCopytoWhole_proven : JuliaLean.Proofs.base.array.WholeCopySpec := by
  intro α copy hc old dest src hd hs
  dsimp only
  intro operation ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  have heq : operation = copyto2arg
      (fun _ : Nat × Nat => (pure one : CopyM α I))
      (fun _ : Nat × Nat => (pure one : CopyM α I)) copyLength
      (groupCopyImplementation (fun i : I => i.val) (fun i : I => i.val)
        (fun i : I => i.val) copy) := by
    rcases ho with ho | ho | ho | ho | ho | ho | ho <;> exact ho
  rw [heq]
  have hsv : (JInt.wrap .i64 (src.2 : Int)).val = src.2 := by
    have hfit : IntTy.i64.min ≤ (src.2 : Int) ∧ (src.2 : Int) ≤ IntTy.i64.max := by
      change -9223372036854775808 ≤ (src.2 : Int) ∧ (src.2 : Int) ≤ 9223372036854775807
      omega
    exact wrapInt_of_inRange .i64 (src.2 : Int) hfit
  simp only [copyto2arg, stateExcept_bind, stateExcept_pure, copyLength_run]
  change (groupCopyImplementation (fun i : I => i.val) (fun i : I => i.val)
    (fun i : I => i.val) copy dest one src one (JInt.wrap .i64 src.2)).run old = _
  rw [groupCopyImplementationRun _ _ _ copy hc old dest src one one
    (JInt.wrap .i64 src.2) hd hs]
  simp only [checkedCopyResult, hsv, show one.val = 1 from rfl]
  by_cases hz : src.2 = 0
  · simp only [hz, Int.natCast_zero, ite_true, Nat.zero_le, groupCopiedZero]
  · have hz' : (src.2 : Int) ≠ 0 := by omega
    have hn : ¬ (src.2 : Int) < 0 := by omega
    by_cases hle : src.2 ≤ dest.2
    · have hi : 1 ≤ (1 : Int) ∧ 1 + (src.2 : Int) - 1 ≤ dest.2 ∧
          1 ≤ (1 : Int) ∧ 1 + (src.2 : Int) - 1 ≤ src.2 := by omega
      simp only [hz', hn, hle, hi, and_self, ite_true, ite_false, Int.sub_self, Int.toNat_zero,
        Nat.add_zero, Int.toNat_natCast]
    · have hi : ¬ (1 ≤ (1 : Int) ∧ 1 + (src.2 : Int) - 1 ≤ dest.2 ∧
          1 ≤ (1 : Int) ∧ 1 + (src.2 : Int) - 1 ≤ src.2) := by omega
      simp only [hz', hn, hle, hi, ite_false]
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
section MaskProofs

variable {α : Type}

attribute [local irreducible] JInt.wrap wrapInt

/-- Copying inside one vector changes no array header and no other memory object. -/
theorem mask_copy_frame (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (p q : I)
    (hp : 1 ≤ p.val ∧ p.val ≤ n.val) (hq : 1 ≤ q.val ∧ q.val ≤ n.val)
    (st' : MutableMemory α)
    (hr : (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
      handle p q).run s = (.ok (), st')) :
    st'.arrays = s.arrays ∧ ∀ other, other ≠ mem → st'.memories[other]? = s.memories[other]? := by
  obtain ⟨slots', hcopy, _, _⟩ :=
    vwCopyItem_run (unsetRuntime := layout.runtime) s handle mem off n slots h p q hp hq
  have hst : st' = {s with memories := s.memories.set mem slots'} :=
    congrArg Prod.snd (hr.symm.trans hcopy)
  rw [hst]
  refine ⟨rfl, ?_⟩
  intro other hne
  exact List.getElem?_set_ne (Ne.symm hne)
end MaskProofs
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- Two-argument copying observes destination firstindex, source firstindex, then source length, retaining the actual returned index/count types and all original operands. -/
def Copyto2argArguments : Prop :=
  ∀ (D S DI SI N : Type) (dest : D) (src : S) (di : DI) (si : SI) (n : N) (initial : List Nat),
    (JuliaLean.base.array.Completion3.copyto2arg (fun _ => call 0 (.ok di))
      (fun _ => call 1 (.ok si)) (fun _ => call 2 (.ok n))
      (fun d i s j n => call 3 (.ok (d, i, s, j, n))) dest src).run initial =
        (.ok (dest, di, src, si, n), initial ++ [0, 1, 2, 3])

/-- Pointer copying determines the element stride before multiplication or the native C call. Layout errors and divergence propagate without moving bytes or evaluating count arithmetic. -/
def PointerCopyLayoutFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Count Bytes : Type)
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (multiply : Count → I → NativeCopyM (NativeCopyWorld State) Bytes)
    (isInteger : Bytes → Bool) (toCsize : Bytes → NativeCopyM (NativeCopyWorld State) (JInt .u64))
    (ccall : NativeMemmove) (dest src : JuliaLean.base.pointer.Ptr T) (n : Count)
    (before : NativeCopyWorld State),
    FirstNativeFailure (nativeCopyLift (elsizeArrayRuntime layout elementType))
      (unsafeCopyPointer layout elementType multiply isInteger toCsize ccall dest src n) before
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Read the datatype flag independently of the modeled isbitstype function.
The bit at position three is the raw native dataFlags bit 0x0008. Source:
base/runtime_internals.jl:917. -/
def NativeCopyBitsFlag
    (layout : LayoutBoundary World V D N Mod P Sym Ref) (elementType : V) : Bool :=
  match layout.types.asDatatype elementType with
  | none => false
  | some datatype => decide ((layout.types.dataFlags datatype).val / 8 % 2 = 1)

/-- Observe the two existing native GC end actions in their source order.
Only a successful destination end permits the source end; any error retains
its family and post-error world, and divergence has no continuation. This is
an observation of native boundary actions, not a supplied correctness law or
an ordinary Base implementation. Source: base/genericmemory.jl:207-208. -/
def NativeCopyGcFinish (native : NativeCopyOps State T) (destToken srcToken : Nat)
    (dest : A) (afterMove : NativeCopyWorld State) :
    NativeCopyResult (NativeCopyWorld State) A :=
  match NativeCopyObserve (native.gcPreserveEnd destToken) afterMove with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok (_, afterDestEnd)) =>
      NativeCopyReturn dest
        (NativeCopyObserve (native.gcPreserveEnd srcToken) afterDestEnd)

/-- Independent bits-copy outcome after a successful raw layout observation.
The mathematical count times stride is reduced modulo 2^64. A residue in the
upper half is a negative signed Int and the checked Csize_t conversion raises
InexactError before the C call or either GC end. Otherwise the raw existing
memmove ABI consumes the independently observed addresses and byte count;
its returned heap precedes both GC end actions. No copy-effect law is assumed.
Sources: base/genericmemory.jl:204-208; base/cmem.jl:26-29. -/
def NativeCopyBitsAfterStride
    (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : A) (destReference srcReference : NativeCopyRef T)
    (destToken srcToken : Nat) (srcCount : Nat) (stride : JInt .i64)
    (afterLayout : NativeCopyWorld State)
    (result : NativeCopyResult (NativeCopyWorld State) A) : Prop :=
  let byteResidue : Int := ((srcCount : Int) * stride.val) % (2 : Int) ^ 64
  if (2 : Int) ^ 63 ≤ byteResidue then
    result = some (.error
      (.inr (.inr (.jl (.inexactError "convert"))), afterLayout))
  else
    let moved := ccall afterLayout.bytes
      (NativeCopyCvoidAddress destReference)
      (NativeCopyCvoidAddress srcReference)
      (JInt.wrap .u64 byteResidue)
    result = NativeCopyGcFinish native destToken srcToken dest
      { afterLayout with bytes := moved.1 }

/-- Complete bits protocol at the existing native boundary. The existential
raw observation is part of the conclusion, so layout success, failure and
divergence cannot be assumed. Native GC begin tokens are captured from the
stored references; begin is pure in the installed interface. Layout queries
use only ObserveArrayLayout, and a successful inline extent is constrained by
MinimalAlignedWord rather than the model's bitwise alignment formula. All
native power-of-two alignments determine a unique signed stride residue;
malformed boundary alignments remain admitted with that existing relation.
No aligned_sizeof, native multiplication, pointer-conversion, memmove-wrapper
or whole-copy model is used to compute the expected outcome. Sources:
base/genericmemory.jl:201-208; base/runtime_internals.jl:665-688. -/
def NativeCopyBitsProtocol
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : A) (before : NativeCopyWorld State)
    (destReference srcReference : NativeCopyRef T) (srcCount : Nat)
    (result : NativeCopyResult (NativeCopyWorld State) A) : Prop :=
  let destToken := native.gcPreserveBegin destReference
  let srcToken := native.gcPreserveBegin srcReference
  ∃ observed : LayoutObservation (NativeCopyWorld State),
    ObserveArrayLayout layout elementType before observed ∧
    match observed with
    | .diverged => result = none
    | .failed error after =>
        result = some (.error (.inr (.inr error), after))
    | .pointerSlot after =>
        NativeCopyBitsAfterStride native ccall dest destReference srcReference
          destToken srcToken srcCount (JInt.wrap .i64 8) after result
    | .inlineExtent payload alignment after =>
        ∃ stride : JInt .i64,
          MinimalAlignedWord payload alignment stride ∧
          NativeCopyBitsAfterStride native ccall dest destReference srcReference
            destToken srcToken srcCount stride after result

/-- Independent whole-copy control invariant. Source cardinality determines
emptiness and destination capacity determines BoundsError. Every success
returns the original destination. For non-bits storage, the independently
computed physical references and mathematical count select exactly one
existing native jl_genericmemory_copyto boundary action, retaining every
possible native error/effect/divergence. There is no precondition that this
boundary copies bytes correctly. Sources: base/array.jl:282-286,323,330-332;
base/genericmemory.jl:198-214. -/
def NativeCopyControl (dest : A) (before : World) (destCount srcCount : Nat)
    (isBits : Bool) (nativeObserved : NativeCopyResult World Unit)
    (result : NativeCopyResult World A) : Prop :=
  (srcCount = 0 → result = some (.ok (dest, before))) ∧
  (destCount < srcCount → result = some (.error (.inl .bounds, before))) ∧
  (∀ returned after, result = some (.ok (returned, after)) → returned = dest) ∧
  (0 < srcCount → srcCount ≤ destCount → isBits = false →
    result = NativeCopyReturn dest nativeObserved)

/-- Whole-copy control plus the complete bits protocol. Both native branches
are selected by independent datatype flag arithmetic. The non-bits request
uses mathematical source cardinality and raw physical references; the bits
request additionally observes raw layout, checked byte-count conversion,
memmove and both GC ends. No source-model success premise or native law is
required. Sources: base/array.jl:323,330-332; base/genericmemory.jl:198-214. -/
def NativeCopyFullControl
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (dest : A) (before : NativeCopyWorld State) (destCount srcCount : Nat)
    (destReference srcReference : NativeCopyRef T)
    (result : NativeCopyResult (NativeCopyWorld State) A) : Prop :=
  NativeCopyControl dest before destCount srcCount
    (NativeCopyBitsFlag layout elementType)
    (NativeCopyObserve (native.ccallCopy destReference.mem destReference.ptr_or_offset
      srcReference.mem srcReference.ptr_or_offset (JInt.wrap .i64 srcCount)) before)
    result ∧
  (0 < srcCount → srcCount ≤ destCount → NativeCopyBitsFlag layout elementType = true →
    NativeCopyBitsProtocol layout elementType native ccall dest before
      destReference srcReference srcCount result)

/-- Full same-T Array/Array domain with arbitrary physical aliasing. The
native count comes from the mathematical product of the complete source shape.
Both bits and non-bits native protocols constrain every success/error world
and divergence outcome. No native byte-copy correctness law is assumed.
Source: base/array.jl:330; base/genericmemory.jl:198-214. -/
def NativeCopyArrayArrayContract : Prop :=
  ∀ (State T V D N Mod P Sym Ref : Type)
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (before : NativeCopyWorld State) (dest src : NativeCopyArray T),
    NativeCopyArrayValid before dest → NativeCopyArrayValid before src →
    NativeCopyFullControl layout elementType native ccall dest before
      (NativeCopyArrayCount dest) (NativeCopyArrayCount src) dest.ref src.ref
      (NativeCopyObserve (nativeCopyArrayArray layout elementType native ccall dest src) before)

/-- Full same-T Array/Memory domain, without a separation assumption. The
source starts at the independently constructed zero-offset Memory reference.
Raw layout observation, signed byte-count overflow, native calls and GC ends
are included on the bits path, with every error and world preserved.
Source: base/array.jl:331; base/genericmemory.jl:198-214. -/
def NativeCopyArrayMemoryContract : Prop :=
  ∀ (State T V D N Mod P Sym Ref : Type)
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (before : NativeCopyWorld State) (dest : NativeCopyArray T) (src : NativeCopyMemory T),
    NativeCopyArrayValid before dest → NativeCopyMemoryValid before src →
    NativeCopyFullControl layout elementType native ccall dest before
      (NativeCopyArrayCount dest) src.capacity.val.toNat dest.ref (NativeCopyRefAt src 0)
      (NativeCopyObserve (nativeCopyArrayMemory layout elementType native ccall dest src) before)

/-- Full same-T Memory/Array domain, without a separation assumption. The
source Array window and destination Memory origin retain their physical address
relationship, including overlapping bytes. Both native paths constrain all
outcomes, including partial effects before layout/conversion/GC errors.
Source: base/array.jl:332; base/genericmemory.jl:198-214. -/
def NativeCopyMemoryArrayContract : Prop :=
  ∀ (State T V D N Mod P Sym Ref : Type)
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (before : NativeCopyWorld State) (dest : NativeCopyMemory T) (src : NativeCopyArray T),
    NativeCopyMemoryValid before dest → NativeCopyArrayValid before src →
    NativeCopyFullControl layout elementType native ccall dest before
      dest.capacity.val.toNat (NativeCopyArrayCount src) (NativeCopyRefAt dest 0) src.ref
      (NativeCopyObserve (nativeCopyMemoryArray layout elementType native ccall dest src) before)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Mathematical shape product, before its native 64-bit interpretation.
Later native effects may change a live shape, so negative/overflowing fields
are retained here instead of being silently truncated with Int.toNat.
Sources: base/essentials.jl:13,1296; base/array.jl:396-397. -/
def NativeLiveCardinality (dimensions : List I) : Int :=
  (dimensions.map (fun dimension => dimension.val)).prod

/-- Independent unsigned residue of a live native length. Reinterpreting this
residue as signed Int gives the same native product even if an unrestricted
native callback changes the dimensions after the initial valid-state check.
An empty tuple has count one. Sources: base/essentials.jl:13,1296. -/
def NativeLiveCountResidue (dimensions : List I) : Nat :=
  (NativeLiveCardinality dimensions % (2 : Int) ^ 64).toNat

/-- The copy request after observing a successful raw allocation. The count
is the unsigned residue of the *current* source length, while source is the
reference captured before allocation. No law relates those two observations.
Empty storage still proceeds to Core header allocation, but has no copy call.
The complete bits/non-bits protocol retains every native failure, partial
world and divergence. Sources: base/array.jl:395-397;
base/genericmemory.jl:198-214. -/
def NativeOrdinaryCopyTransfer
    (layout : LayoutBoundary (NativeCopyWorld State) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps State T) (ccall : NativeMemmove)
    (newMemory : NativeCopyMemory T) (source : NativeCopyRef T) (count : Nat)
    (before : NativeCopyWorld State)
    (copied : NativeCopyResult (NativeCopyWorld State) Unit) : Prop :=
  let destination := NativeCopyRefAt newMemory 0
  if count = 0 then
    copied = some (.ok ((), before))
  else if NativeCopyBitsFlag layout elementType then
    NativeCopyBitsProtocol layout elementType native ccall () before
      destination source count copied
  else
    copied = NativeCopyObserve
      (native.ccallCopy newMemory destination.ptr_or_offset source.mem source.ptr_or_offset
        (JInt.wrap .i64 count)) before

/-- Independent field/frame invariant of Core Array header construction. The
returned identity contains the requested reference and complete size tuple.
Every other typed header and the entire byte/native state retain the raw Core
action's effects. This checks the constructor's fields without reusing the
model's dependent-map update or assuming native identity freshness.
Source: base/array.jl:398. -/
def NativeLiveHeaderCreated (rank identity : Nat) (reference : NativeCopyRef T)
    (dimensions : List I) (afterCore after : NativeLiveWorld State T) : Prop :=
  after.bytes = afterCore.bytes ∧
  after.other.other = afterCore.other.other ∧
  (after.other.headers rank identity).reference = reference ∧
  (after.other.headers rank identity).dimensions = dimensions ∧
  ∀ otherRank key, otherRank ≠ rank ∨ key ≠ identity →
    after.other.headers otherRank key = afterCore.other.headers otherRank key

/-- A failed/diverging copy prevents header allocation. On success, the source
size tuple is observed in that post-copy world, before the raw Core header
identity action; subsequent native effects cannot replace this already-read
tuple. Native errors/divergence are propagated exactly. Successful construction
is constrained by the independent fields/frame invariant above.
Source: base/array.jl:398. -/
def NativeOrdinaryCopyFinish
    (allocation : NativeAllocationBoundary (NativeLiveState State T) T)
    (rank source : Nat) (newMemory : NativeCopyMemory T)
    (copied : NativeCopyResult (NativeLiveWorld State T) Unit)
    (result : NativeCopyResult (NativeLiveWorld State T) Nat) : Prop :=
  match copied with
  | none => result = none
  | some (.error error) => result = some (.error error)
  | some (.ok (_, afterCopy)) =>
      let dimensions := (afterCopy.other.headers rank source).dimensions
      let reference := NativeCopyRefAt newMemory 0
      match allocation.headerIdentity reference dimensions afterCopy with
      | none => result = none
      | some (.error (error, afterCore)) =>
          result = some (.error (.inr (.inr error), afterCore))
      | some (.ok (identity, afterCore)) =>
          ∃ after, result = some (.ok (identity, after)) ∧
            NativeLiveHeaderCreated rank identity reference dimensions afterCore after

/-- Independent complete ordinary-copy protocol. The initial reference and
mathematical shape determine the checked Memory request, using source Memory
metadata rather than arbitrary allocation.layout. After that native action,
the second count comes from the fresh live shape, while copying keeps the
initial reference. After copying, a fresh size read selects the Core header
fields. None of memoryUndef, nativeLiveLength, nativeOrdinaryCopy or the model's
header-update code is used to compute expected observations. No native effects
are assumed to preserve a header. Source: base/array.jl:391-399. -/
def NativeOrdinaryCopyProtocol
    (allocation : NativeAllocationBoundary (NativeLiveState State T) T)
    (layout : LayoutBoundary (NativeLiveWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeLiveState State T) T)
    (ccall : NativeMemmove) (rank source : Nat) (before : NativeLiveWorld State T)
    (result : NativeCopyResult (NativeLiveWorld State T) Nat) : Prop :=
  let initialHeader := before.other.headers rank source
  let reference := initialHeader.reference
  let metadata : MemoryLayout :=
    ⟨reference.mem.layoutBytes.val.toNat, decide (reference.mem.arrayElement = 1),
      decide (reference.mem.arrayElement = 2)⟩
  let sourceAllocation := { allocation with layout := some metadata }
  let allocated := NativeMemoryRequest sourceAllocation
    (NativeLiveCardinality initialHeader.dimensions) before
    (fun memory after => some (.ok (memory, after)))
  match allocated with
  | none => result = none
  | some (.error error) => result = some (.error error)
  | some (.ok (memory, afterAllocation)) =>
      let count := NativeLiveCountResidue
        (afterAllocation.other.headers rank source).dimensions
      ∃ copied : NativeCopyResult (NativeLiveWorld State T) Unit,
        NativeOrdinaryCopyTransfer layout elementType native ccall memory reference count
          afterAllocation copied ∧
        NativeOrdinaryCopyFinish allocation rank source memory copied result

/-- Every valid native Array rank is admitted, including empty arrays,
physical aliases, boxed/inline-pointer/union storage and wrapped-memory size
limits. The independent protocol constrains both length reads, the captured
initial reference, the post-copy size read, all allocation/copy outcomes and
the concrete final header fields. Arbitrary intervening native effects may
change the source dimensions/reference; their changes are observed at exactly
the subsequent source read. Freshness is not silently inferred from a native
identity, and byte-copy semantics remain the explicit primitive boundary.
Sources: base/array.jl:383-399; base/genericmemory.jl:198-214. -/
def NativeOrdinaryCopyContract : Prop :=
  ∀ (State T V D N Mod P Sym Ref : Type)
    (allocation : NativeAllocationBoundary (NativeLiveState State T) T)
    (layout : LayoutBoundary (NativeLiveWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeLiveState State T) T)
    (ccall : NativeMemmove) (before : NativeLiveWorld State T) (rank source : Nat),
    let initialHeader := before.other.headers rank source
    NativeCopyArrayValid before
      ⟨source, initialHeader.reference, initialHeader.dimensions⟩ →
    NativeOrdinaryCopyProtocol allocation layout elementType native ccall rank source before
      (NativeCopyObserve
        (nativeOrdinaryCopy allocation layout elementType native ccall rank source) before)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion3.PointerCopyLayoutFailures_proven : JuliaLean.Proofs.base.array.Completion3.PointerCopyLayoutFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.PointerCopyLayoutFailures
  intros
  simp only [JuliaLean.base.array.Completion3.unsafeCopyPointer]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion3.Copyto2argArguments_proven : JuliaLean.Proofs.base.array.Completion3.Copyto2argArguments := by
  unfold JuliaLean.Proofs.base.array.Completion3.Copyto2argArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.copyto2arg, JuliaLean.base.array.copyto2arg, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesCopyto1 : List JuliaLean.Registry.Entry := [
  { id := "array-copy-shared-heap", juliaFile := "base/array.jl",
    juliaFns := ["copy(a::Array)"],
    statement := "Copying a valid native array allocates a memory object distinct from every old live object, retains the element type, dimensions and every assigned or unassigned slot, and preserves every existing heap object.",
    source := "base/array.jl:391-399; Core memory allocation, memory-reference copy and array header primitives",
    status := .proven, prop := ``SharedHeapArrayCopySpec,
    thm := some ``sharedHeapArrayCopySpec}
]
def entriesCopyto2 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-copyto-alias", juliaFile := "base/array.jl",
    juliaFns := ["copyto!(::Array, ::Integer, ::Array, ::Integer, ::Integer)",
      "copyto!(::Array, ::Integer, ::Memory, ::Integer, ::Integer)",
      "copyto!(::Memory, ::Integer, ::Array, ::Integer, ::Integer)",
      "copyto!(::Array{T}, ::Integer, ::Array{T}, ::Integer, ::Integer)", "_copyto_impl!"],
    statement := "`copyto!(dest, doffs, src, soffs, n)` (array.jl:288-296 through `_copyto_impl!`; docstring at array.jl:282-287: \"Copy `n` elements from collection `src` starting at the linear index `soffs`, to array `dest` starting at the index `doffs`. Return `dest`.\") for the four Array/Memory method pairs, operands of every shape, offsets and count of any `Integer` types, and a source that may share memory with the destination: `n = 0` returns `dest` and changes nothing; a negative `n` raises `ArgumentError`; a window outside either operand raises `BoundsError`; a failed element copy raises its error; no error changes the heap. Otherwise `dest` is returned and its memory holds the copied old source window in place of its own, every other heap object unchanged.",
    source := "base/array.jl:282-287, array.jl:288-296", status := .proven,
    prop := ``CompleteCheckedCopySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayopsCopytoAlias_proven,
    notes := "" },
  { id := "array-copyto-whole", juliaFile := "base/array.jl",
    juliaFns := ["_copyto2arg!", "copyto!(::Array, ::Array)", "copyto!(::Array, ::Memory)",
      "copyto!(::Memory, ::Array)", "copyto!(::Array{T}, ::Array{T})",
      "copyto!(::Array{T}, ::Memory{T})", "copyto!(::Memory{T}, ::Array{T})"],
    statement := "`copyto!(dest, src)` for the seven Array/Memory pairs (array.jl:325-332, through `_copyto2arg!`, array.jl:323: `copyto!(dest, firstindex(dest), src, firstindex(src), length(src))`) for operands of every shape, possibly sharing memory (`copyto!` docstring in abstractarray.jl: \"Copy all elements from collection `src` to array `dest`, whose length must be greater than or equal to the length `n` of `src`. The first `n` elements of `dest` are overwritten, the other elements are left untouched.\"): when `length(src) <= length(dest)` the first `length(src)` slots of `dest` become the copied old source slots and `dest` is returned (a failed element copy raises its error); otherwise `BoundsError`; no error changes the heap.",
    source := "base/array.jl:323, array.jl:325-332", status := .proven,
    prop := ``WholeCopySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayCopytoWhole_proven,
    notes := "" }
]
def entriesCopyto3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-copy", juliaFile := "base/array.jl",
    juliaFns := ["copy(::Array)"],
    statement := "copy(::Array) propagates allocation failures with their resulting state. After successful allocation it preserves type, rank, dimensions, payload bytes and union selector bytes, including null reference representations, in a fresh Array header and fresh nonempty memory, while retaining every old live byte. Empty memories may share the runtime singleton. Sizes accepted by unsafe_wrap but rejected by the ordinary allocator retain ArgumentError.",
    source := "base/array.jl:391-399", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round6e.CopyArraySpec, thm := some ``JuliaLean.Proofs.base.array.round6e.copyArraySpec,
    notes := "" }
]
def entriesCopyto4 : List JuliaLean.Registry.Entry := [
  { id := "array-unsafe-copy-window", juliaFile := "base/array.jl",
    juliaFns := ["unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)"],
    statement := "`n == 0` returns the destination without converting offsets. For any nonzero count, a failed Int conversion of either offset or the count throws an error; otherwise, positive in-bounds windows copy the old source slots, including overlap, while preserving every other heap object. Array lengths are Int-representable.",
    source := "base/array.jl:266-280; src/genericmemory.c:65-66",
    status := .proven, prop := ``JuliaLean.Proofs.base.array.round10.UnsafeArrayCopyWindowSpec,
    thm := some ``JuliaLean.Proofs.base.array.round10.unsafeArrayCopyWindowSpec_proven,
    notes := "" }
]
def entriesCopyto5 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-unsafe-copyto-ptr", juliaFile := "base/array.jl",
    juliaFns := ["unsafe_copyto!(::Ptr{T}, ::Ptr{T}, n)"],
    statement := "Given the native stride returned by aligned_sizeof(T), BitInteger and Bool byte counts use installed wrapping multiplication with that stride. For an unmodelled Integer, multiplication may throw or return a native BitInteger or opaque Integer. An error outcome throws; native results use Csize_t conversion, opaque results use the type's conversion, and successful valid windows copy the converted byte count with other bytes unchanged.",
    source := "base/array.jl:247-264; base/runtime_internals.jl:667-688; base/int.jl:89, 1092-1100; base/cmem.jl:26-29", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round12.PointerCopySpec, thm := some ``ChatGPTBatch1.Array.MultidimcovArrayV2UnsafeCopytoPtr_proven,
    notes := "" }
]
def entriesCopyto6 : List JuliaLean.Registry.Entry := [
{ id := "array-pointer-copy-layout-failures", juliaFile := "base/array.jl",
  juliaFns := ["unsafe_copyto!(dest::Ptr{T}, src::Ptr{T}, n) where T"],
  statement := "Pointer copying determines the element stride before multiplication or the native C call. Layout errors and divergence propagate without moving bytes or evaluating count arithmetic.",
  source := "base/array.jl:259-264", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.PointerCopyLayoutFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.PointerCopyLayoutFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-copyto2arg-arguments", juliaFile := "base/array.jl",
  juliaFns := ["_copyto2arg!(dest, src)"],
  statement := "Two-argument copying observes destination firstindex, source firstindex, then source length, retaining the actual returned index/count types and all original operands.",
  source := "base/array.jl:323-323", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.Copyto2argArguments, thm := some ``JuliaLean.Proofs.base.array.Completion3.Copyto2argArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesCopyto7 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-unsafe-copyto", juliaFile := "base/array.jl", juliaFns := ["unsafe_copyto!(::Array, doffs, ::Array, soffs, n)"],
    statement := "For in-bounds windows unsafe_copyto! sets dest[doffs+k-1] to the old src[soffs+k-1] for k in 1:n (memmove semantics when src === dest) and leaves every other slot, the size and the offset unchanged.", source := "docstring base/array.jl:266", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round10.UnsafeArrayCopyWindowSpec, thm := some ``JuliaLean.Proofs.base.array.round10.unsafeArrayCopyWindowSpec_proven }
]
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesCopyto8 : List JuliaLean.Registry.Entry := [
{ id := "array-copyto-array-array-native-control",
    juliaFile := "base/array.jl", juliaFns := ["copyto!(dest::Array{T}, src::Array{T}) where {T}"],
    statement := "For every valid same-element-type Array pair at every rank, including arbitrary physical overlap, empty source is an exact no-op, short destination raises BoundsError before native effects, and success returns the original destination. Both native branches are constrained by independent mathematical counts and addresses. Non-bits storage reaches its native copy request; bits storage observes raw layout, checked byte-count conversion, memmove and ordered GC ends, preserving every error, partial state and divergence.",
    source := "base/array.jl:330; base/genericmemory.jl:198-214", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.NativeCopyArrayArrayContract,
    thm := none,
    notes := "Complete native protocol contract for both branches, not native byte-copy correctness. Raw layout observations and MinimalAlignedWord specify stride independently; mathematical residues specify addresses/counts. C/GC boundaries have no assumed laws; no disjointness premise." },
  { id := "array-copyto-array-memory-native-control",
    juliaFile := "base/array.jl", juliaFns := ["copyto!(dest::Array{T}, src::Memory{T}) where {T}"],
    statement := "For every valid same-element-type Array destination and Memory source, including arbitrary physical overlap, empty source is an exact no-op, short destination raises BoundsError before native effects, and success returns the original destination. Both native branches use the independent count and Memory origin. The bits protocol includes raw layout, signed-byte-count rejection, memmove and ordered GC ends; every success, error, partial state and divergence is constrained.",
    source := "base/array.jl:331; base/genericmemory.jl:198-214", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.NativeCopyArrayMemoryContract,
    thm := none,
    notes := "Protocol for both native branches. Raw layout failure/divergence, mathematical byte-count conversion, memmove and GC-end outcomes are constrained without a native correctness law. General Integer and mixed-element offset methods remain unclaimed specialized dependencies." },
  { id := "array-copyto-memory-array-native-control",
    juliaFile := "base/array.jl", juliaFns := ["copyto!(dest::Memory{T}, src::Array{T}) where {T}"],
    statement := "For every valid same-element-type Memory destination and Array source at every rank, including arbitrary physical overlap, empty source is an exact no-op, short destination raises BoundsError before native effects, and success returns the original destination. Both native branches use independent counts and physical addresses from the Array window to the Memory origin. The bits protocol includes raw layout, signed-byte-count rejection, memmove and ordered GC ends, retaining every error, partial state and divergence.",
    source := "base/array.jl:332; base/genericmemory.jl:198-214", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.NativeCopyMemoryArrayContract,
    thm := none,
    notes := "Protocol for both native branches. All native layouts and overlap relationships remain admitted. Valid power-of-two alignment fixes the stride residue; malformed native metadata remains covered by the existing MinimalAlignedWord relation. Native byte/GC correctness is outside this property." },
{ id := "array-copy-array-native-shape-protocol",
    juliaFile := "base/array.jl", juliaFns := ["copy(a::Array)"],
    statement := "For every valid native Array at every rank, copy captures the initial source reference, uses the initial shape for checked Memory allocation, rereads its current length after allocation, and rereads its current shape after copying. Independent mathematical counts and native-copy observations constrain all errors, mutations and divergence. A successful Core header action installs exactly the captured final fields at its returned identity and preserves every other header and raw native effect; no callback-preservation or freshness law is assumed.",
    source := "base/array.jl:383-399; base/boot.jl:762; src/genericmemory.c:55-102; base/genericmemory.jl:198-214",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.NativeOrdinaryCopyContract,
    thm := none,
    notes := "Complete Base composition at existing native allocation/copy/GC/Core-header boundaries, using a shared rank-typed mutable header store. No ordinary-copy callback, allocator law, success premise, non-overlap restriction or all-unassigned surrogate. Native header freshness and byte-copy correctness remain the named primitive boundaries; the property does not assume them." }
]
end JuliaLean.Proofs.base.array

