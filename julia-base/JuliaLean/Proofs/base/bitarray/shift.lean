import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.bitarray.common.count
import JuliaLean.Proofs.base.bitarray.common.shift

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Nonnegative signed left shifts dispatch to the unsigned left shift. -/
theorem shiftLeftNonnegativeDispatch (B : BitVector) (i : I64)
    (hi : int 0 ≤ i) :
    bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i =
      Round5.Round2.shiftLeftUnsignedModel B (JuliaLean.base.int.unsigned i) := by
  simp only [bitVectorShiftLeftSigned, id_eq, hi, ite_true]

/-- Negative signed left shifts use the magnitude interpreted as unsigned. -/
theorem shiftLeftNegativeDispatch (B : BitVector) (i : I64)
    (hi : ¬ int 0 ≤ i) :
    bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i =
      Round5.Round2.shiftRightUnsignedModel B (JuliaLean.base.int.unsigned (-i)) := by
  simp only [bitVectorShiftLeftSigned, id_eq, hi, ite_false,
    Round5.Round2.shiftRightSignedArgModel]

/-- Nonnegative signed right shifts dispatch to the unsigned right shift. -/
theorem shiftRightNonnegativeDispatch (B : BitVector) (i : I64)
    (hi : int 0 ≤ i) :
    bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i =
      Round5.Round2.shiftRightUnsignedModel B (JuliaLean.base.int.unsigned i) := by
  simp only [bitVectorShiftRightSigned, id_eq, hi, ite_true]

/-- Negative signed right shifts use the magnitude interpreted as unsigned. -/
theorem shiftRightNegativeDispatch (B : BitVector) (i : I64)
    (hi : ¬ int 0 ≤ i) :
    bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i =
      Round5.Round2.shiftLeftUnsignedModel B (JuliaLean.base.int.unsigned (-i)) := by
  simp only [bitVectorShiftRightSigned, id_eq, hi, ite_false,
    Round5.Round2.shiftLeftSignedArgModel]

/-- Zero unsigned left shifts follow the public copying path. -/
theorem shiftLeftZeroDispatch (B : BitVector) :
    Round5.Round2.shiftLeftUnsignedModel B (u64 0) =
      Round5.Round2.copyBitVectorPublic B := by
  simp only [Round5.Round2.shiftLeftUnsignedModel, bitVectorShiftLeftUnsigned,
    beq_self_eq_true, ite_true]

/-- Zero unsigned right shifts follow the public copying path. -/
theorem shiftRightZeroDispatch (B : BitVector) :
    Round5.Round2.shiftRightUnsignedModel B (u64 0) =
      Round5.Round2.copyBitVectorPublic B := by
  simp only [Round5.Round2.shiftRightUnsignedModel, bitVectorShiftRightUnsigned,
    beq_self_eq_true, ite_true]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The exact single-word copy formula with independent source and destination words. -/
def shiftSingleCopyWord (destination sourceWord : U64) (dest source count : Nat) : U64 :=
  let keep := rangeSingleKeep dest count
  let selected := and_int (shl_int u64Max (int source))
    (not_int (shl_int u64Max (int ((source + count : Nat) : Int))))
  or_int (and_int destination keep)
    (and_int (shl_int (lshr_int (and_int sourceWord selected) (int source)) (int dest)) (not_int keep))

/-- One-chunk copying has exact source-offset semantics and preserves other positions. -/
theorem shiftSingleCopyBit (destination sourceWord : U64) (dest source count bit : Nat)
    (hd : dest + count ≤ 64) (hs : source + count ≤ 64) (hb : bit < 64) :
    packedBit (shiftSingleCopyWord destination sourceWord dest source count) bit =
      if dest ≤ bit ∧ bit < dest + count then packedBit sourceWord (bit - dest + source)
      else packedBit destination bit := by
  simp only [shiftSingleCopyWord, packedBit_or, dequePackedAnd,
    rangeSingleKeepBit dest count bit hd hb, scalar_packedBit_not _ bit hb]
  by_cases hi : dest ≤ bit ∧ bit < dest + count
  · have hout : ¬ (bit < dest ∨ dest + count ≤ bit) := by omega
    simp only [hi, hout, decide_false, Bool.not_false, Bool.and_false,
      Bool.and_true, Bool.false_or, ite_true]
    rw [reversePackedLeft _ dest bit (by omega) hb, if_pos hi.1,
      dequePackedShiftRight _ source (bit - dest) (by omega)]
    simp only [show bit - dest < 64 by omega, decide_true, Bool.true_and]
    rw [dequePackedAnd, dequePackedAnd, scalar_packedBit_not _ _ (by omega),
      rangeSingleHighMaskBit _ _ (by omega) (by omega),
      rangeSingleHighMaskBit _ _ hs (by omega)]
    simp only [show source ≤ bit - dest + source by omega,
      show ¬ source + count ≤ bit - dest + source by omega,
      decide_true, decide_false, Bool.not_false, Bool.true_and, Bool.and_true, and_self, ite_true]
  · have hout : bit < dest ∨ dest + count ≤ bit := by omega
    simp only [hi, hout, decide_true, Bool.not_true, Bool.and_false, Bool.and_true,
      Bool.or_false, ite_false]

/-- The frozen forward copier executes its exact one-word formula for an overlapping leftward copy. -/
theorem shiftSingleCopyRun (destinationHandle sourceHandle dest source count : Nat) (s out : State)
    (destination sourceWord : U64) (hsep : destinationHandle ≠ sourceHandle)
    (hp : 0 < count) (hd : dest + count ≤ 64) (hs : source + count ≤ 64)
    (hg : (mutableGet sourceHandle (int 1)).run s = (.ok sourceWord, s))
    (hgd : (mutableGet destinationHandle (int 1)).run s = (.ok destination, s))
    (hw : (mutableSet destinationHandle (shiftSingleCopyWord destination sourceWord dest source count) (int 1)).run s =
      (.ok (), out)) :
    (copyChunks destinationHandle (int ((dest + 1 : Nat) : Int)) sourceHandle
      (int ((source + 1 : Nat) : Int)) (int count)).run s = (.ok (), out) := by
  have hz : (int count == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val count (by omega)] at hv
    change (count : Int) = 0 at hv
    omega
  have hforward : ¬ (destinationHandle = sourceHandle ∧ int ((dest + 1 : Nat) : Int) > int ((source + 1 : Nat) : Int)) :=
    fun he => hsep he.1
  have hstartD := rangeSingleAddress dest (by omega)
  have hstartS := rangeSingleAddress source (by omega)
  have hendD : int ((dest + 1 : Nat) : Int) + int count - int 1 = int ((dest + count : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hendS : int ((source + 1 : Nat) : Int) + int count - int 1 = int ((source + count : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hlastD : getChunksId (int ((dest + count : Nat) : Int)) =
      (int 1, int ((dest + count - 1 : Nat) : Int)) := by
    have h := rangeSingleAddress (dest + count - 1) (by omega)
    rw [show dest + count - 1 + 1 = dest + count by omega] at h
    exact h
  have hlastS : getChunksId (int ((source + count : Nat) : Int)) =
      (int 1, int ((source + count - 1 : Nat) : Int)) := by
    have h := rangeSingleAddress (source + count - 1) (by omega)
    rw [show source + count - 1 + 1 = source + count by omega] at h
    exact h
  have hincD : int ((dest + count - 1 : Nat) : Int) + int 1 = int ((dest + count : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hincS : int ((source + count - 1 : Nat) : Int) + int 1 = int ((source + count : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, hforward, dite_false,
    hendD, hendS, hstartD, hstartS, hlastD, hlastS,
    show (int 1 - int 1 == int 0) = true from rfl, ite_true, hincD, hincS,
    glueSrcBitChunks, shape_run_bind, hg, hgd,
    show ¬ (int 1 > int 1 ∧ int source > int 0) from by intro h; exact (by decide : ¬ int 1 > int 1) h.1,
    shape_run_pure]
  simp only [shiftSingleCopyWord, rangeSingleKeep] at hw
  rw [hw]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A known initialized first slot can be read through any valid one-based header. -/
theorem shiftSingle_read_first (s : State) (handle mem : Nat) (n : I64) (word : U64)
    (tail : List (Option U64))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some (some word :: tail)) (hn : 1 ≤ n.val) :
    (mutableGet handle (int 1)).run s = (.ok word, s) := by
  have hb : 1 ≤ (int 1).val ∧ int 1 ≤ n := ⟨by decide, hn⟩
  simp only [mutableGet, mutableVector, memoryRead, shape_run_bind, shape_run_get,
    ha, hm, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

/-- A known writable first slot is replaced without modifying its vector header. -/
theorem shiftSingle_store_first (s : State) (handle mem : Nat) (n : I64)
    (old : Option U64) (tail : List (Option U64)) (word : U64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some (old :: tail)) (hn : 1 ≤ n.val) :
    (mutableSet handle word (int 1)).run s =
      (.ok (), {s with memories := s.memories.set mem (some word :: tail)}) := by
  have hb : one ≤ int 1 ∧ int 1 ≤ n := ⟨by decide, hn⟩
  have hmBound : 1 ≤ (int 1).val ∧ (int 1).val ≤ ((old :: tail).length : Int) := by
    change 1 ≤ 1 ∧ 1 ≤ ((old :: tail).length : Int)
    simp only [List.length_cons]
    omega
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_one_add_sub_one, memoryWrite, memoryRead, shape_run_get, hm,
    hmBound, shape_run_modify]
  rfl

/-- Extend an existing heap with one initialized destination word. -/
def shiftSingle_extend (s : State) (word : U64) : State :=
  ⟨s.memories ++ [[some word]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩

/-- The new destination header points to the newly appended one-word memory. -/
theorem shiftSingle_extend_header (s : State) (word : U64) :
    (shiftSingle_extend s word).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), int 1⟩ := by
  simp only [shiftSingle_extend, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

/-- The new destination memory has exactly its one initialized word. -/
theorem shiftSingle_extend_memory (s : State) (word : U64) :
    (shiftSingle_extend s word).memories[s.memories.length]? = some [some word] := by
  simp only [shiftSingle_extend, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

/-- Reading the appended destination returns its current packed word. -/
theorem shiftSingle_extend_read (s : State) (word : U64) :
    (mutableGet s.arrays.length (int 1)).run (shiftSingle_extend s word) =
      (.ok word, shiftSingle_extend s word) :=
  shiftSingle_read_first _ _ _ _ _ [] (shiftSingle_extend_header s word) (shiftSingle_extend_memory s word) (by decide)

/-- Replacing the destination word retains the entire preexisting heap. -/
theorem shiftSingle_extend_store (s : State) (old word : U64) :
    (mutableSet s.arrays.length word (int 1)).run (shiftSingle_extend s old) =
      (.ok (), shiftSingle_extend s word) := by
  rw [shiftSingle_store_first _ _ _ _ _ [] word (shiftSingle_extend_header s old)
    (shiftSingle_extend_memory s old) (by decide)]
  simp only [shiftSingle_extend, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

/-- Appending a destination preserves every initialized source first word. -/
theorem shiftSingle_extend_source (s : State) (destination source : U64) (handle mem : Nat)
    (n : I64) (tail : List (Option U64)) (hh : handle < s.arrays.length) (hm : mem < s.memories.length)
    (hheader : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hmemory : s.memories[mem]? = some (some source :: tail)) (hn : 1 ≤ n.val) :
    (mutableGet handle (int 1)).run (shiftSingle_extend s destination) =
      (.ok source, shiftSingle_extend s destination) := by
  apply shiftSingle_read_first _ handle mem n source tail _ _ hn
  · simpa only [shiftSingle_extend, List.getElem?_append_left hh] using hheader
  · simpa only [shiftSingle_extend, List.getElem?_append_left hm] using hmemory

/-- Allocating one fresh chunk appends one unassigned slot and its one-based header. -/
theorem shiftSingle_allocate_chunk (s : State) :
    (allocateChunkVectorModel 1).run s =
      (.ok s.arrays.length,
        ⟨s.memories ++ [[none]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩) := by
  rfl

/-- Checked multiplication by one preserves every one-word logical length. -/
theorem shiftSingle_checked_one (count : Nat) (hcount : count ≤ 64) :
    JuliaLean.base.checked.checkedMulBits (int 1) (int count) = .ok (int count) := by
  have h : ∀ count : Fin 65,
      JuliaLean.base.checked.checkedMulBits (int 1) (int count.val) = .ok (int count.val) := by decide
  exact h ⟨count, by omega⟩

/-- Checked singleton dimensions compute the single requested length unchanged. -/
theorem shiftSingle_checked_dims (count : Nat) (hcount : count ≤ 64) (s : State) :
    (checkedDimensionsModel [int count]).run s = (.ok (int count), s) := by
  simp only [checkedDimensionsModel, List.forIn_cons, List.forIn_nil, checkedMultiplyMutation,
    shiftSingle_checked_one count hcount, shape_run_bind, shape_run_pure]

/-- Every positive length at most 64 uses exactly one storage chunk. -/
theorem shiftSingle_num_chunks (count : Nat) (hpos : 0 < count) (hcount : count ≤ 64) :
    numBitChunks (int count) = int 1 := by
  have h : ∀ count : Fin 64,
      numBitChunks (int ((count.val + 1 : Nat) : Int)) = int 1 := by decide
  have h' := h ⟨count - 1, by omega⟩
  simpa only [show count - 1 + 1 = count by omega] using h'

/-- Single-word constructor execution separates validation, allocation, and initialization. -/
theorem shiftSingle_construct_single {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (n : I64) (s allocated initialized : State) (handle : Nat)
    (hneg : ¬ n.val < 0) (hchecked : (checked [n]).run s = (.ok n, s))
    (hcount : numBitChunks n = int 1)
    (hallocate : (allocate 1).run s = (.ok handle, allocated))
    (hwrite : (mutableSet handle (u64 0) (int 1)).run allocated = (.ok (), initialized)) :
    (BitArrayUndef (N := N) checked allocate [n]).run s =
      (.ok ⟨handle, n, [n]⟩, initialized) := by
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hneg, ite_false,
    shape_run_bind, shape_run_pure, hchecked, hcount,
    show (int 1).val.toNat = 1 from rfl, hallocate,
    show (int 1).val > 0 from by decide, ite_true, hwrite]

/-- Public BitVector allocation for a positive one-word length initializes its sole destination word to zero. -/
theorem shiftSingle_allocate_single (count : Nat) (hpos : 0 < count) (hcount : count ≤ 64) (s : State) :
    (Round5.Round2.allocateBitArrayModel (N := 1) [int count]).run s =
      (.ok (⟨s.arrays.length, int count, [int count]⟩ : BitVector), shiftSingle_extend s (u64 0)) := by
  have hneg : ¬ (int count).val < 0 := by rw [packedInt_val count (by omega)]; omega
  have ha : (s.arrays ++ [⟨(s.memories.length, one), int 1⟩])[s.arrays.length]? =
      some (⟨(s.memories.length, one), int 1⟩ : MutableVector) := by
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hm : (s.memories ++ [[none]])[s.memories.length]? = some [none] := by
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hwrite := shiftSingle_store_first
    (⟨s.memories ++ [[none]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩ : State)
    s.arrays.length s.memories.length (int 1) none [] (u64 0) ha hm (by decide)
  simp only [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero] at hwrite
  exact shiftSingle_construct_single checkedDimensionsModel allocateChunkVectorModel (int count) s _ _
    s.arrays.length hneg (shiftSingle_checked_dims count hcount s) (shiftSingle_num_chunks count hpos hcount)
    (shiftSingle_allocate_chunk s) hwrite



/-- The appended destination exposes its sole initialized chunk. -/
theorem shiftSingle_extend_contents (s : State) (word : U64) :
    (shiftSingle_extend s word).contents s.arrays.length = [some word] := by
  simp only [MutableMemory.contents, shiftSingle_extend_header, shiftSingle_extend_memory]
  rfl

/-- The appended one-word header has native length one. -/
theorem shiftSingle_extend_length (s : State) (word : U64) :
    (mutableLength s.arrays.length).run (shiftSingle_extend s word) =
      (.ok (int 1), shiftSingle_extend s word) := by
  simp only [mutableLength, mutableMemoryref, mutableRef, shape_run_bind,
    shape_vector_run, shiftSingle_extend_header, shape_run_pure]

/-- Filling the sole destination chunk with zero performs exactly one store. -/
theorem shiftSingle_fill_chunks_zero (s : State) (word : U64) :
    (Round5.Round2.fillChunkVectorModel s.arrays.length (u64 0)).run (shiftSingle_extend s word) =
      (.ok (), shiftSingle_extend s (u64 0)) := by
  apply fillChunkVectorFrom s.arrays.length (u64 0) (int 1) _ _ (shiftSingle_extend_length s word)
  rw [endPop_range_singleton]
  simp only [List.forIn_cons, List.forIn_nil, shape_run_bind,
    shiftSingle_extend_store, shape_run_pure]

/-- The public false constructor composes allocation and filling without inspecting either action. -/
theorem shiftSingleFalseConstruct {N : Nat}
    (allocate : List I64 → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N))
    (n : I64) (B result : BitArray N) (s allocated out : State)
    (ha : (allocate [n]).run s = (.ok B, allocated))
    (hf : (fill B false).run allocated = (.ok result, out)) :
    (falsesIntegerDims allocate fill [n]).run s = (.ok result, out) := by
  simp only [falsesIntegerDims, shape_run_bind, ha, hf]

/-- The public all-false constructor allocates one zero-filled destination chunk. -/
theorem shiftSingle_zero_vector (n : Nat) (hp : 0 < n) (hn : n ≤ 64) (s : State) :
    (Round5.Round2.zeroBitVectorModel (int n)).run s =
      (.ok (⟨s.arrays.length, int n, [int n]⟩ : BitVector), shiftSingle_extend s (u64 0)) := by
  have ha := shiftSingle_allocate_single n hp hn s
  have hc := dequeConvertOk false false (shiftSingle_extend s (u64 0)) rfl
  have hf := fillFalseFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
    (⟨s.arrays.length, int n, [int n]⟩ : BitArray 1) false
    (shiftSingle_extend s (u64 0)) (shiftSingle_extend s (u64 0)) hc
    (fillPositiveLength n hp (by omega)) (shiftSingle_fill_chunks_zero s (u64 0))
  exact shiftSingleFalseConstruct Round5.Round2.allocateBitArrayModel
    (fun B value => fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B value)
    (int n) _ _ s _ _ ha hf
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Logical left shifts preserve vector length for all shift counts. -/
theorem shiftSingleLeftLength (xs : List Bool) (count : Nat) :
    (shiftLeftBits xs count).length = xs.length := by
  unfold shiftLeftBits
  split
  · simp only [List.length_replicate]
  · simp only [List.length_append, List.length_drop, List.length_replicate]
    omega

/-- Logical right shifts preserve vector length for all shift counts. -/
theorem shiftSingleRightLength (xs : List Bool) (count : Nat) :
    (shiftRightBits xs count).length = xs.length := by
  unfold shiftRightBits
  split
  · simp only [List.length_replicate]
  · simp only [List.length_append, List.length_take, List.length_replicate,
      Nat.min_eq_left (show xs.length - count ≤ xs.length by omega)]
    omega

/-- A partial left shift reads the remaining suffix and false-fills every vacated position. -/
theorem shiftSingleLeftGet (xs : List Bool) (count bit : Nat) (hc : count < xs.length) :
    (shiftLeftBits xs count).getD bit false =
      if bit < xs.length - count then xs.getD (count + bit) false else false := by
  rw [shiftLeftBits, if_neg (by omega)]
  by_cases hb : bit < xs.length - count
  · rw [if_pos hb, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp only [List.length_drop]; exact hb), List.getElem?_drop]
    rfl
  · rw [if_neg hb, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp only [List.length_drop]; omega)]
    exact shiftSingleFalseGet _ _

/-- A partial right shift false-fills its prefix and reads the retained source prefix. -/
theorem shiftSingleRightGet (xs : List Bool) (count bit : Nat) (hc : count < xs.length) :
    (shiftRightBits xs count).getD bit false =
      if count ≤ bit ∧ bit < xs.length then xs.getD (bit - count) false else false := by
  rw [shiftRightBits, if_neg (by omega)]
  by_cases hb : bit < count
  · rw [if_neg (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp only [List.length_replicate]; exact hb)]
    exact shiftSingleFalseGet count bit
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp only [List.length_replicate]; omega), List.length_replicate]
    by_cases hi : bit < xs.length
    · rw [if_pos (by omega), List.getElem?_take_of_lt (by omega)]
      rfl
    · rw [if_neg (by omega), List.getElem?_take_eq_none (by omega)]
      rfl

/-- Copying a suffix to bit zero in a zero-filled word implements logical left shift. -/
theorem shiftSingleCopyLeft (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hn : xs.length ≤ 64) :
    shiftSingleCopyWord (u64 0) (packedPrefix xs 0 64) 0 count (xs.length - count) =
      packedPrefix (shiftLeftBits xs count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [shiftSingleCopyBit _ _ _ _ _ bit (by omega) (by omega) hb,
    packedWord_bit (shiftLeftBits xs count) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.zero_le, true_and]
  rw [shiftSingleLeftGet xs count bit hc]
  by_cases hi : bit < xs.length - count
  · rw [if_pos hi, if_pos hi, packedWord_bit xs 0 (bit + count) (by omega)]
    simp only [Nat.zero_mul, Nat.zero_add]
    congr 1
    omega
  · rw [if_neg hi, if_neg hi, packedBit_zero]

/-- Copying a prefix upward in a zero-filled word implements logical right shift. -/
theorem shiftSingleCopyRight (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hn : xs.length ≤ 64) :
    shiftSingleCopyWord (u64 0) (packedPrefix xs 0 64) count 0 (xs.length - count) =
      packedPrefix (shiftRightBits xs count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [shiftSingleCopyBit _ _ _ _ _ bit (by omega) (by omega) hb,
    packedWord_bit (shiftRightBits xs count) 0 bit hb]
  simp only [Nat.zero_add, Nat.add_zero, Nat.zero_mul]
  have hsum : count + (xs.length - count) = xs.length := by omega
  rw [hsum, shiftSingleRightGet xs count bit hc]
  by_cases hi : count ≤ bit ∧ bit < xs.length
  · rw [if_pos hi, if_pos hi, packedWord_bit xs 0 (bit - count) (by omega)]
    simp only [Nat.zero_mul, Nat.zero_add]
  · rw [if_neg hi, if_neg hi, packedBit_zero]

/-- The zero-count left shift is the original list. -/
theorem shiftSingleLeftZero (xs : List Bool) : shiftLeftBits xs 0 = xs := by
  unfold shiftLeftBits
  by_cases hz : xs = []
  · subst xs
    rfl
  · have hp : 0 < xs.length := List.length_pos_iff.mpr hz
    rw [if_neg (by omega)]
    simp only [List.drop_zero, List.replicate_zero, List.append_nil]

/-- The zero-count right shift is the original list. -/
theorem shiftSingleRightZero (xs : List Bool) : shiftRightBits xs 0 = xs := by
  unfold shiftRightBits
  by_cases hz : xs = []
  · subst xs
    rfl
  · have hp : 0 < xs.length := List.length_pos_iff.mpr hz
    rw [if_neg (by omega)]
    simp only [List.replicate_zero, List.nil_append, Nat.sub_zero, List.take_length]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- An allocated destination preserves the original one-chunk source word. -/
theorem shiftSingleSourceRead (xs : List Bool) (destination : U64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    (mutableGet 0 (int 1)).run (shiftSingle_extend (initWords (encodeBits xs)) destination) =
      (.ok (packedPrefix xs 0 64), shiftSingle_extend (initWords (encodeBits xs)) destination) := by
  rw [rangeSingleEncoding xs hp hn]
  exact shiftSingle_extend_source (initWords [packedPrefix xs 0 64]) destination
    (packedPrefix xs 0 64) 0 0 (int 1) (List.replicate 32 none)
    (by change 0 < 1; decide) (by change 0 < 1; decide) rfl rfl (by decide)

/-- An allocated destination preserves the original source's one-word length. -/
theorem shiftSingleSourceLength (xs : List Bool) (destination : U64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    (mutableLength 0).run (shiftSingle_extend (initWords (encodeBits xs)) destination) =
      (.ok (int 1), shiftSingle_extend (initWords (encodeBits xs)) destination) := by
  rw [rangeSingleEncoding xs hp hn]
  exact shiftSingleLengthFrom _ 0 0 (int 1) rfl

/-- A positive unsigned left shift composes zero allocation with its suffix copy. -/
theorem shiftSingleLeftFrom (asUInt : I64 → U64) (asInt : U64 → I64)
    (copy : BitVector → BitMutationM BitVector) (falses : I64 → BitMutationM BitVector)
    (B A : BitVector) (i : U64) (s allocated out : State)
    (hz : (i == u64 0) = false) (hi : asUInt B.len > i)
    (ha : (falses B.len).run s = (.ok A, allocated))
    (hc : (copyChunks A.chunks (int 1) B.chunks (asInt i + int 1) (B.len - asInt i)).run allocated =
      (.ok (), out)) :
    (bitVectorShiftLeftUnsigned asUInt asInt copy falses B i).run s = (.ok A, out) := by
  simp only [bitVectorShiftLeftUnsigned, hz, Bool.false_eq_true, ite_false, shape_run_bind,
    ha, hi, ite_true, hc, shape_run_pure]

/-- A positive unsigned right shift composes zero allocation with its prefix copy. -/
theorem shiftSingleRightFrom (asUInt : I64 → U64) (asInt : U64 → I64)
    (copy : BitVector → BitMutationM BitVector) (falses : I64 → BitMutationM BitVector)
    (B A : BitVector) (i : U64) (s allocated out : State)
    (hz : (i == u64 0) = false) (hi : asUInt B.len > i)
    (ha : (falses B.len).run s = (.ok A, allocated))
    (hc : (copyChunks A.chunks (asInt i + int 1) B.chunks (int 1) (B.len - asInt i)).run allocated =
      (.ok (), out)) :
    (bitVectorShiftRightUnsigned asUInt asInt copy falses B i).run s = (.ok A, out) := by
  simp only [bitVectorShiftRightUnsigned, hz, Bool.false_eq_true, ite_false, shape_run_bind,
    ha, hi, ite_true, hc, shape_run_pure]

/-- A left shift at least as long as the input returns the allocated all-false vector. -/
theorem shiftSingleLeftLargeFrom (asUInt : I64 → U64) (asInt : U64 → I64)
    (copy : BitVector → BitMutationM BitVector) (falses : I64 → BitMutationM BitVector)
    (B A : BitVector) (i : U64) (s out : State)
    (hz : (i == u64 0) = false) (hi : ¬ asUInt B.len > i)
    (ha : (falses B.len).run s = (.ok A, out)) :
    (bitVectorShiftLeftUnsigned asUInt asInt copy falses B i).run s = (.ok A, out) := by
  simp only [bitVectorShiftLeftUnsigned, hz, Bool.false_eq_true, ite_false, shape_run_bind,
    ha, hi, shape_run_pure]

/-- A right shift at least as long as the input returns the allocated all-false vector. -/
theorem shiftSingleRightLargeFrom (asUInt : I64 → U64) (asInt : U64 → I64)
    (copy : BitVector → BitMutationM BitVector) (falses : I64 → BitMutationM BitVector)
    (B A : BitVector) (i : U64) (s out : State)
    (hz : (i == u64 0) = false) (hi : ¬ asUInt B.len > i)
    (ha : (falses B.len).run s = (.ok A, out)) :
    (bitVectorShiftRightUnsigned asUInt asInt copy falses B i).run s = (.ok A, out) := by
  simp only [bitVectorShiftRightUnsigned, hz, Bool.false_eq_true, ite_false, shape_run_bind,
    ha, hi, shape_run_pure]

/-- Equal-size one-word copying transfers the sole source chunk directly. -/
theorem shiftSingleCopytoFrom (B A : BitArray 1) (word : U64) (s out : State)
    (hlen : B.len = A.len)
    (hld : (mutableLength A.chunks).run s = (.ok (int 1), s))
    (hls : (mutableLength B.chunks).run s = (.ok (int 1), s))
    (hg : (mutableGet B.chunks (int 1)).run s = (.ok word, s))
    (hw : (mutableSet A.chunks word (int 1)).run s = (.ok (), out)) :
    (bitArrayCopyto A B).run s = (.ok A, out) := by
  have hn : ¬ B.len > A.len := by rw [hlen]; exact Int.lt_irrefl _
  have he : (B.len == A.len) = true := by rw [hlen]; exact beq_self_eq_true _
  simp only [bitArrayCopyto, hn, ite_false, shape_run_bind, hld, hls,
    show ¬ int 1 < int 1 from by decide,
    show (int 1 == int 0) = false from rfl, Bool.false_eq_true,
    show intRange (int 1) (int 1 - int 1) = [] from rfl,
    List.forIn_nil, shape_run_pure, he, ite_true, hg, hw]

/-- Public copying composes allocation and the installed copy-to operation. -/
theorem shiftSinglePublicCopyFrom (B A : BitArray 1) (s allocated out : State)
    (ha : (Round5.Round2.allocateBitArrayModel B.dims).run s = (.ok A, allocated))
    (hc : (bitArrayCopyto A B).run allocated = (.ok A, out)) :
    (Round5.Round2.copyBitVectorPublic B).run s = (.ok A, out) := by
  simp only [Round5.Round2.copyBitVectorPublic, JuliaLean.base.abstractarray.copyMutableArray,
    JuliaLean.base.bitarray.similarBitArray, shape_run_bind, ha, hc]

/-- A zero shift's public copy creates one independent word with exactly the source contents. -/
theorem shiftSingleCopyCanonical (xs : List Bool) (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    (Round5.Round2.copyBitVectorPublic (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftSingle_extend (initWords (encodeBits xs)) (packedPrefix xs 0 64)) := by
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have ha : (Round5.Round2.allocateBitArrayModel (vectorBits xs).dims).run s =
      (.ok A, shiftSingle_extend s (u64 0)) := shiftSingle_allocate_single xs.length hp hn s
  apply shiftSinglePublicCopyFrom (vectorBits xs) A s (shiftSingle_extend s (u64 0)) _ ha
  apply shiftSingleCopytoFrom (vectorBits xs) A (packedPrefix xs 0 64) _ _ rfl
  · exact shiftSingle_extend_length s (u64 0)
  · exact shiftSingleSourceLength xs (u64 0) hp hn
  · exact shiftSingleSourceRead xs (u64 0) hp hn
  · exact shiftSingle_extend_store s (u64 0) (packedPrefix xs 0 64)

/-- Unsigned reinterpretation preserves a nonnegative single-word logical length. -/
theorem shiftSingleUnsignedLength (n : Nat) (hn : n ≤ 64) :
    (JuliaLean.base.int.unsigned (int n)).val = n := by
  rw [JuliaLean.Proofs.base.int.unsigned_val, packedInt_val n (by omega)]
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ 18446744073709551615
  omega

/-- An unsigned value is exactly the natural number obtained from its nonnegative value. -/
theorem shiftSingleUnsignedNat (i : U64) : ((i.val.toNat : Nat) : Int) = i.val := by
  have h := i.property
  change 0 ≤ i.val ∧ i.val ≤ 18446744073709551615 at h
  exact Int.toNat_of_nonneg h.1

/-- The zero natural unsigned count is the native zero word. -/
theorem shiftSingleUnsignedZero (i : U64) (hz : i.val.toNat = 0) : i = u64 0 := by
  apply Subtype.ext
  have h := shiftSingleUnsignedNat i
  rw [hz] at h
  exact h.symm

/-- A positive natural unsigned count is distinct from native zero. -/
theorem shiftSingleUnsignedNonzero (i : U64) (hp : 0 < i.val.toNat) : (i == u64 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro he
  subst i
  exact (Nat.lt_irrefl 0) hp

/-- A partial one-word unsigned left shift installs the exact encoded shifted list. -/
theorem shiftSingleLeftPartial (xs : List Bool) (i : U64)
    (hp : 0 < i.val.toNat) (hi : i.val.toNat < xs.length) (hn : xs.length ≤ 64) :
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftSingle_extend (initWords (encodeBits xs))
          (packedPrefix (shiftLeftBits xs i.val.toNat) 0 64)) := by
  let s := initWords (encodeBits xs)
  let n := i.val.toNat
  have hncast : (n : Int) = i.val := shiftSingleUnsignedNat i
  have hcast : int i.val = int n := congrArg int hncast.symm
  have hsum : int n + int 1 = int ((n + 1 : Nat) : Int) := by rw [packedInt_add]; rfl
  have hdiff : int xs.length - int n = int ((xs.length - n : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hcmp : JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftSingleUnsignedLength xs.length hn, ← hncast]
    omega
  have ha := shiftSingle_zero_vector xs.length (by omega) hn s
  have hr := shiftSingleCopyRun 1 0 0 n (xs.length - n)
    (shiftSingle_extend s (u64 0))
    (shiftSingle_extend s (shiftSingleCopyWord (u64 0) (packedPrefix xs 0 64) 0 n (xs.length - n)))
    (u64 0) (packedPrefix xs 0 64) (by decide) (by omega) (by omega) (by omega)
    (shiftSingleSourceRead xs (u64 0) (by omega) hn)
    (shiftSingle_extend_read s (u64 0))
    (shiftSingle_extend_store s (u64 0) _)
  rw [shiftSingleCopyLeft xs n hi hn] at hr
  apply shiftSingleLeftFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
    Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
    (vectorBits xs) (⟨1, int xs.length, [int xs.length]⟩ : BitVector) i s _ _
    (shiftSingleUnsignedNonzero i hp) hcmp ha
  change (copyChunks 1 (int 1) 0 (int i.val + int 1) (int xs.length - int i.val)).run _ = _
  rw [hcast, hsum, hdiff]
  simpa only [Nat.zero_add, Int.ofNat_one] using hr

/-- A partial one-word unsigned right shift installs the exact encoded shifted list. -/
theorem shiftSingleRightPartial (xs : List Bool) (i : U64)
    (hp : 0 < i.val.toNat) (hi : i.val.toNat < xs.length) (hn : xs.length ≤ 64) :
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftSingle_extend (initWords (encodeBits xs))
          (packedPrefix (shiftRightBits xs i.val.toNat) 0 64)) := by
  let s := initWords (encodeBits xs)
  let n := i.val.toNat
  have hncast : (n : Int) = i.val := shiftSingleUnsignedNat i
  have hcast : int i.val = int n := congrArg int hncast.symm
  have hsum : int n + int 1 = int ((n + 1 : Nat) : Int) := by rw [packedInt_add]; rfl
  have hdiff : int xs.length - int n = int ((xs.length - n : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hcmp : JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftSingleUnsignedLength xs.length hn, ← hncast]
    omega
  have ha := shiftSingle_zero_vector xs.length (by omega) hn s
  have hr := shiftSingleCopyRun 1 0 n 0 (xs.length - n)
    (shiftSingle_extend s (u64 0))
    (shiftSingle_extend s (shiftSingleCopyWord (u64 0) (packedPrefix xs 0 64) n 0 (xs.length - n)))
    (u64 0) (packedPrefix xs 0 64) (by decide) (by omega) (by omega) (by omega)
    (shiftSingleSourceRead xs (u64 0) (by omega) hn)
    (shiftSingle_extend_read s (u64 0))
    (shiftSingle_extend_store s (u64 0) _)
  rw [shiftSingleCopyRight xs n hi hn] at hr
  apply shiftSingleRightFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
    Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
    (vectorBits xs) (⟨1, int xs.length, [int xs.length]⟩ : BitVector) i s _ _
    (shiftSingleUnsignedNonzero i hp) hcmp ha
  change (copyChunks 1 (int i.val + int 1) 0 (int 1) (int xs.length - int i.val)).run _ = _
  rw [hcast, hsum, hdiff]
  simpa only [Nat.zero_add, Int.ofNat_one] using hr

/-- Every unsigned left-shift count, including zero and oversized counts, is correct on a nonempty single chunk. -/
theorem shiftSingleLeftCanonical (xs : List Bool) (i : U64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftSingle_extend (initWords (encodeBits xs))
          (packedPrefix (shiftLeftBits xs i.val.toNat) 0 64)) := by
  by_cases hz : i.val.toNat = 0
  · have he := shiftSingleUnsignedZero i hz
    subst i
    rw [show (u64 0).val.toNat = 0 from rfl, shiftSingleLeftZero]
    simp only [Round5.Round2.shiftLeftUnsignedModel, bitVectorShiftLeftUnsigned,
      beq_self_eq_true, ite_true]
    exact shiftSingleCopyCanonical xs hp hn
  · have hi : 0 < i.val.toNat := by omega
    by_cases hsmall : i.val.toNat < xs.length
    · exact shiftSingleLeftPartial xs i hi hsmall hn
    · have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
        change ¬ i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
        rw [shiftSingleUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
        omega
      rw [shiftLeftBits, if_pos (by omega), shiftSingleFalseWord]
      exact shiftSingleLeftLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
        Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
        (vectorBits xs) _ i _ _ (shiftSingleUnsignedNonzero i hi) hcmp
        (shiftSingle_zero_vector xs.length hp hn _)

/-- Every unsigned right-shift count, including zero and oversized counts, is correct on a nonempty single chunk. -/
theorem shiftSingleRightCanonical (xs : List Bool) (i : U64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftSingle_extend (initWords (encodeBits xs))
          (packedPrefix (shiftRightBits xs i.val.toNat) 0 64)) := by
  by_cases hz : i.val.toNat = 0
  · have he := shiftSingleUnsignedZero i hz
    subst i
    rw [show (u64 0).val.toNat = 0 from rfl, shiftSingleRightZero]
    simp only [Round5.Round2.shiftRightUnsignedModel, bitVectorShiftRightUnsigned,
      beq_self_eq_true, ite_true]
    exact shiftSingleCopyCanonical xs hp hn
  · have hi : 0 < i.val.toNat := by omega
    by_cases hsmall : i.val.toNat < xs.length
    · exact shiftSingleRightPartial xs i hi hsmall hn
    · have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
        change ¬ i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
        rw [shiftSingleUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
        omega
      rw [shiftRightBits, if_pos (by omega), shiftSingleFalseWord]
      exact shiftSingleRightLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
        Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
        (vectorBits xs) _ i _ _ (shiftSingleUnsignedNonzero i hi) hcmp
        (shiftSingle_zero_vector xs.length hp hn _)

/-- Nonnegative signed shift counts reinterpret to their mathematical magnitude. -/
theorem shiftSingleNonnegativeMagnitude (i : I64) (hi : 0 ≤ i.val) :
    (JuliaLean.base.int.unsigned i).val.toNat = i.val.natAbs := by
  have he := JuliaLean.Proofs.base.int.pattern_unsigned_count i hi
  rw [JuliaLean.Proofs.base.int.pattern_of_unsigned (by rfl)] at he
  have ha := Int.natAbs_of_nonneg hi
  omega

/-- Negating then reinterpreting a negative count gives its magnitude even at the minimum native Int. -/
theorem shiftSingleNegativeMagnitude (i : I64) (hi : ¬ 0 ≤ i.val) :
    (JuliaLean.base.int.unsigned (-i)).val.toNat = i.val.natAbs := by
  have he := JuliaLean.Proofs.base.int.pattern_unsigned_neg_count i hi
  rw [JuliaLean.Proofs.base.int.pattern_of_unsigned (by rfl)] at he
  have ha := Int.ofNat_natAbs_of_nonpos (show i.val ≤ 0 by omega)
  have hneg : JuliaLean.base.int.neg i = -i := by
    apply Subtype.ext
    exact JuliaLean.Proofs.base.int.neg_int_val i
  rw [hneg] at he
  omega

/-- Both signed shifts dispatch to the correct unsigned direction for every native count. -/
theorem shiftSingleSignedRuns (xs : List Bool) (i : I64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i).run s =
        (.ok A, shiftSingle_extend s (packedPrefix
          (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) 0 64)) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i).run s =
        (.ok A, shiftSingle_extend s (packedPrefix
          (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) 0 64)) := by
  dsimp only
  by_cases hi : 0 ≤ i.val
  · have hc := shiftSingleNonnegativeMagnitude i hi
    have hl := shiftSingleLeftCanonical xs (JuliaLean.base.int.unsigned i) hp hn
    have hr := shiftSingleRightCanonical xs (JuliaLean.base.int.unsigned i) hp hn
    rw [hc] at hl hr
    have hcond : i ≥ int 0 := hi
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq,
      hcond, hi, ite_true]
    exact ⟨hl, hr⟩
  · have hc := shiftSingleNegativeMagnitude i hi
    have hl := shiftSingleLeftCanonical xs (JuliaLean.base.int.unsigned (-i)) hp hn
    have hr := shiftSingleRightCanonical xs (JuliaLean.base.int.unsigned (-i)) hp hn
    rw [hc] at hl hr
    have hcond : ¬ i ≥ int 0 := hi
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq,
      hcond, hi, ite_false, Round5.Round2.shiftLeftSignedArgModel, Round5.Round2.shiftRightSignedArgModel]
    exact ⟨hr, hl⟩

/-- Every encoded one-word destination has the requested logical values and invariant. -/
theorem shiftSingleObservations (s : State) (xs : List Bool) (B : BitArray 1)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64)
    (hc : B.chunks = s.arrays.length) (hl : B.len = int xs.length) :
    bitValues (shiftSingle_extend s (packedPrefix xs 0 64)) B = xs ∧
      Round5.Round2.PackedInvariant (shiftSingle_extend s (packedPrefix xs 0 64)) B := by
  have hcontents : (shiftSingle_extend s (packedPrefix xs 0 64)).contents B.chunks =
      (encodeBits xs).map some := by
    rw [hc, shiftSingle_extend_contents, rangeSingleEncoding xs hp hn]
    rfl
  exact ⟨scalar_bitValues_contents _ B xs (by omega) hl hcontents,
    scalar_invariant_of_contents _ B xs (by omega) hl hcontents⟩

/-- Both signed-shift results are logically correct and zero-padded for every nonempty single-chunk input. -/
theorem shiftSingleSignedCorrect (xs : List Bool) (i : I64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    ∃ A leftState rightState,
      (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, leftState) ∧
      (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, rightState) ∧
      bitValues leftState A = (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) ∧
      bitValues rightState A = (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) ∧
      Round5.Round2.PackedInvariant leftState A ∧ Round5.Round2.PackedInvariant rightState A := by
  let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
  let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have hl : left.length = xs.length := by
    unfold left
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hr : right.length = xs.length := by
    unfold right
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hol := shiftSingleObservations s left A (by rw [hl]; exact hp) (by rw [hl]; exact hn) rfl
    (by change int xs.length = int left.length; rw [hl])
  have hor := shiftSingleObservations s right A (by rw [hr]; exact hp) (by rw [hr]; exact hn) rfl
    (by change int xs.length = int right.length; rw [hr])
  have hrun := shiftSingleSignedRuns xs i hp hn
  exact ⟨A, shiftSingle_extend s (packedPrefix left 0 64), shiftSingle_extend s (packedPrefix right 0 64),
    hrun.1, hrun.2, hol.1, hor.1, hol.2, hor.2⟩

/-- The frozen signed-shift contract holds for every native count on a nonempty one-chunk vector. -/
theorem BitarraysShift_nonemptySingleChunk (xs : List Bool) (i : I64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) : Round5.Round2.ShiftAgrees xs i := by
  obtain ⟨A, leftState, rightState, hl, hr, hvl, hvr, _, _⟩ := shiftSingleSignedCorrect xs i hp hn
  unfold Round5.Round2.ShiftAgrees
  dsimp only
  rw [hl, hr]
  exact ⟨hvl, hvr⟩

/-- The zero-dimensional constructor composes checked dimensions with empty allocation. -/
theorem shiftEmptyConstructorFrom
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (s out : State) (handle : Nat)
    (hc : (checked [int 0]).run s = (.ok (int 0), s))
    (ha : (allocate 0).run s = (.ok handle, out)) :
    (BitArrayUndef (N := 1) checked allocate [int 0]).run s =
      (.ok ⟨handle, int 0, [int 0]⟩, out) := by
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil,
    show ¬ (int 0).val < 0 from by decide, ite_false, shape_run_bind, shape_run_pure, hc,
    show numBitChunks (int 0) = int 0 from rfl, show (int 0).val.toNat = 0 from rfl,
    ha, show ¬ (int 0).val > 0 from by decide]

/-- Public empty-vector allocation creates exactly the fresh empty store. -/
theorem shiftEmptyAllocate (s : State) :
    (Round5.Round2.allocateBitArrayModel (N := 1) [int 0]).run s =
      (.ok ⟨s.arrays.length, int 0, [int 0]⟩, shiftEmptyExtend s) := by
  have ha : (allocateChunkVectorModel 0).run s = (.ok s.arrays.length, shiftEmptyExtend s) := rfl
  exact shiftEmptyConstructorFrom checkedDimensionsModel allocateChunkVectorModel s _ s.arrays.length
    (shiftSingle_checked_dims 0 (by decide) s) ha

/-- Public false construction of length zero allocates no visible words. -/
theorem shiftEmptyZeroVector (s : State) :
    (Round5.Round2.zeroBitVectorModel (int 0)).run s =
      (.ok (⟨s.arrays.length, int 0, [int 0]⟩ : BitVector), shiftEmptyExtend s) := by
  have ha := shiftEmptyAllocate s
  have hc := dequeConvertOk false false (shiftEmptyExtend s) rfl
  have hf := fillEmptyFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
    (⟨s.arrays.length, int 0, [int 0]⟩ : BitArray 1) false false (shiftEmptyExtend s) hc rfl
  exact shiftSingleFalseConstruct Round5.Round2.allocateBitArrayModel
    (fun B value => fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B value)
    (int 0) _ _ s _ _ ha hf

/-- Copying equal-size empty chunk vectors returns before reading any word. -/
theorem shiftEmptyCopytoFrom (A B : BitArray 1) (s : State)
    (he : B.len = A.len)
    (hd : (mutableLength A.chunks).run s = (.ok (int 0), s))
    (hs : (mutableLength B.chunks).run s = (.ok (int 0), s)) :
    (bitArrayCopyto A B).run s = (.ok A, s) := by
  have hlen : ¬ B.len > A.len := by rw [he]; exact Int.lt_irrefl _
  simp only [bitArrayCopyto, hlen, ite_false, shape_run_bind, hd, hs,
    show ¬ int 0 < int 0 from by decide, beq_self_eq_true, ite_true, shape_run_pure]

/-- Public copying of the empty input creates an independent empty result. -/
theorem shiftEmptyCopy :
    (Round5.Round2.copyBitVectorPublic (vectorBits [])).run (initWords (encodeBits [])) =
      (.ok (⟨1, int 0, [int 0]⟩ : BitVector), shiftEmptyExtend (initWords (encodeBits []))) := by
  let s := initWords (encodeBits [])
  let A : BitArray 1 := ⟨1, int 0, [int 0]⟩
  apply shiftSinglePublicCopyFrom (vectorBits []) A s (shiftEmptyExtend s) _ (shiftEmptyAllocate s)
  apply shiftEmptyCopytoFrom A (vectorBits []) (shiftEmptyExtend s) rfl
  · exact shiftSingleLengthFrom (shiftEmptyExtend s) 1 1 (int 0) (shiftEmptyHeader s)
  · exact shiftSingleLengthFrom (shiftEmptyExtend s) 0 0 (int 0) rfl

/-- Every unsigned left count gives the same empty public result on the empty input. -/
theorem shiftEmptyLeft (i : U64) :
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits []) i).run (initWords (encodeBits [])) =
      (.ok (⟨1, int 0, [int 0]⟩ : BitVector), shiftEmptyExtend (initWords (encodeBits []))) := by
  by_cases hz : i = u64 0
  · subst i
    simp only [Round5.Round2.shiftLeftUnsignedModel, bitVectorShiftLeftUnsigned,
      beq_self_eq_true, ite_true]
    exact shiftEmptyCopy
  · have hbeq : (i == u64 0) = false := beq_eq_false_iff_ne.mpr hz
    have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits []).len > i := by
      change ¬ i.val < 0
      have hi := i.property
      change 0 ≤ i.val ∧ i.val ≤ 18446744073709551615 at hi
      omega
    exact shiftSingleLeftLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits []) _ i _ _ hbeq hcmp (shiftEmptyZeroVector _)

/-- Every unsigned right count gives the same empty public result on the empty input. -/
theorem shiftEmptyRight (i : U64) :
    (Round5.Round2.shiftRightUnsignedModel (vectorBits []) i).run (initWords (encodeBits [])) =
      (.ok (⟨1, int 0, [int 0]⟩ : BitVector), shiftEmptyExtend (initWords (encodeBits []))) := by
  by_cases hz : i = u64 0
  · subst i
    simp only [Round5.Round2.shiftRightUnsignedModel, bitVectorShiftRightUnsigned,
      beq_self_eq_true, ite_true]
    exact shiftEmptyCopy
  · have hbeq : (i == u64 0) = false := beq_eq_false_iff_ne.mpr hz
    have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits []).len > i := by
      change ¬ i.val < 0
      have hi := i.property
      change 0 ≤ i.val ∧ i.val ≤ 18446744073709551615 at hi
      omega
    exact shiftSingleRightLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits []) _ i _ _ hbeq hcmp (shiftEmptyZeroVector _)

/-- Signed dispatch retains the empty result for all Int values, including both endpoints. -/
theorem shiftEmptySignedRuns (i : I64) :
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
      (vectorBits []) i).run (initWords (encodeBits [])) =
        (.ok (⟨1, int 0, [int 0]⟩ : BitVector), shiftEmptyExtend (initWords (encodeBits []))) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
      (vectorBits []) i).run (initWords (encodeBits [])) =
        (.ok (⟨1, int 0, [int 0]⟩ : BitVector), shiftEmptyExtend (initWords (encodeBits []))) := by
  by_cases h : i ≥ int 0
  · simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, h, ite_true]
    exact ⟨shiftEmptyLeft _, shiftEmptyRight _⟩
  · simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, h, ite_false,
      Round5.Round2.shiftLeftSignedArgModel, Round5.Round2.shiftRightSignedArgModel]
    exact ⟨shiftEmptyRight _, shiftEmptyLeft _⟩

/-- The frozen signed-shift assertion holds for the empty input at every native shift count. -/
theorem BitarraysShift_empty (i : I64) : Round5.Round2.ShiftAgrees [] i := by
  have hr := shiftEmptySignedRuns i
  unfold Round5.Round2.ShiftAgrees
  dsimp only
  rw [hr.1, hr.2]
  have hz : bitValues (shiftEmptyExtend (initWords (encodeBits [])))
      (⟨1, int 0, [int 0]⟩ : BitVector) = [] := rfl
  simp only [hz, shiftLeftBits, shiftRightBits, List.length_nil, Nat.zero_le, ite_true,
    List.replicate_zero, ite_self]
  exact ⟨True.intro, True.intro⟩

/-- Empty shifted outputs also satisfy the exact packed-count and zero-padding invariant. -/
theorem shiftEmptyInvariant (s : State) :
    Round5.Round2.PackedInvariant (shiftEmptyExtend s)
      (⟨s.arrays.length, int 0, [int 0]⟩ : BitArray 1) := by
  apply scalar_invariant_of_contents _ _ [] (by decide) rfl
  exact shiftEmptyContents s

/-- The frozen signed-shift contract holds for every single-chunk input, including empty vectors and all native counts. -/
theorem BitarraysShift_singleChunk (xs : List Bool) (i : I64) (hn : xs.length ≤ 64) :
    Round5.Round2.ShiftAgrees xs i := by
  by_cases hz : xs = []
  · subst xs
    exact BitarraysShift_empty i
  · exact BitarraysShift_nonemptySingleChunk xs i (List.length_pos_iff.mpr hz) hn

/-- A known initialized second slot can be read through an arbitrary valid header. -/
theorem shiftPairReadSecond (s : State) (handle mem : Nat) (n : I64)
    (first : Option U64) (word : U64) (tail : List (Option U64))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some (first :: some word :: tail)) (hn : 2 ≤ n.val) :
    (mutableGet handle (int 2)).run s = (.ok word, s) := by
  have hb : 1 ≤ (int 2).val ∧ int 2 ≤ n := ⟨by decide, hn⟩
  simp only [mutableGet, mutableVector, memoryRead, shape_run_bind, shape_run_get,
    ha, hm, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

/-- Replacing a second slot preserves the first slot and every vector header. -/
theorem shiftPairStoreSecond (s : State) (handle mem : Nat) (n : I64)
    (first old : Option U64) (tail : List (Option U64)) (word : U64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some (first :: old :: tail)) (hn : 2 ≤ n.val) :
    (mutableSet handle word (int 2)).run s =
      (.ok (), {s with memories := s.memories.set mem (first :: some word :: tail)}) := by
  have hb : one ≤ int 2 ∧ int 2 ≤ n := ⟨by decide, hn⟩
  have hmBound : 1 ≤ (int 2).val ∧ (int 2).val ≤ ((first :: old :: tail).length : Int) := by
    change 1 ≤ 2 ∧ 2 ≤ ((first :: old :: tail).length : Int)
    simp only [List.length_cons]
    omega
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_one_add_sub_one, memoryWrite, memoryRead, shape_run_get, hm,
    hmBound, shape_run_modify]
  rfl

/-- An appended two-word destination, allowing either slot to remain unspecified during allocation. -/
def shiftPairHeap (s : State) (low high : Option U64) : State :=
  ⟨s.memories ++ [[low, high]], s.arrays ++ [⟨(s.memories.length, one), int 2⟩]⟩

/-- A fully initialized appended two-word destination. -/
def shiftPairExtend (s : State) (low high : U64) : State := shiftPairHeap s (some low) (some high)

theorem shiftPairHeader (s : State) (low high : Option U64) :
    (shiftPairHeap s low high).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), int 2⟩ := by
  simp only [shiftPairHeap, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem shiftPairMemory (s : State) (low high : Option U64) :
    (shiftPairHeap s low high).memories[s.memories.length]? = some [low, high] := by
  simp only [shiftPairHeap, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem shiftPairDestLow (s : State) (low : U64) (high : Option U64) :
    (mutableGet s.arrays.length (int 1)).run (shiftPairHeap s (some low) high) =
      (.ok low, shiftPairHeap s (some low) high) :=
  shiftSingle_read_first _ _ _ _ low [high] (shiftPairHeader s (some low) high)
    (shiftPairMemory s (some low) high) (by decide)

theorem shiftPairDestHigh (s : State) (low : Option U64) (high : U64) :
    (mutableGet s.arrays.length (int 2)).run (shiftPairHeap s low (some high)) =
      (.ok high, shiftPairHeap s low (some high)) :=
  shiftPairReadSecond _ _ _ _ low high [] (shiftPairHeader s low (some high))
    (shiftPairMemory s low (some high)) (by decide)

theorem shiftPairWriteLow (s : State) (low high : Option U64) (word : U64) :
    (mutableSet s.arrays.length word (int 1)).run (shiftPairHeap s low high) =
      (.ok (), shiftPairHeap s (some word) high) := by
  rw [shiftSingle_store_first _ _ _ _ low [high] word (shiftPairHeader s low high)
    (shiftPairMemory s low high) (by decide)]
  simp only [shiftPairHeap, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

theorem shiftPairWriteHigh (s : State) (low high : Option U64) (word : U64) :
    (mutableSet s.arrays.length word (int 2)).run (shiftPairHeap s low high) =
      (.ok (), shiftPairHeap s low (some word)) := by
  rw [shiftPairStoreSecond _ _ _ _ low high [] word (shiftPairHeader s low high)
    (shiftPairMemory s low high) (by decide)]
  simp only [shiftPairHeap, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

/-- Allocation leaves the earlier source's low chunk untouched. -/
theorem shiftPairSourceLow (xs : List Bool) (low high : Option U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (mutableGet 0 (int 1)).run (shiftPairHeap (initWords (encodeBits xs)) low high) =
      (.ok (packedPrefix xs 0 64), shiftPairHeap (initWords (encodeBits xs)) low high) := by
  rw [copyPairEncoding xs hp hn]
  exact shiftSingle_read_first _ 0 0 (int 2) (packedPrefix xs 0 64)
    (some (packedPrefix xs 1 64) :: List.replicate 32 none) rfl rfl (by decide)

/-- Allocation leaves the earlier source's high chunk untouched. -/
theorem shiftPairSourceHigh (xs : List Bool) (low high : Option U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (mutableGet 0 (int 2)).run (shiftPairHeap (initWords (encodeBits xs)) low high) =
      (.ok (packedPrefix xs 1 64), shiftPairHeap (initWords (encodeBits xs)) low high) := by
  rw [copyPairEncoding xs hp hn]
  exact shiftPairReadSecond _ 0 0 (int 2) (some (packedPrefix xs 0 64)) (packedPrefix xs 1 64)
    (List.replicate 32 none) rfl rfl (by decide)

theorem shiftPairDestLength (s : State) (low high : Option U64) :
    (mutableLength s.arrays.length).run (shiftPairHeap s low high) =
      (.ok (int 2), shiftPairHeap s low high) :=
  shiftSingleLengthFrom _ _ _ _ (shiftPairHeader s low high)

theorem shiftPairSourceLength (xs : List Bool) (low high : Option U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (mutableLength 0).run (shiftPairHeap (initWords (encodeBits xs)) low high) =
      (.ok (int 2), shiftPairHeap (initWords (encodeBits xs)) low high) := by
  rw [copyPairEncoding xs hp hn]
  exact shiftSingleLengthFrom _ 0 0 (int 2) rfl

/-- The appended two-word header exposes exactly the two initialized output chunks. -/
theorem shiftPairContents (s : State) (low high : U64) :
    (shiftPairExtend s low high).contents s.arrays.length = [some low, some high] := by
  simp only [shiftPairExtend, MutableMemory.contents, shiftPairHeader, shiftPairMemory]
  rfl

/-- Checked multiplication by one returns every representable native integer unchanged. -/
theorem shiftPairCheckedOne (n : I64) :
    JuliaLean.base.checked.checkedMulBits (int 1) n = .ok n := by
  have h := JuliaLean.Proofs.base.checked.mulExact .i64 (int 1) n
  have hproduct : (int 1).val * n.val = n.val := by change 1 * n.val = n.val; omega
  have hin : IntTy.i64.min ≤ (int 1).val * n.val ∧ (int 1).val * n.val ≤ IntTy.i64.max := by
    rw [hproduct]
    exact n.property
  unfold JuliaLean.Proofs.base.checked.ExactOrOverflow at h
  rw [if_pos hin] at h
  obtain ⟨value, hrun, hvalue⟩ := h
  have he : value = n := Subtype.ext (hvalue.trans hproduct)
  exact hrun.trans (congrArg Except.ok he)

/-- Checked singleton dimensions preserve every native length. -/
theorem shiftPairCheckedDims (n : Nat) (s : State) :
    (checkedDimensionsModel [int n]).run s = (.ok (int n), s) := by
  simp only [checkedDimensionsModel, List.forIn_cons, List.forIn_nil, checkedMultiplyMutation,
    shiftPairCheckedOne (int n), shape_run_bind, shape_run_pure]

/-- A two-word constructor separates checked dimensions, allocation, and its final-word initialization. -/
theorem shiftPairConstruct {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (n : I64) (s allocated initialized : State) (handle : Nat)
    (hneg : ¬ n.val < 0) (hchecked : (checked [n]).run s = (.ok n, s))
    (hcount : numBitChunks n = int 2)
    (hallocate : (allocate 2).run s = (.ok handle, allocated))
    (hwrite : (mutableSet handle (u64 0) (int 2)).run allocated = (.ok (), initialized)) :
    (BitArrayUndef (N := N) checked allocate [n]).run s =
      (.ok ⟨handle, n, [n]⟩, initialized) := by
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hneg, ite_false,
    shape_run_bind, shape_run_pure, hchecked, hcount,
    show (int 2).val.toNat = 2 from rfl, hallocate,
    show (int 2).val > 0 from by decide, ite_true, hwrite]

/-- Two-chunk allocation initializes its final chunk and reserves its still-unspecified first chunk. -/
theorem shiftPairAllocate (n : Nat) (hp : 64 < n) (hn : n ≤ 128) (s : State) :
    (Round5.Round2.allocateBitArrayModel (N := 1) [int n]).run s =
      (.ok (⟨s.arrays.length, int n, [int n]⟩ : BitVector), shiftPairHeap s none (some (u64 0))) := by
  have ha : (allocateChunkVectorModel 2).run s =
      (.ok s.arrays.length, shiftPairHeap s none none) := by rfl
  exact shiftPairConstruct checkedDimensionsModel allocateChunkVectorModel (int n) s _ _ s.arrays.length
    (by rw [packedInt_val n (by omega)]; omega) (shiftPairCheckedDims n s)
    (rangePairChunkCount n hp hn) ha (shiftPairWriteHigh s none none (u64 0))

/-- Filling two appended chunks with false initializes both words and preserves the earlier heap. -/
theorem shiftPairFillZero (s : State) (low high : Option U64) :
    (Round5.Round2.fillChunkVectorModel s.arrays.length (u64 0)).run (shiftPairHeap s low high) =
      (.ok (), shiftPairExtend s (u64 0) (u64 0)) := by
  apply fillChunkVectorFrom s.arrays.length (u64 0) (int 2) _ _ (shiftPairDestLength s low high)
  rw [show intRange (int 1) (int 2) = [int 1, int 2] from rfl]
  simp only [List.forIn_cons, List.forIn_nil, shape_run_bind, shiftPairWriteLow, shiftPairWriteHigh, shape_run_pure]
  rfl

/-- The public false constructor returns an independent fully initialized two-word vector. -/
theorem shiftPairZeroVector (n : Nat) (hp : 64 < n) (hn : n ≤ 128) (s : State) :
    (Round5.Round2.zeroBitVectorModel (int n)).run s =
      (.ok (⟨s.arrays.length, int n, [int n]⟩ : BitVector), shiftPairExtend s (u64 0) (u64 0)) := by
  have ha := shiftPairAllocate n hp hn s
  have hc := dequeConvertOk false false (shiftPairHeap s none (some (u64 0))) rfl
  have hf := fillFalseFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
    (⟨s.arrays.length, int n, [int n]⟩ : BitArray 1) false
    (shiftPairHeap s none (some (u64 0))) (shiftPairExtend s (u64 0) (u64 0)) hc
    (fillPositiveLength n (by omega) (by omega)) (shiftPairFillZero s none (some (u64 0)))
  exact shiftSingleFalseConstruct Round5.Round2.allocateBitArrayModel
    (fun B value => fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B value)
    (int n) _ _ s _ _ ha hf
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Pasting zero positions leaves the destination word unchanged. -/
theorem copyPairPasteEmpty (destination aligned : U64) (offset : Nat) (ho : offset ≤ 64) :
    copyPairPaste destination aligned offset 0 = destination := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ offset 0 bit (by omega) hb, if_neg (by omega)]

/-- The low boundary write implements exactly the low word of a partial logical left shift. -/
theorem shiftPairLeftLow (xs : List Bool) (count : Nat)
    (hc : count < xs.length) :
    copyPairPaste (u64 0) (copyPairSlice xs count) 0 (min (xs.length - count) 64) =
      packedPrefix (shiftLeftBits xs count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb, packedWord_bit (shiftLeftBits xs count) 0 bit hb]
  simp only [Nat.zero_le, Nat.zero_add, Nat.zero_mul, Nat.sub_zero, true_and]
  rw [shiftSingleLeftGet xs count bit hc]
  by_cases hi : bit < xs.length - count
  · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs count bit hb]
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]

/-- The high boundary write implements exactly the high word of a partial logical left shift. -/
theorem shiftPairLeftHigh (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hn : xs.length ≤ 128) :
    copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64) =
      packedPrefix (shiftLeftBits xs count) 1 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb, packedWord_bit (shiftLeftBits xs count) 1 bit hb]
  simp only [Nat.zero_le, Nat.zero_add, Nat.one_mul, Nat.sub_zero, true_and]
  rw [shiftSingleLeftGet xs count (64 + bit) hc]
  by_cases hi : 64 + bit < xs.length - count
  · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs (count + 64) bit hb]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]

/-- Every packed word of an all-false logical list is zero. -/
theorem shiftPairFalseWord (n chunk : Nat) : packedPrefix (List.replicate n false) chunk 64 = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ chunk bit hb, shiftSingleFalseGet, packedBit_zero]

/-- The first source word gathered for a prefix copy, respecting the possible early endpoint. -/
def shiftPairRightFirst (xs : List Bool) (kept : Nat) : U64 :=
  if kept ≤ 64 then packedPrefix (xs.take kept) 0 64 else packedPrefix xs 0 64

/-- The second gathered prefix word is present exactly when the copied prefix crosses the chunk boundary. -/
def shiftPairRightNext (xs : List Bool) (kept : Nat) : U64 :=
  if kept ≤ 64 then u64 0 else packedPrefix xs 1 64

/-- Every requested bit of the first gathered prefix word is the corresponding original logical bit. -/
theorem shiftPairRightFirstBit (xs : List Bool) (kept bit : Nat) (hk : bit < kept) (hb : bit < 64) :
    packedBit (shiftPairRightFirst xs kept) bit = xs.getD bit false := by
  unfold shiftPairRightFirst
  split
  · rw [packedWord_bit _ 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  · rw [packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]

/-- The two gathered prefix words produce the exact high-destination carry bits. -/
theorem shiftPairRightCarryBit (xs : List Bool) (kept offset bit : Nat)
    (ho : offset ≤ 64) (hb : bit < 64) (hi : 64 + bit - offset < kept) :
    packedBit (copyPairCarry (shiftPairRightFirst xs kept) (shiftPairRightNext xs kept) offset) bit =
      xs.getD (64 + bit - offset) false := by
  rw [copyPairCarry, packedBit_or, copyPairRightBit _ (64 - offset) bit (by omega) hb,
    reversePackedLeft _ offset bit ho hb]
  by_cases hl : bit < offset
  · rw [if_pos (by omega), if_neg (by omega), shiftPairRightFirstBit xs kept (bit + (64 - offset)) (by omega) (by omega), Bool.or_false]
    congr 1
    omega
  · rw [if_neg (by omega), if_pos (by omega)]
    have hk : ¬ kept ≤ 64 := by omega
    rw [shiftPairRightNext, if_neg hk, packedWord_bit xs 1 (bit - offset) (by omega), Bool.false_or]
    simp only [Nat.one_mul]
    congr 1
    omega

/-- A low-word prefix paste is the exact low word of a right shift by less than one word. -/
theorem shiftPairRightLow (xs : List Bool) (count : Nat)
    (hc : count < 64) (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    copyPairPaste (u64 0) (shiftPairRightFirst xs (xs.length - count)) count (64 - count) =
      packedPrefix (shiftRightBits xs count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ count _ bit (by omega) hb, packedWord_bit (shiftRightBits xs count) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [shiftSingleRightGet xs count bit (by omega)]
  by_cases hi : count ≤ bit
  · rw [if_pos (by omega), if_pos (by omega), shiftPairRightFirstBit xs (xs.length - count) (bit - count) (by omega) (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), packedBit_zero]

/-- The high carry paste is the exact high word of a right shift by less than one word. -/
theorem shiftPairRightHigh (xs : List Bool) (count : Nat)
    (hc : count < 64) (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    copyPairPaste (u64 0)
      (copyPairCarry (shiftPairRightFirst xs (xs.length - count)) (shiftPairRightNext xs (xs.length - count)) count)
      0 (xs.length - 64) = packedPrefix (shiftRightBits xs count) 1 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb, packedWord_bit (shiftRightBits xs count) 1 bit hb]
  simp only [Nat.one_mul, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  rw [shiftSingleRightGet xs count (64 + bit) (by omega)]
  by_cases hi : 64 + bit < xs.length
  · rw [if_pos (by omega), if_pos (by omega), shiftPairRightCarryBit xs (xs.length - count) count bit (by omega) hb (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), packedBit_zero]

/-- Shifting right by at least one word clears every low destination bit. -/
theorem shiftPairRightLargeLow (xs : List Bool) (count : Nat) (hc : 64 ≤ count) (hl : count < xs.length) :
    packedPrefix (shiftRightBits xs count) 0 64 = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ 0 bit hb, packedBit_zero]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [shiftSingleRightGet xs count bit hl, if_neg (by omega)]

/-- The one remaining high-destination paste implements a right shift of at least one word. -/
theorem shiftPairRightLargeHigh (xs : List Bool) (count : Nat)
    (hc : 64 ≤ count) (hl : count < xs.length) (hn : xs.length ≤ 128) :
    copyPairPaste (u64 0) (shiftPairRightFirst xs (xs.length - count)) (count - 64) (xs.length - count) =
      packedPrefix (shiftRightBits xs count) 1 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ (count - 64) _ bit (by omega) hb, packedWord_bit (shiftRightBits xs count) 1 bit hb]
  simp only [Nat.one_mul]
  rw [shiftSingleRightGet xs count (64 + bit) hl]
  by_cases hi : count ≤ 64 + bit ∧ 64 + bit < xs.length
  · rw [if_pos hi, if_pos (by omega), shiftPairRightFirstBit xs (xs.length - count) (bit - (count - 64)) (by omega) (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Equal-size two-word copying writes both source chunks to the independent destination. -/
theorem shiftPairCopytoFrom (B A : BitArray 1) (low high : U64) (s mid out : State)
    (hlen : B.len = A.len)
    (hld : (mutableLength A.chunks).run s = (.ok (int 2), s))
    (hls : (mutableLength B.chunks).run s = (.ok (int 2), s))
    (hr0 : (mutableGet B.chunks (int 1)).run s = (.ok low, s))
    (hw0 : (mutableSet A.chunks low (int 1)).run s = (.ok (), mid))
    (hr1 : (mutableGet B.chunks (int 2)).run mid = (.ok high, mid))
    (hw1 : (mutableSet A.chunks high (int 2)).run mid = (.ok (), out)) :
    (bitArrayCopyto A B).run s = (.ok A, out) := by
  have hn : ¬ B.len > A.len := by rw [hlen]; exact Int.lt_irrefl _
  have he : (B.len == A.len) = true := by rw [hlen]; exact beq_self_eq_true _
  simp only [bitArrayCopyto, hn, ite_false, shape_run_bind, hld, hls,
    show ¬ int 2 < int 2 from by decide,
    show (int 2 == int 0) = false from rfl, Bool.false_eq_true,
    show intRange (int 1) (int 2 - int 1) = [int 1] from rfl,
    List.forIn_cons, List.forIn_nil, shape_run_pure, he, ite_true, hr0, hw0, hr1, hw1]

/-- A zero shift copies both packed source words into independent storage. -/
theorem shiftPairCopyCanonical (xs : List Bool) (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (Round5.Round2.copyBitVectorPublic (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftPairExtend (initWords (encodeBits xs)) (packedPrefix xs 0 64) (packedPrefix xs 1 64)) := by
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have ha : (Round5.Round2.allocateBitArrayModel (vectorBits xs).dims).run s =
      (.ok A, shiftPairHeap s none (some (u64 0))) := shiftPairAllocate xs.length hp hn s
  apply shiftSinglePublicCopyFrom (vectorBits xs) A s (shiftPairHeap s none (some (u64 0))) _ ha
  exact shiftPairCopytoFrom (vectorBits xs) A (packedPrefix xs 0 64) (packedPrefix xs 1 64)
    (shiftPairHeap s none (some (u64 0))) (shiftPairHeap s (some (packedPrefix xs 0 64)) (some (u64 0))) _ rfl
    (shiftPairDestLength s none (some (u64 0))) (shiftPairSourceLength xs none (some (u64 0)) hp hn)
    (shiftPairSourceLow xs none (some (u64 0)) hp hn) (shiftPairWriteLow s none (some (u64 0)) _)
    (shiftPairSourceHigh xs (some (packedPrefix xs 0 64)) (some (u64 0)) hp hn)
    (shiftPairWriteHigh s (some (packedPrefix xs 0 64)) (some (u64 0)) _)

/-- The installed suffix copier realizes every partial left shift through two original chunks. -/
theorem shiftPairLeftCopy (xs : List Bool) (count : Nat)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) (hc : count < xs.length) :
    (copyChunks 1 (int 1) 0 (int ((count + 1 : Nat) : Int)) (int ((xs.length - count : Nat) : Int))).run
      (shiftPairExtend (initWords (encodeBits xs)) (u64 0) (u64 0)) =
      (.ok (), shiftPairExtend (initWords (encodeBits xs))
        (packedPrefix (shiftLeftBits xs count) 0 64) (packedPrefix (shiftLeftBits xs count) 1 64)) := by
  let s := initWords (encodeBits xs)
  let allocated := shiftPairExtend s (u64 0) (u64 0)
  let kept := xs.length - count
  have hkept : 0 < kept := by dsimp only [kept]; omega
  have hendS : int ((count + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hendD : int 1 + int kept - int 1 = int kept := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hs0 := copyPairAddress count (by omega)
  have hs1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
      (int 2, int ((xs.length - 65 : Nat) : Int)) := by
    rw [hendS]
    exact copyPairFinalAddress xs.length hp hn
  have hg := copyPairFirstPackedRun xs count 0 allocated hp hn hc
    (shiftPairSourceLow xs (some (u64 0)) (some (u64 0)) hp hn)
    (shiftPairSourceHigh xs (some (u64 0)) (some (u64 0)) hp hn)
  have hlow := shiftPairLeftLow xs count hc
  have hhigh := shiftPairLeftHigh xs count hc hn
  by_cases hk : kept ≤ 64
  · have hmin : min (xs.length - count) 64 = kept := Nat.min_eq_left hk
    rw [hmin] at hlow
    have hzero : xs.length - count - 64 = 0 := by omega
    rw [hzero, copyPairPasteEmpty _ _ 0 (by decide)] at hhigh
    rw [← hlow, ← hhigh]
    have hd1 : getChunksId (int 1 + int kept - int 1) = (int 1, int ((0 + kept - 1 : Nat) : Int)) := by
      rw [hendD]
      have h := rangeSingleAddress (kept - 1) (by omega)
      simpa only [Nat.zero_add, show kept - 1 + 1 = kept by omega] using h
    exact copyPairOneRun 1 0 _ _ kept 0 (int 1) (copyPairStartChunk count)
      (int ((count % 64 : Nat) : Int)) (int 2) (int ((xs.length - 65 : Nat) : Int)) allocated _ (u64 0) _
      hkept (by omega) (by intro h; exact (by decide : (1 : Nat) ≠ 0) h.1) rfl hd1 hs0 hs1 hg
      (shiftPairDestLow s (u64 0) (some (u64 0))) (shiftPairWriteLow s (some (u64 0)) (some (u64 0)) _)
  · have hk' : 64 < kept := by omega
    have hmin : min (xs.length - count) 64 = 64 := Nat.min_eq_right (by omega)
    rw [hmin] at hlow
    rw [← hlow, ← hhigh]
    let low := copyPairPaste (u64 0) (copyPairSlice xs count) 0 64
    let mid := shiftPairExtend s low (u64 0)
    have hd1 : getChunksId (int 1 + int kept - int 1) = (int 2, int ((kept - 64 - 1 : Nat) : Int)) := by
      rw [hendD]
      simpa only [Nat.sub_sub] using copyPairFinalAddress kept hk' (by dsimp only [kept]; omega)
    have hnext := copyPairNextPackedRun xs count 0 mid hp hn hc
      (shiftPairSourceHigh xs (some low) (some (u64 0)) hp hn)
    apply copyPairTwoRun 1 0 _ _ (int kept) 0 (kept - 64) (copyPairStartChunk count)
      (int ((count % 64 : Nat) : Int)) (int 2) (int ((xs.length - 65 : Nat) : Int))
      allocated mid _ (u64 0) (u64 0) (copyPairSlice xs count) (copyPairSlice xs (count + 64))
      (by decide) (by omega) (by dsimp only [kept]; omega)
      (fillPositiveLength kept hkept (by dsimp only [kept]; omega))
      (by intro h; exact (by decide : (1 : Nat) ≠ 0) h.1) rfl hd1 hs0 hs1 hg
      (shiftPairDestLow s (u64 0) (some (u64 0))) (shiftPairWriteLow s (some (u64 0)) (some (u64 0)) low)
      hnext (shiftPairDestHigh s (some low) (u64 0))
    rw [copyPairCarryZero]
    exact shiftPairWriteHigh s (some low) (some (u64 0))
        (copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (kept - 64))

/-- The final source chunk of a nonempty prefix of at most two words. -/
def shiftPairPrefixChunk (kept : Nat) : I64 := if kept ≤ 64 then int 1 else int 2

/-- Its final bit offset within that source chunk. -/
def shiftPairPrefixBit (kept : Nat) : Nat := if kept ≤ 64 then kept - 1 else kept - 65

/-- A prefix endpoint has the expected one- or two-word address. -/
theorem shiftPairPrefixAddress (kept : Nat) (hp : 0 < kept) (hn : kept ≤ 128) :
    getChunksId (int kept) = (shiftPairPrefixChunk kept, int (shiftPairPrefixBit kept)) := by
  by_cases hk : kept ≤ 64
  · simp only [shiftPairPrefixChunk, shiftPairPrefixBit, hk, ite_true]
    have h := rangeSingleAddress (kept - 1) (by omega)
    simpa only [show kept - 1 + 1 = kept by omega] using h
  · simp only [shiftPairPrefixChunk, shiftPairPrefixBit, hk, ite_false]
    exact copyPairFinalAddress kept (by omega) hn

/-- The initial source mask gives precisely the first gathered prefix word. -/
theorem shiftPairPrefixFirstWord (xs : List Bool) (kept : Nat) (hp : 0 < kept) :
    lshr_int (and_int (packedPrefix xs 0 64)
      (copyPairSourceMask (int 1) (shiftPairPrefixChunk kept)
        (int (0 : Nat)) (int (shiftPairPrefixBit kept)))) (int (0 : Nat)) =
      shiftPairRightFirst xs kept := by
  by_cases hk : kept ≤ 64
  · have hinc : int ((kept - 1 : Nat) : Int) + int 1 = int kept := by
      rw [packedInt_add]
      apply congrArg int
      omega
    simp only [shiftPairPrefixChunk, shiftPairPrefixBit, shiftPairRightFirst, hk, ite_true,
      copyPairSourceMask, show (int 1 - int 1 == int 0) = true from rfl, hinc]
    apply packedBit_ext
    intro bit hb
    rw [copyPairRightBit _ 0 bit (by decide) hb, if_pos (by omega),
      dequePackedAnd, dequePackedAnd, scalar_packedBit_not _ _ (by omega),
      rangeSingleHighMaskBit 0 (bit + 0) (by decide) (by omega),
      rangeSingleHighMaskBit kept (bit + 0) hk (by omega),
      packedWord_bit xs 0 (bit + 0) (by omega), packedWord_bit (xs.take kept) 0 bit hb]
    simp only [Nat.zero_le, decide_true, Bool.true_and, Nat.zero_mul, Nat.zero_add, Nat.add_zero,
      List.getD_eq_getElem?_getD, List.getElem?_take]
    by_cases hi : bit < kept
    · simp only [hi, decide_true, Option.guard_true, show ¬ kept ≤ bit by omega,
        decide_false, Bool.not_false, Bool.and_true, ite_true]
    · simp only [hi, decide_false, Option.guard_false, Option.getD_none, show kept ≤ bit by omega,
        decide_true, Bool.not_true, Bool.and_false, ite_false, Option.getD_none]
  · simp only [shiftPairPrefixChunk, shiftPairPrefixBit, shiftPairRightFirst, hk, ite_false,
      copyPairSourceMask, show (int 2 - int 1 == int 0) = false from rfl,
      Bool.false_eq_true, ite_false, shiftPairNoShiftMask]

/-- Gathering the first copied prefix word reads only the original low source word. -/
theorem shiftPairPrefixFirstRun (xs : List Bool) (kept chunks : Nat) (s : State)
    (hp : 0 < kept)
    (hr : (mutableGet chunks (int 1)).run s = (.ok (packedPrefix xs 0 64), s)) :
    (glueSrcBitChunks chunks (int 1) (shiftPairPrefixChunk kept)
      (copyPairSourceMask (int 1) (shiftPairPrefixChunk kept)
        (int (0 : Nat)) (int (shiftPairPrefixBit kept))) (int (0 : Nat))).run s =
      (.ok (shiftPairRightFirst xs kept), s) := by
  simp only [glueSrcBitChunks, shape_run_bind, hr,
    show ¬ int (0 : Nat) > int 0 from by decide, and_false, ite_false, shape_run_pure,
    shiftPairPrefixFirstWord xs kept hp]

/-- The optional next prefix word reads the original high chunk exactly when the prefix includes it. -/
theorem shiftPairPrefixNextRun (xs : List Bool) (kept chunks : Nat) (s : State)
    (hr : (mutableGet chunks (int 2)).run s = (.ok (packedPrefix xs 1 64), s)) :
    ((if shiftPairPrefixChunk kept ≥ int 1 + int 1 then
      glueSrcBitChunks chunks (int 1 + int 1) (shiftPairPrefixChunk kept)
        (copyPairSourceMask (int 1) (shiftPairPrefixChunk kept)
          (int (0 : Nat)) (int (shiftPairPrefixBit kept))) (int (0 : Nat))
      else pure (u64 0)) : BitMutationM U64).run s =
      (.ok (shiftPairRightNext xs kept), s) := by
  by_cases hk : kept ≤ 64
  · simp only [shiftPairPrefixChunk, shiftPairRightNext, hk, ite_true,
      show ¬ int 1 ≥ int 1 + int 1 from by decide, ite_false, shape_run_pure]
  · simp only [shiftPairPrefixChunk, shiftPairRightNext, hk, ite_false,
      show int 1 + int 1 = int 2 from rfl, show int 2 ≥ int 2 from by decide, ite_true,
      copyPairSourceMask, show (int 2 - int 1 == int 0) = false from rfl,
      Bool.false_eq_true, ite_false]
    have h := copyPairLastRun chunks (int (0 : Nat)) (shl_int u64Max (int (0 : Nat)))
      (packedPrefix xs 1 64) s hr
    rw [shiftPairNoShiftMask] at h
    exact h

/-- The installed prefix copier realizes every partial right shift through two original chunks. -/
theorem shiftPairRightCopy (xs : List Bool) (count : Nat)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) (hc : count < xs.length) :
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1) (int ((xs.length - count : Nat) : Int))).run
      (shiftPairExtend (initWords (encodeBits xs)) (u64 0) (u64 0)) =
      (.ok (), shiftPairExtend (initWords (encodeBits xs))
        (packedPrefix (shiftRightBits xs count) 0 64) (packedPrefix (shiftRightBits xs count) 1 64)) := by
  let s := initWords (encodeBits xs)
  let allocated := shiftPairExtend s (u64 0) (u64 0)
  let kept := xs.length - count
  have hkept : 0 < kept := by dsimp only [kept]; omega
  have hendS : int 1 + int kept - int 1 = int kept := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hendD : int ((count + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hs1 : getChunksId (int 1 + int kept - int 1) =
      (shiftPairPrefixChunk kept, int (shiftPairPrefixBit kept)) := by
    rw [hendS]
    exact shiftPairPrefixAddress kept hkept (by dsimp only [kept]; omega)
  have hg := shiftPairPrefixFirstRun xs kept 0 allocated hkept
    (shiftPairSourceLow xs (some (u64 0)) (some (u64 0)) hp hn)
  by_cases hsmall : count < 64
  · have hd0 : getChunksId (int ((count + 1 : Nat) : Int)) = (int 1, int count) := rangeSingleAddress count hsmall
    have hd1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
        (int 2, int ((xs.length - 64 - 1 : Nat) : Int)) := by
      rw [hendD]
      simpa only [Nat.sub_sub] using copyPairFinalAddress xs.length hp hn
    rw [← shiftPairRightLow xs count hsmall hp hn, ← shiftPairRightHigh xs count hsmall hp hn]
    let low := copyPairPaste (u64 0) (shiftPairRightFirst xs kept) count (64 - count)
    let mid := shiftPairExtend s low (u64 0)
    have hnext := shiftPairPrefixNextRun xs kept 0 mid
      (shiftPairSourceHigh xs (some low) (some (u64 0)) hp hn)
    exact copyPairTwoRun 1 0 _ _ (int kept) count (xs.length - 64) (int 1) (int (0 : Nat))
      (shiftPairPrefixChunk kept) (int (shiftPairPrefixBit kept)) allocated mid _ (u64 0) (u64 0)
      (shiftPairRightFirst xs kept) (shiftPairRightNext xs kept) (by omega) (by omega) (by omega)
      (fillPositiveLength kept hkept (by dsimp only [kept]; omega))
      (by intro h; exact (by decide : (1 : Nat) ≠ 0) h.1) hd0 hd1 rfl hs1 hg
      (shiftPairDestLow s (u64 0) (some (u64 0))) (shiftPairWriteLow s (some (u64 0)) (some (u64 0)) low)
      hnext (shiftPairDestHigh s (some low) (u64 0)) (shiftPairWriteHigh s (some low) (some (u64 0)) _)
  · have hlarge : 64 ≤ count := by omega
    have hd0 : getChunksId (int ((count + 1 : Nat) : Int)) = (int 2, int ((count - 64 : Nat) : Int)) := by
      simpa only [copyPairStartChunk, hsmall, ite_false, show count % 64 = count - 64 by omega] using
        copyPairAddress count (by omega)
    have hd1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
        (int 2, int ((count - 64 + kept - 1 : Nat) : Int)) := by
      rw [hendD, copyPairFinalAddress xs.length hp hn]
      rw [show xs.length - 65 = count - 64 + kept - 1 by dsimp only [kept]; omega]
    rw [shiftPairRightLargeLow xs count hlarge hc, ← shiftPairRightLargeHigh xs count hlarge hc hn]
    exact copyPairOneRun 1 0 _ _ kept (count - 64) (int 2) (int 1) (int (0 : Nat))
      (shiftPairPrefixChunk kept) (int (shiftPairPrefixBit kept)) allocated _ (u64 0) _
      hkept (by dsimp only [kept]; omega) (by intro h; exact (by decide : (1 : Nat) ≠ 0) h.1)
      hd0 hd1 rfl hs1 hg (shiftPairDestHigh s (some (u64 0)) (u64 0))
      (shiftPairWriteHigh s (some (u64 0)) (some (u64 0)) _)

/-- Unsigned reinterpretation preserves every supported two-word logical length. -/
theorem shiftPairUnsignedLength (n : Nat) (hn : n ≤ 128) :
    (JuliaLean.base.int.unsigned (int n)).val = n := by
  rw [JuliaLean.Proofs.base.int.unsigned_val, packedInt_val n (by omega)]
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ 18446744073709551615
  omega

/-- A partial unsigned left shift installs both exact encoded output chunks. -/
theorem shiftPairLeftPartial (xs : List Bool) (i : U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128)
    (hi : 0 < i.val.toNat) (hl : i.val.toNat < xs.length) :
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftPairExtend (initWords (encodeBits xs))
          (packedPrefix (shiftLeftBits xs i.val.toNat) 0 64)
          (packedPrefix (shiftLeftBits xs i.val.toNat) 1 64)) := by
  let s := initWords (encodeBits xs)
  let n := i.val.toNat
  have hncast : (n : Int) = i.val := shiftSingleUnsignedNat i
  have hcast : int i.val = int n := congrArg int hncast.symm
  have hsum : int n + int 1 = int ((n + 1 : Nat) : Int) := by rw [packedInt_add]; rfl
  have hdiff : int xs.length - int n = int ((xs.length - n : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hcmp : JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftPairUnsignedLength xs.length hn, ← hncast]
    omega
  apply shiftSingleLeftFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
    Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
    (vectorBits xs) (⟨1, int xs.length, [int xs.length]⟩ : BitVector) i s _ _
    (shiftSingleUnsignedNonzero i hi) hcmp (shiftPairZeroVector xs.length hp hn s)
  change (copyChunks 1 (int 1) 0 (int i.val + int 1) (int xs.length - int i.val)).run _ = _
  rw [hcast, hsum, hdiff]
  exact shiftPairLeftCopy xs n hp hn hl

/-- A partial unsigned right shift installs both exact encoded output chunks. -/
theorem shiftPairRightPartial (xs : List Bool) (i : U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128)
    (hi : 0 < i.val.toNat) (hl : i.val.toNat < xs.length) :
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftPairExtend (initWords (encodeBits xs))
          (packedPrefix (shiftRightBits xs i.val.toNat) 0 64)
          (packedPrefix (shiftRightBits xs i.val.toNat) 1 64)) := by
  let s := initWords (encodeBits xs)
  let n := i.val.toNat
  have hncast : (n : Int) = i.val := shiftSingleUnsignedNat i
  have hcast : int i.val = int n := congrArg int hncast.symm
  have hsum : int n + int 1 = int ((n + 1 : Nat) : Int) := by rw [packedInt_add]; rfl
  have hdiff : int xs.length - int n = int ((xs.length - n : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hcmp : JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftPairUnsignedLength xs.length hn, ← hncast]
    omega
  apply shiftSingleRightFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
    Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
    (vectorBits xs) (⟨1, int xs.length, [int xs.length]⟩ : BitVector) i s _ _
    (shiftSingleUnsignedNonzero i hi) hcmp (shiftPairZeroVector xs.length hp hn s)
  change (copyChunks 1 (int i.val + int 1) 0 (int 1) (int xs.length - int i.val)).run _ = _
  rw [hcast, hsum, hdiff]
  exact shiftPairRightCopy xs n hp hn hl

/-- Every unsigned left-shift count is correct for a two-chunk input, including zero and oversized counts. -/
theorem shiftPairLeftCanonical (xs : List Bool) (i : U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftPairExtend (initWords (encodeBits xs))
          (packedPrefix (shiftLeftBits xs i.val.toNat) 0 64)
          (packedPrefix (shiftLeftBits xs i.val.toNat) 1 64)) := by
  by_cases hz : i.val.toNat = 0
  · have he := shiftSingleUnsignedZero i hz
    subst i
    rw [show (u64 0).val.toNat = 0 from rfl, shiftSingleLeftZero]
    simp only [Round5.Round2.shiftLeftUnsignedModel, bitVectorShiftLeftUnsigned,
      beq_self_eq_true, ite_true]
    exact shiftPairCopyCanonical xs hp hn
  · have hi : 0 < i.val.toNat := by omega
    by_cases hsmall : i.val.toNat < xs.length
    · exact shiftPairLeftPartial xs i hp hn hi hsmall
    · have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
        change ¬ i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
        rw [shiftPairUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
        omega
      rw [shiftLeftBits, if_pos (by omega), shiftPairFalseWord, shiftPairFalseWord]
      exact shiftSingleLeftLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
        Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
        (vectorBits xs) _ i _ _ (shiftSingleUnsignedNonzero i hi) hcmp
        (shiftPairZeroVector xs.length hp hn _)

/-- Every unsigned right-shift count is correct for a two-chunk input, including zero and oversized counts. -/
theorem shiftPairRightCanonical (xs : List Bool) (i : U64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftPairExtend (initWords (encodeBits xs))
          (packedPrefix (shiftRightBits xs i.val.toNat) 0 64)
          (packedPrefix (shiftRightBits xs i.val.toNat) 1 64)) := by
  by_cases hz : i.val.toNat = 0
  · have he := shiftSingleUnsignedZero i hz
    subst i
    rw [show (u64 0).val.toNat = 0 from rfl, shiftSingleRightZero]
    simp only [Round5.Round2.shiftRightUnsignedModel, bitVectorShiftRightUnsigned,
      beq_self_eq_true, ite_true]
    exact shiftPairCopyCanonical xs hp hn
  · have hi : 0 < i.val.toNat := by omega
    by_cases hsmall : i.val.toNat < xs.length
    · exact shiftPairRightPartial xs i hp hn hi hsmall
    · have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
        change ¬ i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
        rw [shiftPairUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
        omega
      rw [shiftRightBits, if_pos (by omega), shiftPairFalseWord, shiftPairFalseWord]
      exact shiftSingleRightLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
        Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
        (vectorBits xs) _ i _ _ (shiftSingleUnsignedNonzero i hi) hcmp
        (shiftPairZeroVector xs.length hp hn _)

/-- Both signed shifts dispatch to the correct complete unsigned two-chunk computation for every native count. -/
theorem shiftPairSignedRuns (xs : List Bool) (i : I64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
    let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i).run s =
        (.ok A, shiftPairExtend s (packedPrefix left 0 64) (packedPrefix left 1 64)) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i).run s =
        (.ok A, shiftPairExtend s (packedPrefix right 0 64) (packedPrefix right 1 64)) := by
  dsimp only
  by_cases hi : 0 ≤ i.val
  · have hc := shiftSingleNonnegativeMagnitude i hi
    have hl := shiftPairLeftCanonical xs (JuliaLean.base.int.unsigned i) hp hn
    have hr := shiftPairRightCanonical xs (JuliaLean.base.int.unsigned i) hp hn
    rw [hc] at hl hr
    have hcond : i ≥ int 0 := hi
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq,
      hcond, hi, ite_true]
    exact ⟨hl, hr⟩
  · have hc := shiftSingleNegativeMagnitude i hi
    have hl := shiftPairLeftCanonical xs (JuliaLean.base.int.unsigned (-i)) hp hn
    have hr := shiftPairRightCanonical xs (JuliaLean.base.int.unsigned (-i)) hp hn
    rw [hc] at hl hr
    have hcond : ¬ i ≥ int 0 := hi
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq,
      hcond, hi, ite_false, Round5.Round2.shiftLeftSignedArgModel, Round5.Round2.shiftRightSignedArgModel]
    exact ⟨hr, hl⟩

/-- Every encoded two-word destination has the requested logical values and zero padding. -/
theorem shiftPairObservations (s : State) (xs : List Bool) (B : BitArray 1)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128)
    (hc : B.chunks = s.arrays.length) (hl : B.len = int xs.length) :
    bitValues (shiftPairExtend s (packedPrefix xs 0 64) (packedPrefix xs 1 64)) B = xs ∧
      Round5.Round2.PackedInvariant (shiftPairExtend s (packedPrefix xs 0 64) (packedPrefix xs 1 64)) B := by
  have hcontents : (shiftPairExtend s (packedPrefix xs 0 64) (packedPrefix xs 1 64)).contents B.chunks =
      (encodeBits xs).map some := by
    rw [hc, shiftPairContents, copyPairEncoding xs hp hn]
    rfl
  exact ⟨scalar_bitValues_contents _ B xs (by omega) hl hcontents,
    scalar_invariant_of_contents _ B xs (by omega) hl hcontents⟩

/-- Both signed-shift results are exact and packed for every native count on a two-chunk input. -/
theorem shiftPairSignedCorrect (xs : List Bool) (i : I64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    ∃ A leftState rightState,
      (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, leftState) ∧
      (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, rightState) ∧
      bitValues leftState A = (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) ∧
      bitValues rightState A = (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) ∧
      Round5.Round2.PackedInvariant leftState A ∧ Round5.Round2.PackedInvariant rightState A := by
  let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
  let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have hl : left.length = xs.length := by
    unfold left
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hr : right.length = xs.length := by
    unfold right
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hol := shiftPairObservations s left A (by rw [hl]; exact hp) (by rw [hl]; exact hn) rfl
    (by change int xs.length = int left.length; rw [hl])
  have hor := shiftPairObservations s right A (by rw [hr]; exact hp) (by rw [hr]; exact hn) rfl
    (by change int xs.length = int right.length; rw [hr])
  have hrun := shiftPairSignedRuns xs i hp hn
  exact ⟨A, shiftPairExtend s (packedPrefix left 0 64) (packedPrefix left 1 64),
    shiftPairExtend s (packedPrefix right 0 64) (packedPrefix right 1 64),
    hrun.1, hrun.2, hol.1, hor.1, hol.2, hor.2⟩

/-- The installed signed-shift assertion holds for every native count on a two-chunk vector. -/
theorem BitarraysShift_exactlyTwoChunks (xs : List Bool) (i : I64)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) : Round5.Round2.ShiftAgrees xs i := by
  obtain ⟨A, leftState, rightState, hl, hr, hvl, hvr, _, _⟩ := shiftPairSignedCorrect xs i hp hn
  unfold Round5.Round2.ShiftAgrees
  dsimp only
  rw [hl, hr]
  exact ⟨hvl, hvr⟩

/-- The frozen signed-shift contract holds through two chunks, including empty input and both extreme native counts. -/
theorem BitarraysShift_twoChunks (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 128) : Round5.Round2.ShiftAgrees xs i := by
  by_cases hs : xs.length ≤ 64
  · exact BitarraysShift_singleChunk xs i hs
  · exact BitarraysShift_exactlyTwoChunks xs i (by omega) hn

/-- The installed chunk fill callback initializes every slot of a fresh allocation. -/
theorem shiftFreshFill (s : State) (slots : List (Option U64)) (value : U64)
    (hn : slots.length ≤ 9223372036854775807) :
    (Round5.Round2.fillChunkVectorModel s.arrays.length value).run (shiftFreshHeap s slots) =
      (.ok (), shiftFreshHeap s (List.replicate slots.length (some value))) := by
  apply fillChunkVectorFrom s.arrays.length value (int slots.length) _ _ (shiftFreshLength s slots)
  rw [packedObserve_intRange slots.length hn, List.forIn_map]
  have h := shiftFreshWriteLoop s (List.range slots.length) slots (fun _ => value) hn
    (by intro i hi; exact List.mem_range.mp hi)
  rw [shiftFreshFoldConstant] at h
  exact h

/-- Positive vector construction factors through arbitrary successful allocation and final-chunk initialization. -/
theorem shiftFreshConstructPositive {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (n : I64) (count : Nat) (s allocated initialized : State) (handle : Nat)
    (hneg : ¬ n.val < 0) (hp : 0 < count) (hn : count ≤ 9223372036854775807)
    (hchecked : (checked [n]).run s = (.ok n, s))
    (hcount : numBitChunks n = int count)
    (hallocate : (allocate count).run s = (.ok handle, allocated))
    (hwrite : (mutableSet handle (u64 0) (int count)).run allocated = (.ok (), initialized)) :
    (BitArrayUndef (N := N) checked allocate [n]).run s =
      (.ok ⟨handle, n, [n]⟩, initialized) := by
  have hpos : (count : Int) > 0 := by omega
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hneg, ite_false,
    shape_run_bind, shape_run_pure, hchecked, hcount,
    packedInt_val count hn, Int.toNat_natCast, hallocate, hpos, ite_true, hwrite]

/-- Every supported positive logical length has a successful fresh packed allocation. -/
theorem shiftFreshAllocateVector (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) (s : State) :
    (Round5.Round2.allocateBitArrayModel (N := 1) [int n]).run s =
      (.ok (⟨s.arrays.length, int n, [int n]⟩ : BitVector), shiftFreshHeap s (shiftFreshInitial n)) := by
  let count := wordCount n
  have hcount : 0 < count := by dsimp only [count]; unfold wordCount; omega
  have hcapacity : count ≤ 576460752303423488 := by dsimp only [count]; unfold wordCount; omega
  have hwrite := shiftFreshSet s (List.replicate count none) (count - 1) (u64 0)
    (by rw [List.length_replicate]; omega) (by rw [List.length_replicate]; omega)
  rw [show count - 1 + 1 = count by omega] at hwrite
  exact shiftFreshConstructPositive checkedDimensionsModel allocateChunkVectorModel (int n) count s _ _ s.arrays.length
    (by rw [packedInt_val n hn]; omega) hcount (by omega) (shiftPairCheckedDims n s)
    (shiftFreshNumChunks n hn) (shiftFreshAllocate s count hcapacity) hwrite

/-- The public false constructor succeeds at every supported positive length and initializes every output chunk. -/
theorem shiftFreshZeroVector (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) (s : State) :
    (Round5.Round2.zeroBitVectorModel (int n)).run s =
      (.ok (⟨s.arrays.length, int n, [int n]⟩ : BitVector),
        shiftFreshHeap s ((encodeBits (List.replicate n false)).map some)) := by
  have ha := shiftFreshAllocateVector n hp hn s
  have hc := dequeConvertOk false false (shiftFreshHeap s (shiftFreshInitial n)) rfl
  have hbound : (shiftFreshInitial n).length ≤ 9223372036854775807 := by
    rw [shiftFreshInitialLength]
    unfold wordCount
    omega
  have hfill := shiftFreshFill s (shiftFreshInitial n) (u64 0) hbound
  rw [shiftFreshInitialLength, shiftFreshZeroSlots] at hfill
  have hf := fillFalseFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
    (⟨s.arrays.length, int n, [int n]⟩ : BitArray 1) false
    (shiftFreshHeap s (shiftFreshInitial n)) (shiftFreshHeap s ((encodeBits (List.replicate n false)).map some)) hc
    (fillPositiveLength n hp hn) hfill
  exact shiftSingleFalseConstruct Round5.Round2.allocateBitArrayModel
    (fun B value => fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B value)
    (int n) _ _ s _ _ ha hf

/-- An arbitrary fresh encoded vector has exact logical values and the full packed invariant. -/
theorem shiftFreshObservations (s : State) (xs : List Bool) (B : BitArray 1)
    (hn : xs.length ≤ 9223372036854775807)
    (hc : B.chunks = s.arrays.length) (hl : B.len = int xs.length) :
    bitValues (shiftFreshHeap s ((encodeBits xs).map some)) B = xs ∧
      Round5.Round2.PackedInvariant (shiftFreshHeap s ((encodeBits xs).map some)) B := by
  have hcontents : (shiftFreshHeap s ((encodeBits xs).map some)).contents B.chunks = (encodeBits xs).map some := by
    rw [hc]
    exact shiftFreshContents s _ (by rw [List.length_map]; exact packedEncoded_lengthBound xs hn)
  exact ⟨scalar_bitValues_contents _ B xs hn hl hcontents,
    scalar_invariant_of_contents _ B xs hn hl hcontents⟩

/-- Unsigned reinterpretation preserves every supported nonnegative vector length. -/
theorem shiftFreshUnsignedLength (n : Nat) (hn : n ≤ 9223372036854775807) :
    (JuliaLean.base.int.unsigned (int n)).val = n := by
  rw [JuliaLean.Proofs.base.int.unsigned_val, packedInt_val n hn]
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ 18446744073709551615
  omega

/-- Every oversized unsigned shift of a nonempty supported vector returns the exact all-false encoding. -/
theorem shiftLargeUnsignedRuns (xs : List Bool) (i : U64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) (hi : xs.length ≤ i.val.toNat) :
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let s := initWords (encodeBits xs)
    let out := shiftFreshHeap s ((encodeBits (List.replicate xs.length false)).map some)
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run s = (.ok A, out) ∧
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run s = (.ok A, out) := by
  have hpos : 0 < i.val.toNat := by omega
  have hcmp : ¬ JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change ¬ i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftFreshUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
    omega
  have ha := shiftFreshZeroVector xs.length hp hn (initWords (encodeBits xs))
  exact ⟨shiftSingleLeftLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits xs) _ i _ _ (shiftSingleUnsignedNonzero i hpos) hcmp ha,
    shiftSingleRightLargeFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits xs) _ i _ _ (shiftSingleUnsignedNonzero i hpos) hcmp ha⟩

/-- Signed counts whose magnitude reaches the vector length yield all-false results in either direction. -/
theorem shiftLargeSignedRuns (xs : List Bool) (i : I64)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) (hi : xs.length ≤ i.val.natAbs) :
    let B := vectorBits xs
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let s := initWords (encodeBits xs)
    let out := shiftFreshHeap s ((encodeBits (List.replicate xs.length false)).map some)
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i).run s = (.ok A, out) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i).run s = (.ok A, out) := by
  dsimp only
  by_cases hsign : 0 ≤ i.val
  · have hmag := shiftSingleNonnegativeMagnitude i hsign
    have h := shiftLargeUnsignedRuns xs (JuliaLean.base.int.unsigned i) hp hn (by rw [hmag]; exact hi)
    have hcond : i ≥ int 0 := hsign
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, hcond, ite_true]
    exact h
  · have hmag := shiftSingleNegativeMagnitude i hsign
    have h := shiftLargeUnsignedRuns xs (JuliaLean.base.int.unsigned (-i)) hp hn (by rw [hmag]; exact hi)
    have hcond : ¬ i ≥ int 0 := hsign
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, hcond, ite_false,
      Round5.Round2.shiftLeftSignedArgModel, Round5.Round2.shiftRightSignedArgModel]
    exact ⟨h.2, h.1⟩

/-- Every oversized native signed shift obeys the frozen contract at every supported vector length. -/
theorem BitarraysShift_oversized (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hi : xs.length ≤ i.val.natAbs) :
    Round5.Round2.ShiftAgrees xs i := by
  by_cases hp : 0 < xs.length
  · let s := initWords (encodeBits xs)
    let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
    have hobs := shiftFreshObservations s (List.replicate xs.length false) A
      (by simpa only [List.length_replicate] using hn) rfl
      (by change int xs.length = int (List.replicate xs.length false).length; rw [List.length_replicate])
    have hrun := shiftLargeSignedRuns xs i hp hn hi
    unfold Round5.Round2.ShiftAgrees
    dsimp only
    rw [hrun.1, hrun.2]
    simp only [shiftLeftBits, shiftRightBits, hi, ite_true, ite_self]
    exact ⟨hobs.1, hobs.1⟩
  · have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact BitarraysShift_empty i

/-- The natural-index source-to-fresh-destination chunk copy action. -/
def shiftFreshCopyAction (j : Nat) : BitMutationM Unit := do
  let word ← mutableGet 0 (int ((j + 1 : Nat) : Int))
  mutableSet 1 word (int ((j + 1 : Nat) : Int))

/-- A source read and destination write compose into one abstract chunk copy. -/
theorem shiftFreshCopyActionFrom (j : Nat) (s out : State) (word : U64)
    (hr : (mutableGet 0 (int ((j + 1 : Nat) : Int))).run s = (.ok word, s))
    (hw : (mutableSet 1 word (int ((j + 1 : Nat) : Int))).run s = (.ok (), out)) :
    (shiftFreshCopyAction j).run s = (.ok (), out) := by
  simp only [shiftFreshCopyAction, shape_run_bind, hr, hw]

/-- One copy action installs the source word without altering earlier source storage. -/
theorem shiftFreshCopyActionRun (words : List U64) (slots : List (Option U64)) (j : Nat)
    (hl : slots.length = words.length) (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (shiftFreshCopyAction j).run (shiftFreshHeap (initWords words) slots) =
      (.ok (), shiftFreshHeap (initWords words) (slots.set j (some (words.getD j (u64 0))))) := by
  have hr := shiftFreshSource words slots j hn hj
  have hw := shiftFreshSet (initWords words) slots j (words.getD j (u64 0))
    (by rw [hl]; exact hn) (by rw [hl]; exact hj)
  change (mutableSet 1 (words.getD j (u64 0)) (int ((j + 1 : Nat) : Int))).run _ = _ at hw
  exact shiftFreshCopyActionFrom j _ _ _ hr hw

/-- The installed native index loop copies exactly the requested source slots into a fresh allocation. -/
theorem shiftFreshCopyLoop (indices : List Nat) (words : List U64) (slots : List (Option U64))
    (hl : slots.length = words.length) (hn : words.length ≤ 9223372036854775807)
    (hi : ∀ i ∈ indices, i < words.length) :
    (forIn (indices.map (fun i => int ((i + 1 : Nat) : Int))) PUnit.unit (fun i _ => do
      let word ← mutableGet 0 i
      mutableSet 1 word i
      pure (ForInStep.yield PUnit.unit))).run (shiftFreshHeap (initWords words) slots) =
      (.ok PUnit.unit, shiftFreshHeap (initWords words)
        (indices.foldl (fun ws i => ws.set i (some (words.getD i (u64 0)))) slots)) := by
  have h := dequeForInFold shiftFreshCopyAction
    (fun (ws : List (Option U64)) i => ws.set i (some (words.getD i (u64 0))))
    (shiftFreshHeap (initWords words)) (fun ws => ws.length = words.length) indices
    (by intro ws hw i hi'; exact shiftFreshCopyActionRun words ws i hw hn (hi i hi'))
    (by intro ws hw i _; rw [List.length_set]; exact hw) slots hl
  rw [List.forIn_map]
  simpa only [shiftFreshCopyAction, bind_assoc] using h

/-- Copying every nonfinal word and then the final word gives the exact source encoding. -/
theorem shiftFreshCopyLast (words : List U64) (slots : List (Option U64))
    (hp : 0 < words.length) (hl : slots.length = words.length) :
    ((List.range (words.length - 1)).foldl
      (fun ws i => ws.set i (some (words.getD i (u64 0)))) slots).set
      (words.length - 1) (some (words.getD (words.length - 1) (u64 0))) = words.map some := by
  have h := shiftFreshFoldCopy words slots hl
  have he : words.length - 1 + 1 = words.length := by omega
  have hr : List.range words.length = List.range (words.length - 1) ++ [words.length - 1] := by
    simpa only [Nat.succ_eq_add_one, he] using (List.range_succ (n := words.length - 1))
  rw [hr, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
  exact h

/-- Equal-size packed copying factors through its nonfinal-word loop and final direct copy. -/
theorem shiftFreshCopytoFrom (B A : BitArray 1) (nc : I64) (word : U64) (s mid out : State)
    (hlen : B.len = A.len) (hnc : (nc == int 0) = false)
    (hld : (mutableLength A.chunks).run s = (.ok nc, s))
    (hls : (mutableLength B.chunks).run s = (.ok nc, s))
    (hloop : (forIn (intRange (int 1) (nc - int 1)) PUnit.unit (fun i _ => do
      let word ← mutableGet B.chunks i
      mutableSet A.chunks word i
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, mid))
    (hr : (mutableGet B.chunks nc).run mid = (.ok word, mid))
    (hw : (mutableSet A.chunks word nc).run mid = (.ok (), out)) :
    (bitArrayCopyto A B).run s = (.ok A, out) := by
  have hn : ¬ B.len > A.len := by rw [hlen]; exact Int.lt_irrefl _
  have he : (B.len == A.len) = true := by rw [hlen]; exact beq_self_eq_true _
  have hnc' : ¬ nc < nc := Int.lt_irrefl _
  simp only [bitArrayCopyto, hn, ite_false, shape_run_bind, hld, hls,
    hnc', hnc, Bool.false_eq_true, hloop, shape_run_pure, he, ite_true, hr, hw]

/-- Equal-size copying succeeds for every positive packed length and arbitrary fresh destination slots. -/
theorem shiftFreshCopytoCanonical (B A : BitArray 1) (words : List U64) (slots : List (Option U64))
    (hb : B.chunks = 0) (ha : A.chunks = 1) (hlen : B.len = A.len)
    (hl : slots.length = words.length) (hp : 0 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (bitArrayCopyto A B).run (shiftFreshHeap (initWords words) slots) =
      (.ok A, shiftFreshHeap (initWords words) (words.map some)) := by
  let middle := (List.range (words.length - 1)).foldl
    (fun ws i => ws.set i (some (words.getD i (u64 0)))) slots
  have hml : middle.length = words.length := (shiftFreshFoldLength _ _ _).trans hl
  have hlast : int ((words.length - 1 + 1 : Nat) : Int) = int words.length := congrArg int (by omega)
  have hsub : int words.length - int 1 = int ((words.length - 1 : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hloop := shiftFreshCopyLoop (List.range (words.length - 1)) words slots hl hn
    (by intro i hi; have := List.mem_range.mp hi; omega)
  have hloop' : (forIn (intRange (int 1) (int words.length - int 1)) PUnit.unit (fun i _ => do
      let word ← mutableGet B.chunks i
      mutableSet A.chunks word i
      pure (ForInStep.yield PUnit.unit))).run (shiftFreshHeap (initWords words) slots) =
      (.ok PUnit.unit, shiftFreshHeap (initWords words) middle) := by
    rw [hb, ha, hsub, packedObserve_intRange (words.length - 1) (by omega)]
    exact hloop
  have hr := shiftFreshSource words middle (words.length - 1) hn (by omega)
  have hw := shiftFreshSet (initWords words) middle (words.length - 1)
    (words.getD (words.length - 1) (u64 0)) (by rw [hml]; exact hn) (by rw [hml]; omega)
  rw [hlast] at hr hw
  have hld : (mutableLength A.chunks).run (shiftFreshHeap (initWords words) slots) =
      (.ok (int words.length), shiftFreshHeap (initWords words) slots) := by
    rw [ha]
    have h := shiftFreshLength (initWords words) slots
    rw [hl] at h
    exact h
  have hls : (mutableLength B.chunks).run (shiftFreshHeap (initWords words) slots) =
      (.ok (int words.length), shiftFreshHeap (initWords words) slots) := by
    rw [hb]
    exact shiftFreshSourceLength words slots
  have hrun := shiftFreshCopytoFrom B A (int words.length) (words.getD (words.length - 1) (u64 0))
    _ _ _ hlen (fillPositiveLength words.length hp hn) hld hls hloop'
    (by rw [hb]; exact hr) (by rw [ha]; exact hw)
  have hout : middle.set (words.length - 1) (some (words.getD (words.length - 1) (u64 0))) = words.map some :=
    shiftFreshCopyLast words slots hp hl
  rw [hout] at hrun
  exact hrun

/-- A public zero-shift copy creates independent exact packed storage at every supported positive length. -/
theorem shiftFreshCopyCanonical (xs : List Bool) (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (Round5.Round2.copyBitVectorPublic (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits xs).map some)) := by
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have ha : (Round5.Round2.allocateBitArrayModel (vectorBits xs).dims).run s =
      (.ok A, shiftFreshHeap s (shiftFreshInitial xs.length)) := shiftFreshAllocateVector xs.length hp hn s
  apply shiftSinglePublicCopyFrom (vectorBits xs) A s (shiftFreshHeap s (shiftFreshInitial xs.length)) _ ha
  exact shiftFreshCopytoCanonical (vectorBits xs) A (encodeBits xs) (shiftFreshInitial xs.length) rfl rfl rfl
    (by rw [shiftFreshInitialLength, packedEncoded_length])
    (by rw [packedEncoded_length]; unfold wordCount; omega)
    (packedEncoded_lengthBound xs hn)

/-- Public copying creates an independent exact encoded destination at every supported length, including zero. -/
theorem shiftFreshCopyAll (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    (Round5.Round2.copyBitVectorPublic (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok (⟨1, int xs.length, [int xs.length]⟩ : BitVector),
        shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits xs).map some)) := by
  by_cases hp : 0 < xs.length
  · exact shiftFreshCopyCanonical xs hp hn
  · have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact shiftEmptyCopy

/-- Both native signed zero shifts perform precisely the supplied public copy. -/
theorem shiftZeroSignedFrom (B A : BitArray 1) (s out : State)
    (hcopy : (Round5.Round2.copyBitVectorPublic B).run s = (.ok A, out)) :
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B (int 0)).run s = (.ok A, out) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B (int 0)).run s = (.ok A, out) := by
  simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq,
    show int 0 ≥ int 0 from by decide, ite_true,
    show JuliaLean.base.int.unsigned (int 0) = u64 0 from rfl,
    Round5.Round2.shiftLeftUnsignedModel, Round5.Round2.shiftRightUnsignedModel,
    bitVectorShiftLeftUnsigned, bitVectorShiftRightUnsigned, beq_self_eq_true, hcopy]
  exact ⟨True.intro, True.intro⟩

/-- Zero-count result equalities can be transported before instantiating the signed operation. -/
theorem shiftZeroSignedFromAt (B A : BitArray 1) (i : I64) (s out : State)
    (hi : i = int 0) (hcopy : (Round5.Round2.copyBitVectorPublic B).run s = (.ok A, out)) :
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i).run s = (.ok A, out) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i).run s = (.ok A, out) := by
  subst i
  exact shiftZeroSignedFrom B A s out hcopy

/-- Both zero-shift results have the original logical contents and packed invariant at arbitrary length. -/
theorem shiftZeroSignedCorrectAt (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hi : i = int 0) :
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let s := initWords (encodeBits xs)
    let out := shiftFreshHeap s ((encodeBits xs).map some)
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
      (vectorBits xs) i).run s = (.ok A, out) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
      (vectorBits xs) i).run s = (.ok A, out) ∧
    bitValues out A = xs ∧ Round5.Round2.PackedInvariant out A := by
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have hr := shiftZeroSignedFromAt (vectorBits xs) A i _ _ hi (shiftFreshCopyAll xs hn)
  have ho := shiftFreshObservations (initWords (encodeBits xs)) xs A hn rfl rfl
  exact ⟨hr.1, hr.2, ho.1, ho.2⟩

/-- The frozen zero-shift assertion follows from its abstract signed results. -/
theorem BitarraysShift_zeroAt (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hi : i = int 0) :
    Round5.Round2.ShiftAgrees xs i := by
  have h := shiftZeroSignedCorrectAt xs i hn hi
  unfold Round5.Round2.ShiftAgrees
  dsimp only
  rw [h.1, h.2.1]
  rw [hi]
  simp only [show (int 0).val ≥ 0 from by decide, ite_true,
    show (int 0).val.natAbs = 0 from rfl, shiftSingleLeftZero, shiftSingleRightZero]
  exact ⟨h.2.2.1, h.2.2.1⟩

/-- Every supported vector obeys the exact frozen assertion for the native zero shift. -/
theorem BitarraysShift_zero (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    Round5.Round2.ShiftAgrees xs (int 0) := by
  with_reducible exact BitarraysShift_zeroAt xs (int 0) hn rfl

/-- The frozen contract holds for two-chunk inputs and, at arbitrary size, for every zero or oversized count. -/
theorem BitarraysShift_supportedCases (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hc : xs.length ≤ 128 ∨ i = int 0 ∨ xs.length ≤ i.val.natAbs) :
    Round5.Round2.ShiftAgrees xs i := by
  rcases hc with hsmall | hzero | hlarge
  · exact BitarraysShift_twoChunks xs i hsmall
  · exact BitarraysShift_zeroAt xs i hn hzero
  · exact BitarraysShift_oversized xs i hn hlarge
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The two boundary-copy results needed when a partial shift retains at most one word of source bits. -/
def shiftNearCopyContract (xs : List Bool) : Prop :=
  ∀ count : Nat, count < xs.length → xs.length - count ≤ 64 →
    let s := initWords (encodeBits xs)
    let allocated := shiftFreshHeap s ((encodeBits (List.replicate xs.length false)).map some)
    (copyChunks 1 (int 1) 0 (int ((count + 1 : Nat) : Int))
      (int ((xs.length - count : Nat) : Int))).run allocated =
      (.ok (), shiftFreshHeap s ((encodeBits (shiftLeftBits xs count)).map some)) ∧
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1)
      (int ((xs.length - count : Nat) : Int))).run allocated =
      (.ok (), shiftFreshHeap s ((encodeBits (shiftRightBits xs count)).map some))

/-- Exact boundary copies lift through the public unsigned allocation and conversion wrappers. -/
theorem shiftNearUnsignedRunsFromCopies (xs : List Bool) (i : U64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.toNat) (hi : i.val.toNat < xs.length)
    (hk : xs.length - i.val.toNat ≤ 64) (hcopy : shiftNearCopyContract xs) :
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let s := initWords (encodeBits xs)
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run s =
      (.ok A, shiftFreshHeap s ((encodeBits (shiftLeftBits xs i.val.toNat)).map some)) ∧
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run s =
      (.ok A, shiftFreshHeap s ((encodeBits (shiftRightBits xs i.val.toNat)).map some)) := by
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  let count := i.val.toNat
  have hcast : int i.val = int count := congrArg int (shiftSingleUnsignedNat i).symm
  have hsum : int count + int 1 = int ((count + 1 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  have hdiff : int xs.length - int count = int ((xs.length - count : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    dsimp only [count]
    omega
  have hcmp : JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftFreshUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
    omega
  have ha := shiftFreshZeroVector xs.length (by omega) hn s
  have hc := hcopy count hi hk
  constructor
  · apply shiftSingleLeftFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits xs) A i s _ _ (shiftSingleUnsignedNonzero i hp) hcmp ha
    change (copyChunks 1 (int 1) 0 (int i.val + int 1) (int xs.length - int i.val)).run _ = _
    rw [hcast, hsum, hdiff]
    exact hc.1
  · apply shiftSingleRightFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits xs) A i s _ _ (shiftSingleUnsignedNonzero i hp) hcmp ha
    change (copyChunks 1 (int i.val + int 1) 0 (int 1) (int xs.length - int i.val)).run _ = _
    rw [hcast, hsum, hdiff]
    exact hc.2

/-- Native signed dispatch retains the appropriate exact left/right encoding, including negative counts. -/
theorem shiftNearSignedRunsFromCopies (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.natAbs) (hi : i.val.natAbs < xs.length)
    (hk : xs.length - i.val.natAbs ≤ 64) (hcopy : shiftNearCopyContract xs) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
    let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i).run s =
        (.ok A, shiftFreshHeap s ((encodeBits left).map some)) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i).run s =
        (.ok A, shiftFreshHeap s ((encodeBits right).map some)) := by
  dsimp only
  by_cases hs : 0 ≤ i.val
  · have hmag := shiftSingleNonnegativeMagnitude i hs
    have h := shiftNearUnsignedRunsFromCopies xs (JuliaLean.base.int.unsigned i) hn
      (by rw [hmag]; exact hp) (by rw [hmag]; exact hi) (by rw [hmag]; exact hk) hcopy
    rw [hmag] at h
    have hcond : i ≥ int 0 := hs
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, hcond, hs, ite_true]
    exact h
  · have hmag := shiftSingleNegativeMagnitude i hs
    have h := shiftNearUnsignedRunsFromCopies xs (JuliaLean.base.int.unsigned (-i)) hn
      (by rw [hmag]; exact hp) (by rw [hmag]; exact hi) (by rw [hmag]; exact hk) hcopy
    rw [hmag] at h
    have hcond : ¬ i ≥ int 0 := hs
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, hcond, hs, ite_false,
      Round5.Round2.shiftLeftSignedArgModel, Round5.Round2.shiftRightSignedArgModel]
    exact ⟨h.2, h.1⟩

/-- Boundary-copy correctness gives exact logical shifts and packed invariants at arbitrary original size. -/
theorem shiftNearSignedCorrectFromCopies (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.natAbs) (hi : i.val.natAbs < xs.length)
    (hk : xs.length - i.val.natAbs ≤ 64) (hcopy : shiftNearCopyContract xs) :
    ∃ A leftState rightState,
      (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, leftState) ∧
      (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, rightState) ∧
      bitValues leftState A = (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) ∧
      bitValues rightState A = (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) ∧
      Round5.Round2.PackedInvariant leftState A ∧ Round5.Round2.PackedInvariant rightState A := by
  let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
  let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have hl : left.length = xs.length := by
    unfold left
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hr : right.length = xs.length := by
    unfold right
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hol := shiftFreshObservations s left A (by rw [hl]; exact hn) rfl
    (by change int xs.length = int left.length; rw [hl])
  have hor := shiftFreshObservations s right A (by rw [hr]; exact hn) rfl
    (by change int xs.length = int right.length; rw [hr])
  have hrun := shiftNearSignedRunsFromCopies xs i hn hp hi hk hcopy
  exact ⟨A, shiftFreshHeap s ((encodeBits left).map some), shiftFreshHeap s ((encodeBits right).map some),
    hrun.1, hrun.2, hol.1, hor.1, hol.2, hor.2⟩

/-- The frozen near-end shift assertion follows from boundary copies, with zero and oversized counts included. -/
theorem BitarraysShift_nearFromCopies (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hnear : xs.length ≤ i.val.natAbs + 64)
    (hcopy : shiftNearCopyContract xs) : Round5.Round2.ShiftAgrees xs i := by
  by_cases hs : xs.length ≤ 128
  · exact BitarraysShift_twoChunks xs i hs
  · by_cases hl : xs.length ≤ i.val.natAbs
    · exact BitarraysShift_oversized xs i hn hl
    · obtain ⟨A, leftState, rightState, hrL, hrR, hvL, hvR, _, _⟩ :=
        shiftNearSignedCorrectFromCopies xs i hn (by omega) (by omega) (by omega) hcopy
      unfold Round5.Round2.ShiftAgrees
      dsimp only
      rw [hrL, hrR]
      exact ⟨hvL, hvR⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A left shift retaining at most one word has no nonzero high output chunks. -/
theorem shiftNearLeftHighZero (xs : List Bool) (count chunk : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64) (hp : 0 < chunk) :
    packedPrefix (shiftLeftBits xs count) chunk 64 = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ chunk bit hb, packedBit_zero, shiftSingleLeftGet xs count _ hc, if_neg (by omega)]

/-- A left shift retaining at most one word is obtained by replacing the low zero word with its preserved suffix. -/
theorem shiftNearLeftEncoding (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64) :
    (List.replicate (wordCount xs.length) (u64 0)).set 0
      (copyPairPaste (u64 0) (copyPairSlice xs count) 0 (xs.length - count)) =
      encodeBits (shiftLeftBits xs count) := by
  have hp : 0 < wordCount xs.length := by unfold wordCount; omega
  have hlow := shiftPairLeftLow xs count hc
  rw [Nat.min_eq_left hk] at hlow
  apply List.ext_getElem
  · simp only [List.length_set, List.length_replicate, packedEncoded_length, shiftSingleLeftLength]
  · intro chunk hj hj'
    have hb : chunk < wordCount xs.length := by simpa only [List.length_set, List.length_replicate] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ 0 chunk _ (by rw [List.length_replicate]; exact hp),
      shiftNearLeftEncodedGet _ chunk (by rw [shiftSingleLeftLength]; exact hb)]
    by_cases hz : chunk = 0
    · subst chunk
      rw [if_pos rfl]
      exact hlow
    · rw [if_neg (by omega), shiftNearLeftHighZero xs count chunk hc hk (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hb, ite_true, Option.getD_some]

/-- The same low-word replacement expressed in the allocator's optional-slot representation. -/
theorem shiftNearLeftSlots (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64) :
    ((encodeBits (List.replicate xs.length false)).map some).set 0
      (some (copyPairPaste (u64 0) (copyPairSlice xs count) 0 (xs.length - count))) =
      (encodeBits (shiftLeftBits xs count)).map some := by
  rw [fillFalseEncoding, ← List.map_set, shiftNearLeftEncoding xs count hc hk]

/-- Every partial left shift retaining at most 64 source bits is exact at arbitrary supported vector length. -/
theorem shiftNearLeftCopy (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length) (hk : xs.length - count ≤ 64) :
    (copyChunks 1 (int 1) 0 (int ((count + 1 : Nat) : Int)) (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (shiftLeftBits xs count)).map some)) := by
  let s := initWords (encodeBits xs)
  let slots := (encodeBits (List.replicate xs.length false)).map some
  let allocated := shiftFreshHeap s slots
  let kept := xs.length - count
  have hp : 0 < kept := by dsimp only [kept]; omega
  have hwords : 0 < wordCount xs.length := by unfold wordCount; omega
  have hlen : slots.length = wordCount xs.length := by
    simp only [slots, List.length_map, packedEncoded_length, List.length_replicate]
  have hbound : slots.length ≤ 9223372036854775807 := by
    rw [hlen]
    unfold wordCount
    omega
  have hrs : ∀ chunk, chunk < wordCount xs.length →
      (mutableGet 0 (int ((chunk + 1 : Nat) : Int))).run allocated = (.ok (packedPrefix xs chunk 64), allocated) := by
    intro chunk hchunk
    have h := shiftFreshSource (encodeBits xs) slots chunk (packedEncoded_lengthBound xs hn)
      (by rw [packedEncoded_length]; exact hchunk)
    rw [shiftNearLeftEncodedGet xs chunk hchunk] at h
    exact h
  have hg := shiftNearGatherRun xs count 0 allocated hn hc hk hrs
  have hzero : slots[0]? = some (some (u64 0)) := by
    simp only [slots, fillFalseEncoding, List.map_replicate, List.getElem?_replicate,
      hwords, ite_true]
  have hread := shiftFreshRead s slots 0 (u64 0) hbound (by rw [hlen]; exact hwords) hzero
  have hwrite := shiftFreshSet s slots 0 (copyPairPaste (u64 0) (copyPairSlice xs count) 0 kept)
    hbound (by rw [hlen]; exact hwords)
  have hout : slots.set 0 (some (copyPairPaste (u64 0) (copyPairSlice xs count) 0 kept)) =
      (encodeBits (shiftLeftBits xs count)).map some := shiftNearLeftSlots xs count hc hk
  rw [hout] at hwrite
  have hendS : int ((count + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hendD : int 1 + int kept - int 1 = int kept := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hs0 := scalar_chunks_nat count (by omega)
  have hs1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int), int (((xs.length - 1) % 64 : Nat) : Int)) := by
    rw [hendS]
    have h := scalar_chunks_nat (xs.length - 1) (by omega)
    simpa only [show xs.length - 1 + 1 = xs.length by omega] using h
  have hd1 : getChunksId (int 1 + int kept - int 1) = (int 1, int ((0 + kept - 1 : Nat) : Int)) := by
    rw [hendD]
    have h := rangeSingleAddress (kept - 1) (by omega)
    simpa only [Nat.zero_add, show kept - 1 + 1 = kept by omega] using h
  apply copyPairOneRun 1 0 _ _ kept 0 (int 1)
    (int ((count / 64 + 1 : Nat) : Int)) (int ((count % 64 : Nat) : Int))
    (int (((xs.length - 1) / 64 + 1 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int))
    allocated _ (u64 0) (copyPairSlice xs count) hp (by omega)
    (by intro h; exact (by decide : (1 : Nat) ≠ 0) h.1) rfl hd1 hs0 hs1 hg
  · exact hread
  · exact hwrite
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- The first destination boundary word of a right shift retaining at most one source word. -/
def shiftNearRightLow (xs : List Bool) (count : Nat) : U64 :=
  copyPairPaste (u64 0) (shiftPairRightFirst xs (xs.length - count)) (count % 64)
    (min (xs.length - count) (64 - count % 64))

/-- The second destination boundary word, if the retained prefix crosses a word boundary. -/
def shiftNearRightHigh (xs : List Bool) (count : Nat) : U64 :=
  copyPairPaste (u64 0)
    (copyPairCarry (shiftPairRightFirst xs (xs.length - count)) (u64 0) (count % 64))
    0 (count % 64 + (xs.length - count) - 64)

/-- Only the final one or two words of the zero-filled destination are changed. -/
def shiftNearRightWords (xs : List Bool) (count : Nat) : List U64 :=
  let zeros := encodeBits (List.replicate xs.length false)
  let first := zeros.set (count / 64) (shiftNearRightLow xs count)
  if count % 64 + (xs.length - count) ≤ 64 then first
  else first.set (count / 64 + 1) (shiftNearRightHigh xs count)
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The first boundary paste is the exact corresponding word of the logical right shift. -/
theorem shiftNearRightLowEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64) :
    shiftNearRightLow xs count = packedPrefix (shiftRightBits xs count) (count / 64) 64 := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  apply packedBit_ext
  intro bit hb
  rw [shiftNearRightLow, copyPairPasteBit _ _ (count % 64) _ bit (by omega) hb,
    packedWord_bit _ _ bit hb, shiftSingleRightGet xs count _ hc]
  by_cases hi : count % 64 ≤ bit ∧ bit < count % 64 + min (xs.length - count) (64 - count % 64)
  · rw [if_pos hi, if_pos (by omega), shiftPairRightFirstBit xs (xs.length - count)
      (bit - count % 64) (by omega) (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]

/-- The carried boundary paste is the exact next word of the logical right shift. -/
theorem shiftNearRightHighEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64)
    (hcross : 64 < count % 64 + (xs.length - count)) :
    shiftNearRightHigh xs count = packedPrefix (shiftRightBits xs count) (count / 64 + 1) 64 := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  have hnext : shiftPairRightNext xs (xs.length - count) = u64 0 := by
    simp only [shiftPairRightNext, hk, ite_true]
  apply packedBit_ext
  intro bit hb
  rw [shiftNearRightHigh, ← hnext, copyPairPasteBit _ _ 0 _ bit (by omega) hb,
    packedWord_bit _ _ bit hb, shiftSingleRightGet xs count _ hc]
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  by_cases hi : bit < count % 64 + (xs.length - count) - 64
  · rw [if_pos hi, if_pos (by omega), shiftPairRightCarryBit xs (xs.length - count)
      (count % 64) bit (by omega) hb (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), hnext, packedBit_zero]

/-- Every word outside the one or two written boundaries consists entirely of false bits. -/
theorem shiftNearRightOtherZero (xs : List Bool) (count chunk : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64)
    (hfirst : count / 64 ≠ chunk)
    (hsecond : count % 64 + (xs.length - count) ≤ 64 ∨ count / 64 + 1 ≠ chunk) :
    packedPrefix (shiftRightBits xs count) chunk 64 = u64 0 := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ _ bit hb, shiftSingleRightGet xs count _ hc,
    if_neg (by omega), packedBit_zero]

/-- Every observation of a false-filled packed list, including the fallback, is zero. -/
theorem shiftNearZerosGet (n chunk : Nat) :
    (encodeBits (List.replicate n false)).getD chunk (u64 0) = u64 0 := by
  rw [fillFalseEncoding]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- The boundary update list is exactly the packed encoding of the near-end right shift. -/
theorem shiftNearRightWordsEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64) :
    shiftNearRightWords xs count = encodeBits (shiftRightBits xs count) := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  let zeros := encodeBits (List.replicate xs.length false)
  have hlength : zeros.length = wordCount xs.length := by
    simp only [zeros, packedEncoded_length, List.length_replicate]
  have hfirst : count / 64 < zeros.length := by rw [hlength]; unfold wordCount; omega
  unfold shiftNearRightWords
  by_cases hs : count % 64 + (xs.length - count) ≤ 64
  · rw [if_pos hs]
    apply List.ext_getElem
    · simp only [List.length_set, packedEncoded_length, List.length_replicate, shiftSingleRightLength]
    · intro chunk hj hj'
      rw [List.getElem_eq_getD (fallback := u64 0), dequeWordGetSet _ _ chunk _ hfirst]
      have he : (encodeBits (shiftRightBits xs count))[chunk] =
          packedPrefix (shiftRightBits xs count) chunk 64 := by
        simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
      rw [he]
      by_cases hi : count / 64 = chunk
      · subst chunk
        rw [if_pos rfl]
        exact shiftNearRightLowEncode xs count hc hk
      · rw [if_neg hi, shiftNearZerosGet]
        exact (shiftNearRightOtherZero xs count chunk hc hk hi (Or.inl hs)).symm
  · rw [if_neg hs]
    have hsecond : count / 64 + 1 < zeros.length := by rw [hlength]; unfold wordCount; omega
    apply List.ext_getElem
    · simp only [List.length_set, packedEncoded_length, List.length_replicate, shiftSingleRightLength]
    · intro chunk hj hj'
      rw [List.getElem_eq_getD (fallback := u64 0), dequeWordGetSet _ _ chunk _
        (by rw [List.length_set]; exact hsecond)]
      have he : (encodeBits (shiftRightBits xs count))[chunk] =
          packedPrefix (shiftRightBits xs count) chunk 64 := by
        simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
      rw [he]
      by_cases hi : count / 64 + 1 = chunk
      · subst chunk
        rw [if_pos rfl]
        exact shiftNearRightHighEncode xs count hc hk (by omega)
      · rw [if_neg hi, dequeWordGetSet _ _ chunk _ hfirst]
        by_cases hi0 : count / 64 = chunk
        · subst chunk
          rw [if_pos rfl]
          exact shiftNearRightLowEncode xs count hc hk
        · rw [if_neg hi0, shiftNearZerosGet]
          exact (shiftNearRightOtherZero xs count chunk hc hk hi0 (Or.inr hi)).symm
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Reading an initialized fresh packed word returns its list observation. -/
theorem shiftNearFreshRead (s : State) (words : List U64) (j : Nat)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableGet s.arrays.length (int ((j + 1 : Nat) : Int))).run
      (shiftFreshHeap s (words.map some)) =
        (.ok (words.getD j (u64 0)), shiftFreshHeap s (words.map some)) := by
  apply shiftFreshRead s (words.map some) j (words.getD j (u64 0))
    (by rw [List.length_map]; exact hn) (by rw [List.length_map]; exact hj)
  rw [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem_eq_getD]
  rfl

/-- Fresh packed-word replacement commutes with optional-slot initialization. -/
theorem shiftNearFreshWrite (s : State) (words : List U64) (j : Nat) (word : U64)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableSet s.arrays.length word (int ((j + 1 : Nat) : Int))).run
      (shiftFreshHeap s (words.map some)) =
        (.ok (), shiftFreshHeap s ((words.set j word).map some)) := by
  have h := shiftFreshSet s (words.map some) j word
    (by rw [List.length_map]; exact hn) (by rw [List.length_map]; exact hj)
  rw [← List.map_set] at h
  exact h

/-- Encoded words have their direct packed-prefix value at every valid chunk index. -/
theorem shiftNearEncodedGet (xs : List Bool) (j : Nat) (hj : j < wordCount xs.length) :
    (encodeBits xs).getD j (u64 0) = packedPrefix xs j 64 := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [packedEncoded_length]; exact hj), Option.getD_some]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]

/-- A partial right shift retaining at most one source word has an exact boundary-write execution. -/
theorem shiftNearRightCopyWords (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hk : xs.length - count ≤ 64) :
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1)
      (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs)) ((shiftNearRightWords xs count).map some)) := by
  let s := initWords (encodeBits xs)
  let zeros := encodeBits (List.replicate xs.length false)
  let kept := xs.length - count
  let chunk := count / 64
  let offset := count % 64
  let first := shiftPairRightFirst xs kept
  let low := shiftNearRightLow xs count
  let high := shiftNearRightHigh xs count
  let lowWords := zeros.set chunk low
  let allocated := shiftFreshHeap s (zeros.map some)
  let middle := shiftFreshHeap s (lowWords.map some)
  have hmod : offset < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  have hkept : 0 < kept := by dsimp only [kept]; omega
  have hzlen : zeros.length = wordCount xs.length := by
    simp only [zeros, packedEncoded_length, List.length_replicate]
  have hzbound : zeros.length ≤ 9223372036854775807 := by
    rw [hzlen]
    unfold wordCount
    omega
  have hchunk : chunk < zeros.length := by
    rw [hzlen]
    dsimp only [chunk]
    unfold wordCount
    omega
  have hsource : (mutableGet 0 (int 1)).run allocated = (.ok (packedPrefix xs 0 64), allocated) := by
    have h := shiftFreshSource (encodeBits xs) (zeros.map some) 0
      (packedEncoded_lengthBound xs hn) (by rw [packedEncoded_length]; unfold wordCount; omega)
    have he : (encodeBits xs).getD 0 (u64 0) = packedPrefix xs 0 64 :=
      shiftNearEncodedGet xs 0 (by unfold wordCount; omega)
    simpa only [Nat.zero_add, Int.ofNat_one, he] using h
  have hg := shiftPairPrefixFirstRun xs kept 0 allocated hkept hsource
  have hs0 : getChunksId (int 1) = (int 1, int (0 : Nat)) := rfl
  have hs1 : getChunksId (int 1 + int kept - int 1) =
      (shiftPairPrefixChunk kept, int (shiftPairPrefixBit kept)) := by
    have he : int 1 + int kept - int 1 = int kept := by
      rw [packedInt_add, dequeIntSub]
      exact congrArg int (by omega)
    rw [he]
    exact shiftPairPrefixAddress kept hkept (by dsimp only [kept]; omega)
  have hd0 : getChunksId (int ((count + 1 : Nat) : Int)) =
      (int ((chunk + 1 : Nat) : Int), int offset) := scalar_chunks_nat count (by omega)
  have hdestEnd : int ((count + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hlast := scalar_chunks_nat (xs.length - 1) (by omega)
  rw [show xs.length - 1 + 1 = xs.length by omega] at hlast
  have hr0 : (mutableGet 1 (int ((chunk + 1 : Nat) : Int))).run allocated =
      (.ok (u64 0), allocated) := by
    have h := shiftNearFreshRead s zeros chunk hzbound hchunk
    rw [shiftNearZerosGet] at h
    exact h
  have hw0 : (mutableSet 1 low (int ((chunk + 1 : Nat) : Int))).run allocated = (.ok (), middle) :=
    shiftNearFreshWrite s zeros chunk low hzbound hchunk
  have hf : ¬ (1 = (0 : Nat) ∧ int ((count + 1 : Nat) : Int) > int 1) := by
    intro h
    exact (by decide : (1 : Nat) ≠ 0) h.1
  by_cases hs : offset + kept ≤ 64
  · have hmin : min kept (64 - offset) = kept := Nat.min_eq_left (by omega)
    have heLow : low = copyPairPaste (u64 0) first offset kept := by
      change copyPairPaste (u64 0) first offset (min kept (64 - offset)) = _
      rw [hmin]
    have hd1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
        (int ((chunk + 1 : Nat) : Int), int ((offset + kept - 1 : Nat) : Int)) := by
      rw [hdestEnd, hlast]
      have hq : (xs.length - 1) / 64 = chunk := by dsimp only [chunk, offset, kept] at *; omega
      have hm : (xs.length - 1) % 64 = offset + kept - 1 := by dsimp only [chunk, offset, kept] at *; omega
      rw [hq, hm]
    have hr := copyPairOneRun 1 0 _ _ kept offset (int ((chunk + 1 : Nat) : Int))
      (int 1) (int (0 : Nat)) (shiftPairPrefixChunk kept) (int (shiftPairPrefixBit kept))
      allocated middle (u64 0) first hkept hs hf hd0 hd1 hs0 hs1 hg hr0 (by rw [← heLow]; exact hw0)
    exact hr.trans (by
      rw [shiftNearRightWords, if_pos (show count % 64 + (xs.length - count) ≤ 64 from hs)])
  · have hcross : 64 < offset + kept := by omega
    have hmin : min kept (64 - offset) = 64 - offset := Nat.min_eq_right (by omega)
    have heLow : low = copyPairPaste (u64 0) first offset (64 - offset) := by
      change copyPairPaste (u64 0) first offset (min kept (64 - offset)) = _
      rw [hmin]
    have hchunk1 : chunk + 1 < zeros.length := by
      rw [hzlen]
      dsimp only [chunk, offset, kept] at *
      unfold wordCount
      omega
    have hdiff : int ((chunk + 1 + 1 : Nat) : Int) - int ((chunk + 1 : Nat) : Int) = int 1 := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    have hd1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
        (int ((chunk + 1 + 1 : Nat) : Int), int ((offset + kept - 64 - 1 : Nat) : Int)) := by
      rw [hdestEnd, hlast]
      have hq : (xs.length - 1) / 64 = chunk + 1 := by dsimp only [chunk, offset, kept] at *; omega
      have hm : (xs.length - 1) % 64 = offset + kept - 64 - 1 := by dsimp only [chunk, offset, kept] at *; omega
      rw [hq, hm]
    have hnext : ((if shiftPairPrefixChunk kept ≥ int 1 + int 1 then
        glueSrcBitChunks 0 (int 1 + int 1) (shiftPairPrefixChunk kept)
          (copyPairSourceMask (int 1) (shiftPairPrefixChunk kept) (int (0 : Nat))
            (int (shiftPairPrefixBit kept))) (int (0 : Nat)) else pure (u64 0)) : BitMutationM U64).run middle =
        (.ok (u64 0), middle) := by
      simp only [shiftPairPrefixChunk, show kept ≤ 64 from hk, ite_true,
        show ¬ int 1 ≥ int 1 + int 1 from by decide, ite_false, shape_run_pure]
    have hr1 : (mutableGet 1 (int ((chunk + 1 + 1 : Nat) : Int))).run middle =
        (.ok (u64 0), middle) := by
      have h := shiftNearFreshRead s lowWords (chunk + 1)
        (by dsimp only [lowWords]; rw [List.length_set]; exact hzbound)
        (by dsimp only [lowWords]; rw [List.length_set]; exact hchunk1)
      have he : lowWords.getD (chunk + 1) (u64 0) = u64 0 := by
        rw [dequeWordGetSet zeros chunk (chunk + 1) low hchunk, if_neg (by omega), shiftNearZerosGet]
      rw [he] at h
      exact h
    have hw1 : (mutableSet 1 high (int ((chunk + 1 + 1 : Nat) : Int))).run middle =
        (.ok (), shiftFreshHeap s ((lowWords.set (chunk + 1) high).map some)) :=
      shiftNearFreshWrite s lowWords (chunk + 1) high
        (by dsimp only [lowWords]; rw [List.length_set]; exact hzbound)
        (by dsimp only [lowWords]; rw [List.length_set]; exact hchunk1)
    have hr := shiftNearTwoRun 1 0 _ _ (int kept) offset (offset + kept - 64)
      (int ((chunk + 1 : Nat) : Int)) (int ((chunk + 1 + 1 : Nat) : Int))
      (int 1) (int (0 : Nat)) (shiftPairPrefixChunk kept) (int (shiftPairPrefixBit kept))
      allocated middle _ (u64 0) (u64 0) first (u64 0)
      (by omega) (by omega) (by dsimp only [kept] at *; omega)
      (fillPositiveLength kept hkept (by dsimp only [kept]; omega)) hf hdiff hd0 hd1 hs0 hs1 hg
      hr0 (by rw [← heLow]; exact hw0) hnext hr1 hw1
    exact hr.trans (by
      rw [shiftNearRightWords, if_neg (show ¬ count % 64 + (xs.length - count) ≤ 64 from hs)])

/-- Right shifts retaining at most sixty-four bits execute correctly at every supported original length. -/
theorem shiftNearRightCopy (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hk : xs.length - count ≤ 64) :
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1)
      (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (shiftRightBits xs count)).map some)) := by
  exact (shiftNearRightCopyWords xs count hn hc hk).trans (by rw [shiftNearRightWordsEncode xs count hc hk])
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Both concrete public boundary copies satisfy the near-end contract at every native original length. -/
theorem shiftNearCopiesCorrect (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    shiftNearCopyContract xs := by
  intro count hc hk
  exact ⟨shiftNearLeftCopy xs count hn hc hk, shiftNearRightCopy xs count hn hc hk⟩

/-- A signed partial shift retaining at most 64 source bits has exact logical results and packed padding. -/
theorem shiftNearSignedCorrect (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.natAbs) (hi : i.val.natAbs < xs.length)
    (hk : xs.length - i.val.natAbs ≤ 64) :
    ∃ A leftState rightState,
      (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, leftState) ∧
      (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, rightState) ∧
      bitValues leftState A = (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) ∧
      bitValues rightState A = (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) ∧
      Round5.Round2.PackedInvariant leftState A ∧ Round5.Round2.PackedInvariant rightState A :=
  shiftNearSignedCorrectFromCopies xs i hn hp hi hk (shiftNearCopiesCorrect xs hn)

/-- The exact frozen assertion holds whenever at most 64 original bits can survive the signed shift. -/
theorem BitarraysShift_nearEnd (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hnear : xs.length ≤ i.val.natAbs + 64) :
    Round5.Round2.ShiftAgrees xs i :=
  BitarraysShift_nearFromCopies xs i hn hnear (shiftNearCopiesCorrect xs hn)

/-- A single frozen assertion combines two-word inputs, arbitrary-length zero shifts, and near-end counts. -/
theorem BitarraysShift_extendedCases (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hc : xs.length ≤ 128 ∨ i = int 0 ∨ xs.length ≤ i.val.natAbs + 64) :
    Round5.Round2.ShiftAgrees xs i := by
  rcases hc with hsmall | hzero | hnear
  · exact BitarraysShift_twoChunks xs i hsmall
  · exact BitarraysShift_zeroAt xs i hn hzero
  · exact BitarraysShift_nearEnd xs i hn hnear
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- The second boundary word uses the actual second retained source word when it is present. -/
def shiftWindowRightHigh (xs : List Bool) (count : Nat) : U64 :=
  copyPairPaste (u64 0)
    (copyPairCarry (shiftPairRightFirst xs (xs.length - count))
      (shiftPairRightNext xs (xs.length - count)) (count % 64))
    0 (count % 64 + (xs.length - count) - 64)

/-- A rightward retained prefix spanning at most two destination chunks changes only those boundary chunks. -/
def shiftWindowRightWords (xs : List Bool) (count : Nat) : List U64 :=
  let zeros := encodeBits (List.replicate xs.length false)
  let first := zeros.set (count / 64) (shiftNearRightLow xs count)
  if count % 64 + (xs.length - count) ≤ 64 then first
  else first.set (count / 64 + 1) (shiftWindowRightHigh xs count)
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The first boundary paste is the exact corresponding word of the logical right shift. -/
theorem shiftWindowRightLowEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : count % 64 + (xs.length - count) ≤ 128) :
    shiftNearRightLow xs count = packedPrefix (shiftRightBits xs count) (count / 64) 64 := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  apply packedBit_ext
  intro bit hb
  rw [shiftNearRightLow, copyPairPasteBit _ _ (count % 64) _ bit (by omega) hb,
    packedWord_bit _ _ bit hb, shiftSingleRightGet xs count _ hc]
  by_cases hi : count % 64 ≤ bit ∧ bit < count % 64 + min (xs.length - count) (64 - count % 64)
  · rw [if_pos hi, if_pos (by omega), shiftPairRightFirstBit xs (xs.length - count)
      (bit - count % 64) (by omega) (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]

/-- The carried boundary paste is the exact next word of the logical right shift. -/
theorem shiftWindowRightHighEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : count % 64 + (xs.length - count) ≤ 128)
    (hcross : 64 < count % 64 + (xs.length - count)) :
    shiftWindowRightHigh xs count = packedPrefix (shiftRightBits xs count) (count / 64 + 1) 64 := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  apply packedBit_ext
  intro bit hb
  rw [shiftWindowRightHigh, copyPairPasteBit _ _ 0 _ bit (by omega) hb,
    packedWord_bit _ _ bit hb, shiftSingleRightGet xs count _ hc]
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  by_cases hi : bit < count % 64 + (xs.length - count) - 64
  · rw [if_pos hi, if_pos (by omega), shiftPairRightCarryBit xs (xs.length - count)
      (count % 64) bit (by omega) hb (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]

/-- Every word outside the one or two written boundaries consists entirely of false bits. -/
theorem shiftWindowRightOtherZero (xs : List Bool) (count chunk : Nat)
    (hc : count < xs.length) (hk : count % 64 + (xs.length - count) ≤ 128)
    (hfirst : count / 64 ≠ chunk)
    (hsecond : count % 64 + (xs.length - count) ≤ 64 ∨ count / 64 + 1 ≠ chunk) :
    packedPrefix (shiftRightBits xs count) chunk 64 = u64 0 := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ _ bit hb, shiftSingleRightGet xs count _ hc,
    if_neg (by omega), packedBit_zero]

/-- The boundary update list is exactly the packed encoding of the near-end right shift. -/
theorem shiftWindowRightWordsEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : count % 64 + (xs.length - count) ≤ 128) :
    shiftWindowRightWords xs count = encodeBits (shiftRightBits xs count) := by
  have hmod : count % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  let zeros := encodeBits (List.replicate xs.length false)
  have hlength : zeros.length = wordCount xs.length := by
    simp only [zeros, packedEncoded_length, List.length_replicate]
  have hfirst : count / 64 < zeros.length := by rw [hlength]; unfold wordCount; omega
  unfold shiftWindowRightWords
  by_cases hs : count % 64 + (xs.length - count) ≤ 64
  · rw [if_pos hs]
    apply List.ext_getElem
    · simp only [List.length_set, packedEncoded_length, List.length_replicate, shiftSingleRightLength]
    · intro chunk hj hj'
      rw [List.getElem_eq_getD (fallback := u64 0), dequeWordGetSet _ _ chunk _ hfirst]
      have he : (encodeBits (shiftRightBits xs count))[chunk] =
          packedPrefix (shiftRightBits xs count) chunk 64 := by
        simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
      rw [he]
      by_cases hi : count / 64 = chunk
      · subst chunk
        rw [if_pos rfl]
        exact shiftWindowRightLowEncode xs count hc hk
      · rw [if_neg hi, shiftNearZerosGet]
        exact (shiftWindowRightOtherZero xs count chunk hc hk hi (Or.inl hs)).symm
  · rw [if_neg hs]
    have hsecond : count / 64 + 1 < zeros.length := by rw [hlength]; unfold wordCount; omega
    apply List.ext_getElem
    · simp only [List.length_set, packedEncoded_length, List.length_replicate, shiftSingleRightLength]
    · intro chunk hj hj'
      rw [List.getElem_eq_getD (fallback := u64 0), dequeWordGetSet _ _ chunk _
        (by rw [List.length_set]; exact hsecond)]
      have he : (encodeBits (shiftRightBits xs count))[chunk] =
          packedPrefix (shiftRightBits xs count) chunk 64 := by
        simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
      rw [he]
      by_cases hi : count / 64 + 1 = chunk
      · subst chunk
        rw [if_pos rfl]
        exact shiftWindowRightHighEncode xs count hc hk (by omega)
      · rw [if_neg hi, dequeWordGetSet _ _ chunk _ hfirst]
        by_cases hi0 : count / 64 = chunk
        · subst chunk
          rw [if_pos rfl]
          exact shiftWindowRightLowEncode xs count hc hk
        · rw [if_neg hi0, shiftNearZerosGet]
          exact (shiftWindowRightOtherZero xs count chunk hc hk hi0 (Or.inr hi)).symm
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A partial right shift whose retained destination spans at most two packed words has an exact boundary-write execution. -/
theorem shiftWindowRightCopyWords (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hk : count % 64 + (xs.length - count) ≤ 128) :
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1)
      (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs)) ((shiftWindowRightWords xs count).map some)) := by
  let s := initWords (encodeBits xs)
  let zeros := encodeBits (List.replicate xs.length false)
  let kept := xs.length - count
  let chunk := count / 64
  let offset := count % 64
  let first := shiftPairRightFirst xs kept
  let low := shiftNearRightLow xs count
  let high := shiftWindowRightHigh xs count
  let lowWords := zeros.set chunk low
  let allocated := shiftFreshHeap s (zeros.map some)
  let middle := shiftFreshHeap s (lowWords.map some)
  have hmod : offset < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div count 64
  have hkept : 0 < kept := by dsimp only [kept]; omega
  have hzlen : zeros.length = wordCount xs.length := by
    simp only [zeros, packedEncoded_length, List.length_replicate]
  have hzbound : zeros.length ≤ 9223372036854775807 := by
    rw [hzlen]
    unfold wordCount
    omega
  have hchunk : chunk < zeros.length := by
    rw [hzlen]
    dsimp only [chunk]
    unfold wordCount
    omega
  have hsource : (mutableGet 0 (int 1)).run allocated = (.ok (packedPrefix xs 0 64), allocated) := by
    have h := shiftFreshSource (encodeBits xs) (zeros.map some) 0
      (packedEncoded_lengthBound xs hn) (by rw [packedEncoded_length]; unfold wordCount; omega)
    have he : (encodeBits xs).getD 0 (u64 0) = packedPrefix xs 0 64 :=
      shiftNearEncodedGet xs 0 (by unfold wordCount; omega)
    simpa only [Nat.zero_add, Int.ofNat_one, he] using h
  have hg := shiftPairPrefixFirstRun xs kept 0 allocated hkept hsource
  have hs0 : getChunksId (int 1) = (int 1, int (0 : Nat)) := rfl
  have hs1 : getChunksId (int 1 + int kept - int 1) =
      (shiftPairPrefixChunk kept, int (shiftPairPrefixBit kept)) := by
    have he : int 1 + int kept - int 1 = int kept := by
      rw [packedInt_add, dequeIntSub]
      exact congrArg int (by omega)
    rw [he]
    exact shiftPairPrefixAddress kept hkept (by dsimp only [kept]; omega)
  have hd0 : getChunksId (int ((count + 1 : Nat) : Int)) =
      (int ((chunk + 1 : Nat) : Int), int offset) := scalar_chunks_nat count (by omega)
  have hdestEnd : int ((count + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hlast := scalar_chunks_nat (xs.length - 1) (by omega)
  rw [show xs.length - 1 + 1 = xs.length by omega] at hlast
  have hr0 : (mutableGet 1 (int ((chunk + 1 : Nat) : Int))).run allocated =
      (.ok (u64 0), allocated) := by
    have h := shiftNearFreshRead s zeros chunk hzbound hchunk
    rw [shiftNearZerosGet] at h
    exact h
  have hw0 : (mutableSet 1 low (int ((chunk + 1 : Nat) : Int))).run allocated = (.ok (), middle) :=
    shiftNearFreshWrite s zeros chunk low hzbound hchunk
  have hf : ¬ (1 = (0 : Nat) ∧ int ((count + 1 : Nat) : Int) > int 1) := by
    intro h
    exact (by decide : (1 : Nat) ≠ 0) h.1
  by_cases hs : offset + kept ≤ 64
  · have hmin : min kept (64 - offset) = kept := Nat.min_eq_left (by omega)
    have heLow : low = copyPairPaste (u64 0) first offset kept := by
      change copyPairPaste (u64 0) first offset (min kept (64 - offset)) = _
      rw [hmin]
    have hd1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
        (int ((chunk + 1 : Nat) : Int), int ((offset + kept - 1 : Nat) : Int)) := by
      rw [hdestEnd, hlast]
      have hq : (xs.length - 1) / 64 = chunk := by dsimp only [chunk, offset, kept] at *; omega
      have hm : (xs.length - 1) % 64 = offset + kept - 1 := by dsimp only [chunk, offset, kept] at *; omega
      rw [hq, hm]
    have hr := copyPairOneRun 1 0 _ _ kept offset (int ((chunk + 1 : Nat) : Int))
      (int 1) (int (0 : Nat)) (shiftPairPrefixChunk kept) (int (shiftPairPrefixBit kept))
      allocated middle (u64 0) first hkept hs hf hd0 hd1 hs0 hs1 hg hr0 (by rw [← heLow]; exact hw0)
    exact hr.trans (by
      rw [shiftWindowRightWords, if_pos (show count % 64 + (xs.length - count) ≤ 64 from hs)])
  · have hcross : 64 < offset + kept := by omega
    have hmin : min kept (64 - offset) = 64 - offset := Nat.min_eq_right (by omega)
    have heLow : low = copyPairPaste (u64 0) first offset (64 - offset) := by
      change copyPairPaste (u64 0) first offset (min kept (64 - offset)) = _
      rw [hmin]
    have hchunk1 : chunk + 1 < zeros.length := by
      rw [hzlen]
      dsimp only [chunk, offset, kept] at *
      unfold wordCount
      omega
    have hdiff : int ((chunk + 1 + 1 : Nat) : Int) - int ((chunk + 1 : Nat) : Int) = int 1 := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    have hd1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
        (int ((chunk + 1 + 1 : Nat) : Int), int ((offset + kept - 64 - 1 : Nat) : Int)) := by
      rw [hdestEnd, hlast]
      have hq : (xs.length - 1) / 64 = chunk + 1 := by dsimp only [chunk, offset, kept] at *; omega
      have hm : (xs.length - 1) % 64 = offset + kept - 64 - 1 := by dsimp only [chunk, offset, kept] at *; omega
      rw [hq, hm]
    have hnext : ((if shiftPairPrefixChunk kept ≥ int 1 + int 1 then
        glueSrcBitChunks 0 (int 1 + int 1) (shiftPairPrefixChunk kept)
          (copyPairSourceMask (int 1) (shiftPairPrefixChunk kept) (int (0 : Nat))
            (int (shiftPairPrefixBit kept))) (int (0 : Nat)) else pure (u64 0)) : BitMutationM U64).run middle =
        (.ok (shiftPairRightNext xs kept), middle) := by
      by_cases hsmall : kept ≤ 64
      · simp only [shiftPairPrefixChunk, shiftPairRightNext, hsmall, ite_true,
          show ¬ int 1 ≥ int 1 + int 1 from by decide, ite_false, shape_run_pure]
      · have hread : (mutableGet 0 (int 2)).run middle =
            (.ok (packedPrefix xs 1 64), middle) := by
          have h := shiftFreshSource (encodeBits xs) (lowWords.map some) 1
            (packedEncoded_lengthBound xs hn) (by rw [packedEncoded_length]; unfold wordCount; dsimp only [kept] at hsmall; omega)
          have he := shiftNearEncodedGet xs 1
            (by unfold wordCount; dsimp only [kept] at hsmall; omega)
          simpa only [show int ((1 + 1 : Nat) : Int) = int 2 from rfl, he] using h
        exact shiftPairPrefixNextRun xs kept 0 middle hread
    have hr1 : (mutableGet 1 (int ((chunk + 1 + 1 : Nat) : Int))).run middle =
        (.ok (u64 0), middle) := by
      have h := shiftNearFreshRead s lowWords (chunk + 1)
        (by dsimp only [lowWords]; rw [List.length_set]; exact hzbound)
        (by dsimp only [lowWords]; rw [List.length_set]; exact hchunk1)
      have he : lowWords.getD (chunk + 1) (u64 0) = u64 0 := by
        rw [dequeWordGetSet zeros chunk (chunk + 1) low hchunk, if_neg (by omega), shiftNearZerosGet]
      rw [he] at h
      exact h
    have hw1 : (mutableSet 1 high (int ((chunk + 1 + 1 : Nat) : Int))).run middle =
        (.ok (), shiftFreshHeap s ((lowWords.set (chunk + 1) high).map some)) :=
      shiftNearFreshWrite s lowWords (chunk + 1) high
        (by dsimp only [lowWords]; rw [List.length_set]; exact hzbound)
        (by dsimp only [lowWords]; rw [List.length_set]; exact hchunk1)
    have hr := shiftNearTwoRun 1 0 _ _ (int kept) offset (offset + kept - 64)
      (int ((chunk + 1 : Nat) : Int)) (int ((chunk + 1 + 1 : Nat) : Int))
      (int 1) (int (0 : Nat)) (shiftPairPrefixChunk kept) (int (shiftPairPrefixBit kept))
      allocated middle _ (u64 0) (u64 0) first (shiftPairRightNext xs kept)
      (by omega) (by omega) (by dsimp only [kept] at *; omega)
      (fillPositiveLength kept hkept (by dsimp only [kept]; omega)) hf hdiff hd0 hd1 hs0 hs1 hg
      hr0 (by rw [← heLow]; exact hw0) hnext hr1 hw1
    exact hr.trans (by
      rw [shiftWindowRightWords, if_neg (show ¬ count % 64 + (xs.length - count) ≤ 64 from hs)])

/-- Right shifts with at most two destination boundary words execute correctly at every supported original length. -/
theorem shiftWindowRightCopy (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hk : count % 64 + (xs.length - count) ≤ 128) :
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1)
      (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (shiftRightBits xs count)).map some)) := by
  exact (shiftWindowRightCopyWords xs count hn hc hk).trans (by rw [shiftWindowRightWordsEncode xs count hc hk])
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The two boundary-copy results needed when every partial destination copy occupies at most two words. -/
def shiftWindowCopyContract (xs : List Bool) : Prop :=
  ∀ count : Nat, count < xs.length → count % 64 + (xs.length - count) ≤ 128 →
    let s := initWords (encodeBits xs)
    let allocated := shiftFreshHeap s ((encodeBits (List.replicate xs.length false)).map some)
    (copyChunks 1 (int 1) 0 (int ((count + 1 : Nat) : Int))
      (int ((xs.length - count : Nat) : Int))).run allocated =
      (.ok (), shiftFreshHeap s ((encodeBits (shiftLeftBits xs count)).map some)) ∧
    (copyChunks 1 (int ((count + 1 : Nat) : Int)) 0 (int 1)
      (int ((xs.length - count : Nat) : Int))).run allocated =
      (.ok (), shiftFreshHeap s ((encodeBits (shiftRightBits xs count)).map some))

/-- Exact boundary copies lift through the public unsigned allocation and conversion wrappers. -/
theorem shiftWindowUnsignedRunsFromCopies (xs : List Bool) (i : U64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.toNat) (hi : i.val.toNat < xs.length)
    (hk : i.val.toNat % 64 + (xs.length - i.val.toNat) ≤ 128) (hcopy : shiftWindowCopyContract xs) :
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let s := initWords (encodeBits xs)
    (Round5.Round2.shiftLeftUnsignedModel (vectorBits xs) i).run s =
      (.ok A, shiftFreshHeap s ((encodeBits (shiftLeftBits xs i.val.toNat)).map some)) ∧
    (Round5.Round2.shiftRightUnsignedModel (vectorBits xs) i).run s =
      (.ok A, shiftFreshHeap s ((encodeBits (shiftRightBits xs i.val.toNat)).map some)) := by
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  let count := i.val.toNat
  have hcast : int i.val = int count := congrArg int (shiftSingleUnsignedNat i).symm
  have hsum : int count + int 1 = int ((count + 1 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  have hdiff : int xs.length - int count = int ((xs.length - count : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    dsimp only [count]
    omega
  have hcmp : JuliaLean.base.int.unsigned (vectorBits xs).len > i := by
    change i.val < (JuliaLean.base.int.unsigned (int xs.length)).val
    rw [shiftFreshUnsignedLength xs.length hn, ← shiftSingleUnsignedNat i]
    omega
  have ha := shiftFreshZeroVector xs.length (by omega) hn s
  have hc := hcopy count hi hk
  constructor
  · apply shiftSingleLeftFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits xs) A i s _ _ (shiftSingleUnsignedNonzero i hp) hcmp ha
    change (copyChunks 1 (int 1) 0 (int i.val + int 1) (int xs.length - int i.val)).run _ = _
    rw [hcast, hsum, hdiff]
    exact hc.1
  · apply shiftSingleRightFrom JuliaLean.base.int.unsigned (fun x : U64 => int x.val)
      Round5.Round2.copyBitVectorPublic Round5.Round2.zeroBitVectorModel
      (vectorBits xs) A i s _ _ (shiftSingleUnsignedNonzero i hp) hcmp ha
    change (copyChunks 1 (int i.val + int 1) 0 (int 1) (int xs.length - int i.val)).run _ = _
    rw [hcast, hsum, hdiff]
    exact hc.2

/-- Native signed dispatch retains the appropriate exact left/right encoding, including negative counts. -/
theorem shiftWindowSignedRunsFromCopies (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.natAbs) (hi : i.val.natAbs < xs.length)
    (hk : i.val.natAbs % 64 + (xs.length - i.val.natAbs) ≤ 128) (hcopy : shiftWindowCopyContract xs) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let A : BitVector := ⟨1, int xs.length, [int xs.length]⟩
    let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
    let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
    (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel B i).run s =
        (.ok A, shiftFreshHeap s ((encodeBits left).map some)) ∧
    (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel B i).run s =
        (.ok A, shiftFreshHeap s ((encodeBits right).map some)) := by
  dsimp only
  by_cases hs : 0 ≤ i.val
  · have hmag := shiftSingleNonnegativeMagnitude i hs
    have h := shiftWindowUnsignedRunsFromCopies xs (JuliaLean.base.int.unsigned i) hn
      (by rw [hmag]; exact hp) (by rw [hmag]; exact hi) (by rw [hmag]; exact hk) hcopy
    rw [hmag] at h
    have hcond : i ≥ int 0 := hs
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, hcond, hs, ite_true]
    exact h
  · have hmag := shiftSingleNegativeMagnitude i hs
    have h := shiftWindowUnsignedRunsFromCopies xs (JuliaLean.base.int.unsigned (-i)) hn
      (by rw [hmag]; exact hp) (by rw [hmag]; exact hi) (by rw [hmag]; exact hk) hcopy
    rw [hmag] at h
    have hcond : ¬ i ≥ int 0 := hs
    simp only [bitVectorShiftLeftSigned, bitVectorShiftRightSigned, id_eq, hcond, hs, ite_false,
      Round5.Round2.shiftLeftSignedArgModel, Round5.Round2.shiftRightSignedArgModel]
    exact ⟨h.2, h.1⟩

/-- Boundary-copy correctness gives exact logical shifts and packed invariants at arbitrary original size. -/
theorem shiftWindowSignedCorrectFromCopies (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.natAbs) (hi : i.val.natAbs < xs.length)
    (hk : i.val.natAbs % 64 + (xs.length - i.val.natAbs) ≤ 128) (hcopy : shiftWindowCopyContract xs) :
    ∃ A leftState rightState,
      (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, leftState) ∧
      (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, rightState) ∧
      bitValues leftState A = (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) ∧
      bitValues rightState A = (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) ∧
      Round5.Round2.PackedInvariant leftState A ∧ Round5.Round2.PackedInvariant rightState A := by
  let left := if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs
  let right := if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs
  let s := initWords (encodeBits xs)
  let A : BitArray 1 := ⟨1, int xs.length, [int xs.length]⟩
  have hl : left.length = xs.length := by
    unfold left
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hr : right.length = xs.length := by
    unfold right
    split <;> simp only [shiftSingleLeftLength, shiftSingleRightLength]
  have hol := shiftFreshObservations s left A (by rw [hl]; exact hn) rfl
    (by change int xs.length = int left.length; rw [hl])
  have hor := shiftFreshObservations s right A (by rw [hr]; exact hn) rfl
    (by change int xs.length = int right.length; rw [hr])
  have hrun := shiftWindowSignedRunsFromCopies xs i hn hp hi hk hcopy
  exact ⟨A, shiftFreshHeap s ((encodeBits left).map some), shiftFreshHeap s ((encodeBits right).map some),
    hrun.1, hrun.2, hol.1, hor.1, hol.2, hor.2⟩

/-- The frozen boundary-only shift assertion follows from boundary copies, with zero and oversized counts included. -/
theorem BitarraysShift_windowFromCopies (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hwindow : i.val.natAbs % 64 + (xs.length - i.val.natAbs) ≤ 128)
    (hcopy : shiftWindowCopyContract xs) : Round5.Round2.ShiftAgrees xs i := by
  by_cases hs : xs.length ≤ 128
  · exact BitarraysShift_twoChunks xs i hs
  · by_cases hl : xs.length ≤ i.val.natAbs
    · exact BitarraysShift_oversized xs i hn hl
    · obtain ⟨A, leftState, rightState, hrL, hrR, hvL, hvR, _, _⟩ :=
        shiftWindowSignedCorrectFromCopies xs i hn (by omega) (by omega) (by omega) hcopy
      unfold Round5.Round2.ShiftAgrees
      dsimp only
      rw [hrL, hrR]
      exact ⟨hvL, hvR⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The second boundary write is the high output word whenever at most two words survive. -/
theorem shiftWindowLeftHigh (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 128) :
    copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64) =
      packedPrefix (shiftLeftBits xs count) 1 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb, packedWord_bit (shiftLeftBits xs count) 1 bit hb]
  simp only [Nat.zero_le, Nat.zero_add, Nat.one_mul, Nat.sub_zero, true_and]
  rw [shiftSingleLeftGet xs count (64 + bit) hc]
  by_cases hi : 64 + bit < xs.length - count
  · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs (count + 64) bit hb]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedBit_zero]

/-- All output words after the two retained boundary words are zero. -/
theorem shiftWindowLeftHighZero (xs : List Bool) (count chunk : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 128) (hp : 2 ≤ chunk) :
    packedPrefix (shiftLeftBits xs count) chunk 64 = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ chunk bit hb, packedBit_zero, shiftSingleLeftGet xs count _ hc,
    if_neg (by omega)]

/-- Two boundary writes give the exact logical left-shift encoding at arbitrary original length. -/
theorem shiftWindowLeftEncoding (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hp : 64 < xs.length - count) (hk : xs.length - count ≤ 128) :
    ((List.replicate (wordCount xs.length) (u64 0)).set 0
      (copyPairPaste (u64 0) (copyPairSlice xs count) 0 64)).set 1
      (copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64)) =
      encodeBits (shiftLeftBits xs count) := by
  have hw : 1 < wordCount xs.length := by unfold wordCount; omega
  have hlow := shiftPairLeftLow xs count hc
  rw [Nat.min_eq_right (by omega)] at hlow
  have hhigh := shiftWindowLeftHigh xs count hc hk
  apply List.ext_getElem
  · simp only [List.length_set, List.length_replicate, packedEncoded_length, shiftSingleLeftLength]
  · intro chunk hj hj'
    have hb : chunk < wordCount xs.length := by
      simpa only [List.length_set, List.length_replicate] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ 1 chunk _ (by simp only [List.length_set, List.length_replicate]; exact hw),
      shiftNearLeftEncodedGet _ chunk (by rw [shiftSingleLeftLength]; exact hb)]
    by_cases h1 : chunk = 1
    · subst chunk
      rw [if_pos rfl]
      exact hhigh
    · rw [if_neg (by omega), dequeWordGetSet _ 0 chunk _
        (by rw [List.length_replicate]; omega)]
      by_cases hz : chunk = 0
      · subst chunk
        rw [if_pos rfl]
        exact hlow
      · rw [if_neg (by omega), shiftWindowLeftHighZero xs count chunk hc hk (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hb, ite_true, Option.getD_some]

/-- The same two boundary writes in the allocator's optional-slot representation. -/
theorem shiftWindowLeftSlots (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hp : 64 < xs.length - count) (hk : xs.length - count ≤ 128) :
    (((encodeBits (List.replicate xs.length false)).map some).set 0
      (some (copyPairPaste (u64 0) (copyPairSlice xs count) 0 64))).set 1
      (some (copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64))) =
      (encodeBits (shiftLeftBits xs count)).map some := by
  rw [fillFalseEncoding, ← List.map_set, ← List.map_set, shiftWindowLeftEncoding xs count hc hp hk]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The next gather in a two-boundary suffix copy returns the following logical window. -/
theorem shiftWindowNextGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hp : 64 < xs.length - source)
    (hr : ∀ chunk, chunk < wordCount xs.length →
      (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s)) :
    ((if int (((xs.length - 1) / 64 + 1 : Nat) : Int) ≥ int ((source / 64 + 1 : Nat) : Int) + int 1 then
      glueSrcBitChunks chunks (int ((source / 64 + 1 : Nat) : Int) + int 1)
        (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
        (copyPairSourceMask (int ((source / 64 + 1 : Nat) : Int))
          (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
          (int ((source % 64 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int)))
        (int ((source % 64 : Nat) : Int)) else pure (u64 0)) : BitMutationM U64).run s =
      (.ok (copyPairSlice xs (source + 64)), s) := by
  have hplus : int ((source / 64 + 1 : Nat) : Int) + int 1 = int ((source / 64 + 2 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hge : int (((xs.length - 1) / 64 + 1 : Nat) : Int) ≥ int ((source / 64 + 2 : Nat) : Int) := by
    change (int ((source / 64 + 2 : Nat) : Int)).val ≤ (int (((xs.length - 1) / 64 + 1 : Nat) : Int)).val
    rw [packedInt_val (source / 64 + 2) (by omega), packedInt_val ((xs.length - 1) / 64 + 1) (by omega)]
    omega
  rw [hplus, if_pos hge, shiftWindowSourceMask xs source hn hs hp]
  have h := shiftWindowHighGatherRun xs (source + 64) chunks s hn (by omega) hr
  simpa only [show (source + 64) / 64 + 1 = source / 64 + 2 by omega,
    show (source + 64) % 64 = source % 64 by omega] using h

/-- A left shift retaining between 65 and 128 bits executes exactly two initialized boundary writes. -/
theorem shiftWindowLeftCopyLong (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hp : 64 < xs.length - count) (hk : xs.length - count ≤ 128) :
    (copyChunks 1 (int 1) 0 (int ((count + 1 : Nat) : Int))
      (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs))
        ((((encodeBits (List.replicate xs.length false)).set 0
          (copyPairPaste (u64 0) (copyPairSlice xs count) 0 64)).set 1
          (copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64))).map some)) := by
  let s := initWords (encodeBits xs)
  let zeros := encodeBits (List.replicate xs.length false)
  let kept := xs.length - count
  let low := copyPairPaste (u64 0) (copyPairSlice xs count) 0 64
  let high := copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (kept - 64)
  let lowWords := zeros.set 0 low
  let allocated := shiftFreshHeap s (zeros.map some)
  let middle := shiftFreshHeap s (lowWords.map some)
  have hzlen : zeros.length = wordCount xs.length := by
    simp only [zeros, packedEncoded_length, List.length_replicate]
  have hzbound : zeros.length ≤ 9223372036854775807 := by
    rw [hzlen]
    unfold wordCount
    omega
  have htwo : 1 < zeros.length := by rw [hzlen]; unfold wordCount; omega
  have hrs : ∀ slots : List (Option U64), ∀ chunk, chunk < wordCount xs.length →
      (mutableGet 0 (int ((chunk + 1 : Nat) : Int))).run (shiftFreshHeap s slots) =
        (.ok (packedPrefix xs chunk 64), shiftFreshHeap s slots) := by
    intro slots chunk hchunk
    have h := shiftFreshSource (encodeBits xs) slots chunk (packedEncoded_lengthBound xs hn)
      (by rw [packedEncoded_length]; exact hchunk)
    rw [shiftNearLeftEncodedGet xs chunk hchunk] at h
    exact h
  have hg : (glueSrcBitChunks 0 (int ((count / 64 + 1 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
      (copyPairSourceMask (int ((count / 64 + 1 : Nat) : Int))
        (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
        (int ((count % 64 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int)))
      (int ((count % 64 : Nat) : Int))).run allocated = (.ok (copyPairSlice xs count), allocated) := by
    rw [shiftWindowSourceMask xs count hn hc hp]
    exact shiftWindowHighGatherRun xs count 0 allocated hn hc (hrs (zeros.map some))
  have hnext := shiftWindowNextGatherRun xs count 0 middle hn hc hp (hrs (lowWords.map some))
  have hr0 : (mutableGet 1 (int 1)).run allocated = (.ok (u64 0), allocated) := by
    have h := shiftNearFreshRead s zeros 0 hzbound (by omega)
    rw [shiftNearZerosGet] at h
    exact h
  have hw0 : (mutableSet 1 low (int 1)).run allocated = (.ok (), middle) :=
    shiftNearFreshWrite s zeros 0 low hzbound (by omega)
  have hr1 : (mutableGet 1 (int 2)).run middle = (.ok (u64 0), middle) := by
    have h := shiftNearFreshRead s lowWords 1 (by rw [List.length_set]; exact hzbound)
      (by rw [List.length_set]; exact htwo)
    have he : lowWords.getD 1 (u64 0) = u64 0 := by
      change (zeros.set 0 low).getD 1 (u64 0) = _
      rw [dequeWordGetSet zeros 0 1 low (by omega), if_neg (by decide)]
      exact shiftNearZerosGet xs.length 1
    rw [he] at h
    exact h
  have hw1 := shiftNearFreshWrite s lowWords 1 high
    (by rw [List.length_set]; exact hzbound) (by rw [List.length_set]; exact htwo)
  have hendS : int ((count + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hendD : int 1 + int kept - int 1 = int kept := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hs0 := scalar_chunks_nat count (by omega)
  have hs1 : getChunksId (int ((count + 1 : Nat) : Int) + int kept - int 1) =
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int), int (((xs.length - 1) % 64 : Nat) : Int)) := by
    rw [hendS]
    have h := scalar_chunks_nat (xs.length - 1) (by omega)
    simpa only [show xs.length - 1 + 1 = xs.length by omega] using h
  have hd1 : getChunksId (int 1 + int kept - int 1) =
      (int 2, int ((kept - 64 - 1 : Nat) : Int)) := by
    rw [hendD]
    simpa only [Nat.sub_sub] using copyPairFinalAddress kept hp hk
  apply copyPairTwoRun 1 0 _ _ (int kept) 0 (kept - 64)
    (int ((count / 64 + 1 : Nat) : Int)) (int ((count % 64 : Nat) : Int))
    (int (((xs.length - 1) / 64 + 1 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int))
    allocated middle _ (u64 0) (u64 0) (copyPairSlice xs count) (copyPairSlice xs (count + 64))
    (by decide) (by dsimp only [kept]; omega) (by dsimp only [kept]; omega)
    (fillPositiveLength kept (by omega) (by omega))
    (by intro h; exact (by decide : (1 : Nat) ≠ 0) h.1) rfl hd1 hs0 hs1 hg hr0 hw0 hnext hr1
  rw [copyPairCarryZero]
  exact hw1

/-- Every partial left shift retaining at most 128 source bits has an exact packed boundary-copy result. -/
theorem shiftWindowLeftCopy (xs : List Bool) (count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hk : xs.length - count ≤ 128) :
    (copyChunks 1 (int 1) 0 (int ((count + 1 : Nat) : Int))
      (int ((xs.length - count : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (List.replicate xs.length false)).map some)) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs)) ((encodeBits (shiftLeftBits xs count)).map some)) := by
  by_cases hp : xs.length - count ≤ 64
  · exact shiftNearLeftCopy xs count hn hc hp
  · have h := shiftWindowLeftCopyLong xs count hn hc (by omega) hk
    have he : ((encodeBits (List.replicate xs.length false)).set 0
          (copyPairPaste (u64 0) (copyPairSlice xs count) 0 64)).set 1
          (copyPairPaste (u64 0) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64)) =
        encodeBits (shiftLeftBits xs count) := by
      rw [fillFalseEncoding]
      exact shiftWindowLeftEncoding xs count hc (by omega) hk
    rw [he] at h
    exact h
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Both concrete public boundary copies satisfy the two-boundary contract at every native original length. -/
theorem shiftWindowCopiesCorrect (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    shiftWindowCopyContract xs := by
  intro count hc hk
  exact ⟨shiftWindowLeftCopy xs count hn hc (by omega), shiftWindowRightCopy xs count hn hc hk⟩

/-- A signed partial shift using only two boundary writes has exact logical results and packed padding. -/
theorem shiftWindowSignedCorrect (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hp : 0 < i.val.natAbs) (hi : i.val.natAbs < xs.length)
    (hk : i.val.natAbs % 64 + (xs.length - i.val.natAbs) ≤ 128) :
    ∃ A leftState rightState,
      (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, leftState) ∧
      (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
        Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok A, rightState) ∧
      bitValues leftState A = (if i.val ≥ 0 then shiftLeftBits xs i.val.natAbs else shiftRightBits xs i.val.natAbs) ∧
      bitValues rightState A = (if i.val ≥ 0 then shiftRightBits xs i.val.natAbs else shiftLeftBits xs i.val.natAbs) ∧
      Round5.Round2.PackedInvariant leftState A ∧ Round5.Round2.PackedInvariant rightState A :=
  shiftWindowSignedCorrectFromCopies xs i hn hp hi hk (shiftWindowCopiesCorrect xs hn)

/-- The exact frozen assertion holds whenever each destination copy uses at most two boundary words. -/
theorem BitarraysShift_boundaryWindow (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807) (hwindow : i.val.natAbs % 64 + (xs.length - i.val.natAbs) ≤ 128) :
    Round5.Round2.ShiftAgrees xs i :=
  BitarraysShift_windowFromCopies xs i hn hwindow (shiftWindowCopiesCorrect xs hn)

/-- A single frozen assertion combines two-word inputs, arbitrary-length zero shifts, and boundary-only copies. -/
theorem BitarraysShift_boundaryCases (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hc : xs.length ≤ 128 ∨ i = int 0 ∨ i.val.natAbs % 64 + (xs.length - i.val.natAbs) ≤ 128) :
    Round5.Round2.ShiftAgrees xs i := by
  rcases hc with hsmall | hzero | hwindow
  · exact BitarraysShift_twoChunks xs i hsmall
  · exact BitarraysShift_zeroAt xs i hn hzero
  · exact BitarraysShift_boundaryWindow xs i hn hwindow
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The installed three-destination-word boundary case rereads source word one in its middle iteration. -/
theorem shift129CopySourceOne (s : State)
    (hs : (mutableGet 0 (int 1)).run s = (.ok (u64 0), s))
    (hd0 : (mutableGet 1 (int 1)).run s = (.ok (u64 0), s))
    (hd2 : (mutableGet 1 (int 3)).run s = (.ok (u64 0), s))
    (hw0 : (mutableSet 1 (u64 0) (int 1)).run s = (.ok (), s))
    (hw1 : (mutableSet 1 (u64 0) (int 2)).run s = (.ok (), s))
    (hw2 : (mutableSet 1 (u64 0) (int 3)).run s = (.ok (), s)) :
    (copyChunks 1 (int 2) 0 (int 1) (int 128)).run s = (.ok (), s) := by
  have hg : (glueSrcBitChunks 0 (int 1) (int 2) u64Max (int 0)).run s = (.ok (u64 0), s) := by
    simp only [glueSrcBitChunks, shape_run_bind, hs,
      show ¬ int 0 > int 0 from by decide, and_false, ite_false, shape_run_pure]
    rfl
  simp only [copyChunks,
    show (int 128 == int 0) = false from rfl, Bool.false_eq_true, ite_false,
    show ¬ (1 = (0 : Nat) ∧ int 2 > int 1) from by omega, dite_false,
    show getChunksId (int 2) = (int 1, int 1) from rfl,
    show int 2 + int 128 - int 1 = int 129 from rfl,
    show getChunksId (int 129) = (int 3, int 0) from rfl,
    show getChunksId (int 1) = (int 1, int 0) from rfl,
    show int 1 + int 128 - int 1 = int 128 from rfl,
    show getChunksId (int 128) = (int 2, int 63) from rfl,
    show int 3 - int 1 = int 2 from rfl,
    show int 2 - int 1 = int 1 from rfl,
    show (int 2 == int 0) = false from rfl,
    show (int 1 == int 0) = false from rfl,
    show shl_int u64Max (int 0) = u64Max from rfl,
    show intRange (int 1) (int 1) = [int 1] from rfl,
    shape_run_bind, hg, hd0,
    show or_int (and_int (u64 0) (not_int (shl_int u64Max (int 1))))
      (and_int (shl_int (u64 0) (int 1)) (not_int (not_int (shl_int u64Max (int 1))))) = u64 0 from rfl,
    hw0, List.forIn_cons, List.forIn_nil,
    show int 1 + int 1 = int 2 from rfl,
    show int 64 - int 1 = int 63 from rfl,
    show or_int (lshr_int (u64 0) (int 63)) (shl_int (u64 0) (int 1)) = u64 0 from rfl,
    hw1, shape_run_pure,
    show ¬ int 2 ≥ int 1 + int 2 from by decide,
    hd2,
    show or_int (and_int (u64 0) (shl_int u64Max (int 0 + int 1)))
      (and_int (u64 0) (not_int (shl_int u64Max (int 0 + int 1)))) = u64 0 from rfl,
    hw2]

/-- The diagnostic input has exactly 129 logical bits. -/
theorem shift129WitnessLength : rangeEmptyDiagnosticBits.length = 129 := by decide

/-- The frozen signed right shift returns a vector whose expected true bit at index 66 is false. -/
theorem shift129ModelRightMiddleBit :
    (match (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
      (vectorBits rangeEmptyDiagnosticBits) (int 1)).run (initWords (encodeBits rangeEmptyDiagnosticBits)) with
    | (.ok B, s) => bitAt s B 65
    | (.error _, _) => true) = false := by
  rw [rangeEmptyDiagnosticEncoding]
  unfold bitVectorShiftRightSigned Round5.Round2.shiftRightUnsignedModel bitVectorShiftRightUnsigned
  simp only [copyChunks]
  decide

/-- The logical right shift of the same input preserves that bit at index 66. -/
theorem shift129ExpectedRightMiddleBit :
    (shiftRightBits rangeEmptyDiagnosticBits 1).getD 65 false = true := by decide

/-- Any failure of the frozen signed-shift assertion requires at least 129 logical bits. -/
theorem shiftFailureRequires129 (xs : List Bool) (i : I64)
    (hfailure : ¬ Round5.Round2.ShiftAgrees xs i) : 129 ≤ xs.length := by
  by_cases hsmall : xs.length ≤ 128
  · exact False.elim (hfailure (BitarraysShift_twoChunks xs i hsmall))
  · omega

/-- A true logical list observation must be the corresponding stored bit. -/
theorem shiftDiagnosticTrueBit {N : Nat} (s : State) (B : BitArray N) (i : Nat)
    (h : (bitValues s B).getD i false = true) : bitAt s B i = true := by
  by_cases hi : i < B.len.val.toNat
  · simpa only [bitValues, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range, hi, ite_true, Option.map_some, Option.getD_some] using h
  · have he : (List.range B.len.val.toNat)[i]? = none :=
      List.getElem?_eq_none (by rw [List.length_range]; omega)
    simp only [bitValues, List.getD_eq_getElem?_getD, List.getElem?_map,
      he, Option.map_none, Option.getD_none] at h
    cases h

/-- The installed 129-bit right-shift execution contradicts its frozen model predicate. -/
theorem shift129FrozenFailure :
    ¬ Round5.Round2.ShiftAgrees rangeEmptyDiagnosticBits (int 1) := by
  intro h
  have hm := shift129ModelRightMiddleBit
  have he := shift129ExpectedRightMiddleBit
  unfold Round5.Round2.ShiftAgrees at h
  dsimp only at h
  generalize hr : (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftSignedArgModel Round5.Round2.shiftRightUnsignedModel
      (vectorBits rangeEmptyDiagnosticBits) (int 1)).run (initWords (encodeBits rangeEmptyDiagnosticBits)) = r at h hm
  rcases r with ⟨rr, s⟩
  cases rr with
  | error e => cases hm
  | ok B =>
    change bitAt s B 65 = false at hm
    simp only [show (int 1).val.natAbs = 1 from rfl,
      show (int 1).val ≥ 0 from by decide, ite_true] at h
    generalize hl : ((bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
      (vectorBits rangeEmptyDiagnosticBits) (int 1)).run (initWords (encodeBits rangeEmptyDiagnosticBits))).1 = lr at h
    cases lr with
    | error e => cases h
    | ok L =>
      have hv := h.2
      have ht := (congrArg (fun bs : List Bool => bs.getD 65 false) hv).trans he
      have hb := shiftDiagnosticTrueBit s B 65 ht
      have hbad : false = true := hm.symm.trans hb
      cases hbad
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096

/-- Ordinary empty BitVectors and shift zero give the public DivideError. -/
theorem BitarraysCircshiftEmpty_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Round2.CircshiftEmptyAgrees := by
  intro h
  have hx := h (int 0)
  change (Except.error .divide : Except Error BitVector) = .ok (vectorBits []) ∧ _ at hx
  cases hx.1
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
namespace NativeShiftContract

open JuliaLean JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15
namespace Model
export JuliaLean.base.bitarray.Models1Group16.NativeShift
  (leftUnsigned rightUnsigned leftSigned rightSigned arithmeticRight)
end Model

def HasBits (state : ObjectState) (target : Ref 1) (bits : List Bool) : Prop :=
  ∃ array : BitVector, state.objects[target.identity]? = some ⟨1, array⟩ ∧
    array.len.val = (bits.length : Int) ∧
    ∀ (index : Nat) (hi : index < bits.length),
      ((getIndex array (int ((index : Int) + 1))).run state.memory).1 =
        .ok (bits[index]'hi)

def leftBits (bits : List Bool) (count : Nat) : List Bool :=
  (List.range bits.length).map (fun index => bits.getD (index + count) false)

def rightBits (bits : List Bool) (count : Nat) : List Bool :=
  (List.range bits.length).map (fun index =>
    if count ≤ index then bits.getD (index - count) false else false)

def SuccessfulValues (action : ObjectM (Ref 1)) (before : ObjectState)
    (source : Ref 1) (old expected : List Bool) : Prop :=
  ∀ result, (action.run before).1 = .ok result →
    HasBits (action.run before).2 result expected ∧
    HasBits (action.run before).2 source old ∧ result ≠ source

def UnsignedValues : Prop :=
  ∀ (runtime : AllocationData) (before : ObjectState) (source : Ref 1)
    (bits : List Bool) (count : U64),
    HasBits before source bits →
    SuccessfulValues (Model.leftUnsigned runtime source count) before source bits
      (leftBits bits count.val.toNat) ∧
    SuccessfulValues (Model.rightUnsigned runtime source count) before source bits
      (rightBits bits count.val.toNat) ∧
    SuccessfulValues (Model.arithmeticRight runtime source (.inr count)) before source bits
      (rightBits bits count.val.toNat)

def SignedValues : Prop :=
  ∀ (runtime : AllocationData) (before : ObjectState) (source : Ref 1)
    (bits : List Bool) (count : I64),
    HasBits before source bits →
    SuccessfulValues (Model.leftSigned runtime source count) before source bits
      (if 0 ≤ count.val then leftBits bits count.val.toNat
        else rightBits bits (-count.val).toNat) ∧
    SuccessfulValues (Model.rightSigned runtime source count) before source bits
      (if 0 ≤ count.val then rightBits bits count.val.toNat
        else leftBits bits (-count.val).toNat) ∧
    SuccessfulValues (Model.arithmeticRight runtime source (.inl count)) before source bits
      (if 0 ≤ count.val then rightBits bits count.val.toNat
        else leftBits bits (-count.val).toNat)

def Values : Prop := UnsignedValues ∧ SignedValues

end NativeShiftContract

def entriesShift1 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-native-shift-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["<<(B::BitVector, i::UInt)", ">>>(B::BitVector, i::UInt)",
      ">>(B::BitVector, i::Union{Int,UInt})", "<<(B::BitVector, i::Int)",
      ">>>(B::BitVector, i::Int)"],
    statement := "Every successful native signed or unsigned shift returns an independent vector of the same logical length, moves bits in the requested direction, fills vacated positions with false, and leaves the source's logical bits unchanged, including typemin(Int) and arbitrarily large UInt counts.",
    source := "base/bitarray.jl:1326-1340,1377,1415,1423", status := .todo,
    prop := ``NativeShiftContract.Values, thm := none,
    notes := "All readable source heaps and alias-resized chunk arrays are included. Allocation and source-storage failures remain explicit outcomes; this contract covers every successful result." },
  { id := "bitarrays-shift", juliaFile := "base/bitarray.jl", juliaFns := ["<<(::BitVector, ::Int)", ">>(::BitVector, ::Int)", ">>>(::BitVector, ::Int)", "<<(::BitVector, ::UInt)", ">>>(::BitVector, ::UInt)"],
    statement := "For every Int shift count, signed left and right shifts move logical bits in the documented direction, fill vacated positions with false, and handle typemin and typemax.", source := "base/bitarray.jl:1333-1423",
    status := .todo, prop := ``Round5.ShiftAgrees, thm := none, notes := "No complete exact proof returned. the remaining target requires correcting the old forward-copy source index." },
  { id := "bitarrays-circshift-empty", juliaFile := "base/bitarray.jl", juliaFns := ["circshift!(::BitVector, ::Integer)", "circshift!(::BitVector, ::BitVector, ::Integer)"],
    statement := "For empty BitVectors, both circular-shift methods return the original vector for every successfully converted Integer shift.", source := "base/bitarray.jl:1425-1444; base/multidimensional.jl:1257-1266",
    status := .refuted, prop := ``Round2.CircshiftEmptyAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group2.BitarraysCircshiftEmpty_refuted,
    issue := "#41402, #54294 (closed, related); no exact duplicate found" },
  { id := "bitarrays-circshift-nonempty", juliaFile := "base/bitarray.jl", juliaFns := ["circshift!(::BitVector, ::Integer)", "circshift!(::BitVector, ::BitVector, ::Integer)"],
    statement := "For nonempty vectors, circshift!(B, k) and circshift!(dest, B, k) rotate exactly like circshift! on Vector{Bool} for every k::Int and keep the invariant.", source := "circshift! docstring (base/abstractarraymath.jl); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``CircshiftNonemptyAgrees, thm := none, notes := "No complete exact proof returned. full multiword rotation correctness remains blocked by that model/source mismatch." }
]
end JuliaLean.Proofs.base.bitarray

