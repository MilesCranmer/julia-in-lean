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
import JuliaLean.Proofs.base.bitarray.common.reshape
import JuliaLean.Proofs.base.bitarray.common.shift

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Conversion failures in public resizing occur before any mutation. -/
theorem rangeResize_conversion_error {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (n : X) (first : Bool) (e : JuliaLean.base.range.Exc)
    (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := I64) n = .error e) :
    (Round5.Round2.resizeBitVectorPublic B n first).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [Round5.Round2.resizeBitVectorPublic, h,
    Round5.Round2.liftRangeResult, shape_run_bind]
  rfl

/-- The complete conversion-error branch of the frozen nonnegative-resize contract. -/
theorem rangeResize_frozen_conversion_error {X : Type}
    [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (n : X) (first : Bool) (e : JuliaLean.base.range.Exc)
    (h : JuliaLean.base.range.JConvert.convert (T := I64) n = .error e) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    match (Round5.Round2.resizeBitVectorPublic B n first).run s |>.1 with
    | .error _ => ((Round5.Round2.resizeBitVectorPublic B n first).run s).2 = s
    | .ok _ => False := by
  dsimp only
  rw [rangeResize_conversion_error (vectorBits xs) n first e
    (initWords (encodeBits xs)) h]

/-- Resizing to the existing length is an exact no-op for either end convention. -/
theorem rangeResize_same_length {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (n : X) (first : Bool) (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := I64) n = .ok B.len) :
    (Round5.Round2.resizeBitVectorPublic B n first).run s = (.ok B, s) := by
  have hle : B.len ≤ B.len := Int.le_refl B.len.val
  simp only [Round5.Round2.resizeBitVectorPublic, h,
    Round5.Round2.liftRangeResult, shape_run_bind, shape_run_pure,
    hle, or_true, ite_true, bitVectorResize, bitVectorResizeInt,
    beq_self_eq_true]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Front-shrinking resize reaches the same frozen packed-copy discrepancy. -/
theorem rangeResize_model_middle_bit :
    (match (Round5.Round2.resizeBitVectorPublic (vectorBits rangeDeleteWitnessBits)
      (int 129) true).run (initWords (encodeBits rangeDeleteWitnessBits)) with
    | (.ok B, s) => bitAt s B 126
    | (.error _, _) => false) = true := by
  rw [rangeDeleteWitness_encode]
  change (match (bitVectorDeleteRange (fun _ => int 1)
    (⟨0, int 130, [int 130]⟩ : BitVector) ⟨int 1, int 1⟩).run
    (initWords [u64 0, u64 1, u64 0]) with
    | (.ok B, s) => bitAt s B 126
    | (.error _, _) => false) = true
  unfold bitVectorDeleteRange
  simp only [copyChunks]
  decide

/-- The documented suffix retained by this resize has a false bit at index 127. -/
theorem rangeResize_expected_middle_bit :
    (rangeDeleteWitnessBits.drop 1).getD 126 false = false := by
  decide
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

/-- Constant clearing preserves the backing-store length. -/
theorem resizeClearLength {α : Type} (indices : List Nat) (slots : List (Option α)) :
    (indices.foldl (fun s i => s.set i none) slots).length = slots.length := by
  induction indices generalizing slots with
  | nil => rfl
  | cons i indices ih => rw [List.foldl_cons, ih, List.length_set]

/-- A clearing fold changes exactly its visited, valid backing slots. -/
theorem resizeClearGet {α : Type} (indices : List Nat) :
    ∀ (slots : List (Option α)), (∀ i ∈ indices, i < slots.length) → ∀ j : Nat,
    (indices.foldl (fun s i => s.set i none) slots).getD j none =
      if j ∈ indices then none else slots.getD j none := by
  induction indices with
  | nil => intro slots _ j; simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons i indices ih =>
    intro slots hi j
    have hib := hi i List.mem_cons_self
    have hr := ih (slots.set i none)
      (by intro k hk; rw [List.length_set]; exact hi k (List.mem_cons_of_mem i hk)) j
    rw [List.foldl_cons, hr]
    by_cases hj : j ∈ indices
    · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
    · rw [if_neg hj]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      by_cases he : i = j
      · subst j
        simp only [hib, and_self, ite_true, Option.getD_some,
          List.mem_cons_self]
      · have hnot : ¬ j ∈ i :: indices := by
          intro hmem
          rcases List.mem_cons.mp hmem with hmem | hmem
          · exact he hmem.symm
          · exact hj hmem
        simp only [he, false_and, ite_false, hnot, List.getD_eq_getElem?_getD]

/-- Clearing a full suffix leaves its original prefix followed by unused slots. -/
theorem resizeClearSuffix {α : Type} (slots : List (Option α)) (k : Nat)
    (hk : k ≤ slots.length) :
    ((List.range (slots.length - k)).map (fun j => k + j)).foldl
      (fun s i => s.set i none) slots =
        slots.take k ++ List.replicate (slots.length - k) none := by
  let indices := (List.range (slots.length - k)).map (fun j => k + j)
  have hmem (j : Nat) : j ∈ indices ↔ k ≤ j ∧ j < slots.length := by
    simp only [indices, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨q, hq, rfl⟩; omega
    · rintro ⟨hkj, hj⟩; exact ⟨j - k, by omega, by omega⟩
  apply List.ext_getElem
  · rw [resizeClearLength, List.length_append, List.length_take,
      Nat.min_eq_left hk, List.length_replicate]
    omega
  · intro j hj hj'
    have hjb : j < slots.length := by simpa only [resizeClearLength] using hj
    rw [List.getElem_eq_getD (fallback := none),
      resizeClearGet indices slots (by intro i hi; exact (hmem i).mp hi |>.2) j,
      List.getElem_eq_getD (fallback := none), List.getD_eq_getElem?_getD]
    by_cases hjk : j < k
    · simp only [List.getD_eq_getElem?_getD]
      rw [if_neg (by intro hm; have := (hmem j).mp hm; omega),
        List.getElem?_append_left (by rw [List.length_take, Nat.min_eq_left hk]; exact hjk),
        List.getElem?_take_of_lt hjk]
    · simp only [List.getD_eq_getElem?_getD]
      rw [if_pos ((hmem j).mpr ⟨by omega, hjb⟩),
        List.getElem?_append_right (by rw [List.length_take, Nat.min_eq_left hk]; omega),
        List.length_take, Nat.min_eq_left hk, List.getElem?_replicate,
        if_pos (by omega), Option.getD_some]

/-- A raw one-vector store, allowing unspecified values in newly exposed words. -/
def resizeSlotStore (slots : List (Option U64)) (n : Nat) : State :=
  ⟨[slots], [⟨(0, one), int n⟩]⟩

/-- Header length is independent of which allocation backs the vector. -/
theorem resizeLengthRaw (s : State) (mem : Nat) (n : I64)
    (ha : s.arrays[0]? = some ⟨(mem, one), n⟩) :
    (mutableLength 0).run s = (.ok n, s) := by
  simp only [mutableLength, shape_run_bind, shape_vector_run, ha, shape_run_pure]

/-- Array writes work unchanged after a backing-allocation replacement. -/
theorem resizeSetRaw (s : State) (slots : List (Option U64)) (mem : Nat)
    (n j : I64) (word : U64)
    (ha : s.arrays[0]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some slots)
    (hn : n.val ≤ (slots.length : Int))
    (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    (mutableSet 0 word j).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (j.val - 1).toNat (some word))}) := by
  have hin : one ≤ j ∧ j ≤ n := hj
  have hw := resizeMemoryWrite s slots mem hm j word (by omega)
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hin, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_one_add_sub_one, hw]

/-- Natural suffix indices agree with their native integer range. -/
theorem resizeSuffixRange (m k : Nat) (hk : k < m)
    (hm : m ≤ 9223372036854775807) :
    intRange (int ((k + 1 : Nat) : Int)) (int (m : Int)) =
      ((List.range (m - k)).map (fun j => k + j)).map
        (fun j => int ((j + 1 : Nat) : Int)) := by
  unfold intRange
  rw [packedInt_val m hm, packedInt_val (k + 1) (by omega)]
  have hlen : (((m : Int) - ((k + 1 : Nat) : Int) + 1).toNat) = m - k := by omega
  rw [hlen]
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  apply Subtype.ext
  change wrapInt .i64 (((k + 1 : Nat) : Int) + (j : Int)) =
    wrapInt .i64 (((k + j + 1 : Nat) : Int))
  apply congrArg (wrapInt .i64)
  omega

/-- Clearing the removed visible suffix converts it into spare capacity. -/
theorem resizeClearWordSuffix (words : List U64) (spare k : Nat) (hk : k ≤ words.length) :
    ((List.range (words.length - k)).map (fun j => k + j)).foldl
      (fun s j => s.set j none) (words.map some ++ List.replicate spare none) =
        (words.take k).map some ++ List.replicate (spare + (words.length - k)) none := by
  let slots := words.map some ++ List.replicate spare none
  let indices := (List.range (words.length - k)).map (fun j => k + j)
  have hlen : slots.length = words.length + spare := by
    simp only [slots, List.length_append, List.length_map, List.length_replicate]
  have ht : ((words.take k).map some).length = k := by
    rw [List.length_map, List.length_take, Nat.min_eq_left hk]
  have hmem (j : Nat) : j ∈ indices ↔ k ≤ j ∧ j < words.length := by
    simp only [indices, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨q, hq, rfl⟩; omega
    · rintro ⟨hkj, hj⟩; exact ⟨j - k, by omega, by omega⟩
  change indices.foldl (fun s j => s.set j none) slots = _
  apply List.ext_getElem
  · rw [resizeClearLength, hlen, List.length_append, ht, List.length_replicate]
    omega
  · intro j hj hj'
    have hjb : j < slots.length := by simpa only [resizeClearLength] using hj
    rw [List.getElem_eq_getD (fallback := none),
      resizeClearGet indices slots
        (by intro i hi; rw [hlen]; have := (hmem i).mp hi; omega) j,
      List.getElem_eq_getD (fallback := none)]
    by_cases hjk : j < k
    · rw [if_neg (by intro h; have := (hmem j).mp h; omega)]
      simp only [slots, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [List.length_map]; omega),
        List.getElem?_append_left (by rw [ht]; omega),
        List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt hjk]
    · have hr : ((words.take k).map some ++
          List.replicate (spare + (words.length - k)) none).getD j none = none := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [ht]; omega), ht,
          List.getElem?_replicate, if_pos (by rw [hlen] at hjb; omega), Option.getD_some]
      rw [hr]
      by_cases hjw : j < words.length
      · rw [if_pos ((hmem j).mpr ⟨by omega, hjw⟩)]
      · rw [if_neg (by intro h; exact hjw ((hmem j).mp h).2)]
        simp only [slots, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [List.length_map]; omega),
          List.length_map, List.getElem?_replicate,
          if_pos (by rw [hlen] at hjb; omega), Option.getD_some]

/-- Preserving the original encoded word prefix preserves every original logical bit. -/
theorem resizeBitAtPrefix (s : State) (B : BitArray 1) (xs : List Bool) (i : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length)
    (hc : (s.contents B.chunks).take (wordCount xs.length) = (encodeBits xs).map some) :
    bitAt s B i = xs.getD i false := by
  have hchunk : i / 64 < wordCount xs.length := by unfold wordCount; omega
  have hget : (s.contents B.chunks)[i / 64]? = ((encodeBits xs).map some)[i / 64]? := by
    rw [← List.getElem?_take_of_lt hchunk, hc]
  have hbound : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    exact hchunk
  rw [List.getElem?_map, List.getElem?_eq_getElem hbound] at hget
  unfold bitAt
  rw [hget]
  simp only [Option.map_some]
  rw [scalar_mask_test_ofNat _ _ (Nat.mod_lt _ (by decide))]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [packedWord_bit xs _ _ (Nat.mod_lt _ (by decide))]
  rw [show i / 64 * 64 + i % 64 = i by omega]

/-- Default resize retains the complete original logical prefix when it grows. -/
theorem resizeBitsPrefix (s : State) (B : BitArray 1) (xs : List Bool) (n : Nat)
    (hle : xs.length ≤ n) (hn : n ≤ 9223372036854775807)
    (hl : B.len = int n)
    (hc : (s.contents B.chunks).take (wordCount xs.length) = (encodeBits xs).map some) :
    (bitValues s B).take xs.length = xs := by
  unfold bitValues
  rw [hl, packedInt_val n hn, Int.toNat_natCast]
  apply List.ext_getElem
  · rw [List.length_take, List.length_map, List.length_range, Nat.min_eq_left hle]
  · intro i hi hi'
    rw [List.getElem_take, List.getElem_map, List.getElem_range,
      resizeBitAtPrefix s B xs i (by omega) hi' hc]
    exact (List.getElem_eq_getD false).symm

/-- Zero words contain no nonzero padding under any mask. -/
theorem resizeZeroPadding (mask : U64) : and_int (u64 0) (not_int mask) = u64 0 := by
  apply packedBit_ext
  intro k hk
  rw [dequePackedAnd, packedBit_zero]
  rfl

/-- A correctly sized visible window ending in a zero word has valid padding. -/
theorem resizeInvariantLastZero (s : State) (B : BitArray 1) (n : Nat)
    (hp : 0 < n) (hn : n ≤ 9223372036854775807) (hl : B.len = int n)
    (hc : (s.contents B.chunks).length = wordCount n)
    (hz : (s.contents B.chunks).getLast? = some (some (u64 0))) :
    Round5.Round2.PackedInvariant s B := by
  have hne : (B.len == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [hl, packedInt_val n hn] at hv
    change (n : Int) = 0 at hv
    omega
  refine ⟨?_, ?_⟩
  · rw [hc, hl, scalar_count_nat n hn]
  · simp only [hne, Bool.false_eq_true, ite_false, hz]
    exact resizeZeroPadding (maskEnd B.len)

/-- Enlarging within the same last word cannot invalidate its already-zero padding. -/
theorem resizeInvariantSameWords (s : State) (B : BitArray 1) (xs : List Bool) (n : Nat)
    (hle : xs.length ≤ n) (hn : n ≤ 9223372036854775807)
    (hl : B.len = int n) (hw : wordCount n = wordCount xs.length)
    (hc : s.contents B.chunks = (encodeBits xs).map some) :
    Round5.Round2.PackedInvariant s B := by
  have hlen : (s.contents B.chunks).length = (numBitChunks B.len).val.toNat := by
    rw [hc, List.length_map, packedEncoded_length, hl, scalar_count_nat n hn, hw]
  by_cases hp : 0 < n
  · have hxp : 0 < xs.length := by unfold wordCount at hw; omega
    have hne : (B.len == int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have hv := congrArg Subtype.val he
      rw [hl, packedInt_val n hn] at hv
      change (n : Int) = 0 at hv
      omega
    refine ⟨hlen, ?_⟩
    simp only [hne, Bool.false_eq_true, ite_false, hc, scalar_encoded_last_some xs hxp]
    change and_int (packedPrefix xs (wordCount xs.length - 1) 64)
      (not_int (maskEnd B.len)) = u64 0
    rw [hl]
    apply packedBit_ext
    intro k hk
    rw [dequePackedAnd, scalar_packedBit_not _ k hk,
      packedWord_bit xs _ k hk, packedBit_zero,
      packedMask_last_bit n k hp hn]
    by_cases hi : (wordCount n - 1) * 64 + k < n
    · simp only [hi, decide_true, Bool.not_true, Bool.and_false]
    · have hx : xs.length ≤ (wordCount xs.length - 1) * 64 + k := by rw [← hw]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hx, Option.getD_none]
      rfl
  · have hz : n = 0 := by omega
    refine ⟨hlen, ?_⟩
    rw [hl, hz]
    trivial

/-- Writing the new final visible word keeps every earlier original backing slot. -/
theorem resizeSetLastPrefix (slots : List (Option U64)) (k m : Nat) (value : U64)
    (hm : m < k) :
    ((slots.set (k - 1) (some value)).take k).take m = slots.take m := by
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_set_of_le (by omega)]

/-- The final-word write makes the last visible slot explicitly initialized. -/
theorem resizeSetLastGetLast (slots : List (Option U64)) (k : Nat) (value : U64)
    (hp : 0 < k) (hk : k ≤ slots.length) :
    ((slots.set (k - 1) (some value)).take k).getLast? = some (some value) := by
  rw [List.getLast?_eq_getElem?, List.length_take, List.length_set, Nat.min_eq_left hk,
    List.getElem?_take_of_lt (by omega), List.getElem?_set_self (by omega)]

/-- The public default shrink selects exactly the suffix range. -/
theorem resizePublicShrinkFrom {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B outB : BitArray 1) (x : X) (n : I64) (s out : State)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok n)
    (hn : ¬ n < int 0) (hlt : n < B.len)
    (hr : (bitVectorDeleteRange
      (fun _ => int 1 + (B.len - (n + int 1))) B ⟨n + int 1, B.len⟩).run s =
        (.ok outB, out)) :
    (Round5.Round2.resizeBitVectorPublic B x false).run s = (.ok outB, out) := by
  have hle : ¬ B.len ≤ n := by change ¬ B.len.val ≤ n.val; exact Int.not_le.mpr hlt
  have hne : (n == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    have := congrArg Subtype.val h
    change n.val < B.len.val at hlt
    omega
  simp only [Round5.Round2.resizeBitVectorPublic, he,
    Round5.Round2.liftRangeResult, shape_run_bind, shape_run_pure,
    hn, hle, or_self, ite_false, Bool.false_eq_true, rangeDelete_length_formula,
    bitVectorResize, bitVectorResizeInt, hne, hlt, ite_true]
  exact hr

/-- Default growth performs only optional word growth and a final zero-word write. -/
theorem resizePublicGrowFrom {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitArray 1) (x : X) (n oldCount : I64) (s out : State)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok n)
    (hn : ¬ n < int 0) (hlt : B.len < n)
    (hl : (mutableLength B.chunks).run s = (.ok oldCount, s))
    (hg : ((if numBitChunks n > oldCount then do
        growChunkVector B.chunks (numBitChunks n - oldCount)
        mutableSet B.chunks (u64 0) (← mutableLength B.chunks)
      else pure ()) : BitMutationM Unit).run s = (.ok (), out)) :
    (Round5.Round2.resizeBitVectorPublic B x false).run s =
      (.ok {B with len := n}, out) := by
  have hle : B.len ≤ n := Int.le_of_lt hlt
  have hnlt : ¬ n < B.len := Int.not_lt.mpr hle
  have hne : (n == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    have := congrArg Subtype.val h
    change B.len.val < n.val at hlt
    omega
  simp only [Round5.Round2.resizeBitVectorPublic, he,
    Round5.Round2.liftRangeResult, shape_run_bind, shape_run_pure,
    hle, or_true, ite_true, bitVectorResize, bitVectorResizeInt,
    hne, Bool.false_eq_true, ite_false, hn, hnlt, hl]
  dsimp only [BitVector] at *
  simp only [ite_false]
  by_cases hglt : numBitChunks n > oldCount
  · simp only [hglt, ite_true] at hg ⊢
    have hfactor : ((do
        growChunkVector B.chunks (numBitChunks n - oldCount)
        mutableSet B.chunks (u64 0) (← mutableLength B.chunks)
        pure ({B with len := n} : BitArray 1)) : BitMutationM (BitArray 1)) =
        ((do
          growChunkVector B.chunks (numBitChunks n - oldCount)
          mutableSet B.chunks (u64 0) (← mutableLength B.chunks)) >>= fun _ =>
            pure ({B with len := n} : BitArray 1)) := by
      simp only [bind_assoc]
    rw [hfactor, shape_run_bind, hg]
    rfl
  · simp only [hglt, ite_false, shape_run_pure] at hg ⊢
    have hs : s = out := congrArg Prod.snd hg
    rw [hs]

/-- A difference of native nonnegative counts has its ordinary signed value. -/
theorem resizeCountSubVal (a b : Nat) (ha : a ≤ 9223372036854775807)
    (hb : b ≤ 9223372036854775807) :
    (int (a : Int) - int (b : Int)).val = (a : Int) - (b : Int) := by
  rw [dequeIntSub]
  change wrapInt .i64 ((a : Int) - (b : Int)) = _
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (a : Int) - (b : Int) ∧
    (a : Int) - (b : Int) ≤ 9223372036854775807
  omega

/-- The suffix-removal count is the positive opposite of its signed size change. -/
theorem resizeCountNegSub (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ 9223372036854775807) :
    -(int (a : Int) - int (b : Int)) = int ((b - a : Nat) : Int) := by
  apply Subtype.ext
  change wrapInt .i64 (-(int (a : Int) - int (b : Int)).val) =
    wrapInt .i64 (((b - a : Nat) : Int))
  rw [resizeCountSubVal a b (by omega) hb]
  apply congrArg (wrapInt .i64)
  omega

/-- The native word-growth action finishes by initializing its new final word. -/
theorem resizeGrowZeroFrom (chunks : Nat) (delta count : I64) (s grown out : State)
    (hg : (growChunkVector chunks delta).run s = (.ok (), grown))
    (hl : (mutableLength chunks).run grown = (.ok count, grown))
    (hw : (mutableSet chunks (u64 0) count).run grown = (.ok (), out)) :
    ((do
      growChunkVector chunks delta
      mutableSet chunks (u64 0) (← mutableLength chunks)) : BitMutationM Unit).run s =
        (.ok (), out) := by
  simp only [shape_run_bind, hg, hl, hw]

/-- Any successful word growth retaining the old prefix gives the complete default-resize result. -/
theorem resizeGrowthFromStore {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X) (n : Nat) (grown : State)
    (slots : List (Option U64)) (mem : Nat)
    (hx : xs.length ≤ 9223372036854775807) (hn : n ≤ 9223372036854775807)
    (hlt : xs.length < n) (hwords : wordCount xs.length < wordCount n)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok (int (n : Int)))
    (hg : (growChunkVector 0 (int ((wordCount n - wordCount xs.length : Nat) : Int))).run
      (initWords (encodeBits xs)) = (.ok (), grown))
    (ha : grown.arrays[0]? = some ⟨(mem, one), int (wordCount n : Int)⟩)
    (hm : grown.memories[mem]? = some slots)
    (hcap : wordCount n ≤ slots.length)
    (hprefix : slots.take (wordCount xs.length) = (encodeBits xs).map some) :
    ∃ B' out,
      (Round5.Round2.resizeBitVectorPublic (vectorBits xs) x false).run
        (initWords (encodeBits xs)) = (.ok B', out) ∧
      B'.len = int (n : Int) ∧ xs = (bitValues out B').take xs.length ∧
      Round5.Round2.PackedInvariant out B' := by
  let B : BitArray 1 := vectorBits xs
  let k := wordCount n
  let newSlots := slots.set (k - 1) (some (u64 0))
  let out : State := {grown with memories := grown.memories.set mem newSlots}
  let B' : BitArray 1 := {B with len := int (n : Int)}
  have hk : k ≤ 9223372036854775807 := by dsimp only [k]; unfold wordCount; omega
  have hkp : 0 < k := by dsimp only [k]; omega
  have hv : (int (k : Int)).val = (k : Int) := packedInt_val k hk
  have hidx : ((int (k : Int)).val - 1).toNat = k - 1 := by rw [hv]; omega
  have hw := resizeSetRaw grown slots mem (int (k : Int)) (int (k : Int)) (u64 0)
    ha hm (by rw [hv]; omega) (by rw [hv]; omega)
  have hw' : (mutableSet 0 (u64 0) (int (k : Int))).run grown = (.ok (), out) := by
    exact hw.trans (by rw [hidx])
  have hl := resizeLengthRaw grown mem (int (k : Int)) ha
  have hzero := resizeGrowZeroFrom 0
    (int ((wordCount n - wordCount xs.length : Nat) : Int)) (int (k : Int))
    (initWords (encodeBits xs)) grown out hg hl hw'
  have hdelta : numBitChunks (int (n : Int)) - int ((encodeBits xs).length : Int) =
      int ((wordCount n - wordCount xs.length : Nat) : Int) := by
    rw [resizeNumChunks n hn, packedEncoded_length, dequeIntSub]
    exact congrArg int (by omega)
  have hgrow : numBitChunks (int (n : Int)) > int ((encodeBits xs).length : Int) := by
    rw [resizeNumChunks n hn, packedEncoded_length]
    change (int (wordCount xs.length : Int)).val < (int (wordCount n : Int)).val
    rw [packedInt_val _ (by unfold wordCount; omega), packedInt_val _ hk]
    omega
  have hphase : ((if numBitChunks (int (n : Int)) > int ((encodeBits xs).length : Int) then do
        growChunkVector 0 (numBitChunks (int (n : Int)) - int ((encodeBits xs).length : Int))
        mutableSet 0 (u64 0) (← mutableLength 0)
      else pure ()) : BitMutationM Unit).run (initWords (encodeBits xs)) = (.ok (), out) := by
    rw [if_pos hgrow, hdelta]
    exact hzero
  have hlold : (mutableLength 0).run (initWords (encodeBits xs)) =
      (.ok (int ((encodeBits xs).length : Int)), initWords (encodeBits xs)) := by
    rw [← dequeWordStoreInitial]
    exact dequeWordLength _ _
  have hr := resizePublicGrowFrom B x (int (n : Int)) (int ((encodeBits xs).length : Int))
    (initWords (encodeBits xs)) out he
    (by change ¬ (int (n : Int)).val < 0; rw [packedInt_val n hn]; omega)
    (by change (int (xs.length : Int)).val < (int (n : Int)).val
        rw [packedInt_val xs.length hx, packedInt_val n hn]; omega)
    hlold hphase
  have haout : out.arrays[0]? = some ⟨(mem, one), int (k : Int)⟩ := ha
  have hmout : out.memories[mem]? = some newSlots := by
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hm).choose
  have hc : out.contents B'.chunks = newSlots.take k :=
    resizeContentsRaw out newSlots mem k haout hmout hk
  have hcprefix : (out.contents B'.chunks).take (wordCount xs.length) =
      (encodeBits xs).map some := by
    rw [hc, resizeSetLastPrefix slots k (wordCount xs.length) (u64 0) hwords, hprefix]
  have hclen : (out.contents B'.chunks).length = wordCount n := by
    rw [hc, List.length_take, List.length_set, Nat.min_eq_left hcap]
  have hlast : (out.contents B'.chunks).getLast? = some (some (u64 0)) := by
    rw [hc]
    exact resizeSetLastGetLast slots k (u64 0) hkp hcap
  refine ⟨B', out, hr, rfl, ?_, ?_⟩
  · exact (resizeBitsPrefix out B' xs n (by omega) hn rfl hcprefix).symm
  · exact resizeInvariantLastZero out B' n (by omega) hn rfl hclen hlast

/-- Growing within the current final word preserves the entire existing store. -/
theorem resizeGrowthSameWordRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X) (n : Nat)
    (hx : xs.length ≤ 9223372036854775807) (hn : n ≤ 9223372036854775807)
    (hlt : xs.length < n) (hwords : wordCount n = wordCount xs.length)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok (int (n : Int))) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) x false).run
      (initWords (encodeBits xs)) =
        (.ok {vectorBits xs with len := int (n : Int)}, initWords (encodeBits xs)) := by
  let B : BitArray 1 := vectorBits xs
  let s := initWords (encodeBits xs)
  have hno : ¬ numBitChunks (int (n : Int)) > int ((encodeBits xs).length : Int) := by
    rw [resizeNumChunks n hn, packedEncoded_length, hwords]
    exact Int.lt_irrefl _
  have hl : (mutableLength 0).run s = (.ok (int ((encodeBits xs).length : Int)), s) := by
    dsimp only [s]
    rw [← dequeWordStoreInitial]
    exact dequeWordLength _ _
  apply resizePublicGrowFrom B x (int (n : Int)) (int ((encodeBits xs).length : Int)) s s he
    (by change ¬ (int (n : Int)).val < 0; rw [packedInt_val n hn]; omega)
    (by change (int (xs.length : Int)).val < (int (n : Int)).val
        rw [packedInt_val xs.length hx, packedInt_val n hn]; omega) hl
  simp only [hno, ite_false, shape_run_pure]

/-- Default same-word growth preserves the original prefix and packed representation. -/
theorem resizeGrowthSameWordCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X) (n : Nat)
    (hx : xs.length ≤ 9223372036854775807) (hn : n ≤ 9223372036854775807)
    (hlt : xs.length < n) (hwords : wordCount n = wordCount xs.length)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok (int (n : Int))) :
    ∃ B' out,
      (Round5.Round2.resizeBitVectorPublic (vectorBits xs) x false).run
        (initWords (encodeBits xs)) = (.ok B', out) ∧
      B'.len = int (n : Int) ∧ xs = (bitValues out B').take xs.length ∧
      Round5.Round2.PackedInvariant out B' := by
  let B' : BitArray 1 := {vectorBits xs with len := int (n : Int)}
  let out := initWords (encodeBits xs)
  have hc : out.contents B'.chunks = (encodeBits xs).map some :=
    scalar_initial_contents _ (packedEncoded_lengthBound xs hx)
  have hp : (out.contents B'.chunks).take (wordCount xs.length) = (encodeBits xs).map some := by
    rw [hc]
    exact List.take_of_length_le (by rw [List.length_map, packedEncoded_length]; exact Nat.le_refl _)
  refine ⟨B', out, resizeGrowthSameWordRun xs x n hx hn hlt hwords he, rfl, ?_, ?_⟩
  · exact (resizeBitsPrefix out B' xs n (by omega) hn rfl hp).symm
  · exact resizeInvariantSameWords out B' xs n (by omega) hn rfl hwords hc

/-- Growing into existing capacity changes only the native visible-word count. -/
theorem resizeGrowRoomRun (words : List U64) (spare k : Nat)
    (hlo : words.length ≤ k) (hcap : k ≤ words.length + spare)
    (hn : words.length + spare ≤ 9223372036854775807) :
    (growChunkVector 0 (int ((k - words.length : Nat) : Int))).run
      (dequeWordStore words spare) =
        (.ok (), resizeSlotStore (words.map some ++ List.replicate spare none) k) := by
  let slots := words.map some ++ List.replicate spare none
  let s := dequeWordStore words spare
  let delta := int ((k - words.length : Nat) : Int)
  have hslen : slots.length = words.length + spare := by
    simp only [slots, List.length_append, List.length_map, List.length_replicate]
  have hdv : delta.val = (k - words.length : Nat) := packedInt_val _ (by omega)
  have hroom : JInt.wrap .i64 slots.length - (one - one) - int words.length = int spare := by
    change int slots.length - (int 1 - int 1) - int words.length = _
    rw [shape_int_sub_self, dequeIntSub, dequeIntSub]
    exact congrArg int (by rw [hslen]; omega)
  have hadd : int words.length + delta = int k := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  have hg := dequeGrowWithRoom s slots (int words.length) delta rfl rfl
    (by change 0 ≤ delta.val; rw [hdv]; omega)
    (by rw [hroom]; change ¬ (int spare).val < delta.val
        rw [packedInt_val spare (by omega), hdv]; omega)
  exact hg.trans (by
    simp only [s, dequeWordStore, resizeSlotStore, List.set_cons_zero, hadd])

/-- The existing allocation retains its encoded prefix after exposing extra spare words. -/
theorem resizeInitialSlotsPrefix (words : List U64) (spare : Nat) :
    (words.map some ++ List.replicate spare none).take words.length = words.map some := by
  exact List.take_left' (List.length_map ..)

/-- Default growth needing at most the initial reserve is correct for every converted input type. -/
theorem resizeGrowthRoomCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X) (n : Nat)
    (hx : xs.length ≤ 9223372036854775807) (hn : n ≤ 9223372036854775807)
    (hlt : xs.length < n) (hwords : wordCount xs.length < wordCount n)
    (hroom : wordCount n ≤ wordCount xs.length + 32)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok (int (n : Int))) :
    ∃ B' out,
      (Round5.Round2.resizeBitVectorPublic (vectorBits xs) x false).run
        (initWords (encodeBits xs)) = (.ok B', out) ∧
      B'.len = int (n : Int) ∧ xs = (bitValues out B').take xs.length ∧
      Round5.Round2.PackedInvariant out B' := by
  let words := encodeBits xs
  let slots := words.map some ++ List.replicate 32 none
  let grown := resizeSlotStore slots (wordCount n)
  have hlen : words.length = wordCount xs.length := packedEncoded_length xs
  have hcapacity : words.length + 32 ≤ 9223372036854775807 := by
    rw [hlen]
    unfold wordCount
    omega
  have hg := resizeGrowRoomRun words 32 (wordCount n)
    (by rw [hlen]; omega) (by rw [hlen]; exact hroom) hcapacity
  have hrun : (growChunkVector 0 (int ((wordCount n - wordCount xs.length : Nat) : Int))).run
      (initWords (encodeBits xs)) = (.ok (), grown) := by
    have hinit := congrArg (fun st : State =>
      (growChunkVector 0 (int ((wordCount n - wordCount xs.length : Nat) : Int))).run st)
      (dequeWordStoreInitial words).symm
    exact hinit.trans (by simpa only [hlen] using hg)
  apply resizeGrowthFromStore xs x n grown slots 0 hx hn hlt hwords he hrun rfl rfl
  · simp only [slots, List.length_append, List.length_map, List.length_replicate, hlen]
    exact hroom
  · rw [← hlen]
    exact resizeInitialSlotsPrefix words 32

/-- Successful default resizing at a natural target length, retaining the frozen prefix contract. -/
def resizeDefaultSuccessAt {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X) (n : Nat) : Prop :=
  ∃ B' out,
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) x false).run
      (initWords (encodeBits xs)) = (.ok B', out) ∧
    B'.len = int (n : Int) ∧
    (if n < xs.length then bitValues out B' = xs.take n
      else xs = (bitValues out B').take xs.length) ∧
    Round5.Round2.PackedInvariant out B'

/-- Unchanged lengths satisfy the default contract without mutating the store. -/
theorem resizeDefaultSameLength {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X) (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := I64) x = .ok (int (xs.length : Int))) :
    resizeDefaultSuccessAt xs x xs.length := by
  let B := vectorBits xs
  let s := initWords (encodeBits xs)
  refine ⟨B, s, rangeResize_same_length B x false s he, rfl, ?_, ?_⟩
  · rw [if_neg (Nat.lt_irrefl _)]
    have hv : bitValues s B = xs := scalar_bits_initial xs [int xs.length] hn
    rw [hv, List.take_length]
  · exact scalar_initial_invariant xs [int xs.length] hn

/-- The frozen nonnegative-resize observations restricted to the documented default end. -/
def resizeDefaultObservation (xs : List Bool) (initial : State)
    (converted : JuliaLean.base.range.JlX I64)
    (result : Id (Except Error BitVector × MutableMemory U64)) : Prop :=
  match converted with
  | .error _ => match result.1 with
    | .error _ => result.2 = initial
    | .ok _ => False
  | .ok newLength =>
    if 0 ≤ newLength.val ∧ newLength.val.toNat < Round5.maxVectorLength then
      match result.1 with
      | .ok B' =>
        B'.len = newLength ∧
        (if newLength.val.toNat < xs.length then
          bitValues result.2 B' = xs.take newLength.val.toNat
         else xs = (bitValues result.2 B').take xs.length) ∧
        Round5.Round2.PackedInvariant result.2 B'
      | .error _ => False
    else True

/-- Every supported converted integer is the machine representation of its nonnegative natural value. -/
theorem resizeNonnegNat (n : I64) (hn : 0 ≤ n.val) :
    n = int (n.val.toNat : Int) := by
  apply Subtype.ext
  change n.val = wrapInt .i64 (n.val.toNat : Int)
  rw [Int.toNat_of_nonneg hn, wrapInt_of_inRange .i64 n.val n.property]

/-- Conversion failures satisfy the default contract before any packed-memory operation. -/
theorem resizeDefaultObservationError (xs : List Bool) (initial : State)
    (e : JuliaLean.base.range.Exc)
    (result : Id (Except Error BitVector × MutableMemory U64))
    (hr : result = (.error (Round5.Round2.mutationErrorOfRange e), initial)) :
    resizeDefaultObservation xs initial (.error e) result := by
  rw [hr]
  rfl

/-- A successful abstract result supplies every default-resize observation. -/
theorem resizeDefaultObservationOk (xs : List Bool) (initial out : State)
    (n : I64) (B' : BitVector)
    (result : Id (Except Error BitVector × MutableMemory U64))
    (hr : result = (.ok B', out))
    (hl : B'.len = n)
    (hb : if n.val.toNat < xs.length then bitValues out B' = xs.take n.val.toNat
      else xs = (bitValues out B').take xs.length)
    (hi : Round5.Round2.PackedInvariant out B') :
    resizeDefaultObservation xs initial (.ok n) result := by
  rw [hr]
  by_cases hn : 0 ≤ n.val ∧ n.val.toNat < Round5.maxVectorLength
  · simp only [resizeDefaultObservation, hn, ite_true]
    exact ⟨hl, hb, hi⟩
  · simp only [resizeDefaultObservation, hn, ite_false]

/-- Natural-length success facts lift to the complete converted default-resize contract. -/
theorem resizeDefaultFromNatural {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (x : X)
    (hsuccess : ∀ n : Nat, n < Round5.maxVectorLength →
      JuliaLean.base.range.JConvert.convert (T := I64) x = .ok (int (n : Int)) →
        resizeDefaultSuccessAt xs x n) :
    resizeDefaultObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) x)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) x false).run
        (initWords (encodeBits xs))) := by
  cases he : JuliaLean.base.range.JConvert.convert (T := I64) x with
  | error e =>
    exact resizeDefaultObservationError xs _ e _
      (rangeResize_conversion_error (vectorBits xs) x false e _ he)
  | ok n =>
    by_cases hn : 0 ≤ n.val ∧ n.val.toNat < Round5.maxVectorLength
    · have hnat := resizeNonnegNat n hn.1
      have he' : JuliaLean.base.range.JConvert.convert (T := I64) x =
          .ok (int (n.val.toNat : Int)) := he.trans (congrArg Except.ok hnat)
      obtain ⟨B', out, hr, hl, hb, hi⟩ := hsuccess n.val.toNat hn.2 he'
      exact resizeDefaultObservationOk xs _ out n B' _ hr (hl.trans hnat.symm) hb hi
    · simp only [resizeDefaultObservation, hn, ite_false]
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

/-- A successful shrinking conversion delegates public resizing to the corresponding public interval deletion. -/
theorem rangeSingleResizeShrinkFrom {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B result : BitVector) (requested : X) (first : Bool) (n : I64) (s out : State)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n)
    (hzero : int 0 ≤ n) (hlt : n < B.len)
    (hr : (Round5.Round2.deleteBitRangePublic B
      (if first then ⟨int 1, B.len - n⟩ else ⟨n + int 1, B.len⟩)).run s = (.ok result, out)) :
    (Round5.Round2.resizeBitVectorPublic B requested first).run s = (.ok result, out) := by
  have hneg : ¬ n < int 0 := by change ¬ n.val < 0; change 0 ≤ n.val at hzero; omega
  have hle : ¬ B.len ≤ n := by change ¬ B.len.val ≤ n.val; exact Int.not_le.mpr hlt
  have hneq : (n == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    subst n
    exact (Int.lt_irrefl B.len.val) hlt
  rw [rangeDelete_public_eq] at hr
  simp only [Round5.Round2.resizeBitVectorPublic, hc, Round5.Round2.liftRangeResult,
    shape_run_bind, shape_run_pure, hneg, hle, or_self, ite_false,
    rangeDelete_length_formula, bitVectorResize, bitVectorResizeInt, hneq,
    Bool.false_eq_true, hlt, ite_true]
  exact hr

/-- Reading a source interval already clipped to its block size needs no additional clipping. -/
theorem resizeFrontSingleClip (word : U64) (count : Nat) (hc : count ≤ 64) :
    and_int (lshr_int (and_int word
      (and_int (shl_int u64Max (int 0)) (not_int (shl_int u64Max (int count))))) (int 0))
      (not_int (shl_int u64Max (int count))) =
    lshr_int (and_int word
      (and_int (shl_int u64Max (int 0)) (not_int (shl_int u64Max (int count))))) (int 0) := by
  apply packedBit_ext
  intro bit hb
  have hshift (w : U64) : packedBit (lshr_int w (int 0)) bit = packedBit w bit := by
    have h := dequePackedShiftRight w 0 bit (by decide)
    simpa only [Int.ofNat_zero, hb, decide_true, Bool.true_and, Nat.add_zero] using h
  rw [dequePackedAnd, scalar_packedBit_not _ _ hb, rangeSingleHighMaskBit count bit hc hb,
    hshift]
  have hmax : packedBit (shl_int u64Max (int 0)) bit = true := by
    simpa only [Int.ofNat_zero, Nat.zero_le, decide_true] using
      rangeSingleHighMaskBit 0 bit (by decide) hb
  rw [dequePackedAnd, dequePackedAnd, scalar_packedBit_not _ _ hb,
    hmax, rangeSingleHighMaskBit count bit hc hb]
  simp only [Nat.zero_le, decide_true, Bool.true_and]
  cases h : decide (count ≤ bit) <;> simp only [h, Bool.not_false, Bool.not_true,
    Bool.and_true, Bool.and_false]

/-- A rightward overlapping copy wholly within one word takes one block iteration. -/
theorem resizeFrontSingleRtolRun (chunks offset count : Nat) (word : U64) (s out : State)
    (ho : 0 < offset) (hc : 0 < count) (hn : offset + count ≤ 64)
    (hg : (mutableGet chunks (int 1)).run s = (.ok word, s))
    (hw : (mutableSet chunks (rangeSingleCopyWord word offset 0 count) (int 1)).run s = (.ok (), out)) :
    (copyChunksRtol chunks (int ((offset + 1 : Nat) : Int)) (int 1) (int count)).run s = (.ok (), out) := by
  have hneq : (int ((offset + 1 : Nat) : Int) == int 1) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val (offset + 1) (by omega)] at hv
    change ((offset + 1 : Nat) : Int) = 1 at hv
    omega
  have horder : ¬ int ((offset + 1 : Nat) : Int) < int 1 := by
    change ¬ (int ((offset + 1 : Nat) : Int)).val < 1
    rw [packedInt_val (offset + 1) (by omega)]
    omega
  have hsmall : int count < int 64 := by
    change (int count).val < 64
    rw [packedInt_val count (by omega)]
    omega
  have hpos : int count > int 0 := by
    change 0 < (int count).val
    rw [packedInt_val count (by omega)]
    omega
  have hsub : int count - int count = int 0 := by rw [dequeIntSub]; simp only [Int.sub_self]
  have hzeroadd : ∀ a : Int, int a + int 0 = int a := by
    intro a
    rw [packedInt_add, Int.add_zero]
  have hd0 := rangeSingleAddress offset (by omega)
  have hde : int ((offset + 1 : Nat) : Int) + int count - int 1 = int ((offset + count : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hse : int 1 + int count - int 1 = int count := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  have hd1 : getChunksId (int ((offset + count : Nat) : Int)) =
      (int 1, int ((offset + count - 1 : Nat) : Int)) := by
    have h := rangeSingleAddress (offset + count - 1) (by omega)
    rw [show offset + count - 1 + 1 = offset + count by omega] at h
    exact h
  have hs1 : getChunksId (int count) = (int 1, int ((count - 1 : Nat) : Int)) := by
    have h := rangeSingleAddress (count - 1) (by omega)
    rw [show count - 1 + 1 = count by omega] at h
    exact h
  have hiD : int ((offset + count - 1 : Nat) : Int) + int 1 = int ((offset + count : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hiS : int ((count - 1 : Nat) : Int) + int 1 = int count := by
    rw [packedInt_add]
    apply congrArg int
    omega
  simp only [copyChunksRtol, hneq, Bool.false_eq_true, ite_false, horder, dite_false,
    hsmall, ite_true, hsub, hzeroadd]
  rw [resizeFrontLoopUnfold]
  simp only [hpos, ite_true, hde, hse, hd0, hd1, hs1,
    show getChunksId (int 1) = (int 1, int 0) from rfl,
    show (int 1 - int 1 == int 0) = true from rfl, hiD, hiS,
    glueSrcBitChunks, shape_run_bind, hg,
    show ¬ (int 1 > int 1 ∧ int 0 > int 0) from by decide, ite_false, shape_run_pure,
    resizeFrontSingleClip word count (by omega)]
  simp only [rangeSingleCopyWord, rangeSingleKeep, Nat.zero_add, Int.ofNat_zero] at hw
  rw [hw]
  simp only [shape_run_bind, hsub,
    show int 0 < int 64 from by decide, ite_true,
    show int 0 - int 0 = int 0 from rfl, hzeroadd,
    show (int 1 - int 1 != int 0) = false from rfl, Bool.false_eq_true, ite_false,
    shape_run_pure]
  rw [resizeFrontLoopUnfold]
  simp only [show ¬ int 0 > int 0 from by decide, ite_false, shape_run_pure, shape_run_bind]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The concrete new prefix retained by in-place front growth, followed by the original sequence. -/
def resizeFrontSingleBits (xs : List Bool) (added : Nat) : List Bool :=
  (List.range added).map (fun i => xs.getD i false) ++ xs

/-- Front growth adds exactly the requested number of logical positions. -/
theorem resizeFrontSingleLength (xs : List Bool) (added : Nat) :
    (resizeFrontSingleBits xs added).length = added + xs.length := by
  simp only [resizeFrontSingleBits, List.length_append, List.length_map, List.length_range]

/-- Every original logical bit is preserved as the exact final suffix. -/
theorem resizeFrontSingleSuffix (xs : List Bool) (added : Nat) :
    (resizeFrontSingleBits xs added).drop added = xs := by
  have hlen : ((List.range added).map (fun i => xs.getD i false)).length = added := by
    simp only [List.length_map, List.length_range]
  change (((List.range added).map (fun i => xs.getD i false)) ++ xs).drop added = xs
  exact List.drop_left' hlen

/-- The grown sequence reads either an unspecified retained prefix position or an original suffix bit. -/
theorem resizeFrontSingleGet (xs : List Bool) (added bit : Nat) :
    (resizeFrontSingleBits xs added).getD bit false =
      if bit < added then xs.getD bit false else xs.getD (bit - added) false := by
  have hlen : ((List.range added).map (fun i => xs.getD i false)).length = added := by
    simp only [List.length_map, List.length_range]
  unfold resizeFrontSingleBits
  by_cases hb : bit < added
  · rw [if_pos hb, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hb),
      List.getElem?_map, List.getElem?_eq_getElem (by simp only [List.length_range]; exact hb)]
    simp only [List.getElem_range, Option.map_some, Option.getD_some]
  · rw [if_neg hb, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen]
    rfl

/-- The one-word overlapping right copy encodes the complete grown logical vector. -/
theorem resizeFrontSingleWord (xs : List Bool) (added : Nat)
    (hn : added + xs.length ≤ 64) :
    rangeSingleCopyWord (packedPrefix xs 0 64) added 0 xs.length =
      packedPrefix (resizeFrontSingleBits xs added) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [rangeSingleCopyBit _ _ _ _ bit hn (by omega) hb,
    packedWord_bit (resizeFrontSingleBits xs added) 0 bit hb]
  simp only [Nat.zero_add, Nat.add_zero, Nat.zero_mul]
  rw [resizeFrontSingleGet xs added bit]
  by_cases hp : bit < added
  · rw [if_neg (by omega), if_pos hp, packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]
  · by_cases hi : bit < added + xs.length
    · rw [if_pos (by omega), if_neg hp, packedWord_bit xs 0 (bit - added) (by omega)]
      simp only [Nat.zero_mul, Nat.zero_add]
    · rw [if_neg (by omega), if_neg hp, packedWord_bit xs 0 bit hb]
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega : xs.length ≤ bit),
        List.getElem?_eq_none (by omega : xs.length ≤ bit - added)]

/-- Front growth of an empty input has a false-filled canonical representative. -/
theorem resizeFrontSingleEmptyBits (added : Nat) :
    resizeFrontSingleBits [] added = List.replicate added false := by
  simp only [resizeFrontSingleBits, List.getD_nil, List.append_nil]
  simpa only [List.length_range] using (List.map_const' (l := List.range added) (b := false))
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

/-- Forward-copy dispatch selects the right-to-left algorithm for a rightward overlapping interval. -/
theorem resizeFrontSingleCopyRun (chunks offset count : Nat) (word : U64) (s out : State)
    (ho : 0 < offset) (hc : 0 < count) (hn : offset + count ≤ 64)
    (hg : (mutableGet chunks (int 1)).run s = (.ok word, s))
    (hw : (mutableSet chunks (rangeSingleCopyWord word offset 0 count) (int 1)).run s = (.ok (), out)) :
    (copyChunks chunks (int ((offset + 1 : Nat) : Int)) chunks (int 1) (int count)).run s = (.ok (), out) := by
  have hz : (int count == int 0) = false := fillPositiveLength count hc (by omega)
  have hgt : int ((offset + 1 : Nat) : Int) > int 1 := by
    change 1 < (int ((offset + 1 : Nat) : Int)).val
    rw [packedInt_val (offset + 1) (by omega)]
    omega
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, hgt, and_self, dite_true]
  exact resizeFrontSingleRtolRun chunks offset count word s out ho hc hn hg hw

/-- Canonical one-word front growth follows the same exact overlapping-copy formula. -/
theorem resizeFrontSingleCopyStore (word : U64) (offset count spare : Nat)
    (ho : 0 < offset) (hc : 0 < count) (hn : offset + count ≤ 64) :
    (copyChunks 0 (int ((offset + 1 : Nat) : Int)) 0 (int 1) (int count)).run
      (dequeWordStore [word] spare) =
        (.ok (), dequeWordStore [rangeSingleCopyWord word offset 0 count] spare) := by
  apply resizeFrontSingleCopyRun 0 offset count word _ _ ho hc hn
  · simpa only [List.getD_cons_zero, Nat.zero_add, Int.ofNat_one] using
      dequeWordRead [word] spare 0 (by simp) (by simp)
  · simpa only [List.set_cons_zero, Nat.zero_add, Int.ofNat_one] using
      dequeWordSet [word] spare 0 (rangeSingleCopyWord word offset 0 count) (by simp) (by simp)

/-- Public front growth composes optional storage growth and the rightward preservation copy. -/
theorem resizeFrontSinglePublicGrowFrom {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitArray 1) (requested : X) (n oldCount : I64) (s grown out : State)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n)
    (hzero : ¬ n < int 0) (hlt : B.len < n)
    (hl : (mutableLength B.chunks).run s = (.ok oldCount, s))
    (hg : ((if numBitChunks n > oldCount then do
        growChunkVector B.chunks (numBitChunks n - oldCount)
        mutableSet B.chunks (u64 0) (← mutableLength B.chunks)
      else pure ()) : BitMutationM Unit).run s = (.ok (), grown))
    (hcopy : (copyChunks B.chunks (int 1 + n - B.len) B.chunks (int 1) B.len).run grown =
      (.ok (), out)) :
    (Round5.Round2.resizeBitVectorPublic B requested true).run s =
      (.ok {B with len := n}, out) := by
  have hle : B.len ≤ n := Int.le_of_lt hlt
  have hnlt : ¬ n < B.len := Int.not_lt.mpr hle
  have hne : (n == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    change B.len.val < n.val at hlt
    omega
  simp only [Round5.Round2.resizeBitVectorPublic, hc, Round5.Round2.liftRangeResult,
    shape_run_bind, shape_run_pure, hle, or_true, ite_true,
    bitVectorResize, bitVectorResizeInt, hne, Bool.false_eq_true, ite_false, hzero, hnlt, hl]
  dsimp only [BitVector] at *
  by_cases hnew : numBitChunks n > oldCount
  · simp only [hnew, ite_true] at hg ⊢
    have hfactor : ((do
        growChunkVector B.chunks (numBitChunks n - oldCount)
        mutableSet B.chunks (u64 0) (← mutableLength B.chunks)
        copyChunks B.chunks (int 1 + n - B.len) B.chunks (int 1) B.len
        pure ({B with len := n} : BitArray 1)) : BitMutationM (BitArray 1)) =
        ((do
          growChunkVector B.chunks (numBitChunks n - oldCount)
          mutableSet B.chunks (u64 0) (← mutableLength B.chunks)) >>= fun _ => do
            copyChunks B.chunks (int 1 + n - B.len) B.chunks (int 1) B.len
            pure ({B with len := n} : BitArray 1)) := by
      simp only [bind_assoc]
    rw [hfactor, shape_run_bind, hg]
    simp only [shape_run_bind, hcopy, shape_run_pure]
  · simp only [hnew, ite_false, shape_run_pure] at hg ⊢
    have he : s = grown := congrArg Prod.snd hg
    rw [he, shape_run_bind, hcopy]
    rfl

/-- Growing a nonempty vector at the front within one chunk installs its exact preserved suffix. -/
theorem resizeFrontSingleNonemptyGrowRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (n : Nat)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n))
    (hp : 0 < xs.length) (hg : xs.length < n) (hn : n ≤ 64) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run (initWords (encodeBits xs)) =
      (.ok {vectorBits xs with len := int n},
        initWords (encodeBits (resizeFrontSingleBits xs (n - xs.length)))) := by
  let word := packedPrefix xs 0 64
  let added := n - xs.length
  let ys := resizeFrontSingleBits xs added
  have hys : ys.length = n := by
    rw [resizeFrontSingleLength]
    dsimp only [added]
    omega
  have henc : encodeBits xs = [word] := rangeSingleEncoding xs hp (by omega)
  have hency : encodeBits ys = [packedPrefix ys 0 64] :=
    rangeSingleEncoding ys (by rw [hys]; omega) (by rw [hys]; exact hn)
  have hinput : initWords (encodeBits xs) = dequeWordStore [word] 32 := by
    rw [← dequeWordStoreInitial, henc]
  have houtput : initWords (encodeBits ys) = dequeWordStore [packedPrefix ys 0 64] 32 := by
    rw [← dequeWordStoreInitial, hency]
  have hcopy := resizeFrontSingleCopyStore word added xs.length 32 (by dsimp only [added]; omega) hp
    (by dsimp only [added]; omega)
  have hword : rangeSingleCopyWord word added 0 xs.length = packedPrefix ys 0 64 :=
    resizeFrontSingleWord xs added (by dsimp only [added]; omega)
  rw [hword] at hcopy
  have hpos : ¬ int n < int 0 := by
    change ¬ (int n).val < 0
    rw [packedInt_val n (by omega)]
    omega
  have hlt : (vectorBits xs).len < int n := by
    change (int xs.length).val < (int n).val
    rw [packedInt_val xs.length (by omega), packedInt_val n (by omega)]
    omega
  have hlen : (mutableLength (vectorBits xs).chunks).run (dequeWordStore [word] 32) =
      (.ok (int 1), dequeWordStore [word] 32) := by
    simpa only [vectorBits, List.length_cons, List.length_nil, Nat.zero_add, Int.ofNat_one] using
      dequeWordLength [word] 32
  have hphase : ((if numBitChunks (int n) > int 1 then do
      growChunkVector 0 (numBitChunks (int n) - int 1)
      mutableSet 0 (u64 0) (← mutableLength 0)
    else pure ()) : BitMutationM Unit).run (dequeWordStore [word] 32) =
      (.ok (), dequeWordStore [word] 32) := by
    rw [rangeSingleChunkCount n (by omega) hn, if_neg (by decide)]
    rfl
  have hdest : int 1 + int n - int xs.length = int ((added + 1 : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [added]
    omega
  rw [hinput, houtput]
  apply resizeFrontSinglePublicGrowFrom (vectorBits xs) requested (int n) (int 1)
    (dequeWordStore [word] 32) (dequeWordStore [word] 32) _ hc hpos hlt hlen hphase
  change (copyChunks 0 (int 1 + int n - int xs.length) 0 (int 1) (int xs.length)).run _ = _
  rw [hdest]
  exact hcopy

/-- Front growth from empty consumes one spare word and leaves a zero-filled representative. -/
theorem resizeFrontSingleEmptyGrowRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (requested : X) (n : Nat)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n))
    (hp : 0 < n) (hn : n ≤ 64) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits []) requested true).run (initWords (encodeBits [])) =
      (.ok {vectorBits [] with len := int n}, dequeWordStore (encodeBits (List.replicate n false)) 31) := by
  have hpos : ¬ int n < int 0 := by
    change ¬ (int n).val < 0
    rw [packedInt_val n (by omega)]
    omega
  have hlt : (vectorBits []).len < int n := by
    change 0 < (int n).val
    rw [packedInt_val n (by omega)]
    omega
  have he : encodeBits (List.replicate n false) = [u64 0] := by
    rw [rangeSingleEncoding _ (by simpa only [List.length_replicate] using hp)
      (by simpa only [List.length_replicate] using hn), shiftSingleFalseWord]
  rw [he]
  have hl : (mutableLength (vectorBits []).chunks).run (initWords (encodeBits [])) =
      (.ok (int 0), initWords (encodeBits [])) := by rfl
  have hphase : ((if numBitChunks (int n) > int 0 then do
      growChunkVector 0 (numBitChunks (int n) - int 0)
      mutableSet 0 (u64 0) (← mutableLength 0)
    else pure ()) : BitMutationM Unit).run (initWords (encodeBits [])) =
      (.ok (), dequeWordStore [u64 0] 31) := by
    rw [rangeSingleChunkCount n hp hn, if_pos (by decide)]
    change dequeGrowZero.run (dequeWordStore [] (31 + 1)) = _
    exact dequeGrowZeroRun [] 31 (by simp)
  apply resizeFrontSinglePublicGrowFrom (vectorBits []) requested (int n) (int 0)
    (initWords (encodeBits [])) (dequeWordStore [u64 0] 31) _ hc hpos hlt hl hphase
  exact rangeSingleCopyEmptyRun 0 _ _ _

/-- Every growing one-chunk request has a canonical packed representation retaining the original suffix. -/
theorem resizeFrontSingleGrowthCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (n : Nat)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n))
    (hg : xs.length < n) (hn : n ≤ 64) :
    ∃ B' out,
      (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs)) = (.ok B', out) ∧
      B'.len = int n ∧ xs = (bitValues out B').drop (n - xs.length) ∧
      Round5.Round2.PackedInvariant out B' := by
  let ys := resizeFrontSingleBits xs (n - xs.length)
  let B' : BitArray 1 := {vectorBits xs with len := int n}
  have hys : ys.length = n := by rw [resizeFrontSingleLength]; omega
  have hb : ys.length ≤ 9223372036854775807 := by rw [hys]; omega
  by_cases hz : xs = []
  · subst xs
    let out := dequeWordStore (encodeBits ys) 31
    have hy : ys = List.replicate n false := by
      dsimp only [ys]
      simp only [List.length_nil, Nat.sub_zero, resizeFrontSingleEmptyBits]
    have hrun := resizeFrontSingleEmptyGrowRun requested n hc (by simpa using hg) hn
    rw [← hy] at hrun
    have hcontents : out.contents B'.chunks = (encodeBits ys).map some :=
      dequeWordContents _ _ (packedEncoded_lengthBound ys hb)
    have hnew : B'.len = int ys.length := by change int n = int ys.length; rw [hys]
    have hv := scalar_bitValues_contents out B' ys hb hnew hcontents
    refine ⟨B', out, hrun, rfl, ?_, scalar_invariant_of_contents out B' ys hb hnew hcontents⟩
    rw [hv]
    exact (resizeFrontSingleSuffix [] (n - [].length)).symm
  · have hp : 0 < xs.length := List.length_pos_iff.mpr hz
    let out := initWords (encodeBits ys)
    have hcontents : out.contents B'.chunks = (encodeBits ys).map some :=
      scalar_initial_contents _ (packedEncoded_lengthBound ys hb)
    have hnew : B'.len = int ys.length := by change int n = int ys.length; rw [hys]
    have hv := scalar_bitValues_contents out B' ys hb hnew hcontents
    refine ⟨B', out, resizeFrontSingleNonemptyGrowRun xs requested n hc hp hg hn, rfl, ?_,
      scalar_invariant_of_contents out B' ys hb hnew hcontents⟩
    rw [hv]
    exact (resizeFrontSingleSuffix xs (n - xs.length)).symm

/-- Successful front resizing at a natural length, with the specified retained suffix. -/
def resizeFrontSingleSuccessAt {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (n : Nat) : Prop :=
  ∃ B' out,
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
      (initWords (encodeBits xs)) = (.ok B', out) ∧
    B'.len = int (n : Int) ∧
    (if n < xs.length then bitValues out B' = xs.drop (xs.length - n)
      else xs = (bitValues out B').drop (n - xs.length)) ∧
    Round5.Round2.PackedInvariant out B'

/-- Front resizing to the existing length retains the entire logical vector and padding. -/
theorem resizeFrontSingleSameLength {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (hn : xs.length ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int xs.length)) :
    resizeFrontSingleSuccessAt xs requested xs.length := by
  let B := vectorBits xs
  let s := initWords (encodeBits xs)
  refine ⟨B, s, rangeResize_same_length B requested true s hc, rfl, ?_, ?_⟩
  · rw [if_neg (Nat.lt_irrefl _), Nat.sub_self, List.drop_zero]
    exact (scalar_bits_initial xs [int xs.length] hn).symm
  · exact scalar_initial_invariant xs [int xs.length] hn

/-- The frozen nonnegative-resize observation specialized to front preservation. -/
def resizeFrontSingleObservation (xs : List Bool) (initial : State)
    (converted : JuliaLean.base.range.JlX I64)
    (result : Id (Except Error BitVector × MutableMemory U64)) : Prop :=
  match converted with
  | .error _ => match result.1 with
    | .error _ => result.2 = initial
    | .ok _ => False
  | .ok newLength =>
    if 0 ≤ newLength.val ∧ newLength.val.toNat < Round5.maxVectorLength then
      match result.1 with
      | .ok B' =>
        B'.len = newLength ∧
        (if newLength.val.toNat < xs.length then
          bitValues result.2 B' = xs.drop (xs.length - newLength.val.toNat)
         else xs = (bitValues result.2 B').drop (newLength.val.toNat - xs.length)) ∧
        Round5.Round2.PackedInvariant result.2 B'
      | .error _ => False
    else True

/-- Nonnegative converted integers agree with their natural representatives. -/
theorem resizeFrontSingleNonnegNat (n : I64) (hn : 0 ≤ n.val) :
    n = int (n.val.toNat : Int) := by
  apply Subtype.ext
  change n.val = wrapInt .i64 (n.val.toNat : Int)
  rw [Int.toNat_of_nonneg hn, wrapInt_of_inRange .i64 n.val n.property]

/-- Failed conversion supplies the frozen front-resize failure observation without mutation. -/
theorem resizeFrontSingleObservationError (xs : List Bool) (initial : State)
    (e : JuliaLean.base.range.Exc)
    (result : Id (Except Error BitVector × MutableMemory U64))
    (hr : result = (.error (Round5.Round2.mutationErrorOfRange e), initial)) :
    resizeFrontSingleObservation xs initial (.error e) result := by
  rw [hr]
  rfl

/-- A successful abstract front-resize result supplies length, suffix, and packing observations. -/
theorem resizeFrontSingleObservationOk (xs : List Bool) (initial out : State)
    (n : I64) (B' : BitVector)
    (result : Id (Except Error BitVector × MutableMemory U64))
    (hr : result = (.ok B', out))
    (hl : B'.len = n)
    (hb : if n.val.toNat < xs.length then
      bitValues out B' = xs.drop (xs.length - n.val.toNat)
      else xs = (bitValues out B').drop (n.val.toNat - xs.length))
    (hi : Round5.Round2.PackedInvariant out B') :
    resizeFrontSingleObservation xs initial (.ok n) result := by
  rw [hr]
  by_cases hn : 0 ≤ n.val ∧ n.val.toNat < Round5.maxVectorLength
  · simp only [resizeFrontSingleObservation, hn, ite_true]
    exact ⟨hl, hb, hi⟩
  · simp only [resizeFrontSingleObservation, hn, ite_false]

/-- Natural-length front-resize success facts lift through arbitrary installed conversions. -/
theorem resizeFrontSingleFromNatural {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hsuccess : ∀ n : Nat, n < Round5.maxVectorLength →
      JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n) →
        resizeFrontSingleSuccessAt xs requested n) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) := by
  cases he : JuliaLean.base.range.JConvert.convert (T := I64) requested with
  | error e =>
    exact resizeFrontSingleObservationError xs _ e _
      (rangeResize_conversion_error (vectorBits xs) requested true e _ he)
  | ok n =>
    by_cases hn : 0 ≤ n.val ∧ n.val.toNat < Round5.maxVectorLength
    · have hnat := resizeFrontSingleNonnegNat n hn.1
      have he' : JuliaLean.base.range.JConvert.convert (T := I64) requested =
          .ok (int (n.val.toNat : Int)) := he.trans (congrArg Except.ok hnat)
      obtain ⟨B', out, hr, hl, hb, hi⟩ := hsuccess n.val.toNat hn.2 he'
      exact resizeFrontSingleObservationOk xs _ out n B' _ hr (hl.trans hnat.symm) hb hi
    · simp only [resizeFrontSingleObservation, hn, ite_false]
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

/-- Public default shrinking and public suffix deletion execute exactly the same operation. -/
theorem rangeSuffixResizeRunEq {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (requested : X) (n : I64) (s : State)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n)
    (hn : ¬ n < int 0) (hlt : n < B.len) :
    (Round5.Round2.resizeBitVectorPublic B requested false).run s =
      (Round5.Round2.deleteBitRangePublic B ⟨n + int 1, B.len⟩).run s := by
  have hle : ¬ B.len ≤ n := by change ¬ B.len.val ≤ n.val; exact Int.not_le.mpr hlt
  have hne : (n == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    have hv := congrArg Subtype.val h
    change n.val < B.len.val at hlt
    omega
  rw [rangeDelete_public_eq]
  simp only [Round5.Round2.resizeBitVectorPublic, hc, Round5.Round2.liftRangeResult,
    shape_run_bind, shape_run_pure, hn, hle, or_self, ite_false, Bool.false_eq_true,
    rangeDelete_length_formula, bitVectorResize, bitVectorResizeInt, hne, hlt, ite_true]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A two-bit vector has one initialized packed word. -/
theorem resizeFrontGrowthWitnessEncoding : encodeBits [true, false] = [u64 1] := by
  decide

/-- A rightward two-bit copy crossing into an uninitialized destination chunk reports that read. -/
theorem resizeFrontUndefinedCopy (chunks : Nat) (s : State) (word : U64)
    (hs : (mutableGet chunks (int 1)).run s = (.ok word, s))
    (hd : (mutableGet chunks (int 2)).run s = (.error .undefinedReference, s)) :
    (copyChunksRtol chunks (int 128) (int 1) (int 2)).run s =
      (.error .undefinedReference, s) := by
  simp only [copyChunksRtol,
    show (int 128 == int 1) = false from rfl,
    show ¬ int 128 < int 1 from by decide,
    show int 2 < int 64 from by decide,
    Bool.false_eq_true, ite_false, dite_false, ite_true,
    show int 2 - int 2 = int 0 from rfl,
    show int 1 + int 0 = int 1 from rfl,
    show int 128 + int 0 = int 128 from rfl]
  rw [resizeFrontLoopUnfold]
  simp only [show int 2 > int 0 from by decide, ite_true,
    show getChunksId (int 128) = (int 2, int 63) from rfl,
    show getChunksId (int 128 + int 2 - int 1) = (int 3, int 0) from rfl,
    show getChunksId (int 1) = (int 1, int 0) from rfl,
    show getChunksId (int 1 + int 2 - int 1) = (int 1, int 1) from rfl,
    show (int 3 - int 2 == int 0) = false from rfl,
    show (int 1 - int 1 == int 0) = true from rfl,
    Bool.false_eq_true, ite_false, ite_true, glueSrcBitChunks,
    shape_run_bind, hs, hd,
    show ¬ (int 1 > int 1 ∧ int 0 > int 0) from by decide, ite_false, shape_run_pure]

/-- A failed preservation copy is propagated by the public front-growth operation. -/
theorem resizeFrontGrowthErrorFrom {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitArray 1) (requested : X) (n oldCount : I64) (s grown out : State) (error : Error)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n)
    (hzero : ¬ n < int 0) (hlt : B.len < n)
    (hl : (mutableLength B.chunks).run s = (.ok oldCount, s))
    (hg : ((if numBitChunks n > oldCount then do
        growChunkVector B.chunks (numBitChunks n - oldCount)
        mutableSet B.chunks (u64 0) (← mutableLength B.chunks)
      else pure ()) : BitMutationM Unit).run s = (.ok (), grown))
    (hcopy : (copyChunks B.chunks (int 1 + n - B.len) B.chunks (int 1) B.len).run grown =
      (.error error, out)) :
    (Round5.Round2.resizeBitVectorPublic B requested true).run s =
      (.error error, out) := by
  have hle : B.len ≤ n := Int.le_of_lt hlt
  have hnlt : ¬ n < B.len := Int.not_lt.mpr hle
  have hne : (n == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    change B.len.val < n.val at hlt
    omega
  simp only [Round5.Round2.resizeBitVectorPublic, hc, Round5.Round2.liftRangeResult,
    shape_run_bind, shape_run_pure, hle, or_true, ite_true,
    bitVectorResize, bitVectorResizeInt, hne, Bool.false_eq_true, ite_false, hzero, hnlt, hl]
  dsimp only [BitVector] at *
  by_cases hnew : numBitChunks n > oldCount
  · simp only [hnew, ite_true] at hg ⊢
    have hfactor : ((do
        growChunkVector B.chunks (numBitChunks n - oldCount)
        mutableSet B.chunks (u64 0) (← mutableLength B.chunks)
        copyChunks B.chunks (int 1 + n - B.len) B.chunks (int 1) B.len
        pure ({B with len := n} : BitArray 1)) : BitMutationM (BitArray 1)) =
        ((do
          growChunkVector B.chunks (numBitChunks n - oldCount)
          mutableSet B.chunks (u64 0) (← mutableLength B.chunks)) >>= fun _ => do
            copyChunks B.chunks (int 1 + n - B.len) B.chunks (int 1) B.len
            pure ({B with len := n} : BitArray 1)) := by
      simp only [bind_assoc]
    rw [hfactor, shape_run_bind, hg]
    simp only [shape_run_bind, hcopy, shape_run_pure]
  · simp only [hnew, ite_false, shape_run_pure] at hg ⊢
    have he : s = grown := congrArg Prod.snd hg
    rw [he, shape_run_bind, hcopy]

/-- The frozen front-growth model reads an uninitialized intermediate destination chunk. -/
theorem resizeFrontGrowthUndefinedReference :
    ((Round5.Round2.resizeBitVectorPublic (vectorBits [true, false]) (int 129) true).run
      (initWords (encodeBits [true, false]))).1 = .error .undefinedReference := by
  let grown := resizeSlotStore ([some (u64 1), none, some (u64 0)] ++ List.replicate 30 none) 3
  have hc := resizeFrontUndefinedCopy 0 grown (u64 1) rfl rfl
  have hcopy : (copyChunks 0 (int 128) 0 (int 1) (int 2)).run grown =
      (.error .undefinedReference, grown) := by
    simp only [copyChunks, show (int 2 == int 0) = false from rfl,
      show 0 = 0 ∧ int 128 > int 1 from by decide, Bool.false_eq_true, ite_false, dite_true]
    exact hc
  have hr := resizeFrontGrowthErrorFrom (vectorBits [true, false]) (int 129) (int 129) (int 1)
    (initWords [u64 1]) grown grown .undefinedReference rfl (by decide) (by decide) rfl
    (by rfl) hcopy
  rw [resizeFrontGrowthWitnessEncoding]
  exact congrArg Prod.fst hr
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- One aligned block pasted into a two-word destination, preserving every other bit. -/
def resizeFrontPairPaste (low high aligned : U64) (destination count : Nat) : U64 × U64 :=
  if destination < 64 then
    (copyPairPaste low aligned destination (min count (64 - destination)),
      if 64 < destination + count then
        copyPairPaste high (lshr_int aligned (int ((64 - destination : Nat) : Int)))
          0 (destination + count - 64)
      else high)
  else
    (low, copyPairPaste high aligned (destination - 64) count)

/-- The first complete block of a two-iteration front-growth copy. -/
def resizeFrontPairStage (xs : List Bool) (n : Nat) : U64 × U64 :=
  resizeFrontPairPaste (packedPrefix xs 0 64) (packedPrefix xs 1 64)
    (copyPairSlice xs (xs.length - 64)) (n - 64) 64

/-- The exact two-word output of the rightward preservation copy. -/
def resizeFrontPairOutput (xs : List Bool) (n : Nat) : U64 × U64 :=
  if xs.length ≤ 64 then
    resizeFrontPairPaste (packedPrefix xs 0 64) (packedPrefix xs 1 64)
      (packedPrefix xs 0 64) (n - xs.length) xs.length
  else
    let stage := resizeFrontPairStage xs n
    resizeFrontPairPaste stage.1 stage.2 (resizeFrontPairClip stage.1 (xs.length - 64))
      (n - xs.length) (xs.length - 64)
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

/-- Logical observation of a pair of packed destination words. -/
def resizeFrontPairBit (words : U64 × U64) (bit : Nat) : Bool :=
  if bit < 64 then packedBit words.1 bit else packedBit words.2 (bit - 64)

/-- A two-word paste changes exactly its destination interval. -/
theorem resizeFrontPairPasteBit (low high aligned : U64) (destination count bit : Nat)
    (hc : count ≤ 64) (hn : destination + count ≤ 128) (hb : bit < 128) :
    resizeFrontPairBit (resizeFrontPairPaste low high aligned destination count) bit =
      if destination ≤ bit ∧ bit < destination + count then packedBit aligned (bit - destination)
      else resizeFrontPairBit (low, high) bit := by
  by_cases hd : destination < 64
  · by_cases hl : bit < 64
    · simp only [resizeFrontPairBit, resizeFrontPairPaste, hd, hl, ite_true]
      rw [copyPairPasteBit _ _ destination (min count (64 - destination)) bit (by omega) hl]
      have hi : (destination ≤ bit ∧ bit < destination + min count (64 - destination)) ↔
          (destination ≤ bit ∧ bit < destination + count) := by omega
      simp only [hi]
    · have hbit : bit - 64 < 64 := by omega
      simp only [resizeFrontPairBit, resizeFrontPairPaste, hd, hl, ite_true, ite_false]
      by_cases hs : 64 < destination + count
      · rw [if_pos hs, copyPairPasteBit _ _ 0 (destination + count - 64) (bit - 64) (by omega) hbit]
        by_cases hi : destination ≤ bit ∧ bit < destination + count
        · rw [if_pos (by omega), if_pos hi]
          simp only [Nat.sub_zero]
          rw [copyPairRightBit aligned (64 - destination) (bit - 64) (by omega) hbit,
            if_pos (by omega)]
          congr 1
          omega
        · rw [if_neg (by omega), if_neg hi]
      · rw [if_neg hs, if_neg (by omega)]
  · by_cases hl : bit < 64
    · simp only [resizeFrontPairBit, resizeFrontPairPaste, hd, hl, ite_false, ite_true]
      rw [if_neg (by omega)]
    · have hbit : bit - 64 < 64 := by omega
      simp only [resizeFrontPairBit, resizeFrontPairPaste, hd, hl, ite_false]
      rw [copyPairPasteBit _ _ (destination - 64) count (bit - 64) (by omega) hbit]
      by_cases hi : destination ≤ bit ∧ bit < destination + count
      · rw [if_pos (by omega), if_pos hi]
        congr 1
        omega
      · rw [if_neg (by omega), if_neg hi]

/-- Canonical paired words expose the original logical input and false padding. -/
theorem resizeFrontPairInitialBit (xs : List Bool) (bit : Nat) (hb : bit < 128) :
    resizeFrontPairBit (packedPrefix xs 0 64, packedPrefix xs 1 64) bit = xs.getD bit false := by
  by_cases hl : bit < 64
  · rw [resizeFrontPairBit, if_pos hl, packedWord_bit xs 0 bit hl]
    simp only [Nat.zero_mul, Nat.zero_add]
  · rw [resizeFrontPairBit, if_neg hl, packedWord_bit xs 1 (bit - 64) (by omega)]
    simp only [Nat.one_mul]
    congr 1
    omega

/-- Selecting all 64 source bits leaves a word unchanged. -/
theorem resizeFrontPairClipFull (word : U64) : resizeFrontPairClip word 64 = word := by
  apply packedBit_ext
  intro bit hb
  rw [resizeFrontPairClipBit word 64 bit (by decide) hb, if_pos hb]

/-- Clipping beyond the logical end preserves an already packed single-word source. -/
theorem resizeFrontPairClipPacked (xs : List Bool) (count : Nat)
    (hx : xs.length ≤ count) (hc : count ≤ 64) :
    resizeFrontPairClip (packedPrefix xs 0 64) count = packedPrefix xs 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [resizeFrontPairClipBit _ count bit hc hb]
  by_cases hi : bit < count
  · rw [if_pos hi]
  · rw [if_neg hi, packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : xs.length ≤ bit)]
    rfl

/-- The first descending block replaces exactly the final 64 destination positions. -/
theorem resizeFrontPairStageBit (xs : List Bool) (n bit : Nat)
    (hp : 64 < xs.length) (hg : xs.length < n) (hn : n ≤ 128) (hb : bit < 128) :
    resizeFrontPairBit (resizeFrontPairStage xs n) bit =
      if n - 64 ≤ bit ∧ bit < n then xs.getD (bit - (n - xs.length)) false
      else xs.getD bit false := by
  rw [resizeFrontPairStage, resizeFrontPairPasteBit _ _ _ (n - 64) 64 bit (by decide) (by omega) hb,
    resizeFrontPairInitialBit xs bit hb]
  have hend : n - 64 + 64 = n := by omega
  rw [hend]
  by_cases hi : n - 64 ≤ bit ∧ bit < n
  · rw [if_pos hi, if_pos hi, copyPairSliceBit xs (xs.length - 64) (bit - (n - 64)) (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg hi]

/-- The first block leaves the low source remainder untouched for the second block. -/
theorem resizeFrontPairStageLow (xs : List Bool) (n bit : Nat)
    (hp : 64 < xs.length) (hg : xs.length < n) (hn : n ≤ 128)
    (hb : bit < xs.length - 64) :
    packedBit (resizeFrontPairStage xs n).1 bit = xs.getD bit false := by
  have h := resizeFrontPairStageBit xs n bit hp hg hn (by omega)
  have hbit : bit < 64 := by omega
  simpa only [resizeFrontPairBit, hbit, ite_true, show ¬ (n - 64 ≤ bit ∧ bit < n) by omega, ite_false] using h

/-- Clipping the preserved low source remainder is independent of the first block's writes. -/
theorem resizeFrontPairStageClip (xs : List Bool) (n : Nat)
    (hp : 64 < xs.length) (hg : xs.length < n) (hn : n ≤ 128) :
    resizeFrontPairClip (resizeFrontPairStage xs n).1 (xs.length - 64) =
      resizeFrontPairClip (packedPrefix xs 0 64) (xs.length - 64) := by
  apply packedBit_ext
  intro bit hb
  rw [resizeFrontPairClipBit _ _ bit (by omega) hb,
    resizeFrontPairClipBit _ _ bit (by omega) hb]
  by_cases hi : bit < xs.length - 64
  · rw [if_pos hi, if_pos hi, resizeFrontPairStageLow xs n bit hp hg hn hi,
      packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]
  · rw [if_neg hi, if_neg hi]

/-- Both descending blocks produce the retained original suffix and exact new-prefix representative. -/
theorem resizeFrontPairOutputBit (xs : List Bool) (n bit : Nat)
    (hg : xs.length < n) (hn : n ≤ 128) (hb : bit < 128) :
    resizeFrontPairBit (resizeFrontPairOutput xs n) bit =
      (resizeFrontSingleBits xs (n - xs.length)).getD bit false := by
  by_cases hs : xs.length ≤ 64
  · simp only [resizeFrontPairOutput, hs, ite_true]
    rw [resizeFrontPairPasteBit _ _ _ (n - xs.length) xs.length bit hs (by omega) hb,
      resizeFrontPairInitialBit xs bit hb, resizeFrontSingleGet]
    by_cases hp : bit < n - xs.length
    · rw [if_neg (by omega), if_pos hp]
    · by_cases hi : bit < n
      · rw [if_pos (by omega), if_neg hp,
          packedWord_bit xs 0 (bit - (n - xs.length)) (by omega)]
        simp only [Nat.zero_mul, Nat.zero_add]
      · rw [if_neg (by omega), if_neg hp]
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega : xs.length ≤ bit),
          List.getElem?_eq_none (by omega : xs.length ≤ bit - (n - xs.length))]
  · have hold : 64 < xs.length := by omega
    simp only [resizeFrontPairOutput, hs, ite_false]
    rw [resizeFrontPairPasteBit _ _ _ (n - xs.length) (xs.length - 64) bit (by omega) (by omega) hb]
    by_cases hi : n - xs.length ≤ bit ∧ bit < (n - xs.length) + (xs.length - 64)
    · rw [if_pos hi, resizeFrontPairClipBit _ (xs.length - 64) (bit - (n - xs.length))
          (by omega) (by omega), if_pos (by omega),
        resizeFrontPairStageLow xs n (bit - (n - xs.length)) hold hg hn (by omega),
        resizeFrontSingleGet, if_neg (by omega)]
    · rw [if_neg hi, resizeFrontPairStageBit xs n bit hold hg hn hb, resizeFrontSingleGet]
      by_cases hp : bit < n - xs.length
      · rw [if_neg (by omega), if_pos hp]
      · by_cases he : bit < n
        · rw [if_pos (by omega), if_neg hp]
        · rw [if_neg (by omega), if_neg hp]
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega : xs.length ≤ bit),
            List.getElem?_eq_none (by omega : xs.length ≤ bit - (n - xs.length))]

/-- Front growth into two chunks installs exactly the encoding of its concrete logical result. -/
theorem resizeFrontPairOutputEncoding (xs : List Bool) (n : Nat)
    (hg : xs.length < n) (hp : 64 < n) (hn : n ≤ 128) :
    [(resizeFrontPairOutput xs n).1, (resizeFrontPairOutput xs n).2] =
      encodeBits (resizeFrontSingleBits xs (n - xs.length)) := by
  let ys := resizeFrontSingleBits xs (n - xs.length)
  have hlen : ys.length = n := by
    rw [resizeFrontSingleLength]
    omega
  have hlo : (resizeFrontPairOutput xs n).1 = packedPrefix ys 0 64 := by
    apply packedBit_ext
    intro bit hb
    rw [packedWord_bit ys 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]
    have h := resizeFrontPairOutputBit xs n bit hg hn (by omega)
    simpa only [resizeFrontPairBit, hb, ite_true] using h
  have hhi : (resizeFrontPairOutput xs n).2 = packedPrefix ys 1 64 := by
    apply packedBit_ext
    intro bit hb
    rw [packedWord_bit ys 1 bit hb]
    simp only [Nat.one_mul]
    have h := resizeFrontPairOutputBit xs n (64 + bit) hg hn (by omega)
    simpa only [resizeFrontPairBit, show ¬ 64 + bit < 64 by omega, ite_false,
      show 64 + bit - 64 = bit by omega] using h
  rw [hlo, hhi]
  exact (copyPairEncoding ys (by rw [hlen]; exact hp) (by rw [hlen]; exact hn)).symm
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

/-- A block contained in one destination word performs exactly one masked paste. -/
theorem frontCopyBlockOne (chunks : Nat) (pd ps : I64) (count offset : Nat)
    (kd ks0 ls0 ks1 ls1 : I64) (s out : State) (destination gathered aligned : U64)
    (hp : 0 < count) (hn : offset + count ≤ 64)
    (hd0 : getChunksId pd = (kd, int offset))
    (hd1 : getChunksId (pd + int count - int 1) = (kd, int ((offset + count - 1 : Nat) : Int)))
    (hs0 : getChunksId ps = (ks0, ls0))
    (hs1 : getChunksId (ps + int count - int 1) = (ks1, ls1))
    (hg : (glueSrcBitChunks chunks ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run s =
      (.ok gathered, s))
    (hclip : and_int gathered (not_int (shl_int u64Max (int count))) = aligned)
    (hr : (mutableGet chunks kd).run s = (.ok destination, s))
    (hw : (mutableSet chunks (copyPairPaste destination aligned offset count) kd).run s = (.ok (), out)) :
    (frontCopyBlock chunks pd ps (int count)).run s = (.ok (), out) := by
  have hinc : int ((offset + count - 1 : Nat) : Int) + int 1 = int ((offset + count : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  simp only [copyPairPaste, rangeSingleKeep] at hw
  simp only [frontCopyBlock, hd0, hd1, hs0, hs1, shape_int_sub_self, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, ite_true, ite_false, hinc]
  by_cases hsame : (ks1 - ks0 == int 0) = true
  all_goals
    simp only [copyPairSourceMask, hsame, Bool.false_eq_true, ite_true, ite_false] at hg ⊢
    simp only [shape_run_bind, hg, hclip, hr, hw, shape_run_pure]

/-- A block spanning the destination boundary performs its low write before its high write. -/
theorem frontCopyBlockTwo (chunks : Nat) (pd ps : I64) (count offset lastCount : Nat)
    (ks0 ls0 ks1 ls1 : I64) (s mid out : State) (low high gathered aligned : U64)
    (ho : offset ≤ 64) (hp : 0 < lastCount) (hn : lastCount ≤ 64)
    (hd0 : getChunksId pd = (int 1, int offset))
    (hd1 : getChunksId (pd + int count - int 1) = (int 2, int ((lastCount - 1 : Nat) : Int)))
    (hs0 : getChunksId ps = (ks0, ls0))
    (hs1 : getChunksId (ps + int count - int 1) = (ks1, ls1))
    (hg : (glueSrcBitChunks chunks ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run s =
      (.ok gathered, s))
    (hclip : and_int gathered (not_int (shl_int u64Max (int count))) = aligned)
    (hr0 : (mutableGet chunks (int 1)).run s = (.ok low, s))
    (hw0 : (mutableSet chunks (copyPairPaste low aligned offset (64 - offset)) (int 1)).run s =
      (.ok (), mid))
    (hr1 : (mutableGet chunks (int 2)).run mid = (.ok high, mid))
    (hw1 : (mutableSet chunks (copyPairPaste high
      (lshr_int aligned (int ((64 - offset : Nat) : Int))) 0 lastCount) (int 2)).run mid =
      (.ok (), out)) :
    (frontCopyBlock chunks pd ps (int count)).run s = (.ok (), out) := by
  have hinc : int ((lastCount - 1 : Nat) : Int) + int 1 = int lastCount := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hsub : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  simp only [copyPairPaste, copyPairKeepHigh offset ho] at hw0
  simp only [copyPairPaste, copyPairKeepLow lastCount hn] at hw1
  have hshift (w : U64) : shl_int w (int (0 : Nat)) = w := by
    apply packedBit_ext
    intro bit hb
    rw [reversePackedLeft w 0 bit (by decide) hb]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  rw [hshift] at hw1
  simp only [frontCopyBlock, hd0, hd1, hs0, hs1, hinc,
    show int 2 - int 1 = int 1 from rfl,
    show (int 1 == int 0) = false from rfl,
    show (int 1 != int 0) = true from rfl,
    Bool.false_eq_true, ite_false, ite_true, hsub]
  by_cases hsame : (ks1 - ks0 == int 0) = true
  all_goals
    simp only [copyPairSourceMask, hsame, Bool.false_eq_true, ite_true, ite_false] at hg ⊢
    simp only [shape_run_bind, hg, hclip, hr0, hw0, hr1, hw1, shape_run_pure]

theorem frontCopyAddZero (x : I64) : x + int 0 = x := by
  apply Subtype.ext
  change wrapInt .i64 (x.val + 0) = x.val
  rw [Int.add_zero, wrapInt_of_inRange .i64 x.val x.property]

/-- At most one word of remaining bits starts at the original source and destination positions. -/
theorem frontCopyRegistersSmall (posD posS : I64) (count : Nat) (hc : count ≤ 64) :
    frontCopyRegisters posD posS (int count) =
      (int count, int count, int 0, posS, posD) := by
  have hs : (if int count < int 64 then int count else int 64) = int count := by
    by_cases h : count < 64
    · have h' : int count < int 64 := by
        change (int count).val < 64
        rw [packedInt_val count (by omega)]
        omega
      rw [if_pos h']
    · have he : count = 64 := by omega
      subst count
      rw [if_neg (by decide)]
      rfl
  simp only [frontCopyRegisters, hs, shape_int_sub_self, frontCopyAddZero]

/-- A first full block leaves the lower source prefix for the next iteration. -/
theorem frontCopyRegistersLarge (posD posS : I64) (count : Nat)
    (hp : 64 < count) (hn : count ≤ 128) :
    frontCopyRegisters posD posS (int count) =
      (int count, int 64, int ((count - 64 : Nat) : Int),
        posS + int ((count - 64 : Nat) : Int), posD + int ((count - 64 : Nat) : Int)) := by
  have hs : ¬ int count < int 64 := by
    change ¬ (int count).val < 64
    rw [packedInt_val count (by omega)]
    omega
  have hd : int count - int 64 = int ((count - 64 : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  simp only [frontCopyRegisters, hs, ite_false, hd]

/-- One positive block of at most64 bits completes the installed loop after its single write phase. -/
theorem frontCopyLoopSmall (chunks : Nat) (posD posS : I64) (count : Nat) (s out : State)
    (hp : 0 < count) (hn : count ≤ 64)
    (hb : (frontCopyBlock chunks posD posS (int count)).run s = (.ok (), out)) :
    (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (int count))).run s =
      (.ok (frontCopyRegisters posD posS (int 0)), out) := by
  have hz : ¬ (frontCopyRegisters posD posS (int 0)).1 > int 0 := by
    change ¬ int 0 > int 0
    decide
  have ht := frontCopyLoopDone chunks posD posS (frontCopyRegisters posD posS (int 0)) out hz
  have hpos : int count > int 0 := by
    change 0 < (int count).val
    rw [packedInt_val count (by omega)]
    omega
  rw [frontCopyRegistersSmall posD posS count hn]
  exact frontCopyLoopYield chunks posD posS
    (int count, int count, int 0, posS, posD) (frontCopyRegisters posD posS (int 0))
    s out out hpos hb (by simpa only [shape_int_sub_self] using ht)

/-- Two positive blocks complete every descending copy of65 through128 bits. -/
theorem frontCopyLoopLarge (chunks : Nat) (posD posS : I64) (count : Nat) (s mid out : State)
    (hp : 64 < count) (hn : count ≤ 128)
    (hfirst : (frontCopyBlock chunks (posD + int ((count - 64 : Nat) : Int))
      (posS + int ((count - 64 : Nat) : Int)) (int 64)).run s = (.ok (), mid))
    (hlast : (frontCopyBlock chunks posD posS (int ((count - 64 : Nat) : Int))).run mid =
      (.ok (), out)) :
    (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (int count))).run s =
      (.ok (frontCopyRegisters posD posS (int 0)), out) := by
  have ht := frontCopyLoopSmall chunks posD posS (count - 64) mid out (by omega) (by omega) hlast
  have hd : int count - int 64 = int ((count - 64 : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hpos : int count > int 0 := by
    change 0 < (int count).val
    rw [packedInt_val count (by omega)]
    omega
  rw [frontCopyRegistersLarge posD posS count hp hn]
  exact frontCopyLoopYield chunks posD posS
    (int count, int 64, int ((count - 64 : Nat) : Int),
      posS + int ((count - 64 : Nat) : Int), posD + int ((count - 64 : Nat) : Int))
    (frontCopyRegisters posD posS (int 0)) s mid out hpos hfirst
    (by simpa only [hd] using ht)

/-- Canonical execution of any positive block pasted wholly within two initialized destination words. -/
theorem frontCopyBlockPairRun (low high gathered aligned : U64) (destination count spare : Nat)
    (ps ks0 ls0 ks1 ls1 : I64)
    (hc : 0 < count) (hn : destination + count ≤ 128)
    (hs0 : getChunksId ps = (ks0, ls0))
    (hs1 : getChunksId (ps + int count - int 1) = (ks1, ls1))
    (hg : (glueSrcBitChunks 0 ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run
      (dequeWordStore [low, high] spare) = (.ok gathered, dequeWordStore [low, high] spare))
    (hclip : and_int gathered (not_int (shl_int u64Max (int count))) = aligned) :
    (frontCopyBlock 0 (int ((destination + 1 : Nat) : Int)) ps (int count)).run
      (dequeWordStore [low, high] spare) =
        (.ok (), dequeWordStore
          [(resizeFrontPairPaste low high aligned destination count).1,
           (resizeFrontPairPaste low high aligned destination count).2] spare) := by
  have hde : int ((destination + 1 : Nat) : Int) + int count - int 1 =
      int ((destination + count : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  by_cases hd : destination < 64
  · have hd0 := rangeSingleAddress destination hd
    by_cases he : destination + count ≤ 64
    · have hd1 : getChunksId (int ((destination + 1 : Nat) : Int) + int count - int 1) =
          (int 1, int ((destination + count - 1 : Nat) : Int)) := by
        rw [hde]
        have h := rangeSingleAddress (destination + count - 1) (by omega)
        rw [show destination + count - 1 + 1 = destination + count by omega] at h
        exact h
      have hm : min count (64 - destination) = count := Nat.min_eq_left (by omega)
      simp only [resizeFrontPairPaste, hd, ite_true, hm, show ¬ 64 < destination + count by omega, ite_false]
      exact frontCopyBlockOne 0 _ ps count destination (int 1) ks0 ls0 ks1 ls1 _ _ low gathered aligned
        hc he hd0 hd1 hs0 hs1 hg hclip (copyPairReadLow low high spare)
        (copyPairSetLow low high _ spare)
    · have hd1 : getChunksId (int ((destination + 1 : Nat) : Int) + int count - int 1) =
          (int 2, int ((destination + count - 64 - 1 : Nat) : Int)) := by
        rw [hde]
        have h := copyPairFinalAddress (destination + count) (by omega) hn
        rw [show destination + count - 65 = destination + count - 64 - 1 by omega] at h
        exact h
      have hm : min count (64 - destination) = 64 - destination := Nat.min_eq_right (by omega)
      simp only [resizeFrontPairPaste, hd, ite_true, hm, show 64 < destination + count by omega]
      exact frontCopyBlockTwo 0 _ ps count destination (destination + count - 64) ks0 ls0 ks1 ls1
        (dequeWordStore [low, high] spare)
        (dequeWordStore [copyPairPaste low aligned destination (64 - destination), high] spare) _
        low high gathered aligned (by omega) (by omega) (by omega)
        hd0 hd1 hs0 hs1 hg hclip (copyPairReadLow low high spare)
        (copyPairSetLow low high _ spare) (copyPairReadHigh _ high spare)
        (copyPairSetHigh _ high _ spare)
  · have hd0 : getChunksId (int ((destination + 1 : Nat) : Int)) =
        (int 2, int ((destination - 64 : Nat) : Int)) := by
      have h := copyPairAddress destination (by omega)
      simpa only [copyPairStartChunk, hd, ite_false,
        show destination % 64 = destination - 64 by omega] using h
    have hd1 : getChunksId (int ((destination + 1 : Nat) : Int) + int count - int 1) =
        (int 2, int ((destination - 64 + count - 1 : Nat) : Int)) := by
      rw [hde]
      have h := copyPairFinalAddress (destination + count) (by omega) hn
      rw [show destination + count - 65 = destination - 64 + count - 1 by omega] at h
      exact h
    simp only [resizeFrontPairPaste, hd, ite_false]
    exact frontCopyBlockOne 0 _ ps count (destination - 64) (int 2) ks0 ls0 ks1 ls1 _ _ high gathered aligned
      hc (by omega) hd0 hd1 hs0 hs1 hg hclip (copyPairReadHigh low high spare)
      (copyPairSetHigh low high _ spare)

/-- Zero-offset source clipping returns exactly the low selected bits of the source word. -/
theorem frontCopyZeroSourceWord (word : U64) (count : Nat) (hc : count ≤ 64) :
    lshr_int (and_int word (and_int (shl_int u64Max (int 0))
      (not_int (shl_int u64Max (int count))))) (int 0) = resizeFrontPairClip word count := by
  apply packedBit_ext
  intro bit hb
  have hshift (w : U64) : packedBit (lshr_int w (int 0)) bit = packedBit w bit := by
    have h := copyPairRightBit w 0 bit (by decide) hb
    simpa only [Int.ofNat_zero, Nat.add_zero, hb, ite_true] using h
  rw [hshift]
  rw [dequePackedAnd, dequePackedAnd, scalar_packedBit_not _ _ hb,
    rangeSingleHighMaskBit count bit hc hb]
  have hmax : packedBit (shl_int u64Max (int 0)) bit = true := by
    simpa only [Int.ofNat_zero, Nat.zero_le, decide_true] using
      rangeSingleHighMaskBit 0 bit (by decide) hb
  rw [hmax, Bool.true_and, resizeFrontPairClipBit word count bit hc hb]
  by_cases h : bit < count <;> simp only [h, show count ≤ bit ↔ ¬ bit < count by omega,
    decide_not, decide_true, decide_false, Bool.not_false, Bool.not_true, Bool.and_true,
    Bool.and_false, ite_true, ite_false]

/-- Clipping a source word a second time leaves the same selected source block. -/
theorem frontCopyClipIdempotent (word : U64) (count : Nat) (hc : count ≤ 64) :
    resizeFrontPairClip (resizeFrontPairClip word count) count = resizeFrontPairClip word count := by
  apply packedBit_ext
  intro bit hb
  rw [resizeFrontPairClipBit _ count bit hc hb, resizeFrontPairClipBit word count bit hc hb]
  by_cases h : bit < count <;> simp only [h, ite_true, ite_false]

/-- Reading a low source prefix has the exact clipped value and leaves the state unchanged. -/
theorem frontCopyZeroSourceRun (chunks count : Nat) (word : U64) (s : State)
    (hp : 0 < count) (hc : count ≤ 64)
    (hr : (mutableGet chunks (int 1)).run s = (.ok word, s)) :
    (glueSrcBitChunks chunks (int 1) (int 1)
      (copyPairSourceMask (int 1) (int 1) (int 0) (int ((count - 1 : Nat) : Int))) (int 0)).run s =
      (.ok (resizeFrontPairClip word count), s) := by
  have hinc : int ((count - 1 : Nat) : Int) + int 1 = int count := by
    rw [packedInt_add]
    apply congrArg int
    omega
  simp only [copyPairSourceMask, shape_int_sub_self, beq_self_eq_true, ite_true, hinc,
    glueSrcBitChunks, shape_run_bind, hr,
    show ¬ (int 1 > int 1 ∧ int 0 > int 0) from by decide, ite_false, shape_run_pure,
    frontCopyZeroSourceWord word count hc]

/-- Every positive source prefix up to64 bits has the expected low-word end address. -/
theorem frontCopySourceEnd (count : Nat) (hp : 0 < count) (hn : count ≤ 64) :
    getChunksId (int 1 + int count - int 1) = (int 1, int ((count - 1 : Nat) : Int)) := by
  have he : int 1 + int count - int 1 = int count := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  rw [he]
  have h := rangeSingleAddress (count - 1) (by omega)
  rw [show count - 1 + 1 = count by omega] at h
  exact h

/-- The concrete descending loop on two initialized words realizes the exact staged output. -/
theorem resizeFrontPairRtolRun (xs : List Bool) (n spare : Nat)
    (hpos : 0 < xs.length) (hg : xs.length < n) (hp : 64 < n) (hn : n ≤ 128) :
    (copyChunksRtol 0 (int ((n - xs.length + 1 : Nat) : Int)) (int 1) (int xs.length)).run
      (dequeWordStore [packedPrefix xs 0 64, packedPrefix xs 1 64] spare) =
        (.ok (), dequeWordStore
          [(resizeFrontPairOutput xs n).1, (resizeFrontPairOutput xs n).2] spare) := by
  let low := packedPrefix xs 0 64
  let high := packedPrefix xs 1 64
  let pd := int ((n - xs.length + 1 : Nat) : Int)
  let initial := dequeWordStore [low, high] spare
  let out := dequeWordStore [(resizeFrontPairOutput xs n).1, (resizeFrontPairOutput xs n).2] spare
  have hdv : pd.val = ((n - xs.length + 1 : Nat) : Int) := packedInt_val _ (by omega)
  have hneq : (pd == int 1) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [hdv] at hv
    change ((n - xs.length + 1 : Nat) : Int) = 1 at hv
    omega
  have horder : ¬ pd < int 1 := by change ¬ pd.val < 1; rw [hdv]; omega
  apply frontCopyRtolFromLoop 0 pd (int 1) (int xs.length) initial out
    (frontCopyRegisters pd (int 1) (int 0)) hneq horder
  by_cases hsmall : xs.length ≤ 64
  · have hsource := frontCopyZeroSourceRun 0 xs.length low initial hpos hsmall
      (copyPairReadLow low high spare)
    have hclip : and_int (resizeFrontPairClip low xs.length)
        (not_int (shl_int u64Max (int xs.length))) = low := by
      change resizeFrontPairClip (resizeFrontPairClip low xs.length) xs.length = low
      rw [frontCopyClipIdempotent low xs.length hsmall,
        resizeFrontPairClipPacked xs xs.length (Nat.le_refl _) hsmall]
    have hblock := frontCopyBlockPairRun low high (resizeFrontPairClip low xs.length) low
      (n - xs.length) xs.length spare (int 1) (int 1) (int 0) (int 1)
      (int ((xs.length - 1 : Nat) : Int)) hpos (by omega) rfl
      (frontCopySourceEnd xs.length hpos hsmall) hsource hclip
    have hblock' : (frontCopyBlock 0 pd (int 1) (int xs.length)).run initial = (.ok (), out) := by
      simpa only [out, resizeFrontPairOutput, hsmall, ite_true] using hblock
    exact frontCopyLoopSmall 0 pd (int 1) xs.length initial out hpos hsmall hblock'
  · have hold : 64 < xs.length := by omega
    have hr : xs.length - 64 < 64 := by omega
    let stage := resizeFrontPairStage xs n
    let mid := dequeWordStore [stage.1, stage.2] spare
    have hsrc : getChunksId (int ((xs.length - 64 + 1 : Nat) : Int)) =
        (int 1, int ((xs.length - 64 : Nat) : Int)) := rangeSingleAddress (xs.length - 64) hr
    have hsrcend : getChunksId (int ((xs.length - 64 + 1 : Nat) : Int) + int 64 - int 1) =
        (int 2, int ((xs.length - 65 : Nat) : Int)) := by
      have he : int ((xs.length - 64 + 1 : Nat) : Int) + int 64 - int 1 = int xs.length := by
        rw [packedInt_add, dequeIntSub]
        apply congrArg int
        omega
      rw [he]
      exact copyPairFinalAddress xs.length hold (by omega)
    have hsource := copyPairFirstPackedRun xs (xs.length - 64) 0 initial hold (by omega)
      (by omega) (copyPairReadLow low high spare) (copyPairReadHigh low high spare)
    simp only [copyPairStartChunk, hr, ite_true, Nat.mod_eq_of_lt hr] at hsource
    have hblock := frontCopyBlockPairRun low high (copyPairSlice xs (xs.length - 64))
      (copyPairSlice xs (xs.length - 64)) (n - 64) 64 spare
      (int ((xs.length - 64 + 1 : Nat) : Int)) (int 1) (int ((xs.length - 64 : Nat) : Int))
      (int 2) (int ((xs.length - 65 : Nat) : Int)) (by decide) (by omega)
      hsrc hsrcend hsource (resizeFrontPairClipFull _)
    have hpd : pd + int ((xs.length - 64 : Nat) : Int) = int ((n - 64 + 1 : Nat) : Int) := by
      rw [packedInt_add]
      apply congrArg int
      omega
    have hps : int 1 + int ((xs.length - 64 : Nat) : Int) = int ((xs.length - 64 + 1 : Nat) : Int) := by
      rw [packedInt_add]
      apply congrArg int
      omega
    have hfirst : (frontCopyBlock 0 (pd + int ((xs.length - 64 : Nat) : Int))
        (int 1 + int ((xs.length - 64 : Nat) : Int)) (int 64)).run initial = (.ok (), mid) := by
      rw [hpd, hps]
      exact hblock
    have hlastsource := frontCopyZeroSourceRun 0 (xs.length - 64) stage.1 mid (by omega) (by omega)
      (copyPairReadLow stage.1 stage.2 spare)
    have hlastclip : and_int (resizeFrontPairClip stage.1 (xs.length - 64))
        (not_int (shl_int u64Max (int ((xs.length - 64 : Nat) : Int)))) =
          resizeFrontPairClip stage.1 (xs.length - 64) :=
      frontCopyClipIdempotent stage.1 (xs.length - 64) (by omega)
    have hlastblock := frontCopyBlockPairRun stage.1 stage.2
      (resizeFrontPairClip stage.1 (xs.length - 64)) (resizeFrontPairClip stage.1 (xs.length - 64))
      (n - xs.length) (xs.length - 64) spare (int 1) (int 1) (int 0) (int 1)
      (int ((xs.length - 64 - 1 : Nat) : Int)) (by omega) (by omega) rfl
      (frontCopySourceEnd (xs.length - 64) (by omega) (by omega)) hlastsource hlastclip
    have hlast : (frontCopyBlock 0 pd (int 1) (int ((xs.length - 64 : Nat) : Int))).run mid =
        (.ok (), out) := by
      simpa only [out, resizeFrontPairOutput, hsmall, ite_false] using hlastblock
    exact frontCopyLoopLarge 0 pd (int 1) xs.length initial mid out hold (by omega) hfirst hlast

/-- Every rightward preservation copy for front growth within two chunks returns the exact logical suffix encoding. -/
theorem resizeFrontPairCopyRun (xs : List Bool) (n spare : Nat)
    (hpos : 0 < xs.length) (hg : xs.length < n) (hp : 64 < n) (hn : n ≤ 128) :
    (copyChunks 0 (int ((n - xs.length + 1 : Nat) : Int)) 0 (int 1) (int xs.length)).run
      (dequeWordStore [packedPrefix xs 0 64, packedPrefix xs 1 64] spare) =
        (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs (n - xs.length))) spare) := by
  have hz : (int xs.length == int 0) = false := fillPositiveLength xs.length hpos (by omega)
  have hd : int ((n - xs.length + 1 : Nat) : Int) > int 1 := by
    change 1 < (int ((n - xs.length + 1 : Nat) : Int)).val
    rw [packedInt_val _ (by omega)]
    omega
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, hd, and_self, dite_true]
  exact (resizeFrontPairRtolRun xs n spare hpos hg hp hn).trans (by
    rw [resizeFrontPairOutputEncoding xs n hg hp hn])
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

/-- The second packed word is zero when all original bits fit the first word. -/
theorem resizeFrontPairInitialHighZero (xs : List Bool) (hn : xs.length ≤ 64) :
    packedPrefix xs 1 64 = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit xs 1 bit hb, packedBit_zero]
  simp only [Nat.one_mul, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : xs.length ≤ 64 + bit)]
  rfl

/-- Native resizing factored over its memory operations for small equational proofs. -/
def resizeInternalProgram
    (length : Nat → BitMutationM I64) (grow : Nat → I64 → BitMutationM Unit)
    (write : Nat → U64 → I64 → BitMutationM Unit)
    (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (deleteRange : (BitRange → I64) → BitVector → BitRange → BitMutationM BitVector)
    (rangeLength : BitRange → I64) (B : BitVector) (n : I64) (first : Bool) :
    BitMutationM BitVector := do
  let n0 := B.len
  if n == n0 then return B
  if n < int 0 then throw .bounds
  if n < n0 then
    let r := if first then ⟨int 1, n0 - n⟩ else ⟨n + int 1, n0⟩
    return ← deleteRange rangeLength B r
  let Bc := B.chunks
  let k0 ← length Bc
  let k1 := numBitChunks n
  if k1 > k0 then
    grow Bc (k1 - k0)
    write Bc (u64 0) (← length Bc)
  if first then copy Bc (int 1 + n - n0) Bc (int 1) n0
  return {B with len := n}

/-- The factorization uses exactly the frozen resize implementation and callbacks. -/
theorem resizeInternalProgramFactor (rangeLength : BitRange → I64)
    (B : BitVector) (n : I64) (first : Bool) :
    bitVectorResizeInt rangeLength B n first =
      resizeInternalProgram mutableLength growChunkVector mutableSet copyChunks
        bitVectorDeleteRange rangeLength B n first := rfl

/-- Empty-source copying makes the choice of growth end observationally irrelevant. -/
theorem resizeInternalEmptyEnds
    (length : Nat → BitMutationM I64) (grow : Nat → I64 → BitMutationM Unit)
    (write : Nat → U64 → I64 → BitMutationM Unit)
    (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (deleteRange : (BitRange → I64) → BitVector → BitRange → BitMutationM BitVector)
    (rangeLength : BitRange → I64) (B : BitVector) (n : I64) (hB : B.len = int 0)
    (hcopy : ∀ dest pd src ps, copy dest pd src ps (int 0) = pure ()) :
    resizeInternalProgram length grow write copy deleteRange rangeLength B n true =
      resizeInternalProgram length grow write copy deleteRange rangeLength B n false := by
  simp only [resizeInternalProgram, hB]
  by_cases hz : (n == int 0) = true
  · simp only [hz, ite_true]
  · have hz' : (n == int 0) = false := Bool.eq_false_iff.mpr hz
    simp only [hz', Bool.false_eq_true, ite_false]
    by_cases hn : n < int 0
    · simp only [hn, ite_true]
      rfl
    · simp only [hn, ite_false, Bool.true_eq, ite_true, Bool.false_eq_true,
        hcopy, pure_bind]
      rfl

/-- On an empty original vector, the selected growth end cannot change execution. -/
theorem resizeEmptyEndsEqual (B : BitVector) (n : I64) (hB : B.len = int 0)
    (rangeLength : BitRange → I64) :
    bitVectorResizeInt rangeLength B n true = bitVectorResizeInt rangeLength B n false := by
  rw [resizeInternalProgramFactor, resizeInternalProgramFactor]
  exact resizeInternalEmptyEnds mutableLength growChunkVector mutableSet copyChunks
    bitVectorDeleteRange rangeLength B n hB (fun dest pd src ps => resizeCopyZero dest src pd ps)

/-- The public conversion wrapper also preserves the equality of empty-vector growth ends. -/
theorem resizeEmptyPublicEndsEqual {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (requested : X) (hB : B.len = int 0) (n : I64)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n)
    (hn : ¬ n < int 0) :
    Round5.Round2.resizeBitVectorPublic B requested true =
      Round5.Round2.resizeBitVectorPublic B requested false := by
  have hle : B.len ≤ n := by rw [hB]; change (0 : Int) ≤ n.val; exact Int.le_of_not_gt hn
  simp only [Round5.Round2.resizeBitVectorPublic, hc, Round5.Round2.liftRangeResult,
    pure_bind, hle, or_true, ite_true, bitVectorResize]
  exact resizeEmptyEndsEqual B n hB _

/-- Two-word front growth composes the checked preservation copy with exact one-word reserve consumption. -/
theorem resizeFrontPairNonemptyGrowFromCopy {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (n : Nat)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n))
    (hp : 0 < xs.length) (hg : xs.length < n) (hnew : 64 < n) (hn : n ≤ 128)
    (hcopy : ∀ spare : Nat,
      (copyChunks 0 (int ((n - xs.length + 1 : Nat) : Int)) 0 (int 1) (int xs.length)).run
        (dequeWordStore [packedPrefix xs 0 64, packedPrefix xs 1 64] spare) =
        (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs (n - xs.length))) spare)) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run (initWords (encodeBits xs)) =
      (.ok {vectorBits xs with len := int n},
        dequeWordStore (encodeBits (resizeFrontSingleBits xs (n - xs.length)))
          (if xs.length ≤ 64 then 31 else 32)) := by
  let low := packedPrefix xs 0 64
  let high := packedPrefix xs 1 64
  have hzero : ¬ int n < int 0 := by
    change ¬ (int n).val < 0
    rw [packedInt_val n (by omega)]
    omega
  have hlt : (vectorBits xs).len < int n := by
    change (int xs.length).val < (int n).val
    rw [packedInt_val xs.length (by omega), packedInt_val n (by omega)]
    omega
  have hdest : int 1 + int n - int xs.length = int ((n - xs.length + 1 : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    omega
  by_cases hs : xs.length ≤ 64
  · have he : encodeBits xs = [low] := rangeSingleEncoding xs hp hs
    have hh : high = u64 0 := resizeFrontPairInitialHighZero xs hs
    have hin : initWords (encodeBits xs) = dequeWordStore [low] 32 := by
      rw [← dequeWordStoreInitial, he]
    rw [hin, if_pos hs]
    have hlen : (mutableLength (vectorBits xs).chunks).run (dequeWordStore [low] 32) =
        (.ok (int 1), dequeWordStore [low] 32) := by
      simpa only [vectorBits, List.length_cons, List.length_nil, Nat.zero_add, Int.ofNat_one] using dequeWordLength [low] 32
    have hgrow : ((if numBitChunks (int n) > int 1 then do
        growChunkVector 0 (numBitChunks (int n) - int 1)
        mutableSet 0 (u64 0) (← mutableLength 0)
      else pure ()) : BitMutationM Unit).run (dequeWordStore [low] 32) =
        (.ok (), dequeWordStore [low, high] 31) := by
      rw [rangePairChunkCount n hnew hn, if_pos (by decide), hh]
      change dequeGrowZero.run (dequeWordStore [low] (31 + 1)) = _
      exact dequeGrowZeroRun [low] 31 (by simp)
    apply resizeFrontSinglePublicGrowFrom (vectorBits xs) requested (int n) (int 1)
      (dequeWordStore [low] 32) (dequeWordStore [low, high] 31) _ hc hzero hlt hlen hgrow
    change (copyChunks 0 (int 1 + int n - int xs.length) 0 (int 1) (int xs.length)).run _ = _
    rw [hdest]
    exact hcopy 31
  · have he : encodeBits xs = [low, high] := copyPairEncoding xs (by omega) (by omega)
    have hin : initWords (encodeBits xs) = dequeWordStore [low, high] 32 := by
      rw [← dequeWordStoreInitial, he]
    rw [hin, if_neg hs]
    have hlen : (mutableLength (vectorBits xs).chunks).run (dequeWordStore [low, high] 32) =
        (.ok (int 2), dequeWordStore [low, high] 32) := by
      simpa only [vectorBits, List.length_cons, List.length_nil, Nat.zero_add,
        show int ((1 + 1 : Nat) : Int) = int 2 from rfl] using dequeWordLength [low, high] 32
    have hgrow : ((if numBitChunks (int n) > int 2 then do
        growChunkVector 0 (numBitChunks (int n) - int 2)
        mutableSet 0 (u64 0) (← mutableLength 0)
      else pure ()) : BitMutationM Unit).run (dequeWordStore [low, high] 32) =
        (.ok (), dequeWordStore [low, high] 32) := by
      rw [rangePairChunkCount n hnew hn, if_neg (by decide)]
      rfl
    apply resizeFrontSinglePublicGrowFrom (vectorBits xs) requested (int n) (int 2)
      (dequeWordStore [low, high] 32) (dequeWordStore [low, high] 32) _ hc hzero hlt hlen hgrow
    change (copyChunks 0 (int 1 + int n - int xs.length) 0 (int 1) (int xs.length)).run _ = _
    rw [hdest]
    exact hcopy 32

/-- Every nonempty front-growth request through two chunks has exact canonical output storage. -/
theorem resizeFrontPairNonemptyGrowRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (n : Nat)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n))
    (hp : 0 < xs.length) (hg : xs.length < n) (hnew : 64 < n) (hn : n ≤ 128) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run (initWords (encodeBits xs)) =
      (.ok {vectorBits xs with len := int n},
        dequeWordStore (encodeBits (resizeFrontSingleBits xs (n - xs.length)))
          (if xs.length ≤ 64 then 31 else 32)) :=
  resizeFrontPairNonemptyGrowFromCopy xs requested n hc hp hg hnew hn
    (fun spare => resizeFrontPairCopyRun xs n spare hp hg hnew hn)

/-- The public two-word growth operation preserves its exact original suffix and packed padding. -/
theorem resizeFrontPairNonemptyGrowthCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (n : Nat)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok (int n))
    (hp : 0 < xs.length) (hg : xs.length < n) (hnew : 64 < n) (hn : n ≤ 128) :
    ∃ B' out,
      (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs)) = (.ok B', out) ∧
      B'.len = int n ∧ xs = (bitValues out B').drop (n - xs.length) ∧
      Round5.Round2.PackedInvariant out B' := by
  let ys := resizeFrontSingleBits xs (n - xs.length)
  let B' : BitArray 1 := {vectorBits xs with len := int n}
  let spare := if xs.length ≤ 64 then 31 else 32
  let out := dequeWordStore (encodeBits ys) spare
  have hlen : ys.length = n := by rw [resizeFrontSingleLength]; omega
  have hb : ys.length ≤ 9223372036854775807 := by rw [hlen]; omega
  have hcontents : out.contents B'.chunks = (encodeBits ys).map some :=
    dequeWordContents _ _ (packedEncoded_lengthBound ys hb)
  have hnewLength : B'.len = int ys.length := by change int n = int ys.length; rw [hlen]
  have hv := scalar_bitValues_contents out B' ys hb hnewLength hcontents
  refine ⟨B', out, resizeFrontPairNonemptyGrowRun xs requested n hc hp hg hnew hn, rfl, ?_,
    scalar_invariant_of_contents out B' ys hb hnewLength hcontents⟩
  rw [hv]
  exact (resizeFrontSingleSuffix xs (n - xs.length)).symm
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- At a descending whole-word copy stage, higher words are already shifted and lower words retain their source. -/
def frontWholeStage (words : List U64) (remaining : Nat) : List U64 :=
  (List.range (words.length + 1)).map fun i =>
    if i ≤ remaining then words.getD i (u64 0) else words.getD (i - 1) (u64 0)

theorem frontWholeStageLength (words : List U64) (remaining : Nat) :
    (frontWholeStage words remaining).length = words.length + 1 := by
  simp only [frontWholeStage, List.length_map, List.length_range]

theorem frontWholeStageGet (words : List U64) (remaining i : Nat) (hi : i < words.length + 1) :
    (frontWholeStage words remaining).getD i (u64 0) =
      if i ≤ remaining then words.getD i (u64 0) else words.getD (i - 1) (u64 0) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [frontWholeStageLength]; exact hi), Option.getD_some]
  simp only [frontWholeStage, List.getElem_map, List.getElem_range]

/-- Before any descending copy, the extra final word is zero and all original words are unchanged. -/
theorem frontWholeStageInitial (words : List U64) :
    frontWholeStage words words.length = words ++ [u64 0] := by
  apply List.ext_getElem
  · simp only [frontWholeStageLength, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  · intro i hi hi'
    have hb : i < words.length + 1 := by simpa only [frontWholeStageLength] using hi
    rw [List.getElem_eq_getD (fallback := u64 0), frontWholeStageGet words words.length i hb,
      if_pos (by omega), List.getElem_eq_getD (fallback := u64 0)]
    by_cases hlt : i < words.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    · have he : i = words.length := by omega
      subst i
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (Nat.le_refl _), Option.getD_none,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

/-- Copying the next source word to its successor advances exactly one stage. -/
theorem frontWholeStageStep (words : List U64) (k : Nat) (hk : k < words.length) :
    (frontWholeStage words (k + 1)).set (k + 1) (words.getD k (u64 0)) = frontWholeStage words k := by
  apply List.ext_getElem
  · simp only [List.length_set, frontWholeStageLength]
  · intro i hi hi'
    have hb : i < words.length + 1 := by simpa only [frontWholeStageLength] using hi'
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ (k + 1) i _ (by rw [frontWholeStageLength]; omega),
      List.getElem_eq_getD (fallback := u64 0), frontWholeStageGet words k i hb]
    by_cases he : k + 1 = i
    · subst i
      rw [if_pos rfl, if_neg (by omega), Nat.add_sub_cancel]
    · rw [if_neg he, frontWholeStageGet words (k + 1) i hb]
      by_cases hle : i ≤ k
      · rw [if_pos hle, if_pos (by omega)]
      · rw [if_neg hle, if_neg (by omega)]

/-- At completion, the unchanged first word precedes the exact original chunk sequence. -/
theorem frontWholeStageFinal (words : List U64) :
    frontWholeStage words 0 = words.headD (u64 0) :: words := by
  apply List.ext_getElem
  · simp only [frontWholeStageLength, List.length_cons]
  · intro i hi hi'
    have hb : i < words.length + 1 := by simpa only [frontWholeStageLength] using hi
    rw [List.getElem_eq_getD (fallback := u64 0), frontWholeStageGet words 0 i hb,
      List.getElem_eq_getD (fallback := u64 0)]
    cases i with
    | zero =>
      simp only [Nat.le_refl, ite_true, List.getD_cons_zero]
      cases words <;> rfl
    | succ i =>
      simp only [Nat.succ_eq_add_one, show ¬ i + 1 ≤ 0 by omega, ite_false,
        Nat.add_sub_cancel, List.getD_cons_succ]
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

/-- An aligned block starts at the first bit of its corresponding native chunk. -/
theorem frontWholeAddress (chunk : Nat) (hn : chunk * 64 + 1 ≤ 9223372036854775807) :
    getChunksId (int ((chunk * 64 + 1 : Nat) : Int)) = (int ((chunk + 1 : Nat) : Int), int 0) := by
  have h := scalar_chunks_nat (chunk * 64) hn
  have hq : chunk * 64 / 64 = chunk := by omega
  have hm : chunk * 64 % 64 = 0 := by omega
  simpa only [hq, hm, Int.ofNat_zero] using h

/-- The end of an aligned block is bit63 of the same chunk. -/
theorem frontWholeEndAddress (chunk : Nat) (hn : (chunk + 1) * 64 ≤ 9223372036854775807) :
    getChunksId (int ((chunk * 64 + 1 : Nat) : Int) + int 64 - int 1) =
      (int ((chunk + 1 : Nat) : Int), int 63) := by
  have he : int ((chunk * 64 + 1 : Nat) : Int) + int 64 - int 1 =
      int ((chunk * 64 + 63 + 1 : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    exact congrArg int (by omega)
  rw [he]
  have h := scalar_chunks_nat (chunk * 64 + 63) (by omega)
  have hq : (chunk * 64 + 63) / 64 = chunk := by omega
  have hm : (chunk * 64 + 63) % 64 = 63 := by omega
  simpa only [hq, hm, show int ((63 : Nat) : Int) = int 63 from rfl] using h

/-- A full source-word gather preserves the state and returns the complete word. -/
theorem frontWholeGather (chunks : Nat) (chunk : I64) (word : U64) (s : State)
    (hr : (mutableGet chunks chunk).run s = (.ok word, s)) :
    (glueSrcBitChunks chunks chunk chunk
      (copyPairSourceMask chunk chunk (int 0) (int 63)) (int 0)).run s = (.ok word, s) := by
  have hm : copyPairSourceMask chunk chunk (int 0) (int 63) = u64Max := by
    rw [copyPairSourceMask, shape_int_sub_self]
    rfl
  have hw : lshr_int (and_int word u64Max) (int 0) = word := shiftPairNoShiftMask word
  simp only [hm, glueSrcBitChunks, shape_run_bind, hr,
    show ¬ chunk > chunk from Int.lt_irrefl _, false_and, ite_false, hw, shape_run_pure]

/-- A full aligned descending block is exactly one source read and one successor-word replacement. -/
theorem frontWholeBlockFrom (chunks k : Nat) (source destination : U64) (s out : State)
    (hn : (k + 2) * 64 ≤ 9223372036854775807)
    (hr : (mutableGet chunks (int ((k + 1 : Nat) : Int))).run s = (.ok source, s))
    (hd : (mutableGet chunks (int ((k + 2 : Nat) : Int))).run s = (.ok destination, s))
    (hw : (mutableSet chunks source (int ((k + 2 : Nat) : Int))).run s = (.ok (), out)) :
    (frontCopyBlock chunks (int (((k + 1) * 64 + 1 : Nat) : Int))
      (int ((k * 64 + 1 : Nat) : Int)) (int 64)).run s = (.ok (), out) := by
  exact frontCopyBlockOne chunks _ _ 64 0 (int ((k + 2 : Nat) : Int))
    (int ((k + 1 : Nat) : Int)) (int 0) (int ((k + 1 : Nat) : Int)) (int 63)
    s out destination source source (by decide) (by decide)
    (frontWholeAddress (k + 1) (by omega)) (frontWholeEndAddress (k + 1) (by omega))
    (frontWholeAddress k (by omega)) (frontWholeEndAddress k (by omega))
    (frontWholeGather chunks _ source s hr) (resizeFrontPairClipFull source) hd
    (by rw [copyPairPasteFull]; exact hw)

/-- One concrete descending block advances the canonical stage without changing reserve. -/
theorem frontWholeBlockRun (words : List U64) (k spare : Nat)
    (hk : k < words.length) (hn : (words.length + 1) * 64 ≤ 9223372036854775807) :
    (frontCopyBlock 0 (int (((k + 1) * 64 + 1 : Nat) : Int))
      (int ((k * 64 + 1 : Nat) : Int)) (int 64)).run
      (dequeWordStore (frontWholeStage words (k + 1)) spare) =
        (.ok (), dequeWordStore (frontWholeStage words k) spare) := by
  have hlen : (frontWholeStage words (k + 1)).length = words.length + 1 := frontWholeStageLength _ _
  have hread := dequeWordRead (frontWholeStage words (k + 1)) spare k (by omega) (by omega)
  have hdest := dequeWordRead (frontWholeStage words (k + 1)) spare (k + 1) (by omega) (by omega)
  rw [frontWholeStageGet words (k + 1) k (by omega), if_pos (by omega)] at hread
  rw [frontWholeStageGet words (k + 1) (k + 1) (by omega), if_pos (Nat.le_refl _)] at hdest
  have hwrite := dequeWordSet (frontWholeStage words (k + 1)) spare (k + 1)
    (words.getD k (u64 0)) (by omega) (by omega)
  rw [frontWholeStageStep words k hk] at hwrite
  exact frontWholeBlockFrom 0 k (words.getD k (u64 0)) (words.getD (k + 1) (u64 0)) _ _
    (by omega) hread hdest hwrite

/-- The aligned whole-word remaining count gives direct source and successor-word addresses. -/
theorem frontWholeRegisters (k : Nat) (hn : (k + 1) * 64 ≤ 9223372036854775807) :
    frontCopyRegisters (int 65) (int 1) (int (((k + 1) * 64 : Nat) : Int)) =
      (int (((k + 1) * 64 : Nat) : Int), int 64, int ((k * 64 : Nat) : Int),
        int ((k * 64 + 1 : Nat) : Int), int (((k + 1) * 64 + 1 : Nat) : Int)) := by
  have hs : ¬ int (((k + 1) * 64 : Nat) : Int) < int 64 := by
    change ¬ (int (((k + 1) * 64 : Nat) : Int)).val < 64
    rw [packedInt_val _ hn]
    omega
  have hd : int (((k + 1) * 64 : Nat) : Int) - int 64 = int ((k * 64 : Nat) : Int) := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hsource : int 1 + int ((k * 64 : Nat) : Int) = int ((k * 64 + 1 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  have hdest : int 65 + int ((k * 64 : Nat) : Int) = int (((k + 1) * 64 + 1 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  simp only [frontCopyRegisters, hs, ite_false, hd, hsource, hdest]

/-- Induction over remaining whole words verifies the entire descending loop at arbitrary native lengths. -/
theorem frontWholeLoopRun (words : List U64) (remaining spare : Nat)
    (hr : remaining ≤ words.length) (hn : (words.length + 1) * 64 ≤ 9223372036854775807) :
    (frontCopyLoop 0 (int 65) (int 1)
      (frontCopyRegisters (int 65) (int 1) (int ((remaining * 64 : Nat) : Int)))).run
      (dequeWordStore (frontWholeStage words remaining) spare) =
        (.ok (frontCopyRegisters (int 65) (int 1) (int 0)),
          dequeWordStore (frontWholeStage words 0) spare) := by
  induction remaining with
  | zero =>
    exact frontCopyLoopDone 0 (int 65) (int 1) (frontCopyRegisters (int 65) (int 1) (int 0))
      (dequeWordStore (frontWholeStage words 0) spare) (by decide)
  | succ k ih =>
    have hb := frontWholeBlockRun words k spare (by omega) hn
    have ht := ih (by omega)
    have hpos : int (((k + 1) * 64 : Nat) : Int) > int 0 := by
      change 0 < (int (((k + 1) * 64 : Nat) : Int)).val
      rw [packedInt_val _ (by omega)]
      omega
    have hsub : int (((k + 1) * 64 : Nat) : Int) - int 64 = int ((k * 64 : Nat) : Int) := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    rw [frontWholeRegisters k (by omega)]
    exact frontCopyLoopYield 0 (int 65) (int 1)
      (int (((k + 1) * 64 : Nat) : Int), int 64, int ((k * 64 : Nat) : Int),
        int ((k * 64 + 1 : Nat) : Int), int (((k + 1) * 64 + 1 : Nat) : Int))
      (frontCopyRegisters (int 65) (int 1) (int 0))
      (dequeWordStore (frontWholeStage words (k + 1)) spare)
      (dequeWordStore (frontWholeStage words k) spare)
      (dequeWordStore (frontWholeStage words 0) spare) hpos hb
      (by simpa only [hsub] using ht)

/-- The exact public preservation copier shifts any native number of full chunks right by one word. -/
theorem frontWholeCopyRun (words : List U64) (spare : Nat)
    (hn : (words.length + 1) * 64 ≤ 9223372036854775807) :
    (copyChunks 0 (int 65) 0 (int 1) (int ((words.length * 64 : Nat) : Int))).run
      (dequeWordStore (words ++ [u64 0]) spare) =
        (.ok (), dequeWordStore (words.headD (u64 0) :: words) spare) := by
  have hlo := frontWholeLoopRun words words.length spare (Nat.le_refl _) hn
  rw [frontWholeStageInitial, frontWholeStageFinal] at hlo
  have hr := frontCopyRtolFromLoop 0 (int 65) (int 1) (int ((words.length * 64 : Nat) : Int))
    (dequeWordStore (words ++ [u64 0]) spare) (dequeWordStore (words.headD (u64 0) :: words) spare)
    (frontCopyRegisters (int 65) (int 1) (int 0)) (by decide) (by decide) hlo
  by_cases hp : 0 < words.length
  · simp only [copyChunks, fillPositiveLength (words.length * 64) (by omega) (by omega),
      Bool.false_eq_true, ite_false, show (0 = (0 : Nat) ∧ int 65 > int 1) from by decide, dite_true]
    exact hr
  · have he : words = [] := List.length_eq_zero_iff.mp (by omega)
    subst words
    exact rangeSingleCopyEmptyRun 0 _ _ _

/-- The first packed word is the first encoding entry, with the zero default for an empty input. -/
theorem frontWholeEncodingHead (xs : List Bool) :
    (encodeBits xs).headD (u64 0) = packedPrefix xs 0 64 := by
  have hh : (encodeBits xs).headD (u64 0) = (encodeBits xs).getD 0 (u64 0) := by
    cases encodeBits xs <;> rfl
  rw [hh]
  by_cases hp : 0 < xs.length
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [packedEncoded_length]; unfold wordCount; omega), Option.getD_some]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  · have he : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact (dequePackedBeyond [] 0 (by simp)).symm

/-- Prepending one complete retained word shifts every original chunk exactly one place. -/
theorem frontWholeEncoding (xs : List Bool) :
    encodeBits (resizeFrontSingleBits xs 64) = (encodeBits xs).headD (u64 0) :: encodeBits xs := by
  have hfirst : packedPrefix (resizeFrontSingleBits xs 64) 0 64 = packedPrefix xs 0 64 := by
    apply packedBit_ext
    intro bit hb
    rw [packedWord_bit _ _ bit hb, packedWord_bit _ _ bit hb]
    simp only [Nat.zero_mul, Nat.zero_add, resizeFrontSingleGet, hb, ite_true]
  have hlater (k : Nat) : packedPrefix (resizeFrontSingleBits xs 64) (k + 1) 64 = packedPrefix xs k 64 := by
    apply packedBit_ext
    intro bit hb
    rw [packedWord_bit _ _ bit hb, packedWord_bit _ _ bit hb, resizeFrontSingleGet,
      if_neg (by omega), show (k + 1) * 64 + bit - 64 = k * 64 + bit by omega]
  apply List.ext_getElem
  · simp only [packedEncoded_length, resizeFrontSingleLength, List.length_cons]
    unfold wordCount
    omega
  · intro i hi hi'
    cases i with
    | zero =>
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range,
        List.getElem_cons_zero]
      exact hfirst.trans (frontWholeEncodingHead xs).symm
    | succ k =>
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range,
        List.getElem_cons_succ]
      exact hlater k

/-- A word-aligned logical vector occupies exactly its length divided by sixty-four chunks. -/
theorem frontWholePackedLength (xs : List Bool) (hm : xs.length % 64 = 0) :
    (encodeBits xs).length * 64 = xs.length := by
  rw [packedEncoded_length]
  unfold wordCount
  omega

/-- Front growth by one complete word has exact canonical packed output at every supported aligned length. -/
theorem resizeFrontWholeRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hm : xs.length % 64 = 0) (hn : xs.length + 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + 64 : Nat) : Int))) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
      (initWords (encodeBits xs)) =
        (.ok {vectorBits xs with len := int ((xs.length + 64 : Nat) : Int)},
          dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) 31) := by
  let words := encodeBits xs
  let n := xs.length + 64
  have hp : words.length * 64 = xs.length := frontWholePackedLength xs hm
  have hb : (words.length + 1) * 64 ≤ 9223372036854775807 := by omega
  have hcount : wordCount n = words.length + 1 := by
    dsimp only [n, words]
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hnum : numBitChunks (int n) = int ((words.length + 1 : Nat) : Int) := by
    rw [resizeNumChunks n hn, hcount]
  have hzero : ¬ int n < int 0 := by
    change ¬ (int n).val < 0
    rw [packedInt_val n hn]
    omega
  have hlt : (vectorBits xs).len < int n := by
    change (int xs.length).val < (int n).val
    rw [packedInt_val xs.length (by omega), packedInt_val n hn]
    dsimp only [n]
    omega
  have hmore : int ((words.length + 1 : Nat) : Int) > int words.length := by
    change (int words.length).val < (int ((words.length + 1 : Nat) : Int)).val
    rw [packedInt_val words.length (by omega), packedInt_val (words.length + 1) (by omega)]
    omega
  have hdiff : int ((words.length + 1 : Nat) : Int) - int words.length = int 1 := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hg : ((if numBitChunks (int n) > int words.length then do
      growChunkVector 0 (numBitChunks (int n) - int words.length)
      mutableSet 0 (u64 0) (← mutableLength 0)
    else pure ()) : BitMutationM Unit).run (dequeWordStore words 32) =
      (.ok (), dequeWordStore (words ++ [u64 0]) 31) := by
    rw [hnum, if_pos hmore, hdiff]
    exact dequeGrowZeroRun words 31 (by omega)
  have hdest : int 1 + int n - (vectorBits xs).len = int 65 := by
    change int 1 + int n - int xs.length = int 65
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [n]
    omega
  have hcopy : (copyChunks 0 (int 1 + int n - (vectorBits xs).len) 0 (int 1) (vectorBits xs).len).run
      (dequeWordStore (words ++ [u64 0]) 31) =
        (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) 31) := by
    rw [hdest]
    change (copyChunks 0 (int 65) 0 (int 1) (int xs.length)).run _ = _
    have h := frontWholeCopyRun words 31 hb
    rw [hp] at h
    exact h.trans (by rw [frontWholeEncoding])
  rw [← dequeWordStoreInitial]
  exact resizeFrontSinglePublicGrowFrom (vectorBits xs) requested (int n) (int words.length)
    (dequeWordStore words 32) (dequeWordStore (words ++ [u64 0]) 31) _ hc hzero hlt
    (dequeWordLength words 32) hg hcopy

/-- Every aligned growth by sixty-four bits preserves the full original suffix and packed padding. -/
theorem resizeFrontWholeSuccess {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hm : xs.length % 64 = 0) (hn : xs.length + 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + 64 : Nat) : Int))) :
    resizeFrontSingleSuccessAt xs requested (xs.length + 64) := by
  let ys := resizeFrontSingleBits xs 64
  let B' : BitArray 1 := {vectorBits xs with len := int ((xs.length + 64 : Nat) : Int)}
  let out := dequeWordStore (encodeBits ys) 31
  have hlen : ys.length = xs.length + 64 := by rw [resizeFrontSingleLength]; omega
  have hy : ys.length ≤ 9223372036854775807 := by rw [hlen]; exact hn
  have hl : B'.len = int ys.length := by change int ((xs.length + 64 : Nat) : Int) = _; rw [hlen]
  have hcontents : out.contents B'.chunks = (encodeBits ys).map some :=
    dequeWordContents _ _ (packedEncoded_lengthBound ys hy)
  have hv := scalar_bitValues_contents out B' ys hy hl hcontents
  refine ⟨B', out, resizeFrontWholeRun xs requested hm hn hc, rfl, ?_,
    scalar_invariant_of_contents out B' ys hy hl hcontents⟩
  rw [if_neg (by omega), show xs.length + 64 - xs.length = 64 by omega, hv]
  exact (resizeFrontSingleSuffix xs 64).symm

/-- All installed conversion outcomes satisfy the frozen front-resize observation when successful conversion requests this aligned word growth. -/
theorem resizeFrontWholeCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hm : xs.length % 64 = 0) (hn : xs.length + 64 ≤ 9223372036854775807)
    (hrequested : ∀ n : I64, JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n →
      n = int ((xs.length + 64 : Nat) : Int)) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) := by
  apply resizeFrontSingleFromNatural xs requested
  intro n hbound hc
  have hn' : n ≤ 9223372036854775807 := by
    change n < 4611686018427387903 at hbound
    omega
  have he := congrArg Subtype.val (hrequested (int n) hc)
  rw [packedInt_val n hn', packedInt_val (xs.length + 64) hn] at he
  have hnEq : n = xs.length + 64 := by omega
  subst n
  exact resizeFrontWholeSuccess xs requested hm hn hc
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- The temporary boundary word retains its old low added bits and shifts the rest upward. -/
def frontBlockPartial (word : U64) (added : Nat) : U64 :=
  copyPairPaste word word added (64 - added)

/-- A completed interior word combines the shifted current word with its predecessor's carry. -/
def frontBlockCarry (current previous : U64) (added : Nat) : U64 :=
  or_int (shl_int current (int added)) (lshr_int previous (int ((64 - added : Nat) : Int)))

/-- Descending front growth has one partial boundary between untouched and completed words. -/
def frontBlockStage (words : List U64) (added remaining : Nat) : List U64 :=
  (List.range (words.length + 1)).map fun i =>
    if i < remaining then words.getD i (u64 0)
    else if i = remaining then frontBlockPartial (words.getD i (u64 0)) added
    else frontBlockCarry (words.getD i (u64 0)) (words.getD (i - 1) (u64 0)) added
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The partial boundary retains its low new bits and shifts its original bits upward. -/
theorem frontBlockPartialBit (word : U64) (added bit : Nat)
    (ha : added ≤ 64) (hb : bit < 64) :
    packedBit (frontBlockPartial word added) bit =
      if bit < added then packedBit word bit else packedBit word (bit - added) := by
  rw [frontBlockPartial, copyPairPasteBit _ _ added (64 - added) bit (by omega) hb]
  by_cases hi : bit < added
  · rw [if_pos hi, if_neg (by omega)]
  · rw [if_neg hi, if_pos (by omega)]

/-- Carry assembly selects either low predecessor carry bits or shifted current bits. -/
theorem frontBlockCarryBit (current previous : U64) (added bit : Nat)
    (ha : added ≤ 64) (hb : bit < 64) :
    packedBit (frontBlockCarry current previous added) bit =
      if bit < added then packedBit previous (bit + (64 - added))
      else packedBit current (bit - added) := by
  rw [frontBlockCarry, packedBit_or, reversePackedLeft _ added bit ha hb,
    copyPairRightBit _ (64 - added) bit (by omega) hb]
  by_cases hi : bit < added
  · rw [if_pos hi, if_neg (by omega), if_pos (by omega), Bool.false_or]
  · rw [if_neg hi, if_pos (by omega), if_neg (by omega), Bool.or_false]

theorem frontBlockPartialZero (added : Nat) (ha : added ≤ 64) :
    frontBlockPartial (u64 0) added = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [frontBlockPartialBit _ added bit ha hb]
  split <;> simp only [packedBit_zero]

/-- Filling the boundary's low carry bits completes that word without disturbing its shifted higher bits. -/
theorem frontBlockPasteCarry (current previous : U64) (added : Nat) (ha : added ≤ 64) :
    copyPairPaste (frontBlockPartial current added)
      (lshr_int previous (int ((64 - added : Nat) : Int))) 0 added =
        frontBlockCarry current previous added := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 added bit (by omega) hb, frontBlockCarryBit _ _ added bit ha hb]
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  by_cases hi : bit < added
  · rw [if_pos hi, if_pos hi, copyPairRightBit _ (64 - added) bit (by omega) hb, if_pos (by omega)]
  · rw [if_neg hi, if_neg hi, frontBlockPartialBit _ added bit ha hb, if_neg hi]

theorem frontBlockStageLength (words : List U64) (added remaining : Nat) :
    (frontBlockStage words added remaining).length = words.length + 1 := by
  simp only [frontBlockStage, List.length_map, List.length_range]

theorem frontBlockStageGet (words : List U64) (added remaining i : Nat)
    (hi : i < words.length + 1) :
    (frontBlockStage words added remaining).getD i (u64 0) =
      if i < remaining then words.getD i (u64 0)
      else if i = remaining then frontBlockPartial (words.getD i (u64 0)) added
      else frontBlockCarry (words.getD i (u64 0)) (words.getD (i - 1) (u64 0)) added := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [frontBlockStageLength]; exact hi), Option.getD_some]
  simp only [frontBlockStage, List.getElem_map, List.getElem_range]

/-- Initializing the extra last word gives precisely the initial descending carry stage. -/
theorem frontBlockStageInitial (words : List U64) (added : Nat) (ha : added ≤ 64) :
    frontBlockStage words added words.length = words ++ [u64 0] := by
  apply List.ext_getElem
  · simp only [frontBlockStageLength, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  · intro i hi hi'
    have hb : i < words.length + 1 := by simpa only [frontBlockStageLength] using hi
    rw [List.getElem_eq_getD (fallback := u64 0), frontBlockStageGet words added words.length i hb,
      List.getElem_eq_getD (fallback := u64 0)]
    by_cases hlt : i < words.length
    · simp only [hlt, ite_true, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    · have he : i = words.length := by omega
      subst i
      simp only [Nat.lt_irrefl, ite_false, ite_true, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (Nat.le_refl _), Option.getD_none,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some, frontBlockPartialZero added ha]

/-- The low write followed by the high carry write advances exactly one descending stage. -/
theorem frontBlockStageStep (words : List U64) (added k : Nat) (hk : k < words.length) :
    ((frontBlockStage words added (k + 1)).set k (frontBlockPartial (words.getD k (u64 0)) added)).set
      (k + 1) (frontBlockCarry (words.getD (k + 1) (u64 0)) (words.getD k (u64 0)) added) =
        frontBlockStage words added k := by
  apply List.ext_getElem
  · simp only [List.length_set, frontBlockStageLength]
  · intro i hi hi'
    have hb : i < words.length + 1 := by simpa only [frontBlockStageLength] using hi'
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ (k + 1) i _ (by rw [List.length_set, frontBlockStageLength]; omega),
      List.getElem_eq_getD (fallback := u64 0), frontBlockStageGet words added k i hb]
    by_cases he : k + 1 = i
    · subst i
      rw [if_pos rfl, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    · rw [if_neg he, dequeWordGetSet _ k i _ (by rw [frontBlockStageLength]; omega)]
      by_cases he0 : k = i
      · subst i
        rw [if_pos rfl, if_neg (Nat.lt_irrefl _), if_pos rfl]
      · rw [if_neg he0, frontBlockStageGet words added (k + 1) i hb]
        by_cases hlt : i < k
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega), if_neg (Ne.symm he0), if_neg (Ne.symm he)]

/-- Out-of-range packed chunks agree with the encoding's zero fallback. -/
theorem frontBlockEncodedGet (xs : List Bool) (chunk : Nat) :
    (encodeBits xs).getD chunk (u64 0) = packedPrefix xs chunk 64 := by
  by_cases hi : chunk < (encodeBits xs).length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  · have hbound : xs.length ≤ chunk * 64 := by
      rw [packedEncoded_length] at hi
      unfold wordCount at hi
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    exact (dequePackedBeyond xs chunk hbound).symm

/-- Completing every aligned source block yields the exact retained-prefix and original-suffix encoding. -/
theorem frontBlockStageEncoding (xs : List Bool) (added : Nat)
    (hm : xs.length % 64 = 0) (ha : 0 < added) (hb : added ≤ 64) :
    frontBlockStage (encodeBits xs) added 0 = encodeBits (resizeFrontSingleBits xs added) := by
  apply List.ext_getElem
  · rw [frontBlockStageLength, packedEncoded_length, packedEncoded_length, resizeFrontSingleLength]
    unfold wordCount
    omega
  · intro chunk hc hc'
    have hchunk : chunk < (encodeBits xs).length + 1 := by simpa only [frontBlockStageLength] using hc
    rw [List.getElem_eq_getD (fallback := u64 0), frontBlockStageGet _ added 0 chunk hchunk]
    have he : (encodeBits (resizeFrontSingleBits xs added))[chunk] =
        packedPrefix (resizeFrontSingleBits xs added) chunk 64 := by
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rw [he]
    by_cases hz : chunk = 0
    · subst chunk
      rw [if_neg (Nat.lt_irrefl _), if_pos rfl, frontBlockEncodedGet]
      apply packedBit_ext
      intro bit hbit
      rw [frontBlockPartialBit _ added bit hb hbit, packedWord_bit (resizeFrontSingleBits xs added) 0 bit hbit]
      simp only [Nat.zero_mul, Nat.zero_add, resizeFrontSingleGet]
      split
      · rw [packedWord_bit _ _ bit hbit]
        simp only [Nat.zero_mul, Nat.zero_add]
      · rw [packedWord_bit _ _ (bit - added) (by omega)]
        simp only [Nat.zero_mul, Nat.zero_add]
    · rw [if_neg (Nat.not_lt_zero _), if_neg hz, frontBlockEncodedGet, frontBlockEncodedGet]
      apply packedBit_ext
      intro bit hbit
      rw [frontBlockCarryBit _ _ added bit hb hbit,
        packedWord_bit (resizeFrontSingleBits xs added) chunk bit hbit,
        resizeFrontSingleGet, if_neg (show ¬ chunk * 64 + bit < added by omega)]
      by_cases hlow : bit < added
      · rw [if_pos hlow, packedWord_bit xs (chunk - 1) (bit + (64 - added)) (by omega)]
        congr 1
        omega
      · rw [if_neg hlow, packedWord_bit xs chunk (bit - added) (by omega)]
        congr 1
        omega
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

/-- A block spanning the destination boundary performs its low write before its high write. -/
theorem frontBlockTwoFrom (chunks : Nat) (pd ps : I64) (count offset lastCount : Nat)
    (kd0 kd1 ks0 ls0 ks1 ls1 : I64) (s mid out : State) (low high gathered aligned : U64)
    (ho : offset ≤ 64) (hp : 0 < lastCount) (hn : lastCount ≤ 64)
    (hdiff : kd1 - kd0 = int 1)
    (hd0 : getChunksId pd = (kd0, int offset))
    (hd1 : getChunksId (pd + int count - int 1) = (kd1, int ((lastCount - 1 : Nat) : Int)))
    (hs0 : getChunksId ps = (ks0, ls0))
    (hs1 : getChunksId (ps + int count - int 1) = (ks1, ls1))
    (hg : (glueSrcBitChunks chunks ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run s =
      (.ok gathered, s))
    (hclip : and_int gathered (not_int (shl_int u64Max (int count))) = aligned)
    (hr0 : (mutableGet chunks kd0).run s = (.ok low, s))
    (hw0 : (mutableSet chunks (copyPairPaste low aligned offset (64 - offset)) kd0).run s =
      (.ok (), mid))
    (hr1 : (mutableGet chunks kd1).run mid = (.ok high, mid))
    (hw1 : (mutableSet chunks (copyPairPaste high
      (lshr_int aligned (int ((64 - offset : Nat) : Int))) 0 lastCount) kd1).run mid =
      (.ok (), out)) :
    (frontCopyBlock chunks pd ps (int count)).run s = (.ok (), out) := by
  have hinc : int ((lastCount - 1 : Nat) : Int) + int 1 = int lastCount := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hsub : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  simp only [copyPairPaste, copyPairKeepHigh offset ho] at hw0
  simp only [copyPairPaste, copyPairKeepLow lastCount hn] at hw1
  have hshift (w : U64) : shl_int w (int (0 : Nat)) = w := by
    apply packedBit_ext
    intro bit hb
    rw [reversePackedLeft w 0 bit (by decide) hb]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  rw [hshift] at hw1
  simp only [frontCopyBlock, hd0, hd1, hs0, hs1, hinc,
    hdiff,
    show (int 1 == int 0) = false from rfl,
    show (int 1 != int 0) = true from rfl,
    Bool.false_eq_true, ite_false, ite_true, hsub]
  by_cases hsame : (ks1 - ks0 == int 0) = true
  all_goals
    simp only [copyPairSourceMask, hsame, Bool.false_eq_true, ite_true, ite_false] at hg ⊢
    simp only [shape_run_bind, hg, hclip, hr0, hw0, hr1, hw1, shape_run_pure]

/-- A block offset strictly inside a word has its corresponding native chunk address. -/
theorem frontBlockAddress (chunk bit : Nat) (hb : bit < 64)
    (hn : chunk * 64 + bit + 1 ≤ 9223372036854775807) :
    getChunksId (int ((chunk * 64 + bit + 1 : Nat) : Int)) =
      (int ((chunk + 1 : Nat) : Int), int bit) := by
  have h := scalar_chunks_nat (chunk * 64 + bit) hn
  have hq : (chunk * 64 + bit) / 64 = chunk := by omega
  have hm : (chunk * 64 + bit) % 64 = bit := by omega
  simpa only [hq, hm] using h

/-- A shifted full block ends in the following destination chunk. -/
theorem frontBlockEndAddress (chunk added : Nat) (ha : 0 < added) (hb : added < 64)
    (hn : (chunk + 2) * 64 ≤ 9223372036854775807) :
    getChunksId (int ((chunk * 64 + added + 1 : Nat) : Int) + int 64 - int 1) =
      (int ((chunk + 2 : Nat) : Int), int ((added - 1 : Nat) : Int)) := by
  have he : int ((chunk * 64 + added + 1 : Nat) : Int) + int 64 - int 1 =
      int (((chunk + 1) * 64 + (added - 1) + 1 : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    exact congrArg int (by omega)
  rw [he]
  exact frontBlockAddress (chunk + 1) (added - 1) (by omega) (by omega)

/-- One descending full-source block advances the partial boundary and finishes its next word. -/
theorem frontBlockRun (words : List U64) (added k spare : Nat)
    (ha : 0 < added) (hb : added < 64) (hk : k < words.length)
    (hn : (words.length + 1) * 64 ≤ 9223372036854775807) :
    (frontCopyBlock 0 (int ((k * 64 + added + 1 : Nat) : Int))
      (int ((k * 64 + 1 : Nat) : Int)) (int 64)).run
      (dequeWordStore (frontBlockStage words added (k + 1)) spare) =
        (.ok (), dequeWordStore (frontBlockStage words added k) spare) := by
  let stage := frontBlockStage words added (k + 1)
  let low := frontBlockPartial (words.getD k (u64 0)) added
  let middleWords := stage.set k low
  let middle := dequeWordStore middleWords spare
  have hlen : stage.length = words.length + 1 := frontBlockStageLength _ _ _
  have hmidlen : middleWords.length = words.length + 1 := by rw [List.length_set]; exact hlen
  have hr0 := dequeWordRead stage spare k (by omega) (by omega)
  have hsource : stage.getD k (u64 0) = words.getD k (u64 0) := by
    rw [frontBlockStageGet words added (k + 1) k (by omega), if_pos (by omega)]
  rw [hsource] at hr0
  have hw0 := dequeWordSet stage spare k low (by omega) (by omega)
  have hr1 := dequeWordRead middleWords spare (k + 1) (by omega) (by omega)
  have hboundary : middleWords.getD (k + 1) (u64 0) =
      frontBlockPartial (words.getD (k + 1) (u64 0)) added := by
    rw [dequeWordGetSet stage k (k + 1) low (by omega), if_neg (by omega),
      frontBlockStageGet words added (k + 1) (k + 1) (by omega),
      if_neg (Nat.lt_irrefl _), if_pos rfl]
  rw [hboundary] at hr1
  have hw1 := dequeWordSet middleWords spare (k + 1)
    (frontBlockCarry (words.getD (k + 1) (u64 0)) (words.getD k (u64 0)) added)
    (by omega) (by omega)
  have hstep : middleWords.set (k + 1)
      (frontBlockCarry (words.getD (k + 1) (u64 0)) (words.getD k (u64 0)) added) =
        frontBlockStage words added k := frontBlockStageStep words added k hk
  rw [hstep] at hw1
  have hdiff : int ((k + 2 : Nat) : Int) - int ((k + 1 : Nat) : Int) = int 1 := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  exact frontBlockTwoFrom 0 _ _ 64 added added
    (int ((k + 1 : Nat) : Int)) (int ((k + 2 : Nat) : Int))
    (int ((k + 1 : Nat) : Int)) (int 0) (int ((k + 1 : Nat) : Int)) (int 63)
    (dequeWordStore stage spare) middle (dequeWordStore (frontBlockStage words added k) spare)
    (words.getD k (u64 0)) (frontBlockPartial (words.getD (k + 1) (u64 0)) added)
    (words.getD k (u64 0)) (words.getD k (u64 0)) (by omega) ha (by omega) hdiff
    (frontBlockAddress k added hb (by omega)) (frontBlockEndAddress k added ha hb (by omega))
    (frontWholeAddress k (by omega)) (frontWholeEndAddress k (by omega))
    (frontWholeGather 0 _ _ _ hr0) (resizeFrontPairClipFull _) hr0 hw0 hr1
    (by rw [frontBlockPasteCarry _ _ added (by omega)]; exact hw1)

/-- Full source blocks have direct aligned source positions and a fixed destination offset. -/
theorem frontBlockRegisters (added k : Nat) (hn : (k + 1) * 64 ≤ 9223372036854775807) :
    frontCopyRegisters (int ((added + 1 : Nat) : Int)) (int 1) (int (((k + 1) * 64 : Nat) : Int)) =
      (int (((k + 1) * 64 : Nat) : Int), int 64, int ((k * 64 : Nat) : Int),
        int ((k * 64 + 1 : Nat) : Int), int ((k * 64 + added + 1 : Nat) : Int)) := by
  have hs : ¬ int (((k + 1) * 64 : Nat) : Int) < int 64 := by
    change ¬ (int (((k + 1) * 64 : Nat) : Int)).val < 64
    rw [packedInt_val _ hn]
    omega
  have hd : int (((k + 1) * 64 : Nat) : Int) - int 64 = int ((k * 64 : Nat) : Int) := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hsource : int 1 + int ((k * 64 : Nat) : Int) = int ((k * 64 + 1 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  have hdest : int ((added + 1 : Nat) : Int) + int ((k * 64 : Nat) : Int) =
      int ((k * 64 + added + 1 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  simp only [frontCopyRegisters, hs, ite_false, hd, hsource, hdest]

/-- Every descending full source block is verified at arbitrary original chunk count. -/
theorem frontBlockLoopRun (words : List U64) (added remaining spare : Nat)
    (ha : 0 < added) (hb : added < 64) (hr : remaining ≤ words.length)
    (hn : (words.length + 1) * 64 ≤ 9223372036854775807) :
    (frontCopyLoop 0 (int ((added + 1 : Nat) : Int)) (int 1)
      (frontCopyRegisters (int ((added + 1 : Nat) : Int)) (int 1) (int ((remaining * 64 : Nat) : Int)))).run
      (dequeWordStore (frontBlockStage words added remaining) spare) =
        (.ok (frontCopyRegisters (int ((added + 1 : Nat) : Int)) (int 1) (int 0)),
          dequeWordStore (frontBlockStage words added 0) spare) := by
  induction remaining with
  | zero =>
    exact frontCopyLoopDone 0 (int ((added + 1 : Nat) : Int)) (int 1)
      (frontCopyRegisters (int ((added + 1 : Nat) : Int)) (int 1) (int 0))
      (dequeWordStore (frontBlockStage words added 0) spare) (by change ¬ int 0 > int 0; decide)
  | succ k ih =>
    have hblock := frontBlockRun words added k spare ha hb (by omega) hn
    have ht := ih (by omega)
    have hpos : int (((k + 1) * 64 : Nat) : Int) > int 0 := by
      change 0 < (int (((k + 1) * 64 : Nat) : Int)).val
      rw [packedInt_val _ (by omega)]
      omega
    have hsub : int (((k + 1) * 64 : Nat) : Int) - int 64 = int ((k * 64 : Nat) : Int) := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    rw [frontBlockRegisters added k (by omega)]
    exact frontCopyLoopYield 0 (int ((added + 1 : Nat) : Int)) (int 1)
      (int (((k + 1) * 64 : Nat) : Int), int 64, int ((k * 64 : Nat) : Int),
        int ((k * 64 + 1 : Nat) : Int), int ((k * 64 + added + 1 : Nat) : Int))
      (frontCopyRegisters (int ((added + 1 : Nat) : Int)) (int 1) (int 0))
      (dequeWordStore (frontBlockStage words added (k + 1)) spare)
      (dequeWordStore (frontBlockStage words added k) spare)
      (dequeWordStore (frontBlockStage words added 0) spare) hpos hblock
      (by simpa only [hsub] using ht)

/-- A positive shift smaller than one word moves any number of complete source chunks correctly. -/
theorem frontBlockCopyRun (words : List U64) (added spare : Nat)
    (ha : 0 < added) (hb : added < 64)
    (hn : (words.length + 1) * 64 ≤ 9223372036854775807) :
    (copyChunks 0 (int ((added + 1 : Nat) : Int)) 0 (int 1) (int ((words.length * 64 : Nat) : Int))).run
      (dequeWordStore (words ++ [u64 0]) spare) =
        (.ok (), dequeWordStore (frontBlockStage words added 0) spare) := by
  have hlo := frontBlockLoopRun words added words.length spare ha hb (Nat.le_refl _) hn
  rw [frontBlockStageInitial words added (by omega)] at hlo
  have hval : (int ((added + 1 : Nat) : Int)).val = ((added + 1 : Nat) : Int) :=
    packedInt_val _ (by omega)
  have hne : (int ((added + 1 : Nat) : Int) == int 1) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [hval] at hv
    change ((added + 1 : Nat) : Int) = 1 at hv
    omega
  have hord : ¬ int ((added + 1 : Nat) : Int) < int 1 := by
    change ¬ (int ((added + 1 : Nat) : Int)).val < 1
    rw [hval]
    omega
  have hgt : int ((added + 1 : Nat) : Int) > int 1 := by
    change 1 < (int ((added + 1 : Nat) : Int)).val
    rw [hval]
    omega
  have hr := frontCopyRtolFromLoop 0 (int ((added + 1 : Nat) : Int)) (int 1)
    (int ((words.length * 64 : Nat) : Int))
    (dequeWordStore (words ++ [u64 0]) spare) (dequeWordStore (frontBlockStage words added 0) spare)
    (frontCopyRegisters (int ((added + 1 : Nat) : Int)) (int 1) (int 0)) hne hord hlo
  by_cases hp : 0 < words.length
  · simp only [copyChunks, fillPositiveLength (words.length * 64) (by omega) (by omega),
      Bool.false_eq_true, ite_false, hgt, and_self, dite_true]
    exact hr
  · have he : words = [] := List.length_eq_zero_iff.mp (by omega)
    subst words
    have hstage := frontBlockStageInitial [] added (by omega)
    simp only [List.length_nil, List.nil_append] at hstage
    rw [hstage]
    exact rangeSingleCopyEmptyRun 0 _ _ _

/-- Front growth by a positive partial word has exact canonical packed output at every supported aligned length. -/
theorem resizeFrontBlockSmallRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (added : Nat)
    (ha : 0 < added) (hab : added < 64)
    (hm : xs.length % 64 = 0) (hn : xs.length + 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + added : Nat) : Int))) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
      (initWords (encodeBits xs)) =
        (.ok {vectorBits xs with len := int ((xs.length + added : Nat) : Int)},
          dequeWordStore (encodeBits (resizeFrontSingleBits xs added)) 31) := by
  let words := encodeBits xs
  let n := xs.length + added
  have hnb : n ≤ 9223372036854775807 := by dsimp only [n]; omega
  have hp : words.length * 64 = xs.length := frontWholePackedLength xs hm
  have hb : (words.length + 1) * 64 ≤ 9223372036854775807 := by omega
  have hcount : wordCount n = words.length + 1 := by
    dsimp only [n, words]
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hnum : numBitChunks (int n) = int ((words.length + 1 : Nat) : Int) := by
    rw [resizeNumChunks n hnb, hcount]
  have hzero : ¬ int n < int 0 := by
    change ¬ (int n).val < 0
    rw [packedInt_val n hnb]
    omega
  have hlt : (vectorBits xs).len < int n := by
    change (int xs.length).val < (int n).val
    rw [packedInt_val xs.length (by omega), packedInt_val n hnb]
    dsimp only [n]
    omega
  have hmore : int ((words.length + 1 : Nat) : Int) > int words.length := by
    change (int words.length).val < (int ((words.length + 1 : Nat) : Int)).val
    rw [packedInt_val words.length (by omega), packedInt_val (words.length + 1) (by omega)]
    omega
  have hdiff : int ((words.length + 1 : Nat) : Int) - int words.length = int 1 := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hg : ((if numBitChunks (int n) > int words.length then do
      growChunkVector 0 (numBitChunks (int n) - int words.length)
      mutableSet 0 (u64 0) (← mutableLength 0)
    else pure ()) : BitMutationM Unit).run (dequeWordStore words 32) =
      (.ok (), dequeWordStore (words ++ [u64 0]) 31) := by
    rw [hnum, if_pos hmore, hdiff]
    exact dequeGrowZeroRun words 31 (by omega)
  have hdest : int 1 + int n - (vectorBits xs).len = int ((added + 1 : Nat) : Int) := by
    change int 1 + int n - int xs.length = int ((added + 1 : Nat) : Int)
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [n]
    omega
  have hcopy : (copyChunks 0 (int 1 + int n - (vectorBits xs).len) 0 (int 1) (vectorBits xs).len).run
      (dequeWordStore (words ++ [u64 0]) 31) =
        (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs added)) 31) := by
    rw [hdest]
    change (copyChunks 0 (int ((added + 1 : Nat) : Int)) 0 (int 1) (int xs.length)).run _ = _
    have h := frontBlockCopyRun words added 31 ha hab hb
    rw [hp] at h
    exact h.trans (by rw [frontBlockStageEncoding xs added hm ha (by omega)])
  rw [← dequeWordStoreInitial]
  exact resizeFrontSinglePublicGrowFrom (vectorBits xs) requested (int n) (int words.length)
    (dequeWordStore words 32) (dequeWordStore (words ++ [u64 0]) 31) _ hc hzero hlt
    (dequeWordLength words 32) hg hcopy

/-- Every aligned growth by fewer than sixty-four bits preserves the full original suffix and packed padding. -/
theorem resizeFrontBlockSmallSuccess {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (added : Nat)
    (ha : 0 < added) (hab : added < 64)
    (hm : xs.length % 64 = 0) (hn : xs.length + 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + added : Nat) : Int))) :
    resizeFrontSingleSuccessAt xs requested (xs.length + added) := by
  let ys := resizeFrontSingleBits xs added
  let B' : BitArray 1 := {vectorBits xs with len := int ((xs.length + added : Nat) : Int)}
  let out := dequeWordStore (encodeBits ys) 31
  have hlen : ys.length = xs.length + added := by rw [resizeFrontSingleLength]; omega
  have hy : ys.length ≤ 9223372036854775807 := by rw [hlen]; omega
  have hl : B'.len = int ys.length := by change int ((xs.length + added : Nat) : Int) = _; rw [hlen]
  have hcontents : out.contents B'.chunks = (encodeBits ys).map some :=
    dequeWordContents _ _ (packedEncoded_lengthBound ys hy)
  have hv := scalar_bitValues_contents out B' ys hy hl hcontents
  refine ⟨B', out, resizeFrontBlockSmallRun xs requested added ha hab hm hn hc, rfl, ?_,
    scalar_invariant_of_contents out B' ys hy hl hcontents⟩
  rw [if_neg (by omega), show xs.length + added - xs.length = added by omega, hv]
  exact (resizeFrontSingleSuffix xs added).symm

/-- All installed conversion outcomes satisfy the frozen front-resize observation when successful conversion requests this aligned partial-word growth. -/
theorem resizeFrontBlockSmallCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (added : Nat)
    (ha : 0 < added) (hab : added < 64)
    (hm : xs.length % 64 = 0) (hn : xs.length + 64 ≤ 9223372036854775807)
    (hrequested : ∀ n : I64, JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n →
      n = int ((xs.length + added : Nat) : Int)) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) := by
  apply resizeFrontSingleFromNatural xs requested
  intro n hbound hc
  have hn' : n ≤ 9223372036854775807 := by
    change n < 4611686018427387903 at hbound
    omega
  have he := congrArg Subtype.val (hrequested (int n) hc)
  rw [packedInt_val n hn', packedInt_val (xs.length + added) (by omega)] at he
  have hnEq : n = xs.length + added := by omega
  subst n
  exact resizeFrontBlockSmallSuccess xs requested added ha hab hm hn hc


/-- Front growth by any number of bits up to one complete word is correct at every aligned original length. -/
theorem resizeFrontAlignedSuccess {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (added : Nat)
    (hm : xs.length % 64 = 0) (ha : added ≤ 64)
    (hn : xs.length + 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + added : Nat) : Int))) :
    resizeFrontSingleSuccessAt xs requested (xs.length + added) := by
  by_cases hz : added = 0
  · subst added
    simp only [Nat.add_zero] at hc ⊢
    exact resizeFrontSingleSameLength xs requested (by omega) hc
  · by_cases he : added = 64
    · subst added
      exact resizeFrontWholeSuccess xs requested hm hn hc
    · exact resizeFrontBlockSmallSuccess xs requested added (by omega) (by omega) hm hn hc

/-- Every installed conversion to a front-growth length within the next word satisfies the complete frozen observation. -/
theorem resizeFrontAlignedCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hm : xs.length % 64 = 0) (hx : xs.length < Round5.maxVectorLength)
    (hrequested : ∀ n : I64, JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n →
      xs.length ≤ n.val.toNat ∧ n.val.toNat ≤ xs.length + 64) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) := by
  have hn : xs.length + 64 ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hx
    omega
  apply resizeFrontSingleFromNatural xs requested
  intro n hbound hc
  have hn' : n ≤ 9223372036854775807 := by
    change n < 4611686018427387903 at hbound
    omega
  have hbetween := hrequested (int n) hc
  rw [packedInt_val n hn', Int.toNat_natCast] at hbetween
  have he : xs.length + (n - xs.length) = n := by omega
  have hc' : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + (n - xs.length) : Nat) : Int)) := by rw [he]; exact hc
  have h := resizeFrontAlignedSuccess xs requested (n - xs.length) hm (by omega) hn hc'
  rw [he] at h
  exact h

/-- A residue-restricted block invariant suffices: the loop visits only the original count modulo64, followed by zero. -/
theorem frontCopyLoopResidue (chunks : Nat) (posD posS : I64) (count : Nat)
    (stage : Nat → State) (hn : count ≤ 9223372036854775807)
    (hstep : ∀ left : Nat, 0 < left → left ≤ count → left % 64 = count % 64 →
      (frontCopyBlock chunks
        (posD + int ((left - min left 64 : Nat) : Int))
        (posS + int ((left - min left 64 : Nat) : Int)) (int ((min left 64 : Nat) : Int))).run
          (stage left) = (.ok (), stage (left - min left 64))) :
    (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (int count))).run
      (stage count) = (.ok (frontCopyRegisters posD posS (int 0)), stage 0) := by
  have hall : ∀ left : Nat, left ≤ count → (left = 0 ∨ left % 64 = count % 64) →
      (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (int left))).run
        (stage left) = (.ok (frontCopyRegisters posD posS (int 0)), stage 0) := by
    intro left
    induction left using Nat.strongRecOn with
    | ind left ih =>
      intro hl hres
      by_cases hz : left = 0
      · subst left
        exact frontCopyLoopDone chunks posD posS (frontCopyRegisters posD posS (int 0))
          (stage 0) (by change ¬ int 0 > int 0; decide)
      · have hp : 0 < left := by omega
        have hm : 0 < min left 64 := by omega
        have hsm : left - min left 64 < left := by omega
        have hr : left % 64 = count % 64 := by omega
        have hrnext : left - min left 64 = 0 ∨ (left - min left 64) % 64 = count % 64 := by omega
        have ht := ih (left - min left 64) hsm (by omega) hrnext
        have hpos : int left > int 0 := by
          change 0 < (int left).val
          rw [packedInt_val left (by omega)]
          omega
        have hd : int left - int ((min left 64 : Nat) : Int) = int ((left - min left 64 : Nat) : Int) := by
          rw [dequeIntSub]
          apply congrArg int
          have hm := Nat.min_le_left left 64
          omega
        rw [frontCopyRegistersNative posD posS left (by omega)]
        exact frontCopyLoopYield chunks posD posS
          (int left, int ((min left 64 : Nat) : Int), int ((left - min left 64 : Nat) : Int),
            posS + int ((left - min left 64 : Nat) : Int),
            posD + int ((left - min left 64 : Nat) : Int))
          (frontCopyRegisters posD posS (int 0))
          (stage left) (stage (left - min left 64)) (stage 0)
          hpos (hstep left hp hl hr) (by simpa only [hd] using ht)
  exact hall count (Nat.le_refl _) (Or.inr rfl)
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The moving boundary retains the low source remainder from its old word and receives the high bits of its predecessor. -/
def frontUnalignedStage (words : List U64) (remainder boundary : Nat) : List U64 :=
  (List.range (words.length + 1)).map fun i =>
    if i < boundary then words.getD i (u64 0)
    else if i = boundary then copyPairPaste (words.getD (i - 1) (u64 0)) (words.getD i (u64 0)) 0 remainder
    else words.getD (i - 1) (u64 0)

theorem frontUnalignedStageLength (words : List U64) (remainder boundary : Nat) :
    (frontUnalignedStage words remainder boundary).length = words.length + 1 := by
  simp only [frontUnalignedStage, List.length_map, List.length_range]

theorem frontUnalignedStageGet (words : List U64) (remainder boundary i : Nat)
    (hi : i < words.length + 1) :
    (frontUnalignedStage words remainder boundary).getD i (u64 0) =
      if i < boundary then words.getD i (u64 0)
      else if i = boundary then copyPairPaste (words.getD (i - 1) (u64 0)) (words.getD i (u64 0)) 0 remainder
      else words.getD (i - 1) (u64 0) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [frontUnalignedStageLength]; exact hi), Option.getD_some]
  simp only [frontUnalignedStage, List.getElem_map, List.getElem_range]

/-- The low write of a descending full block establishes the next mixed boundary word. -/
theorem frontUnalignedLowPaste (previous current : U64) (r : Nat) (hr : r < 64) :
    copyPairPaste current (copyPairGlue previous current r) r (64 - r) =
      copyPairPaste previous current 0 r := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ r (64-r) bit (by omega) hb,
    copyPairPasteBit _ _ 0 r bit (by omega) hb]
  by_cases hi : bit < r
  · simp only [show ¬(r ≤ bit ∧ bit < r + (64-r)) by omega, ite_false,
      show 0 ≤ bit ∧ bit < 0+r by omega, ite_true, and_self, Nat.sub_zero]
  · rw [if_pos (by omega), if_neg (by omega),
      copyPairGlueBit previous current r (bit-r) hr (by omega), if_pos (by omega),
      show bit-r+r=bit by omega]

/-- The high write restores the complete predecessor after its low bits arrive from the same gather. -/
theorem frontUnalignedHighPaste (previous current next : U64) (r : Nat) (hr : r < 64) :
    copyPairPaste (copyPairPaste current next 0 r)
      (lshr_int (copyPairGlue previous current r) (int ((64-r : Nat) : Int))) 0 r = current := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 r bit (by omega) hb]
  by_cases hi : bit < r
  · rw [if_pos (by omega), Nat.sub_zero, copyPairRightBit _ (64-r) bit (by omega) hb,
      if_pos (by omega), copyPairGlueBit previous current r (bit+(64-r)) hr (by omega),
      if_neg (by omega), show bit+(64-r)+r-64=bit by omega]
  · rw [if_neg (by omega), copyPairPasteBit current next 0 r bit (by omega) hb,
      if_neg (by omega)]

/-- The final partial block replaces the mixed boundary prefix and completes the original word. -/
theorem frontUnalignedFinalPaste (word next : U64) (r : Nat) (hr : r ≤ 64) :
    copyPairPaste (copyPairPaste word next 0 r) (resizeFrontPairClip word r) 0 r = word := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 r bit (by omega) hb]
  by_cases hi : bit < r
  · rw [if_pos (by omega), Nat.sub_zero, resizeFrontPairClipBit word r bit hr hb, if_pos hi]
  · rw [if_neg (by omega), copyPairPasteBit word next 0 r bit (by omega) hb, if_neg (by omega)]

/-- Two concrete word replacements advance the mixed boundary by one chunk. -/
theorem frontUnalignedStageStep (words : List U64) (r k : Nat)
    (hk : 0 < k) (hn : k < words.length) :
    ((frontUnalignedStage words r (k+1)).set k
      (copyPairPaste (words.getD (k-1) (u64 0)) (words.getD k (u64 0)) 0 r)).set (k+1)
        (words.getD k (u64 0)) = frontUnalignedStage words r k := by
  apply List.ext_getElem
  · simp only [List.length_set, frontUnalignedStageLength]
  · intro i hi hi'
    have hb : i < words.length+1 := by simpa only [frontUnalignedStageLength] using hi'
    rw [List.getElem_eq_getD (fallback := u64 0), dequeWordGetSet _ (k+1) i _
      (by rw [List.length_set, frontUnalignedStageLength]; omega),
      List.getElem_eq_getD (fallback := u64 0), frontUnalignedStageGet words r k i hb]
    by_cases he : k+1=i
    · subst i
      rw [if_pos rfl, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    · rw [if_neg he, dequeWordGetSet _ k i _ (by rw [frontUnalignedStageLength]; omega)]
      by_cases he' : k=i
      · subst i
        rw [if_pos rfl, if_neg (Nat.lt_irrefl _), if_pos rfl]
      · rw [if_neg he', frontUnalignedStageGet words r (k+1) i hb]
        by_cases hl : i < k
        · rw [if_pos hl, if_pos (by omega)]
        · rw [if_neg hl, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A padded source last word contributes no high bits to the initially empty boundary. -/
theorem frontUnalignedBoundaryZero (word : U64) (r : Nat) (hr : r ≤ 64)
    (hclip : resizeFrontPairClip word r = word) :
    copyPairPaste word (u64 0) 0 r = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 r bit (by omega) hb, packedBit_zero]
  by_cases hi : bit < r
  · rw [if_pos (by omega), packedBit_zero]
  · rw [if_neg (by omega)]
    have h := congrArg (fun w => packedBit w bit) hclip
    rw [resizeFrontPairClipBit word r bit hr hb, if_neg hi] at h
    simpa only [packedBit_zero] using h.symm

/-- The mixed boundary invariant starts at the original encoding followed by its initialized zero chunk. -/
theorem frontUnalignedStageInitial (words : List U64) (r : Nat) (hr : r ≤ 64)
    (hclip : resizeFrontPairClip (words.getD (words.length-1) (u64 0)) r =
      words.getD (words.length-1) (u64 0)) :
    frontUnalignedStage words r words.length = words ++ [u64 0] := by
  apply List.ext_getElem
  · simp only [frontUnalignedStageLength, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  · intro i hi hi'
    have hb : i < words.length+1 := by simpa only [frontUnalignedStageLength] using hi
    rw [List.getElem_eq_getD (fallback := u64 0), frontUnalignedStageGet words r words.length i hb,
      List.getElem_eq_getD (fallback := u64 0)]
    by_cases hl : i < words.length
    · rw [if_pos hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
    · have he : i=words.length := by omega
      subst i
      rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
      have hz : words.getD words.length (u64 0) = u64 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_refl _), Option.getD_none]
      rw [hz, frontUnalignedBoundaryZero _ r hr hclip]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

/-- Once the final partial block restores word1, every source word has its final successor position. -/
theorem frontUnalignedStageFinal (words : List U64) (r : Nat) (hp : 0 < words.length) :
    (frontUnalignedStage words r 1).set 1 (words.getD 0 (u64 0)) = words.headD (u64 0) :: words := by
  apply List.ext_getElem
  · simp only [List.length_set, frontUnalignedStageLength, List.length_cons]
  · intro i hi hi'
    have hb : i < words.length+1 := by simpa only [List.length_set, frontUnalignedStageLength] using hi
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ 1 i _ (by rw [frontUnalignedStageLength]; omega),
      List.getElem_eq_getD (fallback := u64 0)]
    by_cases he : 1=i
    · subst i
      simp only [ite_true, List.getD_cons_succ]
    · rw [if_neg he, frontUnalignedStageGet words r 1 i hb]
      cases i with
      | zero =>
        simp only [show 0 < 1 by decide, ite_true, List.getD_cons_zero]
        cases words <;> rfl
      | succ i =>
        rw [if_neg (by omega), if_neg (by omega)]
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, List.getD_cons_succ]
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

theorem frontUnalignedAddress (chunk r : Nat) (hr : r < 64)
    (hn : chunk*64+r+1 ≤ 9223372036854775807) :
    getChunksId (int ((chunk*64+r+1 : Nat) : Int)) = (int ((chunk+1 : Nat) : Int), int r) := by
  have h := scalar_chunks_nat (chunk*64+r) hn
  simpa only [show (chunk*64+r)/64=chunk by omega,
    show (chunk*64+r)%64=r by omega] using h

theorem frontUnalignedEndAddress (chunk r : Nat) (hp : 0 < r) (hr : r < 64)
    (hn : (chunk+1)*64+r ≤ 9223372036854775807) :
    getChunksId (int ((chunk*64+r+1 : Nat) : Int) + int 64 - int 1) =
      (int ((chunk+2 : Nat) : Int), int ((r-1 : Nat) : Int)) := by
  have he : int ((chunk*64+r+1 : Nat) : Int) + int 64 - int 1 =
      int ((chunk*64+r+63+1 : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    exact congrArg int (by omega)
  rw [he]
  have h := scalar_chunks_nat (chunk*64+r+63) (by omega)
  rw [show (chunk*64+r+63)/64=chunk+1 by omega,
    show (chunk*64+r+63)%64=r-1 by omega, show chunk+1+1=chunk+2 by omega] at h
  exact h

/-- Every full descending block at the common source/destination remainder advances the mixed boundary exactly once. -/
theorem frontUnalignedBlockRun (words : List U64) (r k spare : Nat)
    (hp : 0 < r) (hr : r < 64) (hk : 0 < k) (hk' : k < words.length)
    (hn : (words.length+1)*64 ≤ 9223372036854775807) :
    (frontCopyBlock 0 (int ((k*64+r+1 : Nat) : Int))
      (int (((k-1)*64+r+1 : Nat) : Int)) (int 64)).run
      (dequeWordStore (frontUnalignedStage words r (k+1)) spare) =
        (.ok (), dequeWordStore (frontUnalignedStage words r k) spare) := by
  let original := frontUnalignedStage words r (k+1)
  let boundary := copyPairPaste (words.getD (k-1) (u64 0)) (words.getD k (u64 0)) 0 r
  let changed := original.set k boundary
  let gathered := copyPairGlue (words.getD (k-1) (u64 0)) (words.getD k (u64 0)) r
  have hlen : original.length=words.length+1 := frontUnalignedStageLength _ _ _
  have hlenc : changed.length=words.length+1 := by simp only [changed, List.length_set, hlen]
  have hprev := dequeWordRead original spare (k-1) (by omega) (by omega)
  have hcurrent := dequeWordRead original spare k (by omega) (by omega)
  rw [frontUnalignedStageGet words r (k+1) (k-1) (by omega), if_pos (by omega)] at hprev
  rw [frontUnalignedStageGet words r (k+1) k (by omega), if_pos (by omega)] at hcurrent
  have hg := shiftNearGluePairRun 0 (k-1) r (words.getD (k-1) (u64 0))
    (words.getD k (u64 0)) (dequeWordStore original spare) (by omega) hp hr hprev
    (by simpa only [show k-1+2=k+1 by omega] using hcurrent)
  have hs0 : (k-1+1)=k := by omega
  have hs1 : (k-1+2)=k+1 := by omega
  simp only [hs0, hs1] at hg
  have hdiff : int ((k+2 : Nat) : Int) - int ((k+1 : Nat) : Int) = int 1 := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hsrcdiff : int ((k+1 : Nat) : Int) - int k = int 1 := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hmask : copyPairSourceMask (int k) (int ((k+1 : Nat) : Int)) (int r)
      (int ((r-1 : Nat) : Int)) = shl_int u64Max (int r) := by
    simp only [copyPairSourceMask, hsrcdiff, show (int 1 == int 0)=false from rfl, Bool.false_eq_true, ite_false]
  have hw0 := dequeWordSet original spare k boundary (by omega) (by omega)
  have hr1 := dequeWordRead changed spare (k+1) (by omega) (by omega)
  rw [dequeWordGetSet original k (k+1) boundary (by omega), if_neg (by omega),
    frontUnalignedStageGet words r (k+1) (k+1) (by omega), if_neg (Nat.lt_irrefl _), if_pos rfl,
    Nat.add_sub_cancel] at hr1
  have hw1 := dequeWordSet changed spare (k+1) (words.getD k (u64 0)) (by omega) (by omega)
  have hchange : changed.set (k+1) (words.getD k (u64 0)) = frontUnalignedStage words r k :=
    frontUnalignedStageStep words r k hk hk'
  rw [hchange] at hw1
  exact frontBlockTwoFrom 0 _ _ 64 r r
    (int ((k+1 : Nat) : Int)) (int ((k+2 : Nat) : Int))
    (int k) (int r) (int ((k+1 : Nat) : Int)) (int ((r-1 : Nat) : Int))
    (dequeWordStore original spare) (dequeWordStore changed spare) _
    (words.getD k (u64 0))
    (copyPairPaste (words.getD k (u64 0)) (words.getD (k+1) (u64 0)) 0 r)
    gathered gathered (by omega) hp (by omega) hdiff
    (frontUnalignedAddress k r hr (by omega)) (by simpa only [show int ((64 : Nat) : Int)=int 64 from rfl] using frontUnalignedEndAddress k r hp hr (by omega))
    (by simpa only [hs0] using frontUnalignedAddress (k-1) r hr (by omega))
    (by simpa only [hs1, show int ((64 : Nat) : Int)=int 64 from rfl] using frontUnalignedEndAddress (k-1) r hp hr (by omega))
    (by simpa only [hmask] using hg) (resizeFrontPairClipFull gathered)
    hcurrent (by rw [frontUnalignedLowPaste _ _ r hr]; exact hw0) hr1
    (by rw [frontUnalignedHighPaste _ _ _ r hr]; exact hw1)

/-- The last partial block completes word1 while preserving the original first word. -/
theorem frontUnalignedLastRun (words : List U64) (r spare : Nat)
    (hp : 0 < r) (hr : r < 64) (hw : 0 < words.length)
    (hn : words.length+1 ≤ 9223372036854775807) :
    (frontCopyBlock 0 (int 65) (int 1) (int r)).run
      (dequeWordStore (frontUnalignedStage words r 1) spare) =
        (.ok (), dequeWordStore (words.headD (u64 0)::words) spare) := by
  let original := frontUnalignedStage words r 1
  have hlen : original.length=words.length+1 := frontUnalignedStageLength _ _ _
  have hsource := dequeWordRead original spare 0 (by omega) (by omega)
  have hdest := dequeWordRead original spare 1 (by omega) (by omega)
  rw [frontUnalignedStageGet words r 1 0 (by omega), if_pos (by decide)] at hsource
  rw [frontUnalignedStageGet words r 1 1 (by omega), if_neg (Nat.lt_irrefl _), if_pos rfl] at hdest
  have hwrite := dequeWordSet original spare 1 (words.getD 0 (u64 0)) (by omega) (by omega)
  rw [frontUnalignedStageFinal words r hw] at hwrite
  have hd : getChunksId (int 65 + int r - int 1) = (int 2, int ((r-1 : Nat) : Int)) := by
    have he : int 65 + int r - int 1 = int ((64+r-1+1 : Nat) : Int) := by
      rw [packedInt_add, dequeIntSub]
      exact congrArg int (by omega)
    rw [he]
    have h := scalar_chunks_nat (64+r-1) (by omega)
    rw [show (64+r-1)/64=1 by omega, show (64+r-1)%64=r-1 by omega] at h
    exact h
  have hs : getChunksId (int 1 + int r - int 1) = (int 1, int ((r-1 : Nat) : Int)) := by
    have he : int 1 + int r - int 1 = int ((r-1+1 : Nat) : Int) := by
      rw [packedInt_add, dequeIntSub]
      exact congrArg int (by omega)
    rw [he]
    exact rangeSingleAddress (r-1) (by omega)
  exact frontCopyBlockOne 0 (int 65) (int 1) r 0 (int 2) (int 1) (int 0) (int 1)
    (int ((r-1 : Nat) : Int)) _ _
    (copyPairPaste (words.getD 0 (u64 0)) (words.getD 1 (u64 0)) 0 r)
    (resizeFrontPairClip (words.getD 0 (u64 0)) r)
    (resizeFrontPairClip (words.getD 0 (u64 0)) r)
    hp (by omega) (by decide) (by simpa only [Nat.zero_add] using hd) (by decide) hs
    (frontCopyZeroSourceRun 0 r _ _ hp (by omega) hsource)
    (frontCopyClipIdempotent _ r (by omega)) hdest
    (by rw [frontUnalignedFinalPaste _ _ r (by omega)]; exact hwrite)

/-- A padded unaligned source is copied one word right by the complete native descending loop. -/
theorem frontUnalignedCopyRun (words : List U64) (n r spare : Nat)
    (hp : 0 < r) (hr : r < 64) (hrem : n % 64 = r) (hcount : wordCount n=words.length)
    (hn : (words.length+1)*64 ≤ 9223372036854775807)
    (hclip : resizeFrontPairClip (words.getD (words.length-1) (u64 0)) r =
      words.getD (words.length-1) (u64 0)) :
    (copyChunks 0 (int 65) 0 (int 1) (int n)).run
      (dequeWordStore (words++[u64 0]) spare) =
        (.ok (), dequeWordStore (words.headD (u64 0)::words) spare) := by
  have hc := hcount
  unfold wordCount at hc
  have hnp : 0 < n := by omega
  have hwp : 0 < words.length := by omega
  have hnative : n ≤ 9223372036854775807 := by omega
  let stage : Nat → State := fun left =>
    if left=0 then dequeWordStore (words.headD (u64 0)::words) spare
    else dequeWordStore (frontUnalignedStage words r (wordCount left)) spare
  have hstep : ∀ left : Nat, 0 < left → left ≤ n → left%64=n%64 →
      (frontCopyBlock 0 (int 65 + int ((left-min left 64 : Nat) : Int))
        (int 1 + int ((left-min left 64 : Nat) : Int)) (int ((min left 64 : Nat) : Int))).run
        (stage left) = (.ok (), stage (left-min left 64)) := by
    intro left hl hle hres
    by_cases hs : left ≤ 64
    · have he : left=r := by omega
      subst left
      have hmin : min r 64=r := Nat.min_eq_left (by omega)
      have hwc : wordCount r=1 := by unfold wordCount; omega
      simp only [stage, hmin, Nat.sub_self, show ¬r=0 by omega, ite_false, ite_true,
        hwc, Int.ofNat_zero, frontCopyAddZero]
      exact frontUnalignedLastRun words r spare hp hr hwp (by omega)
    · let k := wordCount left-1
      have hk : 0 < k := by dsimp only [k]; unfold wordCount; omega
      have hkb : k < words.length := by dsimp only [k]; unfold wordCount; omega
      have hkl : wordCount left=k+1 := by dsimp only [k]; unfold wordCount; omega
      have hkr : wordCount (left-64)=k := by dsimp only [k]; unfold wordCount; omega
      have haddr : left-64=(k-1)*64+r := by dsimp only [k]; unfold wordCount; omega
      have hsrc : int 1 + int ((left-64 : Nat) : Int) = int (((k-1)*64+r+1 : Nat) : Int) := by
        rw [packedInt_add]
        exact congrArg int (by omega)
      have hdst : int 65 + int ((left-64 : Nat) : Int) = int ((k*64+r+1 : Nat) : Int) := by
        rw [packedInt_add]
        exact congrArg int (by omega)
      have hmin : min left 64=64 := Nat.min_eq_right (by omega)
      simp only [stage, hmin, show ¬left=0 by omega, show ¬left-64=0 by omega,
        ite_false, hkl, hkr, hsrc, hdst, show int ((64 : Nat) : Int)=int 64 from rfl]
      exact frontUnalignedBlockRun words r k spare hp hr hk hkb hn
  have hlo := frontCopyLoopResidue 0 (int 65) (int 1) n stage hnative hstep
  have hs : stage n=dequeWordStore (words++[u64 0]) spare := by
    simp only [stage, show ¬n=0 by omega, ite_false, hcount,
      frontUnalignedStageInitial words r (by omega) hclip]
  have hz : stage 0=dequeWordStore (words.headD (u64 0)::words) spare := by simp only [stage, ite_true]
  rw [hs, hz] at hlo
  have hrun := frontCopyRtolFromLoop 0 (int 65) (int 1) (int n) _ _
    (frontCopyRegisters (int 65) (int 1) (int 0)) (by decide) (by decide) hlo
  simp only [copyChunks, fillPositiveLength n hnp hnative, Bool.false_eq_true, ite_false,
    show (0=(0:Nat) ∧ int 65>int 1) from by decide, dite_true]
  exact hrun
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The final encoded slot is the canonical packed word at floor((length-1)/64). -/
theorem frontLastEncodedGet (xs : List Bool) (hp : 0 < xs.length) :
    (encodeBits xs).getD ((encodeBits xs).length - 1) (u64 0) =
      packedPrefix xs ((xs.length - 1) / 64) 64 := by
  have hw : 0 < wordCount xs.length := by unfold wordCount; omega
  have hd : wordCount xs.length - 1 = (xs.length - 1) / 64 := by unfold wordCount; omega
  rw [packedEncoded_length, packedPrefix_eq_encode]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp only [List.length_map, List.length_range]; omega), Option.getD_some]
  simp only [List.getElem_map, List.getElem_range, hd]

/-- The last encoded source word satisfies the initial mixed-boundary clipping invariant. -/
theorem frontLastEncodedClip (xs : List Bool) (hr : xs.length % 64 ≠ 0) :
    resizeFrontPairClip ((encodeBits xs).getD ((encodeBits xs).length - 1) (u64 0)) (xs.length % 64) =
      (encodeBits xs).getD ((encodeBits xs).length - 1) (u64 0) := by
  rw [frontLastEncodedGet xs (by omega)]
  exact frontLastPackedClip xs hr
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

/-- Moving a complete logical vector right by64 bits is exact for every original alignment. -/
theorem frontWholeCopyAnyRun (xs : List Bool) (spare : Nat)
    (hn : (wordCount xs.length+1)*64 ≤ 9223372036854775807) :
    (copyChunks 0 (int 65) 0 (int 1) (int xs.length)).run
      (dequeWordStore (encodeBits xs++[u64 0]) spare) =
        (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) spare) := by
  have hlen := packedEncoded_length xs
  by_cases hm : xs.length%64=0
  · have h := frontWholeCopyRun (encodeBits xs) spare (by omega)
    rw [frontWholePackedLength xs hm] at h
    exact h.trans (by rw [frontWholeEncoding])
  · have h := frontUnalignedCopyRun (encodeBits xs) xs.length (xs.length%64) spare
      (by omega) (Nat.mod_lt _ (by decide)) rfl hlen.symm (by omega) (frontLastEncodedClip xs hm)
    exact h.trans (by rw [frontWholeEncoding])

/-- The canonical in-place copy needed by front growth of exactly one word. -/
def frontWordAnyCopyContract (xs : List Bool) : Prop :=
  ∀ spare : Nat,
    (copyChunks 0 (int 65) 0 (int 1) (int xs.length)).run
      (dequeWordStore (encodeBits xs ++ [u64 0]) spare) =
      (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) spare)

theorem frontWordAnyLengthBound (xs : List Bool)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807) :
    xs.length + 64 ≤ 9223372036854775807 := by
  unfold wordCount at hcapacity
  omega

/-- Front growth by one complete word has exact canonical packed output whenever its canonical copy contract holds. -/
theorem resizeFrontWordAnyRunFromCopy {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807)
    (hcopyRun : frontWordAnyCopyContract xs)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + 64 : Nat) : Int))) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
      (initWords (encodeBits xs)) =
        (.ok {vectorBits xs with len := int ((xs.length + 64 : Nat) : Int)},
          dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) 31) := by
  have hn := frontWordAnyLengthBound xs hcapacity
  let words := encodeBits xs
  let n := xs.length + 64
  have hb : (words.length + 1) * 64 ≤ 9223372036854775807 := by
    dsimp only [words]
    rw [packedEncoded_length]
    exact hcapacity
  have hcount : wordCount n = words.length + 1 := by
    dsimp only [n, words]
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hnum : numBitChunks (int n) = int ((words.length + 1 : Nat) : Int) := by
    rw [resizeNumChunks n hn, hcount]
  have hzero : ¬ int n < int 0 := by
    change ¬ (int n).val < 0
    rw [packedInt_val n hn]
    omega
  have hlt : (vectorBits xs).len < int n := by
    change (int xs.length).val < (int n).val
    rw [packedInt_val xs.length (by omega), packedInt_val n hn]
    dsimp only [n]
    omega
  have hmore : int ((words.length + 1 : Nat) : Int) > int words.length := by
    change (int words.length).val < (int ((words.length + 1 : Nat) : Int)).val
    rw [packedInt_val words.length (by omega), packedInt_val (words.length + 1) (by omega)]
    omega
  have hdiff : int ((words.length + 1 : Nat) : Int) - int words.length = int 1 := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hg : ((if numBitChunks (int n) > int words.length then do
      growChunkVector 0 (numBitChunks (int n) - int words.length)
      mutableSet 0 (u64 0) (← mutableLength 0)
    else pure ()) : BitMutationM Unit).run (dequeWordStore words 32) =
      (.ok (), dequeWordStore (words ++ [u64 0]) 31) := by
    rw [hnum, if_pos hmore, hdiff]
    exact dequeGrowZeroRun words 31 (by omega)
  have hdest : int 1 + int n - (vectorBits xs).len = int 65 := by
    change int 1 + int n - int xs.length = int 65
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [n]
    omega
  have hcopy : (copyChunks 0 (int 1 + int n - (vectorBits xs).len) 0 (int 1) (vectorBits xs).len).run
      (dequeWordStore (words ++ [u64 0]) 31) =
        (.ok (), dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) 31) := by
    rw [hdest]
    change (copyChunks 0 (int 65) 0 (int 1) (int xs.length)).run _ = _
    exact hcopyRun 31
  rw [← dequeWordStoreInitial]
  exact resizeFrontSinglePublicGrowFrom (vectorBits xs) requested (int n) (int words.length)
    (dequeWordStore words 32) (dequeWordStore (words ++ [u64 0]) 31) _ hc hzero hlt
    (dequeWordLength words 32) hg hcopy

/-- Every supported growth by sixty-four bits preserves the full original suffix and packed padding. -/
theorem resizeFrontWordAnySuccessFromCopy {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807)
    (hcopyRun : frontWordAnyCopyContract xs)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + 64 : Nat) : Int))) :
    resizeFrontSingleSuccessAt xs requested (xs.length + 64) := by
  have hn := frontWordAnyLengthBound xs hcapacity
  let ys := resizeFrontSingleBits xs 64
  let B' : BitArray 1 := {vectorBits xs with len := int ((xs.length + 64 : Nat) : Int)}
  let out := dequeWordStore (encodeBits ys) 31
  have hlen : ys.length = xs.length + 64 := by rw [resizeFrontSingleLength]; omega
  have hy : ys.length ≤ 9223372036854775807 := by rw [hlen]; exact hn
  have hl : B'.len = int ys.length := by change int ((xs.length + 64 : Nat) : Int) = _; rw [hlen]
  have hcontents : out.contents B'.chunks = (encodeBits ys).map some :=
    dequeWordContents _ _ (packedEncoded_lengthBound ys hy)
  have hv := scalar_bitValues_contents out B' ys hy hl hcontents
  refine ⟨B', out, resizeFrontWordAnyRunFromCopy xs requested hcapacity hcopyRun hc, rfl, ?_,
    scalar_invariant_of_contents out B' ys hy hl hcontents⟩
  rw [if_neg (by omega), show xs.length + 64 - xs.length = 64 by omega, hv]
  exact (resizeFrontSingleSuffix xs 64).symm

/-- All installed conversion outcomes satisfy the frozen front-resize observation when successful conversion requests this word growth. -/
theorem resizeFrontWordAnyCorrectFromCopy {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807)
    (hcopyRun : frontWordAnyCopyContract xs)
    (hrequested : ∀ n : I64, JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n →
      n = int ((xs.length + 64 : Nat) : Int)) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) := by
  have hn := frontWordAnyLengthBound xs hcapacity
  apply resizeFrontSingleFromNatural xs requested
  intro n hbound hc
  have hn' : n ≤ 9223372036854775807 := by
    change n < 4611686018427387903 at hbound
    omega
  have he := congrArg Subtype.val (hrequested (int n) hc)
  rw [packedInt_val n hn', packedInt_val (xs.length + 64) hn] at he
  have hnEq : n = xs.length + 64 := by omega
  subst n
  exact resizeFrontWordAnySuccessFromCopy xs requested hcapacity hcopyRun hc
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The concrete descending copy satisfies the one-word growth contract at every input alignment. -/
theorem frontWordAnyCopyCorrect (xs : List Bool)
    (hn : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807) :
    frontWordAnyCopyContract xs := by
  intro spare
  exact frontWholeCopyAnyRun xs spare hn

theorem resizeFrontWordAnyRun {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + 64 : Nat) : Int))) :
    (Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
      (initWords (encodeBits xs)) =
        (.ok {vectorBits xs with len := int ((xs.length + 64 : Nat) : Int)},
          dequeWordStore (encodeBits (resizeFrontSingleBits xs 64)) 31) :=
  resizeFrontWordAnyRunFromCopy xs requested hcapacity (frontWordAnyCopyCorrect xs hcapacity) hc

theorem resizeFrontWordAnySuccess {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807)
    (hc : JuliaLean.base.range.JConvert.convert (T := I64) requested =
      .ok (int ((xs.length + 64 : Nat) : Int))) :
    resizeFrontSingleSuccessAt xs requested (xs.length + 64) :=
  resizeFrontWordAnySuccessFromCopy xs requested hcapacity (frontWordAnyCopyCorrect xs hcapacity) hc

theorem resizeFrontWordAnyCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X)
    (hcapacity : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807)
    (hrequested : ∀ n : I64, JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n →
      n = int ((xs.length + 64 : Nat) : Int)) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) :=
  resizeFrontWordAnyCorrectFromCopy xs requested hcapacity (frontWordAnyCopyCorrect xs hcapacity) hrequested

/-- Every frozen-supported original vector has the complete front-resize observation for growth by one whole word. -/
theorem resizeFrontWordSupportedCorrect {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (xs : List Bool) (requested : X) (hx : xs.length < Round5.maxVectorLength)
    (hrequested : ∀ n : I64, JuliaLean.base.range.JConvert.convert (T := I64) requested = .ok n →
      n = int ((xs.length + 64 : Nat) : Int)) :
    resizeFrontSingleObservation xs (initWords (encodeBits xs))
      (JuliaLean.base.range.JConvert.convert (T := I64) requested)
      ((Round5.Round2.resizeBitVectorPublic (vectorBits xs) requested true).run
        (initWords (encodeBits xs))) := by
  have hb : (wordCount xs.length + 1) * 64 ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hx
    unfold wordCount
    omega
  exact resizeFrontWordAnyCorrect xs requested hb hrequested
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096

/-- The installed empty-vector proof applies to the bounded public statement. -/
theorem BitarrayBitVectorEmptyAgrees_proven :
    JuliaLean.Proofs.base.bitarray.Round2.BitVectorEmptyAgrees := by
  intro xs _
  dsimp only
  generalize hb : vectorBits xs = B
  generalize hw : encodeBits xs = words
  have hc : B.chunks = 0 := by
    rw [← hb]
    rfl
  exact JuliaLean.ChatGPT.Batch2.Group4.emptyWordsFrozen B words hc

/-- Failed Integer conversion in resizing leaves the complete store unchanged. -/
theorem resizeNegative_conversion_error {X : Type}
    [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (n : X) (first : Bool) (e : JuliaLean.base.range.Exc)
    (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := I64) n = .error e) :
    (Round5.Round2.resizeBitVectorPublic B n first).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [Round5.Round2.resizeBitVectorPublic, h,
    Round5.Round2.liftRangeResult, shape_run_bind]
  rfl

/-- A negative converted length fails before storage is touched. -/
theorem resizeNegative_negative {X : Type}
    [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (n : X) (first : Bool) (newLength : I64) (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := I64) n = .ok newLength)
    (hB : 0 ≤ B.len.val) (hn : newLength.val < 0) :
    (Round5.Round2.resizeBitVectorPublic B n first).run s = (.error .bounds, s) := by
  have hlt : newLength < int 0 := hn
  have hne : (newLength == B.len) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    omega
  simp only [Round5.Round2.resizeBitVectorPublic, h,
    Round5.Round2.liftRangeResult, shape_run_bind, shape_run_pure,
    hlt, true_or, ite_true, bitVectorResize, bitVectorResizeInt,
    hne, Bool.false_eq_true, ite_false]
  rfl

/-- Negative requests and rejected conversions are atomic under the frozen bound. -/
theorem BitarraysResizeNegative_proven :
    JuliaLean.Proofs.base.bitarray.Round5.ResizeNegativeAgrees := by
  intro xs X inst n hlen
  have hbound : xs.length ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hlen
    omega
  have hB : 0 ≤ (vectorBits xs).len.val := by
    change 0 ≤ (int xs.length).val
    rw [packedInt_val xs.length hbound]
    omega
  cases hconv : JuliaLean.base.range.JConvert.convert (T := I64) n with
  | error e =>
    simp only [hconv, resizeNegative_conversion_error (vectorBits xs) n false e
      (initWords (encodeBits xs)) hconv]
  | ok newLength =>
    simp only [hconv]
    by_cases hn : newLength.val < 0
    · simp only [hn, ite_true, resizeNegative_negative (vectorBits xs) n false
        newLength (initWords (encodeBits xs)) hconv hB hn]
    · simp only [hn, ite_false]
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray


/-- An initialized logical bit, described directly from physical chunk contents.
This observation does not call the executable getter and does not read `none` as
false. It is used only for old elements retained by a resize. -/
def KnownBit (s : Heap) (B : BitVector) (i : Nat) (value : Bool) : Prop :=
  ∃ word : U64,
    (s.contents B.chunks)[i / 64]? = some (some word) ∧
    decide ((word.val.toNat / 2 ^ (i % 64)) % 2 = 1) = value

/-- The complete machine-Integer/default-first=false resize specialization,
including every length and checked-conversion or negative-length error.
Successful resizing preserves the old prefix, the BitVector's object/chunk
identity and unused dims field, and gives the requested logical length. Newly
exposed cells need not be initialized: no claim is made about their values or
readability. A same-size request is an exact no-op.

Julia source: base/bitarray.jl:803-825.
Documentation: base/array.jl:1523-1530. These are unproved independent promises;
rows803/804 remain blocked for their unimplemented first=true/general domains. -/
def ResizeLastMachineContract : Prop :=
  ∀ (t : IntTy) (s : Heap) (B : BitVector) (n : JInt t),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.resizeLastMachine B n).run s
    if ¬ FitsNative n.val then
      result.1 = .error .inexact ∧ result.2 = s
    else if n.val < 0 then
      result.1 = .error .bounds ∧ result.2 = s
    else
      (n.val = B.len.val → result = (.ok B, s)) ∧
      match result.1 with
      | .ok updated =>
          updated.chunks = B.chunks ∧ updated.len.val = n.val ∧
          updated.dims = B.dims ∧ result.2.validVector updated.chunks ∧
          (n.val.toNat + 63) / 64 ≤ (result.2.contents updated.chunks).length ∧
          ∀ i, i < min B.len.val.toNat n.val.toNat →
            KnownBit result.2 updated i (bitAt s B i)
      | .error _ => False
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesResize1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-resize-negative", juliaFile := "base/bitarray.jl", juliaFns := ["resize!(::BitVector, n)"],
    statement := "Negative resize lengths and failed Integer conversions return an error without changing the BitVector; no error class is asserted.", source := "base/bitarray.jl:803-825",
    status := .proven, prop := ``Round5.ResizeNegativeAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group2.BitarraysResizeNegative_proven },
  { id := "bitarrays-resize-nonneg", juliaFile := "base/bitarray.jl", juliaFns := ["resize!(::BitVector, n; first)"],
    statement := "For converted nonnegative lengths below the model bound, resize! returns that length, retains the prefix or the first=true suffix, and preserves packed padding; new values are unspecified and failed conversions leave state unchanged.", source := "base/bitarray.jl:803-825",
    status := .todo, prop := ``Round5.ResizeNonnegAgrees, thm := none, notes := "No complete exact proof returned. the remaining exact target is blocked by the old forward-copy source-index discrepancy." }
]
def entriesResize2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-vector-empty-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["empty!@1137"],
    statement := "For BitVectors shorter than typemax(Int)/2, empty! sets length to zero and removes all chunks.", source := "base/bitarray.jl:1137-1141",
    status := .proven, prop := ``Round2.BitVectorEmptyAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group2.BitarrayBitVectorEmptyAgrees_proven }
]
def entriesResize3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-resize-last-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["resize!(::BitVector, ::BitInteger; first=false)", "_resize_int!(::BitVector, ::Int, false)"],
    statement := "Default-direction resize preserves the retained logical prefix and actual chunk identity, returns the requested native length, and retains conversion/negative-length errors; newly exposed bits have no promised value.",
    source := "base/bitarray.jl:803-825; base/array.jl:1523-1530", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.ResizeLastMachineContract, thm := none,
    notes := "No complete exact proof returned. Conversion and growth/shrink retained-prefix preservation remain open." }
]
end JuliaLean.Proofs.base.bitarray

