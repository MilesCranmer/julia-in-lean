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
import JuliaLean.Proofs.base.bitarray.copyto_vcat

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A yielding sorted-index iteration composes with the remaining loop and cleanup. -/
theorem copy_indices_after_yield (B : BitVector) (indices : List I64)
    (before after : copy_indices_Registers) (state middle final : State) (output : BitVector)
    (hstep : (copy_indices_step B.len B.chunks indices () before).run state = (.ok (.yield after), middle))
    (hrest : (copy_indices_after B indices after).run middle = (.ok output, final)) :
    (copy_indices_after B indices before).run state = (.ok output, final) := by
  unfold copy_indices_after at *
  rw [resizeFrontLoopUnfold]
  simp only [bind_assoc, shape_run_bind, hstep]
  simpa only [shape_run_bind] using hrest

/-- An exhausted index iterator delegates directly to its final suffix-copy phase. -/
theorem copy_indices_after_done (B : BitVector) (indices : List I64)
    (newL p q : I64) (state final : State) (output : BitVector)
    (hfinish : (copy_indices_finish B (newL, none, p, q)).run state = (.ok output, final)) :
    (copy_indices_after B indices (newL, none, p, q)).run state = (.ok output, final) := by
  have hloop := reverseLoopDone (copy_indices_step B.len B.chunks indices)
    (newL, none, p, q) (newL, none, p, q) state state (by
      simp only [copy_indices_step, Option.isSome_none, Bool.false_eq_true, ite_false, shape_run_pure])
  exact concat_bind_success _ _ state state final (newL, none, p, q) output hloop hfinish

/-- Index-list and Boolean-mask deletion share exactly the same final mutation phase. -/
theorem copy_indices_finish_eq_mask (B : BitVector) (newL p q : I64) (y : Option (I64 × Nat)) :
    copy_indices_finish B (newL, y, p, q) =
      scan_maskDelete_finish B (newL, none, p, q, q) := rfl

/-- Every valid one-word sorted-index iteration has ordinary natural compaction arithmetic. -/
theorem copy_indices_step_natural (n kept start finish deleted index spare : Nat)
    (word : U64) (indices : List I64) (found : Option (I64 × Nat))
    (hn : n ≤ 64) (hk : kept + deleted = start) (hs : start ≤ finish) (hf : finish < n)
    (hnext : indices[index + 1]?.map (fun value => (value, index + 1)) = found) :
    (copy_indices_step (int n) 0 indices ()
      (int ((n - deleted : Nat) : Int), some (int ((finish + 1 : Nat) : Int), index),
        int ((kept + 1 : Nat) : Int), int ((start + 1 : Nat) : Int))).run
      (dequeWordStore [word] spare) =
      (.ok (.yield (int ((n - (deleted + 1) : Nat) : Int), found,
        int ((kept + (finish - start) + 1 : Nat) : Int), int ((finish + 2 : Nat) : Int))),
        dequeWordStore [rangeSingleCopyWord word kept start (finish - start)] spare) := by
  have hv : int ((start + 1 : Nat) : Int) ≤ int ((finish + 1 : Nat) : Int) ∧
      int ((finish + 1 : Nat) : Int) ≤ int n := by
    change (int ((start + 1 : Nat) : Int)).val ≤ (int ((finish + 1 : Nat) : Int)).val ∧
      (int ((finish + 1 : Nat) : Int)).val ≤ (int n).val
    rw [packedInt_val (start + 1) (by omega), packedInt_val (finish + 1) (by omega),
      packedInt_val n (by omega)]
    omega
  have hnew : int ((n - deleted : Nat) : Int) - int 1 = int ((n - (deleted + 1) : Nat) : Int) := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hq : int ((finish + 1 : Nat) : Int) + int 1 = int ((finish + 2 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  have hp : (if int ((finish + 1 : Nat) : Int) > int ((start + 1 : Nat) : Int) then
      int ((kept + 1 : Nat) : Int) + int ((finish + 1 : Nat) : Int) - int ((start + 1 : Nat) : Int)
      else int ((kept + 1 : Nat) : Int)) = int ((kept + (finish - start) + 1 : Nat) : Int) := by
    by_cases hlt : start < finish
    · have hm : int ((finish + 1 : Nat) : Int) > int ((start + 1 : Nat) : Int) := by
        change (int ((start + 1 : Nat) : Int)).val < (int ((finish + 1 : Nat) : Int)).val
        rw [packedInt_val (start + 1) (by omega), packedInt_val (finish + 1) (by omega)]
        omega
      rw [if_pos hm, packedInt_add, dequeIntSub]
      exact congrArg int (by omega)
    · have he : start = finish := by omega
      rw [he]
      have hnot : ¬ int ((finish + 1 : Nat) : Int) > int ((finish + 1 : Nat) : Int) :=
        Int.lt_irrefl _
      rw [if_neg hnot]
      simp only [Nat.sub_self, Nat.add_zero]
  have hr := copy_indices_step_from (int n) 0 indices
    (int ((n - deleted : Nat) : Int)) (int ((kept + 1 : Nat) : Int))
    (int ((start + 1 : Nat) : Int)) (int ((finish + 1 : Nat) : Int)) index found _ _ hv hnext
    (scan_maskDelete_interval_copy kept start finish spare word (by omega) hs (by omega))
  simpa only [hnew, hp, hq] using hr

/-- The complete sorted-index iterator preserves a compacted prefix and moves each
remaining source interval exactly once within the single packed word. -/
theorem copy_indices_loop_correct (xs : List Bool) (selected remaining : List Nat)
    (before : List Nat) (kept : List Bool) (word : U64) (start deleted spare : Nat)
    (hn : xs.length ≤ 64) (hstart : start ≤ xs.length)
    (hbalance : kept.length + deleted = start)
    (hordered : remaining.Pairwise (· < ·))
    (hbound : ∀ i ∈ remaining, start ≤ i ∧ i < xs.length)
    (hdecomp : selected = before ++ remaining)
    (hprefix : scan_maskDelete_prefix word kept)
    (hsuffix : scan_maskDelete_suffix word xs start) :
    ∃ output outState,
      (copy_indices_after (vectorBits xs) (selected.map (fun i => int ((i + 1 : Nat) : Int)))
        (int ((xs.length - deleted : Nat) : Int),
          remaining.head?.map (fun i => (int ((i + 1 : Nat) : Int), before.length)),
          int ((kept.length + 1 : Nat) : Int), int ((start + 1 : Nat) : Int))).run
        (dequeWordStore [word] spare) = (.ok output, outState) ∧
      bitValues outState output = kept ++ scan_maskDelete_blocks xs remaining start := by
  induction remaining generalizing before kept word start deleted with
  | nil =>
    obtain ⟨outState, hcleanup, hbits⟩ := scan_maskDelete_cleanup_after_tail xs kept word
      start deleted spare hn hstart hbalance hprefix hsuffix
    let output : BitVector := {vectorBits xs with len := int ((xs.length - deleted : Nat) : Int)}
    have hcopy := scan_maskDelete_tail_copy xs.length kept.length start spare word hn (by omega) hstart
    have hlength : (mutableLength 0).run
        (dequeWordStore [rangeSingleCopyWord word kept.length start (xs.length - start)] spare) =
        (.ok (int 1), dequeWordStore [rangeSingleCopyWord word kept.length start (xs.length - start)] spare) :=
      dequeWordLength _ spare
    have hfinish := scan_maskDelete_finish_from (vectorBits xs) output
      (int ((xs.length - deleted : Nat) : Int)) (int ((kept.length + 1 : Nat) : Int))
      (int ((start + 1 : Nat) : Int)) (int ((start + 1 : Nat) : Int)) none (int 1)
      _ _ outState hcopy hlength hcleanup
    have hindexFinish : (copy_indices_finish (vectorBits xs)
        (int ((xs.length - deleted : Nat) : Int), none,
          int ((kept.length + 1 : Nat) : Int), int ((start + 1 : Nat) : Int))).run
        (dequeWordStore [word] spare) = (.ok output, outState) := by
      rw [copy_indices_finish_eq_mask]
      exact hfinish
    refine ⟨output, outState, copy_indices_after_done (vectorBits xs)
      (selected.map (fun i => int ((i + 1 : Nat) : Int))) _ _ _ _ _ _ hindexFinish, ?_⟩
    exact hbits
  | cons i rest ih =>
    have hi := hbound i List.mem_cons_self
    let added := (xs.drop start).take (i - start)
    let newKept := kept ++ added
    let newWord := rangeSingleCopyWord word kept.length start (i - start)
    let newBefore := before ++ [i]
    have hnewLen : newKept.length = kept.length + (i - start) := by
      simp only [newKept, added, List.length_append, List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega)]
    have hnewBalance : newKept.length + (deleted + 1) = i + 1 := by rw [hnewLen]; omega
    have hinvariant := scan_maskDelete_copy_invariant xs kept word start i hn (by omega)
      hi.1 (by omega) hprefix hsuffix
    have hnewPrefix : scan_maskDelete_prefix newWord newKept := hinvariant.1
    have hnewSuffix : scan_maskDelete_suffix newWord xs (i + 1) := by
      intro j hj hjlen
      exact hinvariant.2 j (by omega) hjlen
    have hrestOrdered : rest.Pairwise (· < ·) := (List.pairwise_cons.mp hordered).2
    have hrestBound : ∀ j ∈ rest, i + 1 ≤ j ∧ j < xs.length := by
      intro j hj
      have hjgreater := (List.pairwise_cons.mp hordered).1 j hj
      have hjbound := hbound j (List.mem_cons_of_mem i hj)
      omega
    have hnewDecomp : selected = newBefore ++ rest := by
      rw [hdecomp]
      simp only [newBefore, List.append_assoc, List.singleton_append]
    have hnext : (selected.map (fun j => int ((j + 1 : Nat) : Int)))[before.length + 1]?.map
        (fun value => (value, before.length + 1)) =
        rest.head?.map (fun j => (int ((j + 1 : Nat) : Int), newBefore.length)) := by
      have h := ctor_mask_iterator_next selected before rest i hdecomp
      simpa only [newBefore, List.length_append, List.length_singleton] using h
    have hstep := copy_indices_step_natural xs.length kept.length start i deleted before.length spare
      word (selected.map (fun j => int ((j + 1 : Nat) : Int)))
      (rest.head?.map (fun j => (int ((j + 1 : Nat) : Int), newBefore.length))) hn hbalance hi.1 hi.2 hnext
    have hstep' : (copy_indices_step (vectorBits xs).len (vectorBits xs).chunks
        (selected.map (fun j => int ((j + 1 : Nat) : Int))) ()
        (int ((xs.length - deleted : Nat) : Int), some (int ((i + 1 : Nat) : Int), before.length),
          int ((kept.length + 1 : Nat) : Int), int ((start + 1 : Nat) : Int))).run
        (dequeWordStore [word] spare) =
        (.ok (.yield (int ((xs.length - (deleted + 1) : Nat) : Int),
          rest.head?.map (fun j => (int ((j + 1 : Nat) : Int), newBefore.length)),
          int ((newKept.length + 1 : Nat) : Int), int ((i + 1 + 1 : Nat) : Int))),
          dequeWordStore [newWord] spare) := by
      rw [hnewLen]
      exact hstep
    obtain ⟨output, outState, hrun, hbits⟩ := ih newBefore newKept newWord (i + 1) (deleted + 1)
      (by omega) hnewBalance hrestOrdered hrestBound hnewDecomp hnewPrefix hnewSuffix
    refine ⟨output, outState, copy_indices_after_yield (vectorBits xs)
      (selected.map (fun j => int ((j + 1 : Nat) : Int))) _ _ _ _ _ output hstep' hrun, ?_⟩
    simpa only [newKept, added, scan_maskDelete_blocks, List.append_assoc] using hbits

/-- The exact frozen action succeeds for every increasing natural selection in a single-word input. -/
theorem copy_indices_selected_correct (xs : List Bool) (selected : List Nat)
    (hn : xs.length ≤ 64) (hordered : selected.Pairwise (· < ·))
    (hbound : ∀ i ∈ selected, i < xs.length) :
    ∃ output outState,
      (copy_delete_indices_action xs (selected.map (fun i => int ((i + 1 : Nat) : Int)))).run
        (initWords (encodeBits xs)) = (.ok output, outState) ∧
      bitValues outState output = scan_maskDelete_blocks xs selected 0 := by
  cases selected with
  | nil =>
    have he : copy_delete_indices_action xs [] = pure (vectorBits xs) := by
      unfold copy_delete_indices_action bitVectorDeleteAtIndices
      rfl
    have hr : (copy_delete_indices_action xs []).run (initWords (encodeBits xs)) =
        (.ok (vectorBits xs), initWords (encodeBits xs)) :=
      congrArg (fun action : BitMutationM BitVector => action.run (initWords (encodeBits xs))) he
    refine ⟨vectorBits xs, initWords (encodeBits xs), hr, ?_⟩
    simp only [scan_maskDelete_blocks, List.drop_zero]
    exact scalar_bits_initial xs [int xs.length] (by omega)
  | cons i rest =>
    have hi : i < xs.length := hbound i List.mem_cons_self
    have hrestOrdered : rest.Pairwise (· < ·) := (List.pairwise_cons.mp hordered).2
    have hrestBound : ∀ j ∈ rest, i + 1 ≤ j ∧ j < xs.length := by
      intro j hj
      have horder := (List.pairwise_cons.mp hordered).1 j hj
      have hb := hbound j (List.mem_cons_of_mem i hj)
      omega
    have htake : (xs.take i).length = i := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    obtain ⟨output, outState, hloop, hbits⟩ := copy_indices_loop_correct xs (i :: rest) rest [i]
      (xs.take i) (packedPrefix xs 0 64) (i + 1) 1 32 hn (by omega)
      (by rw [htake]) hrestOrdered hrestBound rfl
      (scan_maskDelete_initial_prefix xs i hn (by omega))
      (scan_maskDelete_initial_suffix xs (i + 1) hn)
    rw [htake] at hloop
    have hiNative : int 1 ≤ int ((i + 1 : Nat) : Int) ∧
        int ((i + 1 : Nat) : Int) ≤ int (Int.ofNat xs.length) := by
      change (int 1).val ≤ (int ((i + 1 : Nat) : Int)).val ∧
        (int ((i + 1 : Nat) : Int)).val ≤ (int xs.length).val
      rw [packedInt_val (i + 1) (by omega), packedInt_val xs.length (by omega)]
      change (1 : Int) ≤ (i + 1 : Nat) ∧ ((i + 1 : Nat) : Int) ≤ (xs.length : Int)
      omega
    have hnew : int xs.length - int 1 = int ((xs.length - 1 : Nat) : Int) :=
      frontPopLengthPred xs.length (by omega)
    have hinc : int ((i + 1 : Nat) : Int) + int 1 = int ((i + 1 + 1 : Nat) : Int) := by
      rw [packedInt_add]
      exact congrArg int (by omega)
    have haction : copy_delete_indices_action xs ((i :: rest).map (fun j => int ((j + 1 : Nat) : Int))) =
        copy_indices_after (vectorBits xs) ((i :: rest).map (fun j => int ((j + 1 : Nat) : Int)))
          (int ((xs.length - 1 : Nat) : Int), rest.head?.map (fun j => (int ((j + 1 : Nat) : Int), 1)),
            int ((i + 1 : Nat) : Int), int ((i + 1 + 1 : Nat) : Int)) := by
      rw [List.map_cons, copy_indices_action_nonempty xs _ _ hiNative]
      rw [hnew, hinc]
      simp only [List.head?_map, Option.map_map, Function.comp_def]
    have hrun := (congrArg (fun action : BitMutationM BitVector =>
      action.run (dequeWordStore [packedPrefix xs 0 64] 32)) haction).trans hloop
    have hsource := scan_maskDelete_initial_store xs (by omega) hn
    refine ⟨output, outState, ?_, ?_⟩
    · exact (congrArg (fun state =>
        (copy_delete_indices_action xs ((i :: rest).map (fun j => int ((j + 1 : Nat) : Int)))).run state)
        hsource.symm).trans hrun
    · simpa only [scan_maskDelete_blocks, List.drop_zero, Nat.sub_zero] using hbits

/-- Native-index decoding preserves the exact expected filtered sequence in the frozen target. -/
theorem copy_indices_decoded_expected (xs : List Bool) (indices : List I64)
    (hn : xs.length ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length))
    (hordered : indices.Pairwise (· < ·)) :
    scan_maskDelete_blocks xs (ctor_mask_decode_indices indices) 0 =
      (List.range xs.length).filterMap (fun j =>
        if indices.contains (int (Int.ofNat (j+1))) then none else some (xs.getD j false)) := by
  have hdecoded := ctor_mask_decode_pairwise indices xs.length hn hvalid hordered
  have hbound := ctor_mask_decode_bounds indices xs.length hn hvalid
  rw [ctor_mask_blocks_filterMap xs _ hdecoded hbound]
  apply copy_filterMap_congr
  intro j hj
  have hcontains := ctor_mask_decode_contains indices xs.length hn hvalid j (List.mem_range.mp hj)
  erw [hcontains]

/-- Every valid strictly sorted index list satisfies the frozen deletion contract
for a Boolean vector of at most one packed word, including empty inputs and deletion of every bit. -/
theorem copy_delete_indices_single_chunk_correct (xs : List Bool) (indices : List I64)
    (hn : xs.length ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length))
    (hordered : indices.Pairwise (· < ·)) :
    ∃ output outState,
      (copy_delete_indices_action xs indices).run (initWords (encodeBits xs)) = (.ok output, outState) ∧
      bitValues outState output = (List.range xs.length).filterMap (fun j =>
        if indices.contains (int (Int.ofNat (j+1))) then none else some (xs.getD j false)) := by
  have hdecoded := ctor_mask_decode_pairwise indices xs.length hn hvalid hordered
  have hbound := ctor_mask_decode_bounds indices xs.length hn hvalid
  have hroundtrip := ctor_mask_decode_roundtrip indices xs.length hn hvalid
  obtain ⟨output, outState, hrun, hbits⟩ := copy_indices_selected_correct xs
    (ctor_mask_decode_indices indices) hn hdecoded hbound
  refine ⟨output, outState, ?_, ?_⟩
  · exact (congrArg (fun values => (copy_delete_indices_action xs values).run
      (initWords (encodeBits xs))) hroundtrip.symm).trans hrun
  · exact hbits.trans (copy_indices_decoded_expected xs indices hn hvalid hordered)

/-- The frozen success-versus-error observation, kept under one explicit head for transport. -/
def copy_indices_outcome (expected : List Bool) (result : Except Error BitVector × State) : Prop :=
  match result.1 with
  | .ok output => bitValues result.2 output = expected
  | .error _ => False

/-- The exact frozen sorted-index observation is true throughout the complete single-word domain. -/
theorem copy_delete_indices_single_chunk_observation (xs : List Bool) (indices : List I64)
    (hn : xs.length ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length))
    (hordered : indices.Pairwise (· < ·)) :
    copy_indices_outcome
      ((List.range xs.length).filterMap (fun j =>
        if indices.contains (int (Int.ofNat (j+1))) then none else some (xs.getD j false)))
      ((copy_delete_indices_action xs indices).run (initWords (encodeBits xs))) := by
  obtain ⟨output, outState, hrun, hbits⟩ := copy_delete_indices_single_chunk_correct xs indices hn hvalid hordered
  exact Eq.mpr (congrArg (copy_indices_outcome
    ((List.range xs.length).filterMap (fun j =>
      if indices.contains (int (Int.ofNat (j+1))) then none else some (xs.getD j false)))) hrun) hbits
end JuliaLean.ChatGPT.Batch5.Group2
end

section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch5.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Replacing a full aligned word discards every original destination bit. -/
theorem copyAudit_full_paste (destination source : U64) :
    or_int (and_int destination (u64 0)) (and_int source u64Max) = source := by
  apply packedBit_ext
  intro bit hbit
  simp only [packedBit_or, scalar_packedBit_and, packedBit_zero, packedBit_max,
    decide_eq_true hbit, Bool.and_false, Bool.and_true, Bool.false_or]

/-- The aligned source gather reads exactly its selected word. -/
theorem copyAudit_glue_aligned (source : Nat) (chunk last : I64) (word : U64) (s : State)
    (hr : (mutableGet source chunk).run s = (.ok word, s)) :
    (glueSrcBitChunks source chunk last u64Max (int 0)).run s = (.ok word, s) := by
  have he : and_int word u64Max = word := by
    apply packedBit_ext
    intro bit hbit
    simp only [scalar_packedBit_and, packedBit_max, decide_eq_true hbit, Bool.and_true]
  have hz : ¬ (int 0 : I64) > int 0 := by decide
  simp only [glueSrcBitChunks, shape_run_bind, hr, hz, and_false, ite_false,
    he, concat_lshr_zero, shape_run_pure]

/-- This exact run rule exposes the repeated first-source read in a three-word
    aligned forward copy. The theorem describes the frozen implementation. -/
theorem copyAudit_three_aligned_from_runs (dest source : Nat)
    (s s1 s2 out : State) (a aAgain c oldFirst oldLast : U64)
    (hsrc0 : (mutableGet source (int 1)).run s = (.ok a, s))
    (hdest0 : (mutableGet dest (int 1)).run s = (.ok oldFirst, s))
    (hwrite0 : (mutableSet dest a (int 1)).run s = (.ok (), s1))
    (hsrc1 : (mutableGet source (int 1)).run s1 = (.ok aAgain, s1))
    (hwrite1 : (mutableSet dest aAgain (int 2)).run s1 = (.ok (), s2))
    (hsrc2 : (mutableGet source (int 3)).run s2 = (.ok c, s2))
    (hdest2 : (mutableGet dest (int 3)).run s2 = (.ok oldLast, s2))
    (hwrite2 : (mutableSet dest c (int 3)).run s2 = (.ok (), out)) :
    (copyChunks dest (int 1) source (int 1) (int 192)).run s = (.ok (), out) := by
  have hshr (word : U64) : lshr_int word (int 64) = u64 0 := copyPairRightFull word
  have hf : ¬ (dest = source ∧ (int 1 : I64) > int 1) := by
    intro h
    exact (by decide : ¬ (int 1 : I64) > int 1) h.2
  have hg0 := copyAudit_glue_aligned source (int 1) (int 3) a s hsrc0
  have hg1 := copyAudit_glue_aligned source (int 1) (int 3) aAgain s1 hsrc1
  have hg2 := copyAudit_glue_aligned source (int 3) (int 3) c s2 hsrc2
  simp only [copyChunks, hf, dite_false,
    show (int 192 == int 0) = false from rfl, Bool.false_eq_true, ite_false,
    show getChunksId (int 1) = (int 1, int 0) from rfl,
    show getChunksId (int 1 + int 192 - int 1) = (int 3, int 63) from rfl,
    show int 3 - int 1 = int 2 from rfl,
    show (int 2 == int 0) = false from rfl,
    show shl_int u64Max (int 0) = u64Max from rfl,
    show not_int u64Max = u64 0 from rfl,
    show shl_int u64Max (int 63 + int 1) = u64 0 from rfl,
    show intRange (int 1) (int 1) = [int 1] from rfl,
    shape_run_bind, hg0, hdest0, concat_shl_zero,
    show not_int (u64 0) = u64Max from rfl, copyAudit_full_paste,
    hwrite0, List.forIn_cons, List.forIn_nil,
    show int 2 - int 1 = int 1 from rfl,
    show int 1 + int 1 = int 2 from rfl,
    show int 64 - int 0 = int 64 from rfl,
    hg1, hshr, reverseCoreOrZeroLeft, hwrite1,
    show int 1 + int 2 = int 3 from rfl,
    show (int 3 : I64) ≥ int 3 from by decide, ite_true,
    hg2, hdest2, hwrite2, shape_run_pure]

/-- Every aligned self-copy of exactly three full words overwrites its second
    word with its first word in the frozen implementation. -/
theorem copyAudit_three_words (a b c : U64) (spare : Nat) :
    (copyChunks 0 (int 1) 0 (int 1) (int 192)).run
      (dequeWordStore [a,b,c] spare) =
      (.ok (), dequeWordStore [a,a,c] spare) := by
  apply copyAudit_three_aligned_from_runs 0 0
    (dequeWordStore [a,b,c] spare) (dequeWordStore [a,b,c] spare)
    (dequeWordStore [a,a,c] spare) (dequeWordStore [a,a,c] spare)
    a a c a c
  · exact dequeWordRead [a,b,c] spare 0 (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordRead [a,b,c] spare 0 (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordSet [a,b,c] spare 0 a (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordRead [a,b,c] spare 0 (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordSet [a,b,c] spare 1 a (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordRead [a,a,c] spare 2 (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordRead [a,a,c] spare 2 (by change 3 ≤ _; decide) (by change _ < 3; decide)
  · exact dequeWordSet [a,a,c] spare 2 c (by change 3 ≤ _; decide) (by change _ < 3; decide)

/-- The three-word frozen self-copy is unchanged exactly when its first two
    source words already coincide. -/
theorem copyAudit_three_words_identity_iff (a b c : U64) (spare : Nat) :
    (copyChunks 0 (int 1) 0 (int 1) (int 192)).run (dequeWordStore [a,b,c] spare) =
      (.ok (), dequeWordStore [a,b,c] spare) ↔ a = b := by
  rw [copyAudit_three_words]
  constructor
  · intro he
    have hs := congrArg (fun p : Except Error Unit × State =>
      (((p.2.memories[0]?.getD [])[1]?.getD none).getD (u64 0))) he
    exact hs
  · intro he
    rw [he]

/-- Even before the forward interior-loop issue arises, growing an empty chunk
    vector by two words leaves its first primitive slot unassigned in the model. -/
theorem copyAudit_append_empty65_error :
    ((bitVectorAppend (fun a b => pure (a + b))
      (⟨0, int 0, [int 0]⟩ : BitVector)
      (⟨1, int 65, [int 65]⟩ : BitVector)).run
      (MutableMemory.initialMany [[], [some (u64 0), some (u64 0)]])).1 =
        .error .undefinedReference := by
  unfold bitVectorAppend
  simp only [copyChunks]
  rfl

/-- Prepending into the same two-word fresh-storage case reaches that same
    primitive unassigned-slot error in the frozen model. -/
theorem copyAudit_prepend_empty65_error :
    ((bitVectorPrepend (fun a b => pure (a + b))
      (⟨0, int 0, [int 0]⟩ : BitVector)
      (⟨1, int 65, [int 65]⟩ : BitVector)).run
      (MutableMemory.initialMany [[], [some (u64 0), some (u64 0)]])).1 =
        .error .undefinedReference := by
  unfold bitVectorPrepend
  simp only [copyChunks]
  rfl

/-- The two fresh-storage errors are reached by the canonical public input
    encoding used in the unchanged append/prepend target. -/
theorem copyAudit_append_prepend_canonical65 :
    let right := List.replicate 65 false
    let a := vectorBits []
    let b : BitVector := ⟨1, int right.length, [int right.length]⟩
    let s := MutableMemory.initialMany [(encodeBits []).map some, (encodeBits right).map some]
    ((bitVectorAppend (fun x y => pure (x + y)) a b).run s).1 = .error .undefinedReference ∧
      ((bitVectorPrepend (fun x y => pure (x + y)) a b).run s).1 = .error .undefinedReference := by
  dsimp only
  rw [fillFalseEncoding]
  change
    ((bitVectorAppend (fun a b => pure (a + b))
      (⟨0, int 0, [int 0]⟩ : BitVector)
      (⟨1, int 65, [int 65]⟩ : BitVector)).run
      (MutableMemory.initialMany [[], [some (u64 0), some (u64 0)]])).1 =
        .error .undefinedReference ∧
    ((bitVectorPrepend (fun a b => pure (a + b))
      (⟨0, int 0, [int 0]⟩ : BitVector)
      (⟨1, int 65, [int 65]⟩ : BitVector)).run
      (MutableMemory.initialMany [[], [some (u64 0), some (u64 0)]])).1 =
        .error .undefinedReference
  exact ⟨copyAudit_append_empty65_error, copyAudit_prepend_empty65_error⟩
end JuliaLean.ChatGPT.Batch5.Group1
end



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

/-- Physical memory windows do not overlap. Different headers of the same
memory are included whenever their windows are disjoint. -/
def DisjointChunkWindows (s : MutableMemory U64) (destination source : Nat) : Prop :=
  ∀ (d h : MutableVector), s.arrays[destination]? = some d →
    s.arrays[source]? = some h →
    d.reference.1 ≠ h.reference.1 ∨
      d.reference.2.val + d.size.val ≤ h.reference.2.val ∨
      h.reference.2.val + h.size.val ≤ d.reference.2.val

/-- The too-long-source BoundsError precedes all heap access for every input,
and successful results retain the destination header. Every run, including an
error after partial copying or an overlapping-alias run, preserves metadata and
all cells outside the valid physical destination chunk window. Logical lengths,
ranks, chunk counts and old source contents are otherwise unrestricted.
Julia source: base/bitarray.jl:429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:1043-1051; frame/error-order invariant. -/
def CopytoBoundsAndGlobalFrame : Prop :=
  ∀ (N M : Nat) (dest : BitArray N) (src : BitArray M) (s : MutableMemory U64),
    let result := (JuliaLean.base.bitarray.Models1Group15.copyto dest src).run s
    (src.len.val > dest.len.val → result.1 = .error .bounds ∧ result.2 = s) ∧
    (match result.1 with
     | .ok returned => returned = dest ∧ src.len.val ≤ dest.len.val
     | .error _ => True) ∧
    DestinationFrame s result.2 dest.chunks

/-- Copying from the very same chunk vector cannot change the heap, even if
logical lengths or ranks differ after reshaping/resizing aliases. Readable
storage guarantees successful return whenever the length check passes; an
unassigned cell can instead stop the read, still without mutation.
Julia source: base/bitarray.jl:429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Source invariant; the general documentation does not promise arbitrary
snapshot behavior for distinct overlapping headers. -/
def CopytoSameChunksUnchanged : Prop :=
  ∀ (N M : Nat) (dest : BitArray N) (src : BitArray M) (s : MutableMemory U64),
    dest.chunks = src.chunks → s.validVector dest.chunks →
    let result := (JuliaLean.base.bitarray.Models1Group15.copyto dest src).run s
    result.2 = s ∧
    (if src.len.val > dest.len.val then result.1 = .error .bounds
     else ReadableChunks s dest.chunks → result.1 = .ok dest)

/-- On ordinary constructible packed arrays whose physical windows are
disjoint, copyto! copies all source logical elements into the destination
prefix, leaves its remaining elements unchanged, preserves source storage and
zero padding, and returns the destination. Too-long inputs raise BoundsError
before mutation. The general copy documentation explicitly warns about shared
memory; it does not promise memmove behavior for distinct overlapping windows.
Julia source: base/bitarray.jl:429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:1043-1051;
base/Base_compiler.jl:222-225 (aliasing warning). -/
def CopytoNonoverlappingValues : Prop :=
  ∀ (N M : Nat) (dest : BitArray N) (src : BitArray M) (s : MutableMemory U64),
    ConsistentPackedArray s dest → ConsistentPackedArray s src →
    DisjointChunkWindows s dest.chunks src.chunks →
    let result := (JuliaLean.base.bitarray.Models1Group15.copyto dest src).run s
    if src.len.val > dest.len.val then result.1 = .error .bounds ∧ result.2 = s
    else result.1 = .ok dest ∧ DestinationFrame s result.2 dest.chunks ∧
      ConsistentPackedArray result.2 dest ∧
      result.2.contents src.chunks = s.contents src.chunks ∧
      (∀ i : Nat, i < dest.len.val.toNat →
        PackedBitValue result.2 dest i =
          if i < src.len.val.toNat then PackedBitValue s src i else PackedBitValue s dest i)

/-- Mathematical interval condition for a checked packed copy. A zero count
accepts arbitrary offsets; a positive count names complete one-based source
and destination intervals. No wrapped implementation intermediate appears. -/
def PackedCopyInterval {N M : Nat} (dest : BitArray N) (doffs : I64)
    (src : BitArray M) (soffs n : I64) : Prop :=
  n.val = 0 ∨ (0 < n.val ∧ 1 ≤ doffs.val ∧ 1 ≤ soffs.val ∧
    doffs.val + n.val - 1 ≤ dest.len.val ∧ soffs.val + n.val - 1 ≤ src.len.val)

/-- Snapshot content and error contract for native-offset packed copying.
The snapshot promise is used for disjoint windows or the explicit same-chunk
alias case, not arbitrary distinct overlapping array headers. -/
def PackedCopyOutcome {N M : Nat} (dest : BitArray N) (doffs : I64)
    (src : BitArray M) (soffs n : I64) (before : MutableMemory U64)
    (result : Except JuliaLean.base.array.Error (BitArray N) × MutableMemory U64) : Prop :=
  (PackedCopyInterval dest doffs src soffs n →
    result.1 = .ok dest ∧ DestinationFrame before result.2 dest.chunks ∧
    ConsistentPackedArray result.2 dest ∧
    (n.val = 0 → result.2 = before) ∧
    (∀ i : Nat, i < dest.len.val.toNat →
      PackedBitValue result.2 dest i =
        if doffs.val - 1 ≤ (i : Int) ∧ (i : Int) < doffs.val - 1 + n.val then
          PackedBitValue before src ((i : Int) - doffs.val + soffs.val).toNat
        else PackedBitValue before dest i)) ∧
  (¬ PackedCopyInterval dest doffs src soffs n → result.2 = before ∧
    result.1 = .error (if n.val < 0 then
      .argument "Number of elements to copy must be non-negative." else .bounds))

/-- Zero-count, negative-count and nonpositive-offset checks happen before any
heap access. In particular zero count succeeds even with invalid offsets or
missing chunk handles, and a negative count retains its ArgumentError priority.
Julia source: base/bitarray.jl:454-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:282-287; source error-order invariant.
Useful partial result: native Int offsets and packed sources only. -/
def PackedOffsetsEarlyErrors : Prop :=
  ∀ (N M : Nat) (dest : BitArray N) (doffs : I64) (src : BitArray M)
    (soffs n : I64) (s : MutableMemory U64),
    let result := (JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets dest doffs src soffs n).run s
    if n.val = 0 then result.1 = .ok dest ∧ result.2 = s
    else if n.val < 0 then result.1 = .error
      (.argument "Number of elements to copy must be non-negative.") ∧ result.2 = s
    else if soffs.val < 1 ∨ doffs.val < 1 then result.1 = .error .bounds ∧ result.2 = s
    else DestinationFrame s result.2 dest.chunks

/-- Native-offset packed copying uses mathematical index intervals, preserves
all destination bits outside the requested slice and zero padding, and handles
both disjoint storage and same-chunk overlap using the source snapshot. Invalid
checked intervals produce the appropriate error without mutation; unsafe_copyto!
is required to succeed only on the documented in-bounds domain.
Julia source: base/bitarray.jl:449-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:265-287; same-chunk overlap branch at
base/bitarray.jl:135-141,189-233. Useful partial result only: generic Integer
conversions and Array sources remain outside these models. -/
def PackedOffsetsValues : Prop :=
  ∀ (N M : Nat) (dest : BitArray N) (doffs : I64) (src : BitArray M)
    (soffs n : I64) (s : MutableMemory U64),
    ConsistentPackedArray s dest → ConsistentPackedArray s src →
    (dest.chunks = src.chunks ∨ DisjointChunkWindows s dest.chunks src.chunks) →
    PackedCopyOutcome dest doffs src soffs n s
      ((JuliaLean.base.bitarray.Models1Group15.copytoPackedInt dest doffs src soffs n).run s) ∧
    PackedCopyOutcome dest doffs src soffs n s
      ((JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets dest doffs src soffs n).run s) ∧
    (PackedCopyInterval dest doffs src soffs n →
      PackedCopyOutcome dest doffs src soffs n s
        ((JuliaLean.base.bitarray.Models1Group15.unsafeCopytoPacked dest doffs src soffs n).run s))

/-- Every logical element is backed by a valid readable chunk window. Extra
chunks left by a resized alias are permitted; exact packed length and zero
padding are not assumed for concatenation. -/
def ReadablePackedExtent (state : MutableMemory U64) (header : BitVector) : Prop :=
  0 ≤ header.len.val ∧ state.validVector header.chunks ∧
  header.len.val.toNat ≤ 64 * (state.contents header.chunks).length ∧
  ReadableChunks state header.chunks

/-- Concatenation's source snapshot is supported for the explicit same-chunk
alias case or separate backing memory objects. Merely disjoint current windows
in the same memory are insufficient: growth may expand or move the target into
the source window. Other alias configurations retain the global frame below. -/
def ConcatStorageIndependent (state : MutableMemory U64)
    (target source : BitVector) : Prop :=
  target.chunks = source.chunks ∨
    ∃ targetHeader sourceHeader : MutableVector,
      state.arrays[target.chunks]? = some targetHeader ∧
      state.arrays[source.chunks]? = some sourceHeader ∧
      targetHeader.reference.1 ≠ sourceHeader.reference.1

/-- Empty items return before chunk access; checked-add overflow returns before
any mutation. All other executions, including malformed or alias-underbacked
storage and partial-copy failures, retain the full object/memory frame. Successful
return is the original target identity with the summed length committed.
Julia source: base/bitarray.jl:757-772,777-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:1384-1420,1449-1478; error/frame invariants. -/
def AppendPrependEarlyErrorsAndFrame : Prop :=
  ∀ (runtime : AllocationData) (target items : Ref 1) (B I : BitVector)
    (state : ObjectState), ObjectContains state target B → ObjectContains state items I →
    ∀ result ∈ [
      (JuliaLean.base.bitarray.Models1Group15.append runtime target items).run state,
      (JuliaLean.base.bitarray.Models1Group15.prepend runtime target items).run state],
      let sum := B.len.val + I.len.val
      VectorMutationFrame state result.2 target B (int sum) ∧
      (if I.len.val = 0 then result.1 = .ok target ∧ result.2 = state
       else if sum < IntTy.min .i64 ∨ IntTy.max .i64 < sum then
         result.1 = .error .overflow ∧ result.2 = state
       else match result.1 with
         | .ok returned => returned = target ∧
             ∃ updated : BitVector, ObjectContains result.2 target updated ∧ updated.len.val = sum
         | .error _ => True)

/-- An independent element-by-element concatenation specification. Reads on the
right-hand side are from the pre-call state, including self-concatenation. -/
def ConcatenatedValues (front : Bool) (before after : MutableMemory U64)
    (B I updated : BitVector) : Prop :=
  updated.len.val = B.len.val + I.len.val ∧
  ∀ position : Nat, position < updated.len.val.toNat →
    PackedBitValue after updated position =
      if front then
        if position < I.len.val.toNat then PackedBitValue before I position
        else PackedBitValue before B (position - I.len.val.toNat)
      else
        if position < B.len.val.toNat then PackedBitValue before B position
        else PackedBitValue before I (position - B.len.val.toNat)

/-- Success and both native size-failure classes are required on their exact
mathematical domains. A spurious error cannot satisfy the success branch. -/
def ConcatValueOutcome (front : Bool) (_runtime : AllocationData)
    (target : Ref 1) (B I : BitVector) (before : ObjectState)
    (result : Except JuliaLean.base.array.Error (Ref 1) × ObjectState) : Prop :=
  let sum := B.len.val + I.len.val
  if IntTy.max .i64 < sum then
    result.1 = .error .overflow ∧ result.2 = before
  else if GrowthExceedsNativeByteLimit before.memory B.chunks ((sum.toNat + 63) / 64) then
    result.1 = .error (.argument JuliaLean.base.array.genericMemorySizeMessage) ∧ result.2 = before
  else
    result.1 = .ok target ∧
    ∃ updated : BitVector, ObjectContains result.2 target updated ∧
      updated.chunks = B.chunks ∧ updated.dims = B.dims ∧
      ReadablePackedExtent result.2.memory updated ∧
      ConcatenatedValues front before.memory result.2.memory B I updated

/-- On full-size native readable inputs, append/prepend return exactly the
corresponding concatenation, preserve target identity and update its actual
mutable header. Includes self-append/self-prepend and different BitArray headers
sharing one chunk vector, even with unequal logical lengths or spare chunks.
All capacities and offsets allowed by native memory allocation are quantified;
checked length overflow and byte-limit growth errors are classified explicitly.
Distinct backing memories support an independent source snapshot. The separate
global frame covers all other sharing, consistent with Base's alias warning.
Julia source: base/bitarray.jl:757-772,777-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:1384-1420,1449-1478;
base/Base_compiler.jl:222-225; native allocation: src/genericmemory.c:55-73. -/
def AppendPrependConcatenationAndNativeLimits : Prop :=
  ∀ (runtime : AllocationData) (target items : Ref 1) (B I : BitVector)
    (state : ObjectState), ObjectContains state target B → ObjectContains state items I →
    AllocationInput runtime state.memory → NativeRawChunkMemory state.memory →
    ReadablePackedExtent state.memory B → ReadablePackedExtent state.memory I →
    ConcatStorageIndependent state.memory B I →
    ConcatValueOutcome false runtime target B I state
      ((JuliaLean.base.bitarray.Models1Group15.append runtime target items).run state) ∧
    ConcatValueOutcome true runtime target B I state
      ((JuliaLean.base.bitarray.Models1Group15.prepend runtime target items).run state)

/-- A source whose chunk vector was shrunk below its logical length must fail
with BoundsError when copied. With enough target capacity, the new target len
has already been committed, even though copying fails. Prepend's initial shift
and any earlier copy writes are not rolled back; the global frame remains valid.
This includes arbitrary readable underlying memory aliases and offset windows.
Julia source: base/bitarray.jl:768-770,789-792 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Source invariant: mutation before unsafe copying; alias behavior warning at
base/Base_compiler.jl:222-225. -/
def AppendPrependUnderbackedSourceKeepsLength : Prop :=
  ∀ (runtime : AllocationData) (target items : Ref 1) (B I : BitVector)
    (state : ObjectState), ObjectContains state target B → ObjectContains state items I →
    0 ≤ B.len.val → 0 < I.len.val → B.len.val + I.len.val ≤ IntTy.max .i64 →
    NativeRawChunkMemory state.memory →
    state.memory.validVector B.chunks → state.memory.validVector I.chunks →
    ((B.len.val + I.len.val).toNat + 63) / 64 ≤ (state.memory.contents B.chunks).length →
    64 * (state.memory.contents I.chunks).length < I.len.val.toNat →
    ∀ result ∈ [
      (JuliaLean.base.bitarray.Models1Group15.append runtime target items).run state,
      (JuliaLean.base.bitarray.Models1Group15.prepend runtime target items).run state],
      result.1 = .error .bounds ∧
      ∃ updated : BitVector, ObjectContains result.2 target updated ∧
        updated.len.val = B.len.val + I.len.val ∧ updated.chunks = B.chunks ∧
        updated.dims = B.dims ∧ VectorMutationFrame state result.2 target B (int updated.len.val)
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean.Proofs.base.int JuliaLean.C

def bh_pack_nat (n : Nat) : Nat :=
  let n := n ||| (n / 2 ^ 7)
  let n := n ||| (n / 2 ^ 14)
  let n := n ||| (n / 2 ^ 28)
  n % 2 ^ 8

theorem bh_pattern_or (a b : U64) :
    pattern (or_int a b) = pattern a ||| pattern b := by
  simp only [or_int, jlOrInt, pattern_toJInt, BitVec.toNat_or, ← pattern_fromJInt]

theorem bh_shift7 (word : U64) :
    pattern (lshr_Int word (int 7)) = pattern word / 2 ^ 7 := by
  exact pattern_lshr_Int word (int 7) (by decide)

theorem bh_shift14 (word : U64) :
    pattern (lshr_Int word (int 14)) = pattern word / 2 ^ 14 := by
  exact pattern_lshr_Int word (int 14) (by decide)

theorem bh_shift28 (word : U64) :
    pattern (lshr_Int word (int 28)) = pattern word / 2 ^ 28 := by
  exact pattern_lshr_Int word (int 28) (by decide)

theorem bh_pack_pattern (word : U64) :
    pattern (JuliaLean.base.bitarray.Models1Group15.pack8bools word) =
      bh_pack_nat (pattern word) := by
  unfold JuliaLean.base.bitarray.Models1Group15.pack8bools
  change pattern (band _ (u64 255)) = _
  rw [pattern_band]
  simp only [bh_pattern_or, bh_shift7, bh_shift14, bh_shift28]
  change _ &&& (2 ^ 8 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem bh_range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem bh_pack_nat_bit (n i : Nat) (hi : i < 8) :
    (bh_pack_nat n).testBit i =
      (List.range 8).any (fun k => n.testBit (i + 7 * k)) := by
  unfold bh_pack_nat
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_or,
    Nat.testBit_div_two_pow, bh_range8, List.any_cons, List.any_nil,
    Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Bool.or_false,
    Bool.or_assoc]

theorem bh_bit_weight (n k : Nat) :
    (if n.testBit k then (2 : Int) ^ k else 0) =
      (n / 2 ^ k % 2 : Nat) * (2 : Int) ^ k := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h
  · simp only [h, Nat.zero_ne_one, decide_false, Bool.false_eq_true,
      ite_false, Int.natCast_zero, Int.zero_mul]
  · simp only [h, decide_true, ite_true, Int.natCast_one, Int.one_mul]

theorem bh_byte_reconstruct (n : Nat) (hn : n < 256) :
    (n : Int) = (List.range 8).foldl
      (fun total bit => total + if n.testBit bit then (2 : Int) ^ bit else 0) 0 := by
  simp only [bh_range8, List.foldl_cons, List.foldl_nil, bh_bit_weight,
    Int.reducePow, Nat.reducePow, Nat.div_one, Int.zero_add, Int.mul_one]
  omega

theorem bh_int_bit (word : U64) (k : Nat) :
    ((word.val / (2 : Int) ^ k) % 2 == 1) = (pattern word).testBit k := by
  rw [pattern_of_nonneg word word.property.1, Nat.testBit_eq_decide_div_mod_eq]
  have hw : (word.val.toNat : Int) = word.val := Int.toNat_of_nonneg word.property.1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← hw]
  change ((word.val.toNat / 2 ^ k % 2 : Nat) : Int) = 1 ↔ _
  exact Int.ofNat_inj

theorem bh_fold_bits_eq (indices : List Nat) (a b : Nat → Bool)
    (h : ∀ i ∈ indices, a i = b i) (start : Int) :
    indices.foldl (fun total bit => total + if a bit then (2 : Int) ^ bit else 0) start =
    indices.foldl (fun total bit => total + if b bit then (2 : Int) ^ bit else 0) start := by
  induction indices generalizing start with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, List.foldl_cons, h i (List.mem_cons_self ..)]
    apply ih
    intro j hj
    exact h j (List.mem_cons_of_mem _ hj)
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

def rc_copyError (e : Error) : Prop := e = .bounds ∨ e = .undefinedReference

def rc_actionPost {α : Type} (P : State → Prop) (Q : α → Prop)
    (action : BitMutationM α) : Prop :=
  ∀ s, P s → P (action.run s).2 ∧
    match (action.run s).1 with
    | .ok value => Q value
    | .error error => rc_copyError error

theorem rc_ap_pure {α : Type} (P : State → Prop) (Q : α → Prop) (x : α)
    (hx : Q x) : rc_actionPost P Q (pure x) := by
  intro s hs
  exact ⟨hs, hx⟩

theorem rc_ap_bind {α β : Type} (P : State → Prop) (Q : β → Prop)
    (action : BitMutationM α) (next : α → BitMutationM β)
    (ha : rc_actionPost P (fun _ => True) action)
    (hn : ∀ value, rc_actionPost P Q (next value)) :
    rc_actionPost P Q (action >>= next) := by
  intro s hs
  have hfirst := ha s hs
  rw [rc_run_bind]
  cases hrun : action.run s with
  | mk result after =>
    rw [hrun] at hfirst
    cases result with
    | error error => exact hfirst
    | ok value => exact hn value after hfirst.1

theorem rc_ap_forIn {α β : Type} (P : State → Prop) (xs : List α)
    (initial : β) (step : α → β → BitMutationM (ForInStep β))
    (hstep : ∀ x acc, rc_actionPost P (fun _ => True) (step x acc)) :
    rc_actionPost P (fun _ => True) (forIn xs initial step) := by
  induction xs generalizing initial with
  | nil => exact rc_ap_pure P (fun _ => True) initial True.intro
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply rc_ap_bind P (fun _ => True) _ _ (hstep x initial)
    intro next
    cases next with
    | done result => exact rc_ap_pure P (fun _ => True) result True.intro
    | yield result => exact ih result

theorem rc_ap_length (P : State → Prop) (a : Nat) :
    rc_actionPost P (fun _ => True) (mutableLength a) := by
  intro s hs
  cases h : s.arrays[a]? with
  | none =>
    simp only [mutableLength, mutableVector, rc_run_bind, rc_run_get, h, rc_run_throw]
    exact ⟨hs, Or.inl rfl⟩
  | some header =>
    simp only [mutableLength, mutableVector, rc_run_bind, rc_run_get, h, rc_run_pure]
    exact ⟨hs, True.intro⟩

theorem rc_ap_get (P : State → Prop) (a : Nat) (i : I64) :
    rc_actionPost P (fun _ => True) (mutableGet a i) := by
  intro s hs
  rw [sp_mutableGet_run]
  refine ⟨hs, ?_⟩
  cases ha : s.arrays[a]? with
  | none => exact Or.inl rfl
  | some header =>
    by_cases hb : 1 ≤ i.val ∧ i.val ≤ header.size.val
    · simp only [ha, hb, and_self, ite_true]
      cases hm : s.memories[header.reference.1]? with
      | none =>
        simp only [hm]
        exact Or.inl rfl
      | some slots =>
        simp only [hm]
        cases hi : slots[(header.reference.2.val + i.val - 2).toNat]? with
        | none =>
          simp only [hi]
          exact Or.inl rfl
        | some value =>
          cases value with
          | none => exact Or.inr rfl
          | some word => trivial
    · simp only [ha, hb, ite_false]
      exact Or.inl rfl

theorem rc_copyto_post {N M : Nat} (P : State → Prop)
    (dest : BitArray N) (src : BitArray M)
    (hset : ∀ word index, rc_actionPost P (fun _ => True) (mutableSet dest.chunks word index)) :
    rc_actionPost P (fun output => output = dest) (copyto dest src) := by
  unfold copyto bitArrayCopyto
  by_cases hlong : src.len > dest.len
  · simp only [hlong, ite_true]
    intro s hs
    simp only [rc_run_bind, rc_run_throw]
    exact ⟨hs, Or.inl rfl⟩
  · simp only [hlong, ite_false]
    apply rc_ap_bind P _ _ _ (rc_ap_length P dest.chunks)
    intro destN
    apply rc_ap_bind P _ _ _ (rc_ap_length P src.chunks)
    intro srcN
    let nc := if destN < srcN then destN else srcN
    by_cases hz : nc == int 0
    · dsimp only [nc] at hz
      simp only [hz, ite_true]
      exact rc_ap_pure P _ dest rfl
    · dsimp only [nc] at hz
      simp only [hz, Bool.false_eq_true, ite_false]
      apply rc_ap_bind P _ _ _ (rc_ap_forIn P _ PUnit.unit _ (by
        intro i _
        apply rc_ap_bind P _ _ _ (rc_ap_get P src.chunks i)
        intro word
        apply rc_ap_bind P _ _ _ (hset word i)
        intro _
        exact rc_ap_pure P _ (ForInStep.yield PUnit.unit) True.intro))
      intro _
      by_cases he : src.len == dest.len
      · simp only [he, ite_true]
        apply rc_ap_bind P _ _ _ (rc_ap_get P src.chunks nc)
        intro word
        apply rc_ap_bind P _ _ _ (hset word nc)
        intro _
        exact rc_ap_pure P _ dest rfl
      · simp only [he, Bool.false_eq_true, ite_false]
        apply rc_ap_bind P _ _ _ (rc_ap_get P dest.chunks nc)
        intro oldD
        apply rc_ap_bind P _ _ _ (rc_ap_get P src.chunks nc)
        intro oldS
        apply rc_ap_bind P _ _ _ (hset _ nc)
        intro _
        exact rc_ap_pure P _ dest rfl
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15

set_option backward.isDefEq.respectTransparency false

theorem bh_shape_preserves_valid {before after : MutableMemory U64}
    (hshape : FixedHeapShape before after) (handle : Nat)
    (hvalid : before.validVector handle) : after.validVector handle := by
  unfold MutableMemory.validVector at hvalid ⊢
  rw [hshape.1]
  cases ha : before.arrays[handle]? with
  | none => simp only [ha] at hvalid
  | some header =>
    simp only [ha] at hvalid ⊢
    cases hm : before.memories[header.reference.1]? with
    | none => simp only [hm] at hvalid
    | some slots =>
      simp only [hm] at hvalid
      have hlength := hshape.2.2 header.reference.1
      rw [hm] at hlength
      cases hn : after.memories[header.reference.1]? with
      | none =>
        simp only [hn, Option.map_none, Option.map_some] at hlength
        cases hlength
      | some newSlots =>
        simp only [hn, Option.map_some, Option.some.injEq] at hlength
        simp only [hn, hlength]
        exact hvalid

theorem bh_frame_trans {before middle after : MutableMemory U64} {handle : Nat}
    (hfirst : DestinationFrame before middle handle)
    (hsecond : DestinationFrame middle after handle) :
    DestinationFrame before after handle := by
  refine ⟨bh_shape_trans hfirst.1 hsecond.1, ?_⟩
  intro header hheader hvalid memory position houtside
  have hmid : middle.arrays[handle]? = some header := by rw [hfirst.1.1, hheader]
  rw [hsecond.2 header hmid (bh_shape_preserves_valid hfirst.1 handle hvalid)
    memory position houtside]
  exact hfirst.2 header hheader hvalid memory position houtside

theorem bh_set_errors (s : MutableMemory U64) (handle : Nat) (word : U64) (index : I64) :
    match ((mutableSet handle word index).run s).1 with
    | .ok _ => True
    | .error e => rc_copyError e := by
  rw [sp_mutableSet_run]
  cases ha : s.arrays[handle]? with
  | none => exact Or.inl rfl
  | some header =>
    simp only [ha]
    by_cases hb : 1 ≤ index.val ∧ index.val ≤ header.size.val
    · simp only [hb, and_self, ite_true]
      cases hm : s.memories[header.reference.1]? with
      | none => exact Or.inl rfl
      | some slots =>
        simp only [hm]
        by_cases hp : 1 ≤ (header.reference.2 + index - one).val ∧
            (header.reference.2 + index - one).val ≤ (slots.length : Int)
        · simp only [hp, and_self, ite_true]
        · simp only [hp, ite_false]
          exact Or.inl rfl
    · simp only [hb, ite_false]
      exact Or.inl rfl

theorem bh_ap_frame_set (before : MutableMemory U64) (handle : Nat)
    (word : U64) (index : I64) :
    rc_actionPost (fun after => DestinationFrame before after handle) (fun _ => True)
      (mutableSet handle word index) := by
  intro s hs
  refine ⟨bh_frame_trans hs (sp_mutableSet_frame s handle word index), ?_⟩
  have herr := bh_set_errors s handle word index
  cases hr : ((mutableSet handle word index).run s).1 with
  | ok value => exact True.intro
  | error error =>
    simp only [hr] at herr
    exact herr

theorem Models1G15CopytoFrame_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.CopytoBoundsAndGlobalFrame := by
  intro N M dest src before
  by_cases hlong : src.len.val > dest.len.val
  · have hlong' : src.len > dest.len := hlong
    have hrun : (JuliaLean.base.bitarray.Models1Group15.copyto dest src).run before =
        (.error .bounds, before) := by
      simp only [JuliaLean.base.bitarray.Models1Group15.copyto, bitArrayCopyto,
        hlong', ite_true, stateExcept_bind, stateExcept_throw]
    rw [hrun]
    exact ⟨fun _ => ⟨rfl, rfl⟩, True.intro, sp_frame_refl before dest.chunks⟩
  · have hpost := rc_copyto_post (fun after => DestinationFrame before after dest.chunks)
      dest src (fun word index => bh_ap_frame_set before dest.chunks word index)
    have hp := hpost before (sp_frame_refl before dest.chunks)
    refine ⟨fun h => False.elim (hlong h), ?_, hp.1⟩
    have hresult := hp.2
    cases hr : ((JuliaLean.base.bitarray.Models1Group15.copyto dest src).run before).1 with
    | error e => trivial
    | ok returned =>
      simp only [hr] at hresult
      exact ⟨hresult, by omega⟩
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option backward.isDefEq.respectTransparency false

theorem bh_glue_post (P : State → Prop) (source : Nat) (k last : I64)
    (mask : U64) (offset : I64) :
    rc_actionPost P (fun _ => True)
      (JuliaLean.base.bitarray.Models1Group15.glueSrcBitChunks source k last mask offset) := by
  simp only [JuliaLean.base.bitarray.Models1Group15.glueSrcBitChunks,
    bind_assoc, pure_bind, bind_pure]
  apply rc_ap_bind P _ _ _ (rc_ap_get P source k)
  intro firstWord
  by_cases h : last > k ∧ offset > int 0
  · simp only [h, ite_true]
    apply rc_ap_bind P _ _ _ (rc_ap_get P source (k + int 1))
    intro nextWord
    exact rc_ap_pure P _ _ True.intro
  · simp only [h, ite_false]
    exact rc_ap_pure P _ _ True.intro

def bh_copy_block (chunks : Nat) (pd ps count : I64) : BitMutationM Unit := do
  let (kd0, ld0) := getChunksId pd
  let (kd1, ld1) := getChunksId (pd + count - int 1)
  let (ks0, ls0) := getChunksId ps
  let (ks1, ls1) := getChunksId (ps + count - int 1)
  let deltaKD := kd1 - kd0
  let deltaKS := ks1 - ks0
  let u := u64Max
  let mut mskD0 := not_int (shl_Int u ld0)
  let mskD1 := shl_Int u (ld1 + int 1)
  if deltaKD == int 0 then mskD0 := or_int mskD0 mskD1
  let mut mskS0 := shl_Int u ls0
  if deltaKS == int 0 then mskS0 := and_int mskS0 (not_int (shl_Int u (ls1 + int 1)))
  let chunkS0 := and_int
    (← JuliaLean.base.bitarray.Models1Group15.glueSrcBitChunks chunks ks0 ks1 mskS0 ls0)
    (not_int (shl_Int u count))
  let destD0 ← mutableGet chunks kd0
  mutableSet chunks (or_int (and_int destD0 mskD0)
    (and_int (shl_Int chunkS0 ld0) (not_int mskD0))) kd0
  if deltaKD != int 0 then
    let chunkS := lshr_Int chunkS0 (int 64 - ld0)
    let destD1 ← mutableGet chunks kd1
    mutableSet chunks (or_int (and_int destD1 mskD1)
      (and_int chunkS (not_int mskD1))) kd1

theorem bh_block_post (P : State → Prop) (chunks : Nat) (pd ps count : I64)
    (hset : ∀ word index, rc_actionPost P (fun _ => True) (mutableSet chunks word index)) :
    rc_actionPost P (fun _ => True) (bh_copy_block chunks pd ps count) := by
  unfold bh_copy_block
  cases getChunksId pd with
  | mk kd0 ld0 =>
    cases getChunksId (pd + count - int 1) with
    | mk kd1 ld1 =>
      cases getChunksId ps with
      | mk ks0 ls0 =>
        cases getChunksId (ps + count - int 1) with
        | mk ks1 ls1 =>
          dsimp only
          split <;> split
          all_goals
            apply rc_ap_bind P _ _ _ (bh_glue_post P _ _ _ _ _)
            intro chunk0
            apply rc_ap_bind P _ _ _ (rc_ap_get P chunks kd0)
            intro dest0
            apply rc_ap_bind P _ _ _ (hset _ _)
            intro ignored
            split
            · apply rc_ap_bind P _ _ _ (rc_ap_get P chunks kd1)
              intro dest1
              exact hset _ _
            · exact rc_ap_pure P _ () True.intro

def bh_copy_step (chunks : Nat) (posD posS : I64) (r : FrontCopyRegisters) :
    BitMutationM (ForInStep FrontCopyRegisters) := do
  if r.1 > int 0 then
    bh_copy_block chunks r.2.2.2.2 r.2.2.2.1 r.2.1
    pure (.yield (frontCopyRegisters posD posS (r.1 - r.2.1)))
  else pure (.done r)

def bh_copy_loop (chunks : Nat) (posD posS : I64) (r : FrontCopyRegisters) :
    BitMutationM FrontCopyRegisters :=
  forIn ({} : Lean.Loop) r (fun _ r => bh_copy_step chunks posD posS r)

theorem bh_copy_factor (chunks : Nat) (posD posS count : I64)
    (hne : (posD == posS) = false) (horder : ¬ posD < posS) :
    JuliaLean.base.bitarray.Models1Group15.copyChunksRtol chunks posD posS count = (do
      let _ ← bh_copy_loop chunks posD posS (frontCopyRegisters posD posS count)
      pure ()) := by
  simp only [JuliaLean.base.bitarray.Models1Group15.copyChunksRtol, hne,
    Bool.false_eq_true, ite_false, horder, dite_false, bh_copy_loop,
    bh_copy_step, frontCopyRegisters, bh_copy_block, bind_assoc, pure_bind,
    frontCopyBindIte]

theorem bh_copy_loop_post (P : State → Prop) (chunks : Nat) (posD posS count : I64)
    (hset : ∀ word index, rc_actionPost P (fun _ => True) (mutableSet chunks word index)) :
    rc_actionPost P (fun _ => True)
      (bh_copy_loop chunks posD posS (frontCopyRegisters posD posS count)) := by
  have all : ∀ fuel : Nat, ∀ left : I64, left.val.toNat = fuel →
      rc_actionPost P (fun _ => True)
        (bh_copy_loop chunks posD posS (frontCopyRegisters posD posS left)) := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro left hleft
      unfold bh_copy_loop
      rw [resizeFrontLoopUnfold]
      by_cases hp : left > int 0
      · let amount := if left < int 64 then left else int 64
        have hamount : 0 < amount.val ∧ amount.val ≤ left.val := by
          dsimp only [amount]
          split
          · exact ⟨hp, Int.le_refl _⟩
          · rename_i h
            change ¬ left.val < 64 at h
            refine ⟨by decide, ?_⟩
            change 64 ≤ left.val
            omega
        have hb : -9223372036854775808 ≤ left.val ∧
            left.val ≤ 9223372036854775807 := ival_bounds left
        have hsub : (left - amount).val = left.val - amount.val :=
          ival_sub _ _ (by omega)
        have hdec : (left - amount).val.toNat < fuel := by rw [hsub]; omega
        have hnext := ih _ hdec (left - amount) rfl
        simp only [bh_copy_step, frontCopyRegisters, hp, ite_true, bind_assoc, pure_bind]
        apply rc_ap_bind P _ _ _ (bh_block_post P chunks _ _ _ hset)
        intro ignored
        exact hnext
      · simp only [bh_copy_step, frontCopyRegisters, hp, ite_false, pure_bind]
        exact rc_ap_pure P _ _ True.intro
  exact all count.val.toNat count rfl

theorem bh_rtol_post (P : State → Prop) (chunks : Nat) (posD posS count : I64)
    (horder : posD > posS)
    (hset : ∀ word index, rc_actionPost P (fun _ => True) (mutableSet chunks word index)) :
    rc_actionPost P (fun _ => True)
      (JuliaLean.base.bitarray.Models1Group15.copyChunksRtol chunks posD posS count) := by
  have hne : (posD == posS) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    have he := congrArg Subtype.val h
    change posS.val < posD.val at horder
    omega
  have hnot : ¬ posD < posS := by
    change ¬ posD.val < posS.val
    change posS.val < posD.val at horder
    omega
  rw [bh_copy_factor chunks posD posS count hne hnot]
  apply rc_ap_bind P _ _ _ (bh_copy_loop_post P chunks posD posS count hset)
  intro ignored
  exact rc_ap_pure P _ () True.intro

def bh_forward_body (dest src : Nat) (kd0 kd1 ks0 ks1 ld0 ls0 : I64)
    (mskD0 mskD1 mskS0 : U64) : BitMutationM Unit := do
  let mut chunkS0 ← JuliaLean.base.bitarray.Models1Group15.glueSrcBitChunks
    src ks0 ks1 mskS0 ls0
  let destD0 ← mutableGet dest kd0
  mutableSet dest (or_int (and_int destD0 mskD0)
    (and_int (shl_Int chunkS0 ld0) (not_int mskD0))) kd0
  if kd1 - kd0 == int 0 then return
  for i in intRange (int 1) (kd1 - kd0 - int 1) do
    let chunkS1 ← JuliaLean.base.bitarray.Models1Group15.glueSrcBitChunks
      src (ks0 + i) ks1 mskS0 ls0
    let chunkS := or_int (lshr_Int chunkS0 (int 64 - ld0)) (shl_Int chunkS1 ld0)
    mutableSet dest chunkS (kd0 + i)
    chunkS0 := chunkS1
  let chunkS1 ← if ks1 ≥ ks0 + (kd1 - kd0) then
    JuliaLean.base.bitarray.Models1Group15.glueSrcBitChunks
      src (ks0 + (kd1 - kd0)) ks1 mskS0 ls0
  else pure (u64 0)
  let chunkS := or_int (lshr_Int chunkS0 (int 64 - ld0)) (shl_Int chunkS1 ld0)
  let destD1 ← mutableGet dest kd1
  mutableSet dest (or_int (and_int destD1 mskD1)
    (and_int chunkS (not_int mskD1))) kd1
  pure ()

theorem bh_forward_post (P : State → Prop) (dest src : Nat)
    (kd0 kd1 ks0 ks1 ld0 ls0 : I64) (mskD0 mskD1 mskS0 : U64)
    (hset : ∀ word index, rc_actionPost P (fun _ => True) (mutableSet dest word index)) :
    rc_actionPost P (fun _ => True)
      (bh_forward_body dest src kd0 kd1 ks0 ks1 ld0 ls0 mskD0 mskD1 mskS0) := by
  unfold bh_forward_body
  apply rc_ap_bind P _ _ _ (bh_glue_post P _ _ _ _ _)
  intro firstWord
  apply rc_ap_bind P _ _ _ (rc_ap_get P dest kd0)
  intro destWord
  apply rc_ap_bind P _ _ _ (hset _ _)
  intro ignored
  split
  · exact rc_ap_pure P _ () True.intro
  · apply rc_ap_bind P _ _ _ (rc_ap_forIn P _ firstWord _ (by
      intro index previous
      apply rc_ap_bind P _ _ _ (bh_glue_post P _ _ _ _ _)
      intro nextWord
      apply rc_ap_bind P _ _ _ (hset _ _)
      intro ignored
      exact rc_ap_pure P _ (ForInStep.yield nextWord) True.intro))
    intro lastWord
    dsimp only
    split
    · apply rc_ap_bind P _ _ _ (bh_glue_post P _ _ _ _ _)
      intro sourceWord
      apply rc_ap_bind P _ _ _ (rc_ap_get P dest kd1)
      intro destWord
      apply rc_ap_bind P _ _ _ (hset _ _)
      intro ignored
      exact rc_ap_pure P _ () True.intro
    · simp only [pure_bind]
      apply rc_ap_bind P _ _ _ (rc_ap_get P dest kd1)
      intro destWord
      apply rc_ap_bind P _ _ _ (hset _ _)
      intro ignored
      exact rc_ap_pure P _ () True.intro

set_option backward.isDefEq.respectTransparency true in
theorem bh_copy_chunks_post (P : State → Prop) (dest src : Nat)
    (posD posS count : I64)
    (hset : ∀ word index, rc_actionPost P (fun _ => True) (mutableSet dest word index)) :
    rc_actionPost P (fun _ => True)
      (JuliaLean.base.bitarray.Models1Group15.copyChunks dest posD src posS count) := by
  by_cases hz : count == int 0
  · simp only [JuliaLean.base.bitarray.Models1Group15.copyChunks, hz, ite_true]
    exact rc_ap_pure P _ () True.intro
  · by_cases ha : dest = src ∧ posD > posS
    · simp only [JuliaLean.base.bitarray.Models1Group15.copyChunks,
        hz, Bool.false_eq_true, ite_false, dif_pos ha]
      exact bh_rtol_post P dest posD posS count ha.2 hset
    · simp only [JuliaLean.base.bitarray.Models1Group15.copyChunks,
        hz, Bool.false_eq_true, ite_false, dif_neg ha]
      cases getChunksId posD with
      | mk kd0 ld0 =>
        cases getChunksId (posD + count - int 1) with
        | mk kd1 ld1 =>
          cases getChunksId posS with
          | mk ks0 ls0 =>
            cases getChunksId (posS + count - int 1) with
            | mk ks1 ls1 =>
              dsimp only
              split
              · rename_i hD
                split
                · simpa only [bh_forward_body, hD, ite_true] using bh_forward_post P dest src kd0 kd1 ks0 ks1 ld0 ls0
                    (or_int (not_int (shl_Int u64Max ld0)) (shl_Int u64Max (ld1 + int 1)))
                    (shl_Int u64Max (ld1 + int 1))
                    (and_int (shl_Int u64Max ls0) (not_int (shl_Int u64Max (ls1 + int 1)))) hset
                · simpa only [bh_forward_body, hD, ite_true] using bh_forward_post P dest src kd0 kd1 ks0 ks1 ld0 ls0
                    (or_int (not_int (shl_Int u64Max ld0)) (shl_Int u64Max (ld1 + int 1)))
                    (shl_Int u64Max (ld1 + int 1)) (shl_Int u64Max ls0) hset
              · rename_i hD
                split
                · simpa only [bh_forward_body, hD, Bool.false_eq_true, ite_false] using bh_forward_post P dest src kd0 kd1 ks0 ks1 ld0 ls0
                    (not_int (shl_Int u64Max ld0)) (shl_Int u64Max (ld1 + int 1))
                    (and_int (shl_Int u64Max ls0) (not_int (shl_Int u64Max (ls1 + int 1)))) hset
                · simpa only [bh_forward_body, hD, Bool.false_eq_true, ite_false] using bh_forward_post P dest src kd0 kd1 ks0 ks1 ld0 ls0
                    (not_int (shl_Int u64Max ld0)) (shl_Int u64Max (ld1 + int 1))
                    (shl_Int u64Max ls0) hset

theorem Models1G15CopyOffsetPreflight_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.PackedOffsetsEarlyErrors := by
  intro N M dest doffs src soffs count before
  by_cases hz : count.val = 0
  · simp only [hz, ite_true]
    have heq : count = int 0 := by apply Subtype.ext; exact hz
    simp only [hz, ite_true, JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
      JuliaLean.base.number.convertSame,
      JuliaLean.base.bitarray.Models1Group15.copytoPackedInt, heq,
      beq_self_eq_true, ite_true, rc_run_pure, and_self]
  · have hbeq : (count == int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro heq
      exact hz (congrArg Subtype.val heq)
    by_cases hn : count.val < 0
    · have hn' : count < int 0 := hn
      simp only [hz, hn, ite_false, ite_true,
        JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
        JuliaLean.base.number.convertSame,
        JuliaLean.base.bitarray.Models1Group15.copytoPackedInt,
        hbeq, Bool.false_eq_true, hn', rc_run_bind, rc_run_throw, and_self]
    · have hn' : ¬ count < int 0 := hn
      by_cases hs : soffs.val < 1
      · have hs' : soffs < int 1 := hs
        simp only [hz, hn, hs, true_or, ite_false, ite_true,
          JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
          JuliaLean.base.number.convertSame,
          JuliaLean.base.bitarray.Models1Group15.copytoPackedInt,
          hbeq, Bool.false_eq_true, hn', hs', rc_run_bind, rc_run_pure,
          rc_run_throw, and_self]
      · have hs' : ¬ soffs < int 1 := hs
        by_cases hd : doffs.val < 1
        · have hd' : doffs < int 1 := hd
          simp only [hz, hn, hs, hd, false_or, ite_false, ite_true,
            JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
            JuliaLean.base.number.convertSame,
            JuliaLean.base.bitarray.Models1Group15.copytoPackedInt,
            hbeq, Bool.false_eq_true, hn', hs', hd', rc_run_bind,
            rc_run_pure, rc_run_throw, and_self]
        · have hd' : ¬ doffs < int 1 := hd
          simp only [hz, hn, hs, hd, false_or, ite_false]
          by_cases hsource : count > bitArrayLength src - soffs + int 1
          · have hrun :
                (JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets
                  dest doffs src soffs count).run before = (.error .bounds, before) := by
              simp only [JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
                JuliaLean.base.number.convertSame,
                JuliaLean.base.bitarray.Models1Group15.copytoPackedInt,
                hbeq, Bool.false_eq_true, hn', hs', hd', hsource,
                ite_false, ite_true, rc_run_bind, rc_run_pure, rc_run_throw]
            rw [hrun]
            exact sp_frame_refl before dest.chunks
          · by_cases hdest : count > bitArrayLength dest - doffs + int 1
            · have hrun :
                  (JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets
                    dest doffs src soffs count).run before = (.error .bounds, before) := by
                simp only [JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
                  JuliaLean.base.number.convertSame,
                  JuliaLean.base.bitarray.Models1Group15.copytoPackedInt,
                  hbeq, Bool.false_eq_true, hn', hs', hd', hsource, hdest,
                  ite_false, ite_true, rc_run_bind, rc_run_pure, rc_run_throw]
              rw [hrun]
              exact sp_frame_refl before dest.chunks
            · have hpost : rc_actionPost
                  (fun after => DestinationFrame before after dest.chunks)
                  (fun _ => True)
                  (JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets
                    dest doffs src soffs count) := by
                simp only [JuliaLean.base.bitarray.Models1Group15.copytoPackedOffsets,
                  JuliaLean.base.number.convertSame,
                  JuliaLean.base.bitarray.Models1Group15.copytoPackedInt,
                  hbeq, Bool.false_eq_true, hn', hs', hd', hsource, hdest,
                  ite_false, pure_bind,
                  JuliaLean.base.bitarray.Models1Group15.unsafeCopytoPacked,
                  JuliaLean.base.bitarray.Models1Group15.copyToBitArrayChunks]
                apply rc_ap_bind _ _ _ _ (bh_copy_chunks_post _ dest.chunks src.chunks
                  doffs soffs count (fun word index => bh_ap_frame_set before dest.chunks word index))
                intro ignored
                exact rc_ap_pure _ _ dest True.intro
              exact (hpost before (sp_frame_refl before dest.chunks)).1
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem rt_mutableSet_readSelf (s : MutableMemory U64) (a : Nat) (i : I64)
    (word : U64) (hv : s.validVector a)
    (hg : (mutableGet a i).run s = (.ok word, s)) :
    (mutableSet a word i).run s = (.ok (), s) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hv
  have hi : 1 ≤ i.val ∧ i.val ≤ n.val := by
    by_cases hb : 1 ≤ i.val ∧ i.val ≤ n.val
    · exact hb
    · simp only [sp_mutableGet_run, h.1, hb, ite_false] at hg
      cases hg
  have hraw : slots[(off.val + i.val - 2).toNat]? = some (some word) := by
    simp only [sp_mutableGet_run, h.1, hi, ite_true, h.2.1] at hg
    cases hk : slots[(off.val + i.val - 2).toNat]? with
    | none => rw [hk] at hg; cases hg
    | some cell =>
      cases cell with
      | none => rw [hk] at hg; cases hg
      | some v =>
        rw [hk] at hg
        have he : v = word := Except.ok.inj (congrArg Prod.fst hg)
        subst v
        rfl
  have hslot : slots.set (off.val - 1 + i.val - 1).toNat (some word) = slots := by
    rw [show off.val - 1 + i.val - 1 = off.val + i.val - 2 by omega]
    obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp hraw
    rw [← he]
    exact List.set_getElem_self hb
  rw [vwSet_run s a mem off n slots h i hi word, hslot, memories_set_self h.2.1]

def rt_copySelf (a : Nat) (i : I64) : BitMutationM Unit := do
  mutableSet a (← mutableGet a i) i

theorem rt_copySelf_readonly (s : MutableMemory U64) (a : Nat) (i : I64)
    (hv : s.validVector a) : ((rt_copySelf a i).run s).2 = s := by
  have hr := sp_mutableGet_readonly s a i
  cases hg : (mutableGet a i).run s with
  | mk result after =>
    rw [hg] at hr
    dsimp only at hr
    subst after
    cases result with
    | error error => simp only [rt_copySelf, shape_run_bind, hg]
    | ok word =>
      rw [rt_copySelf, shape_run_bind, hg]
      dsimp only
      rw [rt_mutableSet_readSelf s a i word hv hg]

theorem rt_readable_get (s : MutableMemory U64) (a : Nat) (i : I64)
    (hv : s.validVector a) (hread : ReadableChunks s a)
    (hi : 1 ≤ i.val ∧ (i.val - 1).toNat < (s.contents a).length) :
    ∃ word : U64, (mutableGet a i).run s = (.ok word, s) := by
  obtain ⟨word, hw⟩ := hread ((s.contents a)[(i.val - 1).toNat]) (List.getElem_mem hi.2)
  refine ⟨word, ?_⟩
  rw [sp_mutableGet_valid s a i hv, if_neg (by omega), List.getElem?_eq_getElem hi.2, hw]

theorem rt_copySelf_success (s : MutableMemory U64) (a : Nat) (i : I64)
    (hv : s.validVector a) (hread : ReadableChunks s a)
    (hi : 1 ≤ i.val ∧ (i.val - 1).toNat < (s.contents a).length) :
    (rt_copySelf a i).run s = (.ok (), s) := by
  obtain ⟨word, hg⟩ := rt_readable_get s a i hv hread hi
  rw [rt_copySelf, shape_run_bind, hg]
  dsimp only
  rw [rt_mutableSet_readSelf s a i word hv hg]

theorem rt_mask_same_word (mask word : U64) :
    or_int (and_int (not_int mask) word) (and_int mask word) = word := by
  apply packedBit_ext
  intro bit hb
  rw [packedBit_or, scalar_packedBit_and, scalar_packedBit_and,
    scalar_packedBit_not mask bit hb]
  cases packedBit mask bit <;> cases packedBit word bit <;> rfl

def rt_copySelfMasked (a : Nat) (i : I64) (mask : U64) : BitMutationM Unit := do
  let d ← mutableGet a i
  let t ← mutableGet a i
  mutableSet a (or_int (and_int (not_int mask) d) (and_int mask t)) i

theorem rt_copySelfMasked_run (s : MutableMemory U64) (a : Nat) (i : I64)
    (mask : U64) : (rt_copySelfMasked a i mask).run s = (rt_copySelf a i).run s := by
  have hr := sp_mutableGet_readonly s a i
  cases hg : (mutableGet a i).run s with
  | mk result after =>
    rw [hg] at hr
    dsimp only at hr
    subst after
    cases result with
    | error error => simp only [rt_copySelfMasked, rt_copySelf, shape_run_bind, hg]
    | ok word =>
      simp only [rt_copySelfMasked, rt_copySelf, shape_run_bind, hg, rt_mask_same_word]

theorem rt_forIn_readonly (action : I64 → BitMutationM Unit)
    (indices : List I64) (s : MutableMemory U64)
    (haction : ∀ i, ((action i).run s).2 = s) :
    ((forIn indices PUnit.unit (fun i _ => do
      action i
      pure (ForInStep.yield PUnit.unit))).run s).2 = s := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hr := haction i
    cases hg : (action i).run s with
    | mk result after =>
      rw [hg] at hr
      dsimp only at hr
      subst after
      cases result with
      | error error => simp only [List.forIn_cons, shape_run_bind, hg]
      | ok unit =>
        simp only [List.forIn_cons, shape_run_bind, hg, shape_run_pure]
        exact ih

theorem rt_forIn_unchanged (action : I64 → BitMutationM Unit)
    (indices : List I64) (s : MutableMemory U64)
    (haction : ∀ i ∈ indices, (action i).run s = (.ok (), s)) :
    (forIn indices PUnit.unit (fun i _ => do
      action i
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, s) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hi := haction i List.mem_cons_self
    have ht := ih (fun j hj => haction j (List.mem_cons_of_mem i hj))
    simp only [List.forIn_cons, shape_run_bind, hi, shape_run_pure, ht]


theorem rt_copySelfMasked_eq (a : Nat) (i : I64) (mask : U64) :
    rt_copySelfMasked a i mask = rt_copySelf a i := by
  funext s
  exact rt_copySelfMasked_run s a i mask

theorem rt_bind_readonly {α β : Type} (action : BitMutationM α)
    (next : α → BitMutationM β) (s : MutableMemory U64)
    (ha : (action.run s).2 = s) (hb : ∀ value, ((next value).run s).2 = s) :
    ((action >>= next).run s).2 = s := by
  cases hr : action.run s with
  | mk result after =>
    rw [hr] at ha
    dsimp only at ha
    subst after
    cases result with
    | error error => simp only [shape_run_bind, hr]
    | ok value => simp only [shape_run_bind, hr, hb]

def rt_copySelfProgram {N : Nat} (dest : BitArray N) (count : I64) :
    BitMutationM (BitArray N) := do
  if count == int 0 then return dest
  for i in intRange (int 1) (count - int 1) do
    rt_copySelf dest.chunks i
  rt_copySelf dest.chunks count
  return dest

theorem rt_copySelfProgram_readonly {N : Nat} (s : MutableMemory U64)
    (dest : BitArray N) (count : I64) (hv : s.validVector dest.chunks) :
    ((rt_copySelfProgram dest count).run s).2 = s := by
  unfold rt_copySelfProgram
  split
  · rfl
  · apply rt_bind_readonly
    · exact rt_forIn_readonly (rt_copySelf dest.chunks) _ s
        (fun i => rt_copySelf_readonly s dest.chunks i hv)
    · intro ignored
      apply rt_bind_readonly
      · exact rt_copySelf_readonly s dest.chunks count hv
      · intro ignored
        rfl

theorem rt_copySelfProgram_success {N : Nat} (s : MutableMemory U64)
    (dest : BitArray N) (count : I64) (hv : s.validVector dest.chunks)
    (hread : ReadableChunks s dest.chunks) (hn : 0 ≤ count.val)
    (hsize : (s.contents dest.chunks).length = count.val.toNat) :
    (rt_copySelfProgram dest count).run s = (.ok dest, s) := by
  by_cases hz : count = int 0
  · simp only [rt_copySelfProgram, hz, beq_self_eq_true, ite_true, shape_run_pure]
  · have hcount : 0 < count.val := by
      have hne : count.val ≠ 0 := by
        intro he
        apply hz
        exact Subtype.ext he
      omega
    have hcmp : (count == int 0) = false := beq_eq_false_iff_ne.mpr hz
    have hprev : (count - int 1).val = count.val - 1 := by
      apply ival_sub
      have hb := count.property
      change -9223372036854775808 ≤ count.val ∧ count.val ≤ 9223372036854775807 at hb
      change -9223372036854775808 ≤ count.val - 1 ∧ count.val - 1 ≤ 9223372036854775807
      omega
    have hloop := rt_forIn_unchanged (rt_copySelf dest.chunks)
      (intRange (int 1) (count - int 1)) s (by
        intro i hi
        have hib := shape_range_mem (count - int 1) i hi
        rw [hprev] at hib
        exact rt_copySelf_success s dest.chunks i hv hread
          ⟨hib.1, by rw [hsize]; omega⟩)
    have hlast := rt_copySelf_success s dest.chunks count hv hread
      ⟨by omega, by rw [hsize]; omega⟩
    simp only [rt_copySelfProgram, hcmp, Bool.false_eq_true, ite_false,
      shape_run_bind, hloop, hlast, shape_run_pure]

theorem rt_copyto_same_run {N M : Nat} (dest : BitArray N) (src : BitArray M)
    (s : MutableMemory U64) (header : MutableVector)
    (hc : dest.chunks = src.chunks) (ha : s.arrays[dest.chunks]? = some header)
    (hle : ¬ src.len.val > dest.len.val) :
    (JuliaLean.base.bitarray.Models1Group15.copyto dest src).run s =
      (rt_copySelfProgram dest header.size).run s := by
  have hlength := mutableLength_run s dest.chunks header ha
  have hsame : ¬ header.size < header.size := Int.lt_irrefl _
  have hle' : ¬ src.len > dest.len := hle
  have htail :
      (if src.len == dest.len then
        (do
          mutableSet dest.chunks (← mutableGet dest.chunks header.size) header.size
          pure dest : BitMutationM (BitArray N))
       else do
        let d ← mutableGet dest.chunks header.size
        let t ← mutableGet dest.chunks header.size
        mutableSet dest.chunks
          (or_int (and_int (not_int (maskEndArray src)) d) (and_int (maskEndArray src) t))
          header.size
        pure dest) = (do rt_copySelf dest.chunks header.size; pure dest) := by
    split
    · simp only [rt_copySelf, bind_assoc]
    · have he := congrArg
        (fun action : BitMutationM Unit =>
          (do action; pure dest : BitMutationM (BitArray N)))
        (rt_copySelfMasked_eq dest.chunks header.size (maskEndArray src))
      simpa only [rt_copySelfMasked, rt_copySelf, bind_assoc] using he
  simp only [JuliaLean.base.bitarray.Models1Group15.copyto, bitArrayCopyto,
    hle', ite_false, ← hc, pure_bind]
  rw [shape_run_bind, hlength]
  dsimp only
  rw [shape_run_bind, hlength]
  dsimp only
  simp only [hsame, ite_false]
  unfold rt_copySelfProgram
  by_cases hz : header.size == int 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false, Bool.false_eq_true]
    simp only [rt_copySelf, bind_assoc, maskEndArray, bitArrayLength] at htail ⊢
    rw [htail]

theorem Models1G15CopytoSameChunks_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.CopytoSameChunksUnchanged := by
  intro N M dest src s hc hv
  dsimp only
  by_cases hlong : src.len.val > dest.len.val
  · have hlong' : src.len > dest.len := hlong
    simp only [JuliaLean.base.bitarray.Models1Group15.copyto, bitArrayCopyto,
      hlong', ite_true, if_pos hlong]
    exact ⟨rfl, rfl⟩
  · obtain ⟨mem, off, count, slots, h⟩ := validVector_vecAt hv
    rw [rt_copyto_same_run dest src s ⟨(mem, off), count⟩ hc h.1 hlong]
    refine ⟨rt_copySelfProgram_readonly s dest count hv, ?_⟩
    rw [if_neg hlong]
    intro hread
    have hsize : (s.contents dest.chunks).length = count.val.toNat := by
      rw [h.contents]
      exact vwWindow_length h
    rw [rt_copySelfProgram_success s dest count hv hread h.2.2.2.1 hsize]
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

/-- Mathematical bit-incidence specification for base/bitarray.jl:266-272.
All UInt64 words are admitted, including noncanonical Boolean-byte encodings.
Output bit j is the disjunction of input bits j+7k for k from zero through seven. -/
def Pack8BoolsBitIncidence : Prop :=
  ∀ word : U64,
    (JuliaLean.base.bitarray.Models1Group15.pack8bools word).val =
      (List.range 8).foldl (fun total bit =>
        total + if (List.range 8).any
          (fun k => (word.val / (2 : Int) ^ (bit + 7 * k)) % 2 == 1)
          then (2 : Int) ^ bit else 0) (0 : Int)
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.int JuliaLean.C

theorem Models1G15Pack8boolsBitIncidence_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.Pack8BoolsBitIncidence := by
  intro word
  rw [← val_of_unsigned_pattern (by rfl)
    (JuliaLean.base.bitarray.Models1Group15.pack8bools word), bh_pack_pattern]
  rw [bh_byte_reconstruct (bh_pack_nat (pattern word)) (Nat.mod_lt _ (by decide))]
  apply bh_fold_bits_eq
  intro i hi
  rw [bh_pack_nat_bit _ _ (List.mem_range.mp hi)]
  simp only [bh_int_bit]
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models2Group11

open JuliaLean JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models2Group11

abbrev BoolCopyByteHeap := JuliaLean.base.pointer.ByteHeap

/-- Mathematical element count of a typed native array header. No machine
arithmetic or copy implementation is used in this observation. -/
def boolCopyDimensionProduct {T : Type} {N : Nat} (a : BoolCopyArray T N) : Int :=
  (a.dimensions.values.map (fun dimension => dimension.val)).prod

/-- Native non-union inline layout and necessary dimension invariants. The
tuple's rank and machine-sized arity are already carried by BoolCopyArray,
and dimension values are native JInts rather than unrestricted Lean lengths.
The whole native array view must fit in the physical address space: otherwise
distinct logical elements could alias after pointer wrap, which is not a native
Array representation. Byte validity is separately required only for accessed
locations. No convenient bound on size or rank is imposed. -/
def BoolCopyNativeHeader {T : Type} {N : Nat}
    (elementBytes : Int) (a : BoolCopyArray T N) : Prop :=
  a.reference.mem.arrayElement ≠ 2 ∧
  a.reference.mem.layoutBytes.val = elementBytes ∧
  (∀ dimension ∈ a.dimensions.values, 0 ≤ dimension.val) ∧
  0 ≤ boolCopyDimensionProduct a ∧
  boolCopyDimensionProduct a ≤ IntTy.max .i64 ∧
  a.reference.ptr_or_offset.val + elementBytes * boolCopyDimensionProduct a ≤
    (2 : Int) ^ 64

/-- Stored current-data address of a native non-union Array reference. -/
def boolCopyStoredBase {T : Type} {N : Nat} (a : BoolCopyArray T N) : Nat :=
  a.reference.ptr_or_offset.val.toNat

/-- First destination word touched by a positive mathematical bit interval,
expressed as its zero-based chunk number. -/
def boolCopyFirstWord (posD : I64) : Nat := (posD.val - 1).toNat / 64

/-- Last destination word touched by a positive mathematical bit interval. -/
def boolCopyLastWord (posD count : I64) : Nat :=
  (posD.val + count.val - 2).toNat / 64

/-- Byte start and size of all destination words touched. Boundary-word stores
write whole UInt64 cells, even when only some of their logical bits change. -/
def boolCopyWriteStart (dst : BoolCopyArray U64 1) (posD : I64) : Nat :=
  boolCopyStoredBase dst + 8 * boolCopyFirstWord posD

def boolCopyWriteSize (posD count : I64) : Nat :=
  8 * (boolCopyLastWord posD count - boolCopyFirstWord posD + 1)

/-- First source Bool byte in the requested positive interval. -/
def boolCopyReadStart {N : Nat} (src : BoolCopyArray Bool N) (posS : I64) : Nat :=
  boolCopyStoredBase src + (posS.val - 1).toNat

/-- Safe positive-count calls admitted by the native BitArray copyto! checks.
The logical destination end remains a Julia Int, including its maximal value.
Only the actually read/written byte intervals must have valid, nonwrapping
backing. Only source Bool bytes actually read must have canonical 0/1 values.
The two differently typed access intervals are disjoint, as required when
accessing externally wrapped storage through Bool and UInt64 arrays; unaccessed
parts of the two views are not unnecessarily required to be disjoint.
Julia source: base/bitarray.jl:454-470; base/array.jl:267-286;
base/pointer.jl:92-104; doc/src/devdocs/ub.md:39-47
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolCopySafeInput {N : Nat} (before : BoolCopyState)
    (dst : BoolCopyArray U64 1) (posD : I64)
    (src : BoolCopyArray Bool N) (posS count : I64) : Prop :=
  BoolCopyNativeHeader 8 dst ∧ BoolCopyNativeHeader 1 src ∧
  1 ≤ posD.val ∧ 1 ≤ posS.val ∧ 0 < count.val ∧
  posD.val + count.val - 1 ≤ IntTy.max .i64 ∧
  posD.val + count.val - 1 ≤ 64 * boolCopyDimensionProduct dst ∧
  posS.val + count.val - 1 ≤ boolCopyDimensionProduct src ∧
  before.heap.validRange (boolCopyWriteStart dst posD) (boolCopyWriteSize posD count) ∧
  before.heap.validRange (boolCopyReadStart src posS) count.val.toNat ∧
  (∀ offset : Nat, offset < count.val.toNat →
    let byte := (before.heap.readByte (boolCopyReadStart src posS + offset)).val
    byte = 0 ∨ byte = 1) ∧
  (boolCopyWriteStart dst posD + boolCopyWriteSize posD count ≤ boolCopyReadStart src posS ∨
    boolCopyReadStart src posS + count.val.toNat ≤ boolCopyWriteStart dst posD)

/-- Independent bit observation directly from the physical byte address and
arithmetic division/remainder. This does not use packing, shifting, masking,
chunk-index helpers, or the model's UInt64 decoder. -/
def boolCopyPackedBit (heap : BoolCopyByteHeap) (base bitIndex : Nat) : Int :=
  ((heap.readByte (base + bitIndex / 8)).val / (2 : Int) ^ (bitIndex % 8)) % 2

/-- Independent little-endian word observation as a finite base-256 sum. -/
def boolCopyWordValue (heap : BoolCopyByteHeap) (address : Nat) : Int :=
  ((List.range 8).map (fun offset =>
    (heap.readByte (address + offset)).val * (256 : Int) ^ offset)).sum

/-- A trailing partial word exists after the initial partial-word segment and
the complete-word segment precisely in this geometric case. An initial partial
word alone is handled by the first block and returns Julia nothing. -/
def BoolCopyHasTrailingWord (posD count : I64) : Prop :=
  (posD.val + count.val - 1) % 64 ≠ 0 ∧
  ((posD.val - 1) % 64 = 0 ∨ boolCopyFirstWord posD < boolCopyLastWord posD count)

/-- Source-level return category and exact stored final word on safe calls.
This catches dropping the assignment's UInt64 result and always returning
nothing, independently of whether the copied bits happen to be correct. -/
def BoolCopySafeReturn (dst : BoolCopyArray U64 1) (posD count : I64)
    (after : BoolCopyState) (returned : Option U64) : Prop :=
  match returned with
  | none => ¬ BoolCopyHasTrailingWord posD count
  | some word =>
      BoolCopyHasTrailingWord posD count ∧
      word.val = boolCopyWordValue after.heap
        (boolCopyStoredBase dst + 8 * boolCopyLastWord posD count)

/-- A byte is mentioned by a new UInt64 store in the instrumentation. Modular
address comparison retains native pointer wrap for arbitrary instrumented
inputs; it is not a bounds assumption or a manufactured Julia exception. -/
def BoolCopyWrittenAddress (events : List BoolCopyAccess) (address : Nat) : Prop :=
  ∃ event ∈ events, event.kind = .chunkWrite ∧
    ∃ offset : Nat, offset < event.width ∧
      address % 2 ^ 64 = (event.address.val.toNat + offset) % 2 ^ 64

/-- All-input frame invariant of the source-mirrored instrumented execution.
Even for negative counts, wrapped indices, aliases, or failed unsafe-access
obligations, only bytes named by an actual logged chunk store can change.
Validity metadata and earlier log entries remain unchanged. The only reported
Julia exception class is the source's AssertionError; invalid unsafe accesses
remain explicit obligations, not invented BoundsErrors. This is a property
of the instrumented model outside the safe domain, not a promise about Julia
after undefined behavior.
Julia source: base/bitarray.jl:274-337, especially :295,310,318,325,331,335;
doc/src/devdocs/ub.md:21-27,39-47
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolCopyAllInputsFrame : Prop :=
  ∀ (N : Nat) (dst : BoolCopyArray U64 1) (posD : I64)
    (src : BoolCopyArray Bool N) (posS count : I64) (before : BoolCopyState),
    let result := (copyBoolChunks dst posD src posS count).run before
    let after := result.2
    let newEvents := after.accesses.drop before.accesses.length
    after.heap.validByte = before.heap.validByte ∧
    after.accesses.take before.accesses.length = before.accesses ∧
    (∀ address : U64, ¬ BoolCopyWrittenAddress newEvents address.val.toNat →
      after.heap.readByte address.val.toNat = before.heap.readByte address.val.toNat) ∧
    match result.1 with
    | .ok _ => True
    | .error error => ∃ message : String, error = .assertion message

/-- On every safe positive-count call, the requested destination bits equal
the original source Bool sequence, and every other destination bit is preserved.
All newly recorded access obligations hold, including canonical Bool bytes and
the deliberately unaligned eight-byte loads. The copied source bytes remain
unchanged because the accessed differently typed intervals are disjoint.
Every physical byte outside the destination words is unchanged, and the return
is exactly nothing or the final assigned UInt64 according to the independent
interval geometry above. No snapshot claim is made for unsafe aliases.
The premises are the native representation and caller/unsafe-pointer contracts;
there is no small-array, alignment, rank, purity, or callee-correctness shortcut.
Julia source: base/bitarray.jl:274-337,454-470;
base/array.jl:267-286; base/pointer.jl:92-104;
doc/src/devdocs/ub.md:39-47
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolCopySafeBitTransfer : Prop :=
  ∀ (N : Nat) (dst : BoolCopyArray U64 1) (posD : I64)
    (src : BoolCopyArray Bool N) (posS count : I64) (before : BoolCopyState),
    BoolCopySafeInput before dst posD src posS count →
    let result := (copyBoolChunks dst posD src posS count).run before
    let after := result.2
    match result.1 with
    | .error _ => False
    | .ok returned =>
      BoolCopySafeReturn dst posD count after returned ∧
      after.heap.validByte = before.heap.validByte ∧
      after.accesses.take before.accesses.length = before.accesses ∧
      (∀ event ∈ after.accesses.drop before.accesses.length,
        event.withinArray = true ∧ event.validBytes = true ∧ event.canonicalBool = true) ∧
      (∀ bitIndex : Nat, bitIndex < 64 * (boolCopyDimensionProduct dst).toNat →
        boolCopyPackedBit after.heap (boolCopyStoredBase dst) bitIndex =
          if (posD.val - 1).toNat ≤ bitIndex ∧
              bitIndex < (posD.val - 1).toNat + count.val.toNat then
            (before.heap.readByte
              (boolCopyReadStart src posS + (bitIndex - (posD.val - 1).toNat))).val
          else boolCopyPackedBit before.heap (boolCopyStoredBase dst) bitIndex) ∧
      (∀ offset : Nat, offset < count.val.toNat →
        after.heap.readByte (boolCopyReadStart src posS + offset) =
          before.heap.readByte (boolCopyReadStart src posS + offset)) ∧
      (∀ address : U64,
        ¬ (boolCopyWriteStart dst posD ≤ address.val.toNat ∧
          address.val.toNat < boolCopyWriteStart dst posD + boolCopyWriteSize posD count) →
        after.heap.readByte address.val.toNat = before.heap.readByte address.val.toNat)

/-- An actually returned UInt64 is the word in the last destination store,
including on instrumented alias or wrapping inputs. The final bytes are read
independently as a base-256 sum. This invariant does not turn a Julia nothing
return into a UInt64, and does not claim successful return after an assertion.
Julia source: base/bitarray.jl:327-337
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolCopyReturnedWordStored : Prop :=
  ∀ (N : Nat) (dst : BoolCopyArray U64 1) (posD : I64)
    (src : BoolCopyArray Bool N) (posS count : I64) (before : BoolCopyState),
    let result := (copyBoolChunks dst posD src posS count).run before
    match result.1 with
    | .ok (some word) =>
      ∃ event : BoolCopyAccess,
        (result.2.accesses.drop before.accesses.length).getLast? = some event ∧
        event.kind = .chunkWrite ∧ event.width = 8 ∧
        boolCopyWordValue result.2.heap event.address.val.toNat = word.val
    | _ => True

/-- Zero bits at a positive word-aligned destination require no source or
destination access and return Julia nothing. No native header, byte validity,
or source-offset premise is needed because those fields are never inspected.
The positive-position requirement is essential: wrapped negative indices can
reach the source assertion even when the low destination offset is zero.
Unaligned zero-count calls are deliberately not asserted to skip accesses;
the source reads and rewrites the initial destination word in that case.
Julia source: base/bitarray.jl:274-337; zero-count caller shortcuts :457,468
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolCopyZeroAlignedNoAccess : Prop :=
  ∀ (N : Nat) (dst : BoolCopyArray U64 1) (posD : I64)
    (src : BoolCopyArray Bool N) (posS : I64) (before : BoolCopyState),
    1 ≤ posD.val → (posD.val - 1) % 64 = 0 →
    (copyBoolChunks dst posD src posS (int 0)).run before = (.ok none, before)

/-- Mathematical signed 64-bit residue, independent of the model's JInt
arithmetic, shift, and comparison implementations. -/
def dumpBoolCacheSigned64 (value : Int) : Int :=
  (value + (2 : Int) ^ 63) % (2 : Int) ^ 64 - (2 : Int) ^ 63

/-- The bit interval selected by the wrapper, expressed mathematically with
the source's native signed wrapping retained. The count is in bits, not words.
An enormous but address-representable vector can make the capacity negative
after its native shift; no no-overflow bound is silently imposed here. -/
def dumpBoolCacheStart (bind : I64) : Int :=
  dumpBoolCacheSigned64 (64 * (bind.val - 1) + 1)

def dumpBoolCacheCount (dst : BoolCopyArray U64 1) (bind : I64) : Int :=
  min 4096 (dumpBoolCacheSigned64
    (64 * (boolCopyDimensionProduct dst - bind.val + 1)))

/-- Safe positive interval selected by dumpbitcache's actual native arithmetic.
The arguments passed to BoolCopySafeInput are representations of the bounded
mathematical signed residues above. This admits wrapping inputs whenever their
resulting positive interval meets the native-array and unsafe-access contracts;
it does not replace native capacity by an unbounded mathematical capacity.
Only read source bytes must be canonical and only accessed ranges must be
valid; complete view nonwrap is a native representation invariant.
Julia source: base/bitarray.jl:342-348,274-337;
base/pointer.jl:92-104; doc/src/devdocs/ub.md:39-47
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def DumpBoolCacheSafeInput (before : BoolCopyState)
    (dst : BoolCopyArray U64 1) (bind : I64) (src : BoolCopyArray Bool 1) : Prop :=
  BoolCopySafeInput before dst (int (dumpBoolCacheStart bind))
    src (int 1) (int (dumpBoolCacheCount dst bind))

/-- Independent all-input frame invariant for the cache wrapper. Only bytes
actually recorded by a chunk store may change; validity metadata and the old
access log are retained. Its only possible reported Julia exception is the
actual assertion in the delegated source body. Unsafe access flags remain
obligations, not fabricated bounds errors. This describes the instrumented
execution on invalid inputs and does not promise Julia behavior after UB.
Julia source: base/bitarray.jl:347-348,274-337
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def DumpBoolCacheAllInputsFrame : Prop :=
  ∀ (dst : BoolCopyArray U64 1) (bind : I64) (src : BoolCopyArray Bool 1)
    (before : BoolCopyState),
    let result := (dumpBoolCache dst bind src).run before
    let after := result.2
    let newEvents := after.accesses.drop before.accesses.length
    after.heap.validByte = before.heap.validByte ∧
    after.accesses.take before.accesses.length = before.accesses ∧
    (∀ address : U64, ¬ BoolCopyWrittenAddress newEvents address.val.toNat →
      after.heap.readByte address.val.toNat = before.heap.readByte address.val.toNat) ∧
    match result.1 with
    | .ok _ => True
    | .error error => ∃ message : String, error = .assertion message

/-- On every safe positive interval selected by the source's native arithmetic,
the wrapper copies the cache prefix into that destination interval and preserves
every other destination bit, source byte, and physical byte outside the touched
words. For ordinary unwrapped arithmetic the interval is the next
min(64, remaining chunk count) whole words. The mathematical signed residues
above retain other native inputs instead of restricting vector lengths for
convenience. The expected result is a bit relation over the physical heap, not
an equality to another call of copyBoolChunks or a correctness law for it.
All access obligations hold, and success returns Julia nothing because this
wrapper always chooses word-aligned positions and a whole-word bit count.
Julia source: base/bitarray.jl:342-348,274-337;
base/pointer.jl:92-104; doc/src/devdocs/ub.md:39-47
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def DumpBoolCacheSafeBitTransfer : Prop :=
  ∀ (dst : BoolCopyArray U64 1) (bind : I64) (src : BoolCopyArray Bool 1)
    (before : BoolCopyState),
    DumpBoolCacheSafeInput before dst bind src →
    let posD := int (dumpBoolCacheStart bind)
    let count := int (dumpBoolCacheCount dst bind)
    let startBit := (dumpBoolCacheStart bind - 1).toNat
    let bitCount := (dumpBoolCacheCount dst bind).toNat
    let result := (dumpBoolCache dst bind src).run before
    let after := result.2
    result.1 = .ok none ∧
    after.heap.validByte = before.heap.validByte ∧
    after.accesses.take before.accesses.length = before.accesses ∧
    (∀ event ∈ after.accesses.drop before.accesses.length,
      event.withinArray = true ∧ event.validBytes = true ∧ event.canonicalBool = true) ∧
    (∀ bitIndex : Nat, bitIndex < 64 * (boolCopyDimensionProduct dst).toNat →
      boolCopyPackedBit after.heap (boolCopyStoredBase dst) bitIndex =
        if startBit ≤ bitIndex ∧ bitIndex < startBit + bitCount then
          (before.heap.readByte (boolCopyStoredBase src + (bitIndex - startBit))).val
        else boolCopyPackedBit before.heap (boolCopyStoredBase dst) bitIndex) ∧
    (∀ offset : Nat, offset < bitCount →
      after.heap.readByte (boolCopyStoredBase src + offset) =
        before.heap.readByte (boolCopyStoredBase src + offset)) ∧
    (∀ address : U64,
      ¬ (boolCopyWriteStart dst posD ≤ address.val.toNat ∧
        address.val.toNat < boolCopyWriteStart dst posD + boolCopyWriteSize posD count) →
      after.heap.readByte address.val.toNat = before.heap.readByte address.val.toNat)

/-- Successful dumpbitcache executions return Julia nothing on all native
integer inputs, including wrapped and negative capacities. Its destination
position is always congruent to 1 modulo 64 and its selected count to 0 modulo
64. Completed whole-word loops leave the final bind incongruent modulo 8 to
kd1, so the final partial-word assignment cannot succeed: a wrapped path that
reaches its guard instead fails the source assertion. The model still retains
the delegated Option UInt64 result type and the exact exception/effect path.
This is a narrow internal invariant, not an invented public contract for
unsafe or invalid storage.
Julia source: base/bitarray.jl:347-348,302-337
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def DumpBoolCacheSuccessfulReturn : Prop :=
  ∀ (dst : BoolCopyArray U64 1) (bind : I64) (src : BoolCopyArray Bool 1)
    (before : BoolCopyState),
    match ((dumpBoolCache dst bind src).run before).1 with
    | .ok returned => returned = none
    | .error _ => True

/-- A selected zero count and positive wrapped destination position perform
no accesses. This includes an empty destination with bind = 1, and requires no
valid source pointer, source length, or canonical source bytes. Negative wrapped
positions are not included: even zero count can reach the source assertion.
Julia source: base/bitarray.jl:347-348,274-337
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def DumpBoolCacheZeroNoAccess : Prop :=
  ∀ (dst : BoolCopyArray U64 1) (bind : I64) (src : BoolCopyArray Bool 1)
    (before : BoolCopyState),
    1 ≤ dumpBoolCacheStart bind → dumpBoolCacheCount dst bind = 0 →
    (dumpBoolCache dst bind src).run before = (.ok none, before)

open JuliaLean.base.array JuliaLean.base.int
open JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

private theorem zeroCountCancellation (position : I64) :
    int 0 - position + position = int 0 := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (0 - position.val) + position.val) = 0
  rw [JuliaLean.Proofs.base.int.wrapInt_add_left]
  rw [Int.sub_add_cancel]
  rfl

theorem BoolCopyZeroAlignedNoAccess_proven : BoolCopyZeroAlignedNoAccess := by
  intro N dst posD src posS before hpositive haligned
  have hbound := posD.property
  change -9223372036854775808 ≤ posD.val ∧ posD.val ≤ 9223372036854775807 at hbound
  have hd : (posD - int 1).val = posD.val - 1 := by
    change wrapInt .i64 (posD.val - 1) = posD.val - 1
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ posD.val - 1 ∧ posD.val - 1 ≤ 9223372036854775807
    omega
  have hstart : (getChunksId posD).2 = int 0 := by
    apply Subtype.ext
    change (mod64 (posD - int 1)).val = 0
    rw [scalar_mod64_val, hd, haligned]
  have hend : (getChunksId (posD + int 0 - int 1)).1.val < (getChunksId posD).1.val := by
    rw [(bh_address _).1, (bh_address _).1]
    unfold Models1Group15.WrappedZeroBasedScalar
    have hl : posD.val % 64 = 1 := by omega
    have hpre : (posD + int 0 - int 1).val = posD.val - 1 := by
      rw [shape_int_add_zero]; exact hd
    rw [hpre]
    omega
  have hfalse : ¬ (getChunksId posD).2 > int 0 := by rw [hstart]; decide
  have hfinish : ¬ (getChunksId posD).1 ≤ (getChunksId (posD + int 0 - int 1)).1 := by
    change ¬ (getChunksId posD).1.val ≤ (getChunksId (posD + int 0 - int 1)).1.val
    omega
  have hz : div64 (int 0) = int 0 := by decide
  have hnc8 : shl_Int (lshr_Int (div64 (int 0)) (int 3)) (int 3) = int 0 := by decide
  have hnc8' : shl_Int (lshr_Int (int 0) (int 3)) (int 3) = int 0 := by decide
  have hnot : ¬ (int 0 : I64) < int 0 := by decide
  have hr : intRange (int 0 + int 1) (int 0) = [] := rfl
  simp only [copyBoolChunks, hfalse, ite_false, pure_bind, zeroCountCancellation,
    hz, hnc8, hnc8', hnot, hr, List.forIn_nil, hfinish]
  rfl
open JuliaLean JuliaLean.base.bitarray JuliaLean.base.bitarray.Models2Group11
open JuliaLean.base.int JuliaLean.Proofs.base.int

private theorem cacheShiftSix (value : I64) :
    (shl_Int value (int 6)).val = wrapInt .i64 (value.val * 64) := by
  have h : le_BitSigned (JuliaLean.base.int.lit .i64 0) (int 6) = true := by decide
  simp only [shl_Int, h, ifelse, ite_true, shl_BitInteger_BitUnsigned]
  rw [shl_int_val]
  rfl

private theorem cacheStart (bind : I64) :
    (shl_Int (bind - int 1) (int 6) + int 1).val = dumpBoolCacheStart bind := by
  change wrapInt .i64 ((shl_Int (bind - int 1) (int 6)).val + 1) = _
  rw [cacheShiftSix, wrapInt_add_left]
  change wrapInt .i64 (wrapInt .i64 (bind.val - 1) * 64 + 1) = _
  rw [← wrapInt_add_left, wrapInt_mul_left, wrapInt_add_left]
  change wrapInt .i64 ((bind.val - 1) * 64 + 1) =
    wrapInt .i64 (64 * (bind.val - 1) + 1)
  congr 1
  omega

private theorem cacheLength (dst : BoolCopyArray U64 1) :
    (boolCopyVectorLength dst).val = boolCopyDimensionProduct dst := by
  rcases dst with ⟨reference, ⟨dimensions, length_eq⟩, rankFits⟩
  cases dimensions with
  | nil => simp at length_eq
  | cons head tail =>
      cases tail with
      | nil => simp [boolCopyVectorLength, boolCopyDimensionProduct,
          JuliaLean.base.essentials.lengthArray1]
      | cons second tail => simp at length_eq

private theorem cacheMin (left right : I64) :
    (boolCopyNativeMin left right).val = min left.val right.val := by
  change (if lt_BitSigned right left then right else left).val = min left.val right.val
  have hlt : lt_BitSigned right left = decide (right.val < left.val) :=
    slt_int_eq (t := .i64) rfl right left
  rw [hlt]
  by_cases h : right.val < left.val
  · simp only [h, decide_true, ite_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

private theorem cacheCount (dst : BoolCopyArray U64 1) (bind : I64) :
    (boolCopyNativeMin bitCacheSize
      (shl_Int (boolCopyVectorLength dst - bind + int 1) (int 6))).val =
      dumpBoolCacheCount dst bind := by
  rw [cacheMin, cacheShiftSix]
  change min 4096 (wrapInt .i64
    (wrapInt .i64 (wrapInt .i64 ((boolCopyVectorLength dst).val - bind.val) + 1) * 64)) = _
  rw [wrapInt_add_left, wrapInt_mul_left, cacheLength]
  change min 4096 (wrapInt .i64 ((boolCopyDimensionProduct dst - bind.val + 1) * 64)) =
    min 4096 (wrapInt .i64 (64 * (boolCopyDimensionProduct dst - bind.val + 1)))
  rw [Int.mul_comm (boolCopyDimensionProduct dst - bind.val + 1) 64]

theorem DumpBoolCacheZeroNoAccess_proven : DumpBoolCacheZeroNoAccess := by
  intro dst bind src before hpositive hzero
  let position := shl_Int (bind - int 1) (int 6) + int 1
  have hposition : position.val = dumpBoolCacheStart bind := cacheStart bind
  have haligned : (position.val - 1) % 64 = 0 := by
    rw [hposition]
    simp only [dumpBoolCacheStart, dumpBoolCacheSigned64]
    omega
  have hcount : boolCopyNativeMin bitCacheSize
      (shl_Int (boolCopyVectorLength dst - bind + int 1) (int 6)) = int 0 := by
    apply Subtype.ext
    rw [cacheCount, hzero]
    rfl
  unfold dumpBoolCache
  rw [hcount]
  exact BoolCopyZeroAlignedNoAccess_proven 1 dst position src (int 1) before
    (by rw [hposition]; exact hpositive) haligned

end JuliaLean.Proofs.base.bitarray.Models2Group11

