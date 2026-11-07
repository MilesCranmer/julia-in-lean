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

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Removing the final visible word leaves its slot assigned beyond the shortened header. -/
theorem dequeWordDeleteLast (words : List U64) (last : U64) (spare : Nat)
    (hn : words.length + 1 ≤ 9223372036854775807) :
    (deleteChunkEnd 0 (int 1)).run (dequeWordStore (words ++ [last]) spare) =
      (.ok (), dequeTailStore words (some last :: List.replicate spare none)) := by
  let n := int ((words.length + 1 : Nat) : Int)
  let slots := (words ++ [last]).map some ++ List.replicate spare none
  let s := dequeWordStore (words ++ [last]) spare
  have hlen : (words ++ [last]).length = words.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hv : n.val = (words.length + 1 : Nat) := packedInt_val _ hn
  have hpred : n - int 1 = int words.length := by
    change int ((words.length + 1 : Nat) : Int) - int 1 = _
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hstart : n - int 1 + one = n := by
    rw [hpred]
    change int (words.length : Int) + int 1 = n
    rw [packedInt_add]
    rfl
  have hrem : (JInt.rem .u64 n).val = (words.length + 1 : Nat) := by
    change wrapInt .u64 n.val = _
    rw [hv]
    apply wrapInt_of_inRange
    change 0 ≤ ((words.length + 1 : Nat) : Int) ∧
      ((words.length + 1 : Nat) : Int) ≤ 18446744073709551615
    omega
  have hslots : slots.length = words.length + 1 + spare := by
    simp only [slots, List.length_append, List.length_map,
      List.length_cons, List.length_nil, List.length_replicate]
  have ha : s.arrays[0]? = some ⟨(0, one), n⟩ := by
    change some (⟨(0, one), int (words ++ [last]).length⟩ : MutableVector) = _
    rw [hlen]
  have hm : s.memories[0]? = some slots := rfl
  have hraw := dequeDeleteChunks s slots n (int 1) ha hm
    (by rw [hv, hslots]; omega)
    (by change ¬ (JInt.rem .u64 n).val < 1; rw [hrem]; omega)
    (by
      intro j hj
      rw [hstart, endPop_range_singleton] at hj
      have hjn : j = n := List.mem_singleton.mp hj
      subst j
      rw [hv]
      omega)
  rw [hpred] at hraw
  refine hraw.trans ?_
  simp only [s, dequeWordStore, dequeTailStore, List.set_cons_zero, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
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

/-- Subtracting one from a positive representable length agrees with natural subtraction. -/
theorem frontPopLengthPred (n : Nat) (hp : 0 < n) :
    int (n : Int) - int 1 = int ((n - 1 : Nat) : Int) := by
  rw [dequeIntSub]
  exact congrArg int (by omega)
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Packed disjunction is commutative. -/
theorem reverseOrComm (a b : U64) : or_int a b = or_int b a := by
  apply packedBit_ext
  intro k _
  rw [packedBit_or, packedBit_or, Bool.or_comm]

/-- A full-width left shift clears all bits. -/
theorem reverseShiftFull (word : U64) :
    shl_int word (int ((64 : Nat) : Int)) = u64 0 := by
  unfold shl_int jlShlInt
  have hc : (fromJInt (int ((64 : Nat) : Int))).toNat = 64 := rfl
  rw [hc, if_pos (show 64 ≥ IntTy.u64.bits by decide)]
  rfl

/-- Left alignment supports all final-bit counts, including a full sixty-four-bit chunk. -/
theorem reversePackedLeft (word : U64) (amount bit : Nat)
    (ha : amount ≤ 64) (hb : bit < 64) :
    packedBit (shl_int word (int amount)) bit =
      if amount ≤ bit then packedBit word (bit - amount) else false := by
  by_cases hs : amount < 64
  · rw [dequePackedShiftLeft word amount bit hs]
    simp only [hb, decide_true, Bool.true_and]
    by_cases hi : amount ≤ bit
    · simp only [hi, decide_true, Bool.true_and, ite_true]
    · simp only [hi, decide_false, Bool.false_and, ite_false]
  · have he : amount = 64 := by omega
    subst amount
    rw [reverseShiftFull, packedBit_zero, if_neg (by omega)]
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

/-- A repeated Boolean sequence has its constant value within bounds and false beyond it. -/
theorem fillReplicateGet (n i : Nat) (value : Bool) :
    (List.replicate n value).getD i false = if i < n then value else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases hi : i < n <;>
    simp only [hi, ite_true, ite_false, Option.getD_some, Option.getD_none]

/-- Packing an all-false logical sequence yields zero in every chunk. -/
theorem fillFalsePackedWord (n chunk : Nat) :
    packedPrefix (List.replicate n false) chunk 64 = u64 0 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, fillReplicateGet, packedBit_zero]
  simp only [ite_self]

/-- The exact encoding of an all-false sequence is a constant zero word list. -/
theorem fillFalseEncoding (n : Nat) :
    encodeBits (List.replicate n false) = List.replicate (wordCount n) (u64 0) := by
  apply List.ext_getElem
  · rw [packedEncoded_length, List.length_replicate, List.length_replicate]
  · intro j hj hj'
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rw [fillFalsePackedWord, List.getElem_replicate]

/-- The installed array fill callback composes its length read and fill loop. -/
theorem fillChunkVectorFrom (chunks : Nat) (word : U64) (nc : I64) (s out : State)
    (hl : (mutableLength chunks).run s = (.ok nc, s))
    (hloop : (forIn (intRange (int 1) nc) PUnit.unit (fun i _ => do
      mutableSet chunks word i
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, out)) :
    (Round5.Round2.fillChunkVectorModel chunks word).run s = (.ok (), out) := by
  simp only [Round5.Round2.fillChunkVectorModel, fillTyped,
    shape_run_bind, hl, shape_run_pure, hloop]

/-- Successful conversion on an empty array returns before inspecting chunk memory. -/
theorem fillEmptyFrom {N : Nat} {X : Type} (convert : X → BitMutationM Bool)
    (fill : Nat → U64 → BitMutationM Unit) (B : BitArray N) (x : X) (value : Bool) (s : State)
    (hc : (convert x).run s = (.ok value, s)) (hz : (B.len == int 0) = true) :
    (fillBitArray convert fill B x).run s = (.ok B, s) := by
  simp only [fillBitArray, shape_run_bind, hc, hz, ite_true, shape_run_pure]

/-- The false branch consists solely of filling every chunk with zero. -/
theorem fillFalseFrom {N : Nat} {X : Type} (convert : X → BitMutationM Bool)
    (fill : Nat → U64 → BitMutationM Unit) (B : BitArray N) (x : X) (s out : State)
    (hc : (convert x).run s = (.ok false, s)) (hz : (B.len == int 0) = false)
    (hf : (fill B.chunks (u64 0)).run s = (.ok (), out)) :
    (fillBitArray convert fill B x).run s = (.ok B, out) := by
  simp only [fillBitArray, shape_run_bind, hc, hz, Bool.false_eq_true, ite_false,
    Bool.not_false, ite_true, hf, shape_run_pure]

/-- A positive native logical length is distinct from machine zero. -/
theorem fillPositiveLength (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    (int (n : Int) == int 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro he
  have h := congrArg Subtype.val he
  rw [packedInt_val n hn] at h
  change (n : Int) = 0 at h
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

/-- A raw slot write updates one backing memory without changing any array header. -/
theorem growthMemoryWrite (s : State) (mem : Nat) (slots : List (Option U64))
    (i : I64) (value : Option U64) (hm : s.memories[mem]? = some slots)
    (hi : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int)) :
    (memoryWrite mem i value).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (i.val - 1).toNat value)}) := by
  simp only [memoryWrite, memoryRead, shape_run_bind, shape_run_get, hm,
    shape_run_pure, hi, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_run_modify]

/-- Copying a finite list into the front of zero-initialized slots gives its exact prefix. -/
theorem growthInstallPrefix (xs pre : List (Option U64)) (spare : Nat) :
    ((xs.zipIdx pre.length).foldl (fun slots pair => slots.set pair.2 pair.1)
      (pre ++ List.replicate (xs.length + spare) none)) =
        pre ++ xs ++ List.replicate spare none := by
  induction xs generalizing pre with
  | nil => simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil,
      Nat.zero_add, List.append_nil]
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
    rw [List.set_append_right _ _ (by omega), Nat.sub_self]
    rw [show xs.length + 1 + spare = (xs.length + spare) + 1 by omega,
      List.replicate_succ, List.set_cons_zero]
    have hp : pre ++ x :: List.replicate (xs.length + spare) none =
        (pre ++ [x]) ++ List.replicate (xs.length + spare) none := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hp]
    have h := ih (pre ++ [x])
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      List.append_assoc, List.cons_append, List.nil_append] using h

/-- Native one-based copy indices are ordinary successors within the native bound. -/
theorem growthCopyIndex (k : Nat) :
    one + JInt.wrap .i64 k = int ((k + 1 : Nat) : Int) := by
  change int 1 + int k = _
  rw [packedInt_add]
  exact congrArg int (by omega)

/-- The concrete memory-copy write loop realizes a pure slot-update fold. -/
theorem growthCopyLoop (s : State) (mem : Nat) (slots values : List (Option U64))
    (hm : s.memories[mem]? = some slots) (hv : values.length ≤ slots.length)
    (hn : slots.length ≤ 9223372036854775807) :
    (forIn values.zipIdx PUnit.unit (fun (pair : Option U64 × Nat) _ => do
      memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1
      pure (ForInStep.yield PUnit.unit))).run s =
      (.ok PUnit.unit,
        {s with memories := s.memories.set mem (values.zipIdx.foldl (fun (ws : List (Option U64)) (pair : Option U64 × Nat) => ws.set pair.2 pair.1) slots)}) := by
  let store := fun ws => ({s with memories := s.memories.set mem ws} : State)
  have hmem : mem < s.memories.length := (List.getElem?_eq_some_iff.mp hm).choose
  have hstore : store slots = s := by
    change {s with memories := s.memories.set mem slots} = s
    have heq : s.memories.set mem slots = s.memories := by
      apply List.ext_getElem?
      intro k
      by_cases he : k = mem
      · subst k
        rw [List.getElem?_set_self hmem, hm]
      · rw [List.getElem?_set_ne (Ne.symm he)]
    rw [heq]
  have hf := dequeForInFold
    (fun pair : Option U64 × Nat => memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1)
    (fun (ws : List (Option U64)) (pair : Option U64 × Nat) => ws.set pair.2 pair.1) store (fun ws => ws.length = slots.length)
    values.zipIdx
    (by
      intro ws hw pair hpair
      have hi : pair.2 < values.length := by
        simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hpair
      have hread : (store ws).memories[mem]? = some ws := by
        exact List.getElem?_set_self hmem
      have hval : (one + JInt.wrap .i64 pair.2).val = (pair.2 + 1 : Nat) := by
        rw [growthCopyIndex, packedInt_val (pair.2 + 1) (by omega)]
      have hidx : ((one + JInt.wrap .i64 pair.2).val - 1).toNat = pair.2 := by
        rw [hval]
        omega
      have hr := growthMemoryWrite (store ws) mem ws
        (one + JInt.wrap .i64 pair.2) pair.1 hread (by rw [hval, hw]; omega)
      simpa only [hidx, store, List.set_set] using hr)
    (by intro ws hw pair _; rw [List.length_set]; exact hw) slots rfl
  rw [hstore] at hf
  exact hf
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

/-- A terminating iteration supplies the result of the installed monadic loop. -/
theorem reverseLoopDone {β : Type} (f : Unit → β → BitMutationM (ForInStep β))
    (a b : β) (s out : State)
    (hs : (f () a).run s = (.ok (.done b), out)) :
    (forIn ({} : Lean.Loop) a f).run s = (.ok b, out) := by
  change (Lean.Loop.forIn ({} : Lean.Loop) a f).run s = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [shape_run_bind, hs, shape_run_pure]

/-- A yielding iteration composes with the rest of a terminating installed monadic loop. -/
theorem reverseLoopYield {β : Type} (f : Unit → β → BitMutationM (ForInStep β))
    (a b c : β) (s mid out : State)
    (hs : (f () a).run s = (.ok (.yield b), mid))
    (hr : (forIn ({} : Lean.Loop) b f).run mid = (.ok c, out)) :
    (forIn ({} : Lean.Loop) a f).run s = (.ok c, out) := by
  change (Lean.Loop.forIn ({} : Lean.Loop) a f).run s = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [shape_run_bind, hs]
  exact hr
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The UInt64 chunk runtime layout projects to the eight-byte inline allocation summary. -/
theorem uint64AllocationLayout :
    (MemoryLayoutMetadata.ofRuntime uint64Layout).allocation = some ⟨8, false, false⟩ := by
  decide

/-- Fresh chunk memory is allocated successfully at the bounded capacities used by resize. -/
theorem growthAllocate (s : State) (old n : Nat) (hn : n ≤ 576460752303423488) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).allocate old (int n)).run s =
      (.ok s.memories.length,
        {s with memories := s.memories ++ [List.replicate n none]}) := by
  have hn64 : n ≤ 9223372036854775807 := by omega
  have hnat : ((int n).val % 2 ^ 64).toNat = n := by
    rw [packedInt_val n hn64, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hb : n * 8 < 2 ^ 64 := by omega
  have hz : (n * 8) % 2 ^ 64 = n * 8 := Nat.mod_eq_of_lt hb
  have hlimit1 : ¬ (n ≥ maxIntVal - 1) := by unfold maxIntVal; omega
  have hlimit2 : ¬ (n * 8 ≥ maxIntVal - 1) := by unfold maxIntVal; omega
  by_cases hn0 : n = 0
  · subst n
    simp only [mutableStorage, uint64AllocationLayout]
    rfl
  · simp only [mutableStorage, uint64AllocationLayout, memoryUndef, memorynew, hnat, allocGenericMemory,
      hn0, ite_false, Bool.false_eq_true, newGenericMemory, sizeMulOverflow,
      hz, show ¬ (2 ^ 64 ≤ n * 8) by omega, decide_false, hlimit1, hlimit2,
      Bool.false_or, Bool.false_eq_true, mutableFreshMemory,
      shape_run_bind, shape_run_get, shape_run_pure]
    rfl
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

/-- Taking a logical prefix changes exactly the observations beyond its new end. -/
theorem resizeTakeGet (xs : List Bool) (n i : Nat) :
    (xs.take n).getD i false = if i < n then xs.getD i false else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take]
  by_cases hi : i < n <;> simp only [hi, ite_true, ite_false,
    Option.getD_none, List.getD_eq_getElem?_getD]

/-- A chunk strictly before the final retained chunk needs no masking. -/
theorem resizeTakeWordBefore (xs : List Bool) (n chunk : Nat)
    (hc : chunk + 1 < wordCount n) :
    packedPrefix (xs.take n) chunk 64 = packedPrefix xs chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk, resizeTakeGet]
  rw [if_pos (show chunk * 64 + k < n by unfold wordCount at hc; omega)]

/-- Masking the retained final chunk packs precisely the requested logical prefix. -/
theorem resizeTakeWordLast (xs : List Bool) (n : Nat)
    (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    and_int (packedPrefix xs (wordCount n - 1) 64) (maskEnd (int (n : Int))) =
      packedPrefix (xs.take n) (wordCount n - 1) 64 := by
  apply packedBit_ext
  intro k hk
  rw [dequePackedAnd, packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk,
    packedMask_last_bit n k hp hn, resizeTakeGet]
  by_cases hi : (wordCount n - 1) * 64 + k < n <;>
    simp only [hi, decide_true, decide_false, ite_true, ite_false,
      Bool.and_true, Bool.and_false]

/-- The word-level suffix-shrink result is the encoding of the retained prefix. -/
theorem resizeTakeEncoding (xs : List Bool) (n : Nat)
    (hp : 0 < n) (hle : n ≤ xs.length) (hn : n ≤ 9223372036854775807) :
    ((encodeBits xs).take (wordCount n)).set (wordCount n - 1)
      (and_int ((encodeBits xs).getD (wordCount n - 1) (u64 0))
        (maskEnd (int (n : Int)))) = encodeBits (xs.take n) := by
  have hc : wordCount n ≤ (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hpos : 0 < wordCount n := by unfold wordCount; omega
  have ht : ((encodeBits xs).take (wordCount n)).length = wordCount n := by
    rw [List.length_take, Nat.min_eq_left hc]
  have hlast : (encodeBits xs).getD (wordCount n - 1) (u64 0) =
      packedPrefix xs (wordCount n - 1) 64 := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [hlast, resizeTakeWordLast xs n hp hn]
  apply List.ext_getElem
  · rw [List.length_set, ht, packedEncoded_length, List.length_take,
      Nat.min_eq_left hle]
  · intro j hj hj'
    have hjb : j < wordCount n := by simpa only [List.length_set, ht] using hj
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ (wordCount n - 1) j _ (by rw [ht]; omega)]
    by_cases he : wordCount n - 1 = j
    · rw [if_pos he]
      subst j
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    · rw [if_neg he, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hjb,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
      exact (resizeTakeWordBefore xs n j (by omega)).symm

/-- The visible window of an arbitrary backing allocation starts at its first slot. -/
theorem resizeContentsRaw (s : State) (slots : List (Option U64)) (mem n : Nat)
    (ha : s.arrays[0]? = some ⟨(mem, one), int n⟩)
    (hm : s.memories[mem]? = some slots) (hn : n ≤ 9223372036854775807) :
    s.contents 0 = slots.take n := by
  simp only [MutableMemory.contents, ha, hm, Option.getD_some,
    packedInt_val n hn]
  rfl

/-- A raw allocation write preserves every other memory and all headers. -/
theorem resizeMemoryWrite (s : State) (slots : List (Option U64)) (mem : Nat)
    (hm : s.memories[mem]? = some slots) (j : I64) (word : U64)
    (hj : 1 ≤ j.val ∧ j.val ≤ (slots.length : Int)) :
    (memoryWrite mem j (some word)).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (j.val - 1).toNat (some word))}) := by
  simp only [memoryWrite, memoryRead, shape_run_bind, shape_run_get, hm,
    shape_run_pure, hj, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_run_modify]

/-- A zero-bit chunk copy accesses no memory. -/
theorem resizeCopyZero (dest src : Nat) (pd ps : I64) :
    copyChunks dest pd src ps (int 0) = (pure () : BitMutationM Unit) := by
  rw [copyChunks]
  rfl

/-- The post-shrink masking action visits only the retained final chunk. -/
def resizeMaskTail (chunks : Nat) (n : I64) : BitMutationM Unit := do
  if n > int 0 then
    let last ← mutableGet chunks (← mutableLength chunks)
    mutableSet chunks (and_int last (maskEnd n)) (← mutableLength chunks)

/-- A positive masking tail composes its length, read, and write primitive outcomes. -/
theorem resizeMaskTailFrom (chunks : Nat) (n nc : I64) (word : U64) (s out : State)
    (hp : n > int 0)
    (hl : (mutableLength chunks).run s = (.ok nc, s))
    (hg : (mutableGet chunks nc).run s = (.ok word, s))
    (hw : (mutableSet chunks (and_int word (maskEnd n)) nc).run s = (.ok (), out)) :
    (resizeMaskTail chunks n).run s = (.ok (), out) := by
  simp only [resizeMaskTail, hp, ite_true, shape_run_bind, hl, hg, hw, shape_run_pure]

/-- Native chunk count equals the corresponding natural ceiling division. -/
theorem resizeNumChunks (n : Nat) (hn : n ≤ 9223372036854775807) :
    numBitChunks (int (n : Int)) = int (wordCount n : Int) := by
  have hv := packedInt_val n hn
  apply Subtype.ext
  rw [scalar_num_chunks _ (by rw [hv]; omega), hv,
    packedInt_val (wordCount n) (by unfold wordCount; omega)]
  unfold wordCount
  omega

/-- The final retained word is read and masked without changing the backing capacity. -/
theorem resizeMaskPrefixRun (xs : List Bool) (n spare : Nat)
    (hp : 0 < n) (hle : n ≤ xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (resizeMaskTail 0 (int (n : Int))).run
      (dequeWordStore ((encodeBits xs).take (wordCount n)) spare) =
        (.ok (), dequeWordStore (encodeBits (xs.take n)) spare) := by
  let words := encodeBits xs
  let retained := words.take (wordCount n)
  have hw : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hk : wordCount n ≤ words.length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hpos : 0 < wordCount n := by unfold wordCount; omega
  have hlen : retained.length = wordCount n := by
    rw [List.length_take, Nat.min_eq_left hk]
  have hreadval : retained.getD (wordCount n - 1) (u64 0) =
      words.getD (wordCount n - 1) (u64 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
    rfl
  have hl := dequeWordLength retained spare
  rw [hlen] at hl
  have hg := dequeWordRead retained spare (wordCount n - 1)
    (by rw [hlen]; omega) (by rw [hlen]; omega)
  rw [show wordCount n - 1 + 1 = wordCount n by omega, hreadval] at hg
  have hwrt := dequeWordSet retained spare (wordCount n - 1)
    (and_int (words.getD (wordCount n - 1) (u64 0)) (maskEnd (int (n : Int))))
    (by rw [hlen]; omega) (by rw [hlen]; omega)
  rw [show wordCount n - 1 + 1 = wordCount n by omega] at hwrt
  have he := resizeMaskTailFrom 0 (int (n : Int)) (int (wordCount n : Int))
    (words.getD (wordCount n - 1) (u64 0)) _ _
    (by change 0 < (int (n : Int)).val; rw [packedInt_val n (by omega)]; omega)
    hl hg hwrt
  exact he.trans (by rw [resizeTakeEncoding xs n hp hle (by omega)])
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The exact preserve mask for a destination interval contained in one chunk. -/
def rangeSingleKeep (offset count : Nat) : U64 :=
  or_int (not_int (shl_int u64Max (int offset)))
    (shl_int u64Max (int ((offset + count : Nat) : Int)))

/-- The exact source selection and alignment used by one-chunk forward copying. -/
def rangeSingleCopyWord (word : U64) (dest source count : Nat) : U64 :=
  let keep := rangeSingleKeep dest count
  let selected := and_int (shl_int u64Max (int source))
    (not_int (shl_int u64Max (int ((source + count : Nat) : Int))))
  or_int (and_int word keep)
    (and_int (shl_int (lshr_int (and_int word selected) (int source)) (int dest)) (not_int keep))

/-- A shifted all-ones word marks the high positions, including endpoint sixty-four. -/
theorem rangeSingleHighMaskBit (offset bit : Nat) (ho : offset ≤ 64) (hb : bit < 64) :
    packedBit (shl_int u64Max (int offset)) bit = decide (offset ≤ bit) := by
  rw [reversePackedLeft _ _ _ ho hb]
  by_cases h : offset ≤ bit
  · simp only [h, ite_true, decide_true, packedBit_max, show bit - offset < 64 by omega]
  · simp only [h, ite_false, decide_false]

/-- The destination mask preserves exactly the positions outside the copied interval. -/
theorem rangeSingleKeepBit (offset count bit : Nat) (hh : offset + count ≤ 64)
    (hb : bit < 64) :
    packedBit (rangeSingleKeep offset count) bit =
      decide (bit < offset ∨ offset + count ≤ bit) := by
  rw [rangeSingleKeep, packedBit_or, scalar_packedBit_not _ _ hb,
    rangeSingleHighMaskBit _ _ (by omega) hb, rangeSingleHighMaskBit _ _ hh hb]
  by_cases hl : offset ≤ bit
  · have hlt : ¬ bit < offset := by omega
    by_cases hr : offset + count ≤ bit <;> simp only [hl, hlt, hr, decide_true,
      decide_false, Bool.not_true, Bool.false_or, false_or]
  · have hlt : bit < offset := by omega
    by_cases hr : offset + count ≤ bit <;> simp only [hl, hlt, hr, decide_true,
      decide_false, Bool.not_false, Bool.true_or, true_or]

/-- One-chunk copying has exact source-offset semantics and preserves other positions. -/
theorem rangeSingleCopyBit (word : U64) (dest source count bit : Nat)
    (hd : dest + count ≤ 64) (hs : source + count ≤ 64) (hb : bit < 64) :
    packedBit (rangeSingleCopyWord word dest source count) bit =
      if dest ≤ bit ∧ bit < dest + count then packedBit word (bit - dest + source)
      else packedBit word bit := by
  simp only [rangeSingleCopyWord, packedBit_or, dequePackedAnd,
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

/-- Copying an empty interval preserves the complete chunk. -/
theorem rangeSingleCopyZero (word : U64) (dest source : Nat)
    (hd : dest ≤ 64) (hs : source ≤ 64) :
    rangeSingleCopyWord word dest source 0 = word := by
  apply packedBit_ext
  intro bit hb
  rw [rangeSingleCopyBit word dest source 0 bit (by omega) (by omega) hb,
    if_neg (by omega)]

/-- Indexed observations of interval removal are the unchanged prefix followed by the suffix. -/
theorem rangeSingleLogicalGet (xs : List Bool) (first last bit : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) :
    (xs.take first ++ xs.drop last).getD bit false =
      if bit < first then xs.getD bit false else xs.getD (last + (bit - first)) false := by
  have ht : (xs.take first).length = first := by
    simp only [List.length_take, Nat.min_eq_left (show first ≤ xs.length by omega)]
  by_cases hb : bit < first
  · simp only [hb, ite_true, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show bit < (xs.take first).length by omega),
      List.getElem?_take, hb, decide_true, Option.guard_true]
  · have hge : (xs.take first).length ≤ bit := by omega
    simp only [hb, ite_false, List.getD_eq_getElem?_getD,
      List.getElem?_append_right hge, ht, List.getElem?_drop]

/-- The end mask for a positive single-chunk vector selects precisely its logical bits. -/
theorem rangeSingleEndMaskBit (n bit : Nat) (hp : 0 < n) (hn : n ≤ 64) (hb : bit < 64) :
    packedBit (maskEnd (int n)) bit = decide (bit < n) := by
  have hw : wordCount n = 1 := by unfold wordCount; omega
  have he := packedMask_last_bit n bit hp (by omega)
  simpa only [hw, Nat.sub_self, Nat.zero_mul, Nat.zero_add] using he

/-- Every nonempty sequence of at most one chunk has a singleton packed encoding. -/
theorem rangeSingleEncoding (xs : List Bool) (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    encodeBits xs = [packedPrefix xs 0 64] := by
  rw [packedPrefix_eq_encode]
  have hw : wordCount xs.length = 1 := by unfold wordCount; omega
  simp only [hw, List.range_one, List.map_cons, List.map_nil]

/-- Every position in the first packed chunk has its expected one-based chunk address. -/
theorem rangeSingleAddress (bit : Nat) (hb : bit < 64) :
    getChunksId (int ((bit + 1 : Nat) : Int)) = (int 1, int bit) := by
  have h := scalar_chunks_nat bit (by omega)
  simpa only [Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb, Nat.zero_add, Int.ofNat_one] using h

/-- An empty copy returns immediately, without reading or changing memory. -/
theorem rangeSingleCopyEmptyRun (chunks : Nat) (dest source : I64) (s : State) :
    (copyChunks chunks dest chunks source (int 0)).run s = (.ok (), s) := by
  simp only [copyChunks, beq_self_eq_true, ite_true, shape_run_pure]

/-- The frozen forward copier executes its exact one-word formula for an overlapping leftward copy. -/
theorem rangeSingleCopyRun (chunks dest source count : Nat) (s out : State) (word : U64)
    (hf : dest ≤ source) (hp : 0 < count) (hs : source + count ≤ 64)
    (hg : (mutableGet chunks (int 1)).run s = (.ok word, s))
    (hw : (mutableSet chunks (rangeSingleCopyWord word dest source count) (int 1)).run s =
      (.ok (), out)) :
    (copyChunks chunks (int ((dest + 1 : Nat) : Int)) chunks
      (int ((source + 1 : Nat) : Int)) (int count)).run s = (.ok (), out) := by
  have hz : (int count == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val count (by omega)] at hv
    change (count : Int) = 0 at hv
    omega
  have hforward : ¬ (chunks = chunks ∧ int ((dest + 1 : Nat) : Int) > int ((source + 1 : Nat) : Int)) := by
    intro he
    have hlt := he.2
    change (int ((source + 1 : Nat) : Int)).val < (int ((dest + 1 : Nat) : Int)).val at hlt
    rw [packedInt_val (source + 1) (by omega), packedInt_val (dest + 1) (by omega)] at hlt
    omega
  have horder : ¬ int ((dest + 1 : Nat) : Int) > int ((source + 1 : Nat) : Int) := fun h => hforward ⟨rfl, h⟩
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
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, horder, and_false, dite_false,
    hendD, hendS, hstartD, hstartS, hlastD, hlastS,
    show (int 1 - int 1 == int 0) = true from rfl, ite_true, hincD, hincS,
    glueSrcBitChunks, shape_run_bind, hg,
    show ¬ (int 1 > int 1 ∧ int source > int 0) from by intro h; exact (by decide : ¬ int 1 > int 1) h.1,
    shape_run_pure]
  simp only [rangeSingleCopyWord, rangeSingleKeep] at hw
  rw [hw]

/-- Canonical one-word storage supports every valid forward copy, including an empty suffix. -/
theorem rangeSingleCopyStore (word : U64) (dest source count spare : Nat)
    (hf : dest ≤ source) (hs : source + count ≤ 64) :
    (copyChunks 0 (int ((dest + 1 : Nat) : Int)) 0
      (int ((source + 1 : Nat) : Int)) (int count)).run (dequeWordStore [word] spare) =
        (.ok (), dequeWordStore [rangeSingleCopyWord word dest source count] spare) := by
  by_cases hp : 0 < count
  · apply rangeSingleCopyRun 0 dest source count _ _ word hf hp hs
    · simpa only [List.getD_cons_zero, Nat.zero_add, Int.ofNat_one] using dequeWordRead [word] spare 0 (by simp) (by simp)
    · simpa only [List.set_cons_zero, Nat.zero_add, Int.ofNat_one] using
        dequeWordSet [word] spare 0 (rangeSingleCopyWord word dest source count) (by simp) (by simp)
  · have hz : count = 0 := by omega
    subst count
    rw [rangeSingleCopyZero word dest source (by omega) (by omega)]
    exact rangeSingleCopyEmptyRun 0 _ _ _

/-- The exact post-copy phases of range deletion are length adjustment and padding cleanup. -/
def rangeSingleFinish (B : BitArray 1) (newLength oldChunks : I64) : BitMutationM (BitArray 1) := do
  if numBitChunks newLength - oldChunks < int 0 then
    deleteChunkEnd B.chunks (-(numBitChunks newLength - oldChunks))
  let result := { B with len := newLength }
  if newLength > int 0 then
    let last ← mutableGet B.chunks (← mutableLength B.chunks)
    mutableSet B.chunks (and_int last (maskEnd newLength)) (← mutableLength B.chunks)
  return result

/-- Every positive length within one word has exactly one packed chunk. -/
theorem rangeSingleChunkCount (n : Nat) (hp : 0 < n) (hn : n ≤ 64) :
    numBitChunks (int n) = int 1 := by
  apply Subtype.ext
  rw [scalar_num_chunks _ (by rw [packedInt_val n (by omega)]; omega), packedInt_val n (by omega)]
  change ((n : Int) + 63) / 64 = 1
  omega

/-- A nonempty one-chunk result performs exactly its final mask write. -/
theorem rangeSingleFinishPositive (B : BitArray 1) (n : Nat) (word : U64) (s out : State)
    (hp : 0 < n) (hn : n ≤ 64)
    (hl : (mutableLength B.chunks).run s = (.ok (int 1), s))
    (hg : (mutableGet B.chunks (int 1)).run s = (.ok word, s))
    (hw : (mutableSet B.chunks (and_int word (maskEnd (int n))) (int 1)).run s = (.ok (), out)) :
    (rangeSingleFinish B (int n) (int 1)).run s =
      (.ok { B with len := int n }, out) := by
  have hp' : int n > int 0 := by
    change 0 < (int n).val
    rw [packedInt_val n (by omega)]
    omega
  simp only [rangeSingleFinish, rangeSingleChunkCount n hp hn,
    show ¬ int 1 - int 1 < int 0 from by decide, ite_false,
    hp', ite_true, shape_run_bind, hl, hg, hw, shape_run_pure]

/-- Deleting the complete contents removes the single chunk and skips the final mask. -/
theorem rangeSingleFinishEmpty (B : BitArray 1) (s out : State)
    (hd : (deleteChunkEnd B.chunks (int 1)).run s = (.ok (), out)) :
    (rangeSingleFinish B (int 0) (int 1)).run s =
      (.ok { B with len := int 0 }, out) := by
  simp only [rangeSingleFinish, show numBitChunks (int 0) = int 0 from rfl,
    show int 0 - int 1 < int 0 from by decide, ite_true,
    show -(int 0 - int 1) = int 1 from rfl, shape_run_bind, hd,
    show ¬ int 0 > int 0 from by decide, ite_false, shape_run_pure]

/-- Every position of a false-filled list, including out-of-bounds defaults, is false. -/
theorem shiftSingleFalseGet (n bit : Nat) :
    (List.replicate n false).getD bit false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- A packed false-filled sequence is the all-zero word. -/
theorem shiftSingleFalseWord (n : Nat) : packedPrefix (List.replicate n false) 0 64 = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ _ _ hb, packedBit_zero]
  simp only [Nat.zero_mul, Nat.zero_add, shiftSingleFalseGet]
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

/-- A known vector header supplies its chunk count without inspecting any chunk. -/
theorem shiftSingleLengthFrom (s : State) (handle mem : Nat) (n : I64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩) :
    (mutableLength handle).run s = (.ok n, s) := by
  simp only [mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run, ha, shape_run_pure]

/-- Fresh storage for a zero-length vector consists of an empty memory and a zero-length header. -/
def shiftEmptyExtend (s : State) : State :=
  ⟨s.memories ++ [[]], s.arrays ++ [⟨(s.memories.length, one), int 0⟩]⟩

/-- The new empty header points to its fresh memory. -/
theorem shiftEmptyHeader (s : State) :
    (shiftEmptyExtend s).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), int 0⟩ := by
  simp only [shiftEmptyExtend, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

/-- The new empty allocation has no visible contents. -/
theorem shiftEmptyContents (s : State) : (shiftEmptyExtend s).contents s.arrays.length = [] := by
  have hm : (shiftEmptyExtend s).memories[s.memories.length]? = some [] := by
    simp only [shiftEmptyExtend, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
  simp only [MutableMemory.contents, shiftEmptyHeader, hm]
  rfl

/-- Expose one iteration of the installed loop through its typeclass-level operation. -/
theorem resizeFrontLoopUnfold {β : Type} (a : β) (f : Unit → β → BitMutationM (ForInStep β)) :
    (forIn ({} : Lean.Loop) a f : BitMutationM β) = (do
      match ← f () a with
      | .done value => pure value
      | .yield value => forIn ({} : Lean.Loop) value f) := by
  change Lean.Loop.forIn ({} : Lean.Loop) a f = _
  exact Lean.Loop.forIn_eq_of_monadTail

/-- Two adjacent source chunks aligned to a bit offset in the lower chunk. -/
def copyPairGlue (low high : U64) (offset : Nat) : U64 :=
  or_int (lshr_int (and_int low (shl_int u64Max (int offset))) (int offset))
    (shl_int (and_int high (not_int (shl_int u64Max (int offset))))
      (int ((64 - offset : Nat) : Int)))

/-- A right shift by exactly the word width clears the word. -/
theorem copyPairRightFull (word : U64) : lshr_int word (int (64 : Nat)) = u64 0 := by
  unfold lshr_int jlLshrInt
  have hc : (fromJInt (int (64 : Nat))).toNat = 64 := rfl
  rw [hc, if_pos (show 64 ≥ IntTy.u64.bits by decide)]
  rfl

/-- Right shifts through the full word width have exact bounded-bit semantics. -/
theorem copyPairRightBit (word : U64) (amount bit : Nat)
    (ha : amount ≤ 64) (hb : bit < 64) :
    packedBit (lshr_int word (int amount)) bit =
      if bit + amount < 64 then packedBit word (bit + amount) else false := by
  by_cases hi : amount < 64
  · rw [dequePackedShiftRight word amount bit hi]
    simp only [hb, decide_true, Bool.true_and]
    by_cases hk : bit + amount < 64
    · rw [if_pos hk]
    · rw [if_neg hk, dequePackedBitHigh word _ (by omega)]
  · have he : amount = 64 := by omega
    subst amount
    rw [copyPairRightFull, packedBit_zero, if_neg (by omega)]

/-- Source gluing reads the consecutive bits of the two-word input. -/
theorem copyPairGlueBit (low high : U64) (offset bit : Nat)
    (ho : offset < 64) (hb : bit < 64) :
    packedBit (copyPairGlue low high offset) bit =
      if bit + offset < 64 then packedBit low (bit + offset)
      else packedBit high (bit + offset - 64) := by
  rw [copyPairGlue, packedBit_or, copyPairRightBit _ offset bit (by omega) hb,
    reversePackedLeft _ (64 - offset) bit (by omega) hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, if_neg (by omega), dequePackedAnd,
      rangeSingleHighMaskBit offset (bit + offset) (by omega) hi]
    simp only [show offset ≤ bit + offset by omega, decide_true, Bool.and_true,
      Bool.or_false, hi, ite_true]
  · rw [if_neg hi, if_pos (by omega)]
    rw [dequePackedAnd, scalar_packedBit_not _ _ (by omega),
      rangeSingleHighMaskBit offset (bit - (64 - offset)) (by omega) (by omega)]
    simp only [show ¬ offset ≤ bit - (64 - offset) by omega, decide_false,
      Bool.not_false, Bool.and_true, Bool.false_or, hi, ite_false]
    congr 1
    omega

/-- Zero-offset gluing reads only the lower source chunk. -/
theorem copyPairGlueZero (low high : U64) : copyPairGlue low high 0 = low := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairGlueBit low high 0 bit (by decide) hb]
  simp only [Nat.add_zero, hb, ite_true]

/-- The aligned pair of packed chunks observes the original logical sequence. -/
theorem copyPairGluePackedBit (xs : List Bool) (offset bit : Nat)
    (ho : offset < 64) (hb : bit < 64) :
    packedBit (copyPairGlue (packedPrefix xs 0 64) (packedPrefix xs 1 64) offset) bit =
      xs.getD (offset + bit) false := by
  rw [copyPairGlueBit _ _ offset bit ho hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, packedWord_bit xs 0 (bit + offset) hi]
    simp only [Nat.zero_mul, Nat.zero_add]
    congr 1
    omega
  · rw [if_neg hi, packedWord_bit xs 1 (bit + offset - 64) (by omega)]
    simp only [Nat.one_mul]
    congr 1
    omega

/-- A destination interval receives an already aligned source word. -/
def copyPairPaste (destination aligned : U64) (offset count : Nat) : U64 :=
  let keep := rangeSingleKeep offset count
  or_int (and_int destination keep)
    (and_int (shl_int aligned (int offset)) (not_int keep))

/-- Pasting changes exactly the selected destination positions. -/
theorem copyPairPasteBit (destination aligned : U64) (offset count bit : Nat)
    (hn : offset + count ≤ 64) (hb : bit < 64) :
    packedBit (copyPairPaste destination aligned offset count) bit =
      if offset ≤ bit ∧ bit < offset + count then packedBit aligned (bit - offset)
      else packedBit destination bit := by
  simp only [copyPairPaste, packedBit_or, dequePackedAnd,
    scalar_packedBit_not _ _ hb, rangeSingleKeepBit offset count bit hn hb]
  by_cases hi : offset ≤ bit ∧ bit < offset + count
  · simp only [show ¬ (bit < offset ∨ offset + count ≤ bit) by omega, decide_false,
      Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_or, hi, and_self, ite_true]
    rw [reversePackedLeft _ offset bit (by omega) hb, if_pos hi.1]
  · simp only [show bit < offset ∨ offset + count ≤ bit by omega, decide_true,
      Bool.not_true, Bool.and_false, Bool.and_true, Bool.or_false, hi, ite_false]

/-- The low destination mask for a spanning copy agrees with a paste through the word boundary. -/
theorem copyPairKeepHigh (offset : Nat) (ho : offset ≤ 64) :
    rangeSingleKeep offset (64 - offset) = not_int (shl_int u64Max (int offset)) := by
  unfold rangeSingleKeep
  rw [show offset + (64 - offset) = 64 by omega, reverseShiftFull, dequePackedOrZero]

/-- The high destination mask for a spanning copy agrees with a paste from bit zero. -/
theorem copyPairKeepLow (count : Nat) (hc : count ≤ 64) :
    rangeSingleKeep 0 count = shl_int u64Max (int count) := by
  apply packedBit_ext
  intro bit hb
  rw [rangeSingleKeepBit 0 count bit (by omega) hb,
    rangeSingleHighMaskBit count bit hc hb]
  simp only [Nat.not_lt_zero, Nat.zero_add, false_or]

/-- Encoding two nonempty packed chunks has their explicit low and high word form. -/
theorem copyPairEncoding (xs : List Bool) (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    encodeBits xs = [packedPrefix xs 0 64, packedPrefix xs 1 64] := by
  rw [packedPrefix_eq_encode]
  have hw : wordCount xs.length = 2 := by unfold wordCount; omega
  rw [hw]
  rfl

/-- The source mask selected by the installed forward-copy routine. -/
def copyPairSourceMask (firstChunk lastChunk firstBit lastBit : I64) : U64 :=
  if lastChunk - firstChunk == int 0 then
    and_int (shl_int u64Max firstBit) (not_int (shl_int u64Max (lastBit + int 1)))
  else shl_int u64Max firstBit

/-- The carry entering the second destination word of a two-word copy. -/
def copyPairCarry (first second : U64) (offset : Nat) : U64 :=
  or_int (lshr_int first (int ((64 - offset : Nat) : Int)))
    (shl_int second (int offset))

/-- A copy confined to one destination chunk may gather its source across a chunk boundary. -/
theorem copyPairOneRun (dest src : Nat) (posD posS : I64) (count offset : Nat)
    (kd ks0 ls0 ks1 ls1 : I64) (s out : State) (destination aligned : U64)
    (hp : 0 < count) (hn : offset + count ≤ 64)
    (hf : ¬ (dest = src ∧ posD > posS))
    (hd0 : getChunksId posD = (kd, int offset))
    (hd1 : getChunksId (posD + int count - int 1) =
      (kd, int ((offset + count - 1 : Nat) : Int)))
    (hs0 : getChunksId posS = (ks0, ls0))
    (hs1 : getChunksId (posS + int count - int 1) = (ks1, ls1))
    (hg : (glueSrcBitChunks src ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run s =
      (.ok aligned, s))
    (hr : (mutableGet dest kd).run s = (.ok destination, s))
    (hw : (mutableSet dest (copyPairPaste destination aligned offset count) kd).run s =
      (.ok (), out)) :
    (copyChunks dest posD src posS (int count)).run s = (.ok (), out) := by
  have hz : (int count == int 0) = false := fillPositiveLength count hp (by omega)
  have hinc : int ((offset + count - 1 : Nat) : Int) + int 1 =
      int ((offset + count : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  simp only [copyPairPaste, rangeSingleKeep] at hw
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, hf, dite_false,
    hd0, hd1, hs0, hs1, shape_int_sub_self, beq_self_eq_true, ite_true, hinc]
  by_cases hsame : (ks1 - ks0 == int 0) = true
  all_goals
    simp only [copyPairSourceMask, hsame, Bool.false_eq_true, ite_true, ite_false] at hg ⊢
    simp only [shape_run_bind, hg, hr, hw, shape_run_pure]

/-- Two destination chunks execute only the two boundary writes; their middle loop is empty. -/
theorem copyPairTwoRun (dest src : Nat) (posD posS count : I64) (offset lastCount : Nat)
    (ks0 ls0 ks1 ls1 : I64) (s mid out : State) (low high first second : U64)
    (ho : offset ≤ 64) (hp : 0 < lastCount) (hn : lastCount ≤ 64)
    (hz : (count == int 0) = false) (hf : ¬ (dest = src ∧ posD > posS))
    (hd0 : getChunksId posD = (int 1, int offset))
    (hd1 : getChunksId (posD + count - int 1) = (int 2, int ((lastCount - 1 : Nat) : Int)))
    (hs0 : getChunksId posS = (ks0, ls0))
    (hs1 : getChunksId (posS + count - int 1) = (ks1, ls1))
    (hg0 : (glueSrcBitChunks src ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run s =
      (.ok first, s))
    (hr0 : (mutableGet dest (int 1)).run s = (.ok low, s))
    (hw0 : (mutableSet dest (copyPairPaste low first offset (64 - offset)) (int 1)).run s =
      (.ok (), mid))
    (hg1 : ((if ks1 ≥ ks0 + int 1 then
      glueSrcBitChunks src (ks0 + int 1) ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0
      else pure (u64 0)) : BitMutationM U64).run mid = (.ok second, mid))
    (hr1 : (mutableGet dest (int 2)).run mid = (.ok high, mid))
    (hw1 : (mutableSet dest (copyPairPaste high (copyPairCarry first second offset) 0 lastCount)
      (int 2)).run mid = (.ok (), out)) :
    (copyChunks dest posD src posS count).run s = (.ok (), out) := by
  have hinc : int ((lastCount - 1 : Nat) : Int) + int 1 = int lastCount := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hsub : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hmask0 := copyPairKeepHigh offset ho
  have hmask1 := copyPairKeepLow lastCount hn
  simp only [copyPairPaste, hmask0] at hw0
  simp only [copyPairPaste, hmask1, copyPairCarry] at hw1
  have hzero : shl_int (copyPairCarry first second offset) (int (0 : Nat)) =
      copyPairCarry first second offset := by
    apply packedBit_ext
    intro bit hb
    rw [reversePackedLeft _ 0 bit (by decide) hb]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  simp only [copyPairCarry] at hzero
  rw [hzero] at hw1
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, hf, dite_false,
    hd0, hd1, hs0, hs1, hinc,
    show int 2 - int 1 = int 1 from rfl,
    show (int 1 == int 0) = false from rfl, ite_false,
    show intRange (int 1) (int 1 - int 1) = [] from rfl,
    List.forIn_nil, hsub]
  by_cases hsame : (ks1 - ks0 == int 0) = true
  all_goals
    simp only [copyPairSourceMask, hsame, Bool.false_eq_true, ite_true, ite_false] at hg0 hg1 ⊢
    by_cases htail : ks1 ≥ ks0 + int 1
    all_goals
      simp only [htail, ite_true, ite_false] at hg1 ⊢
      simp only [shape_run_bind, hg0, hr0, hw0, hg1, hr1, copyPairCarry, hw1, shape_run_pure]

/-- A word-sized window of the logical source, with false defaults beyond its end. -/
def copyPairSlice (xs : List Bool) (start : Nat) : U64 := packedPrefix (xs.drop start) 0 64

/-- A source window exposes consecutive logical positions. -/
theorem copyPairSliceBit (xs : List Bool) (start bit : Nat) (hb : bit < 64) :
    packedBit (copyPairSlice xs start) bit = xs.getD (start + bit) false := by
  rw [copyPairSlice, packedWord_bit _ 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A window beginning after the logical source is the zero word. -/
theorem copyPairSlicePast (xs : List Bool) (start : Nat) (hs : xs.length ≤ start) :
    copyPairSlice xs start = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairSliceBit xs start bit hb, packedBit_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- Gluing a pair of packed source words gives its exact word-sized source window. -/
theorem copyPairGlueSlice (xs : List Bool) (offset : Nat) (ho : offset < 64) :
    copyPairGlue (packedPrefix xs 0 64) (packedPrefix xs 1 64) offset = copyPairSlice xs offset := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairGluePackedBit xs offset bit ho hb, copyPairSliceBit xs offset bit hb]

/-- A final source word can be aligned without consulting a nonexistent later chunk. -/
theorem copyPairTailSlice (xs : List Bool) (offset : Nat)
    (ho : offset < 64) (hn : xs.length ≤ 128) :
    lshr_int (and_int (packedPrefix xs 1 64) (shl_int u64Max (int offset))) (int offset) =
      copyPairSlice xs (64 + offset) := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairRightBit _ offset bit (by omega) hb, copyPairSliceBit xs (64 + offset) bit hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, dequePackedAnd, rangeSingleHighMaskBit offset (bit + offset) (by omega) hi,
      packedWord_bit xs 1 (bit + offset) hi]
    simp only [show offset ≤ bit + offset by omega, decide_true, Bool.and_true, Nat.one_mul]
    congr 1
    omega
  · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- The final source mask clips precisely the existing logical tail of the last chunk. -/
theorem copyPairClippedTailSlice (xs : List Bool) (offset : Nat)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) (ho : offset < xs.length - 64) :
    lshr_int (and_int (packedPrefix xs 1 64)
      (and_int (shl_int u64Max (int offset))
        (not_int (shl_int u64Max (int ((xs.length - 64 : Nat) : Int)))))) (int offset) =
      copyPairSlice xs (64 + offset) := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairRightBit _ offset bit (by omega) hb, copyPairSliceBit xs (64 + offset) bit hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, dequePackedAnd, dequePackedAnd,
      scalar_packedBit_not _ _ hi,
      rangeSingleHighMaskBit offset (bit + offset) (by omega) hi,
      rangeSingleHighMaskBit (xs.length - 64) (bit + offset) (by omega) hi,
      packedWord_bit xs 1 (bit + offset) hi]
    simp only [show offset ≤ bit + offset by omega, decide_true, Bool.true_and, Nat.one_mul]
    by_cases he : xs.length - 64 ≤ bit + offset
    · simp only [he, decide_true, Bool.not_true, Bool.and_false]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    · simp only [he, decide_false, Bool.not_false, Bool.and_true]
      congr 1
      omega
  · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- Carrying between two consecutive aligned windows gives the next destination window. -/
theorem copyPairCarrySliceBit (xs : List Bool) (source offset bit : Nat)
    (ho : offset ≤ 64) (hb : bit < 64) :
    packedBit (or_int
      (lshr_int (copyPairSlice xs source) (int ((64 - offset : Nat) : Int)))
      (shl_int (copyPairSlice xs (source + 64)) (int offset))) bit =
        xs.getD (source + (64 - offset) + bit) false := by
  rw [packedBit_or, copyPairRightBit _ (64 - offset) bit (by omega) hb,
    reversePackedLeft _ offset bit ho hb]
  by_cases hi : bit < offset
  · rw [if_pos (by omega), if_neg (by omega), copyPairSliceBit xs source (bit + (64 - offset)) (by omega),
      Bool.or_false]
    congr 1
    omega
  · rw [if_neg (by omega), if_pos (by omega), copyPairSliceBit xs (source + 64) (bit - offset) (by omega),
      Bool.false_or]
    congr 1
    omega

/-- The packed address of a source position in a two-word vector. -/
def copyPairStartChunk (source : Nat) : I64 := if source < 64 then int 1 else int 2

/-- All positions below 128 have their expected two-word packed address. -/
theorem copyPairAddress (source : Nat) (hs : source < 128) :
    getChunksId (int ((source + 1 : Nat) : Int)) = (copyPairStartChunk source, int ((source % 64 : Nat) : Int)) := by
  have h := scalar_chunks_nat source (by omega)
  rw [copyPairStartChunk]
  by_cases hl : source < 64
  · simpa only [hl, ite_true, Nat.div_eq_of_lt hl, Nat.zero_add, Int.ofNat_one] using h
  · have hd : source / 64 = 1 := by omega
    simpa only [hl, ite_false, hd, show int ((1 + 1 : Nat) : Int) = int 2 from rfl] using h

/-- The gluing primitive reads a two-chunk source without changing storage. -/
theorem copyPairGlueRun (chunks offset : Nat) (low high : U64) (s : State)
    (ho : offset < 64)
    (h0 : (mutableGet chunks (int 1)).run s = (.ok low, s))
    (h1 : (mutableGet chunks (int 2)).run s = (.ok high, s)) :
    (glueSrcBitChunks chunks (int 1) (int 2) (shl_int u64Max (int offset)) (int offset)).run s =
      (.ok (copyPairGlue low high offset), s) := by
  by_cases hp : 0 < offset
  · have hp' : int offset > int 0 := by
      change 0 < (int offset).val
      rw [packedInt_val offset (by omega)]
      omega
    have hshift : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
      rw [dequeIntSub]
      apply congrArg int
      omega
    simp only [glueSrcBitChunks, shape_run_bind, h0,
      show int 2 > int 1 from by decide, hp', and_self, ite_true,
      show int 1 + int 1 = int 2 from rfl, h1, hshift, shape_run_pure, copyPairGlue]
  · have hz : offset = 0 := by omega
    subst offset
    have hzero : lshr_int (and_int low (shl_int u64Max (int (0 : Nat)))) (int (0 : Nat)) = low := by
      apply packedBit_ext
      intro bit hb
      rw [copyPairRightBit _ 0 bit (by decide) hb, if_pos (by omega), dequePackedAnd,
        rangeSingleHighMaskBit 0 (bit + 0) (by decide) (by omega)]
      simp only [Nat.zero_le, decide_true, Bool.and_true, Nat.add_zero]
    simp only [glueSrcBitChunks, shape_run_bind, h0,
      show ¬ int (0 : Nat) > int 0 from by decide, and_false, ite_false,
      shape_run_pure, hzero, copyPairGlueZero]

/-- Gluing the last source chunk needs no read beyond that chunk. -/
theorem copyPairLastRun (chunks : Nat) (offset : I64) (mask word : U64) (s : State)
    (hr : (mutableGet chunks (int 2)).run s = (.ok word, s)) :
    (glueSrcBitChunks chunks (int 2) (int 2) mask offset).run s =
      (.ok (lshr_int (and_int word mask) offset), s) := by
  simp only [glueSrcBitChunks, shape_run_bind, hr,
    show ¬ int 2 > int 2 from by decide, false_and, ite_false, shape_run_pure]

/-- The first source-gather action has the exact logical window for every source position in two chunks. -/
theorem copyPairFirstPackedRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) (hs : source < xs.length)
    (h0 : (mutableGet chunks (int 1)).run s = (.ok (packedPrefix xs 0 64), s))
    (h1 : (mutableGet chunks (int 2)).run s = (.ok (packedPrefix xs 1 64), s)) :
    (glueSrcBitChunks chunks (copyPairStartChunk source) (int 2)
      (copyPairSourceMask (copyPairStartChunk source) (int 2)
        (int ((source % 64 : Nat) : Int)) (int ((xs.length - 65 : Nat) : Int)))
      (int ((source % 64 : Nat) : Int))).run s = (.ok (copyPairSlice xs source), s) := by
  by_cases hl : source < 64
  · simp only [copyPairStartChunk, hl, ite_true, Nat.mod_eq_of_lt hl,
      copyPairSourceMask, show (int 2 - int 1 == int 0) = false from rfl,
      Bool.false_eq_true, ite_false]
    have h := copyPairGlueRun chunks source (packedPrefix xs 0 64) (packedPrefix xs 1 64) s hl h0 h1
    rw [copyPairGlueSlice xs source hl] at h
    exact h
  · have hm : source % 64 = source - 64 := by omega
    have hinc : int ((xs.length - 65 : Nat) : Int) + int 1 = int ((xs.length - 64 : Nat) : Int) := by
      rw [packedInt_add]
      apply congrArg int
      omega
    simp only [copyPairStartChunk, hl, ite_false, hm, copyPairSourceMask,
      show (int 2 - int 2 == int 0) = true from rfl, ite_true, hinc]
    have h := copyPairLastRun chunks (int ((source - 64 : Nat) : Int))
      (and_int (shl_int u64Max (int ((source - 64 : Nat) : Int)))
        (not_int (shl_int u64Max (int ((xs.length - 64 : Nat) : Int)))))
      (packedPrefix xs 1 64) s h1
    rw [copyPairClippedTailSlice xs (source - 64) hp hn (by omega),
      show 64 + (source - 64) = source by omega] at h
    exact h

/-- The optional second source-gather action observes the following logical window, or zero past the end. -/
theorem copyPairNextPackedRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hp : 64 < xs.length) (hn : xs.length ≤ 128) (hs : source < xs.length)
    (h1 : (mutableGet chunks (int 2)).run s = (.ok (packedPrefix xs 1 64), s)) :
    ((if int 2 ≥ copyPairStartChunk source + int 1 then
      glueSrcBitChunks chunks (copyPairStartChunk source + int 1) (int 2)
        (copyPairSourceMask (copyPairStartChunk source) (int 2)
          (int ((source % 64 : Nat) : Int)) (int ((xs.length - 65 : Nat) : Int)))
        (int ((source % 64 : Nat) : Int))
      else pure (u64 0)) : BitMutationM U64).run s = (.ok (copyPairSlice xs (source + 64)), s) := by
  by_cases hl : source < 64
  · simp only [copyPairStartChunk, hl, ite_true, Nat.mod_eq_of_lt hl,
      show int 1 + int 1 = int 2 from rfl, show int 2 ≥ int 2 from by decide,
      copyPairSourceMask, show (int 2 - int 1 == int 0) = false from rfl,
      Bool.false_eq_true, ite_false]
    have h := copyPairLastRun chunks (int source) (shl_int u64Max (int source))
      (packedPrefix xs 1 64) s h1
    rw [copyPairTailSlice xs source hl hn, Nat.add_comm 64 source] at h
    exact h
  · simp only [copyPairStartChunk, hl, ite_false,
      show ¬ int 2 ≥ int 2 + int 1 from by decide, shape_run_pure,
      copyPairSlicePast xs (source + 64) (by omega)]

/-- Reading the low word of canonical two-chunk storage preserves that storage. -/
theorem copyPairReadLow (low high : U64) (spare : Nat) :
    (mutableGet 0 (int 1)).run (dequeWordStore [low, high] spare) =
      (.ok low, dequeWordStore [low, high] spare) := by
  simpa only [List.getD_cons_zero, Nat.zero_add, Int.ofNat_one] using
    dequeWordRead [low, high] spare 0 (by simp) (by simp)

/-- Reading the high word of canonical two-chunk storage preserves that storage. -/
theorem copyPairReadHigh (low high : U64) (spare : Nat) :
    (mutableGet 0 (int 2)).run (dequeWordStore [low, high] spare) =
      (.ok high, dequeWordStore [low, high] spare) := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero,
    show int ((1 + 1 : Nat) : Int) = int 2 from rfl] using
    dequeWordRead [low, high] spare 1 (by simp) (by simp)

/-- Updating the low word retains the untouched high word and spare capacity. -/
theorem copyPairSetLow (low high word : U64) (spare : Nat) :
    (mutableSet 0 word (int 1)).run (dequeWordStore [low, high] spare) =
      (.ok (), dequeWordStore [word, high] spare) := by
  simpa only [List.set_cons_zero, Nat.zero_add, Int.ofNat_one] using
    dequeWordSet [low, high] spare 0 word (by simp) (by simp)

/-- Updating the high word retains the untouched low word and spare capacity. -/
theorem copyPairSetHigh (low high word : U64) (spare : Nat) :
    (mutableSet 0 word (int 2)).run (dequeWordStore [low, high] spare) =
      (.ok (), dequeWordStore [low, word] spare) := by
  simpa only [List.set_cons_succ, List.set_cons_zero,
    show int ((1 + 1 : Nat) : Int) = int 2 from rfl] using
    dequeWordSet [low, high] spare 1 word (by simp) (by simp)

/-- The final logical position in a two-word vector lies at its expected high-word offset. -/
theorem copyPairFinalAddress (n : Nat) (hp : 64 < n) (hn : n ≤ 128) :
    getChunksId (int n) = (int 2, int ((n - 65 : Nat) : Int)) := by
  have h := copyPairAddress (n - 1) (by omega)
  have hs : n - 1 + 1 = n := by omega
  have hm : (n - 1) % 64 = n - 65 := by omega
  simpa only [hs, copyPairStartChunk, show ¬ n - 1 < 64 by omega, ite_false, hm] using h

/-- Every positive two-word logical length has exactly two packed chunks. -/
theorem rangePairChunkCount (n : Nat) (hp : 64 < n) (hn : n ≤ 128) :
    numBitChunks (int n) = int 2 := by
  apply Subtype.ext
  rw [scalar_num_chunks _ (by rw [packedInt_val n (by omega)]; omega), packedInt_val n (by omega)]
  change ((n : Int) + 63) / 64 = 2
  omega
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

/-- A full aligned paste replaces the entire word. -/
theorem copyPairPasteFull (destination aligned : U64) :
    copyPairPaste destination aligned 0 64 = aligned := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 64 bit (by decide) hb, if_pos (by omega)]
  simp only [Nat.sub_zero]

/-- A zero-offset carry consists exactly of the second gathered word. -/
theorem copyPairCarryZero (first second : U64) : copyPairCarry first second 0 = second := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairCarry, packedBit_or, copyPairRightBit _ 64 bit (by decide) hb,
    reversePackedLeft _ 0 bit (by decide) hb]
  simp only [show ¬ bit + 64 < 64 by omega, ite_false, Nat.zero_le, ite_true, Nat.sub_zero, Bool.false_or]
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

/-- Zero alignment with the complete source mask leaves the source word unchanged. -/
theorem shiftPairNoShiftMask (word : U64) :
    lshr_int (and_int word (shl_int u64Max (int (0 : Nat)))) (int (0 : Nat)) = word := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairRightBit _ 0 bit (by decide) hb, if_pos (by omega), dequePackedAnd,
    rangeSingleHighMaskBit 0 (bit + 0) (by decide) (by omega)]
  simp only [Nat.zero_le, decide_true, Bool.and_true, Nat.add_zero]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Low source bits selected for the final block of a rightward copy. -/
def resizeFrontPairClip (word : U64) (count : Nat) : U64 :=
  and_int word (not_int (shl_int u64Max (int count)))
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

/-- Source clipping preserves precisely the requested low bits. -/
theorem resizeFrontPairClipBit (word : U64) (count bit : Nat)
    (hc : count ≤ 64) (hb : bit < 64) :
    packedBit (resizeFrontPairClip word count) bit =
      if bit < count then packedBit word bit else false := by
  rw [resizeFrontPairClip, dequePackedAnd, scalar_packedBit_not _ _ hb,
    rangeSingleHighMaskBit count bit hc hb]
  by_cases hi : bit < count
  · simp only [show ¬ count ≤ bit by omega, decide_false, Bool.not_false, Bool.and_true, hi, ite_true]
  · simp only [show count ≤ bit by omega, decide_true, Bool.not_true, Bool.and_false, hi, ite_false]
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

abbrev FrontCopyRegisters := I64 × I64 × I64 × I64 × I64

/-- The single block copied by each iteration of the frozen descending routine. -/
def frontCopyBlock (chunks : Nat) (pd ps count : I64) : BitMutationM Unit := do
  let (kd0, ld0) := getChunksId pd
  let (kd1, ld1) := getChunksId (pd + count - int 1)
  let (ks0, ls0) := getChunksId ps
  let (ks1, ls1) := getChunksId (ps + count - int 1)
  let deltaKD := kd1 - kd0
  let deltaKS := ks1 - ks0
  let u := u64Max
  let mut mskD0 := not_int (shl_int u ld0)
  let mskD1 := shl_int u (ld1 + int 1)
  if deltaKD == int 0 then mskD0 := or_int mskD0 mskD1
  let mut mskS0 := shl_int u ls0
  if deltaKS == int 0 then mskS0 := and_int mskS0 (not_int (shl_int u (ls1 + int 1)))
  let chunkS0 := and_int (← glueSrcBitChunks chunks ks0 ks1 mskS0 ls0) (not_int (shl_int u count))
  let destD0 ← mutableGet chunks kd0
  mutableSet chunks (or_int (and_int destD0 mskD0)
    (and_int (shl_int chunkS0 ld0) (not_int mskD0))) kd0
  if deltaKD != int 0 then
    let chunkS := lshr_int chunkS0 (int 64 - ld0)
    let destD1 ← mutableGet chunks kd1
    mutableSet chunks (or_int (and_int destD1 mskD1)
      (and_int chunkS (not_int mskD1))) kd1

/-- Registers are recomputed from the number of source bits that remain. -/
def frontCopyRegisters (posD posS left : I64) : FrontCopyRegisters :=
  let count := if left < int 64 then left else int 64
  let before := left - count
  (left, count, before, posS + before, posD + before)

/-- One loop iteration changes only its copied block and remaining register count. -/
def frontCopyStep (chunks : Nat) (posD posS : I64) (r : FrontCopyRegisters) :
    BitMutationM (ForInStep FrontCopyRegisters) := do
  if r.1 > int 0 then
    frontCopyBlock chunks r.2.2.2.2 r.2.2.2.1 r.2.1
    pure (.yield (frontCopyRegisters posD posS (r.1 - r.2.1)))
  else pure (.done r)

def frontCopyLoop (chunks : Nat) (posD posS : I64) (r : FrontCopyRegisters) :
    BitMutationM FrontCopyRegisters :=
  forIn ({} : Lean.Loop) r (fun _ r => frontCopyStep chunks posD posS r)

/-- A fixed continuation distributes over a chosen monadic branch. -/
theorem frontCopyBindIte {α β : Type} (p : Prop) [Decidable p]
    (yes no : BitMutationM α) (f : α → BitMutationM β) :
    ((if p then yes else no) >>= f) = (if p then yes >>= f else no >>= f) := by
  split <;> rfl

/-- Factoring the installed descending copy preserves its exact loop and block order. -/
theorem frontCopyFactor (chunks : Nat) (posD posS count : I64)
    (hne : (posD == posS) = false) (horder : ¬ posD < posS) :
    copyChunksRtol chunks posD posS count = (do
      let _ ← frontCopyLoop chunks posD posS (frontCopyRegisters posD posS count)
      pure ()) := by
  simp only [copyChunksRtol, hne, Bool.false_eq_true, ite_false, horder, dite_false,
    frontCopyLoop, frontCopyStep, frontCopyRegisters, frontCopyBlock,
    bind_assoc, pure_bind, frontCopyBindIte]

/-- Abstract successful block execution supplies the yielding iteration. -/
theorem frontCopyStepFrom (chunks : Nat) (posD posS : I64) (r : FrontCopyRegisters)
    (s out : State) (hp : r.1 > int 0)
    (hb : (frontCopyBlock chunks r.2.2.2.2 r.2.2.2.1 r.2.1).run s = (.ok (), out)) :
    (frontCopyStep chunks posD posS r).run s =
      (.ok (.yield (frontCopyRegisters posD posS (r.1 - r.2.1))), out) := by
  simp only [frontCopyStep, hp, ite_true, shape_run_bind, hb, shape_run_pure]

/-- A nonpositive remaining bit count exits without inspecting storage. -/
theorem frontCopyLoopDone (chunks : Nat) (posD posS : I64) (r : FrontCopyRegisters)
    (s : State) (hp : ¬ r.1 > int 0) :
    (frontCopyLoop chunks posD posS r).run s = (.ok r, s) := by
  apply reverseLoopDone
  simp only [frontCopyStep, hp, ite_false, shape_run_pure]

/-- A completed block composes with a known remaining loop execution. -/
theorem frontCopyLoopYield (chunks : Nat) (posD posS : I64) (r final : FrontCopyRegisters)
    (s mid out : State) (hp : r.1 > int 0)
    (hb : (frontCopyBlock chunks r.2.2.2.2 r.2.2.2.1 r.2.1).run s = (.ok (), mid))
    (ht : (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (r.1 - r.2.1))).run mid =
      (.ok final, out)) :
    (frontCopyLoop chunks posD posS r).run s = (.ok final, out) := by
  exact reverseLoopYield _ r _ final s mid out (frontCopyStepFrom chunks posD posS r s mid hp hb) ht

/-- A completed factored loop supplies the actual descending-copy action. -/
theorem frontCopyRtolFromLoop (chunks : Nat) (posD posS count : I64) (s out : State)
    (final : FrontCopyRegisters) (hne : (posD == posS) = false) (horder : ¬ posD < posS)
    (hl : (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS count)).run s =
      (.ok final, out)) :
    (copyChunksRtol chunks posD posS count).run s = (.ok (), out) := by
  rw [frontCopyFactor chunks posD posS count hne horder]
  simp only [shape_run_bind, hl, shape_run_pure]

/-- Append an arbitrary packed-word allocation and its one-based vector header. -/
def shiftFreshHeap (s : State) (slots : List (Option U64)) : State :=
  ⟨s.memories ++ [slots], s.arrays ++ [⟨(s.memories.length, one), int slots.length⟩]⟩

/-- The appended header exposes exactly its allocated word count. -/
theorem shiftFreshHeader (s : State) (slots : List (Option U64)) :
    (shiftFreshHeap s slots).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), int slots.length⟩ := by
  simp only [shiftFreshHeap, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- The appended allocation retains its complete slot list. -/
theorem shiftFreshMemory (s : State) (slots : List (Option U64)) :
    (shiftFreshHeap s slots).memories[s.memories.length]? = some slots := by
  simp only [shiftFreshHeap, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- A valid header-backed write modifies one slot and no header. -/
theorem shiftFreshSetFrom (s : State) (handle mem : Nat) (slots : List (Option U64)) (n j : I64) (word : U64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some slots) (hn : n.val ≤ (slots.length : Int))
    (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    (mutableSet handle word j).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (j.val - 1).toNat (some word))}) := by
  have hin : one ≤ j ∧ j ≤ n := hj
  have hw := resizeMemoryWrite s slots mem hm j word (by omega)
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hin, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_one_add_sub_one, hw]

/-- A valid initialized slot can be read through any one-based array header. -/
theorem shiftFreshReadFrom (s : State) (handle mem : Nat) (slots : List (Option U64))
    (n j : I64) (word : U64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some slots)
    (hj : 1 ≤ j.val ∧ j.val ≤ n.val)
    (hg : slots[(j.val - 1).toNat]? = some (some word)) :
    (mutableGet handle j).run s = (.ok word, s) := by
  have hb : 1 ≤ j.val ∧ j ≤ n := hj
  have hindex : (one.val + j.val - 2).toNat = (j.val - 1).toNat := by
    change (1 + j.val - 2).toNat = _
    congr 1
    omega
  simp only [mutableGet, mutableVector, memoryRead, shape_run_bind, shape_run_get,
    ha, hm, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, hindex, hg]

/-- Writing an appended slot preserves the earlier heap and the fresh allocation length. -/
theorem shiftFreshSet (s : State) (slots : List (Option U64)) (j : Nat) (word : U64)
    (hn : slots.length ≤ 9223372036854775807) (hj : j < slots.length) :
    (mutableSet s.arrays.length word (int ((j + 1 : Nat) : Int))).run (shiftFreshHeap s slots) =
      (.ok (), shiftFreshHeap s (slots.set j (some word))) := by
  have hsize := packedInt_val slots.length hn
  have hi := packedInt_val (j + 1) (by omega)
  have hindex : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by rw [hi]; omega
  have h := shiftFreshSetFrom (shiftFreshHeap s slots) s.arrays.length s.memories.length slots
    (int slots.length) (int ((j + 1 : Nat) : Int)) word
    (shiftFreshHeader s slots) (shiftFreshMemory s slots)
    (by rw [hsize]; omega) (by rw [hi, hsize]; omega)
  rw [h, hindex]
  simp only [shiftFreshHeap, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero, List.length_set]

/-- Reading an initialized appended slot returns its exact stored word. -/
theorem shiftFreshRead (s : State) (slots : List (Option U64)) (j : Nat) (word : U64)
    (hn : slots.length ≤ 9223372036854775807) (hj : j < slots.length)
    (hg : slots[j]? = some (some word)) :
    (mutableGet s.arrays.length (int ((j + 1 : Nat) : Int))).run (shiftFreshHeap s slots) =
      (.ok word, shiftFreshHeap s slots) := by
  have hsize := packedInt_val slots.length hn
  have hi := packedInt_val (j + 1) (by omega)
  have hindex : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by rw [hi]; omega
  exact shiftFreshReadFrom _ _ _ slots _ _ word (shiftFreshHeader s slots) (shiftFreshMemory s slots)
    (by rw [hi, hsize]; omega) (by rw [hindex]; exact hg)

/-- The fresh header supplies its exact native allocation length. -/
theorem shiftFreshLength (s : State) (slots : List (Option U64)) :
    (mutableLength s.arrays.length).run (shiftFreshHeap s slots) =
      (.ok (int slots.length), shiftFreshHeap s slots) :=
  shiftSingleLengthFrom _ _ _ _ (shiftFreshHeader s slots)

/-- The fresh vector's visible contents are its entire bounded slot allocation. -/
theorem shiftFreshContents (s : State) (slots : List (Option U64))
    (hn : slots.length ≤ 9223372036854775807) :
    (shiftFreshHeap s slots).contents s.arrays.length = slots := by
  simp only [MutableMemory.contents, shiftFreshHeader, shiftFreshMemory, Option.getD_some,
    packedInt_val slots.length hn]
  change slots.take slots.length = slots
  exact List.take_length

/-- Constructing a fresh array header after memory allocation leaves all previous arrays intact. -/
theorem shiftFreshAllocateFrom (n : I64) (s : State) (slots : List (Option U64))
    (hl : int slots.length = n)
    (hm : (memoryUndef (some ⟨8, false, false⟩) (mutableFreshMemory 0) mutableFreshMemory n).run s =
      (.ok s.memories.length, {s with memories := s.memories ++ [slots]})) :
    (mutableAllocate (some ⟨8, false, false⟩) 0 n).run s =
      (.ok s.arrays.length, shiftFreshHeap s slots) := by
  simp only [mutableAllocate, arrayUndef1, shape_run_bind, hm, List.headD_cons,
    shiftFreshHeap, hl]
  rfl

/-- Fresh bounded chunk allocation appends the requested number of unspecified slots. -/
theorem shiftFreshAllocate (s : State) (n : Nat) (hn : n ≤ 576460752303423488) :
    (allocateChunkVectorModel n).run s =
      (.ok s.arrays.length, shiftFreshHeap s (List.replicate n none)) := by
  have hm := growthAllocate s 0 n hn
  simp only [mutableStorage, uint64AllocationLayout] at hm
  exact shiftFreshAllocateFrom (int n) s (List.replicate n none) (by rw [List.length_replicate]) hm

/-- Appending a destination preserves every initialized source chunk. -/
theorem shiftFreshSource (words : List U64) (slots : List (Option U64)) (j : Nat)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableGet 0 (int ((j + 1 : Nat) : Int))).run (shiftFreshHeap (initWords words) slots) =
      (.ok (words.getD j (u64 0)), shiftFreshHeap (initWords words) slots) := by
  have hsize := packedInt_val words.length hn
  have hi := packedInt_val (j + 1) (by omega)
  have hindex : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by rw [hi]; omega
  have ha : (shiftFreshHeap (initWords words) slots).arrays[0]? = some ⟨(0, one), int words.length⟩ := by
    change some (⟨(0, one), int (words.map some).length⟩ : MutableVector) = _
    rw [List.length_map]
  have hm : (shiftFreshHeap (initWords words) slots).memories[0]? =
      some (words.map some ++ List.replicate 32 none) := rfl
  have hg : (words.map some ++ List.replicate 32 none)[j]? = some (some (words.getD j (u64 0))) := by
    rw [List.getElem?_append_left (by rw [List.length_map]; exact hj), List.getElem?_map,
      List.getElem?_eq_getElem hj, List.getElem_eq_getD]
    rfl
  exact shiftFreshReadFrom _ 0 0 _ _ _ _ ha hm (by rw [hi, hsize]; omega)
    (by rw [hindex]; exact hg)

/-- Appending any destination retains the source vector's chunk count. -/
theorem shiftFreshSourceLength (words : List U64) (slots : List (Option U64)) :
    (mutableLength 0).run (shiftFreshHeap (initWords words) slots) =
      (.ok (int words.length), shiftFreshHeap (initWords words) slots) := by
  have ha : (shiftFreshHeap (initWords words) slots).arrays[0]? = some ⟨(0, one), int words.length⟩ := by
    change some (⟨(0, one), int (words.map some).length⟩ : MutableVector) = _
    rw [List.length_map]
  exact shiftSingleLengthFrom _ _ _ _ ha

/-- Reading an optional-slot update changes exactly its chosen index. -/
theorem shiftFreshGetSet (slots : List (Option U64)) (i j : Nat) (value : Option U64)
    (hi : i < slots.length) :
    (slots.set i value).getD j none = if i = j then value else slots.getD j none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hi, and_self, ite_true]
  by_cases he : i = j <;> simp only [he, ite_true, ite_false, Option.getD_some]

/-- An arbitrary indexed-write fold preserves allocation length. -/
theorem shiftFreshFoldLength (indices : List Nat) (slots : List (Option U64)) (value : Nat → Option U64) :
    (indices.foldl (fun ws j => ws.set j (value j)) slots).length = slots.length := by
  induction indices generalizing slots with
  | nil => rfl
  | cons i indices ih => rw [List.foldl_cons, ih, List.length_set]

/-- Indexed-write folds install exactly the values at visited slots. -/
theorem shiftFreshFoldGet (indices : List Nat) (value : Nat → Option U64) :
    ∀ (slots : List (Option U64)), (∀ i ∈ indices, i < slots.length) → ∀ j : Nat,
    (indices.foldl (fun ws i => ws.set i (value i)) slots).getD j none =
      if j ∈ indices then value j else slots.getD j none := by
  induction indices with
  | nil =>
    intro slots _ j
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons i indices ih =>
    intro slots hi j
    have hib := hi i List.mem_cons_self
    have hr := ih (slots.set i (value i))
      (by intro k hk; rw [List.length_set]; exact hi k (List.mem_cons_of_mem i hk)) j
    rw [List.foldl_cons, hr]
    by_cases hj : j ∈ indices
    · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
    · rw [if_neg hj, shiftFreshGetSet slots i j (value i) hib]
      by_cases he : i = j
      · subst j
        rw [if_pos rfl, if_pos List.mem_cons_self]
      · have hnot : ¬ j ∈ i :: indices := by
          intro hmem
          rcases List.mem_cons.mp hmem with hmem | hmem
          · exact he hmem.symm
          · exact hj hmem
        rw [if_neg he, if_neg hnot]

/-- Visiting the whole allocation produces the complete requested indexed-value list. -/
theorem shiftFreshFoldAll (slots : List (Option U64)) (value : Nat → Option U64) :
    (List.range slots.length).foldl (fun ws i => ws.set i (value i)) slots =
      (List.range slots.length).map value := by
  apply List.ext_getElem
  · rw [shiftFreshFoldLength, List.length_map, List.length_range]
  · intro j hj hj'
    have hb : j < slots.length := by rw [shiftFreshFoldLength] at hj; exact hj
    rw [List.getElem_eq_getD (fallback := none),
      shiftFreshFoldGet (List.range slots.length) value slots
        (by intro i hi; exact List.mem_range.mp hi) j,
      if_pos (List.mem_range.mpr hb)]
    simp only [List.getElem_map, List.getElem_range]

/-- A constant indexed fill initializes every visible optional slot. -/
theorem shiftFreshFoldConstant (slots : List (Option U64)) (value : U64) :
    (List.range slots.length).foldl (fun ws i => ws.set i (some value)) slots =
      List.replicate slots.length (some value) := by
  rw [shiftFreshFoldAll]
  simpa only [List.length_range] using (List.map_const' (l := List.range slots.length) (b := some value))

/-- A complete indexed copy installs the source words regardless of initial destination contents. -/
theorem shiftFreshFoldCopy (words : List U64) (slots : List (Option U64)) (hl : slots.length = words.length) :
    (List.range words.length).foldl (fun ws i => ws.set i (some (words.getD i (u64 0)))) slots =
      words.map some := by
  rw [← hl, shiftFreshFoldAll]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hl]
  · intro j hj hj'
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem_eq_getD]

/-- A native fresh-allocation write loop executes the corresponding indexed slot fold. -/
theorem shiftFreshWriteLoop (s : State) (indices : List Nat) (slots : List (Option U64)) (value : Nat → U64)
    (hn : slots.length ≤ 9223372036854775807) (hi : ∀ i ∈ indices, i < slots.length) :
    (forIn indices PUnit.unit (fun i _ => do
      mutableSet s.arrays.length (value i) (int ((i + 1 : Nat) : Int))
      pure (ForInStep.yield PUnit.unit))).run (shiftFreshHeap s slots) =
      (.ok PUnit.unit, shiftFreshHeap s (indices.foldl (fun ws i => ws.set i (some (value i))) slots)) := by
  exact dequeForInFold (fun i => mutableSet s.arrays.length (value i) (int ((i + 1 : Nat) : Int)))
    (fun ws i => ws.set i (some (value i))) (shiftFreshHeap s)
    (fun ws => ws.length = slots.length) indices
    (by intro ws hw i hi'; exact shiftFreshSet s ws i (value i) (by rw [hw]; exact hn) (by rw [hw]; exact hi i hi'))
    (by intro ws hw i _; rw [List.length_set]; exact hw) slots rfl

/-- Every supported nonnegative logical length has its exact natural packed-word count. -/
theorem shiftFreshNumChunks (n : Nat) (hn : n ≤ 9223372036854775807) :
    numBitChunks (int n) = int (wordCount n) := by
  have hm : wordCount n ≤ 9223372036854775807 := by unfold wordCount; omega
  apply Subtype.ext
  rw [scalar_num_chunks _ (by rw [packedInt_val n hn]; omega), packedInt_val n hn,
    packedInt_val (wordCount n) hm]
  unfold wordCount
  omega

/-- Initial packed allocation specifies only the final chunk's zero padding. -/
def shiftFreshInitial (n : Nat) : List (Option U64) :=
  (List.replicate (wordCount n) none).set (wordCount n - 1) (some (u64 0))

theorem shiftFreshInitialLength (n : Nat) : (shiftFreshInitial n).length = wordCount n := by
  simp only [shiftFreshInitial, List.length_set, List.length_replicate]

/-- Filling all new chunks converts final-word-only initialization into the exact all-false encoding. -/
theorem shiftFreshZeroSlots (n : Nat) :
    List.replicate (wordCount n) (some (u64 0)) = (encodeBits (List.replicate n false)).map some := by
  rw [fillFalseEncoding, List.map_replicate]

/-- Every in-bounds encoded word is the corresponding logical packed prefix. -/
theorem shiftNearLeftEncodedGet (xs : List Bool) (chunk : Nat) (hc : chunk < wordCount xs.length) :
    (encodeBits xs).getD chunk (u64 0) = packedPrefix xs chunk 64 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [packedEncoded_length]; exact hc), Option.getD_some]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]

/-- Gluing arbitrary adjacent encoded chunks yields the corresponding consecutive logical window. -/
theorem shiftNearGlueSlice (xs : List Bool) (chunk offset : Nat) (ho : offset < 64) :
    copyPairGlue (packedPrefix xs chunk 64) (packedPrefix xs (chunk + 1) 64) offset =
      copyPairSlice xs (chunk * 64 + offset) := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairGlueBit _ _ offset bit ho hb, copyPairSliceBit xs _ bit hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, packedWord_bit xs chunk (bit + offset) hi]
    congr 1
    omega
  · rw [if_neg hi, packedWord_bit xs (chunk + 1) (bit + offset - 64) (by omega)]
    congr 1
    omega

/-- Clipping and aligning the final source chunk gives its exact logical suffix window. -/
theorem shiftNearClippedSlice (xs : List Bool) (chunk offset limit : Nat)
    (ho : offset < limit) (hl : limit ≤ 64) (hn : xs.length = chunk * 64 + limit) :
    lshr_int (and_int (packedPrefix xs chunk 64)
      (and_int (shl_int u64Max (int offset)) (not_int (shl_int u64Max (int limit))))) (int offset) =
      copyPairSlice xs (chunk * 64 + offset) := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairRightBit _ offset bit (by omega) hb, copyPairSliceBit xs _ bit hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, dequePackedAnd, dequePackedAnd, scalar_packedBit_not _ _ hi,
      rangeSingleHighMaskBit offset (bit + offset) (by omega) hi,
      rangeSingleHighMaskBit limit (bit + offset) hl hi,
      packedWord_bit xs chunk (bit + offset) hi]
    simp only [show offset ≤ bit + offset by omega, decide_true, Bool.true_and]
    by_cases he : limit ≤ bit + offset
    · simp only [he, decide_true, Bool.not_true, Bool.and_false]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    · simp only [he, decide_false, Bool.not_false, Bool.and_true]
      congr 1
      omega
  · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- Gluing the final available source chunk never reads beyond that chunk. -/
theorem shiftNearGlueLastRun (chunks : Nat) (k offset : I64) (mask word : U64) (s : State)
    (hr : (mutableGet chunks k).run s = (.ok word, s)) :
    (glueSrcBitChunks chunks k k mask offset).run s =
      (.ok (lshr_int (and_int word mask) offset), s) := by
  have hk : ¬ k > k := Int.lt_irrefl _
  simp only [glueSrcBitChunks, shape_run_bind, hr, hk, false_and, ite_false, shape_run_pure]

/-- Gluing adjacent source chunks at any supported native address preserves the state. -/
theorem shiftNearGluePairRun (chunks chunk offset : Nat) (low high : U64) (s : State)
    (hk : chunk + 2 ≤ 9223372036854775807) (hp : 0 < offset) (ho : offset < 64)
    (h0 : (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok low, s))
    (h1 : (mutableGet chunks (int ((chunk + 2 : Nat) : Int))).run s = (.ok high, s)) :
    (glueSrcBitChunks chunks (int ((chunk + 1 : Nat) : Int)) (int ((chunk + 2 : Nat) : Int))
      (shl_int u64Max (int offset)) (int offset)).run s = (.ok (copyPairGlue low high offset), s) := by
  have hgt : int ((chunk + 2 : Nat) : Int) > int ((chunk + 1 : Nat) : Int) := by
    change (int ((chunk + 1 : Nat) : Int)).val < (int ((chunk + 2 : Nat) : Int)).val
    rw [packedInt_val (chunk + 1) (by omega), packedInt_val (chunk + 2) hk]
    omega
  have hoff : int offset > int 0 := by
    change 0 < (int offset).val
    rw [packedInt_val offset (by omega)]
    omega
  have hplus : int ((chunk + 1 : Nat) : Int) + int 1 = int ((chunk + 2 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hshift : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  simp only [glueSrcBitChunks, shape_run_bind, h0, hgt, hoff, and_self, ite_true,
    hplus, h1, hshift, shape_run_pure, copyPairGlue]

/-- A suffix of at most 64 bits can be gathered from its final one or two source chunks. -/
theorem shiftNearGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length) (hk : xs.length - source ≤ 64)
    (hr : ∀ chunk, chunk < wordCount xs.length →
      (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s)) :
    (glueSrcBitChunks chunks
      (int ((source / 64 + 1 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
      (copyPairSourceMask
        (int ((source / 64 + 1 : Nat) : Int))
        (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
        (int ((source % 64 : Nat) : Int))
        (int (((xs.length - 1) % 64 : Nat) : Int)))
      (int ((source % 64 : Nat) : Int))).run s = (.ok (copyPairSlice xs source), s) := by
  let chunk := source / 64
  let last := (xs.length - 1) / 64
  let offset := source % 64
  let finalBit := (xs.length - 1) % 64
  have hoff : offset < 64 := Nat.mod_lt _ (by decide)
  have hfinal : finalBit < 64 := Nat.mod_lt _ (by decide)
  have hsource : source = chunk * 64 + offset := by dsimp only [chunk, offset]; omega
  have hlength : xs.length = last * 64 + (finalBit + 1) := by dsimp only [last, finalBit]; omega
  have hcount : wordCount xs.length = last + 1 := by unfold wordCount; dsimp only [last]; omega
  change (glueSrcBitChunks chunks (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
    (copyPairSourceMask (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
      (int offset) (int finalBit)) (int offset)).run s = _
  by_cases he : last = chunk
  · have hinc : int finalBit + int 1 = int ((finalBit + 1 : Nat) : Int) := by rw [packedInt_add]; rfl
    simp only [he, copyPairSourceMask, shape_int_sub_self, beq_self_eq_true, ite_true, hinc]
    have h := shiftNearGlueLastRun chunks (int ((chunk + 1 : Nat) : Int)) (int offset)
      (and_int (shl_int u64Max (int offset)) (not_int (shl_int u64Max (int ((finalBit + 1 : Nat) : Int)))))
      (packedPrefix xs chunk 64) s (hr chunk (by rw [hcount, he]; omega))
    rw [shiftNearClippedSlice xs chunk offset (finalBit + 1) (by omega) (by omega) (by rw [hlength, he]), ← hsource] at h
    exact h
  · have he' : last = chunk + 1 := by omega
    have hdelta : int ((chunk + 2 : Nat) : Int) - int ((chunk + 1 : Nat) : Int) = int 1 := by
      rw [dequeIntSub]
      apply congrArg int
      omega
    rw [he']
    simp only [show chunk + 1 + 1 = chunk + 2 by omega, copyPairSourceMask, hdelta,
      show (int 1 == int 0) = false from rfl, Bool.false_eq_true, ite_false]
    have h := shiftNearGluePairRun chunks chunk offset (packedPrefix xs chunk 64)
      (packedPrefix xs (chunk + 1) 64) s (by omega) (by omega) hoff
      (hr chunk (by rw [hcount, he']; omega)) (by
        have h' := hr (chunk + 1) (by rw [hcount, he']; omega)
        simpa only [show chunk + 1 + 1 = chunk + 2 by omega] using h')
    rw [shiftNearGlueSlice xs chunk offset hoff, ← hsource] at h
    exact h

/-- Two destination chunks execute only the two boundary writes; their middle loop is empty. -/
theorem shiftNearTwoRun (dest src : Nat) (posD posS count : I64) (offset lastCount : Nat)
    (kd0 kd1 ks0 ls0 ks1 ls1 : I64) (s mid out : State) (low high first second : U64)
    (ho : offset ≤ 64) (hp : 0 < lastCount) (hn : lastCount ≤ 64)
    (hz : (count == int 0) = false) (hf : ¬ (dest = src ∧ posD > posS))
    (hdiff : kd1 - kd0 = int 1)
    (hd0 : getChunksId posD = (kd0, int offset))
    (hd1 : getChunksId (posD + count - int 1) = (kd1, int ((lastCount - 1 : Nat) : Int)))
    (hs0 : getChunksId posS = (ks0, ls0))
    (hs1 : getChunksId (posS + count - int 1) = (ks1, ls1))
    (hg0 : (glueSrcBitChunks src ks0 ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0).run s =
      (.ok first, s))
    (hr0 : (mutableGet dest kd0).run s = (.ok low, s))
    (hw0 : (mutableSet dest (copyPairPaste low first offset (64 - offset)) kd0).run s =
      (.ok (), mid))
    (hg1 : ((if ks1 ≥ ks0 + int 1 then
      glueSrcBitChunks src (ks0 + int 1) ks1 (copyPairSourceMask ks0 ks1 ls0 ls1) ls0
      else pure (u64 0)) : BitMutationM U64).run mid = (.ok second, mid))
    (hr1 : (mutableGet dest kd1).run mid = (.ok high, mid))
    (hw1 : (mutableSet dest (copyPairPaste high (copyPairCarry first second offset) 0 lastCount)
      kd1).run mid = (.ok (), out)) :
    (copyChunks dest posD src posS count).run s = (.ok (), out) := by
  have hinc : int ((lastCount - 1 : Nat) : Int) + int 1 = int lastCount := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hsub : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hmask0 := copyPairKeepHigh offset ho
  have hmask1 := copyPairKeepLow lastCount hn
  simp only [copyPairPaste, hmask0] at hw0
  simp only [copyPairPaste, hmask1, copyPairCarry] at hw1
  have hzero : shl_int (copyPairCarry first second offset) (int (0 : Nat)) =
      copyPairCarry first second offset := by
    apply packedBit_ext
    intro bit hb
    rw [reversePackedLeft _ 0 bit (by decide) hb]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  simp only [copyPairCarry] at hzero
  rw [hzero] at hw1
  simp only [copyChunks, hz, Bool.false_eq_true, ite_false, hf, dite_false,
    hd0, hd1, hs0, hs1, hinc,
    hdiff,
    show (int 1 == int 0) = false from rfl, ite_false,
    show intRange (int 1) (int 1 - int 1) = [] from rfl,
    List.forIn_nil, hsub]
  by_cases hsame : (ks1 - ks0 == int 0) = true
  all_goals
    simp only [copyPairSourceMask, hsame, Bool.false_eq_true, ite_true, ite_false] at hg0 hg1 ⊢
    by_cases htail : ks1 ≥ ks0 + int 1
    all_goals
      simp only [htail, ite_true, ite_false] at hg1 ⊢
      simp only [shape_run_bind, hg0, hr0, hw0, hg1, hr1, copyPairCarry, hw1, shape_run_pure]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A small three-chunk vector isolates the installed interior-copy discrepancy. -/
def rangeEmptyDiagnosticBits : List Bool := List.replicate 64 false ++ [true] ++ List.replicate 64 false

/-- Only the low bit of the middle chunk is set in the diagnostic input. -/
theorem rangeEmptyDiagnosticEncoding :
    encodeBits rangeEmptyDiagnosticBits = [u64 0, u64 1, u64 0] := by decide
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

/-- Aligning the final packed word already obtains the zero-padded logical suffix. -/
theorem shiftWindowTailSlice (xs : List Bool) (chunk offset : Nat)
    (ho : offset < 64) (hn : xs.length ≤ (chunk + 1) * 64) :
    lshr_int (and_int (packedPrefix xs chunk 64) (shl_int u64Max (int offset))) (int offset) =
      copyPairSlice xs (chunk * 64 + offset) := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairRightBit _ offset bit (by omega) hb, copyPairSliceBit xs _ bit hb]
  by_cases hi : bit + offset < 64
  · rw [if_pos hi, dequePackedAnd, rangeSingleHighMaskBit offset (bit + offset) (by omega) hi,
      packedWord_bit xs chunk (bit + offset) hi]
    simp only [show offset ≤ bit + offset by omega, decide_true, Bool.and_true]
    congr 1
    omega
  · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- The first two available source chunks suffice for a glued logical window regardless of the final endpoint. -/
theorem shiftWindowGluePairRun (chunks chunk last offset : Nat) (low high : U64) (s : State)
    (hk : last + 1 ≤ 9223372036854775807) (hl : chunk < last) (ho : offset < 64)
    (h0 : (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok low, s))
    (h1 : (mutableGet chunks (int ((chunk + 2 : Nat) : Int))).run s = (.ok high, s)) :
    (glueSrcBitChunks chunks (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
      (shl_int u64Max (int offset)) (int offset)).run s = (.ok (copyPairGlue low high offset), s) := by
  have hgt : int ((last + 1 : Nat) : Int) > int ((chunk + 1 : Nat) : Int) := by
    change (int ((chunk + 1 : Nat) : Int)).val < (int ((last + 1 : Nat) : Int)).val
    rw [packedInt_val (chunk + 1) (by omega), packedInt_val (last + 1) hk]
    omega
  have hplus : int ((chunk + 1 : Nat) : Int) + int 1 = int ((chunk + 2 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hshift : int 64 - int offset = int ((64 - offset : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  by_cases hp : 0 < offset
  · have hoff : int offset > int 0 := by
      change 0 < (int offset).val
      rw [packedInt_val offset (by omega)]
      omega
    simp only [glueSrcBitChunks, shape_run_bind, h0, hgt, hoff, and_self, ite_true,
      hplus, h1, hshift, shape_run_pure, copyPairGlue]
  · have hz : offset = 0 := by omega
    subst offset
    have hzero : lshr_int (and_int low (shl_int u64Max (int (0 : Nat)))) (int (0 : Nat)) = low := by
      apply packedBit_ext
      intro bit hb
      rw [copyPairRightBit _ 0 bit (by decide) hb, if_pos (by omega), dequePackedAnd,
        rangeSingleHighMaskBit 0 (bit + 0) (by decide) (by omega)]
      simp only [Nat.zero_le, decide_true, Bool.and_true, Nat.add_zero]
    simp only [glueSrcBitChunks, shape_run_bind, h0,
      show ¬ int (0 : Nat) > int 0 from by decide, and_false, ite_false,
      shape_run_pure, hzero, copyPairGlueZero]

/-- A high-mask source gather returns the next logical window at any supported packed address. -/
theorem shiftWindowHighGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hr : ∀ chunk, chunk < wordCount xs.length →
      (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s)) :
    (glueSrcBitChunks chunks (int ((source / 64 + 1 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
      (shl_int u64Max (int ((source % 64 : Nat) : Int))) (int ((source % 64 : Nat) : Int))).run s =
      (.ok (copyPairSlice xs source), s) := by
  let chunk := source / 64
  let last := (xs.length - 1) / 64
  let offset := source % 64
  have hoff : offset < 64 := Nat.mod_lt _ (by decide)
  have hsource : source = chunk * 64 + offset := by dsimp only [chunk, offset]; omega
  have hcount : wordCount xs.length = last + 1 := by unfold wordCount; dsimp only [last]; omega
  have horder : chunk ≤ last := by dsimp only [chunk, last]; omega
  change (glueSrcBitChunks chunks (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
    (shl_int u64Max (int offset)) (int offset)).run s = _
  by_cases he : last = chunk
  · rw [he]
    have h := shiftNearGlueLastRun chunks (int ((chunk + 1 : Nat) : Int)) (int offset)
      (shl_int u64Max (int offset)) (packedPrefix xs chunk 64) s (hr chunk (by rw [hcount, he]; omega))
    rw [shiftWindowTailSlice xs chunk offset hoff (by dsimp only [last] at he; omega), ← hsource] at h
    exact h
  · have h := shiftWindowGluePairRun chunks chunk last offset (packedPrefix xs chunk 64)
      (packedPrefix xs (chunk + 1) 64) s (by dsimp only [last]; omega) (by omega) hoff
      (hr chunk (by rw [hcount]; omega)) (by
        have h' := hr (chunk + 1) (by rw [hcount]; omega)
        simpa only [show chunk + 1 + 1 = chunk + 2 by omega] using h')
    rw [shiftNearGlueSlice xs chunk offset hoff, ← hsource] at h
    exact h

/-- A source interval longer than one word selects the unbounded high mask. -/
theorem shiftWindowSourceMask (xs : List Bool) (source : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hp : 64 < xs.length - source) :
    copyPairSourceMask (int ((source / 64 + 1 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
      (int ((source % 64 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int)) =
      shl_int u64Max (int ((source % 64 : Nat) : Int)) := by
  have hd : source / 64 < (xs.length - 1) / 64 := by omega
  have hdelta : int (((xs.length - 1) / 64 + 1 : Nat) : Int) - int ((source / 64 + 1 : Nat) : Int) =
      int ((((xs.length - 1) / 64 - source / 64 : Nat)) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  rw [copyPairSourceMask, hdelta,
    fillPositiveLength ((xs.length - 1) / 64 - source / 64) (by omega) (by omega)]
  rfl

/-- A high-mask source gather returns the next logical window at any supported packed address. -/
theorem prefixDeleteHighGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hr : ∀ chunk, source / 64 ≤ chunk → chunk < wordCount xs.length →
      (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s)) :
    (glueSrcBitChunks chunks (int ((source / 64 + 1 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
      (shl_int u64Max (int ((source % 64 : Nat) : Int))) (int ((source % 64 : Nat) : Int))).run s =
      (.ok (copyPairSlice xs source), s) := by
  let chunk := source / 64
  let last := (xs.length - 1) / 64
  let offset := source % 64
  have hoff : offset < 64 := Nat.mod_lt _ (by decide)
  have hsource : source = chunk * 64 + offset := by dsimp only [chunk, offset]; omega
  have hcount : wordCount xs.length = last + 1 := by unfold wordCount; dsimp only [last]; omega
  have horder : chunk ≤ last := by dsimp only [chunk, last]; omega
  change (glueSrcBitChunks chunks (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
    (shl_int u64Max (int offset)) (int offset)).run s = _
  by_cases he : last = chunk
  · rw [he]
    have h := shiftNearGlueLastRun chunks (int ((chunk + 1 : Nat) : Int)) (int offset)
      (shl_int u64Max (int offset)) (packedPrefix xs chunk 64) s (hr chunk (by exact Nat.le_refl _) (by rw [hcount, he]; omega))
    rw [shiftWindowTailSlice xs chunk offset hoff (by dsimp only [last] at he; omega), ← hsource] at h
    exact h
  · have h := shiftWindowGluePairRun chunks chunk last offset (packedPrefix xs chunk 64)
      (packedPrefix xs (chunk + 1) 64) s (by dsimp only [last]; omega) (by omega) hoff
      (hr chunk (by exact Nat.le_refl _) (by rw [hcount]; omega)) (by
        have h' := hr (chunk + 1) (by dsimp only [chunk]; omega) (by rw [hcount]; omega)
        simpa only [show chunk + 1 + 1 = chunk + 2 by omega] using h')
    rw [shiftNearGlueSlice xs chunk offset hoff, ← hsource] at h
    exact h

/-- The unchanged-size word list after moving a short logical suffix to the front. -/
def prefixDeleteWords (xs : List Bool) (count : Nat) : List U64 :=
  if xs.length - count ≤ 64 then
    (encodeBits xs).set 0 (copyPairPaste (packedPrefix xs 0 64) (copyPairSlice xs count) 0 (xs.length - count))
  else ((encodeBits xs).set 0 (copyPairSlice xs count)).set 1
    (copyPairPaste (packedPrefix xs 1 64) (copyPairSlice xs (count + 64)) 0 (xs.length - count - 64))
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Logical storage after an interior suffix copy, before trimming the retained old tail. -/
def rangeBoundaryBits (xs : List Bool) (first last : Nat) : List Bool :=
  (xs.take first ++ xs.drop last) ++ xs.drop (first + (xs.length - last))
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

/-- Every native remaining count chooses its next descending block by the natural minimum with64. -/
theorem frontCopyRegistersNative (posD posS : I64) (count : Nat)
    (hn : count ≤ 9223372036854775807) :
    frontCopyRegisters posD posS (int count) =
      (int count, int ((min count 64 : Nat) : Int), int ((count - min count 64 : Nat) : Int),
        posS + int ((count - min count 64 : Nat) : Int),
        posD + int ((count - min count 64 : Nat) : Int)) := by
  have hs : (if int count < int 64 then int count else int 64) = int ((min count 64 : Nat) : Int) := by
    by_cases h : count < 64
    · have ht : int count < int 64 := by
        change (int count).val < 64
        rw [packedInt_val count hn]
        omega
      rw [if_pos ht, Nat.min_eq_left (by omega)]
    · have ht : ¬ int count < int 64 := by
        change ¬ (int count).val < 64
        rw [packedInt_val count hn]
        omega
      rw [if_neg ht, Nat.min_eq_right (by omega)]
      rfl
  have hd : int count - int ((min count 64 : Nat) : Int) = int ((count - min count 64 : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    have hm := Nat.min_le_left count 64
    omega
  simp only [frontCopyRegisters, hs, hd]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The canonical partial last word is unchanged by clipping to its nonzero logical remainder. -/
theorem frontLastPackedClip (xs : List Bool) (hr : xs.length % 64 ≠ 0) :
    resizeFrontPairClip (packedPrefix xs ((xs.length - 1) / 64) 64) (xs.length % 64) =
      packedPrefix xs ((xs.length - 1) / 64) 64 := by
  have hm : xs.length % 64 < 64 := Nat.mod_lt xs.length (by decide)
  have hd : (xs.length - 1) / 64 * 64 + xs.length % 64 = xs.length := by omega
  apply packedBit_ext
  intro bit hb
  rw [resizeFrontPairClipBit _ _ bit (by omega) hb]
  by_cases hi : bit < xs.length % 64
  · rw [if_pos hi]
  · rw [if_neg hi, packedWord_bit xs ((xs.length - 1) / 64) bit hb,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096

open JuliaLean.Proofs.base.int

/-- A general initialized chunk vector supports every in-bounds one-based read without state changes. -/
theorem cmp_read_initialized (s : State) (handle memory : Nat) (words : List U64)
    (hsize : words.length ≤ 9223372036854775807)
    (hvector : (mutableVector handle).run s = (.ok ⟨(memory, one), int words.length⟩, s))
    (hmemory : (memoryRead memory).run s = (.ok (words.map some ++ List.replicate 32 none), s))
    (j : Nat) (hj : j < words.length) :
    (mutableGet handle (int ((j + 1 : Nat) : Int))).run s = (.ok words[j], s) := by
  have hi := packedObserve_intVal (j + 1) (by omega)
  have hs := packedObserve_intVal words.length hsize
  have hb : 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      int ((j + 1 : Nat) : Int) ≤ int (words.length : Int) := by
    change 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      (int ((j + 1 : Nat) : Int)).val ≤ (int (words.length : Int)).val
    rw [hi, hs]
    omega
  have hidx : (one.val + (int ((j + 1 : Nat) : Int)).val - 2).toNat = j := by
    rw [hi]
    change (1 + ((j + 1 : Nat) : Int) - 2).toNat = j
    omega
  have hget : (words.map some ++ List.replicate 32 none)[j]? = some (some words[j]) := by
    rw [List.getElem?_append_left (by simpa only [List.length_map] using hj)]
    rw [List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl
  simp only [mutableGet, shape_run_bind, hvector, hb.1, hb.2, and_self,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hmemory, hidx, hget, shape_run_pure]

/-- The exact two-vector initial memory used by the frozen public comparison target. -/
def cmpInitialState (left right : List U64) : State :=
  MutableMemory.initialMany [left.map some, right.map some]

/-- Both initial vector headers expose their full initialized chunk lengths. -/
theorem cmp_initial_headers (left right : List U64) :
    (mutableVector 0).run (cmpInitialState left right) =
      (.ok ⟨(0, one), int left.length⟩, cmpInitialState left right) ∧
    (mutableVector 1).run (cmpInitialState left right) =
      (.ok ⟨(1, one), int right.length⟩, cmpInitialState left right) := by
  constructor
  · change ((Except.ok ⟨(0, one), int (left.map some).length⟩ : Except Error MutableVector),
      cmpInitialState left right) = _
    rw [List.length_map]
  · change ((Except.ok ⟨(1, one), int (right.map some).length⟩ : Except Error MutableVector),
      cmpInitialState left right) = _
    rw [List.length_map]

/-- Both initial chunk arrays report their logical storage length. -/
theorem cmp_initial_lengths (left right : List U64) :
    (mutableLength 0).run (cmpInitialState left right) =
      (.ok (int left.length), cmpInitialState left right) ∧
    (mutableLength 1).run (cmpInitialState left right) =
      (.ok (int right.length), cmpInitialState left right) := by
  obtain ⟨hl, hr⟩ := cmp_initial_headers left right
  constructor <;> simp only [mutableLength, shape_run_bind, hl, hr, shape_run_pure]

/-- Every in-bounds left chunk read returns the original word. -/
theorem cmp_initial_read_left (left right : List U64) (hn : left.length ≤ 9223372036854775807)
    (j : Nat) (hj : j < left.length) :
    (mutableGet 0 (int ((j + 1 : Nat) : Int))).run (cmpInitialState left right) =
      (.ok left[j], cmpInitialState left right) :=
  cmp_read_initialized _ 0 0 left hn (cmp_initial_headers left right).1 rfl j hj

/-- Every in-bounds right chunk read returns the original word. -/
theorem cmp_initial_read_right (left right : List U64) (hn : right.length ≤ 9223372036854775807)
    (j : Nat) (hj : j < right.length) :
    (mutableGet 1 (int ((j + 1 : Nat) : Int))).run (cmpInitialState left right) =
      (.ok right[j], cmpInitialState left right) :=
  cmp_read_initialized _ 1 1 right hn (cmp_initial_headers left right).2 rfl j hj
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Allocating an empty word vector appends fresh memory and a fresh array header. -/
theorem metadataAllocateZero (s : State) :
    (allocateChunkVectorModel 0).run s =
      (.ok s.arrays.length,
        ⟨s.memories ++ [[]], s.arrays ++ [⟨(s.memories.length, one), int 0⟩]⟩) := by
  rfl
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem metadataMemoryWrite (s : State) (slots : List (Option U64))
    (hm : s.memories[0]? = some slots) (j : I64) (word : U64)
    (hj : 1 ≤ j.val ∧ j.val ≤ (slots.length : Int)) :
    (memoryWrite 0 j (some word)).run s =
      (.ok (), {s with memories := s.memories.set 0 (slots.set (j.val - 1).toNat (some word))}) := by
  simp only [memoryWrite, memoryRead, shape_run_bind, shape_run_get, hm,
    shape_run_pure, hj, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_run_modify]

theorem metadataSetRaw (s : State) (slots : List (Option U64)) (n j : I64) (word : U64)
    (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots)
    (hn : n.val ≤ (slots.length : Int))
    (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    (mutableSet 0 word j).run s =
      (.ok (), { s with memories := s.memories.set 0 (slots.set (j.val - 1).toNat (some word)) }) := by
  have hin : one ≤ j ∧ j ≤ n := hj
  have hw := metadataMemoryWrite s slots hm j word (by omega)
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hin, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_one_add_sub_one, hw]
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Subtraction of wrapped signed integers commutes with wrapping. -/
theorem concat_int_sub (a b : Int) : int a - int b = int (a - b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a - wrapInt .i64 b) = wrapInt .i64 (a - b)
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true]
  omega

/-- Every position in the first word has the expected bit address. -/
theorem concat_small_chunks (bit : Nat) (hbit : bit < 64) :
    getChunksId (int ((bit + 1 : Nat) : Int)) = (int 1, int bit) := by
  have h : ∀ bit : Fin 64,
      getChunksId (int ((bit.val + 1 : Nat) : Int)) = (int 1, int bit.val) := by decide
  exact h ⟨bit, hbit⟩

/-- Nonnegative shifts up to one word have their usual unsigned count. -/
theorem concat_shift_count (n : Nat) (hn : n ≤ 64) :
    (fromJInt (int n)).toNat = n := by
  rw [fromJInt, BitVec.toNat_ofInt, packedInt_val n (by omega)]
  change ((n : Int) % 18446744073709551616).toNat = n
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

/-- Packed bit semantics of conjunction. -/
theorem concat_and_bit (a b : U64) (bit : Nat) :
    packedBit (and_int a b) bit = (packedBit a bit && packedBit b bit) := by
  simp only [and_int, jlAndInt, packedBit_toJInt, BitVec.getLsbD_and, packedBit_fromJInt]

/-- Packed bit semantics of complementation within a word. -/
theorem concat_not_bit (a : U64) (bit : Nat) (hbit : bit < 64) :
    packedBit (not_int a) bit = !(packedBit a bit) := by
  unfold not_int
  rw [packedBit_toJInt]
  simp only [jlNotInt, BitVec.getLsbD_not, packedBit_fromJInt]
  change (decide (bit < 64) && !packedBit a bit) = !packedBit a bit
  simp only [hbit, decide_true, Bool.true_and]

/-- Every left-shift count up to and including the full width zero-fills vacated positions. -/
theorem concat_shl_bit (word : U64) (n bit : Nat) (hn : n ≤ 64) (hbit : bit < 64) :
    packedBit (shl_int word (int n)) bit =
      if n ≤ bit then packedBit word (bit - n) else false := by
  unfold shl_int
  rw [packedBit_toJInt]
  unfold jlShlInt
  rw [concat_shift_count n hn]
  by_cases hs : n < 64
  · rw [if_neg (show ¬ n ≥ IntTy.u64.bits by change ¬ n ≥ 64; omega), BitVec.getLsbD_ofNat,
      packedFromJInt_nat, Nat.testBit_mul_two_pow]
    change (decide (bit < 64) && (decide (n ≤ bit) && packedBit word (bit - n))) = _
    simp only [hbit, decide_true, Bool.true_and]
    by_cases hi : n ≤ bit <;> simp only [hi, decide_true, decide_false, Bool.true_and,
      Bool.false_and, ite_true, ite_false]
  · rw [if_pos (show n ≥ IntTy.u64.bits by change n ≥ 64; omega)]
    have hb : ¬ n ≤ bit := by omega
    simp only [BitVec.getLsbD_ofNat, Nat.zero_testBit, Bool.and_false, hb, ite_false]

/-- The shifted all-ones word is exactly a high-bit mask, including endpoint 64. -/
theorem concat_high_mask_bit (n bit : Nat) (hn : n ≤ 64) (hbit : bit < 64) :
    packedBit (shl_int u64Max (int n)) bit = decide (n ≤ bit) := by
  rw [concat_shl_bit _ _ _ hn hbit]
  by_cases h : n ≤ bit
  · simp only [h, ite_true, decide_true, packedBit_max, show bit - n < 64 by omega]
  · simp only [h, ite_false, decide_false]

/-- The exact mask used to retain bits outside a one-word destination interval. -/
def concat_keep_mask (offset count : Nat) : U64 :=
  or_int (not_int (shl_int u64Max (int offset)))
    (shl_int u64Max (int ((offset + count : Nat) : Int)))

/-- The installed one-word copy preserves destination bits outside the requested interval. -/
def concat_copy_word (dest source : U64) (offset count : Nat) : U64 :=
  let keep := concat_keep_mask offset count
  let sourceMask := not_int (shl_int u64Max (int count))
  or_int (and_int dest keep)
    (and_int (shl_int (and_int source sourceMask) (int offset)) (not_int keep))

/-- The destination preserve mask is false precisely on the copied interval. -/
theorem concat_keep_mask_bit (offset count bit : Nat) (hbound : offset + count ≤ 64)
    (hbit : bit < 64) :
    packedBit (concat_keep_mask offset count) bit =
      decide (bit < offset ∨ offset + count ≤ bit) := by
  rw [concat_keep_mask, packedBit_or, concat_not_bit _ _ hbit,
    concat_high_mask_bit _ _ (by omega) hbit, concat_high_mask_bit _ _ hbound hbit]
  by_cases hl : offset ≤ bit
  · have hlt : ¬ bit < offset := by omega
    by_cases hr : offset + count ≤ bit <;> simp only [hl, hlt, hr, decide_true, decide_false,
      Bool.not_true, Bool.false_or, false_or]
  · have hlt : bit < offset := by omega
    by_cases hr : offset + count ≤ bit <;> simp only [hl, hlt, hr, decide_true, decide_false,
      Bool.not_false, Bool.true_or, true_or]


/-- One-word copying selects the source interval and retains every destination bit outside it. -/
theorem concat_copy_word_bit (dest source : U64) (offset count bit : Nat)
    (hbound : offset + count ≤ 64) (hbit : bit < 64) :
    packedBit (concat_copy_word dest source offset count) bit =
      if offset ≤ bit ∧ bit < offset + count then packedBit source (bit - offset)
      else packedBit dest bit := by
  simp only [concat_copy_word, packedBit_or, concat_and_bit,
    concat_keep_mask_bit offset count bit hbound hbit,
    concat_not_bit _ bit hbit]
  rw [concat_shl_bit _ _ _ (by omega) hbit]
  by_cases hl : offset ≤ bit
  · simp only [hl, ite_true, concat_and_bit, concat_not_bit _ _ (by omega : bit - offset < 64),
      concat_high_mask_bit _ _ (by omega : count ≤ 64) (by omega : bit - offset < 64)]
    by_cases hr : bit < offset + count
    · have hout : ¬ (bit < offset ∨ offset + count ≤ bit) := by omega
      have hs : ¬ count ≤ bit - offset := by omega
      simp only [hout, hs, decide_false, Bool.not_false, Bool.and_true, Bool.and_false,
        Bool.false_or, hl, hr, and_self, ite_true]
    · have hout : bit < offset ∨ offset + count ≤ bit := by omega
      simp only [hout, decide_true, Bool.not_true, Bool.and_false, Bool.or_false,
        Bool.and_true, hr, and_false, ite_false]
  · have hout : bit < offset ∨ offset + count ≤ bit := by omega
    simp only [hout, hl, decide_true, Bool.not_true, Bool.and_true, Bool.and_false,
      Bool.false_and, Bool.or_false, ite_false, false_and]

/-- Copying a second sequence after the first in one word constructs their exact packed append. -/
theorem concat_copy_word_append (left right : List Bool)
    (hbound : left.length + right.length ≤ 64) :
    concat_copy_word (packedPrefix left 0 64) (packedPrefix right 0 64)
      left.length right.length = packedPrefix (left ++ right) 0 64 := by
  apply packedBit_ext
  intro bit hbit
  rw [concat_copy_word_bit _ _ _ _ _ hbound hbit,
    packedWord_bit (left ++ right) 0 bit hbit]
  simp only [Nat.zero_mul, Nat.zero_add]
  by_cases hl : bit < left.length
  · have hn : ¬ (left.length ≤ bit ∧ bit < left.length + right.length) := by omega
    rw [if_neg hn, packedWord_bit _ _ _ hbit]
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
  · have hle : left.length ≤ bit := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
    by_cases hr : bit < left.length + right.length
    · rw [if_pos ⟨hle, hr⟩, packedWord_bit _ _ _ (by omega : bit - left.length < 64)]
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD]
    · rw [if_neg (by omega), packedWord_bit _ _ _ hbit]
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega : left.length ≤ bit),
        List.getElem?_eq_none (by omega : right.length ≤ bit - left.length)]

/-- A zero left shift preserves each packed word. -/
theorem concat_shl_zero (word : U64) : shl_int word (int 0) = word := by
  apply packedBit_ext
  intro bit hbit
  have h := concat_shl_bit word 0 bit (by omega) hbit
  simpa only [Int.ofNat_zero, Nat.zero_le, ite_true, Nat.sub_zero] using h

/-- A zero logical right shift preserves each packed word. -/
theorem concat_lshr_zero (word : U64) : lshr_int word (int 0) = word := by
  apply packedBit_ext
  intro bit hbit
  unfold lshr_int
  rw [packedBit_toJInt]
  unfold jlLshrInt
  rw [show (fromJInt (int 0)).toNat = 0 from rfl,
    if_neg (show ¬ 0 ≥ IntTy.u64.bits by decide)]
  rw [BitVec.getLsbD_ofNat, packedFromJInt_nat, Nat.testBit_div_two_pow]
  change (decide (bit < 64) && packedBit word (bit + 0)) = packedBit word bit
  simp only [hbit, decide_true, Bool.true_and, Nat.add_zero]

/-- Intersecting an arbitrary word with the full mask preserves it. -/
theorem concat_and_max_left (word : U64) : and_int u64Max word = word := by
  apply packedBit_ext
  intro bit hbit
  rw [concat_and_bit, packedBit_max]
  simp only [hbit, decide_true, Bool.true_and]

/-- An empty installed chunk-copy request is a no-op in every heap. -/
theorem concat_copy_zero (dest src : Nat) (posD posS : I64) (s : State) :
    (copyChunks dest posD src posS (int 0)).run s = (.ok (), s) := by
  simp only [copyChunks, show (int 0 == int 0) = true from rfl, ite_true, shape_run_pure]

/-- The installed copy operation executes the exact one-word copy formula whenever its reads and write are valid. -/
theorem concat_copy_single_run (dest src offset count : Nat) (s s' : State)
    (destination source : U64) (hsep : dest ≠ src) (hpos : 0 < count)
    (hbound : offset + count ≤ 64)
    (hsource : (mutableGet src (int 1)).run s = (.ok source, s))
    (hdestination : (mutableGet dest (int 1)).run s = (.ok destination, s))
    (hwrite : (mutableSet dest (concat_copy_word destination source offset count) (int 1)).run s =
      (.ok (), s')) :
    (copyChunks dest (int ((offset + 1 : Nat) : Int)) src (int 1) (int count)).run s =
      (.ok (), s') := by
  have hzero : (int count == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val count (by omega)] at hv
    change (count : Int) = 0 at hv
    omega
  have hforward : ¬ (dest = src ∧ int ((offset + 1 : Nat) : Int) > int 1) :=
    fun h => hsep h.1
  have hstart := concat_small_chunks offset (by omega)
  have hendD : int ((offset + 1 : Nat) : Int) + int count - int 1 =
      int ((offset + count : Nat) : Int) := by
    rw [packedInt_add, concat_int_sub]
    apply congrArg int
    omega
  have hendS : int 1 + int count - int 1 = int count := by
    rw [packedInt_add, concat_int_sub]
    apply congrArg int
    omega
  have hlastD : getChunksId (int ((offset + count : Nat) : Int)) =
      (int 1, int ((offset + count - 1 : Nat) : Int)) := by
    have h := concat_small_chunks (offset + count - 1) (by omega)
    rw [show offset + count - 1 + 1 = offset + count by omega] at h
    exact h
  have hlastS : getChunksId (int count) = (int 1, int ((count - 1 : Nat) : Int)) := by
    have h := concat_small_chunks (count - 1) (by omega)
    rw [show count - 1 + 1 = count by omega] at h
    exact h
  have hincD : int ((offset + count - 1 : Nat) : Int) + int 1 =
      int ((offset + count : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hincS : int ((count - 1 : Nat) : Int) + int 1 = int count := by
    rw [packedInt_add]
    apply congrArg int
    omega
  simp only [copyChunks, hzero, Bool.false_eq_true, ite_false, hforward, dite_false,
    hendD, hendS, hstart, hlastD, hlastS,
    show getChunksId (int 1) = (int 1, int 0) from rfl,
    show (int 1 - int 1 == int 0) = true from rfl, ite_true, hincD, hincS,
    concat_shl_zero, concat_and_max_left,
    glueSrcBitChunks, shape_run_bind, hsource, concat_lshr_zero,
    show ¬ (int 1 > int 1 ∧ int 0 > int 0) from by decide,
    hdestination, shape_run_pure]
  simp only [concat_copy_word, concat_keep_mask] at hwrite
  rw [hwrite]

/-- The installed one-word copy appends logical sequences whenever the heap supplies their packed words. -/
theorem concat_copy_single_append (dest src : Nat) (left right : List Bool) (s s' : State)
    (hsep : dest ≠ src) (hpos : 0 < right.length) (hbound : left.length + right.length ≤ 64)
    (hsource : (mutableGet src (int 1)).run s = (.ok (packedPrefix right 0 64), s))
    (hdestination : (mutableGet dest (int 1)).run s = (.ok (packedPrefix left 0 64), s))
    (hwrite : (mutableSet dest (packedPrefix (left ++ right) 0 64) (int 1)).run s = (.ok (), s')) :
    (copyChunks dest (int ((left.length + 1 : Nat) : Int)) src (int 1) (int right.length)).run s =
      (.ok (), s') := by
  apply concat_copy_single_run dest src left.length right.length s s'
    (packedPrefix left 0 64) (packedPrefix right 0 64) hsep hpos hbound hsource hdestination
  rw [concat_copy_word_append left right hbound]
  exact hwrite

/-- A known initialized first slot can be read through any valid one-based header. -/
theorem concat_read_first (s : State) (handle mem : Nat) (n : I64) (word : U64)
    (tail : List (Option U64))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some (some word :: tail)) (hn : 1 ≤ n.val) :
    (mutableGet handle (int 1)).run s = (.ok word, s) := by
  have hb : 1 ≤ (int 1).val ∧ int 1 ≤ n := ⟨by decide, hn⟩
  simp only [mutableGet, mutableVector, memoryRead, shape_run_bind, shape_run_get,
    ha, hm, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

/-- A known writable first slot is replaced without modifying its vector header. -/
theorem concat_store_first (s : State) (handle mem : Nat) (n : I64)
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
def concat_extend (s : State) (word : U64) : State :=
  ⟨s.memories ++ [[some word]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩

/-- The new destination header points to the newly appended one-word memory. -/
theorem concat_extend_header (s : State) (word : U64) :
    (concat_extend s word).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), int 1⟩ := by
  simp only [concat_extend, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

/-- The new destination memory has exactly its one initialized word. -/
theorem concat_extend_memory (s : State) (word : U64) :
    (concat_extend s word).memories[s.memories.length]? = some [some word] := by
  simp only [concat_extend, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

/-- Reading the appended destination returns its current packed word. -/
theorem concat_extend_read (s : State) (word : U64) :
    (mutableGet s.arrays.length (int 1)).run (concat_extend s word) =
      (.ok word, concat_extend s word) :=
  concat_read_first _ _ _ _ _ [] (concat_extend_header s word) (concat_extend_memory s word) (by decide)

/-- Replacing the destination word retains the entire preexisting heap. -/
theorem concat_extend_store (s : State) (old word : U64) :
    (mutableSet s.arrays.length word (int 1)).run (concat_extend s old) =
      (.ok (), concat_extend s word) := by
  rw [concat_store_first _ _ _ _ _ [] word (concat_extend_header s old)
    (concat_extend_memory s old) (by decide)]
  simp only [concat_extend, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

/-- Appending a destination preserves every initialized source first word. -/
theorem concat_extend_source (s : State) (destination source : U64) (handle mem : Nat)
    (n : I64) (tail : List (Option U64)) (hh : handle < s.arrays.length) (hm : mem < s.memories.length)
    (hheader : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hmemory : s.memories[mem]? = some (some source :: tail)) (hn : 1 ≤ n.val) :
    (mutableGet handle (int 1)).run (concat_extend s destination) =
      (.ok source, concat_extend s destination) := by
  apply concat_read_first _ handle mem n source tail _ _ hn
  · simpa only [concat_extend, List.getElem?_append_left hh] using hheader
  · simpa only [concat_extend, List.getElem?_append_left hm] using hmemory

/-- Allocating one fresh chunk appends one unassigned slot and its one-based header. -/
theorem concat_allocate_chunk (s : State) :
    (allocateChunkVectorModel 1).run s =
      (.ok s.arrays.length,
        ⟨s.memories ++ [[none]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩) := by
  rfl

/-- Checked multiplication by one preserves every one-word logical length. -/
theorem concat_checked_one (count : Nat) (hcount : count ≤ 64) :
    JuliaLean.base.checked.checkedMulBits (int 1) (int count) = .ok (int count) := by
  have h : ∀ count : Fin 65,
      JuliaLean.base.checked.checkedMulBits (int 1) (int count.val) = .ok (int count.val) := by decide
  exact h ⟨count, by omega⟩

/-- Checked singleton dimensions compute the single requested length unchanged. -/
theorem concat_checked_dims (count : Nat) (hcount : count ≤ 64) (s : State) :
    (checkedDimensionsModel [int count]).run s = (.ok (int count), s) := by
  simp only [checkedDimensionsModel, List.forIn_cons, List.forIn_nil, checkedMultiplyMutation,
    concat_checked_one count hcount, shape_run_bind, shape_run_pure]

/-- Every positive length at most 64 uses exactly one storage chunk. -/
theorem concat_num_chunks (count : Nat) (hpos : 0 < count) (hcount : count ≤ 64) :
    numBitChunks (int count) = int 1 := by
  have h : ∀ count : Fin 64,
      numBitChunks (int ((count.val + 1 : Nat) : Int)) = int 1 := by decide
  have h' := h ⟨count - 1, by omega⟩
  simpa only [show count - 1 + 1 = count by omega] using h'

/-- Single-word constructor execution separates validation, allocation, and initialization. -/
theorem concat_construct_single {N : Nat}
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
theorem concat_allocate_single (count : Nat) (hpos : 0 < count) (hcount : count ≤ 64) (s : State) :
    (Round5.Round2.allocateBitArrayModel (N := 1) [int count]).run s =
      (.ok (⟨s.arrays.length, int count, [int count]⟩ : BitVector), concat_extend s (u64 0)) := by
  have hneg : ¬ (int count).val < 0 := by rw [packedInt_val count (by omega)]; omega
  have ha : (s.arrays ++ [⟨(s.memories.length, one), int 1⟩])[s.arrays.length]? =
      some (⟨(s.memories.length, one), int 1⟩ : MutableVector) := by
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hm : (s.memories ++ [[none]])[s.memories.length]? = some [none] := by
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hwrite := concat_store_first
    (⟨s.memories ++ [[none]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩ : State)
    s.arrays.length s.memories.length (int 1) none [] (u64 0) ha hm (by decide)
  simp only [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero] at hwrite
  exact concat_construct_single checkedDimensionsModel allocateChunkVectorModel (int count) s _ _
    s.arrays.length hneg (concat_checked_dims count hcount s) (concat_num_chunks count hpos hcount)
    (concat_allocate_chunk s) hwrite


/-- Header attached to one logical input and its existing heap handle. -/
def concat_vector (entry : List Bool × Nat) : BitVector :=
  ⟨entry.2, int entry.1.length, [int entry.1.length]⟩

/-- Each input header records the source logical length. -/
theorem concat_vector_len (entry : List Bool × Nat) :
    (concat_vector entry).len = int entry.1.length := rfl

/-- A source remains readable while the independent one-word destination changes. -/
def concat_ready (s : State) (entry : List Bool × Nat) : Prop :=
  entry.2 < s.arrays.length ∧
  (0 < entry.1.length → ∀ destination : U64,
    (mutableGet entry.2 (int 1)).run (concat_extend s destination) =
      (.ok (packedPrefix entry.1 0 64), concat_extend s destination))

/-- The source length-accumulation loop sums all logical input lengths with the installed Int arithmetic. -/
theorem concat_sum_loop (entries : List (List Bool × Nat)) (start : Int) (s : State) :
    (forIn (entries.map concat_vector) (int start) (fun (v : BitVector) (n : I64) =>
      (pure (ForInStep.yield (n + v.len)) : BitMutationM (ForInStep I64)))).run s =
      (.ok (int (start + ((entries.flatMap Prod.fst).length : Int))), s) := by
  induction entries generalizing start with
  | nil => simp only [List.map_nil, List.forIn_nil, List.flatMap_nil, List.length_nil,
      Int.ofNat_zero, Int.add_zero, shape_run_pure]
  | cons entry entries ih =>
    simp only [List.map_cons, List.forIn_cons, shape_run_bind, shape_run_pure, concat_vector_len]
    rw [packedInt_add, ih]
    simp only [List.flatMap_cons, List.length_append]
    apply congrArg (fun n : Int => (Except.ok (int n), s))
    omega

/-- Abstract iteration composes exact append steps without reducing their source implementations. -/
theorem concat_loop_from_steps (entries : List (List Bool × Nat)) (accum : List Bool)
    (state : List Bool → State) (step : BitVector → I64 → BitMutationM (ForInStep I64))
    (hstep : ∀ entry ∈ entries, ∀ prior : List Bool, prior.length + entry.1.length ≤ 64 →
      (step (concat_vector entry) (int ((prior.length + 1 : Nat) : Int))).run (state prior) =
        (.ok (ForInStep.yield (int (((prior ++ entry.1).length + 1 : Nat) : Int))), state (prior ++ entry.1)))
    (hbound : accum.length + (entries.flatMap Prod.fst).length ≤ 64) :
    (forIn (entries.map concat_vector) (int ((accum.length + 1 : Nat) : Int)) step).run (state accum) =
      (.ok (int (((accum ++ entries.flatMap Prod.fst).length + 1 : Nat) : Int)),
        state (accum ++ entries.flatMap Prod.fst)) := by
  induction entries generalizing accum with
  | nil => simp only [List.map_nil, List.forIn_nil, List.flatMap_nil, List.append_nil, shape_run_pure]
  | cons entry entries ih =>
    have hsum : accum.length + entry.1.length + (entries.flatMap Prod.fst).length ≤ 64 := by
      simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hbound
    have hnext := ih (accum ++ entry.1) (fun e he => hstep e (List.mem_cons_of_mem entry he))
      (by simpa only [List.length_append] using hsum)
    simp only [List.map_cons, List.forIn_cons, shape_run_bind,
      hstep entry List.mem_cons_self accum (by omega)]
    simpa only [List.flatMap_cons, List.append_assoc] using hnext

/-- A ready source appends its bits to the current one-word destination in the installed copy operation. -/
theorem concat_copy_append_ready (entry : List Bool × Nat) (accum : List Bool) (s : State)
    (hready : concat_ready s entry) (hbound : accum.length + entry.1.length ≤ 64) :
    (copyChunks s.arrays.length (int ((accum.length + 1 : Nat) : Int))
      entry.2 (int 1) (int entry.1.length)).run (concat_extend s (packedPrefix accum 0 64)) =
      (.ok (), concat_extend s (packedPrefix (accum ++ entry.1) 0 64)) := by
  by_cases hp : 0 < entry.1.length
  · apply concat_copy_single_append s.arrays.length entry.2 accum entry.1 _ _
      (by have := hready.1; omega) hp hbound
    · exact hready.2 hp _
    · exact concat_extend_read s _
    · exact concat_extend_store s _ _
  · have he : entry.1 = [] := List.length_eq_zero_iff.mp (by omega)
    rw [he, List.length_nil, List.append_nil]
    exact concat_copy_zero _ _ _ _ _

/-- A successful effect followed by a yielded loop register preserves the effect's final heap. -/
theorem concat_yield_after (action : BitMutationM Unit) (s s' : State) (value : I64)
    (ha : action.run s = (.ok (), s')) :
    ((do action; pure (ForInStep.yield value)) : BitMutationM (ForInStep I64)).run s =
      (.ok (ForInStep.yield value), s') := by
  rw [shape_run_bind, ha]
  rfl

/-- One concrete vcat copy step appends exactly one logical source to the destination word. -/
theorem concat_copy_step (entry : List Bool × Nat) (accum : List Bool) (s : State)
    (hready : concat_ready s entry) (hbound : accum.length + entry.1.length ≤ 64) :
    ((do
      copyChunks s.arrays.length (int ((accum.length + 1 : Nat) : Int))
        entry.2 (int 1) (int entry.1.length)
      pure (ForInStep.yield (int ((accum.length + 1 : Nat) : Int) + int entry.1.length))) :
      BitMutationM (ForInStep I64)).run (concat_extend s (packedPrefix accum 0 64)) =
      (.ok (ForInStep.yield (int (((accum ++ entry.1).length + 1 : Nat) : Int))),
        concat_extend s (packedPrefix (accum ++ entry.1) 0 64)) := by
  have hposition : int ((accum.length + 1 : Nat) : Int) + int entry.1.length =
      int (((accum ++ entry.1).length + 1 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    simp only [List.length_append]
    omega
  have h := concat_yield_after _ _ _
    (int ((accum.length + 1 : Nat) : Int) + int entry.1.length)
    (concat_copy_append_ready entry accum s hready hbound)
  exact h.trans (congrArg (fun value =>
    (Except.ok (ForInStep.yield value), concat_extend s (packedPrefix (accum ++ entry.1) 0 64))) hposition)

/-- The installed variadic copy loop packs all inputs after its accumulated logical sequence in one word. -/
theorem concat_copy_loop (entries : List (List Bool × Nat)) (accum : List Bool) (s : State)
    (hready : ∀ entry ∈ entries, concat_ready s entry)
    (hbound : accum.length + (entries.flatMap Prod.fst).length ≤ 64) :
    (forIn (entries.map concat_vector) (int ((accum.length + 1 : Nat) : Int))
      (fun (v : BitVector) (position : I64) => do
        copyChunks s.arrays.length position v.chunks (int 1) v.len
        pure (ForInStep.yield (position + v.len)))).run
      (concat_extend s (packedPrefix accum 0 64)) =
      (.ok (int (((accum ++ entries.flatMap Prod.fst).length + 1 : Nat) : Int)),
        concat_extend s (packedPrefix (accum ++ entries.flatMap Prod.fst) 0 64)) := by
  exact concat_loop_from_steps entries accum (fun prior => concat_extend s (packedPrefix prior 0 64))
    _ (fun entry he prior hb => concat_copy_step entry prior s (hready entry he) hb) hbound

/-- The installed vcat control flow, with its copy action exposed as a proof parameter. -/
def concat_vcat_program (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector) (allocate : I64 → BitMutationM BitVector) : BitMutationM BitVector := do
  let mut n := int 0
  for v in vectors do n := n + v.len
  let out ← allocate n
  let mut j := int 1
  for v in vectors do
    copy out.chunks j v.chunks (int 1) v.len
    j := j + v.len
  return out

/-- The proof-parameterized vcat program is definitionally the installed source operation. -/
theorem concat_vcat_factor (vectors : List BitVector) (allocate : I64 → BitMutationM BitVector) :
    bitArrayVcatVectors vectors allocate = concat_vcat_program copyChunks vectors allocate := rfl

/-- Variadic vcat separates its length pass, allocation, and copy pass. -/
theorem concat_vcat_from_runs (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector)
    (allocate : I64 → BitMutationM BitVector) (s allocated finished : State)
    (length finalPosition : I64) (out : BitVector)
    (hsum : (forIn vectors (int 0) (fun (v : BitVector) (n : I64) =>
      (pure (ForInStep.yield (n + v.len)) : BitMutationM (ForInStep I64)))).run s = (.ok length, s))
    (hallocate : (allocate length).run s = (.ok out, allocated))
    (hcopy : (forIn vectors (int 1) (fun (v : BitVector) (position : I64) => do
      copy out.chunks position v.chunks (int 1) v.len
      pure (ForInStep.yield (position + v.len)))).run allocated = (.ok finalPosition, finished)) :
    (concat_vcat_program copy vectors allocate).run s = (.ok out, finished) := by
  simp only [concat_vcat_program, shape_run_bind, hsum, hallocate, hcopy, shape_run_pure]

/-- The frozen vector allocator with its vector result type kept explicit. -/
def concat_allocate_vector (n : I64) : BitMutationM BitVector :=
  Round5.Round2.allocateBitArrayModel [n]

/-- Every nonempty logical concatenation fitting one word executes correctly from readable independent sources. -/
theorem concat_vcat_single_ready (entries : List (List Bool × Nat)) (s : State)
    (hready : ∀ entry ∈ entries, concat_ready s entry)
    (hpos : 0 < (entries.flatMap Prod.fst).length)
    (hbound : (entries.flatMap Prod.fst).length ≤ 64) :
    (bitArrayVcatVectors (entries.map concat_vector)
      concat_allocate_vector).run s =
      (.ok (⟨s.arrays.length, int (entries.flatMap Prod.fst).length,
        [int (entries.flatMap Prod.fst).length]⟩ : BitVector),
        concat_extend s (packedPrefix (entries.flatMap Prod.fst) 0 64)) := by
  have hsum := concat_sum_loop entries 0 s
  simp only [Int.zero_add] at hsum
  have halloc := concat_allocate_single (entries.flatMap Prod.fst).length hpos hbound s
  have hcopy := concat_copy_loop entries [] s hready (by simpa only [List.length_nil, Nat.zero_add] using hbound)
  have hzero : packedPrefix [] 0 64 = u64 0 := by
    apply (packedWord_zero_iff [] 0).mpr
    intro bit _
    rfl
  simp only [List.length_nil, Nat.zero_add, List.nil_append, hzero, Int.ofNat_one] at hcopy
  rw [concat_vcat_factor]
  exact concat_vcat_from_runs copyChunks (entries.map concat_vector)
    concat_allocate_vector s _ _ _ _ _ hsum halloc hcopy

/-- Every nonempty sequence of at most one word has exactly its one packed prefix word. -/
theorem concat_encode_single (xs : List Bool) (hpos : 0 < xs.length) (hbound : xs.length ≤ 64) :
    encodeBits xs = [packedPrefix xs 0 64] := by
  rw [packedPrefix_eq_encode]
  have hcount : wordCount xs.length = 1 := by unfold wordCount; omega
  rw [hcount]
  rfl

/-- The initial source heap is exactly the heap fixed by the frozen concatenation statement. -/
def concat_initial (vectors : List (List Bool)) : State :=
  MutableMemory.initialMany (vectors.map fun xs => (encodeBits xs).map some)

/-- The frozen source heap has one vector header and one memory per input. -/
theorem concat_initial_lengths (vectors : List (List Bool)) :
    (concat_initial vectors).arrays.length = vectors.length ∧
      (concat_initial vectors).memories.length = vectors.length := by
  simp only [concat_initial, MutableMemory.initialMany, List.length_map, List.length_zipIdx,
    and_self]

/-- Every indexed input header points to its own original encoded storage. -/
theorem concat_initial_header (vectors : List (List Bool)) (entry : List Bool × Nat)
    (he : entry ∈ vectors.zipIdx) :
    (concat_initial vectors).arrays[entry.2]? =
      some ⟨(entry.2, one), int (encodeBits entry.1).length⟩ := by
  have hget := List.mem_zipIdx_iff_getElem?.mp he
  simp only [concat_initial, MutableMemory.initialMany, List.getElem?_map,
    List.getElem?_zipIdx, hget, Option.map_some, Nat.zero_add, List.length_map]
  rfl

/-- Every input memory contains its initialized encoded chunks followed by the model reserve. -/
theorem concat_initial_memory (vectors : List (List Bool)) (entry : List Bool × Nat)
    (he : entry ∈ vectors.zipIdx) :
    (concat_initial vectors).memories[entry.2]? =
      some ((encodeBits entry.1).map some ++ List.replicate 32 none) := by
  have hget := List.mem_zipIdx_iff_getElem?.mp he
  simp only [concat_initial, MutableMemory.initialMany, List.getElem?_map, hget, Option.map_some]

/-- Every source from the frozen heap remains readable after an independent one-word allocation. -/
theorem concat_initial_ready (vectors : List (List Bool)) (entry : List Bool × Nat)
    (he : entry ∈ vectors.zipIdx) (hbound : entry.1.length ≤ 64) :
    concat_ready (concat_initial vectors) entry := by
  have hi : entry.2 < vectors.length := by
    have h := List.snd_lt_of_mem_zipIdx he
    simpa only [Nat.add_zero] using h
  have hl := concat_initial_lengths vectors
  have hh := concat_initial_header vectors entry he
  have hm := concat_initial_memory vectors entry he
  constructor
  · rw [hl.1]
    exact hi
  · intro hp destination
    rw [concat_encode_single entry.1 hp hbound] at hh hm
    simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append] at hh hm
    exact concat_extend_source (concat_initial vectors) destination (packedPrefix entry.1 0 64)
      entry.2 entry.2 (int 1) (List.replicate 32 none) (by rw [hl.1]; exact hi)
      (by rw [hl.2]; exact hi) hh hm (by decide)

/-- Erasing handles from the indexed source list recovers the exact flattened input bits. -/
theorem concat_indexed_bits (vectors : List (List Bool)) :
    (vectors.zipIdx).flatMap Prod.fst = vectors.flatten := by
  rw [List.flatMap_def, List.zipIdx_map_fst]

/-- Indexing by zipIdx agrees with the frozen zip-with-range handle convention. -/
theorem concat_indexed_handles (vectors : List (List Bool)) :
    vectors.zipIdx.map concat_vector =
      (vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)) := by
  rw [List.zipIdx_eq_zip_range', ← List.range_eq_range']
  rfl

/-- A component cannot be longer than the complete flattened input. -/
theorem concat_component_length (vectors : List (List Bool)) (xs : List Bool) (hx : xs ∈ vectors) :
    xs.length ≤ vectors.flatten.length := by
  induction vectors with
  | nil => cases hx
  | cons ys vectors ih =>
    simp only [List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with he | ht
    · subst xs
      omega
    · have h := ih ht
      omega

/-- Concrete frozen variadic vector-vcat succeeds and stores the exact flattening whenever the total is 1–64 bits. -/
theorem concat_vcat_single_word (vectors : List (List Bool))
    (hpos : 0 < vectors.flatten.length) (hbound : vectors.flatten.length ≤ 64) :
    (bitArrayVcatVectors
      ((vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
      (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors) =
      (.ok (⟨vectors.length, int vectors.flatten.length, [int vectors.flatten.length]⟩ : BitVector),
        concat_extend (concat_initial vectors) (packedPrefix vectors.flatten 0 64)) := by
  have h := concat_vcat_single_ready vectors.zipIdx (concat_initial vectors)
    (fun entry he => concat_initial_ready vectors entry he
      (Nat.le_trans (concat_component_length vectors entry.1 (List.fst_mem_of_mem_zipIdx he)) hbound))
    (by rw [concat_indexed_bits]; exact hpos) (by rw [concat_indexed_bits]; exact hbound)
  rw [concat_indexed_bits, concat_indexed_handles, (concat_initial_lengths vectors).1] at h
  exact h

/-- A one-bit mask test agrees with the corresponding packed-bit observation. -/
theorem concat_mask_test (word : U64) (bit : Nat) (hb : bit < 64) :
    (and_int word (shl_int (u64 1) (int bit)) != u64 0) = packedBit word bit := by
  cases hv : packedBit word bit
  · have hz : and_int word (shl_int (u64 1) (int bit)) = u64 0 := by
      apply packedBit_ext
      intro k hk
      rw [concat_and_bit, packedBit_shift_one bit k hb, packedBit_zero]
      by_cases he : k = bit
      · subst k
        rw [hv]
        rfl
      · simp only [he, decide_false, Bool.and_false]
    rw [hz]
    rfl
  · have hz : and_int word (shl_int (u64 1) (int bit)) ≠ u64 0 := by
      intro he
      have hbit := congrArg (fun w => packedBit w bit) he
      rw [concat_and_bit, packedBit_shift_one bit bit hb, packedBit_zero, hv] at hbit
      simp only [decide_true, Bool.true_and] at hbit
      contradiction
    exact bne_iff_ne.mpr hz

/-- The appended one-word destination exposes exactly one initialized chunk through the public contents model. -/
theorem concat_extend_contents (s : State) (word : U64) :
    (concat_extend s word).contents s.arrays.length = [some word] := by
  simp only [MutableMemory.contents, concat_extend_header, concat_extend_memory]
  rfl

/-- Each in-range logical read of the one-word destination sees the matching packed bit. -/
theorem concat_word_bitAt {N : Nat} (s : State) (word : U64) (length : I64)
    (dims : List I64) (bit : Nat) (hb : bit < 64) :
    bitAt (concat_extend s word) (⟨s.arrays.length, length, dims⟩ : BitArray N) bit =
      packedBit word bit := by
  simp only [bitAt, concat_extend_contents, Nat.div_eq_of_lt hb, List.getElem?_cons_zero,
    Nat.mod_eq_of_lt hb]
  exact concat_mask_test word bit hb

/-- Logical observations of a one-word packed list recover every original bit. -/
theorem concat_word_bitValues {N : Nat} (s : State) (xs : List Bool) (dims : List I64)
    (hbound : xs.length ≤ 64) :
    bitValues (concat_extend s (packedPrefix xs 0 64))
      (⟨s.arrays.length, int xs.length, dims⟩ : BitArray N) = xs := by
  have hlen := packedInt_val xs.length (by omega)
  unfold bitValues
  simp only [hlen, Int.toNat_natCast]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro bit hleft hright
    rw [List.getElem_map, List.getElem_range,
      concat_word_bitAt s (packedPrefix xs 0 64) (int xs.length) dims bit (by omega),
      packedWord_bit xs 0 bit (by omega)]
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hright, Option.getD_some]

/-- A packed one-word sequence has no true bits outside its logical length. -/
theorem concat_word_padding (xs : List Bool) (hpos : 0 < xs.length) (hbound : xs.length ≤ 64) :
    and_int (packedPrefix xs 0 64) (not_int (maskEnd (int xs.length))) = u64 0 := by
  have hc : wordCount xs.length = 1 := by unfold wordCount; omega
  apply packedBit_ext
  intro bit hb
  rw [concat_and_bit, concat_not_bit _ _ hb, packedWord_bit xs 0 bit hb,
    packedMask_last_bit xs.length bit hpos (by omega), hc, packedBit_zero]
  simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add]
  by_cases hi : bit < xs.length
  · simp only [hi, decide_true, Bool.not_true, Bool.and_false]
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : xs.length ≤ bit), Option.getD_none, Bool.false_and]

/-- Initialized one-word contents and a zero-padding equation imply the frozen invariant. -/
theorem concat_invariant_from_contents {N : Nat} (s : State) (B : BitArray N) (word : U64)
    (hcontents : s.contents B.chunks = [some word]) (hcount : numBitChunks B.len = int 1)
    (hpadding : and_int word (not_int (maskEndArray B)) = u64 0) :
    Round5.Round2.PackedInvariant s B := by
  unfold Round5.Round2.PackedInvariant
  rw [hcontents, hcount]
  constructor
  · rfl
  · by_cases hz : (B.len == int 0) = true
    · simp only [hz, ite_true]
    · simp only [hz, ite_false]
      exact hpadding

/-- The appended packed word satisfies the frozen chunk-count and final-padding invariant. -/
theorem concat_word_invariant {N : Nat} (s : State) (xs : List Bool) (dims : List I64)
    (hpos : 0 < xs.length) (hbound : xs.length ≤ 64) :
    Round5.Round2.PackedInvariant (concat_extend s (packedPrefix xs 0 64))
      (⟨s.arrays.length, int xs.length, dims⟩ : BitArray N) :=
  concat_invariant_from_contents _ _ _ (concat_extend_contents s (packedPrefix xs 0 64))
    (concat_num_chunks xs.length hpos hbound) (concat_word_padding xs hpos hbound)

/-- The frozen vector-vcat contract, including logical bits and padding, holds for every total length from 1 through 64. -/
theorem concat_vcat_single_correct (vectors : List (List Bool))
    (hpos : 0 < vectors.flatten.length) (hbound : vectors.flatten.length ≤ 64) :
    ∃ (out : BitVector) (finished : State),
      (bitArrayVcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors) =
          (.ok out, finished) ∧
      out.dims = [int vectors.flatten.length] ∧
      bitValues finished out = vectors.flatten ∧ Round5.Round2.PackedInvariant finished out := by
  let s := concat_initial vectors
  let out : BitVector := ⟨s.arrays.length, int vectors.flatten.length, [int vectors.flatten.length]⟩
  let finished := concat_extend s (packedPrefix vectors.flatten 0 64)
  refine ⟨out, finished, ?_, rfl, ?_, ?_⟩
  · have h := concat_vcat_single_word vectors hpos hbound
    apply h.trans
    dsimp only [out, s, finished]
    rw [(concat_initial_lengths vectors).1]
  · exact concat_word_bitValues s vectors.flatten _ hbound
  · exact concat_word_invariant s vectors.flatten _ hpos hbound

/-- A representable product is returned unchanged by the installed checked multiplication. -/
theorem concat_checked_mul_fits (left right result : I64)
    (hproduct : result.val = left.val * right.val) :
    JuliaLean.base.checked.checkedMulBits left right = .ok result := by
  have h : JuliaLean.Proofs.base.checked.ExactOrOverflow
      (JuliaLean.base.checked.checkedMulBits left right) (left.val * right.val) :=
    JuliaLean.Proofs.base.checked.mulExact .i64 left right
  have hin : IntTy.i64.min ≤ left.val * right.val ∧ left.val * right.val ≤ IntTy.i64.max := by
    rw [← hproduct]
    exact result.property
  unfold JuliaLean.Proofs.base.checked.ExactOrOverflow at h
  rw [if_pos hin] at h
  obtain ⟨value, hrun, hvalue⟩ := h
  have he : value = result := Subtype.ext (hvalue.trans hproduct.symm)
  exact hrun.trans (congrArg Except.ok he)

/-- Checked multiplication agrees with a fitting nonnegative natural product. -/
theorem concat_checked_product (left right : Nat)
    (hl : left ≤ 9223372036854775807) (hr : right ≤ 9223372036854775807)
    (hp : left * right ≤ 9223372036854775807) :
    JuliaLean.base.checked.checkedMulBits (int left) (int right) =
      .ok (int ((left * right : Nat) : Int)) := by
  apply concat_checked_mul_fits
  rw [packedInt_val left hl, packedInt_val right hr, packedInt_val (left * right) hp, Int.natCast_mul]

/-- Lifting a successful checked product preserves the heap. -/
theorem concat_checked_mutation_ok (left right value : I64) (s : State)
    (h : JuliaLean.base.checked.checkedMulBits left right = .ok value) :
    (checkedMultiplyMutation left right).run s = (.ok value, s) := by
  simp only [checkedMultiplyMutation, h, shape_run_pure]

/-- The two-factor dimension loop composes its two checked multiplication results. -/
theorem concat_checked_pair_from_runs (rows cols product : I64) (s : State)
    (hfirst : (checkedMultiplyMutation (int 1) rows).run s = (.ok rows, s))
    (hsecond : (checkedMultiplyMutation rows cols).run s = (.ok product, s)) :
    (checkedDimensionsModel [rows, cols]).run s = (.ok product, s) := by
  simp only [checkedDimensionsModel, List.forIn_cons, List.forIn_nil,
    shape_run_bind, shape_run_pure, hfirst, hsecond]

/-- Checked two-dimensional sizes compute their exact fitting product. -/
theorem concat_checked_pair (rows cols : Nat) (hr : rows ≤ 64) (hc : cols ≤ 64)
    (hp : rows * cols ≤ 64) (s : State) :
    (checkedDimensionsModel [int rows, int cols]).run s =
      (.ok (int ((rows * cols : Nat) : Int)), s) := by
  exact concat_checked_pair_from_runs (int rows) (int cols) (int ((rows * cols : Nat) : Int)) s
    (concat_checked_mutation_ok _ _ _ s (concat_checked_one rows hr))
    (concat_checked_mutation_ok _ _ _ s (concat_checked_product rows cols (by omega) (by omega) (by omega)))


/-- Two-dimensional one-word constructor execution separates validation from its supplied effects. -/
theorem concat_construct_pair {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (rows cols n : I64) (s allocated initialized : State) (handle : Nat)
    (hr : ¬ rows.val < 0) (hc : ¬ cols.val < 0)
    (hchecked : (checked [rows, cols]).run s = (.ok n, s))
    (hcount : numBitChunks n = int 1)
    (hallocate : (allocate 1).run s = (.ok handle, allocated))
    (hwrite : (mutableSet handle (u64 0) (int 1)).run allocated = (.ok (), initialized)) :
    (BitArrayUndef (N := N) checked allocate [rows, cols]).run s =
      (.ok ⟨handle, n, [rows, cols]⟩, initialized) := by
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hr, hc, ite_false,
    shape_run_bind, shape_run_pure, hchecked, hcount,
    show (int 1).val.toNat = 1 from rfl, hallocate,
    show (int 1).val > 0 from by decide, ite_true, hwrite]

/-- Allocating any positive matrix of at most 64 bits initializes its sole output word. -/
theorem concat_allocate_matrix (rows cols : Nat) (hr : rows ≤ 64) (hc : cols ≤ 64)
    (hpos : 0 < rows * cols) (hbound : rows * cols ≤ 64) (s : State) :
    (Round5.Round2.allocateBitArrayModel (N := 2) [int rows, int cols]).run s =
      (.ok (⟨s.arrays.length, int ((rows * cols : Nat) : Int), [int rows, int cols]⟩ : BitMatrix),
        concat_extend s (u64 0)) := by
  have hrows : ¬ (int rows).val < 0 := by rw [packedInt_val rows (by omega)]; omega
  have hcols : ¬ (int cols).val < 0 := by rw [packedInt_val cols (by omega)]; omega
  have ha : (s.arrays ++ [⟨(s.memories.length, one), int 1⟩])[s.arrays.length]? =
      some (⟨(s.memories.length, one), int 1⟩ : MutableVector) := by
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hm : (s.memories ++ [[none]])[s.memories.length]? = some [none] := by
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hwrite := concat_store_first
    (⟨s.memories ++ [[none]], s.arrays ++ [⟨(s.memories.length, one), int 1⟩]⟩ : State)
    s.arrays.length s.memories.length (int 1) none [] (u64 0) ha hm (by decide)
  simp only [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero] at hwrite
  exact concat_construct_pair checkedDimensionsModel allocateChunkVectorModel (int rows) (int cols)
    (int ((rows * cols : Nat) : Int)) s _ _ s.arrays.length hrows hcols
    (concat_checked_pair rows cols hr hc hbound s) (concat_num_chunks (rows * cols) hpos hbound)
    (concat_allocate_chunk s) hwrite

/-- Replacing a loop step by an equal step on every visited input preserves the complete loop. -/
theorem concat_forIn_congr {α β : Type} (items : List α) (initial : β)
    (left right : α → β → BitMutationM (ForInStep β))
    (h : ∀ item ∈ items, ∀ acc, left item acc = right item acc) :
    forIn items initial left = forIn items initial right := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    rw [List.forIn_cons, List.forIn_cons, h item List.mem_cons_self initial]
    congr 1
    funext step
    cases step with
    | done value => rfl
    | yield value => exact ih value (fun x hx => h x (List.mem_cons_of_mem item hx))

/-- One-based native index enumeration retrieves an arbitrary list exactly in order. -/
theorem concat_indexed_lookup {α : Type} (items : List α) (fallback : α)
    (hbound : items.length ≤ 9223372036854775807) :
    (intRange (int 1) (int items.length)).map (fun i => items.getD (i.val.toNat - 1) fallback) = items := by
  rw [packedObserve_intRange items.length hbound, List.map_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range, Function.comp_def]
    have hidx : (int ((index + 1 : Nat) : Int)).val.toNat - 1 = index := by
      rw [packedInt_val (index + 1) (by omega), Int.toNat_natCast]
      omega
    rw [hidx]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hright, Option.getD_some]

/-- Indexed iteration through one-based getD is the same iteration as traversing the source list. -/
theorem concat_indexed_loop {α β : Type} (items : List α) (fallback : α) (initial : β)
    (step : α → β → BitMutationM (ForInStep β)) (hbound : items.length ≤ 9223372036854775807) :
    forIn (intRange (int 1) (int items.length)) initial
      (fun i acc => step (items.getD (i.val.toNat - 1) fallback) acc) =
      forIn items initial step := by
  have hmap : forIn ((intRange (int 1) (int items.length)).map
      (fun i => items.getD (i.val.toNat - 1) fallback)) initial step =
      forIn (intRange (int 1) (int items.length)) initial
        (fun i acc => step (items.getD (i.val.toNat - 1) fallback) acc) := List.forIn_map
  exact hmap.symm.trans (congrArg (fun xs => forIn xs initial step)
    (concat_indexed_lookup items fallback hbound))

/-- Equal vector heights remain equal even in the source's getD fallback path. -/
theorem concat_getD_length (vectors : List BitVector) (fallback : BitVector) (height : I64)
    (hall : ∀ v ∈ vectors, v.len = height) (hfallback : fallback.len = height) (index : Nat) :
    (vectors.getD index fallback).len = height := by
  by_cases hi : index < vectors.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hall vectors[index] (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    exact hfallback

/-- Replacing per-vector lengths by a common height preserves every vcat copy step. -/
theorem concat_fixed_height_loop
    (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector) (dest : Nat) (height initial : I64)
    (hall : ∀ v ∈ vectors, v.len = height) :
    forIn vectors initial (fun (v : BitVector) (position : I64) => do
      copy dest position v.chunks (int 1) height
      pure (ForInStep.yield (position + height))) =
    forIn vectors initial (fun (v : BitVector) (position : I64) => do
      copy dest position v.chunks (int 1) v.len
      pure (ForInStep.yield (position + v.len))) := by
  apply concat_forIn_congr
  intro v hv _
  rw [hall v hv]

/-- Equal-height vectors have a rectangular total logical size. -/
theorem concat_rectangular_length (vectors : List (List Bool)) (height : Nat)
    (hall : ∀ xs ∈ vectors, xs.length = height) :
    vectors.flatten.length = height * vectors.length := by
  induction vectors with
  | nil => simp only [List.flatten_nil, List.length_nil, Nat.mul_zero]
  | cons xs vectors ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      hall xs List.mem_cons_self, ih (fun ys hy => hall ys (List.mem_cons_of_mem xs hy)), Nat.mul_add, Nat.mul_one]
    omega

/-- A dimension-validation loop succeeds unchanged when every indexed vector has the expected height. -/
theorem concat_validate_heights (indices : List I64) (lookup : I64 → BitVector) (height : I64)
    (s : State) (hall : ∀ i ∈ indices, (lookup i).len = height) :
    (forIn indices () (fun i _ => (do
      if (lookup i).len != height then throw (.dimensionMismatch "dimensions must match")
      pure (ForInStep.yield ())) : I64 → Unit → BitMutationM (ForInStep Unit))).run s = (.ok (), s) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    simp only [List.forIn_cons, hall index List.mem_cons_self, bne_self_eq_false,
      Bool.false_eq_true, ite_false, shape_run_bind, shape_run_pure]
    exact ih (fun i hi => hall i (List.mem_cons_of_mem index hi))

/-- The installed hcat control flow with an exposed copy action for compositional proofs. -/
def concat_hcat_program (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector) (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix := do
  let first ← match vectors with | [] => throw Error.bounds | v :: _ => pure v
  let height := first.len
  for j in intRange (int 2) (int vectors.length) do
    let v := vectors.getD (j.val.toNat - 1) first
    if v.len != height then throw (.dimensionMismatch "dimensions must match")
  let out ← allocate height (int vectors.length)
  let mut position := int 1
  for j in intRange (int 1) (int vectors.length) do
    let v := vectors.getD (j.val.toNat - 1) first
    copy out.chunks position v.chunks (int 1) height
    position := position + height
  return out

/-- The proof-parameterized hcat program is exactly the installed operation. -/
theorem concat_hcat_factor (vectors : List BitVector) (allocate : I64 → I64 → BitMutationM BitMatrix) :
    bitArrayHcatVectors vectors allocate = concat_hcat_program copyChunks vectors allocate := rfl

/-- The exact horizontal-concatenation height-validation action. -/
def concat_hcat_validation (vectors : List BitVector) (first : BitVector) : BitMutationM Unit :=
  forIn (intRange (int 2) (int vectors.length)) () (fun i _ => do
    if (vectors.getD (i.val.toNat - 1) first).len != first.len then
      throw (.dimensionMismatch "dimensions must match")
    pure (ForInStep.yield ()))

/-- The exact horizontal-concatenation indexed-copy action. -/
def concat_hcat_copy (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector) (first : BitVector) (out : BitMatrix) : BitMutationM I64 :=
  forIn (intRange (int 1) (int vectors.length)) (int 1) (fun (i : I64) (position : I64) => do
    copy out.chunks position (vectors.getD (i.val.toNat - 1) first).chunks (int 1) first.len
    pure (ForInStep.yield (position + first.len)))

/-- The nonempty horizontal-concatenation continuation after its first source is known. -/
def concat_hcat_body (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector) (first : BitVector)
    (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix := do
  concat_hcat_validation vectors first
  let out ← allocate first.len (int vectors.length)
  let _ ← concat_hcat_copy copy vectors first out
  pure out

/-- A successful validation, allocation, and dependent copy return the allocated output in the final heap. -/
theorem concat_three_stage_run {α β : Type}
    (validation : BitMutationM Unit) (allocate : BitMutationM α) (copy : α → BitMutationM β)
    (s allocated finished : State) (out : α) (register : β)
    (hvalidation : validation.run s = (.ok (), s))
    (hallocate : allocate.run s = (.ok out, allocated))
    (hcopy : (copy out).run allocated = (.ok register, finished)) :
    ((do validation; let out ← allocate; let _ ← copy out; pure out) : BitMutationM α).run s =
      (.ok out, finished) := by
  simp only [shape_run_bind, hvalidation, hallocate, hcopy, shape_run_pure]

/-- Selecting the first source reduces hcat exactly to its nonempty continuation. -/
theorem concat_hcat_nonempty_factor (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (first : BitVector) (rest : List BitVector) (allocate : I64 → I64 → BitMutationM BitMatrix) :
    concat_hcat_program copy (first :: rest) allocate =
      concat_hcat_body copy (first :: rest) first allocate := by
  unfold concat_hcat_program
  change (pure first >>= fun v => concat_hcat_body copy (first :: rest) v allocate) = _
  rw [pure_bind]

/-- Horizontal concatenation composes validation, allocation, and its indexed column-copy loop. -/
theorem concat_hcat_from_runs (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (vectors : List BitVector) (first : BitVector) (allocate : I64 → I64 → BitMutationM BitMatrix)
    (s allocated finished : State) (out : BitMatrix) (finalPosition : I64)
    (hvalidate : (forIn (intRange (int 2) (int vectors.length)) ()
      (fun i _ => (do
        if (vectors.getD (i.val.toNat - 1) first).len != first.len then
          throw (.dimensionMismatch "dimensions must match")
        pure (ForInStep.yield ())) : I64 → Unit → BitMutationM (ForInStep Unit))).run s = (.ok (), s))
    (hallocate : (allocate first.len (int vectors.length)).run s = (.ok out, allocated))
    (hcopy : (forIn (intRange (int 1) (int vectors.length)) (int 1)
      (fun (i : I64) (position : I64) => do
        copy out.chunks position (vectors.getD (i.val.toNat - 1) first).chunks (int 1) first.len
        pure (ForInStep.yield (position + first.len)))).run allocated = (.ok finalPosition, finished)) :
    (concat_hcat_body copy vectors first allocate).run s = (.ok out, finished) := by
  exact concat_three_stage_run (concat_hcat_validation vectors first)
    (allocate first.len (int vectors.length)) (concat_hcat_copy copy vectors first)
    s allocated finished out finalPosition hvalidate hallocate hcopy

/-- Equal-height indexed source entries have the rectangular total size. -/
theorem concat_entries_rectangular (entries : List (List Bool × Nat)) (height : Nat)
    (hall : ∀ entry ∈ entries, entry.1.length = height) :
    (entries.flatMap Prod.fst).length = height * entries.length := by
  rw [List.flatMap_def]
  have h := concat_rectangular_length (entries.map Prod.fst) height (by
    intro xs hx
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hx
    exact hall entry he)
  simpa only [List.length_map] using h

/-- The frozen matrix allocator with its matrix result type kept explicit. -/
def concat_allocate_matrix_fn (rows cols : I64) : BitMutationM BitMatrix :=
  Round5.Round2.allocateBitArrayModel [rows, cols]

/-- Horizontal concatenation of equal-height ready sources stores their logical columns exactly in one word. -/
theorem concat_hcat_single_ready (first : List Bool × Nat) (rest : List (List Bool × Nat)) (s : State)
    (hready : ∀ entry ∈ first :: rest, concat_ready s entry)
    (hall : ∀ entry ∈ first :: rest, entry.1.length = first.1.length)
    (hpos : 0 < ((first :: rest).flatMap Prod.fst).length)
    (hbound : ((first :: rest).flatMap Prod.fst).length ≤ 64) :
    (bitArrayHcatVectors ((first :: rest).map concat_vector) concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int ((first :: rest).flatMap Prod.fst).length,
        [int first.1.length, int (first :: rest).length]⟩ : BitMatrix),
        concat_extend s (packedPrefix ((first :: rest).flatMap Prod.fst) 0 64)) := by
  let entries := first :: rest
  let vectors := entries.map concat_vector
  let height := first.1.length
  let bits := entries.flatMap Prod.fst
  have hrect : bits.length = height * entries.length := concat_entries_rectangular entries height hall
  have hhpos : 0 < height := by
    by_cases hz : height = 0
    · have hzbits : bits.length = 0 := by rw [hrect, hz, Nat.zero_mul]
      exact False.elim (by change 0 < bits.length at hpos; omega)
    · omega
  have hen : 0 < entries.length := by change 0 < (first :: rest).length; simp only [List.length_cons]; omega
  have hr : height ≤ 64 := by
    have h := Nat.mul_le_mul_left height (show 1 ≤ entries.length by omega)
    simp only [Nat.mul_one] at h
    change bits.length ≤ 64 at hbound
    omega
  have hc : entries.length ≤ 64 := by
    have h := Nat.mul_le_mul_right entries.length (show 1 ≤ height by omega)
    simp only [Nat.one_mul] at h
    change bits.length ≤ 64 at hbound
    omega
  have hvecLen : vectors.length = entries.length := by simp only [vectors, List.length_map]
  have hvecAll : ∀ v ∈ vectors, v.len = int height := by
    intro v hv
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hv
    rw [concat_vector_len, hall entry he]
  have hvalidation := concat_validate_heights
    (intRange (int 2) (int vectors.length))
    (fun i => vectors.getD (i.val.toNat - 1) (concat_vector first)) (int height) s
    (fun i _ => concat_getD_length vectors (concat_vector first) (int height) hvecAll rfl _)
  have halloc : (concat_allocate_matrix_fn (int height) (int entries.length)).run s =
      (.ok (⟨s.arrays.length, int ((height * entries.length : Nat) : Int),
        [int height, int entries.length]⟩ : BitMatrix), concat_extend s (u64 0)) :=
    concat_allocate_matrix height entries.length hr hc
      (by rw [← hrect]; exact hpos) (by rw [← hrect]; exact hbound) s
  rw [← hrect] at halloc
  have hcopyList := concat_copy_loop entries [] s hready
    (by simpa only [List.length_nil, Nat.zero_add] using hbound)
  have hzero : packedPrefix [] 0 64 = u64 0 := (packedWord_zero_iff [] 0).mpr (fun _ _ => rfl)
  simp only [List.length_nil, Nat.zero_add, List.nil_append, hzero, Int.ofNat_one] at hcopyList
  let step : BitVector → I64 → BitMutationM (ForInStep I64) := fun v position => do
    copyChunks s.arrays.length position v.chunks (int 1) (int height)
    pure (ForInStep.yield (position + int height))
  have hindexed := concat_indexed_loop vectors (concat_vector first) (int 1) step (by rw [hvecLen]; omega)
  have hfixed := concat_fixed_height_loop copyChunks vectors s.arrays.length (int height) (int 1) hvecAll
  have hcopy := (congrArg (fun action => action.run (concat_extend s (u64 0)))
    (hindexed.trans hfixed)).trans hcopyList
  rw [concat_hcat_factor, List.map_cons, concat_hcat_nonempty_factor]
  exact concat_hcat_from_runs copyChunks vectors (concat_vector first) concat_allocate_matrix_fn
    s _ _ _ _ hvalidation (by rw [hvecLen]; exact halloc) hcopy

/-- The frozen hcat contract, including logical bits and padding, holds for every rectangular output of 1–64 bits. -/
theorem concat_hcat_single_correct (vectors : List (List Bool))
    (hpos : 0 < vectors.flatten.length) (hbound : vectors.flatten.length ≤ 64)
    (hall : ∀ xs ∈ vectors, xs.length = (vectors.headD []).length) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayHcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors) =
          (.ok out, finished) ∧
      out.dims = [int (vectors.headD []).length, int vectors.length] ∧
      bitValues finished out = vectors.flatten ∧ Round5.Round2.PackedInvariant finished out := by
  cases vectors with
  | nil => simp only [List.flatten_nil, List.length_nil] at hpos; omega
  | cons first rest =>
    let vectors := first :: rest
    let s := concat_initial vectors
    let out : BitMatrix := ⟨s.arrays.length, int vectors.flatten.length,
      [int (vectors.headD []).length, int vectors.length]⟩
    let finished := concat_extend s (packedPrefix vectors.flatten 0 64)
    have h := concat_hcat_single_ready (first, 0) (rest.zipIdx 1) s
      (fun entry he => concat_initial_ready vectors entry he
        (Nat.le_trans (concat_component_length vectors entry.1 (List.fst_mem_of_mem_zipIdx he)) hbound))
      (fun entry he => hall entry.1 (List.fst_mem_of_mem_zipIdx he))
      (by change 0 < (vectors.zipIdx.flatMap Prod.fst).length; rw [concat_indexed_bits]; exact hpos)
      (by change (vectors.zipIdx.flatMap Prod.fst).length ≤ 64; rw [concat_indexed_bits]; exact hbound)
    change (bitArrayHcatVectors (vectors.zipIdx.map concat_vector) concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int (vectors.zipIdx.flatMap Prod.fst).length,
        [int (vectors.headD []).length, int vectors.zipIdx.length]⟩ : BitMatrix),
        concat_extend s (packedPrefix (vectors.zipIdx.flatMap Prod.fst) 0 64)) at h
    rw [concat_indexed_bits, concat_indexed_handles, List.length_zipIdx] at h
    refine ⟨out, finished, h, rfl, ?_, ?_⟩
    · exact concat_word_bitValues s vectors.flatten _ hbound
    · exact concat_word_invariant s vectors.flatten _ hpos hbound

/-- The matrix-vcat source control flow with its copy operation exposed for proofs. -/
def concat_matrix_program (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit) (arrays : List BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix := do
  let first ← match arrays with | [] => throw Error.bounds | a :: _ => pure a
  let mut nrows := int 0
  let mut nrowsA := []
  for a in arrays do
    let sz1 := sizeDim a (int 1)
    nrows := nrows + sz1
    nrowsA := nrowsA ++ [sz1]
  let ncols := sizeDim first (int 2)
  for j in intRange (int 2) (int arrays.length) do
    let a := arrays.getD (j.val.toNat - 1) first
    if sizeDim a (int 2) != ncols then throw (.dimensionMismatch "column lengths must match")
  let out ← allocate nrows ncols
  let mut posD := int 1
  let mut posS := List.replicate arrays.length (int 1)
  for _ in intRange (int 1) ncols do
    for k in intRange (int 1) (int arrays.length) do
      let a := arrays.getD (k.val.toNat - 1) first
      let n := nrowsA.getD (k.val.toNat - 1) (int 0)
      let s := posS.getD (k.val.toNat - 1) (int 1)
      copy out.chunks posD a.chunks s n
      posS := posS.set (k.val.toNat - 1) (s + n)
      posD := posD + n
  return out

/-- Range iteration composes indexed heap and loop-register invariants. -/
theorem concat_range_loop {α : Type} (start count limit : Nat)
    (registers : Nat → α) (state : Nat → State)
    (step : Nat → α → BitMutationM (ForInStep α))
    (hstep : ∀ index, index < limit → (step index (registers index)).run (state index) =
      (.ok (ForInStep.yield (registers (index + 1))), state (index + 1)))
    (hbound : start + count ≤ limit) :
    (forIn (List.range' start count) (registers start) step).run (state start) =
      (.ok (registers (start + count)), state (start + count)) := by
  induction count generalizing start with
  | zero => simp only [List.range'_zero, List.forIn_nil, Nat.add_zero, shape_run_pure]
  | succ count ih =>
    have hs : start < limit := by omega
    have ht := ih (start + 1) (by omega)
    have he : start + 1 + count = start + (count + 1) := by omega
    rw [he] at ht
    simp only [List.range'_succ, List.forIn_cons, shape_run_bind, hstep start hs]
    exact ht

/-- The installed inner matrix-vcat step expressed with its decoded zero-based index. -/
def concat_matrix_raw_step (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dest : Nat) (arrays : List BitMatrix) (heights : List I64) (fallback : BitMatrix)
    (index : Nat) (registers : I64 × List I64) : BitMutationM (ForInStep (I64 × List I64)) := do
  let A := arrays.getD index fallback
  let rows := heights.getD index (int 0)
  let sourcePos := registers.2.getD index (int 1)
  copy dest registers.1 A.chunks sourcePos rows
  pure (ForInStep.yield (registers.1 + rows, registers.2.set index (sourcePos + rows)))

/-- The installed first pass collects all input row counts while summing the total rows. -/
def concat_matrix_scan (arrays : List BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (initial : I64 × List I64) : BitMutationM (I64 × List I64) :=
  forIn arrays initial fun A registers =>
    pure (ForInStep.yield (registers.1 + sizeDim A (int 1), registers.2 ++ [sizeDim A (int 1)]))


/-- The matrix-vcat column-count validation action, identical to the installed source loop. -/
def concat_matrix_validation (arrays : List BitMatrix) (fallback : BitMatrix)
    (sizeDim : BitMatrix → I64 → I64) (columns : I64) : BitMutationM Unit :=
  forIn (intRange (int 2) (int arrays.length)) () fun index _ => do
    if sizeDim (arrays.getD (index.val.toNat - 1) fallback) (int 2) != columns then
      throw (.dimensionMismatch "column lengths must match")
    pure (ForInStep.yield ())

/-- The source's nested native-index copy phase, with its output header supplied by allocation. -/
def concat_matrix_copies (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (arrays : List BitMatrix) (fallback : BitMatrix) (heights : List I64)
    (columns : I64) (out : BitMatrix) : BitMutationM (I64 × List I64) :=
  forIn (intRange (int 1) columns) (int 1, List.replicate arrays.length (int 1)) fun _ registers => do
    let registers ← forIn (intRange (int 1) (int arrays.length)) registers
      (fun index current => concat_matrix_raw_step copy out.chunks arrays heights fallback
        (index.val.toNat - 1) current)
    pure (ForInStep.yield registers)

/-- The matrix-vcat continuation after the row-count scan, preserving the installed validation/allocation order. -/
def concat_matrix_after_scan (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (arrays : List BitMatrix) (first : BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) (rowInfo : I64 × List I64) :
    BitMutationM BitMatrix := do
  let columns := sizeDim first (int 2)
  concat_matrix_validation arrays first sizeDim columns
  let out ← allocate rowInfo.1 columns
  let _ ← concat_matrix_copies copy arrays first rowInfo.2 columns out
  pure out

/-- The nonempty matrix-vcat body collects rows before executing its remaining source phases. -/
def concat_matrix_body (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (arrays : List BitMatrix) (first : BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix := do
  let rowInfo ← concat_matrix_scan arrays sizeDim (int 0, [])
  concat_matrix_after_scan copy arrays first sizeDim allocate rowInfo

/-- The installed nonempty matrix-vcat operation is exactly its scan/validation/allocation/copy factorization. -/
theorem concat_matrix_nonempty_factor (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (first : BitMatrix) (rest : List BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) :
    concat_matrix_program copy (first :: rest) sizeDim allocate =
      concat_matrix_body copy (first :: rest) first sizeDim allocate := by
  unfold concat_matrix_program
  change (pure first >>= fun value => concat_matrix_body copy (first :: rest) value sizeDim allocate) = _
  rw [pure_bind]

/-- Successful monadic phases compose without unfolding their source implementations. -/
theorem concat_bind_success {α β : Type} (action : BitMutationM α)
    (continuation : α → BitMutationM β) (s middle finished : State) (value : α) (result : β)
    (hfirst : action.run s = (.ok value, middle))
    (hsecond : (continuation value).run middle = (.ok result, finished)) :
    (action >>= continuation).run s = (.ok result, finished) := by
  simp only [shape_run_bind, hfirst]
  exact hsecond


/-- Allocating zero chunks appends an empty backing memory and a zero-length one-based header. -/
def concat_extend_empty (s : State) : State :=
  ⟨s.memories ++ [[]], s.arrays ++ [⟨(s.memories.length, one), int 0⟩]⟩

/-- Zero-chunk allocation has no storage initialization step. -/
theorem concat_allocate_empty_chunk (s : State) :
    (allocateChunkVectorModel 0).run s = (.ok s.arrays.length, concat_extend_empty s) := rfl

/-- The installed empty-vector constructor appends exactly a zero-length destination. -/
theorem concat_allocate_empty_vector (s : State) :
    (concat_allocate_vector (int 0)).run s =
      (.ok (⟨s.arrays.length, int 0, [int 0]⟩ : BitVector), concat_extend_empty s) := rfl

/-- The constructor validates two dimensions but performs no chunk write for a zero total size. -/
theorem concat_construct_empty_pair {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (rows cols : I64) (s allocated : State) (handle : Nat)
    (hr : ¬ rows.val < 0) (hc : ¬ cols.val < 0)
    (hchecked : (checked [rows, cols]).run s = (.ok (int 0), s))
    (hallocate : (allocate 0).run s = (.ok handle, allocated)) :
    (BitArrayUndef (N := N) checked allocate [rows, cols]).run s =
      (.ok ⟨handle, int 0, [rows, cols]⟩, allocated) := by
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hr, hc, ite_false,
    shape_run_bind, shape_run_pure, hchecked,
    show numBitChunks (int 0) = int 0 from rfl,
    show (int 0).val.toNat = 0 from rfl, hallocate,
    show ¬ (int 0).val > 0 from by decide, ite_false]

/-- Checked dimensions produce an exact representable nonnegative product. -/
theorem concat_checked_pair_general (rows cols : Nat)
    (hr : rows ≤ 9223372036854775807) (hc : cols ≤ 9223372036854775807)
    (hp : rows * cols ≤ 9223372036854775807) (s : State) :
    (checkedDimensionsModel [int rows, int cols]).run s =
      (.ok (int ((rows * cols : Nat) : Int)), s) := by
  have hfirst := concat_checked_product 1 rows (by decide) hr (by simpa only [Nat.one_mul] using hr)
  simp only [Nat.one_mul, Int.ofNat_one] at hfirst
  exact concat_checked_pair_from_runs (int rows) (int cols) (int ((rows * cols : Nat) : Int)) s
    (concat_checked_mutation_ok _ _ _ s hfirst)
    (concat_checked_mutation_ok _ _ _ s (concat_checked_product rows cols hr hc hp))

/-- Every representable empty matrix shape allocates an empty destination without touching any source. -/
theorem concat_allocate_empty_matrix (rows cols : Nat)
    (hr : rows ≤ 9223372036854775807) (hc : cols ≤ 9223372036854775807)
    (hz : rows * cols = 0) (s : State) :
    (concat_allocate_matrix_fn (int rows) (int cols)).run s =
      (.ok (⟨s.arrays.length, int 0, [int rows, int cols]⟩ : BitMatrix), concat_extend_empty s) := by
  have hrows : ¬ (int rows).val < 0 := by rw [packedInt_val rows hr]; omega
  have hcols : ¬ (int cols).val < 0 := by rw [packedInt_val cols hc]; omega
  have hchecked := concat_checked_pair_general rows cols hr hc (by omega) s
  rw [hz] at hchecked
  exact concat_construct_empty_pair checkedDimensionsModel allocateChunkVectorModel (int rows) (int cols)
    s _ s.arrays.length hrows hcols hchecked (concat_allocate_empty_chunk s)

/-- The newly allocated zero-length header observes an empty sequence of chunks. -/
theorem concat_empty_contents (s : State) : (concat_extend_empty s).contents s.arrays.length = [] := by
  simp only [MutableMemory.contents, concat_extend_empty,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  rfl

/-- Zero logical length has no bit observations in any heap. -/
theorem concat_empty_bitValues {N : Nat} (s : State) (handle : Nat) (dims : List I64) :
    bitValues s (⟨handle, int 0, dims⟩ : BitArray N) = [] := rfl

/-- The appended empty destination satisfies the full frozen packed invariant. -/
theorem concat_empty_invariant {N : Nat} (s : State) (dims : List I64) :
    Round5.Round2.PackedInvariant (concat_extend_empty s)
      (⟨s.arrays.length, int 0, dims⟩ : BitArray N) := by
  unfold Round5.Round2.PackedInvariant
  rw [concat_empty_contents]
  change [].length = (numBitChunks (int 0)).val.toNat ∧ True
  exact ⟨by decide, trivial⟩

/-- Wrapped signed addition also has zero as a right identity. -/
theorem concat_add_zero (value : I64) : value + int 0 = value := by
  apply Subtype.ext
  change wrapInt .i64 (value.val + 0) = value.val
  rw [Int.add_zero]
  exact wrapInt_of_inRange .i64 value.val value.property

/-- A loop whose every visited step yields the same register and heap is an exact no-op. -/
theorem concat_forIn_unchanged {α β : Type} (items : List α) (value : β)
    (step : α → β → BitMutationM (ForInStep β)) (s : State)
    (hstep : ∀ item ∈ items, (step item value).run s = (.ok (ForInStep.yield value), s)) :
    (forIn items value step).run s = (.ok value, s) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.forIn_cons, shape_run_bind, hstep item List.mem_cons_self]
    exact ih (fun i hi => hstep i (List.mem_cons_of_mem item hi))


/-- Vcat of arbitrary empty logical source headers allocates an empty output and leaves all sources untouched. -/
theorem concat_vcat_empty_ready (vectors : List BitVector) (s : State)
    (hall : ∀ vector ∈ vectors, vector.len = int 0) :
    (bitArrayVcatVectors vectors concat_allocate_vector).run s =
      (.ok (⟨s.arrays.length, int 0, [int 0]⟩ : BitVector), concat_extend_empty s) := by
  have hsum : (forIn vectors (int 0) (fun (v : BitVector) (n : I64) =>
      (pure (ForInStep.yield (n + v.len)) : BitMutationM (ForInStep I64)))).run s = (.ok (int 0), s) := by
    apply concat_forIn_unchanged
    intro vector hv
    simp only [hall vector hv, concat_add_zero, shape_run_pure]
  have hcopy : (forIn vectors (int 1) (fun (vector : BitVector) (position : I64) => do
      copyChunks s.arrays.length position vector.chunks (int 1) vector.len
      pure (ForInStep.yield (position + vector.len)))).run (concat_extend_empty s) =
      (.ok (int 1), concat_extend_empty s) := by
    apply concat_forIn_unchanged
    intro vector hv
    simp only [hall vector hv, concat_add_zero, shape_run_bind, concat_copy_zero, shape_run_pure]
  rw [concat_vcat_factor]
  exact concat_vcat_from_runs copyChunks vectors concat_allocate_vector s _ _ (int 0) (int 1)
    _ hsum (concat_allocate_empty_vector s) hcopy

/-- An empty flattened input can contain only empty component lists. -/
theorem concat_flatten_empty_member (vectors : List (List Bool)) (hempty : vectors.flatten = [])
    (xs : List Bool) (hx : xs ∈ vectors) : xs = [] := by
  have h := concat_component_length vectors xs hx
  rw [hempty, List.length_nil] at h
  exact List.length_eq_zero_iff.mp (by omega)

/-- The frozen vector-vcat contract holds for zero total bits, including an empty source list. -/
theorem concat_vcat_empty_correct (vectors : List (List Bool)) (hempty : vectors.flatten = []) :
    ∃ (out : BitVector) (finished : State),
      (bitArrayVcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors) =
          (.ok out, finished) ∧
      out.dims = [int vectors.flatten.length] ∧
      bitValues finished out = vectors.flatten ∧ Round5.Round2.PackedInvariant finished out := by
  let s := concat_initial vectors
  have hrun := concat_vcat_empty_ready (vectors.zipIdx.map concat_vector) s (by
    intro vector hv
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hv
    rw [concat_vector_len, concat_flatten_empty_member vectors hempty entry.1
      (List.fst_mem_of_mem_zipIdx he)]
    rfl)
  rw [concat_indexed_handles] at hrun
  refine ⟨⟨s.arrays.length, int 0, [int 0]⟩, concat_extend_empty s, hrun, ?_, ?_, concat_empty_invariant s _⟩
  · simp only [hempty, List.length_nil, Int.ofNat_zero]
  · rw [concat_empty_bitValues, hempty]

/-- Vcat satisfies all frozen observations for every total output length at most one word. -/
theorem concat_vcat_small_correct (vectors : List (List Bool)) (hbound : vectors.flatten.length ≤ 64) :
    ∃ (out : BitVector) (finished : State),
      (bitArrayVcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors) =
          (.ok out, finished) ∧
      out.dims = [int vectors.flatten.length] ∧
      bitValues finished out = vectors.flatten ∧ Round5.Round2.PackedInvariant finished out := by
  by_cases hpos : 0 < vectors.flatten.length
  · exact concat_vcat_single_correct vectors hpos hbound
  · exact concat_vcat_empty_correct vectors (List.length_eq_zero_iff.mp (by omega))

/-- Hcat of empty source columns validates their common height and allocates its exact zero-row shape. -/
theorem concat_hcat_empty_ready (first : BitVector) (rest : List BitVector) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hall : ∀ vector ∈ first :: rest, vector.len = int 0) :
    (bitArrayHcatVectors (first :: rest) concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int 0, [int 0, int (first :: rest).length]⟩ : BitMatrix), concat_extend_empty s) := by
  let vectors := first :: rest
  let out : BitMatrix := ⟨s.arrays.length, int 0, [int 0, int vectors.length]⟩
  have hfirst : first.len = int 0 := hall first List.mem_cons_self
  have hvalidation := concat_validate_heights
    (intRange (int 2) (int vectors.length))
    (fun index => vectors.getD (index.val.toNat - 1) first) first.len s (by
      intro index hi
      rw [hfirst]
      exact concat_getD_length vectors first (int 0) hall hfirst (index.val.toNat - 1))
  have hallocate : (concat_allocate_matrix_fn first.len (int vectors.length)).run s =
      (.ok out, concat_extend_empty s) := by
    rw [hfirst]
    exact concat_allocate_empty_matrix 0 vectors.length (by decide) hcount (by simp only [Nat.zero_mul]) s
  have hcopy : (concat_hcat_copy copyChunks vectors first out).run (concat_extend_empty s) =
      (.ok (int 1), concat_extend_empty s) := by
    unfold concat_hcat_copy
    apply concat_forIn_unchanged
    intro index hi
    simp only [hfirst, concat_add_zero, shape_run_bind, concat_copy_zero, shape_run_pure]
  rw [concat_hcat_factor, concat_hcat_nonempty_factor]
  exact concat_hcat_from_runs copyChunks vectors first concat_allocate_matrix_fn
    s _ _ out (int 1) hvalidation hallocate hcopy

/-- Empty nonempty hcat inputs satisfy the frozen shape, contents, and packed invariant. -/
theorem concat_hcat_empty_correct (vectors : List (List Bool)) (hne : vectors ≠ [])
    (hcount : vectors.length ≤ 9223372036854775807) (hempty : vectors.flatten = []) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayHcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors) =
          (.ok out, finished) ∧
      out.dims = [int (vectors.headD []).length, int vectors.length] ∧
      bitValues finished out = vectors.flatten ∧ Round5.Round2.PackedInvariant finished out := by
  cases vectors with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    let vectors := first :: rest
    let s := concat_initial vectors
    have hall : ∀ vector ∈ vectors.zipIdx.map concat_vector, vector.len = int 0 := by
      intro vector hv
      obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hv
      rw [concat_vector_len, concat_flatten_empty_member vectors hempty entry.1
        (List.fst_mem_of_mem_zipIdx he)]
      rfl
    have hrun := concat_hcat_empty_ready (concat_vector (first, 0))
      ((rest.zipIdx 1).map concat_vector) s
      (by simpa only [List.length_cons, List.length_map, List.length_zipIdx] using hcount) hall
    change (bitArrayHcatVectors (vectors.zipIdx.map concat_vector) concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int 0, [int 0, int (vectors.zipIdx.map concat_vector).length]⟩ : BitMatrix),
        concat_extend_empty s) at hrun
    rw [List.length_map, List.length_zipIdx, concat_indexed_handles] at hrun
    refine ⟨⟨s.arrays.length, int 0, [int 0, int vectors.length]⟩, concat_extend_empty s,
      hrun, ?_, ?_, concat_empty_invariant s _⟩
    · have hf : first = [] := concat_flatten_empty_member vectors hempty first List.mem_cons_self
      simp only [vectors, List.headD_cons, hf, List.length_nil, Int.ofNat_zero]
    · rw [concat_empty_bitValues, hempty]

/-- Hcat satisfies all frozen observations for every nonempty rectangular input with at most one word of output. -/
theorem concat_hcat_small_correct (vectors : List (List Bool)) (hne : vectors ≠ [])
    (hcount : vectors.length ≤ 9223372036854775807) (hbound : vectors.flatten.length ≤ 64)
    (hall : ∀ xs ∈ vectors, xs.length = (vectors.headD []).length) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayHcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors) =
          (.ok out, finished) ∧
      out.dims = [int (vectors.headD []).length, int vectors.length] ∧
      bitValues finished out = vectors.flatten ∧ Round5.Round2.PackedInvariant finished out := by
  by_cases hpos : 0 < vectors.flatten.length
  · exact concat_hcat_single_correct vectors hpos hbound hall
  · exact concat_hcat_empty_correct vectors hne hcount (List.length_eq_zero_iff.mp (by omega))

theorem concat_div64_val (i : I64) : (div64 i).val = i.val / 64 := by
  rw [div64, JuliaLean.Proofs.base.int.ashr_int_val (by rfl)]
  rfl


theorem concat_mod64_val (i : I64) : (mod64 i).val = i.val % 64 := by
  have he := packedMod64_nat i
  have hr := JuliaLean.Proofs.base.int.fromJInt_toNat (mod64 i)
  have hb := (mod64 i).property
  change -9223372036854775808 ≤ (mod64 i).val ∧
    (mod64 i).val ≤ 9223372036854775807 at hb
  change ((fromJInt (mod64 i)).toNat : Int) =
    (mod64 i).val % 18446744073709551616 at hr
  have hmod : 0 ≤ i.val % 64 ∧ i.val % 64 < 64 :=
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  rw [he] at hr
  omega


theorem concat_num_chunks_val (n : I64) (hn : 0 ≤ n.val) :
    (numBitChunks n).val = (n.val + 63) / 64 := by
  have hb := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
  have hm : (mod64 n == int 0) = decide (n.val % 64 = 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      rw [concat_mod64_val] at hv
      exact hv
    · intro h
      apply Subtype.ext
      rw [concat_mod64_val, h]
      rfl
  unfold numBitChunks
  rw [hm]
  by_cases hz : n.val % 64 = 0
  · simp only [hz, decide_true, ite_true]
    change wrapInt .i64 ((div64 n).val + 0) = _
    rw [concat_div64_val]
    rw [wrapInt_of_inRange .i64 _ (by
      change -9223372036854775808 ≤ n.val / 64 + 0 ∧
        n.val / 64 + 0 ≤ 9223372036854775807
      omega)]
    omega
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    change wrapInt .i64 ((div64 n).val + 1) = _
    rw [concat_div64_val]
    rw [wrapInt_of_inRange .i64 _ (by
      change -9223372036854775808 ≤ n.val / 64 + 1 ∧
        n.val / 64 + 1 ≤ 9223372036854775807
      omega)]
    omega


/-- Ceiling division counts the installed chunks for every representable nonnegative logical length. -/
theorem concat_num_chunks_general (n : Nat) (hn : n ≤ 9223372036854775807) :
    numBitChunks (int n) = int (wordCount n) := by
  have hc : wordCount n ≤ 9223372036854775807 := by unfold wordCount; omega
  apply Subtype.ext
  rw [concat_num_chunks_val (int n) (by rw [packedInt_val n hn]; omega),
    packedInt_val n hn, packedInt_val (wordCount n) hc]
  unfold wordCount
  omega

/-- Fresh chunk storage keeps its backing memory and visible header length explicit. -/
def concat_new_chunks (s : State) (count : Nat) (slots : List (Option U64)) : State :=
  ⟨s.memories ++ [slots], s.arrays ++ [⟨(s.memories.length, one), int count⟩]⟩

theorem concat_new_chunks_header (s : State) (count : Nat) (slots : List (Option U64)) :
    (concat_new_chunks s count slots).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), int count⟩ := by
  simp only [concat_new_chunks, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem concat_new_chunks_memory (s : State) (count : Nat) (slots : List (Option U64)) :
    (concat_new_chunks s count slots).memories[s.memories.length]? = some slots := by
  simp only [concat_new_chunks, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- The frozen allocator creates the requested number of unassigned chunk slots. -/
theorem concat_allocate_chunks_general (count : Nat) (hc : count ≤ 576460752303423488) (s : State) :
    (allocateChunkVectorModel count).run s =
      (.ok s.arrays.length, concat_new_chunks s count (List.replicate count none)) := by
  have hn64 : count ≤ 9223372036854775807 := by omega
  have hnat : ((int count).val % 2 ^ 64).toNat = count := by
    rw [packedInt_val count hn64, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hb : count * 8 < 2 ^ 64 := by omega
  have hz : (count * 8) % 2 ^ 64 = count * 8 := Nat.mod_eq_of_lt hb
  have hlimit1 : ¬ (count ≥ maxIntVal - 1) := by unfold maxIntVal; omega
  have hlimit2 : ¬ (count * 8 ≥ maxIntVal - 1) := by unfold maxIntVal; omega
  by_cases hn0 : count = 0
  · subst count
    rfl
  · simp only [allocateChunkVectorModel, Int.ofNat_eq_natCast, mutableAllocate, arrayUndef1, memoryUndef, memorynew,
      hnat, allocGenericMemory, hn0, ite_false, Bool.false_eq_true, newGenericMemory,
      sizeMulOverflow, hz, show ¬ (2 ^ 64 ≤ count * 8) by omega, decide_false,
      hlimit1, hlimit2, Bool.false_or, Bool.false_eq_true, mutableFreshMemory,
      shape_run_bind, shape_run_get, shape_run_pure]
    rfl

/-- An arbitrary valid chunk slot is written without changing any source header. -/
theorem concat_store_index (s : State) (handle mem : Nat) (length : I64)
    (slots : List (Option U64)) (index : Nat) (word : U64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), length⟩)
    (hm : s.memories[mem]? = some slots)
    (hi : 1 ≤ index) (hindex : index ≤ 9223372036854775807)
    (hbound : (index : Int) ≤ length.val) (hslot : index ≤ slots.length) :
    (mutableSet handle word (int index)).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (index - 1) (some word))}) := by
  have hb : one ≤ int index ∧ int index ≤ length := by
    change 1 ≤ (int index).val ∧ (int index).val ≤ length.val
    rw [packedInt_val index hindex]
    omega
  have hmem : 1 ≤ (int index).val ∧ (int index).val ≤ (slots.length : Int) := by
    rw [packedInt_val index hindex]
    omega
  have hposition : ((int index).val - 1).toNat = index - 1 := by
    rw [packedInt_val index hindex]
    omega
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_one_add_sub_one, memoryWrite, memoryRead, shape_run_get, hm,
    hmem, shape_run_modify, hposition]

/-- Initializing the last fresh chunk leaves every other newly allocated slot unassigned. -/
theorem concat_initialize_last (count : Nat) (hp : 0 < count) (hc : count ≤ 9223372036854775807)
    (s : State) :
    (mutableSet s.arrays.length (u64 0) (int count)).run
      (concat_new_chunks s count (List.replicate count none)) =
      (.ok (), concat_new_chunks s count ((List.replicate count none).set (count - 1) (some (u64 0)))) := by
  have h := concat_store_index (concat_new_chunks s count (List.replicate count none))
    s.arrays.length s.memories.length (int count) (List.replicate count none) count (u64 0)
    (concat_new_chunks_header s count _) (concat_new_chunks_memory s count _) hp hc
    (by rw [packedInt_val count hc]; exact Int.le_refl _) (by simpa only [List.length_replicate] using (Nat.le_refl count))
  apply h.trans
  simp only [concat_new_chunks, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

/-- A representable native length is preserved by its singleton checked-dimension pass. -/
theorem concat_checked_dims_general (n : I64) (s : State) :
    (checkedDimensionsModel [n]).run s = (.ok n, s) := by
  have hchecked : JuliaLean.base.checked.checkedMulBits (int 1) n = .ok n := by
    apply concat_checked_mul_fits
    change n.val = 1 * n.val
    omega
  simp only [checkedDimensionsModel, List.forIn_cons, List.forIn_nil, checkedMultiplyMutation,
    hchecked, shape_run_bind, shape_run_pure]

/-- Two-dimensional construction separates validation and arbitrary positive chunk initialization. -/
theorem concat_construct_pair_general {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (rows cols n : I64) (count : Nat) (s allocated initialized : State) (handle : Nat)
    (hr : ¬ rows.val < 0) (hc : ¬ cols.val < 0)
    (hchecked : (checked [rows, cols]).run s = (.ok n, s))
    (hcount : numBitChunks n = int count) (hp : 0 < count) (hn : count ≤ 9223372036854775807)
    (hallocate : (allocate count).run s = (.ok handle, allocated))
    (hwrite : (mutableSet handle (u64 0) (int count)).run allocated = (.ok (), initialized)) :
    (BitArrayUndef (N := N) checked allocate [rows, cols]).run s =
      (.ok ⟨handle, n, [rows, cols]⟩, initialized) := by
  have hnat : (int count).val.toNat = count := by rw [packedInt_val count hn, Int.toNat_natCast]
  have hpos : (int count).val > 0 := by rw [packedInt_val count hn]; omega
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hr, hc, ite_false,
    shape_run_bind, shape_run_pure, hchecked, hcount, hnat, hallocate, hpos, ite_true, hwrite]

/-- Every representable two-based native range enumerates the zero-based tail indices in order. -/
theorem concat_intRange_two (n : Nat) (hn : n ≤ 9223372036854775807) :
    intRange (int 2) (int n) = (List.range (n - 1)).map (fun j => int ((j + 2 : Nat) : Int)) := by
  unfold intRange
  rw [packedInt_val n hn]
  have hlen : (((n : Int) - (int 2).val + 1).toNat) = n - 1 := by
    change (((n : Int) - 2 + 1).toNat) = n - 1
    omega
  rw [hlen]
  apply List.map_congr_left
  intro j _
  apply Subtype.ext
  change wrapInt .i64 (2 + (j : Int)) = wrapInt .i64 ((j + 2 : Nat) : Int)
  congr 1
  omega

/-- A failed first phase immediately propagates through an arbitrary monadic continuation. -/
theorem concat_bind_first_error {α β : Type} (action : BitMutationM α)
    (continuation : α → BitMutationM β) (s finished : State) (error : JuliaLean.base.array.Error)
    (herror : action.run s = (.error error, finished)) :
    (action >>= continuation).run s = (.error error, finished) := by
  simp only [shape_run_bind, herror]
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxHeartbeats 1000000

/-- A successful optional list lookup supplies its natural index bound. -/
theorem group8_some_index_bound {α : Type} (xs : List α) (k : Nat) (value : α)
    (h : xs[k]? = some value) : k < xs.length := by
  by_cases hk : k < xs.length
  · exact hk
  · have he : xs[k]? = none := List.getElem?_eq_none (by omega)
    rw [he] at h
    cases h

/-- Reading an assigned visible element of any valid vector returns it unchanged. -/
theorem group8_mutableGet_of_contents {α : Type} (s : MutableMemory α)
    (handle k : Nat) (value : α)
    (hv : s.validVector handle)
    (hget : (s.contents handle)[k]? = some (some value)) :
    (mutableGet handle (int ((k + 1 : Nat) : Int))).run s = (.ok value, s) := by
  cases ha : s.arrays[handle]? with
  | none =>
    simp only [MutableMemory.validVector, ha] at hv
  | some a =>
    cases hm : s.memories[a.reference.1]? with
    | none =>
      simp only [MutableMemory.validVector, ha, hm] at hv
    | some slots =>
      have hv' : 0 ≤ a.size.val ∧ 1 ≤ a.reference.2.val ∧
          a.reference.2.val - 1 + a.size.val ≤ (slots.length : Int) ∧
          slots.length < 2 ^ 63 := by
        simpa only [MutableMemory.validVector, ha, hm] using hv
      simp only [MutableMemory.contents, ha, hm, Option.getD_some] at hget
      have hk := group8_some_index_bound
        ((slots.drop (a.reference.2.val - 1).toNat).take a.size.val.toNat)
        k (some value) hget
      have hkSize : k < a.size.val.toNat := by
        simp only [List.length_take] at hk
        omega
      have hsizeBounds := a.size.property
      change -9223372036854775808 ≤ a.size.val ∧
        a.size.val ≤ 9223372036854775807 at hsizeBounds
      have hfit : k + 1 ≤ 9223372036854775807 := by omega
      have hindex := packedInt_val (k + 1) hfit
      have hin : 1 ≤ (int ((k + 1 : Nat) : Int)).val ∧
          int ((k + 1 : Nat) : Int) ≤ a.size := by
        change 1 ≤ (int ((k + 1 : Nat) : Int)).val ∧
          (int ((k + 1 : Nat) : Int)).val ≤ a.size.val
        rw [hindex]
        omega
      have hleft :
          (((slots.drop (a.reference.2.val - 1).toNat).take a.size.val.toNat) ++
            (slots.drop (a.reference.2.val - 1).toNat).drop a.size.val.toNat)[k]? =
          ((slots.drop (a.reference.2.val - 1).toNat).take a.size.val.toNat)[k]? :=
        List.getElem?_append_left hk
      rw [List.take_append_drop] at hleft
      have hdrop := hleft.trans hget
      have hslot : slots[(a.reference.2.val - 1).toNat + k]? = some (some value) := by
        simpa only [List.getElem?_drop] using hdrop
      have haddress :
          (a.reference.2.val + (int ((k + 1 : Nat) : Int)).val - 2).toNat =
          (a.reference.2.val - 1).toNat + k := by
        rw [hindex]
        omega
      simp only [mutableGet, shape_run_bind, shape_vector_run, ha, hin,
        and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
        memoryRead, shape_run_get, hm, shape_run_pure, haddress, hslot]
end JuliaLean.ChatGPT.Batch4.Group8
end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

/-- A readable visible slot supplies a concrete word. -/
theorem iteration_assigned_word {α : Type} (cells : List (Option α)) (k : Nat)
    (hk : k < cells.length) (ha : ∀ cell ∈ cells, cell.isSome = true) :
    ∃ word, cells[k]? = some (some word) := by
  cases he : cells[k]? with
  | none =>
    rw [List.getElem?_eq_getElem hk] at he
    cases he
  | some cell =>
    have hv := ha cell (List.mem_of_getElem? he)
    cases cell with
    | none => cases hv
    | some word => exact ⟨word, rfl⟩
end JuliaLean.ChatGPT.Batch4.Group8
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Nonnegative dimension validation always terminates without touching memory. -/
theorem ctor_validate (dims : List I64) (index : I64) (s : State)
    (h : ∀ d ∈ dims, int 0 ≤ d) :
    ∃ last,
      (forIn dims index (fun (d i : I64) => do
        if d.val < 0 then
          throw (Error.argument s!"dimension size must be ≥ 0, got {d.val} for dimension {i.val}")
        pure (ForInStep.yield (i + int 1))) : BitMutationM I64).run s = (.ok last, s) := by
  induction dims generalizing index with
  | nil => exact ⟨index, rfl⟩
  | cons dim dims ih =>
    have hdim : ¬ dim.val < 0 := by
      have hd := h dim List.mem_cons_self
      change 0 ≤ dim.val at hd
      omega
    obtain ⟨last, hlast⟩ := ih (index + int 1)
      (fun d hd => h d (List.mem_cons_of_mem dim hd))
    refine ⟨last, ?_⟩
    simp only [List.forIn_cons, hdim, ite_false]
    exact hlast

/-- Validated construction with a positive chunk count performs its final write. -/
theorem ctor_undef_positive {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (dims : List I64) (len : I64) (handle : Nat) (s allocated out : State)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hc : (checked dims).run s = (.ok len, s))
    (ha : (allocate (numBitChunks len).val.toNat).run s = (.ok handle, allocated))
    (hp : 0 < (numBitChunks len).val)
    (hw : (mutableSet handle (u64 0) (numBitChunks len)).run allocated = (.ok (), out)) :
    (BitArrayUndef (N := N) checked allocate dims).run s =
      (.ok ⟨handle, len, dims⟩, out) := by
  obtain ⟨last, hlast⟩ := ctor_validate dims (int 1) s hdims
  simp only [BitArrayUndef, shape_run_bind, hlast, hc, ha, hp, ite_true,
    hw, shape_run_pure]

/-- A nonpositive signed chunk count converts to zero slots and skips the write. -/
theorem ctor_undef_nonpositive {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (dims : List I64) (len : I64) (handle : Nat) (s out : State)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hc : (checked dims).run s = (.ok len, s))
    (ha : (allocate (numBitChunks len).val.toNat).run s = (.ok handle, out))
    (hp : ¬ 0 < (numBitChunks len).val) :
    (BitArrayUndef (N := N) checked allocate dims).run s =
      (.ok ⟨handle, len, dims⟩, out) := by
  obtain ⟨last, hlast⟩ := ctor_validate dims (int 1) s hdims
  simp only [BitArrayUndef, shape_run_bind, hlast, hc, ha, hp, ite_false,
    shape_run_pure]

/-- The original chunk-fill callback composes a length query with its write loop. -/
theorem ctor_fill_chunks_from (chunks : Nat) (word : U64) (count : I64) (s out : State)
    (hl : (mutableLength chunks).run s = (.ok count, s))
    (hloop : (forIn (intRange (int 1) count) PUnit.unit (fun i _ => do
      mutableSet chunks word i
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, out)) :
    (fillVectorChunks chunks word).run s = (.ok (), out) := by
  simp only [fillVectorChunks, shape_run_bind, hl, hloop, shape_run_pure]

/-- The original callback initializes arbitrary fresh storage, including unread slots. -/
theorem ctor_fill_fresh (s : State) (slots : List (Option U64)) (word : U64)
    (hn : slots.length ≤ 9223372036854775807) :
    (fillVectorChunks s.arrays.length word).run (shiftFreshHeap s slots) =
      (.ok (), shiftFreshHeap s (List.replicate slots.length (some word))) := by
  apply ctor_fill_chunks_from _ _ (int slots.length) _ _ (shiftFreshLength s slots)
  rw [packedObserve_intRange slots.length hn, List.forIn_map]
  have h := shiftFreshWriteLoop s (List.range slots.length) slots (fun _ => word) hn
    (by intro i hi; exact List.mem_range.mp hi)
  rw [shiftFreshFoldConstant] at h
  exact h

/-- A supplied positive native product determines the complete fresh constructor state. -/
theorem ctor_native_undef_positive {N : Nat} (dims : List I64) (n : Nat) (s : State)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hproduct : dims.foldl (· * ·) (int 1) = int n)
    (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    (BitArrayUndef (N := N)
      (fun ds => pure (ds.foldl (· * ·) (int 1))) allocateChunkVectorModel dims).run s =
      (.ok ⟨s.arrays.length, int n, dims⟩, shiftFreshHeap s (shiftFreshInitial n)) := by
  let count := wordCount n
  have hc : count ≤ 576460752303423488 := by dsimp only [count]; unfold wordCount; omega
  have hcpos : 0 < count := by dsimp only [count]; unfold wordCount; omega
  have hcount := shiftFreshNumChunks n hn
  have hnat : (numBitChunks (int n)).val.toNat = count := by
    rw [hcount, packedInt_val (wordCount n) (by omega), Int.toNat_natCast]
  have hchecked : ((pure (dims.foldl (· * ·) (int 1))) : BitMutationM I64).run s =
      (.ok (int n), s) := by rw [hproduct]; rfl
  have ha := shiftFreshAllocate s count hc
  have hw := shiftFreshSet s (List.replicate count none) (count - 1) (u64 0)
    (by rw [List.length_replicate]; omega) (by rw [List.length_replicate]; omega)
  rw [show count - 1 + 1 = count by omega] at hw
  apply ctor_undef_positive _ _ dims (int n) s.arrays.length s _ _ hdims hchecked
  · rw [hnat]
    exact ha
  · rw [hcount, packedInt_val (wordCount n) (by omega)]
    omega
  · rw [hcount]
    exact hw

/-- Zero-volume validated construction creates an empty fresh chunk vector. -/
theorem ctor_native_undef_zero {N : Nat} (dims : List I64) (s : State)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hproduct : dims.foldl (· * ·) (int 1) = int 0) :
    (BitArrayUndef (N := N)
      (fun ds => pure (ds.foldl (· * ·) (int 1))) allocateChunkVectorModel dims).run s =
      (.ok ⟨s.arrays.length, int 0, dims⟩, shiftFreshHeap s []) := by
  apply ctor_undef_nonpositive _ _ dims (int 0) s.arrays.length s _ hdims
  · rw [hproduct]
    rfl
  · exact metadataAllocateZero s
  · decide

/-- False fill has its documented logical encoding for every positive native length. -/
theorem ctor_fill_false_positive {N : Nat} (s : State) (n : Nat) (dims : List I64)
    (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    (fillBitArray (fun b => pure b) fillVectorChunks
      (⟨s.arrays.length, int n, dims⟩ : BitArray N) false).run
      (shiftFreshHeap s (shiftFreshInitial n)) =
      (.ok ⟨s.arrays.length, int n, dims⟩,
        shiftFreshHeap s ((encodeBits (List.replicate n false)).map some)) := by
  have hc : (shiftFreshInitial n).length ≤ 9223372036854775807 := by
    rw [shiftFreshInitialLength]
    unfold wordCount
    omega
  have hf := ctor_fill_fresh s (shiftFreshInitial n) (u64 0) hc
  rw [shiftFreshInitialLength, shiftFreshZeroSlots] at hf
  exact fillFalseFrom (fun b => pure b) fillVectorChunks
    (⟨s.arrays.length, int n, dims⟩ : BitArray N) false _ _ rfl
    (fillPositiveLength n hp hn) hf

/-- Fresh storage containing an encoding decodes to all of its original values. -/
theorem ctor_fresh_bits {N : Nat} (s : State) (xs : List Bool) (dims : List I64)
    (hn : xs.length ≤ 9223372036854775807) :
    bitValues (shiftFreshHeap s ((encodeBits xs).map some))
      (⟨s.arrays.length, int xs.length, dims⟩ : BitArray N) = xs := by
  exact scalar_bitValues_contents _ _ xs hn rfl
    (shiftFreshContents s ((encodeBits xs).map some)
      (by rw [List.length_map]; exact packedEncoded_lengthBound xs hn))
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A zero-based native range enumerates exactly its representable positions. -/
theorem abs_intRange_zero (n : Nat) (hn : n ≤ 64) :
    intRange (int 0) (int n - int 1) = (List.range n).map (fun j : Nat => int (j : Int)) := by
  rw [concat_int_sub]
  have hv : (int ((n : Int) - 1)).val = (n : Int) - 1 := by
    change wrapInt .i64 ((n : Int) - 1) = (n : Int) - 1
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ (n : Int) - 1 ∧
      (n : Int) - 1 ≤ 9223372036854775807
    omega
  unfold intRange
  rw [hv]
  have hcount : (((n : Int) - 1 - (int 0).val + 1).toNat) = n := by
    change (((n : Int) - 1 - 0 + 1).toNat) = n
    omega
  rw [hcount]
  apply List.map_congr_left
  intro j _
  change JInt.wrap .i64 (0 + (j : Int)) = JInt.wrap .i64 (j : Int)
  rw [Int.zero_add]

/-- The false source value contributes no set bit to the word accumulator. -/
theorem abs_shift_zero (n : Nat) (hn : n ≤ 64) :
    shl_int (u64 0) (int n) = u64 0 := by
  apply packedBit_ext
  intro bit hb
  rw [concat_shl_bit _ _ _ hn hb, packedBit_zero]
  simp only [packedBit_zero, ite_self]

/-- Packing one source bit advances the independent prefix encoding. -/
theorem abs_prefix_step (xs : List Bool) (chunk bit : Nat) (hb : bit < 64) :
    or_int (packedPrefix xs chunk bit)
      (shl_int (u64 (if xs.getD (chunk * 64 + bit) false then 1 else 0)) (int bit)) =
      packedPrefix xs chunk (bit + 1) := by
  simp only [packedPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  cases h : xs.getD (chunk * 64 + bit) false with
  | false =>
      simp only [h, Bool.false_eq_true, ite_false, abs_shift_zero bit (by omega), dequePackedOrZero]
  | true => simp only [h, ite_true]

/-- The register update in the abstract-array word-packing loop. -/
def abs_pack_step (xs : List Bool) (j : I64) (current : I64 × U64) :
    BitMutationM (ForInStep (I64 × U64)) := do
  let bit ← pure (xs.getD (current.1.val.toNat - 1) false)
  pure (.yield (current.1 + int 1,
    or_int current.2 (shl_int (u64 (if bit then 1 else 0)) j)))

/-- Each packing iteration reads exactly its next source element and preserves the heap. -/
theorem abs_pack_step_run (xs : List Bool) (chunk bit : Nat) (s : State)
    (hb : bit < 64) (hn : chunk * 64 + bit + 1 ≤ 9223372036854775807) :
    (abs_pack_step xs (int bit)
      (int ((chunk * 64 + bit + 1 : Nat) : Int), packedPrefix xs chunk bit)).run s =
      (.ok (.yield (int ((chunk * 64 + (bit + 1) + 1 : Nat) : Int),
        packedPrefix xs chunk (bit + 1))), s) := by
  have hindex : (int ((chunk * 64 + bit + 1 : Nat) : Int)).val.toNat - 1 =
      chunk * 64 + bit := by
    rw [packedInt_val _ hn, Int.toNat_natCast]
    omega
  have hnext : int ((chunk * 64 + bit + 1 : Nat) : Int) + int 1 =
      int ((chunk * 64 + (bit + 1) + 1 : Nat) : Int) := by
    rw [packedInt_add]
    congr 1
  simp only [abs_pack_step, shape_run_bind, shape_run_pure, hindex, hnext,
    abs_prefix_step xs chunk bit hb]

/-- An entire word-packing loop returns the exact independent encoded prefix. -/
theorem abs_pack_loop_run (xs : List Bool) (chunk count : Nat) (s : State)
    (hc : count ≤ 64) (hn : chunk * 64 + count ≤ 9223372036854775807) :
    (forIn (intRange (int 0) (int count - int 1))
      (int ((chunk * 64 + 1 : Nat) : Int), u64 0) (abs_pack_step xs)).run s =
      (.ok (int ((chunk * 64 + count + 1 : Nat) : Int),
        packedPrefix xs chunk count), s) := by
  rw [abs_intRange_zero count hc, List.forIn_map]
  have h := concat_range_loop 0 count count
    (fun bit => (int ((chunk * 64 + bit + 1 : Nat) : Int), packedPrefix xs chunk bit))
    (fun _ => s) (fun bit current => abs_pack_step xs (int bit) current)
    (by
      intro bit hb
      exact abs_pack_step_run xs chunk bit s (by omega) (by omega)) (by omega)
  have hz : packedPrefix xs chunk 0 = u64 0 := rfl
  simpa only [← List.range_eq_range', Nat.zero_add, Nat.add_zero, hz] using h

def abs_tail_count (n : Nat) : Nat := (n - 1) % 64 + 1

theorem abs_tail_counts (n : Nat) (hp : 0 < n) :
    0 < abs_tail_count n ∧ abs_tail_count n ≤ 64 ∧
      (wordCount n - 1) * 64 + abs_tail_count n = n := by
  unfold abs_tail_count wordCount
  omega

/-- The native tail counter is the positive natural remainder used by the specification. -/
theorem abs_tail_native (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    mod64 (int n - int 1) + int 1 = int (abs_tail_count n) := by
  have hs : int n - int 1 = int ((n - 1 : Nat) : Int) := by
    rw [concat_int_sub]
    apply congrArg int
    omega
  have hm : mod64 (int ((n - 1 : Nat) : Int)) = int (((n - 1) % 64 : Nat) : Int) := by
    apply Subtype.ext
    rw [scalar_mod64_val, packedInt_val (n - 1) (by omega),
      packedInt_val ((n - 1) % 64) (by omega)]
    omega
  rw [hs, hm, packedInt_add]
  unfold abs_tail_count
  rfl
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Population count restricted to an initial interval of bit positions. -/
def scan_popBits (n width : Nat) : Nat :=
  (List.range width).countP (fun i => n.testBit i)

/-- Splitting off the low bit exposes the population count of the quotient. -/
theorem scan_popBits_succ (n width : Nat) :
    scan_popBits n (width + 1) = (if n % 2 = 1 then 1 else 0) + scan_popBits (n / 2) width := by
  unfold scan_popBits
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  simp only [Function.comp_def, Nat.testBit_succ]
  have hb : n.testBit 0 = decide (n % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [Nat.pow_zero, Nat.div_one]
  rw [hb]
  by_cases h : n % 2 = 1 <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  · omega
  · omega

/-- Clearing the low set bit always clears the result's least significant bit. -/
theorem scan_clearLow_mod_two (n : Nat) : (n &&& (n - 1)) % 2 = 0 := by
  have hmod := Nat.mod_lt (n &&& (n - 1)) (by decide : 0 < 2)
  have hnot : ¬ (n &&& (n - 1)) % 2 = 1 := by
    rw [Nat.and_mod_two_eq_one]
    omega
  omega

/-- A nonzero bounded natural loses exactly one set bit after `n & (n-1)`. -/
theorem scan_popBits_clearLow (width n : Nat) (hp : 0 < n) (hn : n < 2 ^ width) :
    scan_popBits (n &&& (n - 1)) width + 1 = scan_popBits n width := by
  induction width generalizing n with
  | zero => simp only [Nat.pow_zero] at hn; omega
  | succ width ih =>
    rw [scan_popBits_succ, scan_popBits_succ, scan_clearLow_mod_two]
    simp only [Nat.zero_ne_one, ite_false, Nat.zero_add]
    rw [Nat.and_div_two]
    by_cases hb : n % 2 = 1
    · have hquot : (n - 1) / 2 = n / 2 := by omega
      rw [if_pos hb, hquot, Nat.and_self]
      omega
    · have heven : n % 2 = 0 := by omega
      have hquot : (n - 1) / 2 = n / 2 - 1 := by omega
      have hp' : 0 < n / 2 := by omega
      have hn' : n / 2 < 2 ^ width := by
        rw [Nat.pow_succ] at hn
        omega
      rw [if_neg hb, Nat.zero_add, hquot]
      exact ih (n / 2) hp' hn'

/-- The modeled bit-clear primitive has its natural unsigned value on nonzero words. -/
theorem scan_blsr_value (word : U64) (hw : word ≠ u64 0) :
    (blsr word).val.toNat = word.val.toNat &&& (word.val.toNat - 1) := by
  have hb := word.property
  change 0 ≤ word.val ∧ word.val ≤ 18446744073709551615 at hb
  have hp : 0 < word.val := by
    have hn : word.val ≠ 0 := by
      intro h
      apply hw
      exact Subtype.ext h
    omega
  have hs : (sub_int word (u64 1)).val = word.val - 1 := by
    rw [JuliaLean.Proofs.base.int.sub_int_val]
    change wrapInt .u64 (word.val - 1) = word.val - 1
    apply wrapInt_of_inRange
    change 0 ≤ word.val - 1 ∧ word.val - 1 ≤ 18446744073709551615
    omega
  unfold blsr and_int JuliaLean.C.jlAndInt
  rw [packedToJInt_val, Int.toNat_natCast, BitVec.toNat_and,
    packedFromJInt_nat, packedFromJInt_nat, hs]
  have hsub : (word.val - 1).toNat = word.val.toNat - 1 := by omega
  rw [hsub]

/-- Each nonzero word-scan step consumes exactly one of its remaining output entries. -/
theorem scan_blsr_population (word : U64) (hw : word ≠ u64 0) :
    popcountWord (blsr word) + 1 = popcountWord word := by
  have hb := word.property
  change 0 ≤ word.val ∧ word.val ≤ 18446744073709551615 at hb
  have hp : 0 < word.val.toNat := by
    have hn : word.val ≠ 0 := by
      intro h
      apply hw
      exact Subtype.ext h
    omega
  have hn : word.val.toNat < 2 ^ 64 := by
    change word.val.toNat < 18446744073709551616
    omega
  change scan_popBits (blsr word).val.toNat 64 + 1 = scan_popBits word.val.toNat 64
  rw [scan_blsr_value word hw]
  exact scan_popBits_clearLow 64 word.val.toNat hp hn
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The exact frozen mask action, named so observation transport keeps its body closed. -/
@[irreducible] def copy_delete_mask_action (xs mask : List Bool) : BitMutationM BitVector :=
  let B := vectorBits xs
  let indices := (List.range mask.length).filter fun i => mask.getD i false
  let first : List Bool → BitMutationM (Option I64) := fun _ => pure (indices.head?.map fun i => int (Int.ofNat (i+1)))
  let next : List Bool → I64 → BitMutationM (Option I64) := fun _ start =>
    pure (((indices.filter fun i => int (Int.ofNat (i+1)) ≥ start).head?).map fun i => int (Int.ofNat (i+1)))
  let check : BitVector → I64 → BitMutationM Unit := fun _ i =>
    if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then pure () else throw .bounds
  bitVectorDeleteAtBoolMask (fun _ => int mask.length) first next check B mask
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def mhcat_size (B : BitMatrix) (dimension : I64) : I64 :=
  B.dims.getD (dimension.val.toNat - 1) (int 0)

@[irreducible] def mhcat_pair (rows columnsLeft columnsRight lengthLeft lengthRight : I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix :=
  bitArrayHcatArrays
    [(⟨0, lengthLeft, [rows, columnsLeft]⟩ : BitMatrix),
     (⟨1, lengthRight, [rows, columnsRight]⟩ : BitMatrix)]
    mhcat_size (fun _ => int 2) allocate

def mhcat_pair_body (rows columns lengthLeft lengthRight : I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix := do
  let out ← allocate rows columns
  copyChunks out.chunks (int 1) 0 (int 1) lengthLeft
  copyChunks out.chunks (int 1 + lengthLeft) 1 (int 1) lengthRight
  pure out

theorem mhcat_zero_add (value : I64) : int 0 + value = value := by
  apply Subtype.ext
  change wrapInt .i64 (0 + value.val) = value.val
  rw [Int.zero_add]
  exact JuliaLean.Proofs.base.int.wrapInt_val value

/-- The two-matrix shape pass checks equal rows and sums their columns. -/
theorem mhcat_pair_factor (rows columnsLeft columnsRight lengthLeft lengthRight : I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) :
    mhcat_pair rows columnsLeft columnsRight lengthLeft lengthRight allocate =
      mhcat_pair_body rows (columnsLeft + columnsRight) lengthLeft lengthRight allocate := by
  have hrange : intRange (int 1) (int 2) = [int 1, int 2] := by decide
  have hcount : int ((0 + 1 + 1 : Nat) : Int) = int 2 := rfl
  have hfirst : (int 1).val.toNat - 1 = 0 := rfl
  have hsecond : (int 2).val.toNat - 1 = 1 := rfl
  unfold mhcat_pair bitArrayHcatArrays mhcat_pair_body
  simp only [List.length_cons, List.length_nil, hcount, hrange, hfirst, hsecond,
    List.getD_cons_zero, List.getD_cons_succ, List.forIn_cons, List.forIn_nil,
    pure_bind, mhcat_size, mhcat_zero_add, beq_self_eq_true, ite_true, bne_self_eq_false,
    Bool.false_eq_true, ite_false, bind_assoc]

/-- The frozen hcat control flow composes allocation and both source copies. -/
theorem mhcat_pair_from_runs (rows columnsLeft columnsRight lengthLeft lengthRight : I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) (out : BitMatrix)
    (s allocated middle finished : State)
    (ha : (allocate rows (columnsLeft + columnsRight)).run s = (.ok out, allocated))
    (hl : (copyChunks out.chunks (int 1) 0 (int 1) lengthLeft).run allocated = (.ok (), middle))
    (hr : (copyChunks out.chunks (int 1 + lengthLeft) 1 (int 1) lengthRight).run middle =
      (.ok (), finished)) :
    (mhcat_pair rows columnsLeft columnsRight lengthLeft lengthRight allocate).run s =
      (.ok out, finished) := by
  rw [mhcat_pair_factor]
  simp only [mhcat_pair_body, shape_run_bind, ha, hl, hr, shape_run_pure]

def mhcat_observation (rows : Nat) (left right : List Bool)
    (result : Except Error BitMatrix × State) : Prop :=
  match result with
  | (.ok output, state) =>
      output.dims = [int rows, int ((left.length + right.length) / rows)] ∧
        bitValues state output = left ++ right
  | (.error _, _) => False

theorem mhcat_observe_from (rows : Nat) (left right : List Bool)
    (program : BitMutationM BitMatrix) (s state : State) (output : BitMatrix)
    (hrun : program.run s = (.ok output, state))
    (hdims : output.dims = [int rows, int ((left.length + right.length) / rows)])
    (hbits : bitValues state output = left ++ right) :
    mhcat_observation rows left right (program.run s) := by
  rw [hrun]
  exact ⟨hdims, hbits⟩
end JuliaLean.ChatGPT.Batch5.Group2
end

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

abbrev scan_maskDelete_Registers := I64 × Option I64 × I64 × I64 × I64

/-- The suffix copy and final chunk-length/padding cleanup after mask compaction. -/
def scan_maskDelete_finish (B : BitVector) (registers : scan_maskDelete_Registers) :
    BitMutationM BitVector := do
  let newL := registers.1
  let p := registers.2.2.1
  let q := registers.2.2.2.2
  if q ≤ B.len then copyChunks B.chunks p B.chunks q (B.len - q + int 1)
  let old ← mutableLength B.chunks
  rangeSingleFinish B newL old

/-- The logical retained suffix described by the ascending deletion positions. -/
def scan_maskDelete_blocks (xs : List Bool) : List Nat → Nat → List Bool
  | [], start => xs.drop start
  | i :: rest, start => (xs.drop start).take (i - start) ++ scan_maskDelete_blocks xs rest (i + 1)

def scan_maskDelete_prefix (word : U64) (kept : List Bool) : Prop :=
  ∀ i, i < kept.length → packedBit word i = kept.getD i false

def scan_maskDelete_suffix (word : U64) (xs : List Bool) (start : Nat) : Prop :=
  ∀ i, start ≤ i → i < xs.length → packedBit word i = xs.getD i false

/-- Before the first deletion, the already-retained prefix is the original prefix. -/
theorem scan_maskDelete_initial_prefix (xs : List Bool) (i : Nat)
    (hn : xs.length ≤ 64) (hi : i ≤ xs.length) :
    scan_maskDelete_prefix (packedPrefix xs 0 64) (xs.take i) := by
  intro j hj
  have hlen : (xs.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left hi]
  have hji : j < i := by rw [hlen] at hj; exact hj
  rw [packedWord_bit xs 0 j (by omega)]
  simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
    List.getElem?_take, hji, ite_true]

/-- Every still-unread single-word source bit initially has its original value. -/
theorem scan_maskDelete_initial_suffix (xs : List Bool) (start : Nat)
    (hn : xs.length ≤ 64) :
    scan_maskDelete_suffix (packedPrefix xs 0 64) xs start := by
  intro j _ hj
  simpa only [Nat.zero_mul, Nat.zero_add] using packedWord_bit xs 0 j (by omega)

/-- A nonempty single-word logical vector has the concrete heap used by compaction. -/
theorem scan_maskDelete_initial_store (xs : List Bool) (hp : 0 < xs.length)
    (hn : xs.length ≤ 64) :
    dequeWordStore [packedPrefix xs 0 64] 32 = initWords (encodeBits xs) := by
  rw [rangeSingleEncoding xs hp hn]
  exact dequeWordStoreInitial _

/-- A compacted prefix followed by one source slice has explicit indexed values. -/
theorem scan_maskDelete_append_slice_get (xs kept : List Bool) (start count i : Nat)
    (hi : i < kept.length + count) :
    (kept ++ (xs.drop start).take count).getD i false =
      if i < kept.length then kept.getD i false else xs.getD (start + (i - kept.length)) false := by
  by_cases h : i < kept.length
  · simp only [h, ite_true, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have hh : kept.length ≤ i := by omega
    have hc : i - kept.length < count := by omega
    simp only [h, ite_false, List.getD_eq_getElem?_getD,
      List.getElem?_append_right hh, List.getElem?_take, hc, ite_true,
      List.getElem?_drop]

/-- Copying the next retained interval extends the compacted prefix and leaves
every source bit at or beyond the interval end unchanged. -/
theorem scan_maskDelete_copy_invariant (xs kept : List Bool) (word : U64)
    (start finish : Nat) (hn : xs.length ≤ 64) (hk : kept.length ≤ start)
    (hs : start ≤ finish) (hf : finish ≤ xs.length)
    (hprefix : scan_maskDelete_prefix word kept)
    (hsuffix : scan_maskDelete_suffix word xs start) :
    scan_maskDelete_prefix
      (rangeSingleCopyWord word kept.length start (finish - start))
      (kept ++ (xs.drop start).take (finish - start)) ∧
    scan_maskDelete_suffix
      (rangeSingleCopyWord word kept.length start (finish - start)) xs finish := by
  have hlen : (kept ++ (xs.drop start).take (finish - start)).length =
      kept.length + (finish - start) := by
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega)]
  constructor
  · intro i hi
    rw [hlen] at hi
    rw [rangeSingleCopyBit _ _ _ _ i (by omega) (by omega) (by omega),
      scan_maskDelete_append_slice_get xs kept start (finish - start) i hi]
    by_cases h : i < kept.length
    · rw [if_neg (by omega), if_pos h]
      exact hprefix i h
    · rw [if_pos (by omega), if_neg h]
      have hr := hsuffix (i - kept.length + start) (by omega) (by omega)
      simpa only [Nat.add_comm] using hr
  · intro i hi hib
    rw [rangeSingleCopyBit _ _ _ _ i (by omega) (by omega) (by omega), if_neg (by omega)]
    exact hsuffix i (by omega) hib

/-- A complete logical prefix becomes its canonical packed word after end masking. -/
theorem scan_maskDelete_mask_word (kept : List Bool) (word : U64)
    (hp : 0 < kept.length) (hn : kept.length ≤ 64)
    (hprefix : scan_maskDelete_prefix word kept) :
    and_int word (maskEnd (int kept.length)) = packedPrefix kept 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [dequePackedAnd, rangeSingleEndMaskBit kept.length bit hp hn hb,
    packedWord_bit kept 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  by_cases hi : bit < kept.length
  · rw [decide_eq_true hi, Bool.and_true]
    exact hprefix bit hi
  · rw [decide_eq_false hi, Bool.and_false, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none]

/-- Cleanup exposes the exact retained sequence, including the empty-result case. -/
theorem scan_maskDelete_cleanup (B : BitVector) (kept : List Bool) (word : U64)
    (spare : Nat) (hb : B.chunks = 0) (hn : kept.length ≤ 64)
    (hpref : scan_maskDelete_prefix word kept) :
    ∃ outState : State,
      (rangeSingleFinish B (int kept.length) (int 1)).run (dequeWordStore [word] spare) =
        (.ok {B with len := int kept.length}, outState) ∧
      bitValues outState ({B with len := int kept.length} : BitVector) = kept := by
  by_cases hz : kept = []
  · subst kept
    let out := dequeTailStore [] (some word :: List.replicate spare none)
    refine ⟨out, ?_, rfl⟩
    apply rangeSingleFinishEmpty
    rw [hb]
    exact dequeWordDeleteLast [] word spare (by decide)
  · have hp : 0 < kept.length := List.length_pos_iff.mpr hz
    let out := dequeWordStore [packedPrefix kept 0 64] spare
    have hm := scan_maskDelete_mask_word kept word hp hn hpref
    have hlen : (mutableLength B.chunks).run (dequeWordStore [word] spare) =
        (.ok (int 1), dequeWordStore [word] spare) := by
      rw [hb]
      exact dequeWordLength [word] spare
    have hread : (mutableGet B.chunks (int 1)).run (dequeWordStore [word] spare) =
        (.ok word, dequeWordStore [word] spare) := by
      rw [hb]
      simpa only [List.getD_cons_zero, Nat.zero_add, Int.ofNat_one] using
        dequeWordRead [word] spare 0 (by simp only [List.length_singleton]; decide)
          (by simp only [List.length_singleton]; decide)
    have hwrite : (mutableSet B.chunks (and_int word (maskEnd (int kept.length))) (int 1)).run
        (dequeWordStore [word] spare) = (.ok (), out) := by
      rw [hb]
      have h := dequeWordSet [word] spare 0 (and_int word (maskEnd (int kept.length)))
        (by simp only [List.length_singleton]; decide) (by simp only [List.length_singleton]; decide)
      simpa only [List.set_cons_zero, Nat.zero_add, Int.ofNat_one, hm] using h
    refine ⟨out, rangeSingleFinishPositive B kept.length word _ out hp hn hlen hread hwrite, ?_⟩
    have hc : out.contents B.chunks = (encodeBits kept).map some := by
      rw [hb, rangeSingleEncoding kept hp hn]
      exact dequeWordContents [packedPrefix kept 0 64] spare (by simp only [List.length_singleton]; decide)
    exact scalar_bitValues_contents (N := 1) out
      ({B with len := int kept.length} : BitVector) kept (by omega) rfl hc
end JuliaLean.ChatGPT.Batch5.Group2
end

