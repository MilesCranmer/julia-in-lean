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

/-- The final optional source suffix copy is exact within a single word. -/
theorem scan_maskDelete_tail_copy (n kept start spare : Nat) (word : U64)
    (hn : n ≤ 64) (hk : kept ≤ start) (hs : start ≤ n) :
    ((if int ((start + 1 : Nat) : Int) ≤ int n then
        copyChunks 0 (int ((kept + 1 : Nat) : Int)) 0 (int ((start + 1 : Nat) : Int))
          (int n - int ((start + 1 : Nat) : Int) + int 1)
      else pure ()) : BitMutationM Unit).run (dequeWordStore [word] spare) =
      (.ok (), dequeWordStore [rangeSingleCopyWord word kept start (n - start)] spare) := by
  have hcount : int n - int ((start + 1 : Nat) : Int) + int 1 = int ((n - start : Nat) : Int) := by
    rw [dequeIntSub, packedInt_add]
    exact congrArg int (by omega)
  have hcond : (int ((start + 1 : Nat) : Int) ≤ int n) ↔ start < n := by
    change (int ((start + 1 : Nat) : Int)).val ≤ (int n).val ↔ _
    rw [packedInt_val (start + 1) (by omega), packedInt_val n (by omega)]
    omega
  by_cases hp : start < n
  · rw [if_pos (hcond.mpr hp), hcount]
    exact rangeSingleCopyStore word kept start (n - start) spare (by omega) (by omega)
  · rw [if_neg (fun h => hp (hcond.mp h))]
    have hz : n - start = 0 := by omega
    rw [hz, rangeSingleCopyZero word kept start (by omega) (by omega)]
    rfl

/-- The optional interval move between two selected positions is an exact
one-word source-offset copy, including the empty interval. -/
theorem scan_maskDelete_interval_copy (kept start finish spare : Nat) (word : U64)
    (hk : kept ≤ start) (hs : start ≤ finish) (hf : finish ≤ 64) :
    ((if int ((finish + 1 : Nat) : Int) > int ((start + 1 : Nat) : Int) then
        copyChunks 0 (int ((kept + 1 : Nat) : Int)) 0 (int ((start + 1 : Nat) : Int))
          (int ((finish + 1 : Nat) : Int) - int ((start + 1 : Nat) : Int))
      else pure ()) : BitMutationM Unit).run (dequeWordStore [word] spare) =
      (.ok (), dequeWordStore [rangeSingleCopyWord word kept start (finish - start)] spare) := by
  have hcount : int ((finish + 1 : Nat) : Int) - int ((start + 1 : Nat) : Int) =
      int ((finish - start : Nat) : Int) := by
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hcond : (int ((finish + 1 : Nat) : Int) > int ((start + 1 : Nat) : Int)) ↔ start < finish := by
    change (int ((start + 1 : Nat) : Int)).val < (int ((finish + 1 : Nat) : Int)).val ↔ _
    rw [packedInt_val (start + 1) (by omega), packedInt_val (finish + 1) (by omega)]
    omega
  by_cases hp : start < finish
  · rw [if_pos (hcond.mpr hp), hcount]
    exact rangeSingleCopyStore word kept start (finish - start) spare (by omega) (by omega)
  · rw [if_neg (fun h => hp (hcond.mp h))]
    have hz : finish - start = 0 := by omega
    rw [hz, rangeSingleCopyZero word kept start (by omega) (by omega)]
    rfl

/-- After the final suffix copy, cleanup returns the compacted prefix followed by
the complete surviving source tail, at its exact shortened native length. -/
theorem scan_maskDelete_cleanup_after_tail (xs kept : List Bool) (word : U64)
    (start deleted spare : Nat) (hn : xs.length ≤ 64) (hs : start ≤ xs.length)
    (hbalance : kept.length + deleted = start)
    (hprefix : scan_maskDelete_prefix word kept)
    (hsuffix : scan_maskDelete_suffix word xs start) :
    ∃ outState : State,
      (rangeSingleFinish (vectorBits xs) (int ((xs.length - deleted : Nat) : Int)) (int 1)).run
          (dequeWordStore [rangeSingleCopyWord word kept.length start (xs.length - start)] spare) =
        (.ok {vectorBits xs with len := int ((xs.length - deleted : Nat) : Int)}, outState) ∧
      bitValues outState
        ({vectorBits xs with len := int ((xs.length - deleted : Nat) : Int)} : BitVector) =
        kept ++ xs.drop start := by
  have hk : kept.length ≤ start := by omega
  have he : (xs.drop start).take (xs.length - start) = xs.drop start := by
    rw [← List.length_drop (l := xs) (i := start)]
    exact List.take_length
  have hpref := (scan_maskDelete_copy_invariant xs kept word start xs.length hn hk hs
    (Nat.le_refl _) hprefix hsuffix).1
  rw [he] at hpref
  have hlen : (kept ++ xs.drop start).length = xs.length - deleted := by
    simp only [List.length_append, List.length_drop]
    omega
  obtain ⟨out, hrun, hbits⟩ := scan_maskDelete_cleanup (vectorBits xs)
    (kept ++ xs.drop start) (rangeSingleCopyWord word kept.length start (xs.length - start))
    spare rfl (by rw [hlen]; omega) hpref
  refine ⟨out, ?_, ?_⟩
  · simpa only [hlen] using hrun
  · simpa only [hlen] using hbits

/-- Abstract execution facts compose the optional tail copy and cleanup phase. -/
theorem scan_maskDelete_finish_from (B output : BitVector) (newL p s q : I64)
    (y : Option I64) (old : I64) (state copied final : State)
    (hc : ((if q ≤ B.len then copyChunks B.chunks p B.chunks q (B.len - q + int 1)
      else pure ()) : BitMutationM Unit).run state = (.ok (), copied))
    (hl : (mutableLength B.chunks).run copied = (.ok old, copied))
    (hf : (rangeSingleFinish B newL old).run copied = (.ok output, final)) :
    (scan_maskDelete_finish B (newL, y, p, s, q)).run state = (.ok output, final) := by
  unfold scan_maskDelete_finish
  have ht := concat_bind_success (mutableLength B.chunks) (rangeSingleFinish B newL)
    copied copied final old output hl hf
  by_cases hq : q ≤ B.len
  · simp only [hq, ite_true] at hc ⊢
    exact concat_bind_success _ _ state copied final () output hc ht
  · simp only [hq, ite_false, shape_run_pure] at hc ⊢
    have he : state = copied := congrArg Prod.snd hc
    rw [he]
    exact ht
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/- This fragment follows the shared scan_maskDelete_blocks definition. -/

/-- Pointwise equality on visited inputs preserves a filter-map traversal. -/
theorem ctor_mask_filterMap_congr {A B : Type} (indices : List A) (f g : A → Option B)
    (h : ∀ i ∈ indices, f i = g i) : indices.filterMap f = indices.filterMap g := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hi := h i List.mem_cons_self
    have ht := ih (by intro j hj; exact h j (List.mem_cons_of_mem i hj))
    simp only [List.filterMap_cons, hi, ht]

/-- Mapping a valid index interval recovers the corresponding source slice. -/
theorem ctor_mask_slice_range (xs : List Bool) (start count : Nat)
    (hc : count ≤ xs.length - start) :
    (List.range' start count).map (fun j => xs.getD j false) = (xs.drop start).take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', List.length_take, List.length_drop,
      Nat.min_eq_left hc]
  · intro j hj hj'
    have hjc : j < count := by simpa only [List.length_map, List.length_range'] using hj
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul,
      List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show start + j < xs.length by omega), Option.getD_some]

/-- An interval splits into its retained prefix, one selected position, and its later suffix. -/
theorem ctor_mask_range_split (start i n : Nat) (hs : start ≤ i) (hi : i < n) :
    List.range' start (n - start) =
      List.range' start (i - start) ++ i :: List.range' (i + 1) (n - (i + 1)) := by
  have hlength : n - start = (i - start) + (n - i) := by omega
  rw [hlength, ← List.range'_append_1,
    show start + (i - start) = i by omega,
    show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]

/-- No selected position occurs in the interval strictly preceding its first element. -/
theorem ctor_mask_keep_prefix (xs : List Bool) (start i : Nat) (rest : List Nat)
    (hs : start ≤ i) (horder : ∀ j ∈ rest, i < j) :
    (List.range' start (i - start)).filterMap
      (fun j => if (i :: rest).contains j then none else some (xs.getD j false)) =
      (List.range' start (i - start)).map (fun j => xs.getD j false) := by
  have he := ctor_mask_filterMap_congr (List.range' start (i - start))
    (fun j => if (i :: rest).contains j then none else some (xs.getD j false))
    (fun j => some (xs.getD j false)) (by
      intro j hj
      have hb := List.mem_range'_1.mp hj
      have hnot : j ∉ i :: rest := by
        intro hm
        rcases List.mem_cons.mp hm with hsame | hrest
        · omega
        · have hh := horder j hrest
          omega
      have hfalse : (i :: rest).contains j = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact hnot (List.contains_iff_mem.mp htrue)
      simp only [hfalse, Bool.false_eq_true, ite_false])
  simpa only [List.filterMap_eq_map'] using he

/-- The selected head cannot occur in any index interval beginning after it. -/
theorem ctor_mask_keep_tail (xs : List Bool) (i count : Nat) (rest : List Nat) :
    (List.range' (i + 1) count).filterMap
      (fun j => if (i :: rest).contains j then none else some (xs.getD j false)) =
      (List.range' (i + 1) count).filterMap
        (fun j => if rest.contains j then none else some (xs.getD j false)) := by
  apply ctor_mask_filterMap_congr
  intro j hj
  have hb := (List.mem_range'_1.mp hj).1
  have hne : (j == i) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp only [List.contains_cons, hne, Bool.false_or]

/-- Ascending deletion blocks equal stable filtering of the original index suffix. -/
theorem ctor_mask_blocks_suffix (xs : List Bool) (selected : List Nat) (start : Nat)
    (hordered : selected.Pairwise (· < ·)) (hstart : start ≤ xs.length)
    (hvalid : ∀ i ∈ selected, start ≤ i ∧ i < xs.length) :
    scan_maskDelete_blocks xs selected start =
      (List.range' start (xs.length - start)).filterMap
        (fun j => if selected.contains j then none else some (xs.getD j false)) := by
  induction selected generalizing start with
  | nil =>
    simp only [scan_maskDelete_blocks, List.contains_nil, Bool.false_eq_true,
      ite_false, List.filterMap_eq_map']
    have h := ctor_mask_slice_range xs start (xs.length - start) (Nat.le_refl _)
    rw [List.take_of_length_le (by rw [List.length_drop]; exact Nat.le_refl _)] at h
    exact h.symm
  | cons i rest ih =>
    have hi := hvalid i List.mem_cons_self
    have hp := List.pairwise_cons.mp hordered
    have hrest : ∀ j ∈ rest, i + 1 ≤ j ∧ j < xs.length := by
      intro j hj
      have ho := hp.1 j hj
      have hv := hvalid j (List.mem_cons_of_mem i hj)
      omega
    have ht := ih (i + 1) hp.2 (by omega) hrest
    rw [scan_maskDelete_blocks, ht,
      ctor_mask_range_split start i xs.length hi.1 hi.2, List.filterMap_append]
    have hskip : (if (i :: rest).contains i then none else some (xs.getD i false)) = none := by
      simp only [List.contains_cons, beq_self_eq_true, Bool.true_or, ite_true]
    rw [List.filterMap_cons_none
      (f := fun j : Nat => if (i :: rest).contains j then none else some (xs.getD j false)) hskip,
      ctor_mask_keep_prefix xs start i rest hi.1 hp.1,
      ctor_mask_keep_tail xs i (xs.length - (i + 1)) rest,
      ctor_mask_slice_range xs start (i - start) (by omega)]

/-- The completed block specification is exactly the frozen index-based retained-value formula. -/
theorem ctor_mask_blocks_filterMap (xs : List Bool) (selected : List Nat)
    (hordered : selected.Pairwise (· < ·)) (hvalid : ∀ i ∈ selected, i < xs.length) :
    scan_maskDelete_blocks xs selected 0 =
      (List.range xs.length).filterMap
        (fun j => if selected.contains j then none else some (xs.getD j false)) := by
  have h := ctor_mask_blocks_suffix xs selected 0 hordered (by omega)
    (by intro i hi; exact ⟨Nat.zero_le _, hvalid i hi⟩)
  simpa only [Nat.sub_zero, ← List.range_eq_range'] using h
end JuliaLean.ChatGPT.Batch5.Group2
end



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- A successful stateful action passes its value and output heap directly on. -/
theorem mtx_run_bind_ok {α β : Type} {action : BitMutationM α}
    {s out : State} {value : α} (h : action.run s = (.ok value, out))
    (next : α → BitMutationM β) :
    (action >>= next).run s = (next value).run out := by
  rw [shape_run_bind, h]

/-- Reading the matrix size tuple has no state effect. -/
theorem mtx_read_dimensions (s : State) (B : BitMatrix) (rows columns : I64)
    (hd : B.dims = [rows, columns]) :
    ((do
      let ds := bitArraySize B
      pure (← liftArray (JuliaLean.base.abstractarray.tupleGet ds (int 1)),
        ← liftArray (JuliaLean.base.abstractarray.tupleGet ds (int 2)))) :
      BitMutationM (I64 × I64)).run s = (.ok (rows, columns), s) := by
  simp only [bitArraySize, hd, JuliaLean.base.abstractarray.tupleGet,
    show (int 1).val = 1 from rfl, show (int 2).val = 2 from rfl]
  rfl

/-- A fold of point writes preserves the slot count. -/
theorem mtx_fillfold_length {α : Type} (indices : List Nat) (slots : List α) (value : α) :
    (indices.foldl (fun ws j => ws.set j value) slots).length = slots.length := by
  induction indices generalizing slots with
  | nil => rfl
  | cons i indices ih => rw [List.foldl_cons, ih, List.length_set]

/-- A point-write fold changes precisely the positions it visits. -/
theorem mtx_fillfold_get {α : Type} (indices : List Nat) (value fallback : α) :
    ∀ (slots : List α), (∀ i ∈ indices, i < slots.length) → ∀ j : Nat,
    (indices.foldl (fun ws i => ws.set i value) slots).getD j fallback =
      if j ∈ indices then value else slots.getD j fallback := by
  induction indices with
  | nil =>
    intro slots _ j
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons i indices ih =>
    intro slots hi j
    have hib := hi i List.mem_cons_self
    have hr := ih (slots.set i value)
      (by intro k hk; rw [List.length_set]; exact hi k (List.mem_cons_of_mem i hk)) j
    rw [List.foldl_cons, hr]
    by_cases hj : j ∈ indices
    · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
    · rw [if_neg hj]
      have hs : (slots.set i value).getD j fallback =
          if i = j then value else slots.getD j fallback := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hib, ite_true]
        by_cases he : i = j <;> simp only [he, ite_true, ite_false, Option.getD_some]
      rw [hs]
      by_cases he : i = j
      · subst j
        rw [if_pos rfl, if_pos List.mem_cons_self]
      · have hnot : ¬ j ∈ i :: indices := by
          intro hmem
          rcases List.mem_cons.mp hmem with hmem | hmem
          · exact he hmem.symm
          · exact hj hmem
        rw [if_neg he, if_neg hnot]
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A successful mutation callback exposes its continuation at the returned heap. -/
theorem spc_run_bind_ok {α β : Type} {action : BitMutationM α}
    {s out : State} {value : α} (h : action.run s = (.ok value, out))
    (next : α → BitMutationM β) :
    (action >>= next).run s = (next value).run out := by
  rw [shape_run_bind, h]

/-- Indexed elements can be enumerated over their natural positions. -/
theorem spc_zipIdx_range {α : Type} (words : List α) (fallback : α) :
    words.zipIdx = (List.range words.length).map (fun i => (words.getD i fallback, i)) := by
  apply List.ext_getElem
  · simp only [List.length_zipIdx, List.length_map, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [List.getElem_eq_getD]

/-- The constructor used in the splice specification produces a fresh exact encoding. -/
theorem spc_makeBitVector_run (s : State) (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    (makeBitVector xs).run s =
      (.ok (⟨s.arrays.length, int xs.length, [int xs.length]⟩ : BitVector),
        shiftFreshHeap s ((encodeBits xs).map some)) := by
  have hcount : wordCount xs.length ≤ 576460752303423488 := by
    unfold wordCount
    omega
  have hlen : (encodeBits xs).length = wordCount xs.length := packedEncoded_length xs
  have hslots : (List.replicate (wordCount xs.length) (none : Option U64)).length =
      (encodeBits xs).length := by rw [List.length_replicate, hlen]
  have hloop := shiftFreshWriteLoop s (List.range (encodeBits xs).length)
    (List.replicate (wordCount xs.length) none) (fun i => (encodeBits xs).getD i (u64 0))
    (by rw [List.length_replicate]; omega)
    (by intro i hi; rw [hslots]; exact List.mem_range.mp hi)
  rw [shiftFreshFoldCopy (encodeBits xs) _ hslots] at hloop
  have hindexed :
      (forIn (encodeBits xs).zipIdx PUnit.unit (fun (pair : U64 × Nat) _ => do
        mutableSet s.arrays.length pair.1 (int (Int.ofNat (pair.2+1)))
        pure (ForInStep.yield PUnit.unit))).run
          (shiftFreshHeap s (List.replicate (wordCount xs.length) none)) =
        (.ok PUnit.unit, shiftFreshHeap s ((encodeBits xs).map some)) := by
    rw [spc_zipIdx_range (encodeBits xs) (u64 0), List.forIn_map]
    simpa only [Int.ofNat_eq_natCast] using hloop
  have ha := shiftFreshAllocate s (wordCount xs.length) hcount
  change (mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat (wordCount xs.length)))).run s = _ at ha
  unfold makeBitVector
  erw [spc_run_bind_ok ha, spc_run_bind_ok hindexed]
  rfl
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

/-- The runtime's shared empty UInt64 memory is an existing empty object. This is
an input representation invariant, independent of the constructor result. -/
def AllocationInput (runtime : AllocationData) (s : MutableMemory U64) : Prop :=
  s.memories[runtime.emptyMemory]? = some []

/-- Mathematical number of Boolean elements, before any machine arithmetic. -/
def DimensionProduct (ds : List I64) : Int := (ds.map (fun d => d.val)).prod

/-- Native tuples have a machine-representable field count. No sign, product or
per-dimension validity is assumed here; those are constructor obligations. -/
def TupleCountFits (N : Nat) : Prop := (N : Int) ≤ IntTy.max .i64

/-- Mathematical classification of accepted dimension tuples. The strict
per-axis bound at ranks at least two records the installed Core dimension
validator's exclusion of typemax(Int), including zero-product shapes. Rank one
is accepted through the complete nonnegative Int domain. This predicate uses
no checkedDims, chunk-count helper, allocation result or supplied correctness law. -/
def AcceptedNativeDimensions {N : Nat} (dims : Dims N) : Prop :=
  (∀ d ∈ dims.val, 0 ≤ d.val) ∧
  (N ≤ 1 ∨ ∀ d ∈ dims.val, d.val < IntTy.max .i64) ∧
  DimensionProduct dims.val ≤ IntTy.max .i64

/-- Allocating an array must leave every pre-existing array header and memory
object untouched, including all aliases represented by those headers. -/
def OldHeapPreserved (before after : MutableMemory U64) : Prop :=
  after.arrays.take before.arrays.length = before.arrays ∧
  after.memories.take before.memories.length = before.memories

/-- An observer preserves absent and uninitialized cells as distinct outcomes;
it cannot turn an invalid read into a Boolean default. -/
def PackedBitValue {N : Nat} (s : MutableMemory U64) (B : BitArray N) (i : Nat) : Option Int :=
  match (s.contents B.chunks)[i / 64]? with
  | some (some word) => some ((word.val / (2 : Int) ^ (i % 64)) % 2)
  | _ => none

/-- Every logical Boolean equals the requested value. -/
def LogicalBitsEqual {N : Nat} (s : MutableMemory U64) (B : BitArray N) (x : Bool) : Prop :=
  ∀ i : Nat, i < B.len.val.toNat → PackedBitValue s B i = some (if x then 1 else 0)

/-- A raw cell observer, retaining both missing memory and unassigned cells. -/
def StoredCell (s : MutableMemory U64) (memory position : Nat) : Option (Option U64) :=
  (s.memories[memory]?).bind (fun slots => slots[position]?)

/-- A mutating copy never allocates, resizes, or retargets array headers. -/
def FixedHeapShape (before after : MutableMemory U64) : Prop :=
  after.arrays = before.arrays ∧ after.memories.length = before.memories.length ∧
  ∀ memory : Nat,
    (after.memories[memory]?).map List.length = (before.memories[memory]?).map List.length

/-- Every cell outside the initial physical destination window is preserved.
The frame is a statement about the actual shared memory, so it covers all
aliases and partial writes before errors without a source-snapshot assumption.
No relationship between logical length and physical chunk count is imposed. -/
def DestinationFrame (before after : MutableMemory U64) (destination : Nat) : Prop :=
  FixedHeapShape before after ∧
  ∀ header : MutableVector, before.arrays[destination]? = some header →
    before.validVector destination →
    ∀ (memory position : Nat),
      (memory ≠ header.reference.1 ∨
        (position : Int) + 1 < header.reference.2.val ∨
        header.reference.2.val + header.size.val ≤ (position : Int) + 1) →
      StoredCell after memory position = StoredCell before memory position

/-- Every occupied chunk contains a readable isbits word. -/
def ReadableChunks (s : MutableMemory U64) (chunks : Nat) : Prop :=
  ∀ cell ∈ s.contents chunks, ∃ word : U64, cell = some word

/-- Ordinary packed-array representation, including a machine-bounded physical
window, enough readable chunks, exact logical storage accounting, and zero
padding. This helper is used only for the stronger documented content contract;
the global copy frame below also covers alias-resized, inconsistent headers. -/
def ConsistentPackedArray {N : Nat} (s : MutableMemory U64) (B : BitArray N) : Prop :=
  0 ≤ B.len.val ∧ s.validVector B.chunks ∧
  (s.contents B.chunks).length = (B.len.val.toNat + 63) / 64 ∧
  ReadableChunks s B.chunks ∧
  ∀ i : Nat, B.len.val.toNat ≤ i → i < 64 * (s.contents B.chunks).length →
    PackedBitValue s B i = some 0

/-- The typed-reference representation invariant. This says which header is
stored at an identity; it imposes no physical chunk validity, readability or
chunk-count invariant and therefore admits stale reshape aliases. -/
def ObjectContains {N : Nat} (state : ObjectState) (reference : Ref N)
    (header : BitArray N) : Prop :=
  state.objects[reference.identity]? = some (⟨N, header⟩ : Sigma BitArray)

/-- Source-visible native metadata. Rank-one size is determined solely by len;
the ignored dims field may remain unset or stale. Other ranks have the declared
number of dimension fields. Physical chunks may have been resized by an alias. -/
def NativeHeaderShape {N : Nat} (header : BitArray N) : Prop :=
  0 ≤ header.len.val ∧ (N = 1 ∨ header.dims.length = N)

/-- Independent mathematical domain of Core.checked_dims for reshape.
Unlike the BitArray constructor, reshape performs no preliminary negative-axis
check. At ranks zero and one Core returns the product even for a negative
single dimension; at higher ranks the native multi-axis checks apply. -/
def ReshapeDimensionsChecked {R : Nat} (dims : Dims R) : Prop :=
  R ≤ 1 ∨ AcceptedNativeDimensions dims

/-- Old mutable BitArray objects retain both identity and all header fields. -/
def OldObjectsPreserved (before after : ObjectState) : Prop :=
  after.objects.take before.objects.length = before.objects

/-- Independent allocation accounting for reshape's temporary zero-shaped
BitArray. Rank zero has one logical element and therefore allocates one zeroed
chunk; positive rank has zero elements and only a fresh chunk-vector header
referencing shared empty memory. In both cases the temporary chunk allocation
survives after the returned object's chunks field is replaced by the old one. -/
def ReshapeTemporaryStorage (runtime : AllocationData) (rank : Nat)
    (before after : MutableMemory U64) : Prop :=
  OldHeapPreserved before after ∧
  after.arrays.length = before.arrays.length + 1 ∧
  ∃ temporary : MutableVector,
    after.arrays[before.arrays.length]? = some temporary ∧
    temporary.reference.2.val = 1 ∧
    temporary.size.val = (if rank = 0 then 1 else 0) ∧
    (if rank = 0 then
      temporary.reference.1 = before.memories.length ∧
      after.memories.length = before.memories.length + 1 ∧
      after.memories[before.memories.length]? = some [some (u64 0)]
     else
      temporary.reference.1 = runtime.emptyMemory ∧
      after.memories = before.memories)

/-- A changed reshape has a fresh object identity, the exact requested native
shape and unchanged logical length, while sharing the source's exact chunk-array
identity. Every old object and memory cell remains intact, including unrelated
aliases and underbacked source arrays. The same chunk identity is the storage
alias promised by reshape's documentation; it is not a copy of the values. -/
def FreshReshapePost {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims R) (before after : ObjectState)
    (reshaped : Ref R) : Prop :=
  reshaped.identity = before.objects.length ∧
  reshaped.identity ≠ source.identity ∧
  after.objects.length = before.objects.length + 1 ∧
  OldObjectsPreserved before after ∧
  ReshapeTemporaryStorage runtime R before.memory after.memory ∧
  ∃ header : BitArray R,
    ObjectContains after reshaped header ∧
    header.chunks = original.chunks ∧ header.len = original.len ∧
    header.len.val = DimensionProduct dims.val ∧
    bitArraySizeRanked header = dims.val ∧
    header.dims = (if R = 1 then [] else dims.val)

/-- Complete dimension/error/allocation partition for an internal reshape.
Every signed native tuple is included. Invalid higher-rank dimensions produce
ArgumentError before comparison with the old logical length. Otherwise unequal
mathematical element counts produce DimensionMismatch. Both failures preserve
the complete object and chunk state. Compatible dimensions must succeed when
the runtime shared-empty object exists; a spurious error cannot satisfy this
specification. No assumption concerns the source's physical chunks. -/
def ReshapeFreshOutcome {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims R) (before : ObjectState)
    (result : Except JuliaLean.base.array.Error (Ref R) × ObjectState) : Prop :=
  (¬ ReshapeDimensionsChecked dims →
    result.1 = .error (.argument "invalid Array dimensions") ∧ result.2 = before) ∧
  (ReshapeDimensionsChecked dims →
    if DimensionProduct dims.val = original.len.val then
      AllocationInput runtime before.memory →
        ∃ reshaped : Ref R,
          result.1 = .ok reshaped ∧
          FreshReshapePost runtime source original dims before result.2 reshaped
    else
      (∃ message : String, result.1 = .error (.dimensionMismatch message)) ∧
      result.2 = before)

/-- The internal helper always creates a fresh header on compatible dimensions,
even when the requested shape equals the original shape. This independently
checks the helper's allocation/identity invariant in addition to its two public
dispatch paths. All signed dimensions and alias-reachable storage states remain
in the domain; error branches require no allocator premise.
Julia source: base/bitarray.jl:476-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/reshapedarray.jl:67-79 (shared-data contract). -/
def BitreshapeFreshAllocationAndErrors : Prop :=
  ∀ (N R : Nat) (runtime : AllocationData) (source : Ref N) (original : BitArray N)
    (dims : Dims R) (state : ObjectState),
    TupleCountFits N → TupleCountFits R →
    ObjectContains state source original → NativeHeaderShape original →
    ReshapeFreshOutcome runtime source original dims state
      ((JuliaLean.base.bitarray.Models1Group15.bitreshape runtime source dims).run state)

/-- One physical word is changed at exactly the specified mathematical bit;
all other cells and all headers remain untouched. The returned UInt64 is the
word actually stored, so a discarded or incorrect helper return is detectable.
Out-of-range signed bit positions match no UInt64 bit and leave the word intact. -/
def SingleStoredBitWrite (before after : MutableMemory U64)
    (memory position : Nat) (bitIndex : Int) (x : Bool) (returned : U64) : Prop :=
  FixedHeapShape before after ∧
  (∀ (m p : Nat), m ≠ memory ∨ p ≠ position →
    StoredCell after m p = StoredCell before m p) ∧
  StoredCell after memory position = some (some returned) ∧
  ∃ old : U64, StoredCell before memory position = some (some old) ∧
    ∀ bit : Nat, bit < 64 →
      (returned.val / (2 : Int) ^ bit) % 2 =
        if (bit : Int) = bitIndex then (if x then 1 else 0)
        else (old.val / (2 : Int) ^ bit) % 2

/-- Independent two's-complement predecessor used to specify unsafe addressing
for all Int values, including typemin(Int), whose predecessor wraps to typemax.
This mathematical observer calls neither getChunksId nor any model arithmetic. -/
def WrappedZeroBasedScalar (i : I64) : Int :=
  (i.val + (2 : Int) ^ 63 - 1) % (2 : Int) ^ 64 - (2 : Int) ^ 63

/-- Independent native scalar-bound domain. Rank one uses an unchecked
OneTo axis and therefore interprets a negative stored length as an unsigned
endpoint; other ranks clamp the endpoint to zero through oneto. On ordinary
nonnegative lengths this is exactly 1 <= i <= length(B). The modular predecessor
also covers typemin(Int) without assuming unbounded source arithmetic.
Julia source: base/abstractarray.jl:395-396,753. -/
def ScalarIndexAccepted {N : Nat} (B : BitArray N) (i : I64) : Bool :=
  decide ((i.val - 1) % (2 : Int) ^ 64 <
    if N = 1 then B.len.val % (2 : Int) ^ 64 else max 0 B.len.val)

/-- Native UInt64 memories have a constructible byte count and readable raw
isbits contents, including unused capacity. The exact byte bound is the one
imposed by src/genericmemory.c:55-73; it is not a convenient small-test bound. -/
def NativeRawChunkMemory (state : MutableMemory U64) : Prop :=
  ∀ (identity : Nat) (slots : List (Option U64)),
    state.memories[identity]? = some slots →
      8 * slots.length < 2 ^ 63 - 2 ∧
      (∀ cell ∈ slots, ∃ word : U64, cell = some word)

/-- Mathematical native capacity policy, using ordinary natural arithmetic.
This classifies the actual runtime size-error domain; no capacity bound is
assumed to make successful concatenation easy. The policy is documented in
base/array.jl:1102-1112 and uses the full current memory capacity. -/
def NativeGrowthCapacity (capacity : Nat) : Nat :=
  let width := if capacity = 0 then 0 else capacity.log2 + 1
  min (2 ^ 63 - 1) (capacity + 3 * 2 ^ (width * 7 / 8) + capacity / 8)

/-- Independent byte-size classification for required chunk growth. The native
vector's entire memory capacity and offset determine whether growth can reuse
space, recenter in the old memory, or needs a too-large fresh allocation.
Missing headers/memory are excluded by ReadablePackedExtent in value contracts;
they remain included in the separate unrestricted frame/error contracts. -/
def GrowthExceedsNativeByteLimit (state : MutableMemory U64) (chunks desired : Nat) : Bool :=
  match state.arrays[chunks]? with
  | none => false
  | some header =>
    match state.memories[header.reference.1]? with
    | none => false
    | some slots =>
      let offset := (header.reference.2.val - 1).toNat
      if desired ≤ header.size.val.toNat then false
      else if desired ≤ slots.length - offset then false
      else if offset > desired ∧ offset - desired > desired / 4 then false
      else decide (2 ^ 63 - 2 ≤
        8 * max (NativeGrowthCapacity slots.length) (offset + desired))

/-- Frame for every vector growth/copy run, including overlapping aliases and
errors after partial writes. Only the target BitArray header may change, only
its len field changes, and only its chunk-array header may move/resize. At most
one memory object is allocated. Old memory sizes and all other old backing
memories are preserved. This does not pretend a resize preserves another alias's
logical capacity or that an error rolls back committed mutations. -/
def VectorMutationFrame (before after : ObjectState) (target : Ref 1)
    (original : BitVector) (newLength : I64) : Prop :=
  after.objects.length = before.objects.length ∧
  (∀ identity : Nat, identity ≠ target.identity →
    after.objects[identity]? = before.objects[identity]?) ∧
  (∃ updated : BitVector,
    ObjectContains after target updated ∧
    updated.chunks = original.chunks ∧ updated.dims = original.dims ∧
    (updated.len = original.len ∨ updated.len = newLength)) ∧
  after.memory.arrays.length = before.memory.arrays.length ∧
  (∀ identity : Nat, identity ≠ original.chunks →
    after.memory.arrays[identity]? = before.memory.arrays[identity]?) ∧
  before.memory.memories.length ≤ after.memory.memories.length ∧
  after.memory.memories.length ≤ before.memory.memories.length + 1 ∧
  (∀ identity : Nat, identity < before.memory.memories.length →
    (after.memory.memories[identity]?).map List.length =
      (before.memory.memories[identity]?).map List.length) ∧
  (∀ oldChunkHeader : MutableVector,
    before.memory.arrays[original.chunks]? = some oldChunkHeader →
    ∀ identity : Nat, identity < before.memory.memories.length →
      identity ≠ oldChunkHeader.reference.1 →
      after.memory.memories[identity]? = before.memory.memories[identity]?)
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.ChatGPT.Batch3.Group1

theorem bh_predecessor_val (i : I64) :
    (i - int 1).val = Models1Group15.WrappedZeroBasedScalar i := by
  change (i.val - 1 + 9223372036854775808) % 18446744073709551616 -
      9223372036854775808 =
    (i.val + 9223372036854775808 - 1) % 18446744073709551616 -
      9223372036854775808
  omega

theorem bh_address (i : I64) :
    (getChunksId i).1.val = Models1Group15.WrappedZeroBasedScalar i / 64 + 1 ∧
    (getChunksId i).2.val = Models1Group15.WrappedZeroBasedScalar i % 64 := by
  have hb := (i - int 1).property
  change -9223372036854775808 ≤ (i - int 1).val ∧
    (i - int 1).val ≤ 9223372036854775807 at hb
  constructor
  · change wrapInt .i64 ((div64 (i - int 1)).val + 1) = _
    rw [scalar_div64_val]
    have hr : wrapInt .i64 ((i - int 1).val / 64 + 1) =
        (i - int 1).val / 64 + 1 := by
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ (i - int 1).val / 64 + 1 ∧
        (i - int 1).val / 64 + 1 ≤ 9223372036854775807
      omega
    rw [hr, bh_predecessor_val]
  · change (mod64 (i - int 1)).val = _
    rw [scalar_mod64_val, bh_predecessor_val]
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

theorem rc_run_pure {S α : Type} (x : α) (s : S) :
    ((pure x : ExceptT Error (StateM S) α).run s) = (.ok x, s) := rfl

theorem rc_run_bind {S α β : Type} (action : ExceptT Error (StateM S) α)
    (next : α → ExceptT Error (StateM S) β) (s : S) :
    ((action >>= next).run s) =
      match action.run s with
      | (.ok value, after) => (next value).run after
      | (.error error, after) => (.error error, after) := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action s with
  | mk result after => cases result <;> rfl

theorem rc_run_throw {S α : Type} (error : Error) (s : S) :
    ((throw error : ExceptT Error (StateM S) α).run s) = (.error error, s) := rfl

theorem rc_run_get {S : Type} (s : S) :
    ((get : ExceptT Error (StateM S) S).run s) = (.ok s, s) := rfl

theorem rc_run_set {S : Type} (s after : S) :
    ((set after : ExceptT Error (StateM S) Unit).run s) = (.ok (), after) := rfl

theorem rc_run_modify {S : Type} (f : S → S) (s : S) :
    ((modify f : ExceptT Error (StateM S) Unit).run s) = (.ok (), f s) := rfl

theorem rc_readObject {N : Nat} (state : ObjectState) (reference : Ref N)
    (header : BitArray N) (h : ObjectContains state reference header) :
    (readObject reference).run state = (.ok header, state) := by
  change state.objects[reference.identity]? = some (⟨N, header⟩ : Sigma BitArray) at h
  simp only [readObject, rc_run_bind, rc_run_get, h, dite_true, rc_run_pure]

theorem rc_writeObject {N : Nat} (state : ObjectState) (reference : Ref N)
    (old header : BitArray N) (h : ObjectContains state reference old) :
    (writeObject reference header).run state =
      (.ok (), { state with objects := state.objects.set reference.identity ⟨N, header⟩ }) := by
  simp only [writeObject, rc_run_bind, rc_readObject state reference old h, rc_run_modify]

theorem rc_liftBit {α : Type} (action : BitMutationM α) (state : ObjectState) :
    (liftBit action).run state =
      ((action.run state.memory).1, { state with memory := (action.run state.memory).2 }) := by
  cases h : action.run state.memory with
  | mk result memory =>
    cases result <;>
      simp only [liftBit, rc_run_bind, rc_run_get, h, rc_run_set, rc_run_pure, rc_run_throw]

theorem rc_registerObject {N : Nat} (state : ObjectState) (header : BitArray N) :
    (registerObject header).run state =
      (.ok ⟨state.objects.length⟩,
        { state with objects := state.objects ++ [(⟨N, header⟩ : Sigma BitArray)] }) := by
  simp only [registerObject, rc_run_bind, rc_run_get, rc_run_set, rc_run_pure]

theorem rc_int_val (x : I64) : int x.val = x := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 x.val x.property

theorem rc_many_checked_iff {R : Nat} (dims : Dims R) (hr : 2 ≤ R) :
    ReshapeDimensionsChecked dims ↔
      (∀ x ∈ dims.val, ¬ JuliaLean.Proofs.base.array.opusGrowth.badDim x) ∧
        DimensionProduct dims.val ≤ 9223372036854775807 := by
  have hnot : ¬ R ≤ 1 := by omega
  simp only [ReshapeDimensionsChecked, AcceptedNativeDimensions, hnot, false_or]
  constructor
  · rintro ⟨hn, hb, hp⟩
    refine ⟨?_, hp⟩
    intro x hx
    have h0 := hn x hx
    have hmax := hb x hx
    change x.val < 9223372036854775807 at hmax
    change ¬ (x.val < 0 ∨ x.val = 9223372036854775807)
    omega
  · rintro ⟨hg, hp⟩
    refine ⟨?_, ?_, hp⟩
    · intro x hx
      have h := hg x hx
      change ¬ (x.val < 0 ∨ x.val = 9223372036854775807) at h
      omega
    · intro x hx
      have h := hg x hx
      change ¬ (x.val < 0 ∨ x.val = 9223372036854775807) at h
      have hbound := x.property
      change -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 at hbound
      change x.val < 9223372036854775807
      omega

local instance rc_checkedDec {R : Nat} (dims : Dims R) :
    Decidable (ReshapeDimensionsChecked dims) := by
  unfold ReshapeDimensionsChecked AcceptedNativeDimensions
  infer_instance

theorem rc_checkedDims_run {R : Nat} (dims : Dims R) (s : MutableMemory U64) :
    (JuliaLean.base.array.checkedDims dims.val : BitMutationM I64).run s =
      if ReshapeDimensionsChecked dims then
        (.ok (int (DimensionProduct dims.val)), s)
      else (.error (.argument "invalid Array dimensions"), s) := by
  rcases dims with ⟨ds, hds⟩
  cases ds with
  | nil =>
    have hR : R = 0 := by simpa only [List.length_nil] using hds.symm
    subst R
    have hc : ReshapeDimensionsChecked (⟨[], rfl⟩ : Dims 0) := Or.inl (by decide)
    simp only [hc, ite_true, checkedDims, checkedDims0, rc_run_pure,
      DimensionProduct, List.map_nil, List.prod_nil]
    rfl
  | cons d ds =>
    cases ds with
    | nil =>
      have hR : R = 1 := by simpa only [List.length_cons, List.length_nil] using hds.symm
      subst R
      have hc : ReshapeDimensionsChecked (⟨[d], rfl⟩ : Dims 1) := Or.inl (by decide)
      simp only [hc, ite_true, checkedDims, checkedDims1, rc_run_pure,
        DimensionProduct, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Int.mul_one, rc_int_val]
    | cons e rest =>
      let dims : Dims R := ⟨d :: e :: rest, hds⟩
      have hr : 2 ≤ R := by simp only [List.length_cons] at hds; omega
      have hlen : 2 ≤ (d :: e :: rest).length := by simp only [List.length_cons]; omega
      have hs := JuliaLean.Proofs.base.array.opusGrowth.checkedMulDims_spec
        (d :: e :: rest) hlen
      by_cases hc : ReshapeDimensionsChecked dims
      · obtain ⟨hg, hp⟩ := (rc_many_checked_iff dims hr).mp hc
        obtain ⟨hflag, hval⟩ := hs.2 hg
        have hfalse : (checkedMulDims (d :: e :: rest)).2 = false := by
          rw [hflag]
          apply decide_eq_false
          exact Int.not_lt.mpr hp
        have heq : (checkedMulDims (d :: e :: rest)).1 =
            int (DimensionProduct (d :: e :: rest)) := by
          apply Subtype.ext
          have hv := hval hfalse
          rw [hv]
          symm
          change wrapInt .i64 (DimensionProduct (d :: e :: rest)) =
            DimensionProduct (d :: e :: rest)
          apply wrapInt_of_inRange
          have hz := JuliaLean.Proofs.base.array.opusGrowth.dimProd_nonneg
            (d :: e :: rest) (by
              intro x hx
              have h := hg x hx
              change ¬ (x.val < 0 ∨ x.val = 9223372036854775807) at h
              omega)
          change -9223372036854775808 ≤ DimensionProduct (d :: e :: rest) ∧
            DimensionProduct (d :: e :: rest) ≤ 9223372036854775807
          change 0 ≤ DimensionProduct (d :: e :: rest) at hz
          exact ⟨by omega, hp⟩
        change _ = if ReshapeDimensionsChecked dims then _ else _
        rw [if_pos hc]
        simp only [checkedDims, checkedDimsMany, hfalse, Bool.false_eq_true, ite_false,
          rc_run_bind, rc_run_pure, heq]
      · have htrue : (checkedMulDims (d :: e :: rest)).2 = true := by
          by_cases hb : ∃ x ∈ (d :: e :: rest), JuliaLean.Proofs.base.array.opusGrowth.badDim x
          · exact hs.1 hb
          · have hg : ∀ x ∈ (d :: e :: rest), ¬ JuliaLean.Proofs.base.array.opusGrowth.badDim x :=
              fun x hx h => hb ⟨x, hx, h⟩
            obtain ⟨hflag, _⟩ := hs.2 hg
            rw [hflag]
            apply decide_eq_true
            have hp : ¬ DimensionProduct dims.val ≤ 9223372036854775807 :=
              fun hp => hc ((rc_many_checked_iff dims hr).mpr ⟨hg, hp⟩)
            change 9223372036854775807 < DimensionProduct dims.val
            omega
        change _ = if ReshapeDimensionsChecked dims then _ else _
        rw [if_neg hc]
        simp only [checkedDims, checkedDimsMany, htrue, ite_true, rc_run_bind, rc_run_throw]

theorem rc_product_inRange {R : Nat} (dims : Dims R)
    (hc : ReshapeDimensionsChecked dims) :
    IntTy.min .i64 ≤ DimensionProduct dims.val ∧
      DimensionProduct dims.val ≤ IntTy.max .i64 := by
  by_cases hr : R ≤ 1
  · rcases dims with ⟨ds, hds⟩
    cases ds with
    | nil => change (-9223372036854775808 : Int) ≤ 1 ∧ (1 : Int) ≤ 9223372036854775807; decide
    | cons d ds =>
      cases ds with
      | nil =>
        simpa only [DimensionProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, Int.mul_one] using d.property
      | cons e rest => simp only [List.length_cons] at hds; omega
  · have hg : AcceptedNativeDimensions dims := hc.resolve_left hr
    have hn := JuliaLean.Proofs.base.array.opusGrowth.dimProd_nonneg dims.val hg.1
    change 0 ≤ DimensionProduct dims.val at hn
    refine ⟨?_, hg.2.2⟩
    change -9223372036854775808 ≤ DimensionProduct dims.val
    omega

theorem rc_checked_product_val {R : Nat} (dims : Dims R)
    (hc : ReshapeDimensionsChecked dims) :
    (int (DimensionProduct dims.val)).val = DimensionProduct dims.val :=
  wrapInt_of_inRange .i64 _ (rc_product_inRange dims hc)

theorem rc_setObjectChunks {N : Nat} (state : ObjectState) (reference : Ref N)
    (header : BitArray N) (chunks : Nat) (h : ObjectContains state reference header) :
    (setObjectChunks reference chunks).run state =
      (.ok (), { state with objects := state.objects.set reference.identity (⟨N, { header with chunks := chunks }⟩) }) := by
  simp only [setObjectChunks, rc_run_bind, rc_readObject state reference header h,
    rc_writeObject state reference header _ h]

theorem rc_setObjectLength {N : Nat} (state : ObjectState) (reference : Ref N)
    (header : BitArray N) (len : I64) (h : ObjectContains state reference header) :
    (setObjectLength reference len).run state =
      (.ok (), { state with objects := state.objects.set reference.identity (⟨N, { header with len := len }⟩) }) := by
  simp only [setObjectLength, rc_run_bind, rc_readObject state reference header h,
    rc_writeObject state reference header _ h]

theorem rc_setObjectDims {N : Nat} (state : ObjectState) (reference : Ref N)
    (header : BitArray N) (dims : Dims N) (h : ObjectContains state reference header) :
    (setObjectDims reference dims).run state =
      (.ok (), { state with objects := state.objects.set reference.identity (⟨N, { header with dims := dims.val }⟩) }) := by
  simp only [setObjectDims, rc_run_bind, rc_readObject state reference header h,
    rc_writeObject state reference header _ h]

def rc_addedState {N : Nat} (before : ObjectState) (memory : MutableMemory U64)
    (header : BitArray N) : ObjectState :=
  { memory := memory, objects := before.objects ++ [(⟨N, header⟩ : Sigma BitArray)] }

theorem rc_addedContains {N : Nat} (before : ObjectState) (memory : MutableMemory U64)
    (header : BitArray N) :
    ObjectContains (rc_addedState before memory header) ⟨before.objects.length⟩ header := by
  simp only [ObjectContains, rc_addedState, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem rc_addedChunks {N : Nat} (before : ObjectState) (memory : MutableMemory U64)
    (header : BitArray N) (chunks : Nat) :
    (setObjectChunks (⟨before.objects.length⟩ : Ref N) chunks).run
      (rc_addedState before memory header) =
      (.ok (), rc_addedState (N := N) before memory { header with chunks := chunks }) := by
  rw [rc_setObjectChunks _ _ header chunks (rc_addedContains before memory header)]
  simp only [rc_addedState, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero]

theorem rc_addedLength {N : Nat} (before : ObjectState) (memory : MutableMemory U64)
    (header : BitArray N) (len : I64) :
    (setObjectLength (⟨before.objects.length⟩ : Ref N) len).run
      (rc_addedState before memory header) =
      (.ok (), rc_addedState (N := N) before memory { header with len := len }) := by
  rw [rc_setObjectLength _ _ header len (rc_addedContains before memory header)]
  simp only [rc_addedState, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero]

theorem rc_addedDims {N : Nat} (before : ObjectState) (memory : MutableMemory U64)
    (header : BitArray N) (dims : Dims N) :
    (setObjectDims (⟨before.objects.length⟩ : Ref N) dims).run
      (rc_addedState before memory header) =
      (.ok (), rc_addedState (N := N) before memory { header with dims := dims.val }) := by
  rw [rc_setObjectDims _ _ header dims (rc_addedContains before memory header)]
  simp only [rc_addedState, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero]

theorem rc_zero_product (R : Nat) :
    DimensionProduct (List.replicate R (int 0)) = if R = 0 then 1 else 0 := by
  cases R with
  | zero => rfl
  | succ R =>
    simp only [List.replicate_succ, DimensionProduct, List.map_cons, List.prod_cons,
      Nat.succ_ne_zero, ite_false]
    change 0 * _ = 0
    exact Int.zero_mul _

theorem rc_zero_accepted (R : Nat) :
    AcceptedNativeDimensions (⟨List.replicate R (int 0), List.length_replicate ..⟩ : Dims R) := by
  refine ⟨?_, Or.inr ?_, ?_⟩
  · intro d hd
    have hd0 := (List.mem_replicate.mp hd).2
    rw [hd0]
    decide
  · intro d hd
    have hd0 := (List.mem_replicate.mp hd).2
    rw [hd0]
    decide
  · rw [rc_zero_product]
    split <;> decide

theorem rc_source_identity_lt {N : Nat} (state : ObjectState) (source : Ref N)
    (original : BitArray N) (hobj : ObjectContains state source original) :
    source.identity < state.objects.length := by
  change state.objects[source.identity]? = some (⟨N, original⟩ : Sigma BitArray) at hobj
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hobj
  exact hlt
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 256
set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true

def rc_nativeValidation (ds : List I64) (index : I64) : BitMutationM I64 := do
  let mut i := index
  for d in ds do
    if d.val < 0 then
      throw (.argument s!"dimension size must be ≥ 0, got {d.val} for dimension {i.val}")
    i := i + int 1
  pure i

theorem rc_nativeValidation_good (ds : List I64) (index : I64) (s : State)
    (hn : ∀ d ∈ ds, 0 ≤ d.val) :
    ∃ last, (rc_nativeValidation ds index).run s = (.ok last, s) := by
  induction ds generalizing index with
  | nil => exact ⟨index, rfl⟩
  | cons d ds ih =>
    have hd : ¬ d.val < 0 := by have := hn d List.mem_cons_self; omega
    obtain ⟨last, hlast⟩ := ih (index + int 1)
      (fun e he => hn e (List.mem_cons_of_mem d he))
    refine ⟨last, ?_⟩
    simpa only [rc_nativeValidation, List.forIn_cons, hd, ite_false,
      rc_run_bind, rc_run_pure] using hlast

def rc_undefBody {N : Nat} (runtime : AllocationData) (dims : Dims N) : BitMutationM (BitArray N) := do
  let n ← checkedDims dims.val
  let nc := numBitChunks n
  let chunks ← allocateChunks runtime nc
  if nc > int 0 then
    mutableSet chunks (u64 0) (← mutableLength chunks)
  pure ⟨chunks, n, if N = 1 then [] else dims.val⟩

theorem rc_undef_factor {N : Nat} (runtime : AllocationData) (dims : Dims N) (s : State) :
    (undef runtime dims).run s =
      ((rc_nativeValidation dims.val (int 1) >>= fun _ => rc_undefBody runtime dims).run s) := by
  simp only [undef, rc_nativeValidation, rc_undefBody, rc_run_bind, rc_run_pure]
  split <;> rfl
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem sp_frame_refl (s : MutableMemory U64) (a : Nat) :
    DestinationFrame s s a := by
  exact ⟨⟨rfl, rfl, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩

theorem sp_mutableGet_run (s : MutableMemory U64) (a : Nat) (i : I64) :
    (mutableGet a i).run s =
      ((match s.arrays[a]? with
      | none => .error .bounds
      | some h =>
          if 1 ≤ i.val ∧ i.val ≤ h.size.val then
            match s.memories[h.reference.1]? with
            | none => .error .bounds
            | some slots =>
                match slots[(h.reference.2.val + i.val - 2).toNat]? with
                | none => .error .bounds
                | some none => .error .undefinedReference
                | some (some word) => .ok word
          else .error .bounds), s) := by
  cases ha : s.arrays[a]? with
  | none =>
      simp only [mutableGet, stateExcept_bind, mutableVector_run, ha]
  | some h =>
      by_cases hb : 1 ≤ i.val ∧ i.val ≤ h.size.val
      · have hb' : 1 ≤ i.val ∧ i ≤ h.size := hb
        simp only [mutableGet, stateExcept_bind, mutableVector_run, ha,
          hb', hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
          ite_false, ite_true]
        cases hm : s.memories[h.reference.1]? with
        | none =>
            simp only [memoryRead, stateExcept_bind, mutation_get_run, hm,
              stateExcept_throw]
        | some slots =>
            rw [memoryRead_run s h.reference.1 slots hm]
            cases hg : slots[(h.reference.2.val + i.val - 2).toNat]? with
            | none => simp only [hg, stateExcept_throw]
            | some cell => cases cell <;> simp only [hg, stateExcept_pure, stateExcept_throw]
      · have hb' : ¬ (1 ≤ i.val ∧ i ≤ h.size) := hb
        simp only [mutableGet, stateExcept_bind, mutableVector_run, ha,
          hb', hb, decide_false, Bool.not_false, ite_true, ite_false,
          stateExcept_throw]

theorem sp_mutableGet_readonly (s : MutableMemory U64) (a : Nat) (i : I64) :
    ((mutableGet a i).run s).2 = s := by
  rw [sp_mutableGet_run]

theorem sp_mutableSet_run (s : MutableMemory U64) (a : Nat) (word : U64) (i : I64) :
    (mutableSet a word i).run s =
      match s.arrays[a]? with
      | none => (.error .bounds, s)
      | some h =>
          if 1 ≤ i.val ∧ i.val ≤ h.size.val then
            match s.memories[h.reference.1]? with
            | none => (.error .bounds, s)
            | some slots =>
                if 1 ≤ (h.reference.2 + i - one).val ∧
                    (h.reference.2 + i - one).val ≤ (slots.length : Int) then
                  (.ok (), {s with memories := (s.memories.set h.reference.1
                    (slots.set ((h.reference.2 + i - one).val - 1).toNat (some word)))})
                else (.error .bounds, s)
          else (.error .bounds, s) := by
  cases ha : s.arrays[a]? with
  | none =>
      simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
        mutableLength, stateExcept_bind, mutableVector_run, ha]
  | some h =>
      by_cases hb : 1 ≤ i.val ∧ i.val ≤ h.size.val
      · have hb' : one ≤ i ∧ i ≤ h.size := hb
        simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
          stateExcept_bind, mutableLength_run s a h ha, stateExcept_pure,
          hb, hb', and_self, decide_true, Bool.not_true, Bool.false_eq_true,
          ite_false, ite_true, mutableMemoryref, mutableRef_run s a h ha]
        cases hm : s.memories[h.reference.1]? with
        | none =>
            simp only [memoryWrite, memoryRead, stateExcept_bind,
              mutation_get_run, hm, stateExcept_throw]
        | some slots =>
            simp only [memoryWrite, stateExcept_bind,
              memoryRead_run s h.reference.1 slots hm]
            by_cases hp : 1 ≤ (h.reference.2 + i - one).val ∧
                (h.reference.2 + i - one).val ≤ (slots.length : Int)
            · simp only [hp, and_self, decide_true, Bool.not_true,
                Bool.false_eq_true, ite_false, ite_true, mutation_modify_run,
                stateExcept_pure]
            · simp only [hp, decide_false, Bool.not_false, ite_true,
                ite_false, stateExcept_bind, stateExcept_throw]
      · have hb' : ¬ (one ≤ i ∧ i ≤ h.size) := hb
        simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
          stateExcept_bind, mutableLength_run s a h ha, stateExcept_pure,
          hb, hb', decide_false, Bool.not_false, ite_true, ite_false,
          stateExcept_throw]

theorem sp_memory_update_shape (s : MutableMemory U64) (m p : Nat)
    (slots : List (Option U64)) (value : Option U64)
    (hm : s.memories[m]? = some slots) :
    FixedHeapShape s {s with memories := s.memories.set m (slots.set p value)} := by
  refine ⟨rfl, List.length_set, ?_⟩
  intro other
  by_cases he : m = other
  · subst other
    have hlt : m < s.memories.length := (List.getElem?_eq_some_iff.mp hm).choose
    simp only [List.getElem?_set_self hlt, hm, Option.map_some, List.length_set]
  · rw [List.getElem?_set_ne he]

theorem sp_memory_update_elsewhere (s : MutableMemory U64) (m p : Nat)
    (slots : List (Option U64)) (value : Option U64)
    (hm : s.memories[m]? = some slots) (other pos : Nat)
    (hne : other ≠ m ∨ pos ≠ p) :
    StoredCell {s with memories := s.memories.set m (slots.set p value)} other pos =
      StoredCell s other pos := by
  unfold StoredCell
  by_cases he : other = m
  · subst other
    have hpos : p ≠ pos := Ne.symm (hne.resolve_left (not_not_intro rfl))
    have hlt : m < s.memories.length := (List.getElem?_eq_some_iff.mp hm).choose
    simp only [List.getElem?_set_self hlt, hm, Option.bind_some,
      List.getElem?_set_ne hpos]
  · rw [List.getElem?_set_ne (Ne.symm he)]

theorem sp_mutableSet_frame (s : MutableMemory U64) (a : Nat) (word : U64) (i : I64) :
    DestinationFrame s ((mutableSet a word i).run s).2 a := by
  rw [sp_mutableSet_run]
  split
  · exact sp_frame_refl s a
  · rename_i header ha
    split
    · rename_i hb
      split
      · exact sp_frame_refl s a
      · rename_i slots hm
        split
        · refine ⟨sp_memory_update_shape s _ _ slots (some word) hm, ?_⟩
          intro otherHeader hheader hvalid m p hout
          have he : otherHeader = header := Option.some.inj (hheader.symm.trans ha)
          subst otherHeader
          have hv : 0 ≤ header.size.val ∧ 1 ≤ header.reference.2.val ∧
              header.reference.2.val - 1 + header.size.val ≤ (slots.length : Int) ∧
              slots.length < 2 ^ 63 := by
            simpa only [MutableMemory.validVector, ha, hm] using hvalid
          have haddr : (header.reference.2 + i - one).val =
              header.reference.2.val + i.val - 1 :=
            ival_add_sub_one _ _ (by omega)
          apply sp_memory_update_elsewhere s _ _ slots (some word) hm m p
          by_cases hmem : m = header.reference.1
          · right
            rw [haddr]
            omega
          · exact Or.inl hmem
        · exact sp_frame_refl s a
    · exact sp_frame_refl s a

theorem sp_checkindexOneTo (last i : I64) :
    JuliaLean.base.abstractarray.checkindexOneTo last i =
      decide ((i.val - 1) % (2 : Int) ^ 64 < last.val % (2 : Int) ^ 64) := by
  change decide (wrapInt .i64 (i.val - 1) % (2 : Int) ^ 64 <
      last.val % (2 : Int) ^ 64) = _
  have hm := JuliaLean.Proofs.base.int.wrapInt_emod_self .i64 (i.val - 1)
  change wrapInt .i64 (i.val - 1) % (2 : Int) ^ 64 =
    (i.val - 1) % (2 : Int) ^ 64 at hm
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, hm]

theorem sp_nativeOneTo_stop (n : I64) :
    (JuliaLean.base.bitarray.Models1Group15.nativeOneTo n).stop.val = max 0 n.val := by
  change (max_BitInteger (int 0) n).val = _
  exact JuliaLean.Proofs.base.int.maxExact_proven .i64 .i64 (int 0) n

theorem sp_nativeCheck_result {N : Nat} (B : BitArray N) (i : I64) :
    JuliaLean.base.abstractarray.checkboundsOne
      JuliaLean.base.bitarray.Models1Group15.nativeScalarEachindex
      (fun axis j => pure (JuliaLean.base.abstractarray.checkindexOneTo axis.stop j)) B i =
      .ok (ScalarIndexAccepted B i) := by
  unfold JuliaLean.base.abstractarray.checkboundsOne
  by_cases hn : N = 1
  · simp only [JuliaLean.base.bitarray.Models1Group15.nativeScalarEachindex, hn,
      ite_true, JuliaLean.base.abstractarray.eachindexLinearVector,
      JuliaLean.base.abstractarray.axes1, JuliaLean.base.abstractarray.axesDefault,
      bitArraySizeRanked, pure_bind]
    change Except.ok (JuliaLean.base.abstractarray.checkindexOneTo B.len i) = _
    rw [sp_checkindexOneTo]
    simp only [ScalarIndexAccepted, hn, ite_true]
  · simp only [JuliaLean.base.bitarray.Models1Group15.nativeScalarEachindex, hn,
      ite_false, JuliaLean.base.abstractarray.eachindexLinear, pure_bind]
    change Except.ok (JuliaLean.base.abstractarray.checkindexOneTo
      (JuliaLean.base.bitarray.Models1Group15.nativeOneTo B.len).stop i) = _
    rw [sp_checkindexOneTo, sp_nativeOneTo_stop]
    have hb := B.len.property
    have hm : max 0 B.len.val % (2 : Int) ^ 64 = max 0 B.len.val :=
      Int.emod_eq_of_lt (by omega) (by change -9223372036854775808 ≤ B.len.val ∧
        B.len.val ≤ 9223372036854775807 at hb; omega)
    simp only [hm, ScalarIndexAccepted, hn, ite_false]

macro (name := sp_unfoldNativeBounds) "sp_unfoldNativeBounds" : tactic => do
  let name : Lean.Name := .str (.str (.str (.str (.str
    (.num `_private.JuliaLean.base.bitarray 0) "JuliaLean") "base") "bitarray")
    "Models1Group15") "liftNativeBounds"
  `(tactic| unfold $(Lean.mkIdent name))

macro (name := sp_privateBoundsOnly) "sp_privateBoundsOnly" : term => do
  pure (Lean.mkIdent (.str (.str (.str (.str (.str
    (.num `_private.JuliaLean.base.bitarray 0) "JuliaLean") "base") "bitarray")
    "Models1Group15") "BoundsOnly"))

macro (name := sp_privateLiftBounds) "sp_privateLiftBounds" : term => do
  pure (Lean.mkIdent (.str (.str (.str (.str (.str
    (.num `_private.JuliaLean.base.bitarray 0) "JuliaLean") "base") "bitarray")
    "Models1Group15") "liftNativeBounds"))

theorem sp_liftNativeBounds_eq {α : Type} (result : JuliaLean.base.abstractarray.Result α)
    (proof : sp_privateBoundsOnly result) :
    (sp_privateLiftBounds result proof : BitMutationM α) =
      (match (generalizing := false) result with
       | .ok value => pure value
       | .error _ => throw Error.bounds) := by
  sp_unfoldNativeBounds
  cases result <;> rfl

theorem sp_nativeBounds_expand {N : Nat} (B : BitArray N) (i : I64) :
    JuliaLean.base.bitarray.Models1Group15.nativeScalarBounds B i =
      (do
        let b ← (match JuliaLean.base.abstractarray.checkboundsOne
          JuliaLean.base.bitarray.Models1Group15.nativeScalarEachindex
          (fun axis j => pure (JuliaLean.base.abstractarray.checkindexOneTo axis.stop j)) B i with
          | .ok b => pure b
          | .error _ => throw Error.bounds : BitMutationM Bool)
        if !b then throw Error.bounds : BitMutationM Unit) := by
  unfold JuliaLean.base.bitarray.Models1Group15.nativeScalarBounds
  dsimp only
  simp only [sp_liftNativeBounds_eq]
  cases JuliaLean.base.abstractarray.checkboundsOne
    JuliaLean.base.bitarray.Models1Group15.nativeScalarEachindex
    (fun axis j => pure (JuliaLean.base.abstractarray.checkindexOneTo axis.stop j)) B i <;> rfl

theorem sp_nativeBounds_run {N : Nat} (B : BitArray N) (i : I64)
    (s : MutableMemory U64) :
    (JuliaLean.base.bitarray.Models1Group15.nativeScalarBounds B i).run s =
      if ScalarIndexAccepted B i then (.ok (), s) else (.error .bounds, s) := by
  rw [sp_nativeBounds_expand, sp_nativeCheck_result B i]
  cases hc : ScalarIndexAccepted B i <;> rfl

theorem sp_mutableGet_valid (s : MutableMemory U64) (a : Nat) (i : I64)
    (hv : s.validVector a) :
    (mutableGet a i).run s =
      ((if i.val < 1 then .error .bounds
        else match (s.contents a)[(i.val - 1).toNat]? with
          | none => .error .bounds
          | some none => .error .undefinedReference
          | some (some word) => .ok word), s) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hv
  have hlen : (s.contents a).length = n.val.toNat := by
    rw [h.contents]
    exact vwWindow_length h
  by_cases hlow : i.val < 1
  · simp only [sp_mutableGet_run, h.1, hlow, ite_true,
      show ¬ (1 ≤ i.val ∧ i.val ≤ n.val) by omega, ite_false]
  · by_cases hhigh : i.val ≤ n.val
    · have hindex : (i.val - 1).toNat < (s.contents a).length := by
        rw [hlen]
        omega
      rw [vwGet_run s a mem off n slots h i ⟨by omega, hhigh⟩,
        ← h.contents, if_neg hlow, List.getElem?_eq_getElem hindex]
      cases (s.contents a)[(i.val - 1).toNat] <;> rfl
    · have hnone : (s.contents a)[(i.val - 1).toNat]? = none :=
        List.getElem?_eq_none_iff.mpr (by rw [hlen]; omega)
      simp only [sp_mutableGet_run, h.1, hlow, ite_false, hnone,
        show ¬ (1 ≤ i.val ∧ i.val ≤ n.val) by omega]

theorem sp_bit_math (word : U64) (bit : Nat) :
    JuliaLean.ChatGPT.Batch2.Group4.packedBit word bit =
      decide ((word.val / (2 : Int) ^ bit) % 2 = 1) := by
  have hv : (word.val.toNat : Int) = word.val :=
    Int.toNat_of_nonneg word.property.1
  have hc : ((word.val.toNat / 2 ^ bit % 2 : Nat) : Int) =
      (word.val / (2 : Int) ^ bit) % 2 := by
    rw [Int.natCast_emod, Int.natCast_ediv, Int.natCast_pow, hv]
    rfl
  unfold JuliaLean.ChatGPT.Batch2.Group4.packedBit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem sp_bit_value (word : U64) (bit : Nat) :
    (word.val / (2 : Int) ^ bit) % 2 =
      if JuliaLean.ChatGPT.Batch2.Group4.packedBit word bit then 1 else 0 := by
  rw [sp_bit_math]
  have h0 := Int.emod_nonneg (word.val / (2 : Int) ^ bit) (by decide : (2 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos (word.val / (2 : Int) ^ bit) (by decide : (0 : Int) < 2)
  by_cases h : (word.val / (2 : Int) ^ bit) % 2 = 1
  · simp only [h, decide_true, ite_true]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

theorem sp_memory_update_here (s : MutableMemory U64) (m p : Nat)
    (slots : List (Option U64)) (value : Option U64)
    (hm : s.memories[m]? = some slots) (hp : p < slots.length) :
    StoredCell {s with memories := s.memories.set m (slots.set p value)} m p = some value := by
  have hmem : m < s.memories.length := (List.getElem?_eq_some_iff.mp hm).choose
  simp only [StoredCell, List.getElem?_set_self hmem, Option.bind_some,
    List.getElem?_set_self hp]

theorem sp_singleBitUpdate (s : MutableMemory U64) (m p : Nat)
    (slots : List (Option U64)) (old : U64) (bit : Nat) (x : Bool)
    (hm : s.memories[m]? = some slots)
    (hold : slots[p]? = some (some old)) (hb : bit < 64) :
    let word := if x then or_int old (shl_int (u64 1) (int bit))
      else and_int old (not_int (shl_int (u64 1) (int bit)))
    SingleStoredBitWrite s {s with memories := s.memories.set m (slots.set p (some word))}
      m p (bit : Int) x word := by
  dsimp only
  have hp : p < slots.length := (List.getElem?_eq_some_iff.mp hold).choose
  refine ⟨sp_memory_update_shape s m p slots _ hm,
    sp_memory_update_elsewhere s m p slots _ hm, sp_memory_update_here s m p slots _ hm hp,
    old, ?_, ?_⟩
  · simp only [StoredCell, hm, Option.bind_some, hold]
  · intro k hk
    rw [sp_bit_value, JuliaLean.ChatGPT.Batch3.Group1.scalar_set_word_bits old bit k x hb hk,
      sp_bit_value]
    by_cases he : k = bit
    · subst k
      simp only [ite_true]
    · have hcast : (k : Int) ≠ (bit : Int) := by omega
      simp only [he, hcast, ite_false]

theorem sp_publicWrite_run {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (x : Bool) (i : I64) :
    (JuliaLean.base.bitarray.Models1Group15.setIndexBool B x i).run s =
      if ScalarIndexAccepted B i then
        match (unsafeBitSetIndex B.chunks x i).run s with
        | (.error e, after) => (.error e, after)
        | (.ok _, after) => (.ok B, after)
      else (.error .bounds, s) := by
  simp only [JuliaLean.base.bitarray.Models1Group15.setIndexBool,
    bitArraySetIndex, stateExcept_bind, sp_nativeBounds_run]
  cases h : ScalarIndexAccepted B i
  · rfl
  · simp only [ite_true, JuliaLean.base.number.convertSame, stateExcept_pure]
    cases hr : (unsafeBitSetIndex B.chunks x i).run s with
    | mk res after => cases res <;> rfl
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15
open JuliaLean.ChatGPT.Batch5.Group2
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.base.tuple

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def rt_rawSlots (runtime : AllocationData) (s : State) (count : Nat) : List (Option U64) :=
  (List.range count).map (fun i => some (runtime.rawWord s.memories.length i))

theorem rt_rawSlots_length (runtime : AllocationData) (s : State) (count : Nat) :
    (rt_rawSlots runtime s count).length = count := by
  simp only [rt_rawSlots, List.length_map, List.length_range]

def rt_emptyHeap (runtime : AllocationData) (s : State) : State :=
  { s with arrays := s.arrays ++ [⟨(runtime.emptyMemory, int 1), int 0⟩] }

theorem rt_allocateChunks_zero (runtime : AllocationData) (s : State) :
    (allocateChunks runtime (int 0)).run s =
      (.ok s.arrays.length, rt_emptyHeap runtime s) := by
  rfl

set_option backward.isDefEq.respectTransparency true in
theorem rt_allocateChunks_positive (runtime : AllocationData) (s : State) (count : Nat)
    (hp : 0 < count) (hc : count ≤ 576460752303423488) :
    (allocateChunks runtime (int count)).run s =
      (.ok s.arrays.length, shiftFreshHeap s (rt_rawSlots runtime s count)) := by
  have hn64 : count ≤ 9223372036854775807 := by omega
  have hnat : ((int count).val % 2 ^ 64).toNat = count := by
    rw [packedInt_val count hn64, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hb : count * 8 < 2 ^ 64 := by omega
  have hz : (count * 8) % 2 ^ 64 = count * 8 := Nat.mod_eq_of_lt hb
  have hlimit1 : ¬ (count ≥ maxIntVal - 1) := by unfold maxIntVal; omega
  have hlimit2 : ¬ (count * 8 ≥ maxIntVal - 1) := by unfold maxIntVal; omega
  have hn0 : count ≠ 0 := by omega
  have hLayout : allocationSummary uint64Layout = ⟨8, false, false⟩ := by decide
  simp only [allocateChunks, hLayout, arrayUndef1, memoryUndef, memorynew,
    hnat, allocGenericMemory, hn0, ite_false, Bool.false_eq_true, newGenericMemory,
    sizeMulOverflow, hz,
    show ¬ (2 ^ 64 ≤ count * 8) by omega, decide_false,
    hlimit1, hlimit2, Bool.false_or, Bool.false_eq_true, allocateRawWords,
    shape_run_bind, shape_run_get, shape_run_pure]
  simp only [shiftFreshHeap, rt_rawSlots, List.length_map, List.length_range]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 50000 in
set_option maxRecDepth 512 in
theorem rt_undef_zero_run {N : Nat} (runtime : AllocationData) (dims : Dims N)
    (s : State) (hdims : ∀ d ∈ dims.val, 0 ≤ d.val)
    (hchecked : (checkedDims dims.val : BitMutationM I64).run s = (.ok (int 0), s)) :
    ExceptT.run (JuliaLean.base.bitarray.Models1Group15.undef (N := N) runtime dims : BitMutationM (BitArray N)) s =
      (.ok (⟨s.arrays.length, int 0, if N = 1 then [] else dims.val⟩ : BitArray N),
        rt_emptyHeap runtime s) := by
  obtain ⟨last, hlast⟩ := rc_nativeValidation_good dims.val (int 1) s hdims
  have hnc : numBitChunks (int 0) = int 0 := rfl
  have hpos : ¬ int 0 > int 0 := by decide
  calc
    (undef runtime dims).run s = (rc_undefBody runtime dims).run s := by
      rw [rc_undef_factor, shape_run_bind, hlast]
    _ = _ := by
      unfold rc_undefBody
      rw [shape_run_bind, hchecked]
      dsimp only
      rw [hnc, shape_run_bind, rt_allocateChunks_zero]
      dsimp only
      rw [if_neg hpos]
      rfl
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.bitarray.Models1Group15

theorem bh_shape_trans {s middle after : MutableMemory U64}
    (h₁ : FixedHeapShape s middle) (h₂ : FixedHeapShape middle after) :
    FixedHeapShape s after := by
  exact ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1,
    fun memory => (h₂.2.2 memory).trans (h₁.2.2 memory)⟩
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

def rc_zeroMemory (runtime : AllocationData) (R : Nat) (s : State) : State :=
  if R = 0 then shiftFreshHeap s [some (u64 0)] else rt_emptyHeap runtime s

theorem rc_undef_rankZero (runtime : AllocationData) (s : State) :
    (undef runtime (⟨[], rfl⟩ : Dims 0)).run s =
      (.ok (⟨s.arrays.length, int 1, []⟩ : BitArray 0), shiftFreshHeap s [some (u64 0)]) := by
  have hc : (checkedDims ([] : List I64) : BitMutationM I64).run s = (.ok (int 1), s) := rfl
  have hn : numBitChunks (int 1) = int 1 := rfl
  have ha := rt_allocateChunks_positive runtime s 1 (by decide) (by decide)
  have hl := shiftFreshLength s (rt_rawSlots runtime s 1)
  rw [rt_rawSlots_length] at hl
  have hw := shiftFreshSet s (rt_rawSlots runtime s 1) 0 (u64 0)
    (by rw [rt_rawSlots_length]; decide) (by rw [rt_rawSlots_length]; decide)
  have hp : int 1 > int 0 := by decide
  simp only [Nat.zero_add, Int.natCast_one] at ha hl hw
  simp only [undef, List.forIn_nil, rc_run_bind, rc_run_pure, hc, hn, ha, hp,
    ite_true, hl, hw] <;> rfl

theorem rc_undef_zeros (runtime : AllocationData) (R : Nat) (s : State) :
    (undef runtime (⟨List.replicate R (int 0), List.length_replicate ..⟩ : Dims R)).run s =
      (.ok ⟨s.arrays.length, int (if R = 0 then 1 else 0),
        if R = 1 then [] else List.replicate R (int 0)⟩,
        rc_zeroMemory runtime R s) := by
  let dims : Dims R := ⟨List.replicate R (int 0), List.length_replicate ..⟩
  have hn : ∀ d ∈ dims.val, 0 ≤ d.val := (rc_zero_accepted R).1
  have hc := rc_checkedDims_run dims s
  have ha : ReshapeDimensionsChecked dims := Or.inr (rc_zero_accepted R)
  rw [if_pos ha] at hc
  have hp := rc_zero_product R
  change DimensionProduct dims.val = _ at hp
  rw [hp] at hc
  by_cases hr : R = 0
  · subst R
    change _ = (Except.ok (⟨s.arrays.length, int 1, []⟩ : BitArray 0),
      shiftFreshHeap s [some (u64 0)])
    exact rc_undef_rankZero runtime s
  · have hc0 : (checkedDims dims.val : BitMutationM I64).run s = (.ok (int 0), s) := by
      simpa only [hr, ite_false] using hc
    have h := rt_undef_zero_run runtime dims s hn hc0
    simpa only [hr, ite_false, rc_zeroMemory] using h

theorem rc_zero_storage (runtime : AllocationData) (R : Nat) (s : State) :
    ReshapeTemporaryStorage runtime R s (rc_zeroMemory runtime R s) := by
  unfold rc_zeroMemory
  by_cases hr : R = 0
  · rw [if_pos hr]
    refine ⟨?_, ?_, ⟨(s.memories.length, int 1), int 1⟩, ?_, rfl, ?_, ?_⟩
    · simp only [OldHeapPreserved, shiftFreshHeap, List.take_left, and_self]
    · simp only [shiftFreshHeap, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add]
    · exact shiftFreshHeader s [some (u64 0)]
    · simp only [hr, ite_true]
      rfl
    · simp only [hr, ite_true, shiftFreshHeap, List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, and_self]
  · rw [if_neg hr]
    refine ⟨?_, ?_, ⟨(runtime.emptyMemory, int 1), int 0⟩, ?_, rfl, ?_, ?_⟩
    · simp only [OldHeapPreserved, rt_emptyHeap, List.take_left, List.take_length, and_self]
    · simp only [rt_emptyHeap, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add]
    · simp only [rt_emptyHeap, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
    · simp only [hr, ite_false]
      rfl
    · simp only [hr, ite_false, rt_emptyHeap, and_self]

theorem rc_undefObject_zeros (runtime : AllocationData) (R : Nat) (state : ObjectState) :
    (undefObject runtime (⟨List.replicate R (int 0), List.length_replicate ..⟩ : Dims R)).run state =
      (.ok ⟨state.objects.length⟩,
        rc_addedState state (rc_zeroMemory runtime R state.memory)
          (⟨state.memory.arrays.length, int (if R = 0 then 1 else 0),
            if R = 1 then [] else List.replicate R (int 0)⟩ : BitArray R)) := by
  simp only [undefObject, rc_run_bind, rc_liftBit, rc_undef_zeros, rc_registerObject,
    rc_addedState]

theorem rc_bitreshape_invalid {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (dims : Dims R) (state : ObjectState) (hbad : ¬ ReshapeDimensionsChecked dims) :
    (bitreshape runtime source dims).run state =
      (.error (.argument "invalid Array dimensions"), state) := by
  have hcheck := rc_checkedDims_run dims state.memory
  rw [if_neg hbad] at hcheck
  simp only [bitreshape, rc_run_bind, rc_liftBit, hcheck]

theorem rc_bitreshape_mismatch {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims R) (state : ObjectState)
    (hobj : ObjectContains state source original) (hc : ReshapeDimensionsChecked dims)
    (hm : DimensionProduct dims.val ≠ original.len.val) :
    (bitreshape runtime source dims).run state =
      (.error (.dimensionMismatch "new dimensions must be consistent with array length"), state) := by
  have hcheck := rc_checkedDims_run dims state.memory
  rw [if_pos hc] at hcheck
  have hne : int (DimensionProduct dims.val) ≠ bitArrayLength original := by
    intro he
    have hv := congrArg Subtype.val he
    rw [rc_checked_product_val dims hc] at hv
    exact hm hv
  simp only [bitreshape, rc_run_bind, rc_liftBit, hcheck,
    rc_readObject state source original hobj, bne_iff_ne.mpr hne, ite_true, rc_run_throw]

theorem rc_bitreshape_success {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims R) (state : ObjectState)
    (hobj : ObjectContains state source original) (hc : ReshapeDimensionsChecked dims)
    (hm : DimensionProduct dims.val = original.len.val) :
    (bitreshape runtime source dims).run state =
      (.ok ⟨state.objects.length⟩,
        rc_addedState state (rc_zeroMemory runtime R state.memory)
          (⟨original.chunks, original.len, if R = 1 then [] else dims.val⟩ : BitArray R)) := by
  have hcheck := rc_checkedDims_run dims state.memory
  rw [if_pos hc] at hcheck
  have he : int (DimensionProduct dims.val) = original.len := by
    apply Subtype.ext
    rw [rc_checked_product_val dims hc, hm]
  rw [he] at hcheck
  simp only [bitreshape, rc_run_bind, rc_liftBit, hcheck,
    rc_readObject state source original hobj, bitArrayLength, bne_self_eq_false,
    Bool.false_eq_true, ite_false, rc_undefObject_zeros, rc_addedChunks, rc_addedLength]
  by_cases hr : R = 1
  · simp only [hr, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, rc_run_pure]
  · simp only [bne_iff_ne.mpr hr, hr, ite_true, ite_false, rc_run_bind,
      rc_addedDims, rc_run_pure]

theorem rc_reshape_size {N R : Nat} (original : BitArray N) (dims : Dims R)
    (hm : DimensionProduct dims.val = original.len.val) :
    bitArraySizeRanked (⟨original.chunks, original.len,
      if R = 1 then [] else dims.val⟩ : BitArray R) = dims.val := by
  unfold bitArraySizeRanked
  by_cases hr : R = 1
  · simp only [hr, ite_true]
    rcases dims with ⟨ds, hds⟩
    have hlen : ds.length = 1 := hds.trans hr
    cases ds with
    | nil => cases hlen
    | cons d ds =>
      cases ds with
      | nil =>
        have hd : d = original.len := by
          apply Subtype.ext
          simpa only [DimensionProduct, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil, Int.mul_one] using hm
        simp only [hd]
      | cons e rest => simp only [List.length_cons] at hlen; omega
  · simp only [hr, ite_false]

theorem rc_fresh_reshape_post {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims R) (state : ObjectState)
    (hobj : ObjectContains state source original)
    (hm : DimensionProduct dims.val = original.len.val) :
    FreshReshapePost runtime source original dims state
      (rc_addedState state (rc_zeroMemory runtime R state.memory)
        (⟨original.chunks, original.len, if R = 1 then [] else dims.val⟩ : BitArray R))
      ⟨state.objects.length⟩ := by
  have hlt := rc_source_identity_lt state source original hobj
  refine ⟨rfl, (by change state.objects.length ≠ source.identity; omega),
    ?_, ?_, rc_zero_storage runtime R state.memory, ?_⟩
  · simp only [rc_addedState, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add]
  · simp only [OldObjectsPreserved, rc_addedState, List.take_left]
  · refine ⟨⟨original.chunks, original.len, if R = 1 then [] else dims.val⟩,
      rc_addedContains _ _ _, rfl, rfl, hm.symm, rc_reshape_size original dims hm, rfl⟩

theorem Models1G15BitreshapeFreshAllocation_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.BitreshapeFreshAllocationAndErrors := by
  intro N R runtime source original dims state _ _ hobj _
  constructor
  · intro hbad
    rw [rc_bitreshape_invalid runtime source dims state hbad]
    exact ⟨rfl, rfl⟩
  · intro hc
    by_cases hm : DimensionProduct dims.val = original.len.val
    · rw [if_pos hm]
      intro _
      rw [rc_bitreshape_success runtime source original dims state hobj hc hm]
      exact ⟨⟨state.objects.length⟩, rfl,
        rc_fresh_reshape_post runtime source original dims state hobj hm⟩
    · rw [if_neg hm, rc_bitreshape_mismatch runtime source original dims state hobj hc hm]
      exact ⟨⟨"new dimensions must be consistent with array length", rfl⟩, rfl⟩
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

abbrev Heap := JuliaLean.base.array.MutableMemory U64

/-- Independent positional interpretation of packed bytes; no model getter is used. -/
def bitAt (s : Heap) {N : Nat} (B : BitArray N) (i : Nat) : Bool :=
  let w := ((s.contents B.chunks)[i / 64]?.getD none).getD (u64 0)
  decide ((w.val.toNat / 2 ^ (i % 64)) % 2 = 1)

def bits (s : Heap) {N : Nat} (B : BitArray N) : List Bool :=
  (List.range B.len.val.toNat).map (bitAt s B)

/-- Constructible native storage, including extra chunks and dirty padding reached
through shared-chunk aliases. Every actual UInt64 realization of undef bits is
included. The heap byte-size bound is the native eight-byte element allocation
limit, not a bound chosen to simplify a proof. Rank-one size is read from len. -/
def Readable {N : Nat} (s : Heap) (B : BitArray N) : Prop :=
  s.validVector B.chunks ∧
  0 ≤ B.len.val ∧
  N < 2 ^ 63 ∧
  (bitArraySizeRanked B).length = N ∧
  (∀ d ∈ bitArraySizeRanked B, 0 ≤ d.val) ∧
  (N ≠ 1 → ∀ d ∈ bitArraySizeRanked B, d.val < (2 : Int)^63 - 1) ∧
  ((bitArraySizeRanked B).map (fun d => d.val.toNat)).prod = B.len.val.toNat ∧
  (B.len.val.toNat + 63) / 64 ≤ (s.contents B.chunks).length ∧
  (∀ cell ∈ s.contents B.chunks, cell.isSome = true) ∧
  (∀ slots ∈ s.memories, slots.length < 2 ^ 60)

/-- The source's packed representation invariant (base/bitarray.jl:5-6).
This stronger predicate is used only for contracts that require a normally packed
vector; read-only and pointwise mapping contracts use Readable where possible. -/
def Packed {N : Nat} (s : Heap) (B : BitArray N) : Prop :=
  Readable s B ∧
  (s.contents B.chunks).length = (B.len.val.toNat + 63) / 64 ∧
  (∀ w, (s.contents B.chunks).getLast? = some (some w) →
    B.len.val.toNat % 64 ≠ 0 → w.val.toNat < 2 ^ (B.len.val.toNat % 64))

/-- Mathematical native conversion domain, independent of the implementation's
checked-conversion branch. -/
def FitsNative (n : Int) : Prop := -(2 : Int)^63 ≤ n ∧ n < (2 : Int)^63

instance (n : Int) : Decidable (FitsNative n) := by
  unfold FitsNative
  infer_instance


/-- Allocation may append objects, but it must not change any pre-existing
memory or header, including all aliases of the source. -/
def PreservesExisting (s after : Heap) : Prop :=
  after.arrays.take s.arrays.length = s.arrays ∧
  after.memories.take s.memories.length = s.memories

/-- The physical cells belonging to a mutable chunk-vector view. -/
def InChunkWindow (s : Heap) (handle memory cell : Nat) : Prop :=
  ∃ header, s.arrays[handle]? = some header ∧ header.reference.1 = memory ∧
    header.reference.2.val - 1 ≤ (cell : Int) ∧
    (cell : Int) < header.reference.2.val - 1 + header.size.val

/-- A map! may mutate only cells in its destination's physical window; headers,
allocation identities, and every other cell remain unchanged, even on failure. -/
def MutationFrame (s after : Heap) (handle : Nat) : Prop :=
  after.arrays = s.arrays ∧ after.memories.length = s.memories.length ∧
  ∀ memory cell, ¬ InChunkWindow s handle memory cell →
    (after.memories[memory]?.getD [])[cell]? = (s.memories[memory]?.getD [])[cell]?

/-- Nonoverlapping windows, or windows with the same start and logical extent.
The latter explicitly includes in-place maps and rank-changing shared-storage
views. Shifted partial overlaps retain the executable source behavior but have
no snapshot-value promise, as warned by the map! documentation.
Source: base/abstractarray.jl:3563-3568; base/Base_compiler.jl:222-225. -/
def SnapshotSafe {D N : Nat} (s : Heap) (dest : BitArray D) (A : BitArray N) : Prop :=
  match s.arrays[dest.chunks]?, s.arrays[A.chunks]? with
  | some d, some a =>
      d.reference.1 ≠ a.reference.1 ∨
      d.reference.2.val - 1 + d.size.val ≤ a.reference.2.val - 1 ∨
      a.reference.2.val - 1 + a.size.val ≤ d.reference.2.val - 1 ∨
      (d.reference.2 = a.reference.2 ∧ dest.len = A.len)
  | _, _ => False
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group16


def countAliasHeap : Heap := ⟨[[some (u64 2)]], [⟨(0, int 1), int 1⟩]⟩

def countAliasArray : BitArray 2 := ⟨0, int 1, [int 1, int 1]⟩

theorem countAliasReadable : Readable countAliasHeap countAliasArray := by
  unfold Readable countAliasHeap countAliasArray
  decide
end JuliaLean.ChatGPT.Batch9.Group10

