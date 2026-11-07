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

set_option maxRecDepth 4096

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

theorem equalityPublicShape{N : Nat} (xs : List Bool) (dims : List I64)
    (hrank : dims.length = N) (hnonneg : ∀ d ∈ dims, int 0 ≤ d)
    (hnat : dims.foldl (fun total d => total * d.val.toNat) 1 = xs.length)
    (hbound : xs.length ≤ 9223372036854775807) :
    bitArraySizeRanked (⟨0, int xs.length, dims⟩ : BitArray N) = dims := by
  unfold bitArraySizeRanked
  split
  · rename_i hone
    have hrankOne : dims.length = 1 := hrank.trans hone
    cases dims with
    | nil => simp at hrankOne
    | cons d tail =>
      cases tail with
      | cons e rest => simp at hrankOne
      | nil =>
        have hd : 0 ≤ d.val := hnonneg d (by simp)
        have hlen : d.val.toNat = xs.length := by simpa using hnat
        have hval : d.val = (xs.length : Int) := by omega
        have heq : d = int xs.length := by
          apply Subtype.ext
          rw [packedInt_val xs.length hbound]
          exact hval
        simp [heq]
  · rfl

/-- Public shapes decide the unequal-shape branch without inspecting memory. -/
theorem equalityDifferentDims {N M : Nat} (a : BitArray N) (b : BitArray M)
    (chunkEqual : Nat → Nat → BitMutationM Bool) (s : State)
    (h : bitArraySizeRanked a ≠ bitArraySizeRanked b) :
    (bitArrayEqual chunkEqual a b).run s = (.ok false, s) := by
  have hb : (bitArraySizeRanked a != bitArraySizeRanked b) = true := bne_iff_ne.mpr h
  simp only [bitArrayEqual, bitArrayEqualWith, hb, ite_true]
  rfl

/-- Equal-length logical bit sequences are determined by their packed words. -/
theorem packedEncodingInjectiveOfLength (xs ys : List Bool)
    (hlen : xs.length = ys.length) (henc : encodeBits xs = encodeBits ys) : xs = ys := by
  apply List.ext_getElem
  · exact hlen
  · intro i hi hj
    have hc : i / 64 < wordCount xs.length := by
      unfold wordCount
      omega
    have hcy : i / 64 < wordCount ys.length := by
      rw [← hlen]
      exact hc
    have he := congrArg (fun words : List U64 => words[i / 64]?) henc
    simp only [packedPrefix_eq_encode, List.getElem?_map, List.getElem?_range,
      hc, hcy, ite_true, Option.map_some] at he
    have hp : packedPrefix xs (i / 64) 64 = packedPrefix ys (i / 64) 64 :=
      Option.some.inj he
    have hb := congrArg (fun word => packedBit word (i % 64)) hp
    rw [packedWord_bit xs (i / 64) (i % 64) (Nat.mod_lt _ (by decide)),
      packedWord_bit ys (i / 64) (i % 64) (Nat.mod_lt _ (by decide))] at hb
    have hindex : i / 64 * 64 + i % 64 = i := by omega
    rw [hindex, ← List.getElem_eq_getD (h := hi),
      ← List.getElem_eq_getD (h := hj)] at hb
    exact hb
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- The specialized equality loop never creates a missing-value result. -/
def equalityStep (pair : Option U64 × Option U64)
    (acc : Option (Option Bool) × Bool) :
    BitMutationM (ForInStep (Option (Option Bool) × Bool)) := do
  let eq ← (pure (pair.1 == pair.2) : BitMutationM Bool)
  let ne ← (pure (!eq) : BitMutationM Bool)
  if ne then pure (.done (some (some false), acc.2))
  else pure (.yield (none, acc.2))

/-- Executing the list loop records failure precisely when a pair differs. -/
theorem equalityLoopRun (pairs : List (Option U64 × Option U64)) (s : State) :
    (forIn pairs (none, false) equalityStep).run s =
      (.ok ((if pairs.all (fun pair => pair.1 == pair.2) then none
        else some (some false)), false), s) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨a, b⟩
      by_cases hab : a = b
      · subst b
        simp only [List.forIn_cons, equalityStep, beq_self_eq_true,
          Bool.false_eq_true, ite_false, shape_run_bind, shape_run_pure,
          Bool.not_true, ih, List.all_cons, Bool.true_and]
      · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr hab
        simp only [List.forIn_cons, equalityStep, hb,
          Bool.false_eq_true, ite_false, shape_run_bind, shape_run_pure,
          Bool.not_false, ite_true, List.all_cons, Bool.false_and]

/-- For lists of equal length, pairwise equality is equivalent to list equality. -/
theorem equalityZipAll (xs ys : List (Option U64)) (hlen : xs.length = ys.length) :
    (xs.zip ys).all (fun pair => pair.1 == pair.2) = (xs == ys) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
      cases ys with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y ys =>
          have hl : xs.length = ys.length := Nat.succ.inj hlen
          simp only [List.zip_cons_cons, List.all_cons, ih ys hl]
          rfl

/-- The imported public array-equality model computes ordinary list equality. -/
theorem equalityArrayRun (xs ys : List (Option U64)) (s : State) :
    (JuliaLean.base.abstractarray.arrayEqual
      (fun chunks : List (Option U64) => (pure chunks.length : BitMutationM Nat))
      (fun chunks : List (Option U64) => (pure chunks.length : BitMutationM Nat))
      (fun a b => pure (List.zip a b))
      (fun a b => pure (a == b))
      (fun _ => false) (fun equal => pure (!equal)) xs ys).run s =
      (.ok (some (xs == ys)), s) := by
  by_cases hlen : xs.length = ys.length
  · have hlenb : (xs.length != ys.length) = false := by
      simp only [hlen, bne_self_eq_false]
    simp only [JuliaLean.base.abstractarray.arrayEqual, shape_run_bind,
      shape_run_pure, hlenb, Bool.false_eq_true, ite_false]
    have hloop := equalityLoopRun (xs.zip ys) s
    unfold equalityStep at hloop
    rw [hloop, equalityZipAll xs ys hlen]
    cases h : xs == ys <;> rfl
  · have hlenb : (xs.length != ys.length) = true := bne_iff_ne.mpr hlen
    have hxy : xs ≠ ys := fun he => hlen (congrArg List.length he)
    have hxyb : (xs == ys) = false := beq_eq_false_iff_ne.mpr hxy
    simp only [JuliaLean.base.abstractarray.arrayEqual, shape_run_bind,
      shape_run_pure, hlenb, ite_true, hxyb]

/-- The chunk comparison wrapper observes exactly the two logical chunk lists. -/
theorem equalityChunksRun (s : State) (left right : Nat) (t : State) :
    (Round5.Round2.bitArrayChunkEqualPublic s left right).run t =
      (.ok (s.contents left == s.contents right), t) := by
  simp only [Round5.Round2.bitArrayChunkEqualPublic, shape_run_bind,
    equalityArrayRun, Option.getD_some, shape_run_pure]

/-- The second vector of a two-vector store exposes exactly its initialized words. -/
theorem equalityInitialRight (xs ys : List U64)
    (hy : ys.length ≤ 9223372036854775807) :
    (MutableMemory.initialMany [xs.map some, ys.map some]).contents 1 = ys.map some := by
  have hv : (JInt.wrap .i64 (ys.map some).length).val.toNat = ys.length := by
    rw [List.length_map]
    change (int (ys.length : Int)).val.toNat = ys.length
    rw [packedInt_val ys.length hy, Int.toNat_natCast]
  change ((ys.map some ++ List.replicate 32 none).drop 0).take
    (JInt.wrap .i64 (ys.map some).length).val.toNat = ys.map some
  rw [List.drop_zero, hv]
  have hn : ys.length = (ys.map some).length := (List.length_map _).symm
  rw [hn, List.take_left]

/-- Wrapping initialized words in `some` preserves equality of their sequences. -/
theorem equalitySomeMap (xs ys : List U64) :
    xs.map some = ys.map some ↔ xs = ys := by
  constructor
  · intro h
    have h' := congrArg (List.map (fun value : Option U64 => value.getD (u64 0))) h
    simp only [List.map_map, Function.comp_def, Option.getD_some] at h'
    change xs.map id = ys.map id at h'
    simpa only [List.map_id] using h'
  · intro h
    rw [h]

/-- Exact frozen equality target: dimensions and packed logical contents agree. -/
theorem BitarrayBitArrayEqualityAgrees_proven :
    JuliaLean.Proofs.base.bitarray.Round5.BitArrayEqualityAgrees := by
  intro N M xs ys dimsA dimsB hRankA hRankB hDimsA hDimsB hSizeA hSizeB hNatA hNatB hx hy
  have hbx : xs.length ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hx
    omega
  have hby : ys.length ≤ 9223372036854775807 := by
    change ys.length < 4611686018427387903 at hy
    omega
  have hwx : (encodeBits xs).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound xs hbx
  have hwy : (encodeBits ys).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound ys hby
  have hshapeA : bitArraySizeRanked (⟨0, int xs.length, dimsA⟩ : BitArray N) = dimsA :=
    equalityPublicShape xs dimsA hRankA hDimsA hNatA hbx
  have hshapeB : bitArraySizeRanked (⟨1, int ys.length, dimsB⟩ : BitArray M) = dimsB :=
    equalityPublicShape ys dimsB hRankB hDimsB hNatB hby
  unfold Round5.Round2.BitArrayEqualityAgrees
  dsimp only
  by_cases hd : dimsA = dimsB
  · subst dimsB
    have hlen : xs.length = ys.length := hNatA.symm.trans hNatB
    have he : ((encodeBits xs).map some == (encodeBits ys).map some) = decide (xs = ys) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, equalitySomeMap]
      constructor
      · intro hp
        exact packedEncodingInjectiveOfLength xs ys hlen hp
      · intro hp
        rw [hp]
    have hr := equalityChunksRun
      (MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]) 0 1
      (MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some])
    rw [equalityInitialLeft (encodeBits xs) (encodeBits ys) hwx,
      equalityInitialRight (encodeBits xs) (encodeBits ys) hwy, he] at hr
    simp only [bitArrayEqual, bitArrayEqualWith, hshapeA, hshapeB, bne_self_eq_false, Bool.false_eq_true, ite_false,
      hr, true_and]
  · have hdb : (dimsA != dimsB) = true := bne_iff_ne.mpr hd
    simp only [bitArrayEqual, bitArrayEqualWith, hshapeA, hshapeB, hdb, ite_true, shape_run_pure, hd, false_and, decide_false]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

/-- Exact ceiling division for every nonnegative native logical length. -/
theorem BitarrayBitArrayChunkCount_proven : JuliaLean.Proofs.base.bitarray.BitArrayChunkCount := by
  intro n hn
  rw [JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1.scalar_num_chunks n hn]
  change (n.val + 63) / 64 = (((n.val.toNat + 63) / 64 : Nat) : Int)
  omega
end JuliaLean.ChatGPT.Batch4.Group8
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

def unary_word (bit : Bool) : U64 := if bit then u64Max else u64 0

def unary_cell (bit : Bool) : Option U64 := some (unary_word bit)

def unary_slots (xs : List Bool) (done : Nat) : List (Option U64) :=
  (xs.take done).map unary_cell ++ List.replicate (xs.length - done) none

def unary_state (xs : List Bool) (done : Nat) : State :=
  shiftFreshHeap (initWords (encodeBits xs)) (unary_slots xs done)

theorem unary_slots_length (xs : List Bool) (done : Nat) (hd : done ≤ xs.length) :
    (unary_slots xs done).length = xs.length := by
  simp only [unary_slots, List.length_append, List.length_map, List.length_take,
    Nat.min_eq_left hd, List.length_replicate]
  omega

theorem unary_slots_next (xs : List Bool) (done : Nat) (hd : done < xs.length) :
    (unary_slots xs done).set done (unary_cell (xs.getD done false)) =
      unary_slots xs (done + 1) := by
  have hp : ((xs.take done).map unary_cell).length = done := by
    simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hd)]
  have hn : xs.length - done = (xs.length - (done + 1)) + 1 := by omega
  unfold unary_slots
  rw [List.set_append_right _ _ (by omega), hp, Nat.sub_self, hn,
    List.replicate_succ, List.set_cons_zero, List.take_succ_eq_append_getElem hd,
    List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rw [List.getElem_eq_getD]
  rfl

/-- A unary output store changes only its next destination element. -/
theorem unary_store_run (xs : List Bool) (done : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hd : done < xs.length) :
    (mutableSet 1 (unary_word (xs.getD done false)) (int ((done + 1 : Nat) : Int))).run
      (unary_state xs done) = (.ok (), unary_state xs (done + 1)) := by
  have hw := shiftFreshSet (initWords (encodeBits xs)) (unary_slots xs done) done
    (unary_word (xs.getD done false))
    (by rw [unary_slots_length xs done (by omega)]; exact hn)
    (by rw [unary_slots_length xs done (by omega)]; exact hd)
  have hs : (unary_slots xs done).set done (some (unary_word (xs.getD done false))) =
      unary_slots xs (done + 1) := unary_slots_next xs done hd
  rw [hs] at hw
  exact hw

/-- Appended output cells never alter the source chunk being scanned. -/
theorem unary_source_chunk (xs : List Bool) (done chunk : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : chunk < wordCount xs.length) :
    (mutableGet 0 (int ((chunk + 1 : Nat) : Int))).run (unary_state xs done) =
      (.ok (packedPrefix xs chunk 64), unary_state xs done) := by
  have hchunk : chunk < (encodeBits xs).length := by rw [packedEncoded_length]; exact hc
  have hr := shiftFreshSource (encodeBits xs) (unary_slots xs done) chunk
    (packedEncoded_lengthBound xs hn) hchunk
  have hword : (encodeBits xs).getD chunk (u64 0) = packedPrefix xs chunk 64 := by
    rw [← List.getElem_eq_getD (h := hchunk)]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [hword] at hr
  exact hr

def unary_mask (bit : Nat) : U64 := shl_int (u64 1) (int bit)

/-- The 64 mask transitions include the final shift to zero. -/
theorem unary_mask_next (bit : Nat) (hb : bit < 64) :
    shl_int (unary_mask bit) (u64 1) = unary_mask (bit + 1) := by
  have h : ∀ bit : Fin 64,
      shl_int (unary_mask bit.val) (u64 1) = unary_mask (bit.val + 1) := by decide
  exact h ⟨bit, hb⟩

theorem unary_mask_start : unary_mask 0 = u64 1 := by decide

/-- One iteration of the packed unary-minus bit loop. -/
def unary_step (word : U64) (current : I64 × U64) : BitMutationM (ForInStep (I64 × U64)) := do
  if and_int word current.2 != u64 0 then
    mutableSet 1 (u64 (int (-1)).val) current.1
  else mutableSet 1 (u64 (int 0).val) current.1
  pure (.yield (current.1 + int 1, shl_int current.2 (u64 1)))

theorem unary_step_from (word mask : U64) (index : I64) (bit : Bool) (s out : State)
    (ht : (and_int word mask != u64 0) = bit)
    (hw : (mutableSet 1 (unary_word bit) index).run s = (.ok (), out)) :
    (unary_step word (index, mask)).run s =
      (.ok (.yield (index + int 1, shl_int mask (u64 1))), out) := by
  unfold unary_step
  rw [ht]
  cases bit with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      change ((do mutableSet 1 (unary_word false) index
                  pure (.yield (index + int 1, shl_int mask (u64 1)))) :
        BitMutationM (ForInStep (I64 × U64))).run s = _
      rw [shape_run_bind, hw]
      rfl
  | true =>
      simp only [ite_true]
      change ((do mutableSet 1 (unary_word true) index
                  pure (.yield (index + int 1, shl_int mask (u64 1)))) :
        BitMutationM (ForInStep (I64 × U64))).run s = _
      rw [shape_run_bind, hw]
      rfl

/-- Each packed bit produces exactly zero or negative one in the fresh array. -/
theorem unary_step_run (xs : List Bool) (chunk bit : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hb : bit < 64)
    (hi : chunk * 64 + bit < xs.length) :
    (unary_step (packedPrefix xs chunk 64)
      (int ((chunk * 64 + bit + 1 : Nat) : Int), unary_mask bit)).run
      (unary_state xs (chunk * 64 + bit)) =
      (.ok (.yield (int ((chunk * 64 + (bit + 1) + 1 : Nat) : Int), unary_mask (bit + 1))),
        unary_state xs (chunk * 64 + (bit + 1))) := by
  have ht : (and_int (packedPrefix xs chunk 64) (unary_mask bit) != u64 0) =
      xs.getD (chunk * 64 + bit) false := by
    rw [unary_mask, scalar_mask_test _ bit hb, packedWord_bit xs chunk bit hb]
  have hw := unary_store_run xs (chunk * 64 + bit) hn hi
  have hr := unary_step_from (packedPrefix xs chunk 64) (unary_mask bit)
    (int ((chunk * 64 + bit + 1 : Nat) : Int)) (xs.getD (chunk * 64 + bit) false)
    (unary_state xs (chunk * 64 + bit)) (unary_state xs (chunk * 64 + bit + 1)) ht hw
  have hc : int ((chunk * 64 + bit + 1 : Nat) : Int) + int 1 =
      int ((chunk * 64 + (bit + 1) + 1 : Nat) : Int) := by
    rw [packedInt_add]
    congr 1
  rw [hc, unary_mask_next bit hb] at hr
  simpa only [Nat.add_assoc] using hr

/-- The bit loop depends only on the number of indices it visits. -/
theorem unary_forIn_count (indices : List I64) (count : Nat) (hlen : indices.length = count)
    (initial : I64 × U64) (word : U64) :
    forIn indices initial (fun _ current => unary_step word current) =
      forIn (List.range count) initial (fun _ current => unary_step word current) := by
  have hleft :
      forIn (indices.map (fun _ => ())) initial (fun (_ : Unit) current => unary_step word current) =
        forIn indices initial (fun _ current => unary_step word current) := List.forIn_map
  have hright :
      forIn ((List.range count).map (fun _ => ())) initial
        (fun (_ : Unit) current => unary_step word current) =
        forIn (List.range count) initial (fun _ current => unary_step word current) := List.forIn_map
  simp only [List.map_const', hlen, List.length_range] at hleft hright
  exact hleft.symm.trans hright

/-- A complete or partial source word produces precisely its corresponding output cells. -/
theorem unary_inner_count_run (xs : List Bool) (chunk count : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count ≤ 64)
    (hi : chunk * 64 + count ≤ xs.length) :
    (forIn (List.range count)
      (int ((chunk * 64 + 1 : Nat) : Int), u64 1)
      (fun _ current => unary_step (packedPrefix xs chunk 64) current)).run
        (unary_state xs (chunk * 64)) =
      (.ok (int ((chunk * 64 + count + 1 : Nat) : Int), unary_mask count),
        unary_state xs (chunk * 64 + count)) := by
  have h := concat_range_loop 0 count count
    (fun bit => (int ((chunk * 64 + bit + 1 : Nat) : Int), unary_mask bit))
    (fun bit => unary_state xs (chunk * 64 + bit))
    (fun _ current => unary_step (packedPrefix xs chunk 64) current)
    (by intro bit hb; exact unary_step_run xs chunk bit hn (by omega) (by omega)) (by omega)
  simpa only [← List.range_eq_range', Nat.zero_add, Nat.add_zero, unary_mask_start] using h

theorem unary_inner_run (xs : List Bool) (chunk count : Nat) (indices : List I64)
    (hlen : indices.length = count) (hn : xs.length ≤ 9223372036854775807)
    (hc : count ≤ 64) (hi : chunk * 64 + count ≤ xs.length) :
    (forIn indices (int ((chunk * 64 + 1 : Nat) : Int), u64 1)
      (fun _ current => unary_step (packedPrefix xs chunk 64) current)).run
        (unary_state xs (chunk * 64)) =
      (.ok (int ((chunk * 64 + count + 1 : Nat) : Int), unary_mask count),
        unary_state xs (chunk * 64 + count)) := by
  have he := unary_forIn_count indices count hlen
    (int ((chunk * 64 + 1 : Nat) : Int), u64 1) (packedPrefix xs chunk 64)
  exact (congrArg (fun action : BitMutationM (I64 × U64) => action.run
    (unary_state xs (chunk * 64))) he).trans (unary_inner_count_run xs chunk count hn hc hi)

def unary_full_step_with (indices : List I64) (index cursor : I64) :
    BitMutationM (ForInStep I64) := do
  let word ← mutableGet 0 index
  let result ← forIn indices (cursor, u64 1) (fun _ current => unary_step word current)
  pure (.yield result.1)

def unary_full_step (index cursor : I64) : BitMutationM (ForInStep I64) :=
  unary_full_step_with (intRange (int 1) (int 64)) index cursor

theorem unary_full_from_runs (indices : List I64) (index cursor next : I64)
    (word mask : U64) (s out : State)
    (hr : (mutableGet 0 index).run s = (.ok word, s))
    (hi : (forIn indices (cursor, u64 1) (fun _ current => unary_step word current)).run s =
      (.ok (next, mask), out)) :
    (unary_full_step_with indices index cursor).run s = (.ok (.yield next), out) := by
  simp only [unary_full_step_with, shape_run_bind, hr, hi, shape_run_pure]

theorem unary_full_step_run (xs : List Bool) (chunk : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hi : chunk * 64 + 64 ≤ xs.length) :
    (unary_full_step (int ((chunk + 1 : Nat) : Int))
      (int ((chunk * 64 + 1 : Nat) : Int))).run (unary_state xs (chunk * 64)) =
      (.ok (.yield (int (((chunk + 1) * 64 + 1 : Nat) : Int))),
        unary_state xs ((chunk + 1) * 64)) := by
  have hchunk : chunk < wordCount xs.length := by unfold wordCount; omega
  have hr := unary_source_chunk xs (chunk * 64) chunk hn hchunk
  have hlen : (intRange (int 1) (int 64)).length = 64 := by decide
  have hb := unary_inner_run xs chunk 64 (intRange (int 1) (int 64)) hlen hn (by omega) hi
  have h := unary_full_from_runs (intRange (int 1) (int 64))
    (int ((chunk + 1 : Nat) : Int)) (int ((chunk * 64 + 1 : Nat) : Int))
    (int ((chunk * 64 + 64 + 1 : Nat) : Int))
    (packedPrefix xs chunk 64) (unary_mask 64) _ _ hr hb
  have he : chunk * 64 + 64 = (chunk + 1) * 64 := by omega
  rw [he] at h
  exact h

/-- The outer loop scans each complete source chunk once. -/
theorem unary_full_loop_run (xs : List Bool) (hp : 0 < xs.length)
    (hn : xs.length ≤ 9223372036854775807) :
    (forIn (intRange (int 1) (int (wordCount xs.length) - int 1)) (int 1)
      unary_full_step).run (unary_state xs 0) =
      (.ok (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int)),
        unary_state xs ((wordCount xs.length - 1) * 64)) := by
  have hpos : 0 < wordCount xs.length := by unfold wordCount; omega
  have hsub : int (wordCount xs.length) - int 1 =
      int ((wordCount xs.length - 1 : Nat) : Int) := by
    rw [concat_int_sub]
    apply congrArg int
    omega
  have hbound : wordCount xs.length - 1 ≤ 9223372036854775807 := by unfold wordCount; omega
  rw [hsub, packedObserve_intRange _ hbound, List.forIn_map]
  have h := concat_range_loop 0 (wordCount xs.length - 1) (wordCount xs.length - 1)
    (fun chunk => int ((chunk * 64 + 1 : Nat) : Int))
    (fun chunk => unary_state xs (chunk * 64))
    (fun chunk cursor => unary_full_step (int ((chunk + 1 : Nat) : Int)) cursor)
    (by
      intro chunk hc
      exact unary_full_step_run xs chunk hn (by unfold wordCount at hc; omega)) (by omega)
  simpa only [← List.range_eq_range', Nat.zero_add, Nat.zero_mul, Int.natCast_one] using h

/-- The final native range visits exactly the logical bits in the last chunk. -/
theorem unary_tail_range_length (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    (intRange (int 0) (mod64 (int n - int 1))).length = abs_tail_count n := by
  have hs : int n - int 1 = int ((n - 1 : Nat) : Int) := by
    rw [concat_int_sub]
    apply congrArg int
    omega
  rw [hs]
  simp only [intRange, List.length_map, List.length_range, scalar_mod64_val,
    packedInt_val (n - 1) (by omega)]
  change (((((n - 1 : Nat) : Int) % 64) - 0 + 1).toNat) = abs_tail_count n
  unfold abs_tail_count
  omega

def unary_tail_with (indices : List I64) (index cursor : I64) : BitMutationM Nat := do
  let word ← mutableGet 0 index
  let _ ← forIn indices (cursor, u64 1) (fun _ current => unary_step word current)
  pure 1

theorem unary_tail_from_runs (indices : List I64) (index cursor next : I64)
    (word mask : U64) (s out : State)
    (hr : (mutableGet 0 index).run s = (.ok word, s))
    (hi : (forIn indices (cursor, u64 1) (fun _ current => unary_step word current)).run s =
      (.ok (next, mask), out)) :
    (unary_tail_with indices index cursor).run s = (.ok 1, out) := by
  simp only [unary_tail_with, shape_run_bind, hr, hi, shape_run_pure]

theorem unary_tail_run (xs : List Bool) (hp : 0 < xs.length)
    (hn : xs.length ≤ 9223372036854775807) :
    (unary_tail_with (intRange (int 0) (mod64 (int xs.length - int 1)))
      (int (wordCount xs.length)) (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int))).run
      (unary_state xs ((wordCount xs.length - 1) * 64)) =
      (.ok 1, unary_state xs xs.length) := by
  have hc := abs_tail_counts xs.length hp
  have hlast : wordCount xs.length - 1 < wordCount xs.length := by unfold wordCount; omega
  have hidx : wordCount xs.length - 1 + 1 = wordCount xs.length := by omega
  have hr := unary_source_chunk xs ((wordCount xs.length - 1) * 64)
    (wordCount xs.length - 1) hn hlast
  rw [hidx] at hr
  have hi := unary_inner_run xs (wordCount xs.length - 1) (abs_tail_count xs.length)
    (intRange (int 0) (mod64 (int xs.length - int 1)))
    (unary_tail_range_length xs.length hp hn) hn hc.2.1 (by omega)
  rw [hc.2.2] at hi
  exact unary_tail_from_runs _ _ _ _ (packedPrefix xs (wordCount xs.length - 1) 64)
    (unary_mask (abs_tail_count xs.length)) _ _ hr hi

def unary_scan_body (nc : I64) (tailIndices : List I64) : BitMutationM Nat := do
  let cursor ← forIn (intRange (int 1) (nc - int 1)) (int 1) unary_full_step
  unary_tail_with tailIndices nc cursor

theorem unary_scan_from_runs (nc cursor : I64) (tailIndices : List I64) (s middle out : State)
    (hfull : (forIn (intRange (int 1) (nc - int 1)) (int 1) unary_full_step).run s =
      (.ok cursor, middle))
    (htail : (unary_tail_with tailIndices nc cursor).run middle = (.ok 1, out)) :
    (unary_scan_body nc tailIndices).run s = (.ok 1, out) := by
  simp only [unary_scan_body, shape_run_bind, hfull]
  exact htail

theorem unary_scan_run (xs : List Bool) (hp : 0 < xs.length)
    (hn : xs.length ≤ 9223372036854775807) :
    (unary_scan_body (int (wordCount xs.length))
      (intRange (int 0) (mod64 (int xs.length - int 1)))).run (unary_state xs 0) =
      (.ok 1, unary_state xs xs.length) :=
  unary_scan_from_runs _ _ _ _ _ _ (unary_full_loop_run xs hp hn) (unary_tail_run xs hp hn)

def unary_allocate (dims : List I64) : BitMutationM Nat :=
  mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1))

@[irreducible] def unary_program (xs : List Bool) : BitMutationM Nat :=
  bitArrayUnaryMinus unary_allocate (fun _ => int xs.length)
    (fun handle i value => mutableSet handle (u64 value.val) i) (vectorBits xs)

theorem unary_allocate_run (xs : List Bool) (hn : xs.length ≤ 576460752303423488) :
    (unary_allocate [int xs.length]).run (initWords (encodeBits xs)) =
      (.ok 1, unary_state xs 0) := by
  have hmul : int 1 * int xs.length = int xs.length := by
    apply Subtype.ext
    change wrapInt .i64 (1 * (int xs.length).val) = (int xs.length).val
    rw [Int.one_mul]
    exact JuliaLean.Proofs.base.int.wrapInt_val _
  have ha := shiftFreshAllocate (initWords (encodeBits xs)) xs.length hn
  simp only [unary_allocate, List.foldl_cons, List.foldl_nil, hmul]
  simpa only [allocateChunkVectorModel, Int.ofNat_eq_natCast, unary_state, unary_slots,
    List.take_zero, List.map_nil, Nat.sub_zero, List.nil_append,
    show (initWords (encodeBits xs)).arrays.length = 1 from rfl] using ha

theorem unary_source_length (xs : List Bool) :
    (mutableLength 0).run (unary_state xs 0) =
      (.ok (int (wordCount xs.length)), unary_state xs 0) := by
  have h := shiftFreshSourceLength (encodeBits xs) (unary_slots xs 0)
  rw [packedEncoded_length] at h
  exact h

/-- Allocation and the native source scan compose without unfolding concrete storage. -/
theorem unary_model_from_runs (allocate : List I64 → BitMutationM Nat)
    (len nc : I64) (dims : List I64) (s allocated out : State)
    (ha : (allocate dims).run s = (.ok 1, allocated))
    (hz : (len == int 0) = false)
    (hc : (mutableLength 0).run allocated = (.ok nc, allocated))
    (hb : (unary_scan_body nc (intRange (int 0) (mod64 (len - int 1)))).run allocated =
      (.ok 1, out)) :
    (bitArrayUnaryMinus allocate (fun _ => len)
      (fun handle i value => mutableSet handle (u64 value.val) i)
      (⟨0, len, dims⟩ : BitVector)).run s = (.ok 1, out) := by
  simp only [bitArrayUnaryMinus, shape_run_bind, ha, hz, Bool.false_eq_true, ite_false, hc]
  unfold unary_scan_body unary_full_step unary_full_step_with unary_tail_with unary_step at hb
  simpa only [shape_run_bind] using hb

theorem unary_model_empty (allocate : List I64 → BitMutationM Nat)
    (dims : List I64) (s out : State)
    (ha : (allocate dims).run s = (.ok 1, out)) :
    (bitArrayUnaryMinus allocate (fun _ => int 0)
      (fun handle i value => mutableSet handle (u64 value.val) i)
      (⟨0, int 0, dims⟩ : BitVector)).run s = (.ok 1, out) := by
  simp only [bitArrayUnaryMinus, shape_run_bind, ha, beq_self_eq_true, ite_true, shape_run_pure]

/-- Unary minus completely initializes its result with the integer encoding of each bit. -/
theorem unary_program_run (xs : List Bool) (hn : xs.length ≤ 576460752303423488) :
    (unary_program xs).run (initWords (encodeBits xs)) =
      (.ok 1, unary_state xs xs.length) := by
  unfold unary_program
  have hnative : xs.length ≤ 9223372036854775807 := by omega
  have ha := unary_allocate_run xs hn
  by_cases hp : 0 < xs.length
  · have hz : (int xs.length == int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have hv := congrArg Subtype.val he
      rw [packedInt_val xs.length hnative] at hv
      change (xs.length : Int) = 0 at hv
      omega
    exact unary_model_from_runs unary_allocate (int xs.length) (int (wordCount xs.length))
      [int xs.length] _ _ _ ha hz (unary_source_length xs) (unary_scan_run xs hp hnative)
  · have he : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => simp only [List.length_cons] at hp; omega
    subst xs
    exact unary_model_empty unary_allocate [int 0] _ _ ha

theorem unary_contents_complete (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    (unary_state xs xs.length).contents 1 = xs.map unary_cell := by
  have h := shiftFreshContents (initWords (encodeBits xs)) (unary_slots xs xs.length)
    (by rw [unary_slots_length xs xs.length (Nat.le_refl _)]; exact hn)
  simpa only [unary_state, unary_slots, List.take_length, Nat.sub_self,
    List.replicate_zero, List.append_nil,
    show (initWords (encodeBits xs)).arrays.length = 1 from rfl] using h

def unary_observation (xs : List Bool) (result : Except Error Nat × State) : Prop :=
  match result.1 with
  | .ok output => (List.range xs.length).all fun i => (result.2.contents output)[i]? =
      some (some (if xs.getD i false then u64Max else u64 0))
  | .error _ => False

/-- Observation of a completed output follows from its contents and successful run. -/
theorem unary_observation_of_run (xs : List Bool) (program : BitMutationM Nat)
    (s out : State) (hr : program.run s = (.ok 1, out))
    (hc : out.contents 1 = xs.map unary_cell) :
    unary_observation xs (program.run s) := by
  rw [hr]
  change ((List.range xs.length).all fun i =>
    (out.contents 1)[i]? =
      some (some (if xs.getD i false then u64Max else u64 0))) = true
  rw [hc]
  apply List.all_eq_true.mpr
  intro i hi
  have hindex : i < xs.length := List.mem_range.mp hi
  apply decide_eq_true
  rw [List.getElem?_map, List.getElem?_eq_getElem hindex]
  simp only [Option.map_some, unary_cell, unary_word]
  rw [List.getElem_eq_getD]

/-- The frozen unary-minus observation holds under an explicit successful-allocation bound. -/
theorem unary_bounded (xs : List Bool) (hn : xs.length ≤ 576460752303423488) :
    unary_observation xs ((unary_program xs).run (initWords (encodeBits xs))) :=
  unary_observation_of_run xs (unary_program xs) (initWords (encodeBits xs))
    (unary_state xs xs.length) (unary_program_run xs hn)
    (unary_contents_complete xs (by omega))

/-- Allocation of the frozen zero-filled matrix initializes its only word. -/
theorem mhcat_allocate_single_from (rows columns length : I64) (handle : Nat)
    (s allocated finished : State) (hmul : rows * columns = length)
    (hc : numBitChunks length = int 1)
    (ha : (mutableAllocate (some ⟨8, false, false⟩) 0 (int 1)).run s = (.ok handle, allocated))
    (hl : (mutableLength handle).run allocated = (.ok (int 1), allocated))
    (hw : (mutableSet handle (u64 0) (int 1)).run allocated = (.ok (), finished)) :
    (allocateMatrix rows columns).run s =
      (.ok (⟨handle, length, [rows, columns]⟩ : BitMatrix), finished) := by
  have hrange : intRange (int 1) (int 1) = [int 1] := by decide
  simp only [allocateMatrix, hmul, hc, shape_run_bind, ha, hl, hrange,
    List.forIn_cons, List.forIn_nil, hw, shape_run_pure]

theorem mhcat_allocate_single (rows columns : I64) (n : Nat) (s : State)
    (hmul : rows * columns = int n) (hp : 0 < n) (hn : n ≤ 64) :
    (allocateMatrix rows columns).run s =
      (.ok (⟨s.arrays.length, int n, [rows, columns]⟩ : BitMatrix), concat_extend s (u64 0)) := by
  have ha := concat_allocate_chunk s
  have hl := shiftSingleLengthFrom (shiftFreshHeap s [none]) s.arrays.length s.memories.length
    (int 1) (shiftFreshHeader s [none])
  have hw := shiftFreshSet s [none] 0 (u64 0) (by decide) (by decide)
  exact mhcat_allocate_single_from rows columns (int n) s.arrays.length s _ _ hmul
    (concat_num_chunks n hp hn) ha hl hw

theorem mhcat_packed_empty : packedPrefix [] 0 64 = u64 0 := by
  apply (packedWord_zero_iff [] 0).mpr
  intro bit _
  rfl

/-- Matrix hcat joins both inputs correctly whenever the declared product is their one-word total. -/
theorem mhcat_pair_single_run (rows columnsLeft columnsRight : I64) (left right : List Bool)
    (hp : 0 < left.length + right.length) (hn : left.length + right.length ≤ 64)
    (hshape : rows * (columnsLeft + columnsRight) = int ((left.length + right.length : Nat) : Int)) :
    (mhcat_pair rows columnsLeft columnsRight (int left.length) (int right.length) allocateMatrix).run
      (concat_initial [left, right]) =
      (.ok (⟨2, int ((left.length + right.length : Nat) : Int),
        [rows, columnsLeft + columnsRight]⟩ : BitMatrix),
        concat_extend (concat_initial [left, right]) (packedPrefix (left ++ right) 0 64)) := by
  have hlready := concat_initial_ready [left, right] (left, 0)
    (by change (left, 0) ∈ [(left, 0), (right, 1)]; exact List.mem_cons_self)
    (by change left.length ≤ 64; omega)
  have hrready := concat_initial_ready [left, right] (right, 1)
    (by change (right, 1) ∈ [(left, 0), (right, 1)]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    (by change right.length ≤ 64; omega)
  have ha := mhcat_allocate_single rows (columnsLeft + columnsRight)
    (left.length + right.length) (concat_initial [left, right]) hshape hp hn
  have hl := concat_copy_append_ready (left, 0) [] (concat_initial [left, right]) hlready
    (by simpa only [List.length_nil, Nat.zero_add] using (show left.length ≤ 64 by omega))
  simp only [List.length_nil, Nat.zero_add, Int.natCast_one, List.nil_append, mhcat_packed_empty] at hl
  have hr := concat_copy_append_ready (right, 1) left (concat_initial [left, right]) hrready hn
  have hi : int 1 + int left.length = int ((left.length + 1 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  rw [← hi] at hr
  exact mhcat_pair_from_runs rows columnsLeft columnsRight (int left.length) (int right.length)
    allocateMatrix _ _ _ _ _ ha hl hr

/-- Native multiplication agrees with the natural product before the final wrap. -/
theorem mhcat_native_mul (rows columns : Nat)
    (hr : rows ≤ 9223372036854775807) (hc : columns ≤ 9223372036854775807) :
    int rows * int columns = int ((rows * columns : Nat) : Int) := by
  apply Subtype.ext
  change wrapInt .i64 ((int rows).val * (int columns).val) =
    wrapInt .i64 ((rows * columns : Nat) : Int)
  rw [packedInt_val rows hr, packedInt_val columns hc, Int.natCast_mul]

/-- Valid nonempty matrices satisfy the exact hcat observation when the combined bits fit one word. -/
theorem mhcat_matrix_hcat_single_chunk (rows : Nat) (left right : List Bool)
    (hr : 0 < rows) (he : left.length = right.length) (hd : rows ∣ left.length)
    (hp : 0 < left.length) (hn : left.length + right.length ≤ 64) :
    mhcat_observation rows left right
      ((mhcat_pair (int rows) (int (left.length / rows)) (int (right.length / rows))
        (int left.length) (int right.length) allocateMatrix).run (concat_initial [left, right])) := by
  have hleft : rows * (left.length / rows) = left.length := Nat.mul_div_cancel_left' hd
  have hright : rows * (right.length / rows) = right.length := by rw [← he]; exact hleft
  have hproduct : rows * (left.length / rows + right.length / rows) =
      left.length + right.length := by rw [Nat.mul_add, hleft, hright]
  have hquotient : left.length / rows + right.length / rows =
      (left.length + right.length) / rows := by
    have h := Nat.mul_div_cancel_left (left.length / rows + right.length / rows) hr
    rw [hproduct] at h
    exact h.symm
  have hcolumns : int (left.length / rows) + int (right.length / rows) =
      int ((left.length / rows + right.length / rows : Nat) : Int) := by
    rw [packedInt_add, Int.natCast_add, Int.natCast_ediv, Int.natCast_ediv]
  have hrowbound : rows ≤ 64 := by
    have hq : 0 < left.length / rows := by
      by_cases hz : left.length / rows = 0
      · rw [hz, Nat.mul_zero] at hleft
        omega
      · exact Nat.pos_of_ne_zero hz
    have hb := Nat.mul_le_mul_left rows (show 1 ≤ left.length / rows by omega)
    rw [Nat.mul_one, hleft] at hb
    omega
  have hcolbound : left.length / rows + right.length / rows ≤ 64 := by
    have hl := Nat.div_le_self left.length rows
    have hr' := Nat.div_le_self right.length rows
    omega
  have hshape : int rows * (int (left.length / rows) + int (right.length / rows)) =
      int ((left.length + right.length : Nat) : Int) := by
    rw [hcolumns, mhcat_native_mul rows _ (by omega) (by omega), hproduct]
  have hrun := mhcat_pair_single_run (int rows) (int (left.length / rows))
    (int (right.length / rows)) left right (by omega) hn hshape
  have hbits := concat_word_bitValues (N := 2) (concat_initial [left, right]) (left ++ right)
    [int rows, int (left.length / rows) + int (right.length / rows)]
    (by simpa only [List.length_append] using hn)
  simp only [List.length_append] at hbits
  apply mhcat_observe_from rows left right _ _ _ _ hrun
  · change [int rows, int (left.length / rows) + int (right.length / rows)] = _
    rw [hcolumns, hquotient]
    rw [Int.natCast_ediv, Int.natCast_add]
  · exact hbits
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Every selected position removes exactly one element from the remaining logical suffix. -/
theorem ctor_mask_blocks_length (xs : List Bool) (selected : List Nat) (start : Nat)
    (hordered : selected.Pairwise (· < ·)) (hstart : start ≤ xs.length)
    (hvalid : ∀ i ∈ selected, start ≤ i ∧ i < xs.length) :
    (scan_maskDelete_blocks xs selected start).length + selected.length = xs.length - start := by
  induction selected generalizing start with
  | nil => simp only [scan_maskDelete_blocks, List.length_drop, List.length_nil, Nat.add_zero]
  | cons i rest ih =>
    have hi := hvalid i List.mem_cons_self
    have hp := List.pairwise_cons.mp hordered
    have hrest : ∀ j ∈ rest, i + 1 ≤ j ∧ j < xs.length := by
      intro j hj
      have ho := hp.1 j hj
      have hv := hvalid j (List.mem_cons_of_mem i hj)
      omega
    have ht := ih (i + 1) hp.2 (by omega) hrest
    have hslice : ((xs.drop start).take (i - start)).length = i - start := by
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
    rw [scan_maskDelete_blocks, List.length_append, hslice, List.length_cons]
    omega

/-- The retained block count is the original suffix length minus the number of selections. -/
theorem ctor_mask_blocks_length_eq (xs : List Bool) (selected : List Nat) (start : Nat)
    (hordered : selected.Pairwise (· < ·)) (hstart : start ≤ xs.length)
    (hvalid : ∀ i ∈ selected, start ≤ i ∧ i < xs.length) :
    (scan_maskDelete_blocks xs selected start).length = xs.length - start - selected.length := by
  have h := ctor_mask_blocks_length xs selected start hordered hstart hvalid
  omega

/-- A strictly ascending valid selection has at most one entry per source position. -/
theorem ctor_mask_positions_length (xs : List Bool) (selected : List Nat)
    (hordered : selected.Pairwise (· < ·)) (hvalid : ∀ i ∈ selected, i < xs.length) :
    selected.length ≤ xs.length := by
  have h := ctor_mask_blocks_length xs selected 0 hordered (Nat.zero_le _)
    (by intro i hi; exact ⟨Nat.zero_le _, hvalid i hi⟩)
  omega
end JuliaLean.ChatGPT.Batch5.Group2
end

section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch5.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean.C JuliaLean.base.int

/-- The scalar chunk-read target holds at every constructible native list length. -/
theorem b5ChunkReadNative (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hi : int 1 ≤ i) (hl : i ≤ int xs.length) :
    ((unsafeBitGetIndex (vectorBits xs).chunks i).run (initWords (encodeBits xs))).1 =
      .ok (bitAt (initWords (encodeBits xs)) (vectorBits xs) (i.val.toNat - 1)) := by
  obtain ⟨hj, hei⟩ := scalar_valid_index_coordinates xs i hn ⟨hi, hl⟩
  have hr := scalar_read_initial xs (i.val.toNat - 1) hn hj
  have hb := scalar_bitAt_initial (N := 1) xs [int xs.length]
    (i.val.toNat - 1) hn hj
  change ((unsafeBitGetIndex 0 i).run (initWords (encodeBits xs))).1 = _
  have hr' := (congrArg (fun k : I64 =>
    (unsafeBitGetIndex 0 k).run (initWords (encodeBits xs))) hei).trans hr
  rw [hr']
  exact congrArg (fun b : Bool => (Except.ok b : Except Error Bool)) hb.symm
end JuliaLean.ChatGPT.Batch5.Group1
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

/-- The three independent initialized allocations in the frozen map proposition. -/
def b5MapStore (dest left right : List U64) : State :=
  ⟨[dest.map some ++ List.replicate 32 none,
    left.map some ++ List.replicate 32 none,
    right.map some ++ List.replicate 32 none],
   [⟨(0, one), int dest.length⟩, ⟨(1, one), int left.length⟩,
    ⟨(2, one), int right.length⟩]⟩

theorem b5MapStoreInitial (dest left right : List U64) :
    MutableMemory.initialMany [dest.map some, left.map some, right.map some] =
      b5MapStore dest left right := by
  change MutableMemory.mk _
    [⟨(0, one), int (dest.map some).length⟩,
      ⟨(1, one), int (left.map some).length⟩,
      ⟨(2, one), int (right.map some).length⟩] = _
  simp only [List.length_map]
  rfl

theorem b5MapLengthLeft (dest left right : List U64) :
    (mutableLength 1).run (b5MapStore dest left right) =
      (.ok (int left.length), b5MapStore dest left right) := rfl

theorem b5MapLengthRight (dest left right : List U64) :
    (mutableLength 2).run (b5MapStore dest left right) =
      (.ok (int right.length), b5MapStore dest left right) := rfl

theorem b5MapReadDest (dest left right : List U64) (j : Nat)
    (hn : dest.length ≤ 9223372036854775807) (hj : j < dest.length) :
    (mutableGet 0 (int ((j + 1 : Nat) : Int))).run (b5MapStore dest left right) =
      (.ok (dest.getD j (u64 0)), b5MapStore dest left right) := by
  have h := cmp_read_initialized (b5MapStore dest left right) 0 0 dest hn rfl rfl j hj
  rw [List.getElem_eq_getD] at h
  exact h

theorem b5MapReadLeft (dest left right : List U64) (j : Nat)
    (hn : left.length ≤ 9223372036854775807) (hj : j < left.length) :
    (mutableGet 1 (int ((j + 1 : Nat) : Int))).run (b5MapStore dest left right) =
      (.ok (left.getD j (u64 0)), b5MapStore dest left right) := by
  have h := cmp_read_initialized (b5MapStore dest left right) 1 1 left hn rfl rfl j hj
  rw [List.getElem_eq_getD] at h
  exact h

theorem b5MapReadRight (dest left right : List U64) (j : Nat)
    (hn : right.length ≤ 9223372036854775807) (hj : j < right.length) :
    (mutableGet 2 (int ((j + 1 : Nat) : Int))).run (b5MapStore dest left right) =
      (.ok (right.getD j (u64 0)), b5MapStore dest left right) := by
  have h := cmp_read_initialized (b5MapStore dest left right) 2 2 right hn rfl rfl j hj
  rw [List.getElem_eq_getD] at h
  exact h

/-- A destination update retains both source allocations and every header. -/
theorem b5MapWriteDest (dest left right : List U64) (j : Nat) (value : U64)
    (hn : dest.length ≤ 9223372036854775807) (hj : j < dest.length) :
    (mutableSet 0 value (int ((j + 1 : Nat) : Int))).run (b5MapStore dest left right) =
      (.ok (), b5MapStore (dest.set j value) left right) := by
  have hsize := packedInt_val dest.length hn
  have hindex := packedInt_val (j + 1) (by omega)
  have haddress : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by
    rw [hindex]
    omega
  have hraw := metadataSetRaw (b5MapStore dest left right)
    (dest.map some ++ List.replicate 32 none) (int dest.length)
    (int ((j + 1 : Nat) : Int)) value rfl rfl
    (by rw [hsize]; simp only [List.length_append, List.length_map, List.length_replicate]; omega)
    (by rw [hindex, hsize]; omega)
  have hslots : (dest.map some ++ List.replicate 32 none).set j (some value) =
      (dest.set j value).map some ++ List.replicate 32 none := by
    rw [List.set_append_left _ _ (by simpa only [List.length_map] using hj),
      ← List.map_set]
  rw [hraw, haddress]
  simp only [b5MapStore, List.set_cons_zero, hslots, List.length_set]

theorem b5MapContents (dest left right : List U64)
    (hn : dest.length ≤ 9223372036854775807) :
    (b5MapStore dest left right).contents 0 = dest.map some := by
  rw [resizeContentsRaw (b5MapStore dest left right)
    (dest.map some ++ List.replicate 32 none) 0 dest.length rfl rfl hn]
  exact List.take_left' (List.length_map ..)

/-- A logical negation changes the default only outside the list's valid indices. -/
theorem b5MapNotGet (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (xs.map (!·)).getD i false = !(xs.getD i false) := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

/-- The false default distributes through Boolean conjunction even beyond either input. -/
theorem b5MapAndGet (xs ys : List Bool) (i : Nat) :
    (List.zipWith (· && ·) xs ys).getD i false =
      (xs.getD i false && ys.getD i false) := by
  induction xs generalizing ys i with
  | nil => simp only [List.zipWith_nil_left, List.getD_nil, Bool.false_and]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.zipWith_nil_right, List.getD_nil, Bool.and_false]
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => exact ih ys i

/-- Every complete source word may be negated without a padding adjustment. -/
theorem b5MapNotBefore (xs : List Bool) (chunk : Nat)
    (hc : chunk + 1 < wordCount xs.length) :
    not_int (packedPrefix xs chunk 64) = packedPrefix (xs.map (!·)) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [scalar_packedBit_not _ k hk, packedWord_bit xs chunk k hk,
    packedWord_bit (xs.map (!·)) chunk k hk,
    b5MapNotGet xs (chunk * 64 + k) (by unfold wordCount at hc; omega)]

/-- Masked negation of the final word is the exact zero-padded logical encoding. -/
theorem b5MapNotLast (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    and_int (not_int (packedPrefix xs (wordCount xs.length - 1) 64))
      (maskEnd (int xs.length)) =
      packedPrefix (xs.map (!·)) (wordCount xs.length - 1) 64 := by
  apply packedBit_ext
  intro k hk
  rw [scalar_packedBit_and, scalar_packedBit_not _ k hk,
    packedWord_bit xs _ k hk, packedWord_bit (xs.map (!·)) _ k hk,
    packedMask_last_bit xs.length k hp hn]
  by_cases hi : (wordCount xs.length - 1) * 64 + k < xs.length
  · rw [b5MapNotGet xs _ hi, decide_eq_true hi, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        simp only [List.length_map]
        omega), Option.getD_none]

/-- Conjunction of packed words is the packed logical conjunction. -/
theorem b5MapAndWord (xs ys : List Bool) (chunk : Nat) :
    and_int (packedPrefix xs chunk 64) (packedPrefix ys chunk 64) =
      packedPrefix (List.zipWith (· && ·) xs ys) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [scalar_packedBit_and, packedWord_bit xs chunk k hk,
    packedWord_bit ys chunk k hk,
    packedWord_bit (List.zipWith (· && ·) xs ys) chunk k hk, b5MapAndGet]

/-- The final mask preserves any correctly encoded word at that logical length. -/
theorem b5MapMaskLast (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    and_int (packedPrefix xs (wordCount xs.length - 1) 64) (maskEnd (int xs.length)) =
      packedPrefix xs (wordCount xs.length - 1) 64 := by
  have h := resizeTakeWordLast xs xs.length hp hn
  rw [List.take_length] at h
  exact h

/-- Indexed word writes preserve the visible destination length. -/
theorem b5MapFoldLength (indices : List Nat) (dest : List U64) (value : Nat → U64) :
    (indices.foldl (fun ws j => ws.set j (value j)) dest).length = dest.length := by
  induction indices generalizing dest with
  | nil => rfl
  | cons i indices ih => rw [List.foldl_cons, ih, List.length_set]

/-- An indexed-write fold changes exactly the visited destination words. -/
theorem b5MapFoldGet (indices : List Nat) (value : Nat → U64) :
    ∀ (dest : List U64), (∀ i ∈ indices, i < dest.length) → ∀ j : Nat,
    (indices.foldl (fun ws i => ws.set i (value i)) dest).getD j (u64 0) =
      if j ∈ indices then value j else dest.getD j (u64 0) := by
  induction indices with
  | nil =>
    intro dest _ j
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons i indices ih =>
    intro dest hi j
    have hib := hi i List.mem_cons_self
    have hr := ih (dest.set i (value i))
      (by intro k hk; rw [List.length_set]; exact hi k (List.mem_cons_of_mem i hk)) j
    rw [List.foldl_cons, hr]
    by_cases hj : j ∈ indices
    · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
    · rw [if_neg hj, dequeWordGetSet dest i j (value i) hib]
      by_cases he : i = j
      · subst j
        rw [if_pos rfl, if_pos List.mem_cons_self]
      · have hnot : ¬ j ∈ i :: indices := by
          intro hmem
          rcases List.mem_cons.mp hmem with hmem | hmem
          · exact he hmem.symm
          · exact hj hmem
        rw [if_neg he, if_neg hnot]

/-- Completing a prefix-write loop with the final word constructs the requested full list. -/
theorem b5MapFoldFinish (dest wanted : List U64) (value : Nat → U64)
    (hp : 0 < dest.length) (hlen : dest.length = wanted.length)
    (hbefore : ∀ j, j + 1 < dest.length → value j = wanted.getD j (u64 0)) :
    ((List.range (dest.length - 1)).foldl (fun ws j => ws.set j (value j)) dest).set
      (dest.length - 1) (wanted.getD (dest.length - 1) (u64 0)) = wanted := by
  let stage := (List.range (dest.length - 1)).foldl (fun ws j => ws.set j (value j)) dest
  have hstage : stage.length = dest.length := b5MapFoldLength _ _ _
  apply List.ext_getElem
  · rw [List.length_set, b5MapFoldLength, hlen]
  · intro j hj hj'
    have hb : j < dest.length := by simpa only [List.length_set, b5MapFoldLength] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0)]
    change (stage.set (dest.length - 1) _).getD j (u64 0) = _
    rw [dequeWordGetSet stage (dest.length - 1) j _ (by rw [hstage]; omega)]
    by_cases he : dest.length - 1 = j
    · rw [if_pos he, he]
    · rw [if_neg he]
      dsimp only [stage]
      rw [b5MapFoldGet _ value dest (by intro i hi; have := List.mem_range.mp hi; omega),
        if_pos (List.mem_range.mpr (by omega))]
      exact hbefore j (by omega)
end JuliaLean.ChatGPT.Batch5.Group1
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

/-- Native square identity execution composes size, construction and assignment. -/
theorem mtx_one_from_runs (s initialized out : State) (B A : BitMatrix) (n : I64)
    (hd : B.dims = [n, n])
    (hfalses : (matrixFalses [n, n]).run s = (.ok A, initialized))
    (hloop : (forIn (intRange (int 1) n) PUnit.unit (fun i _ => do
      let _ ← matrixSet A true [i, i]
      pure (ForInStep.yield PUnit.unit))).run initialized = (.ok PUnit.unit, out)) :
    (oneMatrix B).run s = (.ok A, out) := by
  unfold oneMatrix bitMatrixOne
  rw [shape_run_bind, mtx_read_dimensions s B n n hd]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  erw [mtx_run_bind_ok hfalses]
  erw [mtx_run_bind_ok hloop]
  rfl
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

/-- Bool push retains the original object identity and the global frame, with
native wrapping in the length field. If no chunk growth is needed, the wrapped
length is committed before any possible final scalar-write error. Arbitrary
source chunk states and aliases are included in this mutation-order contract.
Julia source: base/bitarray.jl:739-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:1326-1349; native wrapping/error-order invariant.
Useful partial result: Bool item specialization only. -/
def PushBoolFrameAndCommittedLength : Prop :=
  ∀ (runtime : AllocationData) (target : Ref 1) (B : BitVector) (item : Bool)
    (state : ObjectState), ObjectContains state target B →
    let result := (JuliaLean.base.bitarray.Models1Group15.pushBool runtime target item).run state
    let newLength := int (B.len.val + 1)
    VectorMutationFrame state result.2 target B newLength ∧
    (match result.1 with
     | .ok returned => returned = target ∧
         ∃ updated : BitVector, ObjectContains result.2 target updated ∧ updated.len = newLength
     | .error _ => True) ∧
    (B.len.val % 64 ≠ 0 →
      ∃ updated : BitVector, ObjectContains result.2 target updated ∧ updated.len = newLength)

/-- On ordinary native packed input, Bool push appends exactly the supplied
Boolean, preserves preceding bits and zero padding, and returns the same object.
Every native capacity and offset is included; too-large runtime growth is a
specified no-mutation ArgumentError, not an excluded small-bound case.
Julia source: base/bitarray.jl:739-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:1326-1349; base/bitarray.jl:1-23 (padding).
Useful partial result: Bool item specialization; typemax length is covered by
PushBoolNativeLengthWrap below rather than hidden by this nonoverflow branch. -/
def PushBoolAppendOneAndNativeLimits : Prop :=
  ∀ (runtime : AllocationData) (target : Ref 1) (B : BitVector) (item : Bool)
    (state : ObjectState), ObjectContains state target B →
    AllocationInput runtime state.memory → NativeRawChunkMemory state.memory →
    ConsistentPackedArray state.memory B → B.len.val < IntTy.max .i64 →
    let result := (JuliaLean.base.bitarray.Models1Group15.pushBool runtime target item).run state
    if GrowthExceedsNativeByteLimit state.memory B.chunks ((B.len.val.toNat + 1 + 63) / 64) then
      result.1 = .error (.argument JuliaLean.base.array.genericMemorySizeMessage) ∧ result.2 = state
    else result.1 = .ok target ∧
      ∃ updated : BitVector, ObjectContains result.2 target updated ∧
        updated.len.val = B.len.val + 1 ∧ updated.chunks = B.chunks ∧ updated.dims = B.dims ∧
        ConsistentPackedArray result.2.memory updated ∧
        PackedBitValue result.2.memory updated B.len.val.toNat = some (if item then 1 else 0) ∧
        (∀ position : Nat, position < B.len.val.toNat →
          PackedBitValue result.2.memory updated position = PackedBitValue state.memory B position)

/-- Independent physical outcome of the write reached after native length wrap.
The wrapped predecessor is typemax(Int), so the addressed one-based chunk is
2^57 and the bit is 63. Missing headers, short windows and absent cells are
bounds failures; an explicit unassigned raw cell is undefinedReference. A
readable cell permits the write exactly when its one-based backing position
is positive and representable. The extra checks retain the installed raw
boundary's behavior on malformed headers as well as all native valid windows.
No allocation, setter model or correctness premise defines the expected result. -/
def WrappedPushStorageOutcome (before after : MutableMemory U64) (chunks : Nat)
    (target : Ref 1) (returned : Except JuliaLean.base.array.Error (Ref 1)) : Prop :=
  let chunk : Int := (2 : Int) ^ 57
  let boundsFailure := returned = .error .bounds ∧ after = before
  match before.arrays[chunks]? with
  | none => boundsFailure
  | some header =>
      if header.size.val < chunk then boundsFailure
      else match before.memories[header.reference.1]? with
        | none => boundsFailure
        | some slots =>
            let position := header.reference.2.val + chunk - 1
            match slots[(position - 1).toNat]? with
            | none => boundsFailure
            | some none => returned = .error .undefinedReference ∧ after = before
            | some (some _) =>
                if 1 ≤ position ∧ position ≤ IntTy.max .i64 ∧
                    position ≤ (slots.length : Int) then
                  returned = .ok target ∧
                  ∃ word : U64, SingleStoredBitWrite before after header.reference.1
                    (position - 1).toNat 63 true word
                else boundsFailure

/-- The source's unchecked increment at native maximum length wraps the stored
length to typemin before any subsequent error. False returns without accessing
chunks. For true, the specialized rank-one unchecked OneTo axis uses unsigned
bounds comparison and accepts the wrapped typemin index; the packed setter then
addresses chunk 2^57, bit 63. Sufficient readable physical backing therefore
succeeds and changes exactly that bit. Short or missing storage raises the
installed boundary's BoundsError, while explicit raw unassigned markers give
undefinedReference. Every case preserves other object headers and commits the
wrapped target length; failures leave the backing heap unchanged.
All capacities are included, with no small-size restriction. In particular,
2^57 UInt64 words occupy 2^60 bytes, below the native raw-memory size bound.
This is an extreme source-behavior invariant, not an asserted documented
correctness promise or a runtime-confirmed Julia bug.
Julia source: base/bitarray.jl:122,675-692,745-754;
base/abstractarray.jl:100-103,141,396,753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Useful partial result: Bool-valued push only. -/
def PushBoolNativeLengthWrap : Prop :=
  ∀ (runtime : AllocationData) (target : Ref 1) (B : BitVector) (item : Bool)
    (state : ObjectState), ObjectContains state target B → B.len.val = IntTy.max .i64 →
    let result := (JuliaLean.base.bitarray.Models1Group15.pushBool runtime target item).run state
    (if item then WrappedPushStorageOutcome state.memory result.2.memory B.chunks target result.1
     else result.1 = .ok target ∧ result.2.memory = state.memory) ∧
    result.2.objects.length = state.objects.length ∧
    (∀ identity : Nat, identity ≠ target.identity → result.2.objects[identity]? = state.objects[identity]?) ∧
    ∃ updated : BitVector, ObjectContains result.2 target updated ∧
      updated.len.val = IntTy.min .i64 ∧ updated.chunks = B.chunks ∧ updated.dims = B.dims
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.ChatGPT.Batch3.Group1

theorem bh_mask_quotient (r : Int) (hr0 : 0 ≤ r) (hr64 : r < 64) :
    wrapInt .u64 ((18446744073709551615 : Int) / (2 : Int) ^ ((-r) % 64).toNat) =
      (2 : Int) ^ (if r = 0 then 64 else r.toNat) - 1 := by
  have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 ∨ r = 32 ∨ r = 33 ∨ r = 34 ∨ r = 35 ∨ r = 36 ∨ r = 37 ∨ r = 38 ∨ r = 39 ∨ r = 40 ∨ r = 41 ∨ r = 42 ∨ r = 43 ∨ r = 44 ∨ r = 45 ∨ r = 46 ∨ r = 47 ∨ r = 48 ∨ r = 49 ∨ r = 50 ∨ r = 51 ∨ r = 52 ∨ r = 53 ∨ r = 54 ∨ r = 55 ∨ r = 56 ∨ r = 57 ∨ r = 58 ∨ r = 59 ∨ r = 60 ∨ r = 61 ∨ r = 62 ∨ r = 63 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide

theorem bh_mask_val (length : I64) :
    (maskEnd length).val =
      (2 : Int) ^ (if length.val % 64 = 0 then 64 else (length.val % 64).toNat) - 1 := by
  have hneg : (-length).val % 64 = (-length.val) % 64 := by
    change (((-length.val + 9223372036854775808) % 18446744073709551616 -
      9223372036854775808) % 64) = (-length.val) % 64
    omega
  have hmod0 : 0 ≤ (mod64 (-length)).val := by
    rw [scalar_mod64_val]
    exact Int.emod_nonneg _ (by decide)
  rw [maskEnd, JuliaLean.Proofs.base.int.lshr_int_val,
    JuliaLean.Proofs.base.int.pattern_of_nonneg _ hmod0, scalar_mod64_val, hneg]
  change wrapInt .u64 ((18446744073709551615 : Int) / (2 : Int) ^ ((-length.val) % 64).toNat) = _
  have hrem : (-length.val) % 64 = (-(length.val % 64)) % 64 := by omega
  rw [hrem]
  exact bh_mask_quotient _ (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide))
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray.Models1Group15
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.array

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem sp_object_set_contains {N : Nat} (state : ObjectState) (reference : Ref N)
    (old header : BitArray N) (h : ObjectContains state reference old) :
    ObjectContains {state with objects := state.objects.set reference.identity ⟨N, header⟩}
      reference header := by
  have hlt : reference.identity < state.objects.length :=
    (List.getElem?_eq_some_iff.mp h).choose
  exact List.getElem?_set_self hlt

theorem sp_setObjectLength_run {N : Nat} (state : ObjectState) (reference : Ref N)
    (old : BitArray N) (length : I64) (h : ObjectContains state reference old) :
    (setObjectLength reference length).run state =
      (.ok (), {state with objects := (state.objects.set reference.identity
        ⟨N, {old with len := length}⟩)}) := by
  simp only [setObjectLength, rc_run_bind, rc_readObject state reference old h,
    rc_writeObject state reference old _ h]

theorem sp_push_noGrowth_run (runtime : AllocationData) (target : Ref 1)
    (B : BitVector) (item : Bool) (state : ObjectState)
    (hobj : ObjectContains state target B) (hmod : B.len.val % 64 ≠ 0) :
    let updated : BitVector := {B with len := B.len + int 1}
    let committed : ObjectState :=
      {state with objects := state.objects.set target.identity ⟨1, updated⟩}
    (pushBool runtime target item).run state =
      if item then
        let result := (setIndexBool updated true updated.len).run state.memory
        (result.1.map (fun _ => target), {committed with memory := result.2})
      else (.ok target, committed) := by
  dsimp only
  have hne : (mod64 (bitArrayLength B) == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [JuliaLean.ChatGPT.Batch3.Group1.scalar_mod64_val] at hv
    exact hmod hv
  have hnew := sp_object_set_contains state target B {B with len := B.len + int 1} hobj
  simp only [pushBool, JuliaLean.base.number.convertSame, rc_run_bind,
    rc_readObject state target B hobj, hne, Bool.false_eq_true, ite_false, rc_run_pure,
    sp_setObjectLength_run state target B (B.len + int 1) hobj]
  cases item
  · rfl
  · simp only [ite_true, rc_run_bind, rc_readObject _ target _ hnew, rc_liftBit,
      bitArrayLength]
    cases hr : (setIndexBool {B with len := B.len + int 1} true (B.len + int 1)).run state.memory with
    | mk result memory => cases result <;> rfl

theorem sp_wrappedAddress : getChunksId (int (-9223372036854775808)) =
    (int 144115188075855872, int 63) := by decide

theorem sp_wrappedPosition (off : I64) :
    (off + int 144115188075855872 - one).val =
      wrapInt .i64 (off.val + 144115188075855872 - 1) := by
  change wrapInt .i64 (wrapInt .i64 (off.val + 144115188075855872) - 1) = _
  exact JuliaLean.Proofs.base.int.wrapInt_sub_left .i64 _ 1

theorem sp_wrappedPosition_check (off : I64) (length : Nat) :
    (1 ≤ (off + int 144115188075855872 - one).val ∧
      (off + int 144115188075855872 - one).val ≤ (length : Int)) ↔
    (1 ≤ off.val + 144115188075855872 - 1 ∧
      off.val + 144115188075855872 - 1 ≤ IntTy.max .i64 ∧
      off.val + 144115188075855872 - 1 ≤ (length : Int)) := by
  rw [sp_wrappedPosition]
  have hb := off.property
  change -9223372036854775808 ≤ off.val ∧ off.val ≤ 9223372036854775807 at hb
  change (1 ≤ (off.val + 144115188075855872 - 1 + 9223372036854775808) %
      18446744073709551616 - 9223372036854775808 ∧
    (off.val + 144115188075855872 - 1 + 9223372036854775808) %
      18446744073709551616 - 9223372036854775808 ≤ (length : Int)) ↔
    (1 ≤ off.val + 144115188075855872 - 1 ∧
      off.val + 144115188075855872 - 1 ≤ 9223372036854775807 ∧
      off.val + 144115188075855872 - 1 ≤ (length : Int))
  omega

theorem sp_wrappedSetter_run (s : MutableMemory U64) (chunks : Nat) :
    (unsafeBitSetIndex chunks true (int (-9223372036854775808))).run s =
      match s.arrays[chunks]? with
      | none => (.error .bounds, s)
      | some header =>
          if header.size.val < 144115188075855872 then (.error .bounds, s)
          else match s.memories[header.reference.1]? with
            | none => (.error .bounds, s)
            | some slots =>
                let position := header.reference.2.val + 144115188075855872 - 1
                match slots[(position - 1).toNat]? with
                | none => (.error .bounds, s)
                | some none => (.error .undefinedReference, s)
                | some (some old) =>
                    if 1 ≤ position ∧ position ≤ IntTy.max .i64 ∧
                        position ≤ (slots.length : Int) then
                      (.ok (), {s with memories := (s.memories.set header.reference.1
                        (slots.set (position - 1).toNat
                          (some (or_int old (shl_int (u64 1) (int 63))))))})
                    else (.error .bounds, s) := by
  have hc : (int 144115188075855872).val = 144115188075855872 := by decide
  simp only [unsafeBitSetIndex, sp_wrappedAddress, unsafeBitSetIndexAt, stateExcept_bind,
    sp_mutableGet_run, hc, ite_true]
  cases ha : s.arrays[chunks]? with
  | none => rfl
  | some header =>
      by_cases hsize : header.size.val < 144115188075855872
      · have hno : ¬ (1 ≤ (144115188075855872 : Int) ∧ 144115188075855872 ≤ header.size.val) := by omega
        simp only [hsize, hno, ite_false, ite_true]
      · have hyes : 1 ≤ (144115188075855872 : Int) ∧ 144115188075855872 ≤ header.size.val := by omega
        simp only [hsize, hyes, and_self, ite_true, ite_false]
        cases hm : s.memories[header.reference.1]? with
        | none => rfl
        | some slots =>
            have haddr : header.reference.2.val + 144115188075855872 - 2 =
                header.reference.2.val + 144115188075855872 - 1 - 1 := by omega
            simp only [haddr]
            cases hread : slots[(header.reference.2.val + 144115188075855872 - 1 - 1).toNat]? with
            | none => simp only [hread]
            | some cell =>
                cases cell with
                | none => simp only [hread]
                | some old =>
                    simp only [hread, sp_mutableSet_run, ha, hc, hyes, and_self, ite_true, hm]
                    simp only [sp_wrappedPosition_check]
                    by_cases hp : 1 ≤ header.reference.2.val + 144115188075855872 - 1 ∧
                        header.reference.2.val + 144115188075855872 - 1 ≤ IntTy.max .i64 ∧
                        header.reference.2.val + 144115188075855872 - 1 ≤ (slots.length : Int)
                    · have hpos : (header.reference.2 + int 144115188075855872 - one).val =
                          header.reference.2.val + 144115188075855872 - 1 := by
                        rw [sp_wrappedPosition]
                        exact wrapInt_of_inRange .i64 _ ⟨by change -9223372036854775808 ≤ _; omega, hp.2.1⟩
                      simp only [hp, and_self, ite_true, hpos]
                    · simp only [hp, ite_false]

theorem sp_wrappedWriteOutcome (s : MutableMemory U64) (chunks : Nat) (target : Ref 1) :
    let result := (unsafeBitSetIndex chunks true (int (-9223372036854775808))).run s
    WrappedPushStorageOutcome s result.2 chunks target (result.1.map (fun _ => target)) := by
  dsimp only
  rw [sp_wrappedSetter_run]
  unfold WrappedPushStorageOutcome
  have hpow : (2 : Int) ^ 57 = 144115188075855872 := by decide
  simp only [hpow]
  cases ha : s.arrays[chunks]? with
  | none => simp only [Except.map, and_self]
  | some header =>
      by_cases hsize : header.size.val < 144115188075855872
      · simp only [hsize, ite_true, Except.map, and_self]
      · simp only [hsize, ite_false]
        cases hm : s.memories[header.reference.1]? with
        | none => simp only [Except.map, and_self]
        | some slots =>
            cases hread : slots[(header.reference.2.val + 144115188075855872 - 1 - 1).toNat]? with
            | none => simp only [hread, Except.map, and_self]
            | some cell =>
                cases cell with
                | none => simp only [hread, Except.map, and_self]
                | some old =>
                    by_cases hp : 1 ≤ header.reference.2.val + 144115188075855872 - 1 ∧
                        header.reference.2.val + 144115188075855872 - 1 ≤ IntTy.max .i64 ∧
                        header.reference.2.val + 144115188075855872 - 1 ≤ (slots.length : Int)
                    · simp only [hread, hp, and_self, ite_true, Except.map]
                      constructor
                      · trivial
                      · refine ⟨or_int old (shl_int (u64 1) (int 63)), ?_⟩
                        exact sp_singleBitUpdate s header.reference.1
                          (header.reference.2.val + 144115188075855872 - 1 - 1).toNat
                          slots old 63 true hm hread (by decide)
                    · simp only [hread, hp, ite_false, Except.map, and_self]

theorem sp_push_wrap_run (runtime : AllocationData) (target : Ref 1)
    (B : BitVector) (item : Bool) (state : ObjectState)
    (hobj : ObjectContains state target B) (hlen : B.len.val = IntTy.max .i64) :
    let updated : BitVector := {B with len := int (-9223372036854775808)}
    let committed : ObjectState :=
      {state with objects := state.objects.set target.identity ⟨1, updated⟩}
    (pushBool runtime target item).run state =
      if item then
        let result := (unsafeBitSetIndex B.chunks true (int (-9223372036854775808))).run state.memory
        (result.1.map (fun _ => target), {committed with memory := result.2})
      else (.ok target, committed) := by
  have hmod : B.len.val % 64 ≠ 0 := by rw [hlen]; decide
  have hinc : B.len + int 1 = int (-9223372036854775808) := by
    apply Subtype.ext
    change wrapInt .i64 (B.len.val + 1) = _
    rw [hlen]
    decide
  have hrun := sp_push_noGrowth_run runtime target B item state hobj hmod
  dsimp only at hrun ⊢
  rw [hinc] at hrun
  rw [hrun]
  cases item
  · rfl
  · simp only [ite_true]
    have hbounds : ScalarIndexAccepted
        ({B with len := int (-9223372036854775808)} : BitVector)
        (int (-9223372036854775808)) = true := by
      change decide (((int (-9223372036854775808)).val - 1) % (2 : Int) ^ 64 <
        (int (-9223372036854775808)).val % (2 : Int) ^ 64) = true
      exact (by decide : decide (((int (-9223372036854775808)).val - 1) % (2 : Int) ^ 64 <
        (int (-9223372036854775808)).val % (2 : Int) ^ 64) = true)
    rw [sp_publicWrite_run, if_pos hbounds]
    cases hr : (unsafeBitSetIndex B.chunks true (int (-9223372036854775808))).run state.memory with
    | mk result memory => cases result <;> rfl

theorem Models1G15PushBoolNativeWrap_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.PushBoolNativeLengthWrap := by
  intro runtime target B item state hobj hlen
  dsimp only
  rw [sp_push_wrap_run runtime target B item state hobj hlen]
  have hnew := sp_object_set_contains state target B
    {B with len := int (-9223372036854775808)} hobj
  have hlenmin : (int (-9223372036854775808)).val = IntTy.min .i64 := by decide
  cases item
  · exact ⟨⟨rfl, rfl⟩, List.length_set,
      fun identity hne => List.getElem?_set_ne (Ne.symm hne),
      {B with len := int (-9223372036854775808)}, hnew, hlenmin, rfl, rfl⟩
  · exact ⟨sp_wrappedWriteOutcome state.memory B.chunks target, List.length_set,
      fun identity hne => List.getElem?_set_ne (Ne.symm hne),
      {B with len := int (-9223372036854775808)}, hnew, hlenmin, rfl, rfl⟩
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

/-- Mathematical low-bit mask over every signed native length, including
wrapped lengths. Julia source: base/bitarray.jl:118-119. -/
def ReusedMaskEndLowBits : Prop :=
  (∀ length : I64,
    (maskEnd length).val =
      (2 : Int) ^ (if length.val % 64 = 0 then 64 else (length.val % 64).toNat) - 1) ∧
  (∀ (N : Nat) (B : BitArray N),
    (maskEndArray B).val =
      (2 : Int) ^ (if B.len.val % 64 = 0 then 64 else (B.len.val % 64).toNat) - 1)

/-- Full signed-index mathematical address, including predecessor wrap.
Julia source: base/bitarray.jl:122. -/
def ReusedChunkAddressFull : Prop :=
  ∀ index : I64,
    (getChunksId index).1.val = WrappedZeroBasedScalar index / 64 + 1 ∧
    (getChunksId index).2.val = WrappedZeroBasedScalar index % 64
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.ChatGPT.Batch3.Group1

theorem Models1G15ReusedMaskLowBits_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedMaskEndLowBits := by
  constructor
  · exact bh_mask_val
  · intro N B
    exact bh_mask_val B.len

theorem Models1G15ReusedChunkAddressFull_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedChunkAddressFull :=
  bh_address
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

def NewArrayResult {N : Nat} (s : Heap) (A : BitArray N) (expected : List Bool)
    (result : Except JuliaLean.base.array.Error (BitArray N) × Heap) : Prop :=
  PreservesExisting s result.2 ∧
  match result.1 with
  | .ok output =>
      s.arrays[output.chunks]? = none ∧ output.len = A.len ∧
      bitArraySizeRanked output = bitArraySizeRanked A ∧
      bits result.2 output = expected ∧
      Readable result.2 output
  | .error _ => False

def BangResult {D : Nat} (s : Heap) (dest : BitArray D) (expected : List Bool)
    (result : Except JuliaLean.base.array.Error (BitArray D) × Heap) : Prop :=
  result.1 = .ok dest ∧ bits result.2 dest = expected ∧
  (Packed s dest → Packed result.2 dest)

/-- Native Int output-store representation. Every old memory has an admissible
eight-byte allocation size and every stored header describes a live window.
Raw unknown cells and arbitrary shared references are retained; there is no
initialization or separation precondition. Source: base/boot.jl:821-845 and
src/genericmemory.c:55-73. -/
def NativeIntStore (s : JuliaLean.base.array.MutableMemory I64) : Prop :=
  (∀ slots ∈ s.memories, slots.length < 2 ^ 60) ∧
  (∀ handle, handle < s.arrays.length → s.validVector handle)

/-- The output's old native-Int arrays and memories are unchanged even if a later
source access or output bounds check throws. The UInt64 input is the immutable
ReaderT component, so it and its existing aliases cannot be changed by this model.
Julia source: base/bitarray.jl:1145-1172. -/
def UnaryMinusPreservesOld (before after : JuliaLean.base.array.MutableMemory I64) : Prop :=
  after.arrays.take before.arrays.length = before.arrays ∧
  after.memories.take before.memories.length = before.memories

/-- Independent elementwise negation, ranked shape, and allocation-failure promise.
The full Readable input domain is retained, including empty and rank-zero arrays,
dirty padding, shared chunks, excess chunks, and native lengths too large for the
unpacked Int output. The allocator rejects n >= 2^60: its eight-byte elements would
reach the native byte bound 2^63-2. For smaller lengths, this states the public
elementwise result rather than reproducing the chunk traversal.
Julia source: base/bitarray.jl:1145-1172; base/array.jl:590-608;
src/genericmemory.c:55-73. -/
def UnaryMinusContract : Prop :=
  ∀ (N : Nat) (input : Heap) (outputBefore : JuliaLean.base.array.MutableMemory I64)
    (B : BitArray N), Readable input B → NativeIntStore outputBefore →
    let result := ((JuliaLean.base.bitarray.Models1Group16.unaryMinus B).run input).run outputBefore
    UnaryMinusPreservesOld outputBefore result.2 ∧
    if (2 : Int)^60 ≤ B.len.val then
      result.1 = .error (.argument
        "invalid GenericMemory size: the number of elements is either negative or too large for system address width") ∧
      result.2 = outputBefore
    else
      match result.1 with
      | .ok A =>
          outputBefore.arrays[A.handle]? = none ∧
          A.elementType = .i64 ∧
          A.dimensions = (bitArraySizeRanked B).map (fun d => d.val.toNat) ∧
          A.axes = A.dimensions.map (fun d => ((1 : Int), d)) ∧
          result.2.validVector A.handle ∧
          result.2.contents A.handle =
            (bits input B).map (fun bit => some (int (if bit then -1 else 0)))
      | .error _ => False

/-- Mathematical shape compatibility: append singleton dimensions to the shorter
shape, then compare all extents. This independent statement does not invoke
promote_shape, its mismatch logic, or any array iterator.
Documentation: base/indices.jl:156-173. -/
def ArithmeticShapesCompatible (a b : List I64) : Prop :=
  a ++ List.replicate (b.length - a.length) (int 1) =
    b ++ List.replicate (a.length - b.length) (int 1)

instance (a b : List I64) : Decidable (ArithmeticShapesCompatible a b) := by
  unfold ArithmeticShapesCompatible
  infer_instance

/-- Independent mathematical Bool addition/subtraction. Only the property uses
unbounded Int; the model calls the actual native-Int Bool arithmetic methods.
Julia source: base/bool.jl:145-146. -/
def arithmeticValue (f : JuliaLean.base.bitarray.Models1Group16.ArithmeticFunction) (a b : Bool) : Int :=
  let x : Int := if a then 1 else 0
  let y : Int := if b then 1 else 0
  match f with
  | .add => x + y
  | .subtract => x - y

/-- Full generated addition/subtraction contract: shape disagreement throws before allocation;
compatible shapes select the input with more dimensions and native Int storage.
The output allocation bound is part of the conclusion, not a restriction on
readable input lengths. On success old storage is unchanged, the result is fresh,
and all values are the independent elementwise arithmetic result. Shared input
chunks, dirty padding, excess chunks, rank zero, and empty arrays remain included.
Julia source: base/bitarray.jl:1176-1190; base/bool.jl:145-146.
Documentation: base/indices.jl:156-173; src/genericmemory.c:55-73. -/
def BinaryArithmeticContract : Prop :=
  ∀ (N K : Nat) (f : JuliaLean.base.bitarray.Models1Group16.ArithmeticFunction) (input : Heap)
    (outputBefore : JuliaLean.base.array.MutableMemory I64) (A : BitArray N) (B : BitArray K),
    Readable input A → Readable input B → NativeIntStore outputBefore →
    let result := ((JuliaLean.base.bitarray.Models1Group16.binaryArithmetic f A B).run input).run outputBefore
    UnaryMinusPreservesOld outputBefore result.2 ∧
    if ¬ ArithmeticShapesCompatible (bitArraySizeRanked A) (bitArraySizeRanked B) then
      (∃ message, result.1 = .error (.dimensionMismatch message)) ∧ result.2 = outputBefore
    else if (2 : Int)^60 ≤ A.len.val then
      result.1 = .error (.argument
        "invalid GenericMemory size: the number of elements is either negative or too large for system address width") ∧
      result.2 = outputBefore
    else
      match result.1 with
      | .ok output =>
          outputBefore.arrays[output.handle]? = none ∧
          output.elementType = .i64 ∧
          output.dimensions =
            (if N < K then bitArraySizeRanked B else bitArraySizeRanked A).map
              (fun d => d.val.toNat) ∧
          output.axes = output.dimensions.map (fun d => ((1 : Int), d)) ∧
          result.2.validVector output.handle ∧
          result.2.contents output.handle =
            List.zipWith (fun a b => some (int (arithmeticValue f a b)))
              (bits input A) (bits input B)
      | .error _ => False

/-- A Boolean whole-array sum is the mathematical number of logical true
elements. The sum is representable because a constructible BitArray has native
nonnegative length. Aliases and dirty padding are included; they may expose a
source bug rather than being excluded by the statement.
Julia source: base/bitarray.jl:1722; base/reduce.jl count/sum documentation. -/
def SumColonContract : Prop :=
  ∀ (N : Nat) (s : Heap) (B : BitArray N),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.sumColon B).run s
    result.2 = s ∧
    match result.1 with
    | .ok n => n.val = ((bits s B).count true : Int)
    | .error _ => False


/-- Allocating logical complement preserves shape, returns fresh storage,
and leaves every input/alias unchanged. This includes every native constructible
rank and readable input, rather than assuming raw dims is initialized for vectors.
Julia source: base/bitarray.jl:1756; base/abstractarray.jl map documentation. -/
def MapNotContract : Prop :=
  ∀ (N : Nat) (s : Heap) (A : BitArray N), Readable s A →
    NewArrayResult s A ((bits s A).map Bool.not) ((JuliaLean.base.bitarray.Models1Group16.mapNot A).run s)

/-- Allocating zero-map returns one false bit per logical input element at the
same shape. Its output is fully packed even if the input has extra aliased chunks.
Julia source: base/bitarray.jl:1757; zero and map documentation. -/
def MapZeroContract : Prop :=
  ∀ (N : Nat) (s : Heap) (A : BitArray N), Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapZero A).run s
    NewArrayResult s A (List.replicate A.len.val.toNat false) result ∧
    match result.1 with
    | .ok output => Packed result.2 output
    | .error _ => False

/-- Allocating one-map returns one true value per logical element and zero
padding in a fresh array of the same ranked shape. Every old object is preserved,
including when the source shares excess chunks with another header.
Julia source: base/bitarray.jl:1758; one and map documentation. -/
def MapOneContract : Prop :=
  ∀ (N : Nat) (s : Heap) (A : BitArray N), Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapOne A).run s
    NewArrayResult s A (List.replicate A.len.val.toNat true) result ∧
    match result.1 with
    | .ok output => Packed result.2 output
    | .error _ => False

/-- Identity mapping returns an independent copy of the logical elements and
actual ranked shape, and preserves all old objects. No comparison to another
implementation is used as the expected value.
Julia source: base/bitarray.jl:1759; base/abstractarray.jl:1154-1157,1211-1214. -/
def MapIdentityContract : Prop :=
  ∀ (N : Nat) (s : Heap) (A : BitArray N), Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapIdentity A).run s
    NewArrayResult s A (bits s A) result ∧
    match result.1 with
    | .ok output => Packed s A → Packed result.2 output
    | .error _ => False

/-- Complement-map! checks capacity before writing and preserves the unused
logical suffix. Identical-view aliases are included; shifted partial overlaps
are subject to the documented alias warning, while the frame still holds.
Julia source: base/bitarray.jl:1761,1795-1813.
Documentation: base/abstractarray.jl:3563-3568. -/
def MapNotBangContract : Prop :=
  ∀ (D N : Nat) (s : Heap) (dest : BitArray D) (A : BitArray N),
    Readable s dest → Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapNotBang dest A).run s
    MutationFrame s result.2 dest.chunks ∧
    if dest.len.val < A.len.val then
      result.1 = .error (.dimensionMismatch "length of destination must be >= length of collection") ∧
      result.2 = s
    else SnapshotSafe s dest A →
      BangResult s dest (((bits s A).map Bool.not) ++ (bits s dest).drop A.len.val.toNat) result

/-- Constant-zero map! overwrites precisely the logical prefix selected by
the source length, even when source and destination overlap arbitrarily.
Julia source: base/bitarray.jl:1762,1789-1793.
Documentation: base/abstractarray.jl:3563-3568. -/
def MapZeroBangContract : Prop :=
  ∀ (D N : Nat) (s : Heap) (dest : BitArray D) (A : BitArray N),
    Readable s dest → Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapZeroBang dest A).run s
    MutationFrame s result.2 dest.chunks ∧
    if dest.len.val < A.len.val then
      result.1 = .error (.dimensionMismatch "length of destination must be >= length of collection") ∧
      result.2 = s
    else BangResult s dest
      (List.replicate A.len.val.toNat false ++ (bits s dest).drop A.len.val.toNat) result

/-- Constant-one map! preserves every destination bit beyond the affected
prefix and permits arbitrary aliases, since it need not read source values.
Julia source: base/bitarray.jl:1763,1789-1793.
Documentation: base/abstractarray.jl:3563-3568. -/
def MapOneBangContract : Prop :=
  ∀ (D N : Nat) (s : Heap) (dest : BitArray D) (A : BitArray N),
    Readable s dest → Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapOneBang dest A).run s
    MutationFrame s result.2 dest.chunks ∧
    if dest.len.val < A.len.val then
      result.1 = .error (.dimensionMismatch "length of destination must be >= length of collection") ∧
      result.2 = s
    else BangResult s dest
      (List.replicate A.len.val.toNat true ++ (bits s dest).drop A.len.val.toNat) result

/-- Identity map! uses the documented logical prefix/suffix behavior, and
preserves the actual copyto! BoundsError on a short destination. Identical-view
aliases are included. Julia source: base/bitarray.jl:1764,429-447.
Documentation: base/abstractarray.jl:3563-3568. -/
def MapIdentityBangContract : Prop :=
  ∀ (D N : Nat) (s : Heap) (dest : BitArray D) (A : BitArray N),
    Readable s dest → Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapIdentityBang dest A).run s
    MutationFrame s result.2 dest.chunks ∧
    if dest.len.val < A.len.val then result.1 = .error .bounds ∧ result.2 = s
    else SnapshotSafe s dest A →
      BangResult s dest (bits s A ++ (bits s dest).drop A.len.val.toNat) result


/-- Independent Boolean meanings of the public functions. These apply to
logical values, not the UInt64 operations or their masks. -/
def binaryTruth (f : JuliaLean.base.bitarray.Models1Group16.BinaryFunction) (a b : Bool) : Bool :=
  match f with
  | .bitAnd | .multiply | .minimum => a && b
  | .bitOr | .maximum => a || b
  | .bitXor | .notEqual => a != b
  | .nand => !(a && b)
  | .nor => !(a || b)
  | .greaterEqual | .power => decide ((if b then 1 else 0 : Nat) ≤ (if a then 1 else 0))
  | .lessEqual => decide ((if a then 1 else 0 : Nat) ≤ (if b then 1 else 0))
  | .equal => a == b
  | .less => decide ((if a then 1 else 0 : Nat) < (if b then 1 else 0))
  | .greater => decide ((if b then 1 else 0 : Nat) < (if a then 1 else 0))


/-- Mathematical shape selected by two-array map. Different ranks produce a
vector, vectors use the shorter length, and every other common rank retains the
input shape after checking that both shapes agree. This describes the public
shape rule without reusing zip, axes-promotion, allocation or chunk operations.
Julia source: base/bitarray.jl:1776,1783-1787; base/iterators.jl:71-75,413-416. -/
def binaryExpectedShape {N K : Nat} (A : BitArray N) (B : BitArray K) : List I64 :=
  if N = K ∧ N ≠ 1 then bitArraySizeRanked A
  else [int (min A.len.val B.len.val)]

/-- All fifteen generated allocating maps preserve old objects, allocate fresh
storage, use the documented shortest logical iteration, and return the correct
ranked shape. Incompatible equal-rank multidimensional shapes throw before any
allocation or mutation. Readable alias states remain in the domain.
Julia source: base/bitarray.jl:1766-1787; base/abstractarray.jl map documentation;
base/iterators.jl:413-416; base/indices.jl:192-204. -/
def MapBinaryContract : Prop :=
  ∀ (N K : Nat) (f : JuliaLean.base.bitarray.Models1Group16.BinaryFunction) (s : Heap)
    (A : BitArray N) (B : BitArray K), Readable s A → Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapBinary f A B).run s
    if N = K ∧ 1 < N ∧ bitArraySizeRanked A ≠ bitArraySizeRanked B then
      (∃ message, result.1 = .error (.dimensionMismatch message)) ∧ result.2 = s
    else
      PreservesExisting s result.2 ∧
      match result.1 with
      | .ok output =>
          s.arrays[output.chunks]? = none ∧
          output.len.val = min A.len.val B.len.val ∧
          bitArraySizeRanked output = binaryExpectedShape A B ∧
          bits result.2 output = List.zipWith (binaryTruth f) (bits s A) (bits s B) ∧
          Packed result.2 output
      | .error _ => False


/-- Every generated binary map! operates on the shorter logical prefix,
preserves the unused destination suffix, checks its capacity before mutation,
and retains metadata and the physical frame. Independently ranked arrays and
identical-view aliases are included. Shifted overlap retains the source behavior
without an undocumented snapshot promise.
Julia source: base/bitarray.jl:1766-1778,1814-1835.
Documentation: base/abstractarray.jl:3563-3568; source alias-order comment. -/
def MapBinaryBangContract : Prop :=
  ∀ (D N K : Nat) (f : JuliaLean.base.bitarray.Models1Group16.BinaryFunction) (s : Heap)
    (dest : BitArray D) (A : BitArray N) (B : BitArray K),
    Readable s dest → Readable s A → Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.mapBinaryBang f dest A B).run s
    let n := min A.len.val.toNat B.len.val.toNat
    MutationFrame s result.2 dest.chunks ∧
    if dest.len.val < min A.len.val B.len.val then
      result.1 = .error (.dimensionMismatch "length of destination must be >= length of smallest input collection") ∧
      result.2 = s
    else SnapshotSafe s dest A → SnapshotSafe s dest B →
      BangResult s dest
        (List.zipWith (binaryTruth f) (bits s A) (bits s B) ++ (bits s dest).drop n) result

/-- Constant mapping preserves the destination suffix and every physical cell
outside its destination window, for either Boolean and arbitrary storage aliases.
Julia source: base/bitarray.jl:1789-1793. -/
def ConstantMapPrefix : Prop :=
  ∀ (D N : Nat) (s : Heap) (dest : BitArray D) (A : BitArray N) (value : Bool),
    Readable s dest → Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.bitMapConstant dest A value).run s
    MutationFrame s result.2 dest.chunks ∧
    if dest.len.val < A.len.val then
      result.1 = .error (.dimensionMismatch "length of destination must be >= length of collection") ∧
      result.2 = s
    else BangResult s dest
      (List.replicate A.len.val.toNat value ++ (bits s dest).drop A.len.val.toNat) result
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group16


def mapsShortSource : BitArray 2 := ⟨0, int 1, [int 1, int 1]⟩


def mapsLongDestination : BitArray 1 := ⟨1, int 65, [int 65]⟩


def mapsExampleHeap (first second : U64) : Heap :=
  ⟨[[some (u64 0), some (u64 0)], [some first, some second]],
   [⟨(0, int 1), int 2⟩, ⟨(1, int 1), int 2⟩]⟩

theorem mapsShortSourceReadable (first second : U64) :
    Readable (mapsExampleHeap first second) mapsShortSource := by
  simp only [Readable, mapsExampleHeap, mapsShortSource, MutableMemory.validVector,
    MutableMemory.contents, bitArraySizeRanked, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.length_cons, List.length_nil,
    Option.isSome_some, ite_self,
    show ((int 2).val).toNat = 2 from rfl,
    show ((int 1).val - 1).toNat = 0 from rfl,
    List.drop_zero, List.take_succ_cons, List.take_zero]
  decide

theorem mapsLongDestinationReadable (first second : U64) :
    Readable (mapsExampleHeap first second) mapsLongDestination := by
  simp only [Readable, mapsExampleHeap, mapsLongDestination, MutableMemory.validVector,
    MutableMemory.contents, bitArraySizeRanked, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.length_cons, List.length_nil,
    Option.isSome_some, ite_self,
    show ((int 2).val).toNat = 2 from rfl,
    show ((int 1).val - 1).toNat = 0 from rfl,
    List.drop_zero, List.take_succ_cons, List.take_zero]
  decide

theorem mapsIndependentWindows (first second : U64) :
    SnapshotSafe (mapsExampleHeap first second) mapsLongDestination mapsShortSource := by
  exact Or.inl (by decide)


theorem mapsNotBangSecondBit :
    (bits ((JuliaLean.base.bitarray.Models1Group16.mapNotBang
      mapsLongDestination mapsShortSource).run (mapsExampleHeap (u64 0) (u64 0))).2
      mapsLongDestination)[1]? = some true := by
  rfl

theorem Models1G16MapNotBang_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.MapNotBangContract := by
  intro contract
  have observed := contract 1 2 (mapsExampleHeap (u64 0) (u64 0))
    mapsLongDestination mapsShortSource
    (mapsLongDestinationReadable _ _) (mapsShortSourceReadable _ _)
  have enough : ¬ mapsLongDestination.len.val < mapsShortSource.len.val := by decide
  have values := ((if_neg enough).mp observed.2) (mapsIndependentWindows _ _)
  have second := congrArg (fun xs : List Bool => xs[1]?) values.2.1
  rw [mapsNotBangSecondBit] at second
  change some true = some false at second
  cases second


theorem mapsIdentityBangSecondBit :
    (bits ((JuliaLean.base.bitarray.Models1Group16.mapIdentityBang
      mapsLongDestination mapsShortSource).run (mapsExampleHeap u64Max (u64 1))).2
      mapsLongDestination)[1]? = some false := by
  rfl

theorem Models1G16MapIdentityBang_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.MapIdentityBangContract := by
  intro contract
  have observed := contract 1 2 (mapsExampleHeap u64Max (u64 1))
    mapsLongDestination mapsShortSource
    (mapsLongDestinationReadable _ _) (mapsShortSourceReadable _ _)
  have enough : ¬ mapsLongDestination.len.val < mapsShortSource.len.val := by decide
  have values := ((if_neg enough).mp observed.2) (mapsIndependentWindows _ _)
  have second := congrArg (fun xs : List Bool => xs[1]?) values.2.1
  rw [mapsIdentityBangSecondBit] at second
  change some false = some true at second
  cases second


theorem mapsBinaryBangSecondBit :
    (bits ((JuliaLean.base.bitarray.Models1Group16.mapBinaryBang .bitOr
      mapsLongDestination mapsShortSource mapsShortSource).run
        (mapsExampleHeap u64Max (u64 1))).2 mapsLongDestination)[1]? = some false := by
  rfl

theorem Models1G16MapBinaryBang_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.MapBinaryBangContract := by
  intro contract
  have observed := contract 1 2 2 .bitOr (mapsExampleHeap u64Max (u64 1))
    mapsLongDestination mapsShortSource mapsShortSource
    (mapsLongDestinationReadable _ _) (mapsShortSourceReadable _ _)
    (mapsShortSourceReadable _ _)
  have enough : ¬ mapsLongDestination.len.val <
      min mapsShortSource.len.val mapsShortSource.len.val := by decide
  have values := ((if_neg enough).mp observed.2)
    (mapsIndependentWindows _ _) (mapsIndependentWindows _ _)
  have second := congrArg (fun xs : List Bool => xs[1]?) values.2.1
  rw [mapsBinaryBangSecondBit] at second
  change some false = some true at second
  cases second

def mapsIsBounds {α : Type} (result : Except Error α) : Bool :=
  match result with
  | .error .bounds => true
  | _ => false

theorem mapsIsBoundsSound {α : Type} (result : Except Error α)
    (classified : mapsIsBounds result = true) : result = .error .bounds := by
  cases result with
  | ok _ => cases classified
  | error error =>
    cases error <;> (try rfl) <;> cases classified


theorem mapsBinaryAllocationError :
    ((JuliaLean.base.bitarray.Models1Group16.mapBinary .bitOr
      mapsShortSource mapsShortSource).run (mapsExampleHeap (u64 0) (u64 0))).1 =
      .error .bounds := by
  apply mapsIsBoundsSound
  decide +kernel

theorem Models1G16MapBinary_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.MapBinaryContract := by
  intro contract
  have observed := contract 2 2 .bitOr (mapsExampleHeap (u64 0) (u64 0))
    mapsShortSource mapsShortSource
    (mapsShortSourceReadable _ _) (mapsShortSourceReadable _ _)
  have sameShape : ¬ (2 = 2 ∧ 1 < 2 ∧
      bitArraySizeRanked mapsShortSource ≠ bitArraySizeRanked mapsShortSource) := by
    intro incompatible
    exact incompatible.2.2 rfl
  have success := ((if_neg sameShape).mp observed).2
  rw [mapsBinaryAllocationError] at success
  exact success
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group16

theorem Models1G16SumColon_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.SumColonContract := by
  intro h
  have hv := (h 2 countAliasHeap countAliasArray countAliasReadable).2
  have hrun : ((JuliaLean.base.bitarray.Models1Group16.sumColon countAliasArray).run
      countAliasHeap).1 = .ok (int 1) := by decide
  change (match ((JuliaLean.base.bitarray.Models1Group16.sumColon countAliasArray).run
    countAliasHeap).1 with
    | .ok n => n.val = ((bits countAliasHeap countAliasArray).count true : Int)
    | .error _ => False) at hv
  rw [hrun] at hv
  change (1 : Int) = 0 at hv
  exact (by decide : (1 : Int) ≠ 0) hv
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def allocTinyVector : BitVector := ⟨0, int 1, [int 1]⟩
def allocExtraZeroHeap : MutableMemory U64 :=
  MutableMemory.initial [some (u64 0), some (u64 0)]
def allocExtraTrueHeap : MutableMemory U64 :=
  MutableMemory.initial [some (u64 0), some (u64 1)]
def allocEmptyIntHeap : MutableMemory I64 := ⟨[], []⟩

theorem allocExtraZeroReadable :
    JuliaLean.Proofs.base.bitarray.Models1Group16.Readable allocExtraZeroHeap allocTinyVector := by
  unfold JuliaLean.Proofs.base.bitarray.Models1Group16.Readable
  decide

theorem allocExtraTrueReadable :
    JuliaLean.Proofs.base.bitarray.Models1Group16.Readable allocExtraTrueHeap allocTinyVector := by
  unfold JuliaLean.Proofs.base.bitarray.Models1Group16.Readable
  decide

theorem allocEmptyIntValid :
    JuliaLean.Proofs.base.bitarray.Models1Group16.NativeIntStore allocEmptyIntHeap := by
  constructor
  · intro slots hs
    cases hs
  · intro handle hh
    exact False.elim (Nat.not_lt_zero handle hh)


theorem Models1G16MapNot_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.MapNotContract := by
  intro h
  have hx := h 1 allocExtraZeroHeap allocTinyVector allocExtraZeroReadable
  have hr : ((JuliaLean.base.bitarray.Models1Group16.mapNot allocTinyVector).run
      allocExtraZeroHeap).1 = .error .bounds := by rfl
  unfold JuliaLean.Proofs.base.bitarray.Models1Group16.NewArrayResult at hx
  rw [hr] at hx
  exact hx.2


theorem Models1G16UnaryMinus_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.UnaryMinusContract := by
  intro h
  have hx := (h 1 allocExtraTrueHeap allocEmptyIntHeap allocTinyVector
    allocExtraTrueReadable allocEmptyIntValid).2
  have hsmall : ¬ (2 : Int)^60 ≤ allocTinyVector.len.val := by decide
  rw [if_neg hsmall] at hx
  have hr : (((JuliaLean.base.bitarray.Models1Group16.unaryMinus allocTinyVector).run
      allocExtraTrueHeap).run allocEmptyIntHeap).1 = .error .bounds := by rfl
  rw [hr] at hx
  exact hx
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models2Group11

open JuliaLean JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models2Group11

/-- On every primitive signed or unsigned integer type, _div64 gives the
mathematical floor quotient by 64. The selected Base shift is instantiated by
its installed model; the expected result is integer arithmetic, not a second
shift expression. Every primitive value is quantified, including negative
signed values, zero, and both endpoints of every width.
This is the internal helper's narrow numeric invariant; arbitrary nonnumeric
dispatch has no invented division contract.
Julia source: base/bitarray.jl:115; base/int.jl:604-612
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/mathematical-operations.md:88-101. -/
def Div64PrimitiveFloorQuotient : Prop :=
  ∀ (t : IntTy) (value : JInt t),
    let ops : Div64Ops Id (JInt t) (JInt t) :=
      { shiftRight := fun input count => pure (JuliaLean.base.int.shr_Int input count) }
    (Id.run (div64Generic ops value)).val = value.val / 64

/-- For the native Int case used by BitArray indexing, _mod64 returns the
nonnegative mathematical remainder modulo 64. This includes the entire signed
domain, so negative inputs must still yield their low-six-bit residue rather
than a signed remainder or an error. The Base bitwise-and method is concrete;
the expected value does not call any bitwise or model helper.
Julia source: base/bitarray.jl:116; base/int.jl:407
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/mathematical-operations.md:88-101. -/
def Mod64NativeEuclideanRemainder : Prop :=
  ∀ value : I64,
    let ops : Mod64Ops Id I64 I64 :=
      { bitAnd := fun input mask => pure (JuliaLean.base.int.band input mask) }
    (Id.run (mod64Generic ops value)).val = value.val % 64

/-- On native Int, _blsr leaves zero unchanged and removes exactly the lowest
set bit of every nonzero 64-bit two's-complement pattern. A least set bit at k
is characterized independently by the arithmetic residue
`pattern % 2^(k+1) = 2^k`; subtracting that power leaves every other bit intact.
The expected result contains no bitwise-and or wrapped predecessor expression.
There are no sign or nonzero preconditions: typemin(Int), every negative value,
and zero are included. Thus the wrap at typemin(Int)-1 is part of the invariant.
This is a narrow true invariant of an internal helper, not a contract imposed
on arbitrary overloaded subtraction/bitwise-and methods.
Julia source: base/bitarray.jl:117; base/int.jl:87,407
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/mathematical-operations.md:88-101;
doc/src/manual/integers-and-floating-point-numbers.md:235-249. -/
def BlsrNativeClearsLeastSetBit : Prop :=
  ∀ value : I64,
    let ops : BlsrOps Id I64 I64 I64 :=
      { subtract := fun input one => pure (JuliaLean.base.int.sub input one)
        bitAnd := fun input difference => pure (JuliaLean.base.int.band input difference) }
    let pattern := value.val % (2 : Int) ^ 64
    let result := (Id.run (blsrGeneric ops value)).val % (2 : Int) ^ 64
    if pattern = 0 then result = 0
    else ∃ k : Nat, k < 64 ∧
      pattern % (2 : Int) ^ (k + 1) = (2 : Int) ^ k ∧
      result = pattern - (2 : Int) ^ k

/-- A generic test carrier records arbitrary state, arbitrary exceptions with
their throw-state, and divergence. It adds no laws for selected operators. -/
abbrev BitHelperEffect (E S A : Type) := StateT S (ExceptT (E × S) Option) A

/-- Subtraction is evaluated before bitwise-and. If the actual selected
subtraction diverges or throws, _blsr cannot return a value, call a recovery
path, replace the exception, roll back earlier state changes, or add later
state changes. This observation quantifies every operand/intermediate/result
type and every pair of selected operators. It matches the actual first
operation's outcome rather than assuming a correctness law for that operation.
The successful-subtraction branch intentionally makes no claim about arbitrary
custom bitwise-and behavior.
Julia source: base/bitarray.jl:117
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Source invariant: evaluation of the right operand finishes before the outer
operator call, and an exception prevents that outer call. -/
def BlsrSubtractionFaultPreserved : Prop :=
  ∀ (E S A Difference R : Type)
    (ops : BlsrOps (BitHelperEffect E S) A Difference R) (value : A) (before : S),
    match ops.subtract value (int 1) before with
    | none => blsrGeneric ops value before = none
    | some (.error failure) => blsrGeneric ops value before = some (.error failure)
    | some (.ok _) => True

theorem Mod64NativeEuclideanRemainder_proven : Mod64NativeEuclideanRemainder := by
  intro value
  exact JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1.scalar_mod64_val value

theorem BlsrSubtractionFaultPreserved_proven : BlsrSubtractionFaultPreserved := by
  intro E S A Difference R ops value before
  cases h : ops.subtract value (int 1) before with
  | none =>
      simp [blsrGeneric, Bind.bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, h]
  | some result =>
      cases result with
      | error failure =>
          simp [blsrGeneric, Bind.bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, h]
      | ok result => trivial

open JuliaLean.base.int JuliaLean.Proofs.base.int

theorem blsrNatClearsLeastSetBit (n : Nat) : n ≠ 0 →
    ∃ k : Nat, 2 ^ k ≤ n ∧ n % 2 ^ (k + 1) = 2 ^ k ∧
      n &&& (n - 1) = n - 2 ^ k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    have hzero : (n &&& (n - 1)) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (n &&& (n - 1)) with hz | ho
      · exact hz
      · have hboth := Nat.and_mod_two_eq_one.mp ho
        omega
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · have hhalfPositive : n / 2 ≠ 0 := by omega
      have hhalfLess : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      obtain ⟨k, hk, hm, hr⟩ := ih (n / 2) hhalfLess hhalfPositive
      have hpred : (n - 1) / 2 = n / 2 - 1 := by omega
      have hhalf : (n &&& (n - 1)) / 2 = n / 2 - 2 ^ k := by
        rw [Nat.and_div_two, hpred, hr]
      have heq : n = 2 * (n / 2) := by omega
      have hpower : 2 ^ (k + 1) ≤ n := by
        rw [Nat.pow_succ]
        omega
      have hexp : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hmod : n % 2 ^ (k + 1 + 1) = 2 ^ (k + 1) := by
        calc
          n % 2 ^ (k + 1 + 1) = (2 * (n / 2)) % 2 ^ (k + 1 + 1) :=
            congrArg (fun x => x % 2 ^ (k + 1 + 1)) heq
          _ = (2 * (n / 2)) % (2 * 2 ^ (k + 1)) :=
            congrArg (fun d => (2 * (n / 2)) % d) hexp
          _ = 2 * ((n / 2) % 2 ^ (k + 1)) := Nat.mul_mod_mul_left _ _ _
          _ = 2 * 2 ^ k := by rw [hm]
          _ = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      refine ⟨k + 1, hpower, hmod, ?_⟩
      rw [Nat.pow_succ]
      omega
    · have hpred : (n - 1) / 2 = n / 2 := by omega
      have hhalf : (n &&& (n - 1)) / 2 = n / 2 := by
        rw [Nat.and_div_two, hpred, Nat.and_self]
      refine ⟨0, ?_, ?_, ?_⟩
      · change 1 ≤ n
        omega
      · simpa using hodd
      · simp only [Nat.pow_zero]
        omega

theorem BlsrNativeClearsLeastSetBit_proven : BlsrNativeClearsLeastSetBit := by
  intro value
  let p := pattern value
  have hpBound : p < 2 ^ 64 := pattern_lt value
  have hpCast : (p : Int) = value.val % (2 : Int) ^ 64 := pattern_cast value
  have hresult : (band value (sub value (int 1))).val % (2 : Int) ^ 64 =
      ((p &&& pattern (sub value (int 1)) : Nat) : Int) := by
    exact (pattern_cast (band value (sub value (int 1)))).symm.trans
      (congrArg (fun n : Nat => (n : Int)) (pattern_band value (sub value (int 1))))
  change (if value.val % (2 : Int) ^ 64 = 0 then
    (band value (sub value (int 1))).val % (2 : Int) ^ 64 = 0
    else ∃ k : Nat, k < 64 ∧ value.val % (2 : Int) ^ 64 % (2 : Int) ^ (k + 1) =
      (2 : Int) ^ k ∧ (band value (sub value (int 1))).val % (2 : Int) ^ 64 =
        value.val % (2 : Int) ^ 64 - (2 : Int) ^ k)
  rw [← hpCast, hresult]
  by_cases hp : p = 0
  · simp [hp]
  · have hsub : pattern (sub value (int 1)) = p - 1 := by
      have hcast : (pattern (sub value (int 1)) : Int) = (p : Int) - 1 := by
        rw [pattern_cast, sub, sub_int_val]
        change wrapInt .i64 (value.val - 1) % (2 : Int) ^ 64 = (p : Int) - 1
        have hw : wrapInt .i64 (value.val - 1) % (2 : Int) ^ 64 =
            (value.val - 1) % (2 : Int) ^ 64 := wrapInt_emod_self .i64 (value.val - 1)
        rw [hw, Int.sub_emod, ← hpCast]
        have hone : (1 : Int) % (2 : Int) ^ 64 = 1 := by decide
        rw [hone]
        apply Int.emod_eq_of_lt <;> omega
      omega
    obtain ⟨k, hpower, hmod, hclear⟩ := blsrNatClearsLeastSetBit p hp
    have hk : k < 64 := by
      by_cases hsmall : k < 64
      · exact hsmall
      · have hmono : (2 : Nat) ^ 64 ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
    have hmodInt := congrArg (fun n : Nat => (n : Int)) hmod
    push_cast at hmodInt
    have hclearInt := congrArg (fun n : Nat => (n : Int)) hclear
    rw [Int.ofNat_sub hpower] at hclearInt
    push_cast at hclearInt
    have hpInt : (p : Int) ≠ 0 := by omega
    rw [if_neg hpInt]
    refine ⟨k, hk, hmodInt, ?_⟩
    rw [hsub]
    exact hclearInt

end JuliaLean.Proofs.base.bitarray.Models2Group11



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesArith1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-map", juliaFile := "base/bitarray.jl", juliaFns := ["map!(!, dest::BitArray, A::BitArray)", "map!(f, dest::BitArray, A::BitArray, B::BitArray)", "bit_map!"],
    statement := "The chunkwise map! specializations agree with elementwise map! over the shortest input, leave the rest of dest unchanged and keep the invariant, also when A === dest.", source := "map! docstring (destination at least as large as the smallest collection); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``MapAgrees, thm := none, notes := "Statement defect: take xs = ys = zs = replicate (2^63) false; every successful result has at most typemax(Int) logical bits, so its observations cannot equal the required 2^63-element mapped list; Julia cannot construct this input; require xs.length \u2264 typemax(Int)." }
]
def entriesArith2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-chunk-count", juliaFile := "base/bitarray.jl", juliaFns := ["_div64@115", "_mod64@116", "_blsr@117", "_msk_end@118", "num_bit_chunks@120", "BitArray@28", "get_chunks_id@122", "similar@359", "similar@363", "similar@366", "unsafe_bitsetindex!@675", "_bitreshape@476", "BitArray@500", "BitArray@498", "falses@396", "falses@397", "trues@415", "trues@416", "fill_bitarray_from_itr!@634", "gen_bitarray@576", "gen_bitarray@585", "gen_bitarray@589", "gen_bitarrayN@598", "similar@360", "similar@361", "reshape@472", "BitArray{N}@567", "generated@1177"],
    statement := "A BitArray stores exactly the ceiling of its logical length divided by 64 chunks.", source := "obvious invariant; base/bitarray.jl:28",
    status := .proven, prop := ``BitArrayChunkCount, thm := some ``JuliaLean.ChatGPT.Batch4.Group8.BitarrayBitArrayChunkCount_proven }
]
def entriesArith3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-equality-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["==@1206"],
    statement := "BitArray equality is true exactly when dimensions and logical bit sequences match, across arbitrary ranks.", source := "base/bitarray.jl:1206-1210",
    status := .proven, prop := ``Round5.BitArrayEqualityAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group1.BitarrayBitArrayEqualityAgrees_proven }
]
def entriesArith4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-vector-unary-minus-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["-@1145"],
    statement := "Unary minus maps false to zero and true to negative one in the integer result array.", source := "obvious invariant; base/bitarray.jl:1145",
    status := .todo, prop := ``BitVectorUnaryMinusAgrees, thm := none, notes := "Statement defect: false for List.replicate (2^64) false, whose modeled native length wraps to zero and allocates an empty output while the observation still requires 2^64 cells; Julia cannot construct this input, and xs.length \u2264 2^59 is a sufficient installed-allocation bound by root9UnaryMinusSupported." }
]
def entriesArith5 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-div64-native-quotient",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["_div64(l)"],
    statement := "For every primitive signed or unsigned integer value, the concrete Base shift instantiation of _div64 returns the mathematical floor quotient by 64.",
    source := "base/bitarray.jl:115; base/int.jl:604-612; doc/src/manual/mathematical-operations.md:88-101",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.Div64PrimitiveFloorQuotient,
    thm := none,
    notes := "Both direct shiftIntCount_proven projection and staged rewriting fail kernel checking: the kernel refuses Nat.pow because its exponent exceeds UInt32. A kernel-safe specialization remains open." },
  { id := "bitarray-mod64-native-remainder",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["_mod64(l)"],
    statement := "For every native signed Int, the concrete Base bitwise-and instantiation of _mod64 returns the nonnegative mathematical remainder modulo 64.",
    source := "base/bitarray.jl:116; base/int.jl:407; doc/src/manual/mathematical-operations.md:88-101",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.Mod64NativeEuclideanRemainder,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.Mod64NativeEuclideanRemainder_proven },
  { id := "bitarray-blsr-native-lowest-bit",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["_blsr(x)"],
    statement := "For every native signed Int, including zero and typemin, the concrete Base operator instantiation of _blsr clears exactly the least set bit of its 64-bit two's-complement pattern.",
    source := "base/bitarray.jl:117; base/int.jl:87,407; doc/src/manual/integers-and-floating-point-numbers.md:235-249",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.BlsrNativeClearsLeastSetBit,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.BlsrNativeClearsLeastSetBit_proven },
  { id := "bitarray-blsr-subtraction-fault",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["_blsr(x)"],
    statement := "For arbitrary selected subtraction and bitwise-and operators, subtraction failure or divergence propagates before the outer AND call and preserves the exact error and reached state.",
    source := "base/bitarray.jl:117; ordered evaluation and exception propagation invariant",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.BlsrSubtractionFaultPreserved,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.BlsrSubtractionFaultPreserved_proven }
]
def entriesArith6 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-constant-map-prefix", juliaFile := "base/bitarray.jl",
    juliaFns := ["bit_map_constant!(::BitArray, ::BitArray, ::Bool)"],
    statement := "Constant bit mapping checks destination capacity before mutation, changes precisely the source-length prefix, and preserves the destination suffix and physical frame.",
    source := "base/bitarray.jl:1789-1793", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.ConstantMapPrefix, thm := none,
    notes := "No complete exact proof returned. cmFrameRefl, cmFrameTrans, cmAllSet, cmConstantShortRun, cmConstantEmptyRun, and the zero/one reductions are retained; remaining goal: generic nonempty masked chunk fill, exact bit-prefix semantics, and padding preservation." }
]
def entriesArith7 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-unary-minus", juliaFile := "base/bitarray.jl",
    juliaFns := ["-(::BitArray)"],
    statement := "Unary minus preserves all old storage, allocates fresh native-Int output of the same ranked shape, and negates each logical Boolean; lengths >=2^60 retain the actual allocation ArgumentError before allocation.",
    source := "base/bitarray.jl:1145-1172; base/array.jl:631-653; src/genericmemory.c:55-73", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.UnaryMinusContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16UnaryMinus_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-binary-arithmetic", juliaFile := "base/bitarray.jl",
    juliaFns := ["+(::BitArray, ::BitArray)", "-(::BitArray, ::BitArray)"],
    statement := "Generated addition/subtraction checks trailing-singleton shape compatibility before allocation, preserves native Int allocation failures, and returns fresh ranked elementwise Int results while preserving old input and output storage.",
    source := "base/bitarray.jl:1176-1190; base/indices.jl:108,139-186; base/bool.jl:145-146", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.BinaryArithmeticContract, thm := none,
    notes := "Statement defect: Two rank-typemax(Int) arrays with every dimension 1 and logical length 1 make promote_shape overflow the second-loop start rank + 1; Julia cannot construct the required typemax(Int)-entry shape tuples, so the statement needs each represented rank < typemax(Int)." }
]
def entriesArith8 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-sum-colon", juliaFile := "base/bitarray.jl",
    juliaFns := ["_sum(::BitArray, ::Colon)"],
    statement := "Whole-array Boolean sum equals the mathematical number of logical true bits and leaves the complete heap unchanged, including readable alias states.",
    source := "base/bitarray.jl:1722", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.SumColonContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16SumColon_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-map-not", juliaFile := "base/bitarray.jl",
    juliaFns := ["map(!, ::BitArray)", "map(~, ::BitArray)"],
    statement := "Allocating complement preserves actual ranked shape, creates fresh storage, complements each logical bit and leaves all pre-existing objects unchanged.",
    source := "base/bitarray.jl:1756", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapNotContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16MapNot_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-map-zero", juliaFile := "base/bitarray.jl",
    juliaFns := ["map(zero, ::BitArray)"],
    statement := "Allocating zero-map creates a fresh fully packed false array with the same logical length and ranked shape, preserving all old storage.",
    source := "base/bitarray.jl:1757", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapZeroContract, thm := none,
    notes := "No complete exact proof returned. No target-specific lemma completed; remaining goal: fresh allocation, ranked shape, false contents, packing, and preservation of prior storage." },
  { id := "bitarray-map-one", juliaFile := "base/bitarray.jl",
    juliaFns := ["map(one, ::BitArray)"],
    statement := "Allocating one-map returns a fresh fully packed all-true array of the same ranked shape, preserving every old object and alias.",
    source := "base/bitarray.jl:1758; required Bool fill dependency368-379", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapOneContract, thm := none,
    notes := "No complete exact proof returned. No target-specific lemma completed; remaining goal: fresh allocation, ranked shape, true contents, packing, and preservation of prior storage." },
  { id := "bitarray-map-identity", juliaFile := "base/bitarray.jl",
    juliaFns := ["map(identity, ::BitArray)"],
    statement := "Allocating identity-map returns an independent logical copy of the actual ranked shape and preserves every pre-existing memory and header.",
    source := "base/bitarray.jl:1759", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapIdentityContract, thm := none,
    notes := "No complete exact proof returned. No target-specific lemma completed; remaining goal: allocation of an independent logical copy with the ranked shape and preservation of prior storage." },
  { id := "bitarray-map-not-bang", juliaFile := "base/bitarray.jl",
    juliaFns := ["map!(!, ::BitArray, ::BitArray)", "map!(~, ::BitArray, ::BitArray)"],
    statement := "Complement-map! supports independent ranks, rejects short destinations before mutation, preserves the suffix and destination frame, and supports identical-view aliases.",
    source := "base/bitarray.jl:1761,1795-1813", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapNotBangContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16MapNotBang_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-map-zero-bang", juliaFile := "base/bitarray.jl",
    juliaFns := ["map!(zero, ::BitArray, ::BitArray)"],
    statement := "Constant-zero map! overwrites precisely the affected logical prefix, preserves the suffix and physical frame, and handles arbitrary source aliases.",
    source := "base/bitarray.jl:1762,1789-1793", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapZeroBangContract, thm := none,
    notes := "No complete exact proof returned. cmConstantShortRun, cmConstantEmptyRun, and cmConstantImpliesZero are retained; remaining goal: generic nonempty masked chunk fill with exact logical-prefix, suffix, frame, and packing preservation." },
  { id := "bitarray-map-one-bang", juliaFile := "base/bitarray.jl",
    juliaFns := ["map!(one, ::BitArray, ::BitArray)"],
    statement := "Constant-one map! overwrites precisely the affected logical prefix, preserves the suffix and physical frame, and handles arbitrary source aliases.",
    source := "base/bitarray.jl:1763,1789-1793", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapOneBangContract, thm := none,
    notes := "No complete exact proof returned. cmConstantShortRun, cmConstantEmptyRun, and cmConstantImpliesOne are retained; remaining goal: generic nonempty masked chunk fill with exact logical-prefix, suffix, frame, and packing preservation." },
  { id := "bitarray-map-identity-bang", juliaFile := "base/bitarray.jl",
    juliaFns := ["map!(identity, ::BitArray, ::BitArray)"],
    statement := "Identity map! copies the source logical prefix, leaves the destination suffix unchanged on documented snapshot-safe inputs, and reports BoundsError before writing a short destination.",
    source := "base/bitarray.jl:1764,429-447", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapIdentityBangContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16MapIdentityBang_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-map-binary", juliaFile := "base/bitarray.jl",
    juliaFns := ["map(::$T, ::BitArray, ::BitArray) [all fifteen generated tags]"],
    statement := "Every generated binary map preserves old storage, allocates a fresh packed result with the source-defined rank and shape, and maps the shorter logical input; incompatible equal-rank multidimensional shapes throw before allocation.",
    source := "base/bitarray.jl:1766-1787; base/iterators.jl:71-75,413-416; base/indices.jl:192-204", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapBinaryContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16MapBinary_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-map-binary-bang", juliaFile := "base/bitarray.jl",
    juliaFns := ["map!(::$T, ::BitArray, ::BitArray, ::BitArray) [all fifteen generated tags]"],
    statement := "Every generated binary map! checks destination capacity before mutation, maps the shortest prefix, preserves the destination suffix and physical frame, and supports independent ranks and documented aliases.",
    source := "base/bitarray.jl:1766-1778,1814-1835; base/abstractarray.jl:3563-3568", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.MapBinaryBangContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16MapBinaryBang_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." }
]
def entriesArith9 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-push-bool-frame", juliaFile := "base/bitarray.jl",
    juliaFns := ["push!(B::BitVector, item) [Bool specialization]"],
    statement := "Bool-valued push retains target identity and the global mutation frame. Its length field uses native wrapping; whenever no chunk growth is needed, that new length is committed before a possible scalar-write error, including alias-underbacked inputs.",
    source := "base/bitarray.jl:739-755; base/array.jl:1326-1349", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.PushBoolFrameAndCommittedLength, thm := none,
    notes := "No complete exact proof returned. The internal-growth factor equality and outer growth wrapper composition remain open." },
  { id := "bitarray-push-bool-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["push!(B::BitVector, item) [Bool specialization]"],
    statement := "Below native maximum length, Bool push appends the requested Boolean, preserves all old logical elements and zero padding, and returns the same mutable object. The full native capacity and offset domain is included, with exact no-mutation GenericMemory size errors when required growth exceeds the byte limit.",
    source := "base/bitarray.jl:739-755,1-23; base/array.jl:1326-1349; src/genericmemory.c:55-73", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.PushBoolAppendOneAndNativeLimits, thm := none,
    notes := "No complete exact proof returned. Growth, retained-prefix values, padding and size errors remain open." },
  { id := "bitarray-push-bool-native-wrap", juliaFile := "base/bitarray.jl",
    juliaFns := ["push!(B::BitVector, item) [Bool specialization]"],
    statement := "At typemax(Int) length, push stores typemin(Int). False returns without touching chunks. True passes the rank-one unsigned bounds check and addresses chunk 2^57, bit 63: readable backing permits that bit write and a successful return; missing or short backing yields BoundsError, and explicit unassigned raw cells yield undefinedReference. Every outcome retains the wrapped length and preserves other object headers; failed writes preserve the backing heap.",
    source := "base/bitarray.jl:122,675-692,745-754; base/abstractarray.jl:100-103,141,396,753", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.PushBoolNativeLengthWrap, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15PushBoolNativeWrap_proven,
    notes := "Extreme source-behavior invariant of the useful Bool specialization. Full physical capacity and malformed-boundary outcomes are classified without a convenient size restriction; 2^57 UInt64 words are within the native byte bound. Explicit unassigned-cell errors describe the existing Option-memory boundary, not native uninitialized UInt64 values. This is not a claimed documented correctness guarantee or a runtime-confirmed Julia defect." }
]
def entriesArith10 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-reused-mask-low-bits", juliaFile := "base/bitarray.jl",
    juliaFns := ["_msk_end(l::Int)", "_msk_end(B::BitArray)"],
    statement := "For every native signed length, both mask spellings return the low remainder bits set, with a full word when the length is divisible by 64.",
    source := "base/bitarray.jl:118-119", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedMaskEndLowBits,
    thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ReusedMaskLowBits_proven },
  { id := "bitarray-reused-chunk-address-full", juliaFile := "base/bitarray.jl",
    juliaFns := ["get_chunks_id(i::Int)"],
    statement := "Every signed scalar index maps to the mathematical quotient and remainder of its two's-complement wrapped predecessor.",
    source := "base/bitarray.jl:122", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedChunkAddressFull,
    thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ReusedChunkAddressFull_proven }
]
end JuliaLean.Proofs.base.bitarray

