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

namespace JuliaLean.CompletionState5

@[simp] theorem runBind {E S A B : Type} (action : ExceptT E (StateM S) A)
    (next : A → ExceptT E (StateM S) B) (state : S) :
    ((action >>= next).run state) =
      match action.run state with
      | (.ok value, final) => (next value).run final
      | (.error error, final) => (.error error, final) := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runMap {E S A B : Type} (action : ExceptT E (StateM S) A)
    (f : A → B) (state : S) :
    ((f <$> action).run state) =
      match action.run state with
      | (.ok value, final) => (.ok (f value), final)
      | (.error error, final) => (.error error, final) := by
  simp only [Functor.map, ExceptT.map, Bind.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runCatch {E S A : Type} (action : ExceptT E (StateM S) A)
    (handler : E → ExceptT E (StateM S) A) (state : S) :
    (tryCatchThe E action handler).run state =
      match action.run state with
      | (.ok value, final) => (.ok value, final)
      | (.error error, final) => (handler error).run final := by
  simp only [tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind,
    ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runPure {E S A : Type} (value : A) (state : S) :
    ((pure value : ExceptT E (StateM S) A).run state) = (.ok value, state) := rfl

@[simp] theorem runThrow {E S A : Type} (error : E) (state : S) :
    ((throwThe E error : ExceptT E (StateM S) A).run state) = (.error error, state) := rfl

@[simp] theorem runGet {E S : Type} (state : S) :
    ((get : ExceptT E (StateM S) S).run state) = (.ok state, state) := rfl

@[simp] theorem byteToListLength (bytes : ByteArray) : bytes.toList.length = bytes.size := by
  have loop : ∀ (i : Nat) (r : List UInt8),
      (ByteArray.toList.loop bytes i r).length = bytes.size - i + r.length := by
    intro i r
    fun_induction ByteArray.toList.loop bytes i r with
    | case1 i r h ih => simp only [List.length_cons] at ih; omega
    | case2 i r h => simp only [List.length_reverse]; omega
  exact loop 0 []


end JuliaLean.CompletionState5

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Range-level conversion errors do not change the mutable store. -/
theorem dequeConvertError {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (x : X) (e : JuliaLean.base.range.Exc) (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (Round5.Round2.convertBoolMutation x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [Round5.Round2.convertBoolMutation, h, Round5.Round2.liftRangeResult]
  rfl

/-- A rejected end-push conversion occurs before allocation or writes. -/
theorem dequePushConvertError {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (x : X) (e : JuliaLean.base.range.Exc) (B : BitVector) (s : State)
    (check : BitVector → I64 → BitMutationM Unit)
    (h : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (bitVectorPush Round5.Round2.convertBoolMutation check B x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [bitVectorPush, shape_run_bind, dequeConvertError x e s h]

/-- A rejected front-push conversion occurs before allocation or writes. -/
theorem dequePushfirstConvertError {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (x : X) (e : JuliaLean.base.range.Exc) (B : BitVector) (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (bitVectorPushfirst Round5.Round2.convertBoolMutation B x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [bitVectorPushfirst, shape_run_bind, dequeConvertError x e s h]

/-- The complete failed-conversion branch of the frozen deque property. -/
theorem dequeFrozenConvertError {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (xs : List Bool) (x : X) (e : JuliaLean.base.range.Exc)
    (h : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    Round5.Round2.DequeAgrees xs x := by
  simp only [Round5.Round2.DequeAgrees, h,
    dequePushConvertError x e (vectorBits xs) (initWords (encodeBits xs))
      Round5.Round2.checkBitVectorBounds h,
    dequePushfirstConvertError x e (vectorBits xs) (initWords (encodeBits xs)) h]
  exact ⟨True.intro, True.intro⟩

/-- End-pop rejects a zero-length vector before using its accessors. -/
theorem dequePopEmpty (getindex : BitVector → I64 → BitMutationM Bool)
    (setindex : BitVector → Bool → I64 → BitMutationM BitVector)
    (B : BitVector) (s : State) (h : B.len = int 0) :
    (bitVectorPop getindex setindex B).run s =
      (.error (.argument "argument must not be empty"), s) := by
  simp only [bitVectorPop, h, beq_self_eq_true, ite_true]
  rfl

/-- Front-pop rejects a zero-length vector before reading any chunk. -/
theorem dequePopfirstEmpty (B : BitVector) (s : State) (h : B.len = int 0) :
    (bitVectorPopfirst B).run s =
      (.error (.argument "argument must not be empty"), s) := by
  simp only [bitVectorPopfirst, h, beq_self_eq_true, ite_true]
  rfl

/-- Invalid insertion positions are rejected before conversion or mutation. -/
theorem insertOutside {X : Type} (convert : X → BitMutationM Bool)
    (B : BitVector) (i : I64) (x : X) (s : State)
    (h : ¬ (int 1 ≤ i ∧ i ≤ B.len + int 1)) :
    (bitVectorInsertInt convert B i x).run s = (.error .bounds, s) := by
  simp only [bitVectorInsertInt, h, decide_false, Bool.not_false, ite_true]
  rfl

/-- A valid insertion with a failed conversion leaves all memory unchanged. -/
theorem insertConvertError {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (B : BitVector) (i : I64) (x : X) (e : JuliaLean.base.range.Exc) (s : State)
    (hi : int 1 ≤ i ∧ i ≤ B.len + int 1)
    (hx : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (bitVectorInsertInt Round5.Round2.convertBoolMutation B i x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [bitVectorInsertInt, hi, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_run_bind, dequeConvertError x e s hx]

/-- The integer public wrapper preserves the insertion error and its store. -/
theorem insertPublicConvertError {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (B : BitVector) (i : I64) (x : X) (e : JuliaLean.base.range.Exc) (s : State)
    (hi : int 1 ≤ i ∧ i ≤ B.len + int 1)
    (hx : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (bitVectorInsert id (bitVectorInsertInt Round5.Round2.convertBoolMutation)
      B i x).run s = (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  exact insertConvertError B i x e s hi hx

/-- Invalid scalar deletions fail before touching the packed representation. -/
theorem deleteOutside (B : BitVector) (i : I64) (s : State)
    (h : ¬ (int 1 ≤ i ∧ i ≤ B.len)) :
    (bitVectorDeleteAt (fun _ : I64 => false) (fun _ => pure ()) id B i).run s =
      (.error .bounds, s) := by
  simp only [bitVectorDeleteAt, id_eq, Bool.false_eq_true, ite_false, h,
    decide_false, Bool.not_false, ite_true]
  rfl

/-- The frozen size hypothesis prevents incrementing a length from wrapping. -/
theorem dequeLengthSucc (n : Nat) (h : n < Round5.maxVectorLength) :
    int n + int 1 = int (n + 1 : Nat) := by
  rw [packedInt_add]
  rfl

/-- Length values under the frozen bound are their mathematical naturals. -/
theorem dequeLengthVal (n : Nat) (h : n < Round5.maxVectorLength) :
    (int n).val = (n : Int) := by
  apply packedInt_val
  change n < 4611686018427387903 at h
  omega

/-- A valid insertion bound agrees with the one used by the packed algorithm. -/
theorem insertBoundsAgree (xs : List Bool) (i : I64)
    (h : xs.length + 1 < Round5.maxVectorLength) :
    (int 1 ≤ i ∧ i ≤ int (xs.length + 1 : Nat)) ↔
      (int 1 ≤ i ∧ i ≤ (vectorBits xs).len + int 1) := by
  change (int 1 ≤ i ∧ i ≤ int (xs.length + 1 : Nat)) ↔
    (int 1 ≤ i ∧ i ≤ int xs.length + int 1)
  rw [dequeLengthSucc xs.length (by omega)]

/-- A false push into an existing partial chunk performs no writes. -/
theorem dequePushFalseNoGrow {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (B : BitVector) (x : X) (s : State)
    (check : BitVector → I64 → BitMutationM Unit)
    (hx : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok false)
    (hn : (mod64 B.len == int 0) = false) :
    (bitVectorPush Round5.Round2.convertBoolMutation check B x).run s =
      (.ok { B with len := B.len + int 1 }, s) := by
  simp only [bitVectorPush, shape_run_bind, dequeConvertOk x false s hx,
    hn, Bool.false_eq_true, ite_false, shape_run_pure]
  rfl

theorem dequePackedLeftOne (word : U64) (k : Nat) :
    packedBit (shl_int word (int 1)) k =
      (decide (k < 64) && (decide (1 ≤ k) && packedBit word (k - 1))) :=
  dequePackedShiftLeft word 1 k (by decide)

theorem dequePackedRightOne (word : U64) (k : Nat) :
    packedBit (lshr_int word (int 1)) k =
      (decide (k < 64) && packedBit word (k + 1)) :=
  dequePackedShiftRight word 1 k (by decide)

theorem dequePackedLeft63 (word : U64) (k : Nat) :
    packedBit (shl_int word (int 63)) k =
      (decide (k < 64) && (decide (63 ≤ k) && packedBit word (k - 63))) :=
  dequePackedShiftLeft word 63 k (by decide)

theorem dequePackedRight63 (word : U64) (k : Nat) :
    packedBit (lshr_int word (int 63)) k =
      (decide (k < 64) && packedBit word (k + 63)) :=
  dequePackedShiftRight word 63 k (by decide)

/-- One packed-word step of the front-push and insertion carry loops. -/
theorem dequePackedCarryLeft (current previous : U64) (k : Nat) (hk : k < 64) :
    packedBit (or_int (shl_int current (int 1))
      (lshr_int previous (int 63))) k =
      if k = 0 then packedBit previous 63 else packedBit current (k - 1) := by
  rw [packedBit_or, dequePackedLeftOne current k,
    dequePackedRight63 previous k]
  by_cases hz : k = 0
  · subst k
    rfl
  · have hpos : 1 ≤ k := by omega
    have hhigh : 64 ≤ k + 63 := by omega
    rw [if_neg hz, dequePackedBitHigh previous (k + 63) hhigh]
    simp only [hk, hpos, decide_true, Bool.true_and, Bool.and_false, Bool.or_false]

/-- One packed-word step of the front-pop and deletion carry loops. -/
theorem dequePackedCarryRight (current next : U64) (k : Nat) (hk : k < 64) :
    packedBit (or_int (lshr_int current (int 1))
      (shl_int next (int 63))) k =
      if k = 63 then packedBit next 0 else packedBit current (k + 1) := by
  rw [packedBit_or, dequePackedRightOne current k,
    dequePackedLeft63 next k]
  by_cases htop : k = 63
  · subst k
    rw [dequePackedBitHigh current (63 + 1) (by decide)]
    rfl
  · have hlow : ¬ 63 ≤ k := by omega
    rw [if_neg htop]
    simp only [hk, hlow, decide_true, decide_false, Bool.true_and,
      Bool.false_and, Bool.or_false]

/-- Bitwise complement flips precisely the 64 stored bits. -/
theorem dequePackedNot (a : U64) (k : Nat) :
    packedBit (not_int a) k = (decide (k < 64) && !packedBit a k) := by
  simp only [not_int, jlNotInt, packedBit_toJInt, BitVec.getLsbD_not,
    packedBit_fromJInt]
  rfl

/-- A Boolean stored as a machine word occupies only bit zero. -/
theorem dequePackedBool (value : Bool) (k : Nat) :
    packedBit (u64 (if value then 1 else 0)) k =
      if k = 0 then value else false := by
  cases value
  · change packedBit (u64 0) k = if k = 0 then false else false
    rw [packedBit_zero]
    exact (ite_self false).symm
  · change Nat.testBit 1 k = if k = 0 then true else false
    rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    by_cases hk : k = 0
    · subst k
      rfl
    · simp only [hk, Ne.symm hk, decide_false, ite_false]

/-- Cons indexing expressed in the zero-based offsets used by packed words. -/
theorem dequeGetCons (xs : List Bool) (value : Bool) (k : Nat) :
    (value :: xs).getD k false =
      if k = 0 then value else xs.getD (k - 1) false := by
  cases k <;> rfl

/-- Dropping the first logical bit advances each packed index by one. -/
theorem dequeGetDropOne (xs : List Bool) (k : Nat) :
    (xs.drop 1).getD k false = xs.getD (k + 1) false := by
  cases xs <;> rfl

/-- The initial word of a front-push is exactly the encoded cons word. -/
theorem dequePackedConsFirst (xs : List Bool) (value : Bool) :
    or_int (u64 (if value then 1 else 0))
      (shl_int (packedPrefix xs 0 64) (int 1)) =
        packedPrefix (value :: xs) 0 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedBit_or, dequePackedBool, dequePackedLeftOne _ k,
    packedWord_bit (value :: xs) 0 k hk]
  rw [dequeGetCons]
  simp only [Nat.zero_mul, Nat.zero_add]
  by_cases hz : k = 0
  · subst k
    cases value <;> rfl
  · have hp : 1 ≤ k := by omega
    have hkm : k - 1 < 64 := by omega
    rw [packedWord_bit xs 0 (k - 1) hkm]
    simp only [hz, hp, hk, decide_true, Bool.true_and, ite_false,
      Bool.false_or, Nat.zero_mul, Nat.zero_add]

/-- Every later front-push word combines a left shift with the prior carry. -/
theorem dequePackedConsLater (xs : List Bool) (value : Bool) (chunk : Nat) :
    or_int (shl_int (packedPrefix xs (chunk + 1) 64) (int 1))
      (lshr_int (packedPrefix xs chunk 64) (int 63)) =
        packedPrefix (value :: xs) (chunk + 1) 64 := by
  apply packedBit_ext
  intro k hk
  rw [dequePackedCarryLeft _ _ k hk, packedWord_bit (value :: xs) (chunk + 1) k hk,
    dequeGetCons]
  have hindex : (chunk + 1) * 64 + k ≠ 0 := by omega
  rw [if_neg hindex]
  by_cases hz : k = 0
  · subst k
    rw [if_pos rfl, packedWord_bit xs chunk 63 (by decide)]
    congr 1
    omega
  · rw [if_neg hz, packedWord_bit xs (chunk + 1) (k - 1) (by omega)]
    congr 1
    omega

/-- The front-pop word formula is exactly the encoding of a one-bit drop. -/
theorem dequePackedDropFirst (xs : List Bool) (chunk : Nat) :
    or_int (lshr_int (packedPrefix xs chunk 64) (int 1))
      (shl_int (packedPrefix xs (chunk + 1) 64) (int 63)) =
        packedPrefix (xs.drop 1) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [dequePackedCarryRight _ _ k hk, packedWord_bit (xs.drop 1) chunk k hk,
    dequeGetDropOne]
  by_cases htop : k = 63
  · subst k
    rw [if_pos rfl, packedWord_bit xs (chunk + 1) 0 (by decide)]
    congr 1
    omega
  · rw [if_neg htop, packedWord_bit xs chunk (k + 1) (by omega)]
    congr 1 <;> omega

/-- Decrementing a positive natural index stays within the machine interval. -/
theorem dequeIntPred (j : Nat) (hj : j + 1 ≤ 9223372036854775807) :
    int ((j + 1 : Nat) : Int) - int 1 = int j := by
  apply Subtype.ext
  change wrapInt .i64 ((int ((j + 1 : Nat) : Int)).val - 1) = (int j).val
  rw [packedInt_val (j + 1) hj, packedInt_val j (by omega)]
  have he : ((j + 1 : Nat) : Int) - 1 = (j : Int) := by omega
  rw [he]
  exact wrapInt_of_inRange .i64 _ ⟨by change -9223372036854775808 ≤ (j : Int); omega,
    by change (j : Int) ≤ 9223372036854775807; omega⟩

/-- The list operation performed by one iteration of a left-carry loop. -/
def dequeCarryLeftStep (words : List U64) (j : Nat) : List U64 :=
  words.set j (or_int (shl_int (words.getD j (u64 0)) (int 1))
    (lshr_int (words.getD (j - 1) (u64 0)) (int 63)))
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Descending carry updates read each source word before that word is overwritten. -/
theorem dequeCarryLeftFoldGet (indices : List Nat) :
    ∀ (words : List U64),
      (∀ j ∈ indices, 0 < j ∧ j < words.length) →
      List.Pairwise (fun a b : Nat => b < a) indices →
      ∀ k : Nat,
      (indices.foldl dequeCarryLeftStep words).getD k (u64 0) =
        if k ∈ indices then
          or_int (shl_int (words.getD k (u64 0)) (int 1))
            (lshr_int (words.getD (k - 1) (u64 0)) (int 63))
        else words.getD k (u64 0) := by
  induction indices with
  | nil =>
    intro words _ _ k
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons j indices ih =>
    intro words hi hs k
    have hj := hi j List.mem_cons_self
    have hpair := List.pairwise_cons.mp hs
    have hrec := ih (dequeCarryLeftStep words j)
      (by intro q hq; simpa only [dequeCarryLeftStep, List.length_set]
          using hi q (List.mem_cons_of_mem j hq)) hpair.2 k
    rw [List.foldl_cons, hrec]
    by_cases hk : k ∈ indices
    · have hkj : k < j := hpair.1 k hk
      have hkn : j ≠ k := by omega
      have hkp : j ≠ k - 1 := by omega
      simp only [hk, List.mem_cons_of_mem j hk, ite_true, dequeCarryLeftStep,
        dequeWordGetSet words j k _ hj.2, dequeWordGetSet words j (k - 1) _ hj.2,
        hkn, hkp, ite_false]
    · simp only [hk, ite_false, dequeCarryLeftStep,
        dequeWordGetSet words j k _ hj.2]
      by_cases he : j = k
      · subst k
        simp only [List.mem_cons_self, ite_true]
      · have hmem : ¬ k ∈ j :: indices := by
          intro hm
          rcases List.mem_cons.mp hm with hm | hm
          · exact he hm.symm
          · exact hk hm
        simp only [he, hmem, ite_false]

theorem dequeTailContents (words : List U64) (tail : List (Option U64))
    (hn : words.length ≤ 9223372036854775807) :
    (dequeTailStore words tail).contents 0 = words.map some := by
  change ((words.map some ++ tail).drop 0).take
    (int words.length).val.toNat = words.map some
  rw [packedInt_val words.length hn, Int.toNat_natCast, List.drop_zero]
  exact List.take_left' (List.length_map ..)

/-- Growing by one logical bit needs a new word exactly at a word boundary. -/
theorem dequeWordCountSucc (n : Nat) :
    wordCount (n + 1) = if n % 64 = 0 then wordCount n + 1 else wordCount n := by
  unfold wordCount
  split <;> omega

/-- The logical chunk list immediately after the growth phase of a push. -/
def dequeGrownWords (xs : List Bool) : List U64 :=
  if xs.length % 64 = 0 then encodeBits xs ++ [u64 0] else encodeBits xs

/-- Growth is the same packing map extended to the next required chunk count. -/
theorem dequeGrownWordsRange (xs : List Bool) :
    dequeGrownWords xs = (List.range (wordCount (xs.length + 1))).map
      (fun c => packedPrefix xs c 64) := by
  unfold dequeGrownWords
  rw [dequeWordCountSucc]
  by_cases hm : xs.length % 64 = 0
  · rw [if_pos hm, if_pos hm, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]
    rw [dequePackedBeyond xs (wordCount xs.length) (by unfold wordCount; omega)]
    rw [packedPrefix_eq_encode]
  · rw [if_neg hm, if_neg hm, packedPrefix_eq_encode]

/-- The growth phase has the correct number of chunks for the extended vector. -/
theorem dequeGrownWordsLength (xs : List Bool) :
    (dequeGrownWords xs).length = wordCount (xs.length + 1) := by
  rw [dequeGrownWordsRange, List.length_map, List.length_range]

/-- Each grown chunk still contains the original bits, including zero padding. -/
theorem dequeGrownWordsGet (xs : List Bool) (c : Nat)
    (hc : c < wordCount (xs.length + 1)) :
    (dequeGrownWords xs).getD c (u64 0) = packedPrefix xs c 64 := by
  rw [← List.getElem_eq_getD (h := by rw [dequeGrownWordsLength]; exact hc)]
  simp only [dequeGrownWordsRange, List.getElem_map, List.getElem_range]

/-- Appending the default bit preserves every padded logical observation. -/
theorem dequeAppendFalseGet (xs : List Bool) (k : Nat) :
    (xs ++ [false]).getD k false = xs.getD k false := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons b xs ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

/-- Appending a false bit preserves each word's old bit pattern. -/
theorem dequePackedAppendFalse (xs : List Bool) (c : Nat) :
    packedPrefix (xs ++ [false]) c 64 = packedPrefix xs c 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk, dequeAppendFalseGet]

/-- The push growth phase is exactly the encoding of an appended false bit. -/
theorem dequeEncodeAppendFalse (xs : List Bool) :
    encodeBits (xs ++ [false]) = dequeGrownWords xs := by
  rw [packedPrefix_eq_encode, dequeGrownWordsRange]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
  apply List.map_congr_left
  intro c _
  exact dequePackedAppendFalse xs c

/-- Word shifts retain the number of chunks. -/
theorem dequeCarryLeftFoldLength (indices : List Nat) (words : List U64) :
    (indices.foldl dequeCarryLeftStep words).length = words.length := by
  induction indices generalizing words with
  | nil => rfl
  | cons j indices ih =>
    rw [List.foldl_cons, ih]
    exact List.length_set

/-- Zero-based chunk indices used by the descending carry loop. -/
def dequeLeftIndices (n : Nat) : List Nat :=
  (List.range (n - 1)).reverse.map (fun j => j + 1)

theorem dequeLeftIndicesMem (n k : Nat) :
    k ∈ dequeLeftIndices n ↔ 1 ≤ k ∧ k < n := by
  simp only [dequeLeftIndices, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · intro hk
    exact ⟨k - 1, by omega, by omega⟩

theorem dequeDescendingRangeSorted (n : Nat) :
    List.Pairwise (fun a b : Nat => b < a)
      ((List.range n).reverse.map (fun j => j + 1)) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.map_cons]
    refine List.Pairwise.cons ?_ ih
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have hn : j < n := List.mem_range.mp (List.mem_reverse.mp hj)
    omega

/-- All iterations in the front-push carry loop lie in descending chunk order. -/
theorem dequeLeftIndicesSorted (n : Nat) :
    List.Pairwise (fun a b : Nat => b < a) (dequeLeftIndices n) :=
  dequeDescendingRangeSorted (n - 1)

/-- The pure chunk expression computed by front-push after its growth phase. -/
def dequeFrontWords (xs : List Bool) (value : Bool) : List U64 :=
  let words := dequeGrownWords xs
  let shifted := (dequeLeftIndices words.length).foldl dequeCarryLeftStep words
  shifted.set 0 (or_int (u64 (if value then 1 else 0))
    (shl_int (shifted.getD 0 (u64 0)) (int 1)))

/-- The complete packed carry expression encodes a Boolean cons exactly. -/
theorem dequeFrontWordsEncode (xs : List Bool) (value : Bool) :
    dequeFrontWords xs value = encodeBits (value :: xs) := by
  let words := dequeGrownWords xs
  let indices := dequeLeftIndices words.length
  let shifted := indices.foldl dequeCarryLeftStep words
  have hlen : words.length = wordCount (xs.length + 1) := dequeGrownWordsLength xs
  have hpos : 0 < words.length := by rw [hlen]; unfold wordCount; omega
  have hib : ∀ j ∈ indices, 0 < j ∧ j < words.length := by
    intro j hj
    exact (dequeLeftIndicesMem words.length j).mp hj
  have hfold := dequeCarryLeftFoldGet indices words hib
    (dequeLeftIndicesSorted words.length)
  have hz : ¬ 0 ∈ indices := by
    rw [dequeLeftIndicesMem]
    omega
  have hzero : shifted.getD 0 (u64 0) = packedPrefix xs 0 64 := by
    rw [hfold 0, if_neg hz]
    exact dequeGrownWordsGet xs 0 (by rw [← hlen]; exact hpos)
  have hslen : shifted.length = words.length := dequeCarryLeftFoldLength indices words
  have hfirst : or_int (u64 (if value then 1 else 0))
      (shl_int (shifted.getD 0 (u64 0)) (int 1)) = packedPrefix (value :: xs) 0 64 := by
    rw [hzero]
    exact dequePackedConsFirst xs value
  change shifted.set 0 _ = _
  rw [hfirst]
  apply List.ext_getElem
  · rw [List.length_set, hslen, hlen, packedEncoded_length]
    rfl
  · intro k hk hk'
    rw [List.getElem_eq_getD (fallback := u64 0)]
    rw [dequeWordGetSet shifted 0 k _ (by rw [hslen]; exact hpos)]
    have hkbound : k < words.length := by
      simpa only [List.length_set, hslen] using hk
    have hk64 : k < wordCount (xs.length + 1) := by rw [← hlen]; exact hkbound
    have hout : (encodeBits (value :: xs))[k] = packedPrefix (value :: xs) k 64 := by
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rw [hout]
    by_cases he : 0 = k
    · subst k
      rw [if_pos rfl]
    · rw [if_neg he, hfold k]
      have hkp : 1 ≤ k := by omega
      have hmem : k ∈ indices := (dequeLeftIndicesMem words.length k).mpr ⟨hkp, hkbound⟩
      rw [if_pos hmem]
      rw [dequeGrownWordsGet xs k hk64,
        dequeGrownWordsGet xs (k - 1) (by omega)]
      have hck : k - 1 + 1 = k := by omega
      have hcarry := dequePackedConsLater xs value (k - 1)
      rw [hck] at hcarry
      exact hcarry
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- A single left-carry action, kept separate from its loop. -/
def dequeCarryLeftAction (j : Nat) : BitMutationM Unit := do
  let i := int ((j + 1 : Nat) : Int)
  let current ← mutableGet 0 i
  let previous ← mutableGet 0 (i - int 1)
  mutableSet 0 (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) i

/-- A carry action uses two read-only observations and one write. -/
theorem dequeCarryLeftActionRaw (s s' : State) (j : Nat) (current previous : U64)
    (hc : (mutableGet 0 (int ((j + 1 : Nat) : Int))).run s = (.ok current, s))
    (hp : (mutableGet 0 (int ((j + 1 : Nat) : Int) - int 1)).run s = (.ok previous, s))
    (hs : (mutableSet 0 (or_int (shl_int current (int 1)) (lshr_int previous (int 63)))
      (int ((j + 1 : Nat) : Int))).run s = (.ok (), s')) :
    (dequeCarryLeftAction j).run s = (.ok (), s') := by
  simp only [dequeCarryLeftAction, shape_run_bind, hc, hp, hs]

theorem dequeCarryLeftActionRun (words : List U64) (spare j : Nat)
    (hn : words.length ≤ 9223372036854775807) (hj : 0 < j ∧ j < words.length) :
    (dequeCarryLeftAction j).run (dequeWordStore words spare) =
      (.ok (), dequeWordStore (dequeCarryLeftStep words j) spare) := by
  have hcur := dequeWordRead words spare j hn hj.2
  have hprev := dequeWordRead words spare (j - 1) hn (by omega)
  rw [show j - 1 + 1 = j by omega] at hprev
  have hset := dequeWordSet words spare j
    (or_int (shl_int (words.getD j (u64 0)) (int 1))
      (lshr_int (words.getD (j - 1) (u64 0)) (int 63))) hn hj.2
  have hp : (mutableGet 0 (int ((j + 1 : Nat) : Int) - int 1)).run
      (dequeWordStore words spare) =
        (.ok (words.getD (j - 1) (u64 0)), dequeWordStore words spare) := by
    rw [dequeIntPred j (by omega)]
    exact hprev
  exact dequeCarryLeftActionRaw _ _ j _ _ hcur hp hset


/-- The concrete left-carry loop implements the list fold proved above. -/
theorem dequeCarryLeftLoop (indices : List Nat) (words : List U64) (spare : Nat)
    (hn : words.length ≤ 9223372036854775807)
    (hi : ∀ j ∈ indices, 0 < j ∧ j < words.length) :
    (forIn (indices.map (fun j => int ((j + 1 : Nat) : Int))) PUnit.unit
      (fun i _ => do
        let current ← mutableGet 0 i
        let previous ← mutableGet 0 (i - int 1)
        mutableSet 0 (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) i
        pure (ForInStep.yield PUnit.unit))).run (dequeWordStore words spare) =
      (.ok PUnit.unit, dequeWordStore (indices.foldl dequeCarryLeftStep words) spare) := by
  have hf := dequeForInFold dequeCarryLeftAction dequeCarryLeftStep
    (fun ws => dequeWordStore ws spare) (fun ws => ws.length = words.length) indices
    (by
      intro ws hw j hj
      apply dequeCarryLeftActionRun ws spare j
      · rw [hw]
        exact hn
      · rw [hw]
        exact hi j hj)
    (by
      intro ws hw j _
      simp only [dequeCarryLeftStep, List.length_set, hw]) words rfl
  rw [List.forIn_map]
  simpa only [dequeCarryLeftAction, bind_assoc] using hf

/-- The list update performed by a front-pop or deletion carry iteration. -/
def dequeCarryRightStep (words : List U64) (j : Nat) : List U64 :=
  words.set j (or_int (lshr_int (words.getD j (u64 0)) (int 1))
    (shl_int (words.getD (j + 1) (u64 0)) (int 63)))

/-- Every packed right-carry iteration retains the number of words. -/
theorem dequeCarryRightFoldLength (indices : List Nat) (words : List U64) :
    (indices.foldl dequeCarryRightStep words).length = words.length := by
  induction indices generalizing words with
  | nil => rfl
  | cons j indices ih =>
    rw [List.foldl_cons, ih]
    exact List.length_set

/-- Ascending updates use original source words before those words are overwritten. -/
theorem dequeCarryRightFoldGet (indices : List Nat) :
    ∀ (words : List U64),
      (∀ j ∈ indices, j + 1 < words.length) →
      List.Pairwise (fun a b : Nat => a < b) indices →
      ∀ k : Nat,
      (indices.foldl dequeCarryRightStep words).getD k (u64 0) =
        if k ∈ indices then
          or_int (lshr_int (words.getD k (u64 0)) (int 1))
            (shl_int (words.getD (k + 1) (u64 0)) (int 63))
        else words.getD k (u64 0) := by
  induction indices with
  | nil =>
    intro words _ _ k
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons j indices ih =>
    intro words hi hs k
    have hj := hi j List.mem_cons_self
    have hpair := List.pairwise_cons.mp hs
    have hrec := ih (dequeCarryRightStep words j)
      (by intro q hq; simpa only [dequeCarryRightStep, List.length_set]
          using hi q (List.mem_cons_of_mem j hq)) hpair.2 k
    rw [List.foldl_cons, hrec]
    by_cases hk : k ∈ indices
    · have hjk : j < k := hpair.1 k hk
      have hkn : j ≠ k := by omega
      have hkp : j ≠ k + 1 := by omega
      simp only [hk, List.mem_cons_of_mem j hk, ite_true, dequeCarryRightStep,
        dequeWordGetSet words j k _ (by omega), dequeWordGetSet words j (k + 1) _ (by omega),
        hkn, hkp, ite_false]
    · simp only [hk, ite_false, dequeCarryRightStep,
        dequeWordGetSet words j k _ (by omega)]
      by_cases he : j = k
      · subst k
        simp only [List.mem_cons_self, ite_true]
      · have hmem : ¬ k ∈ j :: indices := by
          intro hm
          rcases List.mem_cons.mp hm with hm | hm
          · exact he hm.symm
          · exact hk hm
        simp only [he, hmem, ite_false]

/-- The final front-pop chunk needs no carry from a nonexistent next chunk. -/
theorem dequePackedDropLast (xs : List Bool) (chunk : Nat)
    (hc : xs.length ≤ (chunk + 1) * 64) :
    lshr_int (packedPrefix xs chunk 64) (int 1) = packedPrefix (xs.drop 1) chunk 64 := by
  have h := dequePackedDropFirst xs chunk
  rw [dequePackedBeyond xs (chunk + 1) hc] at h
  have hz : shl_int (u64 0) (int 63) = u64 0 := rfl
  rw [hz, dequePackedOrZero] at h
  exact h

/-- A one-bit removal drops a whole word exactly when its final word held one bit. -/
theorem dequeWordCountPred (n : Nat) (hn : 0 < n) :
    wordCount (n - 1) = if n % 64 = 1 then wordCount n - 1 else wordCount n := by
  unfold wordCount
  split <;> omega

/-- The pure packed expression computed by front-pop. -/
def dequeDropWords (xs : List Bool) : List U64 :=
  let words := encodeBits xs
  let shifted := (List.range (words.length - 1)).foldl dequeCarryRightStep words
  if xs.length % 64 = 1 then shifted.take (words.length - 1)
  else shifted.set (words.length - 1)
    (lshr_int (shifted.getD (words.length - 1) (u64 0)) (int 1))

/-- The complete front-pop chunk expression encodes dropping the first Boolean. -/
theorem dequeDropWordsEncode (xs : List Bool) (hxs : 0 < xs.length) :
    dequeDropWords xs = encodeBits (xs.drop 1) := by
  let words := encodeBits xs
  let shifted := (List.range (words.length - 1)).foldl dequeCarryRightStep words
  have hlen : words.length = wordCount xs.length := packedEncoded_length xs
  have hpos : 0 < words.length := by rw [hlen]; unfold wordCount; omega
  have hslen : shifted.length = words.length := dequeCarryRightFoldLength _ words
  have hib : ∀ j ∈ List.range (words.length - 1), j + 1 < words.length := by
    intro j hj
    have hj' := List.mem_range.mp hj
    omega
  have hfold := dequeCarryRightFoldGet (List.range (words.length - 1)) words hib
    List.pairwise_lt_range
  have hinner (k : Nat) (hk : k < words.length - 1) :
      shifted.getD k (u64 0) = packedPrefix (xs.drop 1) k 64 := by
    rw [hfold k, if_pos (List.mem_range.mpr hk)]
    rw [dequeEncodedGet xs k (by rw [← hlen]; omega),
      dequeEncodedGet xs (k + 1) (by rw [← hlen]; omega)]
    exact dequePackedDropFirst xs k
  have hlast : shifted.getD (words.length - 1) (u64 0) =
      packedPrefix xs (words.length - 1) 64 := by
    rw [hfold (words.length - 1), if_neg (by simp only [List.mem_range, Nat.lt_irrefl, not_false_eq_true])]
    exact dequeEncodedGet xs (words.length - 1) (by rw [← hlen]; omega)
  have hlastShift : lshr_int (shifted.getD (words.length - 1) (u64 0)) (int 1) =
      packedPrefix (xs.drop 1) (words.length - 1) 64 := by
    rw [hlast]
    apply dequePackedDropLast
    rw [hlen]
    unfold wordCount
    omega
  by_cases hm : xs.length % 64 = 1
  · unfold dequeDropWords
    rw [if_pos hm]
    change shifted.take (words.length - 1) = _
    apply List.ext_getElem
    · rw [List.length_take, hslen, Nat.min_eq_left (by omega), packedEncoded_length (xs.drop 1),
        List.length_drop, dequeWordCountPred xs.length hxs, if_pos hm, hlen]
    · intro k hk hk'
      rw [List.getElem_take, List.getElem_eq_getD (fallback := u64 0)]
      have hkbound : k < words.length - 1 := by
        have hkt := hk
        rw [List.length_take, hslen, Nat.min_eq_left (by omega)] at hkt
        exact hkt
      rw [hinner k hkbound]
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  · unfold dequeDropWords
    rw [if_neg hm]
    change shifted.set (words.length - 1) _ = _
    rw [hlastShift]
    apply List.ext_getElem
    · rw [List.length_set, hslen, packedEncoded_length (xs.drop 1), List.length_drop,
        dequeWordCountPred xs.length hxs, if_neg hm, hlen]
    · intro k hk hk'
      have hkbound : k < words.length := by simpa only [List.length_set, hslen] using hk
      rw [List.getElem_eq_getD (fallback := u64 0),
        dequeWordGetSet shifted (words.length - 1) k _ (by rw [hslen]; omega)]
      have hout : (encodeBits (xs.drop 1))[k] = packedPrefix (xs.drop 1) k 64 := by
        simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
      rw [hout]
      by_cases he : words.length - 1 = k
      · subst k
        rw [if_pos rfl]
      · rw [if_neg he]
        exact hinner k (by omega)

def dequeCarryRightAction (j : Nat) : BitMutationM Unit := do
  let i := int ((j + 1 : Nat) : Int)
  let current ← mutableGet 0 i
  let next ← mutableGet 0 (i + int 1)
  mutableSet 0 (or_int (lshr_int current (int 1)) (shl_int next (int 63))) i

/-- An ascending carry action is verified from its three primitive outcomes. -/
theorem dequeCarryRightActionRaw (s s' : State) (j : Nat) (current next : U64)
    (hc : (mutableGet 0 (int ((j + 1 : Nat) : Int))).run s = (.ok current, s))
    (hn : (mutableGet 0 (int ((j + 1 : Nat) : Int) + int 1)).run s = (.ok next, s))
    (hs : (mutableSet 0 (or_int (lshr_int current (int 1)) (shl_int next (int 63)))
      (int ((j + 1 : Nat) : Int))).run s = (.ok (), s')) :
    (dequeCarryRightAction j).run s = (.ok (), s') := by
  simp only [dequeCarryRightAction, shape_run_bind, hc, hn, hs]

/-- One concrete right-carry action changes exactly the indicated chunk. -/
theorem dequeCarryRightActionRun (words : List U64) (spare j : Nat)
    (hn : words.length ≤ 9223372036854775807) (hj : j + 1 < words.length) :
    (dequeCarryRightAction j).run (dequeWordStore words spare) =
      (.ok (), dequeWordStore (dequeCarryRightStep words j) spare) := by
  have hcur := dequeWordRead words spare j hn (by omega)
  have hnext := dequeWordRead words spare (j + 1) hn hj
  have hset := dequeWordSet words spare j
    (or_int (lshr_int (words.getD j (u64 0)) (int 1))
      (shl_int (words.getD (j + 1) (u64 0)) (int 63))) hn (by omega)
  have hnext' : (mutableGet 0 (int ((j + 1 : Nat) : Int) + int 1)).run
      (dequeWordStore words spare) =
        (.ok (words.getD (j + 1) (u64 0)), dequeWordStore words spare) := by
    rw [dequeNatAddOne (j + 1)]
    exact hnext
  exact dequeCarryRightActionRaw _ _ j _ _ hcur hnext' hset

/-- Concrete ascending carry writes implement a list fold without changing capacity. -/
theorem dequeCarryRightLoop (indices : List Nat) (words : List U64) (spare : Nat)
    (hn : words.length ≤ 9223372036854775807)
    (hi : ∀ j ∈ indices, j + 1 < words.length) :
    (forIn (indices.map (fun j => int ((j + 1 : Nat) : Int))) PUnit.unit
      (fun i _ => do
        let current ← mutableGet 0 i
        let next ← mutableGet 0 (i + int 1)
        mutableSet 0 (or_int (lshr_int current (int 1)) (shl_int next (int 63))) i
        pure (ForInStep.yield PUnit.unit))).run (dequeWordStore words spare) =
      (.ok PUnit.unit, dequeWordStore (indices.foldl dequeCarryRightStep words) spare) := by
  have hf := dequeForInFold dequeCarryRightAction dequeCarryRightStep
    (fun ws => dequeWordStore ws spare) (fun ws => ws.length = words.length) indices
    (by
      intro ws hw j hj
      apply dequeCarryRightActionRun ws spare j
      · rw [hw]
        exact hn
      · rw [hw]
        exact hi j hj)
    (by
      intro ws hw j _
      simp only [dequeCarryRightStep, List.length_set, hw]) words rfl
  rw [List.forIn_map]
  simpa only [dequeCarryRightAction, bind_assoc] using hf

/-- The common growth phase of both pushes. -/
def dequeGrowthFor (B : BitVector) : BitMutationM Unit := do
  if mod64 B.len == int 0 then
    growChunkVector B.chunks (int 1)
    mutableSet B.chunks (u64 0) (← mutableLength B.chunks)

/-- Front-push after the shared growth phase. -/
def dequeFrontTail (B : BitVector) (value : Bool) : BitMutationM BitVector := do
  let B := { B with len := B.len + int 1 }
  if B.len == int 1 then
    mutableSet B.chunks (u64 (if value then 1 else 0)) (int 1)
    return B
  for i in (intRange (int 2) (← mutableLength B.chunks)).reverse do
    let current ← mutableGet B.chunks i
    let previous ← mutableGet B.chunks (i - int 1)
    mutableSet B.chunks (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) i
  let first ← mutableGet B.chunks (int 1)
  mutableSet B.chunks (or_int (u64 (if value then 1 else 0)) (shl_int first (int 1))) (int 1)
  return B

/-- End-push after its growth phase. -/
def dequeEndTail (check : BitVector → I64 → BitMutationM Unit)
    (B : BitVector) (value : Bool) : BitMutationM BitVector := do
  let B := { B with len := B.len + int 1 }
  if value then
    let _ ← bitArraySetIndex check (fun b => pure b) B value B.len
    pure ()
  return B

/-- The frozen front-push model is exactly conversion, growth, then its tail. -/
theorem dequeFrontFactor {X : Type} (convert : X → BitMutationM Bool)
    (B : BitVector) (x : X) :
    bitVectorPushfirst convert B x = (do
      let value ← convert x
      dequeGrowthFor B
      dequeFrontTail B value) := by
  by_cases h : (mod64 B.len == int 0) = true <;>
    simp only [bitVectorPushfirst, dequeGrowthFor, dequeFrontTail, h, ite_true,
      Bool.false_eq_true, ite_false, bind_assoc, pure_bind]

/-- The frozen end-push model has the same three-phase structure. -/
theorem dequeEndFactor {X : Type} (convert : X → BitMutationM Bool)
    (check : BitVector → I64 → BitMutationM Unit) (B : BitVector) (x : X) :
    bitVectorPush convert check B x = (do
      let value ← convert x
      dequeGrowthFor B
      dequeEndTail check B value) := by
  by_cases h : (mod64 B.len == int 0) = true <;>
    simp only [bitVectorPush, dequeGrowthFor, dequeEndTail, h, ite_true,
      Bool.false_eq_true, ite_false, bind_assoc, pure_bind]

/-- Abstract composition of the three checked front-push phases. -/
theorem dequeFrontFrom {X : Type} (convert : X → BitMutationM Bool)
    (B outB : BitVector) (x : X) (value : Bool) (s mid out : State)
    (hc : (convert x).run s = (.ok value, s))
    (hg : (dequeGrowthFor B).run s = (.ok (), mid))
    (ht : (dequeFrontTail B value).run mid = (.ok outB, out)) :
    (bitVectorPushfirst convert B x).run s = (.ok outB, out) := by
  rw [dequeFrontFactor]
  simp only [shape_run_bind, hc, hg, ht]

/-- Abstract composition of the three checked end-push phases. -/
theorem dequeEndFrom {X : Type} (convert : X → BitMutationM Bool)
    (check : BitVector → I64 → BitMutationM Unit)
    (B outB : BitVector) (x : X) (value : Bool) (s mid out : State)
    (hc : (convert x).run s = (.ok value, s))
    (hg : (dequeGrowthFor B).run s = (.ok (), mid))
    (ht : (dequeEndTail check B value).run mid = (.ok outB, out)) :
    (bitVectorPush convert check B x).run s = (.ok outB, out) := by
  rw [dequeEndFactor]
  simp only [shape_run_bind, hc, hg, ht]

/-- False end-push leaves the grown chunk store unchanged. -/
theorem dequeEndTailFalse (check : BitVector → I64 → BitMutationM Unit)
    (B : BitVector) (s : State) :
    (dequeEndTail check B false).run s =
      (.ok { B with len := B.len + int 1 }, s) := rfl

/-- A successful final scalar write supplies the true end-push branch. -/
theorem dequeEndTailTrueFrom (check : BitVector → I64 → BitMutationM Unit)
    (B : BitVector) (s out : State)
    (hs : (bitArraySetIndex check (fun b => pure b)
      { B with len := B.len + int 1 } true (B.len + int 1)).run s =
        (.ok { B with len := B.len + int 1 }, out)) :
    (dequeEndTail check B true).run s =
      (.ok { B with len := B.len + int 1 }, out) := by
  change ((bitArraySetIndex check (fun b => pure b)
    { B with len := B.len + int 1 } true (B.len + int 1)) >>=
      (fun _ => pure { B with len := B.len + int 1 })).run s = _
  rw [shape_run_bind, hs]
  rfl

/-- A one-bit front-push needs only the first chunk write. -/
theorem dequeFrontTailOneFrom (B : BitVector) (value : Bool) (s out : State)
    (hlen : (B.len + int 1 == int 1) = true)
    (hs : (mutableSet B.chunks (u64 (if value then 1 else 0)) (int 1)).run s = (.ok (), out)) :
    (dequeFrontTail B value).run s = (.ok { B with len := B.len + int 1 }, out) := by
  simp only [dequeFrontTail, hlen, ite_true, shape_run_bind, hs, shape_run_pure]
  rfl

/-- The longer front-push branch follows from its loop and final word write. -/
theorem dequeFrontTailLongFrom (B : BitVector) (value : Bool)
    (s shifted out : State) (nc : I64) (first : U64)
    (hlen : (B.len + int 1 == int 1) = false)
    (hl : (mutableLength B.chunks).run s = (.ok nc, s))
    (hloop : (forIn (intRange (int 2) nc).reverse PUnit.unit (fun i _ => do
      let current ← mutableGet B.chunks i
      let previous ← mutableGet B.chunks (i - int 1)
      mutableSet B.chunks (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) i
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, shifted))
    (hf : (mutableGet B.chunks (int 1)).run shifted = (.ok first, shifted))
    (hs : (mutableSet B.chunks
      (or_int (u64 (if value then 1 else 0)) (shl_int first (int 1))) (int 1)).run shifted =
        (.ok (), out)) :
    (dequeFrontTail B value).run s = (.ok { B with len := B.len + int 1 }, out) := by
  simp only [dequeFrontTail, hlen, Bool.false_eq_true, ite_false,
    shape_run_bind, hl, hloop, hf, hs, shape_run_pure]
  rfl
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- The descending Julia chunk range has exactly the pure carry indices. -/
theorem dequeIntRangeTwo (n : Nat) (hn : n ≤ 9223372036854775807) :
    (intRange (int 2) (int n)).reverse =
      (dequeLeftIndices n).map (fun j => int ((j + 1 : Nat) : Int)) := by
  unfold intRange
  rw [packedInt_val n hn]
  have hlen : (((n : Int) - (int 2).val + 1).toNat) = n - 1 := by
    change (((n : Int) - 2 + 1).toNat) = n - 1
    omega
  rw [hlen]
  simp only [dequeLeftIndices, List.map_map, List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro j _
  apply Subtype.ext
  change wrapInt .i64 (2 + (j : Int)) = wrapInt .i64 (((j + 1 + 1 : Nat) : Int))
  apply congrArg (wrapInt .i64)
  omega

/-- A singleton bit sequence occupies its single low bit. -/
theorem dequeEncodeSingleton (value : Bool) :
    encodeBits [value] = [u64 (if value then 1 else 0)] := by
  have hw : packedPrefix [value] 0 64 = u64 (if value then 1 else 0) := by
    apply packedBit_ext
    intro k hk
    rw [packedWord_bit _ _ _ hk, dequePackedBool]
    simp only [Nat.zero_mul, Nat.zero_add]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.getD_cons_succ, List.getD_nil, Nat.add_one_ne_zero, ite_false]
  rw [packedPrefix_eq_encode]
  have hc : wordCount ([value].length) = 1 := by
    change wordCount 1 = 1
    decide
  rw [hc]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, hw]

/-- The final bit write changes the appended default bit to its converted value. -/
theorem dequeAppendSet (xs : List Bool) (value : Bool) :
    (xs ++ [false]).set xs.length value = xs ++ [value] := by
  rw [List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self, List.set_cons_zero]

/-- The first-word equality test distinguishes the empty input. -/
theorem dequeNewLengthOne (xs : List Bool)
    (hn : xs.length + 1 ≤ 9223372036854775807) :
    (int xs.length + int 1 == int 1) = xs.isEmpty := by
  have hs : int xs.length + int 1 = int ((xs.length + 1 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  rw [hs]
  by_cases he : xs = []
  · subst xs
    rfl
  · have hlen : 0 < xs.length := List.length_pos_iff.mpr he
    have hv : int ((xs.length + 1 : Nat) : Int) ≠ int 1 := by
      intro h
      have h' := congrArg Subtype.val h
      rw [packedInt_val (xs.length + 1) hn] at h'
      change ((xs.length + 1 : Nat) : Int) = 1 at h'
      omega
    rw [beq_eq_false_iff_ne.mpr hv]
    exact (List.isEmpty_eq_false_iff.mpr he).symm

/-- Natural logical lengths have the expected machine remainder. -/
theorem dequeMod64Nat (n : Nat) (hn : n ≤ 9223372036854775807) :
    mod64 (int n) = int ((n % 64 : Nat) : Int) := by
  apply Subtype.ext
  rw [scalar_mod64_val, packedInt_val n hn,
    packedInt_val (n % 64) (by omega)]
  omega

/-- The one-step push leaves either thirty-one or thirty-two reserve slots. -/
def dequePushSpare (xs : List Bool) : Nat :=
  if xs.length % 64 = 0 then 31 else 32

/-- Canonical store immediately after the common push growth phase. -/
def dequeGrowthState (xs : List Bool) : State :=
  dequeWordStore (dequeGrownWords xs) (dequePushSpare xs)

/-- Testing the source length selects the natural chunk-growth boundary. -/
theorem dequeGrowthForVector (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    dequeGrowthFor (vectorBits xs) =
      if xs.length % 64 = 0 then dequeGrowZero else pure () := by
  have hm := dequeMod64Nat xs.length hn
  by_cases hz : xs.length % 64 = 0
  · have he : (mod64 (int xs.length) == int 0) = true := by rw [hm, hz]; rfl
    simp only [dequeGrowthFor, vectorBits, he, hz, ite_true]
    rfl
  · have hne : int ((xs.length % 64 : Nat) : Int) ≠ int 0 := by
      intro he
      have hv := congrArg Subtype.val he
      rw [packedInt_val (xs.length % 64) (by omega)] at hv
      change ((xs.length % 64 : Nat) : Int) = 0 at hv
      omega
    have he : (mod64 (int xs.length) == int 0) = false := by
      rw [hm]
      exact beq_eq_false_iff_ne.mpr hne
    simp only [dequeGrowthFor, vectorBits, he, hz, Bool.false_eq_true, ite_false]

/-- The growth phase initializes precisely the newly exposed packed chunk. -/
theorem dequeGrowthPhaseRun (xs : List Bool)
    (hn : xs.length < Round5.maxVectorLength) :
    (dequeGrowthFor (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok (), dequeGrowthState xs) := by
  have hbits : xs.length ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hn
    omega
  rw [dequeGrowthForVector xs hbits]
  by_cases hz : xs.length % 64 = 0
  · rw [if_pos hz]
    have hwords : (encodeBits xs).length + 31 + 1 ≤ 9223372036854775807 := by
      rw [packedEncoded_length]
      unfold wordCount
      change xs.length < 4611686018427387903 at hn
      omega
    have hg := dequeGrowZeroRun (encodeBits xs) 31 hwords
    rw [dequeWordStoreInitial] at hg
    simpa only [dequeGrowthState, dequePushSpare, dequeGrownWords, hz, ite_true] using hg
  · rw [if_neg hz]
    simp only [shape_run_pure, dequeGrowthState, dequePushSpare, dequeGrownWords, hz, ite_false,
      dequeWordStoreInitial]

/-- The generic bit setter preserves spare capacity and updates the packed encoding. -/
theorem dequeBitSetRun (xs : List Bool) (spare i : Nat) (value : Bool)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (unsafeBitSetIndex 0 value (int ((i + 1 : Nat) : Int))).run
      (dequeWordStore (encodeBits xs) spare) =
        (.ok (), dequeWordStore (encodeBits (xs.set i value)) spare) := by
  have hw : (encodeBits xs).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound xs hn
  have hc : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hget := dequeWordRead (encodeBits xs) spare (i / 64) hw hc
  have hword : (encodeBits xs).getD (i / 64) (u64 0) = packedPrefix xs (i / 64) 64 := by
    rw [← List.getElem_eq_getD (h := hc)]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [hword] at hget
  apply scalar_internal_write_run (dequeWordStore (encodeBits xs) spare)
    (dequeWordStore (encodeBits (xs.set i value)) spare) 0
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int)) (int ((i % 64 : Nat) : Int))
    (packedPrefix xs (i / 64) 64) value (scalar_chunks_nat i (by omega)) hget
  rw [dequeWordSet (encodeBits xs) spare (i / 64) _ hw hc]
  rw [scalar_encode_set xs i value hi]
  rfl

/-- A public Boolean write with the identity conversion returns the updated header. -/
theorem dequePublicBoolWrite (B : BitVector) (i : I64) (value : Bool) (s out : State)
    (hn : 0 ≤ B.len.val) (hi : int 1 ≤ i ∧ i ≤ B.len)
    (hs : (unsafeBitSetIndex B.chunks value i).run s = (.ok (), out)) :
    (bitArraySetIndex Round5.Round2.checkBitVectorBounds (fun b => pure b) B value i).run s =
      (.ok B, out) := by
  simp only [bitArraySetIndex, Round5.Round2.checkBitVectorBounds, shape_run_bind,
    scalar_bounds_run B i s hn, hi, and_self, ite_true, shape_run_pure, hs]
  rfl

/-- The front-push carry tail installs the encoding of a Boolean cons. -/
theorem dequeFrontTailRun (xs : List Bool) (value : Bool)
    (hn : xs.length < Round5.maxVectorLength) :
    (dequeFrontTail (vectorBits xs) value).run (dequeGrowthState xs) =
      (.ok { vectorBits xs with len := (vectorBits xs).len + int 1 },
        dequeWordStore (encodeBits (value :: xs)) (dequePushSpare xs)) := by
  have hbits : xs.length + 1 ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hn
    omega
  by_cases he : xs = []
  · subst xs
    have hs := dequeWordSet [u64 0] 31 0 (u64 (if value then 1 else 0))
      (by decide) (by decide)
    have hstate : dequeGrowthState [] = dequeWordStore [u64 0] 31 := rfl
    rw [hstate, dequeEncodeSingleton]
    apply dequeFrontTailOneFrom
    · rfl
    · simpa only [List.set_cons_zero, dequePushSpare, List.length_nil,
        Nat.zero_mod, Nat.zero_add, Int.ofNat_one, ite_true, vectorBits] using hs
  · let words := dequeGrownWords xs
    let spare := dequePushSpare xs
    let indices := dequeLeftIndices words.length
    let shifted := indices.foldl dequeCarryLeftStep words
    have hw : words.length ≤ 9223372036854775807 := by
      rw [dequeGrownWordsLength]
      unfold wordCount
      omega
    have hp : 0 < words.length := by
      rw [dequeGrownWordsLength]
      unfold wordCount
      omega
    have hslen : shifted.length = words.length := dequeCarryLeftFoldLength indices words
    have hib : ∀ j ∈ indices, 0 < j ∧ j < words.length := by
      intro j hj
      exact (dequeLeftIndicesMem words.length j).mp hj
    have hlo := dequeCarryLeftLoop indices words spare hw hib
    have hloop : (forIn (intRange (int 2) (int words.length)).reverse PUnit.unit
        (fun i _ => do
          let current ← mutableGet 0 i
          let previous ← mutableGet 0 (i - int 1)
          mutableSet 0 (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) i
          pure (ForInStep.yield PUnit.unit))).run (dequeWordStore words spare) =
            (.ok PUnit.unit, dequeWordStore shifted spare) := by
      rw [dequeIntRangeTwo words.length hw]
      exact hlo
    have hf := dequeWordRead shifted spare 0 (by rw [hslen]; exact hw)
      (by rw [hslen]; exact hp)
    have hs := dequeWordSet shifted spare 0
      (or_int (u64 (if value then 1 else 0)) (shl_int (shifted.getD 0 (u64 0)) (int 1)))
      (by rw [hslen]; exact hw) (by rw [hslen]; exact hp)
    have henc : shifted.set 0
        (or_int (u64 (if value then 1 else 0)) (shl_int (shifted.getD 0 (u64 0)) (int 1))) =
          encodeBits (value :: xs) := dequeFrontWordsEncode xs value
    rw [henc] at hs
    have hlong : ((vectorBits xs).len + int 1 == int 1) = false := by
      change (int xs.length + int 1 == int 1) = false
      rw [dequeNewLengthOne xs hbits]
      exact List.isEmpty_eq_false_iff.mpr he
    exact dequeFrontTailLongFrom (vectorBits xs) value _ _ _ (int words.length)
      (shifted.getD 0 (u64 0)) hlong (dequeWordLength words spare) hloop hf hs

/-- The end-push tail changes only the newly appended Boolean. -/
theorem dequeEndTailRun (xs : List Bool) (value : Bool)
    (hn : xs.length < Round5.maxVectorLength) :
    (dequeEndTail Round5.Round2.checkBitVectorBounds (vectorBits xs) value).run
      (dequeGrowthState xs) =
      (.ok { vectorBits xs with len := (vectorBits xs).len + int 1 },
        dequeWordStore (encodeBits (xs ++ [value])) (dequePushSpare xs)) := by
  have hbits : xs.length + 1 ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hn
    omega
  have hnew : (vectorBits xs).len + int 1 = int ((xs.length + 1 : Nat) : Int) := by
    exact dequeLengthSucc xs.length hn
  cases value with
  | false =>
    rw [dequeEndTailFalse]
    change (_, dequeWordStore (dequeGrownWords xs) (dequePushSpare xs)) = _
    rw [dequeEncodeAppendFalse]
  | true =>
    apply dequeEndTailTrueFrom
    have hs := dequeBitSetRun (xs ++ [false]) (dequePushSpare xs) xs.length true
      (by simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using hbits)
      (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]; omega)
    rw [dequeAppendSet, dequeEncodeAppendFalse] at hs
    apply dequePublicBoolWrite
    · change 0 ≤ ((vectorBits xs).len + int 1).val
      rw [hnew, packedInt_val (xs.length + 1) hbits]
      omega
    · change int 1 ≤ (vectorBits xs).len + int 1 ∧
        (vectorBits xs).len + int 1 ≤ (vectorBits xs).len + int 1
      rw [hnew]
      constructor
      · change 1 ≤ (int ((xs.length + 1 : Nat) : Int)).val
        rw [packedInt_val (xs.length + 1) hbits]
        omega
      · exact Int.le_refl _
    · change (unsafeBitSetIndex 0 true ((vectorBits xs).len + int 1)).run
        (dequeGrowthState xs) = _
      rw [hnew]
      exact hs

/-- Complete successful end-push execution on the frozen initial store. -/
theorem dequePushRun (xs : List Bool) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hn : xs.length < Round5.maxVectorLength)
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    (bitVectorPush Round5.Round2.convertBoolMutation Round5.Round2.checkBitVectorBounds
      (vectorBits xs) x).run (initWords (encodeBits xs)) =
      (.ok { vectorBits xs with len := (vectorBits xs).len + int 1 },
        dequeWordStore (encodeBits (xs ++ [value])) (dequePushSpare xs)) := by
  exact dequeEndFrom Round5.Round2.convertBoolMutation Round5.Round2.checkBitVectorBounds
    (vectorBits xs) _ x value _ _ _ (dequeConvertOk x value _ hc)
    (dequeGrowthPhaseRun xs hn) (dequeEndTailRun xs value hn)

/-- Complete successful front-push execution on the frozen initial store. -/
theorem dequePushfirstRun (xs : List Bool) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hn : xs.length < Round5.maxVectorLength)
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    (bitVectorPushfirst Round5.Round2.convertBoolMutation (vectorBits xs) x).run
      (initWords (encodeBits xs)) =
      (.ok { vectorBits xs with len := (vectorBits xs).len + int 1 },
        dequeWordStore (encodeBits (value :: xs)) (dequePushSpare xs)) := by
  exact dequeFrontFrom Round5.Round2.convertBoolMutation (vectorBits xs) _ x value _ _ _
    (dequeConvertOk x value _ hc) (dequeGrowthPhaseRun xs hn) (dequeFrontTailRun xs value hn)

/-- A canonical encoded store supplies logical equality and packed padding together. -/
theorem dequeEncodedObservations {N : Nat} (xs : List Bool) (B : BitArray N) (spare : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hl : B.len = int xs.length) (hc : B.chunks = 0) :
    bitValues (dequeWordStore (encodeBits xs) spare) B = xs ∧
      Round5.Round2.PackedInvariant (dequeWordStore (encodeBits xs) spare) B := by
  have hcontents : (dequeWordStore (encodeBits xs) spare).contents B.chunks =
      (encodeBits xs).map some := by
    rw [hc]
    exact dequeWordContents (encodeBits xs) spare (packedEncoded_lengthBound xs hn)
  exact ⟨scalar_bitValues_contents _ B xs hn hl hcontents,
    scalar_invariant_of_contents _ B xs hn hl hcontents⟩

/-- End-push meets the complete successful observation contract. -/
theorem dequePushCorrect (xs : List Bool) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hn : xs.length < Round5.maxVectorLength)
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    ∃ B' s',
      (bitVectorPush Round5.Round2.convertBoolMutation Round5.Round2.checkBitVectorBounds
        (vectorBits xs) x).run (initWords (encodeBits xs)) = (.ok B', s') ∧
      bitValues s' B' = xs ++ [value] ∧ Round5.Round2.PackedInvariant s' B' := by
  refine ⟨_, _, dequePushRun xs x value hn hc, ?_⟩
  apply dequeEncodedObservations
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
    change xs.length < 4611686018427387903 at hn
    omega
  · change int xs.length + int 1 = int (xs ++ [value]).length
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
    exact dequeLengthSucc xs.length hn
  · rfl

/-- Front-push meets the complete successful observation contract. -/
theorem dequePushfirstCorrect (xs : List Bool) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hn : xs.length < Round5.maxVectorLength)
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    ∃ B' s',
      (bitVectorPushfirst Round5.Round2.convertBoolMutation (vectorBits xs) x).run
        (initWords (encodeBits xs)) = (.ok B', s') ∧
      bitValues s' B' = value :: xs ∧ Round5.Round2.PackedInvariant s' B' := by
  refine ⟨_, _, dequePushfirstRun xs x value hn hc, ?_⟩
  apply dequeEncodedObservations
  · simp only [List.length_cons]
    change xs.length < 4611686018427387903 at hn
    omega
  · change int xs.length + int 1 = int (value :: xs).length
    simp only [List.length_cons]
    exact dequeLengthSucc xs.length hn
  · rfl
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Lower-bound errors precede all packed-memory accesses. -/
theorem rangeDelete_bad_first (B : BitVector) (r : BitRange) (s : State)
    (h : r.first < int 1) :
    (Round5.Round2.deleteBitRangePublic B r).run s = (.error .bounds, s) := by
  rw [rangeDelete_public_eq]
  simp only [bitVectorDeleteRange, h, ite_true, shape_run_bind]
  rfl

/-- Upper-bound errors precede all packed-memory accesses. -/
theorem rangeDelete_bad_last (B : BitVector) (r : BitRange) (s : State)
    (hfirst : ¬ r.first < int 1) (hlast : r.last > B.len) :
    (Round5.Round2.deleteBitRangePublic B r).run s = (.error .bounds, s) := by
  rw [rangeDelete_public_eq]
  simp only [bitVectorDeleteRange, hfirst, hlast, ite_false, ite_true,
    shape_run_bind, shape_run_pure]
  rfl

/-- The public range deletion method rejects a small empty range before mutation. -/
theorem rangeDelete_empty_zero_rejected :
    (JuliaLean.Proofs.base.bitarray.Round5.Round2.deleteBitRangePublic
      (vectorBits []) ⟨int 0, int (-1)⟩).run (initWords (encodeBits [])) =
      (.error .bounds, initWords (encodeBits [])) := by
  rfl

/-- The counterexample uses an empty BitVector and the public range `0:-1`. -/
theorem BitarraysDeleteatEmptyRange_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Round5.DeleteatRangeAgrees := by
  intro h
  have hx := h [] (int 0) (int (-1)) (by decide)
  change
    ((JuliaLean.Proofs.base.bitarray.Round5.Round2.deleteBitRangePublic
      (vectorBits []) ⟨int 0, int (-1)⟩).run (initWords (encodeBits []))).1 =
      .ok (vectorBits []) ∧
    ((JuliaLean.Proofs.base.bitarray.Round5.Round2.deleteBitRangePublic
      (vectorBits []) ⟨int 0, int (-1)⟩).run (initWords (encodeBits []))).2 =
      initWords (encodeBits []) at hx
  rw [rangeDelete_empty_zero_rejected] at hx
  cases hx.1
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

/-- The ascending packed loop used by the public front-pop. -/
def frontPopLoop (chunks : Nat) (nc : I64) : BitMutationM PUnit :=
  forIn (intRange (int 1) (nc - int 1)) PUnit.unit (fun i _ => do
    let current ← mutableGet chunks i
    let next ← mutableGet chunks (i + int 1)
    mutableSet chunks (or_int (lshr_int current (int 1))
      (shl_int next (int 63))) i
    pure (ForInStep.yield PUnit.unit))

/-- The final-word action of front-pop is separate from its carry loop. -/
def frontPopTail (B : BitVector) (nc : I64) (item : Bool) :
    BitMutationM (BitVector × Bool) := do
  if mod64 B.len == int 1 then
    deleteChunkEnd B.chunks (int 1)
  else
    let last ← mutableGet B.chunks nc
    mutableSet B.chunks (lshr_int last (int 1)) nc
  pure ({B with len := B.len - int 1}, item)

/-- Primitive read and mutation results compose to the public front-pop result. -/
theorem frontPopRunFrom (B B' : BitVector) (s mid out : State)
    (nc : I64) (item : Bool)
    (hne : (B.len == int 0) = false)
    (hread : (unsafeBitGetIndex B.chunks (int 1)).run s = (.ok item, s))
    (hlen : (mutableLength B.chunks).run s = (.ok nc, s))
    (hloop : (frontPopLoop B.chunks nc).run s = (.ok PUnit.unit, mid))
    (htail : (frontPopTail B nc item).run mid = (.ok (B', item), out)) :
    (bitVectorPopfirst B).run s = (.ok (B', item), out) := by
  unfold frontPopLoop at hloop
  unfold frontPopTail at htail
  simp only [bitVectorPopfirst, hne, Bool.false_eq_true, ite_false,
    shape_run_bind, hread, hlen]
  rw [hloop]
  exact htail

/-- The machine carry interval visits every word except the final one. -/
theorem frontPopRange (n : Nat) (hp : 0 < n)
    (hn : n ≤ 9223372036854775807) :
    intRange (int 1) (int (n : Int) - int 1) =
      (List.range (n - 1)).map (fun j => int ((j + 1 : Nat) : Int)) := by
  rw [frontPopLengthPred n hp]
  exact packedObserve_intRange (n - 1) (by omega)

/-- The public carry loop preserves the word count and computes the pure ascending fold. -/
theorem frontPopLoopRun (words : List U64) (spare : Nat)
    (hp : 0 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (frontPopLoop 0 (int (words.length : Int))).run (dequeWordStore words spare) =
      (.ok PUnit.unit, dequeWordStore
        ((List.range (words.length - 1)).foldl dequeCarryRightStep words) spare) := by
  unfold frontPopLoop
  rw [frontPopRange words.length hp hn]
  exact dequeCarryRightLoop _ words spare hn (by
    intro j hj
    have h := List.mem_range.mp hj
    omega)

/-- A nonempty word list splits into its visible prefix and its last word. -/
theorem frontPopLastSplit (words : List U64) (hp : 0 < words.length) :
    words.take (words.length - 1) ++ [words.getD (words.length - 1) (u64 0)] = words := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_cons,
      List.length_nil, Nat.min_eq_left (by omega : words.length - 1 ≤ words.length)]
    omega
  · intro i hi hi'
    by_cases hip : i < words.length - 1
    · rw [List.getElem_append_left (by
        simp only [List.length_take, Nat.min_eq_left (by omega : words.length - 1 ≤ words.length)]
        exact hip), List.getElem_take]
    · have he : i = words.length - 1 := by omega
      subst i
      rw [List.getElem_append_right (by
        simp only [List.length_take, Nat.min_eq_left (by omega : words.length - 1 ≤ words.length)]
        exact Nat.le_refl _)]
      simp only [List.length_take, Nat.min_eq_left (by omega : words.length - 1 ≤ words.length),
        Nat.sub_self, List.getElem_cons_zero]
      exact (List.getElem_eq_getD (u64 0)).symm

/-- Front-pop deletion on any nonempty canonical word store. -/
theorem frontPopDeleteLastRun (words : List U64) (spare : Nat)
    (hp : 0 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (deleteChunkEnd 0 (int 1)).run (dequeWordStore words spare) =
      (.ok (), dequeTailStore (words.take (words.length - 1))
        (some (words.getD (words.length - 1) (u64 0)) :: List.replicate spare none)) := by
  have h := dequeWordDeleteLast (words.take (words.length - 1))
    (words.getD (words.length - 1) (u64 0)) spare (by
      simp only [List.length_take, Nat.min_eq_left (by omega : words.length - 1 ≤ words.length)]
      omega)
  rw [frontPopLastSplit words hp] at h
  exact h

/-- Logical observations depend on the visible contents and native logical length. -/
theorem frontPopBitsOfContents {N : Nat} (s : State) (B : BitArray N)
    (xs : List Bool) (hn : xs.length ≤ 9223372036854775807)
    (hl : B.len = int xs.length)
    (hc : s.contents B.chunks = (encodeBits xs).map some) :
    bitValues s B = xs := by
  exact scalar_bitValues_contents s B xs hn hl hc

/-- The final-word branch tests the natural remainder of the logical length. -/
theorem frontPopModOne (n : Nat) (hn : n ≤ 9223372036854775807) :
    (mod64 (int (n : Int)) == int 1) = decide (n % 64 = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [scalar_mod64_val, packedInt_val n hn] at hv
    change (n : Int) % 64 = 1 at hv
    omega
  · intro h
    apply Subtype.ext
    rw [scalar_mod64_val, packedInt_val n hn]
    change (n : Int) % 64 = 1
    omega

/-- A tail deletion composes with the returned header without opening a concrete store. -/
theorem frontPopTailDeleteFrom (B : BitVector) (nc : I64) (item : Bool)
    (s out : State) (hb : (mod64 B.len == int 1) = true)
    (hd : (deleteChunkEnd B.chunks (int 1)).run s = (.ok (), out)) :
    (frontPopTail B nc item).run s =
      (.ok ({B with len := B.len - int 1}, item), out) := by
  simp only [frontPopTail, hb, ite_true, shape_run_bind, hd, shape_run_pure]

/-- A tail shift composes one read and one write before returning the shortened header. -/
theorem frontPopTailShiftFrom (B : BitVector) (nc : I64) (item : Bool)
    (s out : State) (word : U64) (hb : (mod64 B.len == int 1) = false)
    (hr : (mutableGet B.chunks nc).run s = (.ok word, s))
    (hw : (mutableSet B.chunks (lshr_int word (int 1)) nc).run s = (.ok (), out)) :
    (frontPopTail B nc item).run s =
      (.ok ({B with len := B.len - int 1}, item), out) := by
  simp only [frontPopTail, hb, Bool.false_eq_true, ite_false, shape_run_bind,
    hr, hw, shape_run_pure]

/-- Spare slots after front-pop; a removed final word stays assigned in backing memory. -/
def frontPopStaleTail (xs : List Bool) (spare : Nat) : List (Option U64) :=
  let words := encodeBits xs
  let shifted := (List.range (words.length - 1)).foldl dequeCarryRightStep words
  if xs.length % 64 = 1 then
    some (shifted.getD (words.length - 1) (u64 0)) :: List.replicate spare none
  else List.replicate spare none

/-- After the carry loop, the tail either clears an exhausted word or shifts the last word. -/
theorem frontPopTailRun (xs : List Bool) (spare : Nat) (item : Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    let words := encodeBits xs
    let shifted := (List.range (words.length - 1)).foldl dequeCarryRightStep words
    (frontPopTail (vectorBits xs) (int (words.length : Int)) item).run
      (dequeWordStore shifted spare) =
        (.ok ({vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)}, item),
          dequeTailStore (dequeDropWords xs) (frontPopStaleTail xs spare)) := by
  let words := encodeBits xs
  let shifted := (List.range (words.length - 1)).foldl dequeCarryRightStep words
  have hcount : words.length = wordCount xs.length := packedEncoded_length xs
  have hpos : 0 < words.length := by rw [hcount]; unfold wordCount; omega
  have hbound : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hslen : shifted.length = words.length := dequeCarryRightFoldLength _ words
  have hspos : 0 < shifted.length := by rw [hslen]; exact hpos
  have hsbound : shifted.length ≤ 9223372036854775807 := by rw [hslen]; exact hbound
  have hpred := frontPopLengthPred xs.length hp
  have hheader : ({vectorBits xs with len := (vectorBits xs).len - int 1} : BitVector) =
      {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)} :=
    congrArg (fun len => ({vectorBits xs with len := len} : BitVector)) hpred
  by_cases hm : xs.length % 64 = 1
  · have hbranch : (mod64 (int (xs.length : Int)) == int 1) = true := by
      simp only [frontPopModOne xs.length hn, hm, decide_true]
    have hd := frontPopDeleteLastRun shifted spare hspos hsbound
    rw [hslen] at hd
    change (frontPopTail (vectorBits xs) (int (words.length : Int)) item).run
      (dequeWordStore shifted spare) = _
    have ht := frontPopTailDeleteFrom (vectorBits xs) (int (words.length : Int)) item
      (dequeWordStore shifted spare) _ hbranch hd
    exact ht.trans (by
      rw [hheader]
      simp only [dequeDropWords, frontPopStaleTail, hm, ite_true]
      rfl)
  · have hbranch : (mod64 (int (xs.length : Int)) == int 1) = false := by
      simp only [frontPopModOne xs.length hn, hm, decide_false]
    have hr := dequeWordRead shifted spare (words.length - 1) hsbound (by rw [hslen]; omega)
    have hw := dequeWordSet shifted spare (words.length - 1)
      (lshr_int (shifted.getD (words.length - 1) (u64 0)) (int 1))
      hsbound (by rw [hslen]; omega)
    have hi : words.length - 1 + 1 = words.length := by omega
    rw [hi] at hr hw
    change (frontPopTail (vectorBits xs) (int (words.length : Int)) item).run
      (dequeWordStore shifted spare) = _
    have ht := frontPopTailShiftFrom (vectorBits xs) (int (words.length : Int)) item
      (dequeWordStore shifted spare) _ _ hbranch hr hw
    exact ht.trans (by
      rw [hheader]
      simp only [dequeDropWords, frontPopStaleTail, hm, ite_false]
      rfl)

/-- Successful front-pop returns the first bit and the exact packed encoding of the tail. -/
theorem frontPopPackedRun (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (bitVectorPopfirst (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok ({vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)}, xs.headD false),
        dequeTailStore (encodeBits (xs.drop 1)) (frontPopStaleTail xs 32)) := by
  let words := encodeBits xs
  let shifted := (List.range (words.length - 1)).foldl dequeCarryRightStep words
  have hpos : 0 < words.length := by
    change 0 < (encodeBits xs).length
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hbound : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hne : ((vectorBits xs).len == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    have hv := congrArg Subtype.val h
    change (int (xs.length : Int)).val = (int 0).val at hv
    rw [packedInt_val xs.length hn] at hv
    change (xs.length : Int) = 0 at hv
    omega
  have hread := scalar_read_initial xs 0 hn hp
  have hhead : xs.getD 0 false = xs.headD false := by cases xs <;> rfl
  rw [hhead] at hread
  rw [← dequeWordStoreInitial words] at hread ⊢
  have hlen := dequeWordLength words 32
  have hloop := frontPopLoopRun words 32 hpos hbound
  have htail := frontPopTailRun xs 32 (xs.headD false) hp hn
  dsimp only at htail
  rw [dequeDropWordsEncode xs hp] at htail
  exact frontPopRunFrom (vectorBits xs) _ _ _ _ (int (words.length : Int))
    (xs.headD false) hne hread hlen hloop htail

/-- The front-pop branch satisfies the logical result and packed-storage invariant. -/
theorem frontPopSuccess (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    ∃ (B' : BitVector) (s' : State),
      (bitVectorPopfirst (vectorBits xs)).run (initWords (encodeBits xs)) =
        (.ok (B', xs.headD false), s') ∧
      bitValues s' B' = xs.drop 1 ∧ Round5.Round2.PackedInvariant s' B' := by
  let B' : BitVector := {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)}
  let s' := dequeTailStore (encodeBits (xs.drop 1)) (frontPopStaleTail xs 32)
  have hlen : B'.len = int (xs.drop 1).length := by
    simp only [B', List.length_drop]
  have hn' : (xs.drop 1).length ≤ 9223372036854775807 := by
    rw [List.length_drop]
    omega
  have hcontents : s'.contents B'.chunks = (encodeBits (xs.drop 1)).map some :=
    dequeTailContents _ _ (packedEncoded_lengthBound _ hn')
  exact ⟨B', s', frontPopPackedRun xs hp hn,
    frontPopBitsOfContents s' B' (xs.drop 1) hn' hlen hcontents,
    scalar_invariant_of_contents s' B' (xs.drop 1) hn' hlen hcontents⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem endPop_getD_last (xs : List Bool) (value : Bool) :
    (xs ++ [value]).getD xs.length false = value := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem endPop_set_last (xs : List Bool) (old value : Bool) :
    (xs ++ [old]).set xs.length value = xs ++ [value] := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

/-- End-pop execution is determined by the read, clearing write, and optional chunk removal. -/
theorem endPop_run
    (getindex : BitVector → I64 → BitMutationM Bool)
    (setindex : BitVector → Bool → I64 → BitMutationM BitVector)
    (B : BitVector) (s s1 s2 s3 : State) (item : Bool)
    (hz : (B.len == int 0) = false)
    (hg : (getindex B B.len).run s = (.ok item, s1))
    (hs : (setindex B false B.len).run s1 = (.ok B, s2))
    (hd : ((if mod64 B.len == int 1 then deleteChunkEnd B.chunks (int 1)
      else pure ()) : BitMutationM Unit).run s2 = (.ok (), s3)) :
    (bitVectorPop getindex setindex B).run s =
      (.ok ({B with len := B.len - int 1}, item), s3) := by
  simp only [bitVectorPop, hz, Bool.false_eq_true, ite_false,
    shape_run_bind, hg, hs]
  by_cases hm : mod64 B.len == int 1
  · simp only [hm, ite_true] at hd ⊢
    simp only [shape_run_bind, hd, shape_run_pure]
  · simp only [hm, ite_false, shape_run_pure] at hd ⊢
    have hstate : s2 = s3 := congrArg Prod.snd hd
    exact congrArg (fun st => ((.ok ({B with len := B.len - int 1}, item) :
      Except Error (BitVector × Bool)), st)) hstate

/-- A successful end-pop removes the last logical bit and retains a canonical packed store. -/
theorem dequeEndPopAppend (xs : List Bool) (last : Bool)
    (hn : xs.length + 1 ≤ 9223372036854775807) :
    (bitVectorPop
      (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
      (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation)
      (vectorBits (xs ++ [last]))).run (initWords (encodeBits (xs ++ [last]))) =
      (.ok ({vectorBits (xs ++ [last]) with len := int xs.length}, last),
        dequeTailStore (encodeBits xs) (if xs.length % 64 = 0
          then some (u64 0) :: List.replicate 32 none else List.replicate 32 none)) := by
  let B := vectorBits (xs ++ [last])
  let s := initWords (encodeBits (xs ++ [last]))
  let cleared := initWords (encodeBits (xs ++ [false]))
  let out := dequeTailStore (encodeBits xs) (if xs.length % 64 = 0
    then some (u64 0) :: List.replicate 32 none else List.replicate 32 none)
  have hlen : (xs ++ [last]).length = xs.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hbound : (xs ++ [last]).length ≤ 9223372036854775807 := by rw [hlen]; exact hn
  have hi : xs.length < (xs ++ [last]).length := by rw [hlen]; omega
  have hBl : B.len = int ((xs.length + 1 : Nat) : Int) := by
    change int ((xs ++ [last]).length : Int) = _
    rw [hlen]
  have hv : B.len.val = (xs.length + 1 : Nat) := by
    rw [hBl, packedInt_val _ hn]
  have hnonnegative : 0 ≤ B.len.val := by rw [hv]; omega
  have hvalid : int 1 ≤ B.len ∧ B.len ≤ B.len := by
    change 1 ≤ B.len.val ∧ B.len.val ≤ B.len.val
    rw [hv]
    omega
  have hzero : (B.len == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have h := congrArg Subtype.val he
    rw [hv] at h
    change ((xs.length + 1 : Nat) : Int) = 0 at h
    omega
  have hpred : B.len - int 1 = int xs.length := by
    rw [hBl, dequeIntSub]
    exact congrArg int (by omega)
  have hread : (bitArrayGetIndex Round5.Round2.checkBitVectorBounds B B.len).run s =
      (.ok last, s) := by
    change (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B B.len).run s = _
    rw [scalar_public_read_valid B B.len s hnonnegative hvalid]
    change (unsafeBitGetIndex 0 B.len).run s = _
    rw [hBl]
    have h := scalar_read_initial (xs ++ [last]) xs.length hbound hi
    rw [endPop_getD_last] at h
    exact h
  have hwrite : (bitArraySetIndex Round5.Round2.checkBitVectorBounds
      Round5.Round2.convertBoolMutation B false B.len).run s = (.ok B, cleared) := by
    change (bitArraySetIndex Round5.Round2.checkBitArrayBounds
      Round5.Round2.convertBoolMutation B false B.len).run s = _
    apply scalar_public_write_valid B false B.len false s cleared hnonnegative hvalid (by rfl)
    change (unsafeBitSetIndex 0 false B.len).run s = _
    rw [hBl]
    have h := scalar_write_initial (xs ++ [last]) xs.length false hbound hi
    rw [endPop_set_last] at h
    exact h
  have hmod : (mod64 B.len == int 1) = decide (xs.length % 64 = 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro he
      have h := congrArg Subtype.val he
      rw [scalar_mod64_val, hv] at h
      change (((xs.length + 1 : Nat) : Int) % 64) = 1 at h
      omega
    · intro he
      apply Subtype.ext
      rw [scalar_mod64_val, hv]
      change (((xs.length + 1 : Nat) : Int) % 64) = 1
      omega
  have hclear : cleared = dequeWordStore (dequeGrownWords xs) 32 := by
    change initWords (encodeBits (xs ++ [false])) = _
    rw [dequeEncodeAppendFalse, dequeWordStoreInitial]
  have hdrop : ((if mod64 B.len == int 1 then deleteChunkEnd B.chunks (int 1)
      else pure ()) : BitMutationM Unit).run cleared = (.ok (), out) := by
    change ((if mod64 B.len == int 1 then deleteChunkEnd 0 (int 1)
      else pure ()) : BitMutationM Unit).run cleared =
      (.ok (), dequeTailStore (encodeBits xs) (if xs.length % 64 = 0
        then some (u64 0) :: List.replicate 32 none else List.replicate 32 none))
    rw [hmod, hclear]
    by_cases hm : xs.length % 64 = 0
    · simp only [hm, decide_true, ite_true, dequeGrownWords]
      apply dequeWordDeleteLast (encodeBits xs) (u64 0) 32
      rw [packedEncoded_length]
      unfold wordCount
      omega
    · simp only [hm, decide_false, Bool.false_eq_true, ite_false, dequeGrownWords]
      rfl
  have h := endPop_run (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
    (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation)
    B s s cleared out last hzero hread hwrite hdrop
  exact h.trans (by rw [hpred])

/-- A nonempty logical vector splits into its prefix and its final Boolean. -/
theorem endPopLastSplit (xs : List Bool) (hp : 0 < xs.length) :
    xs.take (xs.length - 1) ++ [xs.getD (xs.length - 1) false] = xs := by
  have hne : xs ≠ [] := by intro he; rw [he] at hp; exact Nat.lt_irrefl _ hp
  have hlast : xs.getLast hne = xs.getD (xs.length - 1) false := by
    rw [List.getLast_eq_getElem, List.getElem_eq_getD (fallback := false)]
  have h := List.take_append_getLast xs hne
  rw [hlast] at h
  exact h

/-- Successful end-pop returns the last bit and the exact encoding of the remaining prefix. -/
theorem endPopPackedRun (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (bitVectorPop
      (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
      (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation)
      (vectorBits xs)).run (initWords (encodeBits xs)) =
      (.ok ({vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)},
        xs.getD (xs.length - 1) false),
        dequeTailStore (encodeBits (xs.take (xs.length - 1)))
          (if xs.length % 64 = 1 then some (u64 0) :: List.replicate 32 none
            else List.replicate 32 none)) := by
  have hsplit := endPopLastSplit xs hp
  have hlen : (xs.take (xs.length - 1)).length = xs.length - 1 := by
    rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
  have hrem : (xs.length - 1) % 64 = 0 ↔ xs.length % 64 = 1 := by omega
  have h := dequeEndPopAppend (xs.take (xs.length - 1))
    (xs.getD (xs.length - 1) false) (by rw [hlen]; omega)
  have htransport := congrArg (fun ys : List Bool =>
    (bitVectorPop
      (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
      (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation)
      (vectorBits ys)).run (initWords (encodeBits ys))) hsplit.symm
  exact htransport.trans (h.trans (by
    simp only [vectorBits, List.length_append, List.length_cons, List.length_nil,
      hlen, hrem, Nat.sub_add_cancel (by omega : 1 ≤ xs.length)]))

/-- The end-pop branch satisfies both the logical result and the packed representation invariant. -/
theorem endPopSuccess (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    ∃ (B' : BitVector) (s' : State),
      (bitVectorPop
        (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
        (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation)
        (vectorBits xs)).run (initWords (encodeBits xs)) =
          (.ok (B', xs.getD (xs.length - 1) false), s') ∧
      bitValues s' B' = xs.take (xs.length - 1) ∧
      Round5.Round2.PackedInvariant s' B' := by
  let B' : BitVector := {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)}
  let s' := dequeTailStore (encodeBits (xs.take (xs.length - 1)))
    (if xs.length % 64 = 1 then some (u64 0) :: List.replicate 32 none
      else List.replicate 32 none)
  have htlen : (xs.take (xs.length - 1)).length = xs.length - 1 := by
    rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
  have hlen : B'.len = int (xs.take (xs.length - 1)).length := by
    change int ((xs.length - 1 : Nat) : Int) = _
    rw [htlen]
  have hn' : (xs.take (xs.length - 1)).length ≤ 9223372036854775807 := by
    rw [htlen]
    omega
  have hc : s'.contents B'.chunks = (encodeBits (xs.take (xs.length - 1))).map some :=
    dequeTailContents _ _ (packedEncoded_lengthBound _ hn')
  exact ⟨B', s', endPopPackedRun xs hp hn,
    scalar_bitValues_contents s' B' (xs.take (xs.length - 1)) hn' hlen hc,
    scalar_invariant_of_contents s' B' (xs.take (xs.length - 1)) hn' hlen hc⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- The frozen deque result predicate with its four execution results made explicit. -/
def dequeObservation (xs : List Bool) (s : State)
    (converted : JuliaLean.base.range.JlX Bool)
    (push pushfront : Id (Except Error BitVector × MutableMemory U64))
    (pop popfront : Id (Except Error (BitVector × Bool) × MutableMemory U64)) : Prop :=
  Round5.Round2.DequeAgrees.match_5 (fun _ => Prop) converted
    (fun _ =>
      Round5.Round2.DequeAgrees.match_1 (fun _ => Prop) push.1
        (fun _ => push.2 = s) (fun _ => False) ∧
      Round5.Round2.DequeAgrees.match_1 (fun _ => Prop) pushfront.1
        (fun _ => pushfront.2 = s) (fun _ => False))
    (fun value =>
      if xs.isEmpty then
        (JuliaLean.Proofs.base.bitarray.AppendPrependAgrees.match_1
          (fun _ _ => Prop) push.1 pushfront.1
          (fun pushed front =>
            bitValues push.2 pushed = [value] ∧ bitValues pushfront.2 front = [value] ∧
            Round5.Round2.PackedInvariant push.2 pushed ∧
            Round5.Round2.PackedInvariant pushfront.2 front)
          (fun _ _ => False)) ∧
        (Round5.Round2.DequeAgrees.match_3 (fun _ => Prop) pop.1
          (fun _ => pop.2 = s) (fun _ => False)) ∧
        (Round5.Round2.DequeAgrees.match_3 (fun _ => Prop) popfront.1
          (fun _ => popfront.2 = s) (fun _ => False))
      else
        JuliaLean.Proofs.base.bitarray.DequeAgrees.match_1 (fun _ _ _ _ => Prop)
          push.1 pushfront.1 pop.1 popfront.1
          (fun pushed front popped last frontPopped first =>
            bitValues push.2 pushed = xs ++ [value] ∧
            bitValues pushfront.2 front = value :: xs ∧
            last = xs.getD (xs.length - 1) false ∧
            bitValues pop.2 popped = xs.take (xs.length - 1) ∧
            first = xs.headD false ∧
            bitValues popfront.2 frontPopped = xs.drop 1 ∧
            Round5.Round2.PackedInvariant push.2 pushed ∧
            Round5.Round2.PackedInvariant pushfront.2 front ∧
            Round5.Round2.PackedInvariant pop.2 popped ∧
            Round5.Round2.PackedInvariant popfront.2 frontPopped)
          (fun _ _ _ _ => False))

/-- Abstracting the execution results preserves the exact frozen proposition. -/
theorem dequeFrozenFromObservation (xs : List Bool) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    dequeObservation xs s (JuliaLean.base.range.JConvert.convert (T := Bool) x)
      ((bitVectorPush Round5.Round2.convertBoolMutation Round5.Round2.checkBitVectorBounds B x).run s)
      ((bitVectorPushfirst Round5.Round2.convertBoolMutation B x).run s)
      ((bitVectorPop (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
        (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation) B).run s)
      ((bitVectorPopfirst B).run s) → Round5.Round2.DequeAgrees xs x := by
  exact fun h => h

/-- Failed conversions preserve both push states, irrespective of unused pop results. -/
theorem dequeObservationError (xs : List Bool) (s : State)
    (push pushfront : Id (Except Error BitVector × MutableMemory U64))
    (pop popfront : Id (Except Error (BitVector × Bool) × MutableMemory U64))
    (e : JuliaLean.base.range.Exc) (ep ef : Error)
    (hp : push = (.error ep, s)) (hf : pushfront = (.error ef, s)) :
    dequeObservation xs s (.error e) push pushfront pop popfront := by
  simp only [dequeObservation, hp, hf]
  exact ⟨True.intro, True.intro⟩

/-- Four successful nonempty deque calls combine into the frozen observation clause. -/
theorem dequeObservationNonempty (xs : List Bool) (s : State) (value : Bool)
    (push pushfront : Id (Except Error BitVector × MutableMemory U64))
    (pop popfront : Id (Except Error (BitVector × Bool) × MutableMemory U64))
    (Bp Bf Bo Bof : BitVector) (sp sf so sof : State)
    (hne : xs.isEmpty = false)
    (hp : push = (.ok Bp, sp)) (hf : pushfront = (.ok Bf, sf))
    (ho : pop = (.ok (Bo, xs.getD (xs.length - 1) false), so))
    (hof : popfront = (.ok (Bof, xs.headD false), sof))
    (hbp : bitValues sp Bp = xs ++ [value]) (hbf : bitValues sf Bf = value :: xs)
    (hbo : bitValues so Bo = xs.take (xs.length - 1))
    (hbof : bitValues sof Bof = xs.drop 1)
    (hip : Round5.Round2.PackedInvariant sp Bp) (hif : Round5.Round2.PackedInvariant sf Bf)
    (hio : Round5.Round2.PackedInvariant so Bo) (hiof : Round5.Round2.PackedInvariant sof Bof) :
    dequeObservation xs s (.ok value) push pushfront pop popfront := by
  simp only [dequeObservation, hne, Bool.false_eq_true, ite_false, hp, hf, ho, hof]
  exact ⟨hbp, hbf, True.intro, hbo, True.intro, hbof, hip, hif, hio, hiof⟩

/-- Empty deque calls combine successful single-bit pushes with unchanged error states. -/
theorem dequeObservationEmpty (s : State) (value : Bool)
    (push pushfront : Id (Except Error BitVector × MutableMemory U64))
    (pop popfront : Id (Except Error (BitVector × Bool) × MutableMemory U64))
    (Bp Bf : BitVector) (sp sf : State) (eo eof : Error)
    (hp : push = (.ok Bp, sp)) (hf : pushfront = (.ok Bf, sf))
    (ho : pop = (.error eo, s)) (hof : popfront = (.error eof, s))
    (hbp : bitValues sp Bp = [value]) (hbf : bitValues sf Bf = [value])
    (hip : Round5.Round2.PackedInvariant sp Bp) (hif : Round5.Round2.PackedInvariant sf Bf) :
    dequeObservation [] s (.ok value) push pushfront pop popfront := by
  simp only [dequeObservation, List.isEmpty_nil, ite_true, hp, hf, ho, hof]
  exact ⟨⟨hbp, hbf, hip, hif⟩, True.intro, True.intro⟩

/-- Conversion-case reasoning can be performed before instantiating any concrete executions. -/
theorem dequeObservationConvert (xs : List Bool) (s : State)
    (converted : JuliaLean.base.range.JlX Bool)
    (push pushfront : Id (Except Error BitVector × MutableMemory U64))
    (pop popfront : Id (Except Error (BitVector × Bool) × MutableMemory U64))
    (he : ∀ e, converted = .error e →
      dequeObservation xs s (.error e) push pushfront pop popfront)
    (hv : ∀ value, converted = .ok value →
      dequeObservation xs s (.ok value) push pushfront pop popfront) :
    dequeObservation xs s converted push pushfront pop popfront := by
  cases hc : converted with
  | error e => exact he e hc
  | ok value => exact hv value hc

/-- All four public deque operations satisfy the exact frozen logical and storage contract. -/
theorem BitarraysDeque_proven : JuliaLean.Proofs.base.bitarray.Round5.DequeAgrees := by
  intro xs X _ x hn
  let B := vectorBits xs
  let s := initWords (encodeBits xs)
  let push := (bitVectorPush Round5.Round2.convertBoolMutation
    Round5.Round2.checkBitVectorBounds B x).run s
  let pushfront := (bitVectorPushfirst Round5.Round2.convertBoolMutation B x).run s
  let pop := (bitVectorPop (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
    (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation) B).run s
  let popfront := (bitVectorPopfirst B).run s
  apply dequeFrozenFromObservation xs x
  change dequeObservation xs s (JuliaLean.base.range.JConvert.convert (T := Bool) x)
    push pushfront pop popfront
  apply dequeObservationConvert xs s _ push pushfront pop popfront
  · intro e hc
    exact dequeObservationError xs s push pushfront pop popfront e
      (Round5.Round2.mutationErrorOfRange e) (Round5.Round2.mutationErrorOfRange e)
      (dequePushConvertError x e B s Round5.Round2.checkBitVectorBounds hc)
      (dequePushfirstConvertError x e B s hc)
  · intro value hc
    obtain ⟨Bp, sp, hp, hbp, hip⟩ := dequePushCorrect xs x value hn hc
    obtain ⟨Bf, sf, hf, hbf, hif⟩ := dequePushfirstCorrect xs x value hn hc
    by_cases hempty : xs = []
    · subst xs
      have ho : pop = (.error (.argument "argument must not be empty"), s) :=
        dequePopEmpty (bitArrayGetIndex Round5.Round2.checkBitVectorBounds)
          (bitArraySetIndex Round5.Round2.checkBitVectorBounds Round5.Round2.convertBoolMutation)
          B s rfl
      have hof : popfront = (.error (.argument "argument must not be empty"), s) :=
        dequePopfirstEmpty B s rfl
      exact dequeObservationEmpty s value push pushfront pop popfront Bp Bf sp sf
        (.argument "argument must not be empty") (.argument "argument must not be empty")
        hp hf ho hof (by simpa only [List.nil_append] using hbp) hbf hip hif
    · have hpos : 0 < xs.length := List.length_pos_iff.mpr hempty
      have hbound : xs.length ≤ 9223372036854775807 := by
        change xs.length < 4611686018427387903 at hn
        omega
      obtain ⟨Bo, so, ho, hbo, hio⟩ := endPopSuccess xs hpos hbound
      obtain ⟨Bof, sof, hof, hbof, hiof⟩ := frontPopSuccess xs hpos hbound
      have hne : xs.isEmpty = false := by
        cases xs with
        | nil => exact False.elim (hempty rfl)
        | cons _ _ => rfl
      exact dequeObservationNonempty xs s value push pushfront pop popfront
        Bp Bf Bo Bof sp sf so sof hne hp hf ho hof hbp hbf hbo hbof hip hif hio hiof
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Logical insertion at a zero-based position. -/
def insertLogical (xs : List Bool) (p : Nat) (value : Bool) : List Bool :=
  xs.take p ++ value :: xs.drop p

/-- Insertion adds one Boolean when its position is at or before the logical end. -/
theorem insertLogicalLength (xs : List Bool) (p : Nat) (value : Bool)
    (hp : p ≤ xs.length) : (insertLogical xs p value).length = xs.length + 1 := by
  simp only [insertLogical, List.length_append, List.length_take, List.length_cons,
    List.length_drop, Nat.min_eq_left hp]
  omega

/-- Each logical insertion observation selects the prefix, new bit, or shifted suffix. -/
theorem insertLogicalGet (xs : List Bool) (p : Nat) (value : Bool)
    (hp : p ≤ xs.length) (k : Nat) :
    (insertLogical xs p value).getD k false =
      if k < p then xs.getD k false
      else if k = p then value else xs.getD (k - 1) false := by
  have ht : (xs.take p).length = p := by rw [List.length_take, Nat.min_eq_left hp]
  simp only [insertLogical, List.getD_eq_getElem?_getD]
  by_cases hk : k < p
  · rw [List.getElem?_append_left (by rw [ht]; exact hk),
      List.getElem?_take_of_lt hk, if_pos hk]
  · rw [List.getElem?_append_right (by rw [ht]; omega), ht, if_neg hk]
    by_cases he : k = p
    · subst k
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ite_true]
    · have hpos : k - p = (k - p - 1) + 1 := by omega
      rw [hpos, List.getElem?_cons_succ, List.getElem?_drop, if_neg he]
      have hi : p + (k - p - 1) = k - 1 := by omega
      rw [hi]

/-- A word mask after an insertion point contains exactly the higher bit positions. -/
theorem insertMaskBit (bit k : Nat) (hb : bit < 64) (hk : k < 64) :
    packedBit (shl_int u64Max (int bit)) k = decide (bit ≤ k) := by
  rw [dequePackedShiftLeft _ bit k hb, packedBit_max]
  have hsub : k - bit < 64 := by omega
  simp only [hk, hsub, decide_true, Bool.true_and, Bool.and_true]

/-- The selected insertion word preserves its low prefix and shifts its high suffix. -/
def insertShiftWord (word : U64) (bit : Nat) : U64 :=
  let after := shl_int u64Max (int bit)
  or_int (and_int (not_int after) word) (shl_int (and_int after word) (int 1))

/-- The vacant position in the partially shifted insertion word is zero. -/
theorem insertShiftWordBit (word : U64) (bit k : Nat) (hb : bit < 64) (hk : k < 64) :
    packedBit (insertShiftWord word bit) k =
      if k < bit then packedBit word k
      else if k = bit then false else packedBit word (k - 1) := by
  rw [insertShiftWord, packedBit_or, dequePackedAnd, dequePackedNot,
    insertMaskBit bit k hb hk, dequePackedLeftOne, dequePackedAnd,
    insertMaskBit bit (k - 1) hb (by omega)]
  simp only [hk, decide_true, Bool.true_and]
  by_cases hlt : k < bit
  · have h1 : ¬ bit ≤ k := by omega
    have h2 : ¬ bit ≤ k - 1 := by omega
    simp only [hlt, h1, h2, ite_true, decide_false, Bool.not_false, Bool.true_and,
      Bool.false_and, Bool.and_false, Bool.or_false]
  · have h1 : bit ≤ k := by omega
    rw [if_neg hlt]
    by_cases he : k = bit
    · subst k
      by_cases hz : bit = 0
      · subst bit
        rfl
      · have h2 : ¬ bit ≤ bit - 1 := by omega
        simp only [ite_true, h1, h2, decide_true, decide_false, Bool.not_true,
          Bool.false_and, Bool.and_false, Bool.false_or]
    · have h2 : bit ≤ k - 1 := by omega
      have h3 : 1 ≤ k := by omega
      simp only [he, h1, h2, h3, ite_false, decide_true, Bool.not_true,
        Bool.false_and, Bool.true_and, Bool.false_or]

/-- Zero-based chunk positions strictly after the insertion word, in Julia order. -/
def insertCarryIndices (n chunk : Nat) : List Nat :=
  (List.range (n - (chunk + 1))).reverse.map (fun j => chunk + 1 + j)

/-- The insertion carry range contains exactly the higher visible chunks. -/
theorem insertCarryIndicesMem (n chunk k : Nat) :
    k ∈ insertCarryIndices n chunk ↔ chunk < k ∧ k < n := by
  simp only [insertCarryIndices, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · intro hk
    exact ⟨k - (chunk + 1), by omega, by omega⟩

/-- Higher insertion chunks are updated in descending order. -/
theorem insertCarryIndicesSorted (n chunk : Nat) :
    List.Pairwise (fun a b : Nat => b < a) (insertCarryIndices n chunk) := by
  have general (count : Nat) : List.Pairwise (fun a b : Nat => b < a)
      ((List.range count).reverse.map (fun j => chunk + 1 + j)) := by
    induction count with
    | zero => exact List.Pairwise.nil
    | succ count ih =>
      simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.map_cons]
      refine List.Pairwise.cons ?_ ih
      intro k hk
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      have hj' : j < count := List.mem_range.mp (List.mem_reverse.mp hj)
      omega
  exact general _

/-- The complete shift stage before storing the new insertion bit. -/
def insertWords (xs : List Bool) (p : Nat) : List U64 :=
  let words := dequeGrownWords xs
  let shifted := (insertCarryIndices words.length (p / 64)).foldl dequeCarryLeftStep words
  shifted.set (p / 64) (insertShiftWord (shifted.getD (p / 64) (u64 0)) (p % 64))

/-- Packed words entirely before an insertion point retain their original bits. -/
theorem insertPackedBefore (xs : List Bool) (p chunk : Nat)
    (hp : p ≤ xs.length) (hc : (chunk + 1) * 64 ≤ p) :
    packedPrefix xs chunk 64 = packedPrefix (insertLogical xs p false) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk, insertLogicalGet xs p false hp]
  rw [if_pos (by omega)]

/-- Higher insertion words have the same carry expression as a front insertion. -/
theorem insertPackedAfter (xs : List Bool) (p chunk : Nat)
    (hp : p ≤ xs.length) (hc : p < chunk * 64) :
    packedPrefix (false :: xs) chunk 64 = packedPrefix (insertLogical xs p false) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk,
    insertLogicalGet xs p false hp, dequeGetCons]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The selected insertion word is the packed logical prefix and shifted suffix. -/
theorem insertPackedMiddle (xs : List Bool) (p : Nat) (hp : p ≤ xs.length) :
    insertShiftWord (packedPrefix xs (p / 64) 64) (p % 64) =
      packedPrefix (insertLogical xs p false) (p / 64) 64 := by
  apply packedBit_ext
  intro k hk
  rw [insertShiftWordBit _ (p % 64) k (Nat.mod_lt _ (by decide)) hk,
    packedWord_bit (insertLogical xs p false) (p / 64) k hk, insertLogicalGet xs p false hp]
  by_cases hlt : k < p % 64
  · rw [if_pos hlt, if_pos (show p / 64 * 64 + k < p by omega),
      packedWord_bit _ _ _ hk]
  · rw [if_neg hlt, if_neg (show ¬ p / 64 * 64 + k < p by omega)]
    by_cases he : k = p % 64
    · rw [if_pos he, if_pos (show p / 64 * 64 + k = p by omega)]
    · rw [if_neg he, if_neg (show p / 64 * 64 + k ≠ p by omega),
        packedWord_bit _ _ _ (by omega)]
      have hidx : p / 64 * 64 + (k - 1) = p / 64 * 64 + k - 1 := by omega
      rw [hidx]

/-- The complete packed insertion shift creates exactly one false logical slot. -/
theorem insertWordsEncode (xs : List Bool) (p : Nat) (hp : p ≤ xs.length) :
    insertWords xs p = encodeBits (insertLogical xs p false) := by
  let words := dequeGrownWords xs
  let chunk := p / 64
  let indices := insertCarryIndices words.length chunk
  let shifted := indices.foldl dequeCarryLeftStep words
  have hlen : words.length = wordCount (xs.length + 1) := dequeGrownWordsLength xs
  have hc : chunk < words.length := by
    rw [hlen]
    unfold wordCount
    dsimp only [chunk]
    omega
  have hslen : shifted.length = words.length := dequeCarryLeftFoldLength indices words
  have hib : ∀ j ∈ indices, 0 < j ∧ j < words.length := by
    intro j hj
    have hj' := (insertCarryIndicesMem words.length chunk j).mp hj
    omega
  have hfold := dequeCarryLeftFoldGet indices words hib
    (insertCarryIndicesSorted words.length chunk)
  have hmiddle : shifted.getD chunk (u64 0) = packedPrefix xs chunk 64 := by
    rw [hfold chunk, if_neg (by rw [insertCarryIndicesMem]; omega)]
    exact dequeGrownWordsGet xs chunk (by rw [← hlen]; exact hc)
  change shifted.set chunk (insertShiftWord (shifted.getD chunk (u64 0)) (p % 64)) = _
  rw [hmiddle]
  apply List.ext_getElem
  · rw [List.length_set, hslen, packedEncoded_length (insertLogical xs p false),
      insertLogicalLength xs p false hp, hlen]
  · intro k hk hk'
    have hkwords : k < words.length := by simpa only [List.length_set, hslen] using hk
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet shifted chunk k _ (by rw [hslen]; exact hc)]
    have hout : (encodeBits (insertLogical xs p false))[k] =
        packedPrefix (insertLogical xs p false) k 64 := by
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rw [hout]
    by_cases he : chunk = k
    · subst k
      rw [if_pos rfl]
      exact insertPackedMiddle xs p hp
    · rw [if_neg he, hfold k]
      by_cases hhigh : chunk < k
      · rw [if_pos ((insertCarryIndicesMem words.length chunk k).mpr ⟨hhigh, hkwords⟩)]
        rw [dequeGrownWordsGet xs k (by rw [← hlen]; exact hkwords),
          dequeGrownWordsGet xs (k - 1) (by rw [← hlen]; omega)]
        have hpast : p < k * 64 := by dsimp only [chunk] at hhigh; omega
        have hsucc : k - 1 + 1 = k := by omega
        have hcarry := dequePackedConsLater xs false (k - 1)
        rw [hsucc] at hcarry
        rw [hcarry]
        exact insertPackedAfter xs p k hp hpast
      · rw [if_neg (by rw [insertCarryIndicesMem]; omega)]
        rw [dequeGrownWordsGet xs k (by rw [← hlen]; exact hkwords)]
        apply insertPackedBefore xs p k hp
        dsimp only [chunk] at he hhigh
        omega

/-- The insertion tail after bounds checking, conversion, and chunk growth. -/
def insertTail (B : BitVector) (i : I64) (value : Bool) : BitMutationM BitVector := do
  let (k, j) := getChunksId i
  let B := { B with len := B.len + int 1 }
  let nc ← mutableLength B.chunks
  for t in (intRange (k + int 1) nc).reverse do
    let current ← mutableGet B.chunks t
    let previous ← mutableGet B.chunks (t - int 1)
    mutableSet B.chunks (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) t
  let after := shl_int u64Max j
  let before := not_int after
  let word ← mutableGet B.chunks k
  mutableSet B.chunks (or_int (and_int before word) (shl_int (and_int after word) (int 1))) k
  let _ ← bitArraySetIndex (fun _ _ => pure ()) (fun x => pure x) B value i
  return B

/-- Valid insertion is conversion, the common growth phase, and its packed tail. -/
theorem insertFactor {X : Type} (convert : X → BitMutationM Bool)
    (B : BitVector) (i : I64) (x : X)
    (hi : int 1 ≤ i ∧ i ≤ B.len + int 1) :
    bitVectorInsertInt convert B i x = (do
      let value ← convert x
      dequeGrowthFor B
      insertTail B i value) := by
  by_cases h : (mod64 B.len == int 0) = true <;>
    simp only [bitVectorInsertInt, hi, and_self, decide_true, Bool.not_true,
      Bool.false_eq_true, ite_false, dequeGrowthFor, insertTail, h, ite_true,
      bind_assoc, pure_bind]

/-- Successful insertion composes its abstract conversion, growth, and carry phases. -/
theorem insertFrom {X : Type} (convert : X → BitMutationM Bool)
    (B outB : BitVector) (i : I64) (x : X) (value : Bool) (s grown out : State)
    (hi : int 1 ≤ i ∧ i ≤ B.len + int 1)
    (hc : (convert x).run s = (.ok value, s))
    (hg : (dequeGrowthFor B).run s = (.ok (), grown))
    (ht : (insertTail B i value).run grown = (.ok outB, out)) :
    (bitVectorInsertInt convert B i x).run s = (.ok outB, out) := by
  rw [insertFactor convert B i x hi]
  simp only [shape_run_bind, hc, hg, ht]

/-- A checked internal store supplies the unchecked public setter used by insertion. -/
theorem insertUncheckedWrite (B : BitArray 1) (i : I64) (value : Bool) (s out : State)
    (hs : (unsafeBitSetIndex B.chunks value i).run s = (.ok (), out)) :
    (bitArraySetIndex (fun _ _ => pure ()) (fun x => pure x) B value i).run s =
      (.ok B, out) := by
  simp only [bitArraySetIndex, pure_bind]
  rw [shape_run_bind, hs]
  rfl

/-- An insertion tail follows from the checked outcomes of its packed operations. -/
theorem insertTailFrom (B : BitVector) (i chunk bit nc : I64) (value : Bool)
    (word : U64) (s shifted prepared out : State)
    (ha : getChunksId i = (chunk, bit))
    (hl : (mutableLength B.chunks).run s = (.ok nc, s))
    (hloop : (forIn (intRange (chunk + int 1) nc).reverse PUnit.unit (fun t _ => do
      let current ← mutableGet B.chunks t
      let previous ← mutableGet B.chunks (t - int 1)
      mutableSet B.chunks (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) t
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, shifted))
    (hget : (mutableGet B.chunks chunk).run shifted = (.ok word, shifted))
    (hmask : (mutableSet B.chunks
      (or_int (and_int (not_int (shl_int u64Max bit)) word)
        (shl_int (and_int (shl_int u64Max bit) word) (int 1))) chunk).run shifted =
          (.ok (), prepared))
    (hbit : (unsafeBitSetIndex B.chunks value i).run prepared = (.ok (), out)) :
    (insertTail B i value).run s = (.ok { B with len := B.len + int 1 }, out) := by
  have hwrite := insertUncheckedWrite { B with len := B.len + int 1 } i value
    prepared out hbit
  simp only [insertTail, ha]
  dsimp only [BitVector] at *
  simp only [shape_run_bind, hl, hloop, hget, hmask, hwrite]
  rfl

/-- The descending machine range enumerates the natural insertion carry positions. -/
theorem insertIntRange (n chunk : Nat) (hn : n + 1 ≤ 9223372036854775807)
    (hc : chunk < n) :
    (intRange (int ((chunk + 1 : Nat) : Int) + int 1) (int n)).reverse =
      (insertCarryIndices n chunk).map (fun j => int ((j + 1 : Nat) : Int)) := by
  have hstart : int ((chunk + 1 : Nat) : Int) + int 1 =
      int ((chunk + 2 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  rw [hstart]
  unfold intRange
  rw [packedInt_val n (by omega), packedInt_val (chunk + 2) (by omega)]
  have hlen : (((n : Int) - ((chunk + 2 : Nat) : Int) + 1).toNat) = n - (chunk + 1) := by
    omega
  rw [hlen]
  simp only [insertCarryIndices, List.map_map, List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro j _
  apply Subtype.ext
  change wrapInt .i64 (((chunk + 2 : Nat) : Int) + (j : Int)) =
    wrapInt .i64 (((chunk + 1 + j + 1 : Nat) : Int))
  apply congrArg (wrapInt .i64)
  omega

/-- Writing the vacant insertion bit gives the chosen logical value. -/
theorem insertLogicalSet (xs : List Bool) (p : Nat) (value : Bool)
    (hp : p ≤ xs.length) :
    (insertLogical xs p false).set p value = insertLogical xs p value := by
  have ht : (xs.take p).length = p := by rw [List.length_take, Nat.min_eq_left hp]
  unfold insertLogical
  rw [List.set_append_right p value (by rw [ht]; omega), ht]
  simp only [Nat.sub_self, List.set_cons_zero]

/-- The insertion tail preserves low bits and shifts every higher bit once. -/
theorem insertTailRun (xs : List Bool) (p : Nat) (value : Bool)
    (hp : p ≤ xs.length) (hn : xs.length < Round5.maxVectorLength) :
    (insertTail (vectorBits xs) (int ((p + 1 : Nat) : Int)) value).run (dequeGrowthState xs) =
      (.ok { vectorBits xs with len := (vectorBits xs).len + int 1 },
        dequeWordStore (encodeBits (insertLogical xs p value)) (dequePushSpare xs)) := by
  let words := dequeGrownWords xs
  let spare := dequePushSpare xs
  let chunk := p / 64
  let indices := insertCarryIndices words.length chunk
  let shifted := indices.foldl dequeCarryLeftStep words
  have hbits : xs.length + 1 ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hn
    omega
  have hlen : words.length = wordCount (xs.length + 1) := dequeGrownWordsLength xs
  have hwords : words.length + 1 ≤ 9223372036854775807 := by
    rw [hlen]
    unfold wordCount
    omega
  have hc : chunk < words.length := by
    rw [hlen]
    unfold wordCount
    dsimp only [chunk]
    omega
  have hslen : shifted.length = words.length := dequeCarryLeftFoldLength indices words
  have hib : ∀ j ∈ indices, 0 < j ∧ j < words.length := by
    intro j hj
    have hj' := (insertCarryIndicesMem words.length chunk j).mp hj
    omega
  have hlo := dequeCarryLeftLoop indices words spare (by omega) hib
  have hloop : (forIn
      (intRange (int ((chunk + 1 : Nat) : Int) + int 1) (int words.length)).reverse
      PUnit.unit (fun t _ => do
        let current ← mutableGet 0 t
        let previous ← mutableGet 0 (t - int 1)
        mutableSet 0 (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) t
        pure (ForInStep.yield PUnit.unit))).run (dequeWordStore words spare) =
          (.ok PUnit.unit, dequeWordStore shifted spare) := by
    rw [insertIntRange words.length chunk hwords hc]
    exact hlo
  have hget := dequeWordRead shifted spare chunk (by rw [hslen]; omega)
    (by rw [hslen]; exact hc)
  have hmask := dequeWordSet shifted spare chunk
    (insertShiftWord (shifted.getD chunk (u64 0)) (p % 64))
    (by rw [hslen]; omega) (by rw [hslen]; exact hc)
  have henc : shifted.set chunk (insertShiftWord (shifted.getD chunk (u64 0)) (p % 64)) =
      encodeBits (insertLogical xs p false) := insertWordsEncode xs p hp
  rw [henc] at hmask
  have hbit := dequeBitSetRun (insertLogical xs p false) spare p value
    (by rw [insertLogicalLength xs p false hp]; exact hbits)
    (by rw [insertLogicalLength xs p false hp]; omega)
  rw [insertLogicalSet xs p value hp] at hbit
  exact insertTailFrom (vectorBits xs) (int ((p + 1 : Nat) : Int))
    (int ((chunk + 1 : Nat) : Int)) (int ((p % 64 : Nat) : Int)) (int words.length)
    value (shifted.getD chunk (u64 0)) _ _ _ _ (scalar_chunks_nat p (by omega))
    (dequeWordLength words spare) hloop hget hmask hbit

/-- A natural insertion position satisfies the frozen machine bounds check. -/
theorem insertValidNat (xs : List Bool) (p : Nat)
    (hp : p ≤ xs.length) (hn : xs.length < Round5.maxVectorLength) :
    int 1 ≤ int ((p + 1 : Nat) : Int) ∧
      int ((p + 1 : Nat) : Int) ≤ (vectorBits xs).len + int 1 := by
  have hbits : xs.length + 1 ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hn
    omega
  have hnew : (vectorBits xs).len + int 1 = int ((xs.length + 1 : Nat) : Int) :=
    dequeLengthSucc xs.length hn
  rw [hnew]
  change 1 ≤ (int ((p + 1 : Nat) : Int)).val ∧
    (int ((p + 1 : Nat) : Int)).val ≤ (int ((xs.length + 1 : Nat) : Int)).val
  rw [packedInt_val (p + 1) (by omega), packedInt_val (xs.length + 1) hbits]
  omega

/-- Complete successful insertion execution at a natural zero-based position. -/
theorem insertRunNat (xs : List Bool) (p : Nat) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hp : p ≤ xs.length) (hn : xs.length < Round5.maxVectorLength)
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    (bitVectorInsertInt Round5.Round2.convertBoolMutation (vectorBits xs)
      (int ((p + 1 : Nat) : Int)) x).run (initWords (encodeBits xs)) =
      (.ok { vectorBits xs with len := (vectorBits xs).len + int 1 },
        dequeWordStore (encodeBits (insertLogical xs p value)) (dequePushSpare xs)) := by
  exact insertFrom Round5.Round2.convertBoolMutation (vectorBits xs) _
    (int ((p + 1 : Nat) : Int)) x value _ _ _ (insertValidNat xs p hp hn)
    (dequeConvertOk x value _ hc) (dequeGrowthPhaseRun xs hn) (insertTailRun xs p value hp hn)

/-- Complete successful insertion observations at a natural zero-based position. -/
theorem insertCorrectNat (xs : List Bool) (p : Nat) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hp : p ≤ xs.length) (hn : xs.length < Round5.maxVectorLength)
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    ∃ B' s',
      (bitVectorInsertInt Round5.Round2.convertBoolMutation (vectorBits xs)
        (int ((p + 1 : Nat) : Int)) x).run (initWords (encodeBits xs)) = (.ok B', s') ∧
      bitValues s' B' = insertLogical xs p value ∧ Round5.Round2.PackedInvariant s' B' := by
  refine ⟨_, _, insertRunNat xs p x value hp hn hc, ?_⟩
  apply dequeEncodedObservations
  · rw [insertLogicalLength xs p value hp]
    change xs.length < 4611686018427387903 at hn
    omega
  · change int xs.length + int 1 = int (insertLogical xs p value).length
    rw [insertLogicalLength xs p value hp]
    exact dequeLengthSucc xs.length hn
  · rfl

/-- The public insertion wrapper satisfies its complete successful contract. -/
theorem insertPublicCorrect (xs : List Bool) (i : I64) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hn : xs.length + 1 < Round5.maxVectorLength)
    (hi : int 1 ≤ i ∧ i ≤ int ((xs.length + 1 : Nat) : Int))
    (hc : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    ∃ B' s',
      (bitVectorInsert id (bitVectorInsertInt Round5.Round2.convertBoolMutation)
        (vectorBits xs) i x).run (initWords (encodeBits xs)) = (.ok B', s') ∧
      bitValues s' B' = xs.take (i.val.toNat - 1) ++ [value] ++ xs.drop (i.val.toNat - 1) ∧
      Round5.Round2.PackedInvariant s' B' := by
  have hbits : xs.length + 1 ≤ 9223372036854775807 := by
    change xs.length + 1 < 4611686018427387903 at hn
    omega
  have hiv : 1 ≤ i.val ∧ i.val ≤ ((xs.length + 1 : Nat) : Int) := by
    change 1 ≤ i.val ∧ i.val ≤ (int ((xs.length + 1 : Nat) : Int)).val at hi
    rw [packedInt_val (xs.length + 1) hbits] at hi
    exact hi
  let p := i.val.toNat - 1
  have hp : p ≤ xs.length := by dsimp only [p]; omega
  have hn' : xs.length < Round5.maxVectorLength := by omega
  have he : i = int ((p + 1 : Nat) : Int) := by
    apply Subtype.ext
    rw [packedInt_val (p + 1) (by omega)]
    dsimp only [p]
    omega
  obtain ⟨B', s', hr, hv, hinv⟩ := insertCorrectNat xs p x value hp hn' hc
  refine ⟨B', s', ?_, ?_, hinv⟩
  · change (bitVectorInsertInt Round5.Round2.convertBoolMutation (vectorBits xs) i x).run
      (initWords (encodeBits xs)) = _
    rw [he]
    exact hr
  · rw [hv]
    simp only [insertLogical, List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- Logical deletion at a zero-based position. -/
def deleteLogical (xs : List Bool) (p : Nat) : List Bool :=
  xs.take p ++ xs.drop (p + 1)

/-- Deleting an existing bit shortens the logical sequence by one. -/
theorem deleteLogicalLength (xs : List Bool) (p : Nat) (hp : p < xs.length) :
    (deleteLogical xs p).length = xs.length - 1 := by
  simp only [deleteLogical, List.length_append, List.length_take, List.length_drop,
    Nat.min_eq_left (by omega : p ≤ xs.length)]
  omega

/-- A logical deletion preserves its prefix and advances the remaining observations. -/
theorem deleteLogicalGet (xs : List Bool) (p : Nat) (hp : p < xs.length) (k : Nat) :
    (deleteLogical xs p).getD k false =
      if k < p then xs.getD k false else xs.getD (k + 1) false := by
  have ht : (xs.take p).length = p := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  simp only [deleteLogical, List.getD_eq_getElem?_getD]
  by_cases hk : k < p
  · rw [List.getElem?_append_left (by rw [ht]; exact hk),
      List.getElem?_take_of_lt hk, if_pos hk]
  · rw [List.getElem?_append_right (by rw [ht]; omega), ht, List.getElem?_drop, if_neg hk]
    have hi : p + 1 + (k - p) = k + 1 := by omega
    rw [hi]

/-- Subtraction forms the representable shift count used by the deletion mask. -/
theorem deleteMaskCount (bit : Nat) (hb : bit < 64) :
    int 63 - int bit = int ((63 - bit : Nat) : Int) := by
  rw [dequeIntSub]
  apply congrArg int
  omega

/-- The first deletion mask contains the selected bit and all lower positions. -/
theorem deleteBeforeMaskBit (bit k : Nat) (hb : bit < 64) :
    packedBit (lshr_int u64Max (int 63 - int bit)) k = decide (k ≤ bit) := by
  rw [deleteMaskCount bit hb, dequePackedShiftRight _ (63 - bit) k (by omega), packedBit_max]
  by_cases hk : k < 64
  · have he : (k + (63 - bit) < 64) ↔ k ≤ bit := by omega
    simp only [hk, he, decide_true, Bool.true_and]
  · have hnot : ¬ k ≤ bit := by omega
    simp only [hk, hnot, decide_false, Bool.false_and]

/-- The selected deletion word preserves its low prefix and shifts its high suffix. -/
def deleteShiftWord (word : U64) (bit : Nat) : U64 :=
  let before := lshr_int u64Max (int 63 - int bit)
  let after := not_int before
  or_int (and_int (lshr_int before (int 1)) word)
    (lshr_int (and_int after word) (int 1))

/-- The masked deletion shift removes the selected bit within one word. -/
theorem deleteShiftWordBit (word : U64) (bit k : Nat) (hb : bit < 64) (hk : k < 64) :
    packedBit (deleteShiftWord word bit) k =
      if k < bit then packedBit word k else packedBit word (k + 1) := by
  rw [deleteShiftWord, packedBit_or, dequePackedAnd, dequePackedRightOne,
    deleteBeforeMaskBit bit (k + 1) hb, dequePackedRightOne, dequePackedAnd,
    dequePackedNot, deleteBeforeMaskBit bit (k + 1) hb]
  simp only [hk, decide_true, Bool.true_and]
  by_cases hlt : k < bit
  · have hle : k + 1 ≤ bit := by omega
    simp only [hlt, hle, decide_true, ite_true, Bool.true_and, Bool.not_true,
      Bool.and_false, Bool.false_and, Bool.or_false]
  · have hle : ¬ k + 1 ≤ bit := by omega
    rw [if_neg hlt]
    simp only [hle, decide_false, Bool.false_and, Bool.not_false, Bool.and_true,
      Bool.false_or]
    by_cases htop : k + 1 < 64
    · simp only [htop, decide_true, Bool.true_and]
    · rw [dequePackedBitHigh word (k + 1) (by omega)]
      simp only [Bool.and_false]

/-- The chosen chunk also receives the low bit of its next chunk when one exists. -/
def deleteSelectedWord (words : List U64) (chunk bit : Nat) : U64 :=
  let base := deleteShiftWord (words.getD chunk (u64 0)) bit
  if chunk + 1 < words.length then
    or_int base (shl_int (words.getD (chunk + 1) (u64 0)) (int 63))
  else base

/-- The selected deletion word is prepared before the later ascending carry loop. -/
def deletePreparedWords (xs : List Bool) (p : Nat) : List U64 :=
  let words := encodeBits xs
  words.set (p / 64) (deleteSelectedWord words (p / 64) (p % 64))

/-- The ascending carry range excludes the selected word and final word. -/
def deleteCarryIndices (n chunk : Nat) : List Nat :=
  (List.range (n - (chunk + 2))).map (fun j => chunk + 1 + j)

/-- Exactly the interior words after the selected word receive loop carries. -/
theorem deleteCarryIndicesMem (n chunk k : Nat) :
    k ∈ deleteCarryIndices n chunk ↔ chunk < k ∧ k + 1 < n := by
  simp only [deleteCarryIndices, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · intro hk
    exact ⟨k - (chunk + 1), by omega, by omega⟩

/-- Deletion updates the later words in increasing order. -/
theorem deleteCarryIndicesSorted (n chunk : Nat) :
    List.Pairwise (fun a b : Nat => a < b) (deleteCarryIndices n chunk) := by
  rw [deleteCarryIndices, List.pairwise_map]
  exact List.Pairwise.imp (by intro a b hab; omega) List.pairwise_lt_range

/-- The packed expression computed by scalar deletion. -/
def deleteWords (xs : List Bool) (p : Nat) : List U64 :=
  let words := encodeBits xs
  let shifted := (deleteCarryIndices words.length (p / 64)).foldl dequeCarryRightStep
    (deletePreparedWords xs p)
  if xs.length % 64 = 1 then shifted.take (words.length - 1)
  else if p / 64 + 1 < words.length then
    shifted.set (words.length - 1)
      (lshr_int (shifted.getD (words.length - 1) (u64 0)) (int 1))
  else shifted

/-- A packed word wholly before the removed bit remains unchanged. -/
theorem deletePackedBefore (xs : List Bool) (p chunk : Nat)
    (hp : p < xs.length) (hc : (chunk + 1) * 64 ≤ p) :
    packedPrefix xs chunk 64 = packedPrefix (deleteLogical xs p) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk, deleteLogicalGet xs p hp]
  rw [if_pos (by omega)]

/-- Higher deletion chunks use the same right-carry formula as front-pop. -/
theorem deletePackedAfter (xs : List Bool) (p chunk : Nat)
    (hp : p < xs.length) (hc : p < chunk * 64) :
    packedPrefix (xs.drop 1) chunk 64 = packedPrefix (deleteLogical xs p) chunk 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ _ _ hk, packedWord_bit _ _ _ hk,
    deleteLogicalGet xs p hp, dequeGetDropOne]
  rw [if_neg (by omega)]

/-- The masked deletion word and carry encode the selected logical chunk. -/
theorem deletePackedMiddle (xs : List Bool) (p : Nat) (hp : p < xs.length) :
    or_int (deleteShiftWord (packedPrefix xs (p / 64) 64) (p % 64))
      (shl_int (packedPrefix xs (p / 64 + 1) 64) (int 63)) =
        packedPrefix (deleteLogical xs p) (p / 64) 64 := by
  apply packedBit_ext
  intro k hk
  rw [packedBit_or, deleteShiftWordBit _ (p % 64) k (Nat.mod_lt _ (by decide)) hk,
    dequePackedLeft63, packedWord_bit (deleteLogical xs p) (p / 64) k hk,
    deleteLogicalGet xs p hp]
  by_cases htop : k = 63
  · subst k
    have hrem : ¬ 63 < p % 64 := by omega
    rw [if_neg hrem, dequePackedBitHigh _ (63 + 1) (by decide)]
    simp only [hk, Nat.le_refl, decide_true, Bool.true_and, Bool.false_or, Nat.sub_self]
    rw [packedWord_bit _ _ 0 (by decide), if_neg (show ¬ p / 64 * 64 + 63 < p by omega)]
    have hidx : (p / 64 + 1) * 64 + 0 = p / 64 * 64 + 63 + 1 := by omega
    rw [hidx]
  · have hlow : ¬ 63 ≤ k := by omega
    simp only [hlow, decide_false, Bool.false_and, Bool.and_false, Bool.or_false]
    by_cases hlt : k < p % 64
    · rw [if_pos hlt, if_pos (show p / 64 * 64 + k < p by omega),
        packedWord_bit _ _ _ hk]
    · rw [if_neg hlt, if_neg (show ¬ p / 64 * 64 + k < p by omega),
        packedWord_bit _ _ _ (by omega)]
      have hidx : p / 64 * 64 + (k + 1) = p / 64 * 64 + k + 1 := by omega
      rw [hidx]

/-- Reading the next word conditionally is equivalent to its zero-padded packing. -/
theorem deleteSelectedWordPacked (xs : List Bool) (p : Nat) (hp : p < xs.length) :
    deleteSelectedWord (encodeBits xs) (p / 64) (p % 64) =
      packedPrefix (deleteLogical xs p) (p / 64) 64 := by
  have hc : p / 64 < wordCount xs.length := by unfold wordCount; omega
  unfold deleteSelectedWord
  rw [dequeEncodedGet xs (p / 64) hc]
  by_cases hn : p / 64 + 1 < (encodeBits xs).length
  · rw [if_pos hn, dequeEncodedGet xs (p / 64 + 1)
      (by rw [← packedEncoded_length xs]; exact hn)]
    exact deletePackedMiddle xs p hp
  · rw [if_neg hn]
    have hb : xs.length ≤ (p / 64 + 1) * 64 := by
      rw [packedEncoded_length] at hn
      unfold wordCount at hn
      omega
    have h := deletePackedMiddle xs p hp
    rw [dequePackedBeyond xs (p / 64 + 1) hb] at h
    have hz : shl_int (u64 0) (int 63) = u64 0 := rfl
    rw [hz, dequePackedOrZero] at h
    exact h

/-- Preparing the chosen deletion chunk changes no other chunk. -/
theorem deletePreparedGet (xs : List Bool) (p k : Nat) (hp : p < xs.length) :
    (deletePreparedWords xs p).getD k (u64 0) =
      if p / 64 = k then packedPrefix (deleteLogical xs p) (p / 64) 64
      else (encodeBits xs).getD k (u64 0) := by
  have hc : p / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  rw [deletePreparedWords, dequeWordGetSet _ _ _ _ hc, deleteSelectedWordPacked xs p hp]

/-- The full packed scalar-deletion expression encodes removal of exactly one bit. -/
theorem deleteWordsEncode (xs : List Bool) (p : Nat) (hp : p < xs.length) :
    deleteWords xs p = encodeBits (deleteLogical xs p) := by
  let words := encodeBits xs
  let chunk := p / 64
  let prepared := deletePreparedWords xs p
  let indices := deleteCarryIndices words.length chunk
  let shifted := indices.foldl dequeCarryRightStep prepared
  have hlen : words.length = wordCount xs.length := packedEncoded_length xs
  have hpos : 0 < words.length := by rw [hlen]; unfold wordCount; omega
  have hc : chunk < words.length := by
    rw [hlen]
    unfold wordCount
    dsimp only [chunk]
    omega
  have hplen : prepared.length = words.length := List.length_set
  have hslen : shifted.length = words.length := by
    rw [dequeCarryRightFoldLength]
    exact hplen
  have hib : ∀ j ∈ indices, j + 1 < prepared.length := by
    intro j hj
    have hj' := (deleteCarryIndicesMem words.length chunk j).mp hj
    rw [hplen]
    exact hj'.2
  have hfold := dequeCarryRightFoldGet indices prepared hib
    (deleteCarryIndicesSorted words.length chunk)
  have hselected : shifted.getD chunk (u64 0) =
      packedPrefix (deleteLogical xs p) chunk 64 := by
    rw [hfold chunk, if_neg (by rw [deleteCarryIndicesMem]; omega),
      deletePreparedGet xs p chunk hp, if_pos rfl]
  have hinner (k : Nat) (hk : k < words.length - 1) :
      shifted.getD k (u64 0) = packedPrefix (deleteLogical xs p) k 64 := by
    by_cases he : chunk = k
    · subst k
      exact hselected
    · rw [hfold k]
      by_cases hhigh : chunk < k
      · rw [if_pos ((deleteCarryIndicesMem words.length chunk k).mpr ⟨hhigh, by omega⟩)]
        rw [deletePreparedGet xs p k hp, if_neg he,
          deletePreparedGet xs p (k + 1) hp, if_neg (show p / 64 ≠ k + 1 by dsimp only [chunk] at hhigh; omega)]
        rw [dequeEncodedGet xs k (by rw [← hlen]; omega),
          dequeEncodedGet xs (k + 1) (by rw [← hlen]; omega), dequePackedDropFirst]
        apply deletePackedAfter xs p k hp
        dsimp only [chunk] at hhigh
        omega
      · rw [if_neg (by rw [deleteCarryIndicesMem]; omega),
          deletePreparedGet xs p k hp, if_neg he,
          dequeEncodedGet xs k (by rw [← hlen]; omega)]
        apply deletePackedBefore xs p k hp
        dsimp only [chunk] at he hhigh
        omega
  have hlast (hhigh : chunk + 1 < words.length) :
      shifted.getD (words.length - 1) (u64 0) =
        packedPrefix xs (words.length - 1) 64 := by
    rw [hfold (words.length - 1), if_neg (by rw [deleteCarryIndicesMem]; omega),
      deletePreparedGet xs p (words.length - 1) hp,
      if_neg (show p / 64 ≠ words.length - 1 by dsimp only [chunk] at hhigh; omega)]
    exact dequeEncodedGet xs (words.length - 1) (by rw [← hlen]; omega)
  have hlastShift (hhigh : chunk + 1 < words.length) :
      lshr_int (shifted.getD (words.length - 1) (u64 0)) (int 1) =
        packedPrefix (deleteLogical xs p) (words.length - 1) 64 := by
    rw [hlast hhigh, dequePackedDropLast xs (words.length - 1)
      (by rw [hlen]; unfold wordCount; omega)]
    apply deletePackedAfter xs p (words.length - 1) hp
    dsimp only [chunk] at hhigh
    omega
  by_cases hm : xs.length % 64 = 1
  · unfold deleteWords
    rw [if_pos hm]
    change shifted.take (words.length - 1) = _
    apply List.ext_getElem
    · rw [List.length_take, hslen, Nat.min_eq_left (by omega),
        packedEncoded_length (deleteLogical xs p), deleteLogicalLength xs p hp,
        dequeWordCountPred xs.length (by omega), if_pos hm, hlen]
    · intro k hk hk'
      rw [List.getElem_take, List.getElem_eq_getD (fallback := u64 0)]
      have hkbound : k < words.length - 1 := by
        have hkt := hk
        rw [List.length_take, hslen, Nat.min_eq_left (by omega)] at hkt
        exact hkt
      rw [hinner k hkbound]
      simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  · unfold deleteWords
    rw [if_neg hm]
    by_cases hhigh : chunk + 1 < words.length
    · rw [if_pos hhigh]
      change shifted.set (words.length - 1) _ = _
      rw [hlastShift hhigh]
      apply List.ext_getElem
      · rw [List.length_set, hslen, packedEncoded_length (deleteLogical xs p),
          deleteLogicalLength xs p hp, dequeWordCountPred xs.length (by omega), if_neg hm, hlen]
      · intro k hk hk'
        have hkbound : k < words.length := by simpa only [List.length_set, hslen] using hk
        rw [List.getElem_eq_getD (fallback := u64 0),
          dequeWordGetSet shifted (words.length - 1) k _ (by rw [hslen]; omega)]
        have hout : (encodeBits (deleteLogical xs p))[k] =
            packedPrefix (deleteLogical xs p) k 64 := by
          simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
        rw [hout]
        by_cases he : words.length - 1 = k
        · subst k
          rw [if_pos rfl]
        · rw [if_neg he]
          exact hinner k (by omega)
    · rw [if_neg hhigh]
      change shifted = _
      apply List.ext_getElem
      · rw [hslen, packedEncoded_length (deleteLogical xs p), deleteLogicalLength xs p hp,
          dequeWordCountPred xs.length (by omega), if_neg hm, hlen]
      · intro k hk hk'
        have hkbound : k < words.length := by simpa only [hslen] using hk
        rw [List.getElem_eq_getD (fallback := u64 0)]
        have hout : (encodeBits (deleteLogical xs p))[k] =
            packedPrefix (deleteLogical xs p) k 64 := by
          simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
        rw [hout]
        by_cases he : k = chunk
        · subst k
          exact hselected
        · exact hinner k (by omega)
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

/-- The selected deletion word removes one bit before adding a possible carry. -/
def deleteRawWord (word : U64) (bit : I64) : U64 :=
  let before := lshr_int u64Max (int 63 - bit)
  or_int (and_int (lshr_int before (int 1)) word)
    (lshr_int (and_int (not_int before) word) (int 1))

/-- The scalar-deletion carry loop visits words after the selected chunk. -/
def deleteAtLoop (chunks : Nat) (chunk nc : I64) : BitMutationM PUnit :=
  forIn (intRange (chunk + int 1) (nc - int 1)) PUnit.unit (fun t _ => do
    let current ← mutableGet chunks t
    let next ← mutableGet chunks (t + int 1)
    mutableSet chunks (or_int (lshr_int current (int 1)) (shl_int next (int 63))) t
    pure (ForInStep.yield PUnit.unit))

/-- Scalar deletion either removes an exhausted last word or shifts the final word. -/
def deleteAtTail (B : BitArray 1) (chunk nc : I64) : BitMutationM (BitArray 1) := do
  if mod64 B.len == int 1 then
    deleteChunkEnd B.chunks (int 1)
  else if nc > chunk then
    let last ← mutableGet B.chunks nc
    mutableSet B.chunks (lshr_int last (int 1)) nc
  return { B with len := B.len - int 1 }

/-- Known primitive outcomes compose to the complete packed scalar deletion. -/
theorem deleteRunFrom (B outB : BitArray 1) (i chunk bit nc : I64)
    (word next : U64) (s prepared shifted out : State)
    (ha : getChunksId i = (chunk, bit))
    (hg : (mutableGet B.chunks chunk).run s = (.ok word, s))
    (hl : (mutableLength B.chunks).run s = (.ok nc, s))
    (hn : nc > chunk → (mutableGet B.chunks (chunk + int 1)).run s = (.ok next, s))
    (hw : (mutableSet B.chunks
      (if nc > chunk then or_int (deleteRawWord word bit) (shl_int next (int 63))
        else deleteRawWord word bit) chunk).run s = (.ok (), prepared))
    (hloop : (deleteAtLoop B.chunks chunk nc).run prepared = (.ok PUnit.unit, shifted))
    (htail : (deleteAtTail B chunk nc).run shifted = (.ok outB, out)) :
    (bitVectorDeleteAtInt B i).run s = (.ok outB, out) := by
  unfold deleteAtLoop at hloop
  unfold deleteAtTail at htail
  by_cases hc : nc > chunk
  · simp only [hc, ite_true] at htail
    have hnext := hn hc
    simp only [hc, ite_true, deleteRawWord] at hw
    simp only [bitVectorDeleteAtInt, ha, shape_run_bind, hg, hl, hc, ite_true,
      hnext, hw, hloop]
    exact htail
  · simp only [hc, ite_false] at htail
    simp only [hc, ite_false, deleteRawWord] at hw
    simp only [bitVectorDeleteAtInt, ha, shape_run_bind, hg, hl, hc, ite_false,
      shape_run_pure, hw, hloop]
    exact htail

/-- A deleting tail composes the memory removal with the updated vector header. -/
theorem deleteTailDeleteFrom (B : BitArray 1) (chunk nc : I64) (s out : State)
    (hm : (mod64 B.len == int 1) = true)
    (hd : (deleteChunkEnd B.chunks (int 1)).run s = (.ok (), out)) :
    (deleteAtTail B chunk nc).run s = (.ok { B with len := B.len - int 1 }, out) := by
  simp only [deleteAtTail, hm, ite_true, shape_run_bind, hd, shape_run_pure]

/-- A shifting tail composes its final read and write with the updated header. -/
theorem deleteTailShiftFrom (B : BitArray 1) (chunk nc : I64) (word : U64) (s out : State)
    (hm : (mod64 B.len == int 1) = false) (hc : nc > chunk)
    (hr : (mutableGet B.chunks nc).run s = (.ok word, s))
    (hw : (mutableSet B.chunks (lshr_int word (int 1)) nc).run s = (.ok (), out)) :
    (deleteAtTail B chunk nc).run s = (.ok { B with len := B.len - int 1 }, out) := by
  simp only [deleteAtTail, hm, Bool.false_eq_true, ite_false, hc, ite_true, dite_true,
    shape_run_bind, hr, hw, shape_run_pure]

/-- Deleting within the final word needs no further tail mutation. -/
theorem deleteTailSameFrom (B : BitArray 1) (chunk nc : I64) (s : State)
    (hm : (mod64 B.len == int 1) = false) (hc : ¬ nc > chunk) :
    (deleteAtTail B chunk nc).run s = (.ok { B with len := B.len - int 1 }, s) := by
  simp only [deleteAtTail, hm, Bool.false_eq_true, ite_false, hc, dite_false, shape_run_pure]

/-- The public deletion wrapper performs the packed deletion after a valid bounds check. -/
theorem deletePublicValid (B : BitArray 1) (i : I64)
    (hi : int 1 ≤ i ∧ i ≤ B.len) :
    bitVectorDeleteAt (fun _ : I64 => false) (fun _ => pure ()) id B i =
      bitVectorDeleteAtInt B i := by
  simp only [bitVectorDeleteAt, Bool.false_eq_true, ite_false, id_eq, hi, and_self,
    decide_true, Bool.not_true]

/-- The machine deletion interval enumerates the interior natural carry indices. -/
theorem deleteIntRange (n chunk : Nat) (hn : n + 1 ≤ 9223372036854775807)
    (hc : chunk < n) :
    intRange (int ((chunk + 1 : Nat) : Int) + int 1) (int n - int 1) =
      (deleteCarryIndices n chunk).map (fun j => int ((j + 1 : Nat) : Int)) := by
  have hstart : int ((chunk + 1 : Nat) : Int) + int 1 =
      int ((chunk + 2 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  rw [hstart, frontPopLengthPred n (by omega)]
  unfold intRange
  rw [packedInt_val (n - 1) (by omega), packedInt_val (chunk + 2) (by omega)]
  have hlen : ((((n - 1 : Nat) : Int) - ((chunk + 2 : Nat) : Int) + 1).toNat) =
      n - (chunk + 2) := by omega
  rw [hlen]
  simp only [deleteCarryIndices, List.map_map]
  apply List.map_congr_left
  intro j _
  apply Subtype.ext
  change wrapInt .i64 (((chunk + 2 : Nat) : Int) + (j : Int)) =
    wrapInt .i64 (((chunk + 1 + j + 1 : Nat) : Int))
  apply congrArg (wrapInt .i64)
  omega

/-- The concrete deletion carry loop implements the ascending word fold. -/
theorem deleteLoopRun (words : List U64) (spare chunk : Nat)
    (hn : words.length + 1 ≤ 9223372036854775807) (hc : chunk < words.length) :
    (deleteAtLoop 0 (int ((chunk + 1 : Nat) : Int)) (int words.length)).run
      (dequeWordStore words spare) =
        (.ok PUnit.unit, dequeWordStore
          ((deleteCarryIndices words.length chunk).foldl dequeCarryRightStep words) spare) := by
  unfold deleteAtLoop
  rw [deleteIntRange words.length chunk hn hc]
  apply dequeCarryRightLoop _ words spare (by omega)
  intro j hj
  exact ((deleteCarryIndicesMem words.length chunk j).mp hj).2

/-- Comparing a word count with the selected one-based word is ordinary natural comparison. -/
theorem deleteChunkLt (n chunk : Nat) (hn : n ≤ 9223372036854775807)
    (hc : chunk + 1 ≤ 9223372036854775807) :
    (int n > int ((chunk + 1 : Nat) : Int)) ↔ chunk + 1 < n := by
  change (int ((chunk + 1 : Nat) : Int)).val < (int n).val ↔ _
  rw [packedInt_val (chunk + 1) hc, packedInt_val n hn]
  omega

/-- The selected word is changed exactly once before higher carry positions are visited. -/
theorem deletePrepareRun (xs : List Bool) (p spare : Nat)
    (hp : p < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    let words := encodeBits xs
    let chunk := p / 64
    (mutableSet 0
      (if int words.length > int ((chunk + 1 : Nat) : Int) then
        or_int (deleteRawWord (words.getD chunk (u64 0)) (int ((p % 64 : Nat) : Int)))
          (shl_int (words.getD (chunk + 1) (u64 0)) (int 63))
      else deleteRawWord (words.getD chunk (u64 0)) (int ((p % 64 : Nat) : Int)))
      (int ((chunk + 1 : Nat) : Int))).run (dequeWordStore words spare) =
        (.ok (), dequeWordStore (deletePreparedWords xs p) spare) := by
  let words := encodeBits xs
  let chunk := p / 64
  have hw : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hc : chunk < words.length := by
    change p / 64 < (encodeBits xs).length
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hindex := deleteChunkLt words.length chunk hw (by omega)
  have hword :
      (if int words.length > int ((chunk + 1 : Nat) : Int) then
        or_int (deleteRawWord (words.getD chunk (u64 0)) (int ((p % 64 : Nat) : Int)))
          (shl_int (words.getD (chunk + 1) (u64 0)) (int 63))
      else deleteRawWord (words.getD chunk (u64 0)) (int ((p % 64 : Nat) : Int))) =
        deleteSelectedWord words chunk (p % 64) := by
    simp only [hindex, deleteSelectedWord, deleteRawWord, deleteShiftWord]
  have hset := dequeWordSet words spare chunk (deleteSelectedWord words chunk (p % 64)) hw hc
  dsimp only
  rw [hword]
  exact hset

/-- Spare slots after scalar deletion; a removed final word stays assigned in backing memory. -/
def deleteStaleTail (xs : List Bool) (p spare : Nat) : List (Option U64) :=
  let words := encodeBits xs
  let shifted := (deleteCarryIndices words.length (p / 64)).foldl dequeCarryRightStep
    (deletePreparedWords xs p)
  if xs.length % 64 = 1 then
    some (shifted.getD (words.length - 1) (u64 0)) :: List.replicate spare none
  else List.replicate spare none

/-- The final scalar-deletion phase handles exhausted and surviving final words. -/
theorem deleteTailRun (xs : List Bool) (p spare : Nat)
    (hp : p < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    let words := encodeBits xs
    let shifted := (deleteCarryIndices words.length (p / 64)).foldl dequeCarryRightStep
      (deletePreparedWords xs p)
    (deleteAtTail (vectorBits xs) (int ((p / 64 + 1 : Nat) : Int)) (int words.length)).run
      (dequeWordStore shifted spare) =
        (.ok {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)},
          dequeTailStore (deleteWords xs p) (deleteStaleTail xs p spare)) := by
  let words := encodeBits xs
  let prepared := deletePreparedWords xs p
  let shifted := (deleteCarryIndices words.length (p / 64)).foldl dequeCarryRightStep prepared
  have hcount : words.length = wordCount xs.length := packedEncoded_length xs
  have hpos : 0 < words.length := by rw [hcount]; unfold wordCount; omega
  have hbound : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hprelen : prepared.length = words.length := List.length_set
  have hslen : shifted.length = words.length :=
    (dequeCarryRightFoldLength _ prepared).trans hprelen
  have hspos : 0 < shifted.length := by rw [hslen]; exact hpos
  have hsbound : shifted.length ≤ 9223372036854775807 := by rw [hslen]; exact hbound
  have hchunk : p / 64 < words.length := by rw [hcount]; unfold wordCount; omega
  have hcompare := deleteChunkLt words.length (p / 64) hbound (by omega)
  have hheader : ({vectorBits xs with len := (vectorBits xs).len - int 1} : BitVector) =
      {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)} :=
    congrArg (fun len => ({vectorBits xs with len := len} : BitVector))
      (frontPopLengthPred xs.length (by omega))
  by_cases hm : xs.length % 64 = 1
  · have hbranch : (mod64 (int (xs.length : Int)) == int 1) = true := by
      simp only [frontPopModOne xs.length hn, hm, decide_true]
    have hd := frontPopDeleteLastRun shifted spare hspos hsbound
    rw [hslen] at hd
    have ht := deleteTailDeleteFrom (vectorBits xs) (int ((p / 64 + 1 : Nat) : Int))
      (int words.length) (dequeWordStore shifted spare) _ hbranch hd
    exact ht.trans (by
      rw [hheader]
      simp only [deleteWords, deleteStaleTail, hm, ite_true]
      rfl)
  · have hbranch : (mod64 (int (xs.length : Int)) == int 1) = false := by
      simp only [frontPopModOne xs.length hn, hm, decide_false]
    by_cases hc : p / 64 + 1 < words.length
    · change p / 64 + 1 < (encodeBits xs).length at hc
      have hr := dequeWordRead shifted spare (words.length - 1) hsbound
        (by rw [hslen]; omega)
      have hw := dequeWordSet shifted spare (words.length - 1)
        (lshr_int (shifted.getD (words.length - 1) (u64 0)) (int 1)) hsbound
        (by rw [hslen]; omega)
      have hi : words.length - 1 + 1 = words.length := by omega
      rw [hi] at hr hw
      have ht := deleteTailShiftFrom (vectorBits xs) (int ((p / 64 + 1 : Nat) : Int))
        (int words.length) _ (dequeWordStore shifted spare) _ hbranch (hcompare.mpr hc) hr hw
      exact ht.trans (by
        rw [hheader]
        simp only [deleteWords, deleteStaleTail, hm, ite_false, hc, ite_true]
        rfl)
    · change ¬ p / 64 + 1 < (encodeBits xs).length at hc
      have ht := deleteTailSameFrom (vectorBits xs) (int ((p / 64 + 1 : Nat) : Int))
        (int words.length) (dequeWordStore shifted spare) hbranch
        (fun h => hc (hcompare.mp h))
      exact ht.trans (by
        rw [hheader]
        simp only [deleteWords, deleteStaleTail, hm, ite_false, hc]
        rfl)

/-- Scalar deletion at a natural position computes the exact remaining packed encoding. -/
theorem deleteRunNat (xs : List Bool) (p : Nat)
    (hp : p < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (bitVectorDeleteAtInt (vectorBits xs) (int ((p + 1 : Nat) : Int))).run
      (initWords (encodeBits xs)) =
        (.ok {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)},
          dequeTailStore (encodeBits (deleteLogical xs p)) (deleteStaleTail xs p 32)) := by
  let words := encodeBits xs
  let chunk := p / 64
  let prepared := deletePreparedWords xs p
  let shifted := (deleteCarryIndices words.length chunk).foldl dequeCarryRightStep prepared
  have hcount : words.length = wordCount xs.length := packedEncoded_length xs
  have hbound : words.length + 1 ≤ 9223372036854775807 := by
    rw [hcount]
    unfold wordCount
    omega
  have hc : chunk < words.length := by rw [hcount]; unfold wordCount; dsimp only [chunk]; omega
  have hprelen : prepared.length = words.length := List.length_set
  have hget := dequeWordRead words 32 chunk (by omega) hc
  have hlength := dequeWordLength words 32
  have hnext : int words.length > int ((chunk + 1 : Nat) : Int) →
      (mutableGet 0 (int ((chunk + 1 : Nat) : Int) + int 1)).run (dequeWordStore words 32) =
        (.ok (words.getD (chunk + 1) (u64 0)), dequeWordStore words 32) := by
    intro h
    have hj := (deleteChunkLt words.length chunk (by omega) (by omega)).mp h
    have hr := dequeWordRead words 32 (chunk + 1) (by omega) hj
    rw [dequeNatAddOne (chunk + 1)]
    exact hr
  have hwrite := deletePrepareRun xs p 32 hp hn
  have hloop := deleteLoopRun prepared 32 chunk (by rw [hprelen]; exact hbound)
    (by rw [hprelen]; exact hc)
  rw [hprelen] at hloop
  have htail := deleteTailRun xs p 32 hp hn
  dsimp only at htail
  have hrun := deleteRunFrom (vectorBits xs) _ (int ((p + 1 : Nat) : Int))
    (int ((chunk + 1 : Nat) : Int)) (int ((p % 64 : Nat) : Int)) (int words.length)
    (words.getD chunk (u64 0)) (words.getD (chunk + 1) (u64 0))
    (dequeWordStore words 32) (dequeWordStore prepared 32) (dequeWordStore shifted 32) _
    (scalar_chunks_nat p (by omega)) hget hlength hnext hwrite hloop htail
  have hinit := congrArg (fun st : State =>
    (bitVectorDeleteAtInt (vectorBits xs) (int ((p + 1 : Nat) : Int))).run st)
    (dequeWordStoreInitial words).symm
  exact hinit.trans (hrun.trans (by rw [deleteWordsEncode xs p hp]))

/-- A successful natural-position deletion satisfies the logical result and representation invariant. -/
theorem deleteCorrectNat (xs : List Bool) (p : Nat)
    (hp : p < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    ∃ (B' : BitArray 1) (s' : State),
      (bitVectorDeleteAtInt (vectorBits xs) (int ((p + 1 : Nat) : Int))).run
        (initWords (encodeBits xs)) = (.ok B', s') ∧
      bitValues s' B' = deleteLogical xs p ∧ Round5.Round2.PackedInvariant s' B' := by
  let B' : BitArray 1 := {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)}
  let s' := dequeTailStore (encodeBits (deleteLogical xs p)) (deleteStaleTail xs p 32)
  have hn' : (deleteLogical xs p).length ≤ 9223372036854775807 := by
    rw [deleteLogicalLength xs p hp]
    omega
  have hl : B'.len = int (deleteLogical xs p).length := by
    change int ((xs.length - 1 : Nat) : Int) = _
    rw [deleteLogicalLength xs p hp]
  have hc : s'.contents B'.chunks = (encodeBits (deleteLogical xs p)).map some :=
    dequeTailContents _ _ (packedEncoded_lengthBound _ hn')
  exact ⟨B', s', deleteRunNat xs p hp hn,
    scalar_bitValues_contents s' B' (deleteLogical xs p) hn' hl hc,
    scalar_invariant_of_contents s' B' (deleteLogical xs p) hn' hl hc⟩

/-- The public scalar deletion wrapper satisfies its complete valid-index contract. -/
theorem deletePublicCorrect (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hi : int 1 ≤ i ∧ i ≤ int xs.length) :
    ∃ (B' : BitArray 1) (s' : State),
      (bitVectorDeleteAt (fun _ : I64 => false) (fun _ => pure ()) id
        (vectorBits xs) i).run (initWords (encodeBits xs)) = (.ok B', s') ∧
      bitValues s' B' = xs.take (i.val.toNat - 1) ++ xs.drop i.val.toNat ∧
      Round5.Round2.PackedInvariant s' B' := by
  obtain ⟨hp, he⟩ := scalar_valid_index_coordinates xs i hn hi
  obtain ⟨B', s', hr, hb, hinv⟩ := deleteCorrectNat xs (i.val.toNat - 1) hp hn
  have hposit : 1 ≤ i.val.toNat := by
    change 1 ≤ i.val ∧ i.val ≤ (int xs.length).val at hi
    omega
  refine ⟨B', s', ?_, ?_, hinv⟩
  · have hpub := congrArg (fun action : BitMutationM BitVector =>
        action.run (initWords (encodeBits xs))) (deletePublicValid (vectorBits xs) i hi)
    have hindex := congrArg (fun j : I64 =>
      (bitVectorDeleteAtInt (vectorBits xs) j).run (initWords (encodeBits xs))) he
    exact hpub.trans (hindex.trans hr)
  · rw [hb]
    simp only [deleteLogical, Nat.sub_add_cancel hposit]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The frozen insertion/deletion observations on abstract execution results. -/
def insertDeleteObservation (xs : List Bool) (i : I64) (s : State)
    (converted : JuliaLean.base.range.JlX Bool)
    (inserted deleted : Id (Except Error BitVector × MutableMemory U64)) : Prop :=
  (int 1 ≤ i ∧ i ≤ int (Int.ofNat (xs.length + 1))) →
    (Round5.Round2.DequeAgrees.match_5 (fun _ => Prop) converted
      (fun _ => Round5.Round2.DequeAgrees.match_1 (fun _ => Prop) inserted.1
        (fun _ => inserted.2 = s) (fun _ => False))
      (fun value => JuliaLean.Proofs.base.bitarray.InsertDeleteAgrees.match_1
        (fun _ => Prop) inserted.1
        (fun B' => bitValues inserted.2 B' =
          xs.take (i.val.toNat - 1) ++ [value] ++ xs.drop (i.val.toNat - 1) ∧
          Round5.Round2.PackedInvariant inserted.2 B')
        (fun _ => False))) ∧
    (if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then
      JuliaLean.Proofs.base.bitarray.InsertDeleteAgrees.match_1 (fun _ => Prop) deleted.1
        (fun B' => bitValues deleted.2 B' =
          xs.take (i.val.toNat - 1) ++ xs.drop i.val.toNat ∧
          Round5.Round2.PackedInvariant deleted.2 B')
        (fun _ => False)
      else True)

theorem insertDeleteFrozenFromObservation (xs : List Bool) (i : I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X) :
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    insertDeleteObservation xs i s (JuliaLean.base.range.JConvert.convert (T := Bool) x)
      ((bitVectorInsert id (bitVectorInsertInt Round5.Round2.convertBoolMutation) B i x).run s)
      ((bitVectorDeleteAt (fun _ : I64 => false) (fun _ => pure ()) id B i).run s) →
      Round5.Round2.InsertDeleteAgrees xs i x := by
  exact fun h => h

/-- Successful and rejected insertions and valid deletions imply the frozen observations. -/
theorem insertDeleteObservationFrom (xs : List Bool) (i : I64) (s : State)
    (converted : JuliaLean.base.range.JlX Bool)
    (inserted deleted : Id (Except Error BitVector × MutableMemory U64))
    (he : (int 1 ≤ i ∧ i ≤ int (Int.ofNat (xs.length + 1))) →
      ∀ e, converted = .error e → ∃ e', inserted = (.error e', s))
    (hv : (int 1 ≤ i ∧ i ≤ int (Int.ofNat (xs.length + 1))) →
      ∀ value, converted = .ok value → ∃ B' s', inserted = (.ok B', s') ∧
        bitValues s' B' = xs.take (i.val.toNat - 1) ++ [value] ++ xs.drop (i.val.toNat - 1) ∧
        Round5.Round2.PackedInvariant s' B')
    (hd : (int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length)) →
      ∃ B' s', deleted = (.ok B', s') ∧
        bitValues s' B' = xs.take (i.val.toNat - 1) ++ xs.drop i.val.toNat ∧
        Round5.Round2.PackedInvariant s' B') :
    insertDeleteObservation xs i s converted inserted deleted := by
  intro hi
  constructor
  · cases hc : converted with
    | error e =>
      obtain ⟨e', hw⟩ := he hi e hc
      simp only [hw]
    | ok value =>
      obtain ⟨B', s', hw, hb, hinv⟩ := hv hi value hc
      simp only [hw]
      exact ⟨hb, hinv⟩
  · by_cases hi' : int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length)
    · obtain ⟨B', s', hw, hb, hinv⟩ := hd hi'
      simp only [hi', ite_true, hw]
      exact ⟨hb, hinv⟩
    · simp only [hi', ite_false]

/-- Scalar insertion and deletion satisfy the exact frozen logical and packed-storage contract. -/
theorem BitarraysInsertDeleteat_proven :
    JuliaLean.Proofs.base.bitarray.Round5.InsertDeleteAgrees := by
  intro xs i X _ x hn
  let B := vectorBits xs
  let s := initWords (encodeBits xs)
  let inserted := (bitVectorInsert id (bitVectorInsertInt Round5.Round2.convertBoolMutation) B i x).run s
  let deleted := (bitVectorDeleteAt (fun _ : I64 => false) (fun _ => pure ()) id B i).run s
  apply insertDeleteFrozenFromObservation xs i x
  change insertDeleteObservation xs i s (JuliaLean.base.range.JConvert.convert (T := Bool) x)
    inserted deleted
  apply insertDeleteObservationFrom xs i s _ inserted deleted
  · intro hi e hc
    refine ⟨Round5.Round2.mutationErrorOfRange e, ?_⟩
    apply insertPublicConvertError B i x e s
    · have hlen : int (Int.ofNat (xs.length + 1)) = B.len + int 1 := by
        have hn' : xs.length < Round5.maxVectorLength := by omega
        exact (dequeLengthSucc xs.length hn').symm
      rw [hlen] at hi
      exact hi
    · exact hc
  · intro hi value hc
    exact insertPublicCorrect xs i x value hn hi hc
  · intro hi
    have hbound : xs.length ≤ 9223372036854775807 := by
      change xs.length + 1 < 4611686018427387903 at hn
      omega
    exact deletePublicCorrect xs i hbound hi
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Factor public range deletion through successful copy and final cleanup actions. -/
theorem rangeSingleDeleteFrom (B result : BitVector) (r : BitRange)
    (newLength oldChunks : I64) (s copied out : State)
    (hf : ¬ r.first < int 1) (hl : ¬ r.last > B.len)
    (hn : B.len - (int 1 + (r.last - r.first)) = newLength)
    (hcount : (mutableLength B.chunks).run s = (.ok oldChunks, s))
    (hcopy : (copyChunks B.chunks r.first B.chunks (r.last + int 1) (B.len - r.last)).run s =
      (.ok (), copied))
    (hfinish : (rangeSingleFinish B newLength oldChunks).run copied = (.ok result, out)) :
    (Round5.Round2.deleteBitRangePublic B r).run s = (.ok result, out) := by
  rw [rangeDelete_public_eq]
  simp only [bitVectorDeleteRange, hf, hl, ite_false, hn, shape_run_bind, hcount, hcopy]
  exact hfinish

/-- The installed public interval length agrees with the natural length of a valid nonempty interval. -/
theorem rangeSingleNewLength (n first last : Nat) (hf : first < last) (hl : last ≤ n) :
    int n - (int 1 + (int last - int ((first + 1 : Nat) : Int))) =
      int ((n - (last - first) : Nat) : Int) := by
  rw [dequeIntSub, packedInt_add, dequeIntSub]
  apply congrArg int
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

/-- The low word after a forward suffix copy within two original chunks. -/
def rangePairLow (xs : List Bool) (first last : Nat) : U64 :=
  if first < 64 then copyPairPaste (packedPrefix xs 0 64) (copyPairSlice xs last)
    first (min (xs.length - last) (64 - first))
  else packedPrefix xs 0 64

/-- The high word after that copy, before the public deletion method clears final padding. -/
def rangePairHigh (xs : List Bool) (first last : Nat) : U64 :=
  if first < 64 then
    if 64 < first + (xs.length - last) then
      copyPairPaste (packedPrefix xs 1 64)
        (copyPairCarry (copyPairSlice xs last) (copyPairSlice xs (last + 64)) first)
        0 (first + (xs.length - last) - 64)
    else packedPrefix xs 1 64
  else copyPairPaste (packedPrefix xs 1 64) (copyPairSlice xs last) (first - 64) (xs.length - last)

/-- The two-chunk intermediate representation produced by the boundary copies. -/
def rangePairWords (xs : List Bool) (first last : Nat) : List U64 :=
  [rangePairLow xs first last, rangePairHigh xs first last]

/-- The low copied word has exact logical source-offset semantics. -/
theorem rangePairLowBit (xs : List Bool) (first last bit : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hn : xs.length ≤ 128) (hb : bit < 64) :
    packedBit (rangePairLow xs first last) bit =
      if first ≤ bit ∧ bit < first + (xs.length - last) then xs.getD (last + (bit - first)) false
      else xs.getD bit false := by
  unfold rangePairLow
  by_cases hs : first < 64
  · rw [if_pos hs, copyPairPasteBit _ _ first _ bit (by omega) hb,
      packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]
    by_cases hi : first ≤ bit ∧ bit < first + (xs.length - last)
    · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs last (bit - first) (by omega)]
    · rw [if_neg hi, if_neg (by omega)]
  · rw [if_neg hs, if_neg (by omega), packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]

/-- The high copied word has exact logical source-offset semantics, including the cross-word carry. -/
theorem rangePairHighBit (xs : List Bool) (first last bit : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hn : xs.length ≤ 128) (hb : bit < 64) :
    packedBit (rangePairHigh xs first last) bit =
      if first ≤ 64 + bit ∧ 64 + bit < first + (xs.length - last) then
        xs.getD (last + (64 + bit - first)) false
      else xs.getD (64 + bit) false := by
  unfold rangePairHigh
  by_cases hs : first < 64
  · rw [if_pos hs]
    by_cases he : 64 < first + (xs.length - last)
    · rw [if_pos he, copyPairPasteBit _ _ 0 _ bit (by omega) hb,
        packedWord_bit xs 1 bit hb]
      simp only [Nat.one_mul, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
      by_cases hi : 64 + bit < first + (xs.length - last)
      · rw [if_pos (by omega), if_pos (by omega)]
        rw [copyPairCarry, copyPairCarrySliceBit xs last first bit (by omega) hb]
        congr 1
        omega
      · rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg he, if_neg (by omega), packedWord_bit xs 1 bit hb]
  · rw [if_neg hs, copyPairPasteBit _ _ (first - 64) _ bit (by omega) hb,
      packedWord_bit xs 1 bit hb]
    simp only [Nat.one_mul]
    by_cases hi : first ≤ 64 + bit ∧ 64 + bit < first + (xs.length - last)
    · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs last (bit - (first - 64)) (by omega)]
      congr 1
      omega
    · rw [if_neg hi, if_neg (by omega)]

/-- An empty suffix copy preserves both original chunks. -/
theorem rangePairWordsEmpty (xs : List Bool) (first : Nat)
    (hf : first ≤ xs.length) (hn : xs.length ≤ 128) :
    rangePairWords xs first xs.length = [packedPrefix xs 0 64, packedPrefix xs 1 64] := by
  have hl : rangePairLow xs first xs.length = packedPrefix xs 0 64 := by
    apply packedBit_ext
    intro bit hb
    rw [rangePairLowBit xs first xs.length bit hf (Nat.le_refl _) hn hb,
      if_neg (by omega), packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]
  have hh : rangePairHigh xs first xs.length = packedPrefix xs 1 64 := by
    apply packedBit_ext
    intro bit hb
    rw [rangePairHighBit xs first xs.length bit hf (Nat.le_refl _) hn hb,
      if_neg (by omega), packedWord_bit xs 1 bit hb]
  simp only [rangePairWords, hl, hh]

/-- If the retained result occupies two chunks, its low copied word is already its final encoding. -/
theorem rangePairLowEncode (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hn : xs.length ≤ 128)
    (hp : 64 < first + (xs.length - last)) :
    rangePairLow xs first last = packedPrefix (xs.take first ++ xs.drop last) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [rangePairLowBit xs first last bit hf hl hn hb,
    packedWord_bit (xs.take first ++ xs.drop last) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [rangeSingleLogicalGet xs first last bit hf hl]
  by_cases hi : bit < first
  · rw [if_pos hi, if_neg (by omega)]
  · rw [if_neg hi, if_pos (by omega)]

/-- Final padding cleanup makes a one-chunk retained result exactly encode the logical deletion. -/
theorem rangePairLowMaskEncode (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hn : xs.length ≤ 128)
    (hp : 0 < first + (xs.length - last)) (he : first + (xs.length - last) ≤ 64) :
    and_int (rangePairLow xs first last) (maskEnd (int ((first + (xs.length - last) : Nat) : Int))) =
      packedPrefix (xs.take first ++ xs.drop last) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [dequePackedAnd, rangePairLowBit xs first last bit hf hl hn hb,
    rangeSingleEndMaskBit _ bit hp he hb, packedWord_bit (xs.take first ++ xs.drop last) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  by_cases hi : bit < first + (xs.length - last)
  · simp only [hi, decide_true, Bool.and_true, and_true]
    rw [rangeSingleLogicalGet xs first last bit hf hl]
    by_cases hj : bit < first
    · rw [if_pos hj, if_neg (by omega)]
    · rw [if_neg hj, if_pos (by omega)]
  · simp only [hi, decide_false, Bool.and_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega

/-- The final end mask for a two-chunk vector selects its remaining high-word logical bits. -/
theorem rangePairEndMaskBit (n bit : Nat) (hp : 64 < n) (hn : n ≤ 128) (hb : bit < 64) :
    packedBit (maskEnd (int n)) bit = decide (64 + bit < n) := by
  have hw : wordCount n = 2 := by unfold wordCount; omega
  have h := packedMask_last_bit n bit (by omega) (by omega)
  simpa only [hw] using h

/-- Final high-word padding cleanup exactly encodes the retained prefix and suffix. -/
theorem rangePairHighMaskEncode (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hn : xs.length ≤ 128)
    (hp : 64 < first + (xs.length - last)) :
    and_int (rangePairHigh xs first last) (maskEnd (int ((first + (xs.length - last) : Nat) : Int))) =
      packedPrefix (xs.take first ++ xs.drop last) 1 64 := by
  apply packedBit_ext
  intro bit hb
  rw [dequePackedAnd, rangePairHighBit xs first last bit hf hl hn hb,
    rangePairEndMaskBit _ bit hp (by omega) hb, packedWord_bit (xs.take first ++ xs.drop last) 1 bit hb]
  simp only [Nat.one_mul]
  by_cases hi : 64 + bit < first + (xs.length - last)
  · simp only [hi, decide_true, Bool.and_true, and_true]
    rw [rangeSingleLogicalGet xs first last (64 + bit) hf hl]
    by_cases hj : 64 + bit < first
    · rw [if_pos hj, if_neg (by omega)]
    · rw [if_neg hj, if_pos (by omega)]
  · simp only [hi, decide_false, Bool.and_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega

/-- Every forward suffix copy within two original chunks has the exact two boundary-word result. -/
theorem rangePairCopyRun (xs : List Bool) (first last spare : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hp : 64 < xs.length) (hn : xs.length ≤ 128) :
    (copyChunks 0 (int ((first + 1 : Nat) : Int)) 0 (int ((last + 1 : Nat) : Int))
      (int ((xs.length - last : Nat) : Int))).run
      (dequeWordStore [packedPrefix xs 0 64, packedPrefix xs 1 64] spare) =
      (.ok (), dequeWordStore (rangePairWords xs first last) spare) := by
  let low := packedPrefix xs 0 64
  let high := packedPrefix xs 1 64
  let count := xs.length - last
  let length := first + count
  let s := dequeWordStore [low, high] spare
  by_cases hz : last = xs.length
  · subst last
    rw [Nat.sub_self, rangePairWordsEmpty xs first hf hn]
    exact rangeSingleCopyEmptyRun 0 _ _ _
  have hc : 0 < count := by dsimp only [count]; omega
  have hlength : length ≤ 128 := by dsimp only [length, count]; omega
  have hsource : last < xs.length := by omega
  have hforward : ¬ (0 = (0 : Nat) ∧ int ((first + 1 : Nat) : Int) > int ((last + 1 : Nat) : Int)) := by
    intro h
    have hv := h.2
    change (int ((last + 1 : Nat) : Int)).val < (int ((first + 1 : Nat) : Int)).val at hv
    rw [packedInt_val (last + 1) (by omega), packedInt_val (first + 1) (by omega)] at hv
    omega
  have hendS : int ((last + 1 : Nat) : Int) + int count - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [count]
    omega
  have hendD : int ((first + 1 : Nat) : Int) + int count - int 1 = int length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [length]
    omega
  have hs0 := copyPairAddress last (by omega)
  have hs1 : getChunksId (int ((last + 1 : Nat) : Int) + int count - int 1) =
      (int 2, int ((xs.length - 65 : Nat) : Int)) := by
    rw [hendS]
    exact copyPairFinalAddress xs.length hp hn
  have hg := copyPairFirstPackedRun xs last 0 s hp hn hsource
    (copyPairReadLow low high spare) (copyPairReadHigh low high spare)
  by_cases hfirst : first < 64
  · have hd0 : getChunksId (int ((first + 1 : Nat) : Int)) = (int 1, int first) :=
      rangeSingleAddress first hfirst
    by_cases hshort : length ≤ 64
    · have hmin : min count (64 - first) = count := Nat.min_eq_left (by dsimp only [length] at hshort; omega)
      have hout : rangePairWords xs first last =
          [copyPairPaste low (copyPairSlice xs last) first count, high] := by
        simp only [rangePairWords, rangePairLow, rangePairHigh, hfirst, ite_true]
        change [copyPairPaste low (copyPairSlice xs last) first (min count (64 - first)),
          if 64 < length then _ else high] = _
        rw [hmin, if_neg (by omega)]
      rw [hout]
      have hd1 : getChunksId (int ((first + 1 : Nat) : Int) + int count - int 1) =
          (int 1, int ((first + count - 1 : Nat) : Int)) := by
        rw [hendD]
        have h := rangeSingleAddress (length - 1) (by omega)
        rw [show length - 1 + 1 = length by dsimp only [length]; omega] at h
        exact h
      exact copyPairOneRun 0 0 _ _ count first (int 1) (copyPairStartChunk last)
        (int ((last % 64 : Nat) : Int)) (int 2) (int ((xs.length - 65 : Nat) : Int)) s _ low _
        hc hshort hforward hd0 hd1 hs0 hs1 hg (copyPairReadLow low high spare)
        (copyPairSetLow low high _ spare)
    · have hlong : 64 < length := by omega
      have hmin : min count (64 - first) = 64 - first := Nat.min_eq_right (by dsimp only [length] at hlong; omega)
      let changed := copyPairPaste low (copyPairSlice xs last) first (64 - first)
      let mid := dequeWordStore [changed, high] spare
      have hout : rangePairWords xs first last =
          [changed, copyPairPaste high
            (copyPairCarry (copyPairSlice xs last) (copyPairSlice xs (last + 64)) first) 0 (length - 64)] := by
        simp only [rangePairWords, rangePairLow, rangePairHigh, hfirst, ite_true]
        change [copyPairPaste low (copyPairSlice xs last) first (min count (64 - first)),
          if 64 < length then _ else high] = _
        rw [hmin, if_pos hlong]
      rw [hout]
      have hd1 : getChunksId (int ((first + 1 : Nat) : Int) + int count - int 1) =
          (int 2, int ((length - 64 - 1 : Nat) : Int)) := by
        rw [hendD]
        simpa only [Nat.sub_sub] using copyPairFinalAddress length hlong hlength
      have hnext := copyPairNextPackedRun xs last 0 mid hp hn hsource (copyPairReadHigh changed high spare)
      exact copyPairTwoRun 0 0 _ _ (int count) first (length - 64)
        (copyPairStartChunk last) (int ((last % 64 : Nat) : Int)) (int 2)
        (int ((xs.length - 65 : Nat) : Int)) s mid _ low high (copyPairSlice xs last)
        (copyPairSlice xs (last + 64)) (by omega) (by omega) (by omega)
        (fillPositiveLength count hc (by dsimp only [count]; omega)) hforward hd0 hd1 hs0 hs1 hg
        (copyPairReadLow low high spare) (copyPairSetLow low high changed spare) hnext
        (copyPairReadHigh changed high spare) (copyPairSetHigh changed high _ spare)
  · have hlong : 64 < length := by dsimp only [length]; omega
    have hsmall : first - 64 + count ≤ 64 := by dsimp only [count]; omega
    have hmod : first % 64 = first - 64 := by omega
    have hd0 : getChunksId (int ((first + 1 : Nat) : Int)) = (int 2, int ((first - 64 : Nat) : Int)) := by
      simpa only [copyPairStartChunk, hfirst, ite_false, hmod] using copyPairAddress first (by omega)
    have hd1 : getChunksId (int ((first + 1 : Nat) : Int) + int count - int 1) =
        (int 2, int ((first - 64 + count - 1 : Nat) : Int)) := by
      rw [hendD, copyPairFinalAddress length hlong hlength]
      congr 2
      dsimp only [length]
      omega
    have hout : rangePairWords xs first last =
        [low, copyPairPaste high (copyPairSlice xs last) (first - 64) count] := by
      simp only [rangePairWords, rangePairLow, rangePairHigh, hfirst, ite_false]
      rfl
    rw [hout]
    exact copyPairOneRun 0 0 _ _ count (first - 64) (int 2) (copyPairStartChunk last)
      (int ((last % 64 : Nat) : Int)) (int 2) (int ((xs.length - 65 : Nat) : Int)) s _ high _
      hc hsmall hforward hd0 hd1 hs0 hs1 hg (copyPairReadHigh low high spare)
      (copyPairSetHigh low high _ spare)

/-- Removing both original chunks is the entire cleanup for an empty result. -/
theorem rangePairFinishZero (B : BitArray 1) (s out : State)
    (hd : (deleteChunkEnd B.chunks (int 2)).run s = (.ok (), out)) :
    (rangeSingleFinish B (int 0) (int 2)).run s = (.ok {B with len := int 0}, out) := by
  simp only [rangeSingleFinish, show numBitChunks (int 0) = int 0 from rfl,
    show int 0 - int 2 < int 0 from by decide, ite_true,
    show -(int 0 - int 2) = int 2 from rfl, shape_run_bind, hd,
    show ¬ int 0 > int 0 from by decide, ite_false, shape_run_pure]

/-- A one-word retained result deletes the original high chunk before masking the low word. -/
theorem rangePairFinishOne (B : BitArray 1) (n : Nat) (word : U64) (s trimmed out : State)
    (hp : 0 < n) (hn : n ≤ 64)
    (hd : (deleteChunkEnd B.chunks (int 1)).run s = (.ok (), trimmed))
    (hl : (mutableLength B.chunks).run trimmed = (.ok (int 1), trimmed))
    (hr : (mutableGet B.chunks (int 1)).run trimmed = (.ok word, trimmed))
    (hw : (mutableSet B.chunks (and_int word (maskEnd (int n))) (int 1)).run trimmed = (.ok (), out)) :
    (rangeSingleFinish B (int n) (int 2)).run s = (.ok {B with len := int n}, out) := by
  have hp' : int n > int 0 := by
    change 0 < (int n).val
    rw [packedInt_val n (by omega)]
    omega
  simp only [rangeSingleFinish, rangeSingleChunkCount n hp hn,
    show int 1 - int 2 < int 0 from by decide, ite_true,
    show -(int 1 - int 2) = int 1 from rfl, shape_run_bind, hd,
    hp', ite_true, hl, hr, hw, shape_run_pure]

/-- A two-word retained result only masks the final copied high word. -/
theorem rangePairFinishTwo (B : BitArray 1) (n : Nat) (word : U64) (s out : State)
    (hp : 64 < n) (hn : n ≤ 128)
    (hl : (mutableLength B.chunks).run s = (.ok (int 2), s))
    (hr : (mutableGet B.chunks (int 2)).run s = (.ok word, s))
    (hw : (mutableSet B.chunks (and_int word (maskEnd (int n))) (int 2)).run s = (.ok (), out)) :
    (rangeSingleFinish B (int n) (int 2)).run s = (.ok {B with len := int n}, out) := by
  have hp' : int n > int 0 := by
    change 0 < (int n).val
    rw [packedInt_val n (by omega)]
    omega
  simp only [rangeSingleFinish, rangePairChunkCount n hp hn,
    show ¬ int 2 - int 2 < int 0 from by decide, ite_false,
    hp', ite_true, shape_run_bind, hl, hr, hw, shape_run_pure]

/-- A one-word copy onto the same interval leaves every packed bit unchanged. -/
theorem rangeEmptySingleCopyWord (word : U64) (start count : Nat)
    (hn : start + count ≤ 64) :
    rangeSingleCopyWord word start start count = word := by
  apply packedBit_ext
  intro bit hb
  rw [rangeSingleCopyBit word start start count bit hn hn hb]
  by_cases hi : start ≤ bit ∧ bit < start + count
  · rw [if_pos hi, show bit - start + start = bit by omega]
  · rw [if_neg hi]

/-- A two-word suffix copy onto its original positions leaves both words unchanged. -/
theorem rangeEmptyPairWords (xs : List Bool) (start : Nat)
    (hs : start ≤ xs.length) (hn : xs.length ≤ 128) :
    rangePairWords xs start start = [packedPrefix xs 0 64, packedPrefix xs 1 64] := by
  have hlo : rangePairLow xs start start = packedPrefix xs 0 64 := by
    apply packedBit_ext
    intro bit hb
    rw [rangePairLowBit xs start start bit (Nat.le_refl _) hs hn hb,
      packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]
    by_cases hi : start ≤ bit ∧ bit < start + (xs.length - start)
    · rw [if_pos hi, show start + (bit - start) = bit by omega]
    · rw [if_neg hi]
  have hhi : rangePairHigh xs start start = packedPrefix xs 1 64 := by
    apply packedBit_ext
    intro bit hb
    rw [rangePairHighBit xs start start bit (Nat.le_refl _) hs hn hb,
      packedWord_bit xs 1 bit hb]
    simp only [Nat.one_mul]
    by_cases hi : start ≤ 64 + bit ∧ 64 + bit < start + (xs.length - start)
    · rw [if_pos hi, show start + (64 + bit - start) = 64 + bit by omega]
    · rw [if_neg hi]
  simp only [rangePairWords, hlo, hhi]

/-- Self-copy of any suffix in at most two initialized chunks preserves the exact state. -/
theorem rangeEmptyCopyRun (xs : List Bool) (start spare : Nat)
    (hs : start ≤ xs.length) (hn : xs.length ≤ 128) :
    (copyChunks 0 (int ((start + 1 : Nat) : Int)) 0 (int ((start + 1 : Nat) : Int))
      (int ((xs.length - start : Nat) : Int))).run (dequeWordStore (encodeBits xs) spare) =
        (.ok (), dequeWordStore (encodeBits xs) spare) := by
  by_cases hz : xs.length = 0
  · have hs0 : start = 0 := by omega
    rw [hz, hs0, Nat.sub_zero]
    exact rangeSingleCopyEmptyRun 0 _ _ _
  by_cases hsmall : xs.length ≤ 64
  · rw [rangeSingleEncoding xs (by omega) hsmall]
    have hr := rangeSingleCopyStore (packedPrefix xs 0 64) start start (xs.length - start)
      spare (Nat.le_refl _) (by omega)
    rw [rangeEmptySingleCopyWord _ start (xs.length - start) (by omega)] at hr
    exact hr
  · rw [copyPairEncoding xs (by omega) hn]
    exact (rangePairCopyRun xs start start spare (Nat.le_refl _) hs (by omega) hn).trans (by
      rw [rangeEmptyPairWords xs start hs hn])

/-- If final-word cleanup is state preserving, the unchanged-length deletion finish is state preserving. -/
theorem rangeEmptyFinishFrom (B : BitArray 1) (s : State)
    (ht : (resizeMaskTail B.chunks B.len).run s = (.ok (), s)) :
    (rangeSingleFinish B B.len (numBitChunks B.len)).run s = (.ok B, s) := by
  have he : rangeSingleFinish B B.len (numBitChunks B.len) =
      (resizeMaskTail B.chunks B.len >>= fun _ => pure B) := by
    simp only [rangeSingleFinish, shape_int_sub_self, show ¬ int 0 < int 0 from by decide,
      ite_false, resizeMaskTail]
    split <;> simp only [pure_bind, bind_assoc]
  rw [he, shape_run_bind, ht]
  rfl

/-- Cleanup at the original logical length preserves canonical packed storage at every native length. -/
theorem rangeEmptyFinishRun (xs : List Bool) (spare : Nat)
    (hn : xs.length ≤ 9223372036854775807) :
    (rangeSingleFinish (vectorBits xs) (int xs.length) (numBitChunks (int xs.length))).run
      (dequeWordStore (encodeBits xs) spare) =
        (.ok (vectorBits xs), dequeWordStore (encodeBits xs) spare) := by
  have ht : (resizeMaskTail 0 (int xs.length)).run (dequeWordStore (encodeBits xs) spare) =
      (.ok (), dequeWordStore (encodeBits xs) spare) := by
    by_cases hp : 0 < xs.length
    · have hr := resizeMaskPrefixRun xs xs.length spare hp (Nat.le_refl _) hn
      have htake : (encodeBits xs).take (wordCount xs.length) = encodeBits xs := by
        rw [← packedEncoded_length xs, List.take_length]
      simpa only [htake, List.take_length] using hr
    · have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      rfl
  exact rangeEmptyFinishFrom (vectorBits xs) (dequeWordStore (encodeBits xs) spare) ht

/-- Every canonical empty interval p+1:p inside a vector of at most two chunks is an exact no-op. -/
theorem rangeEmptyInsideRun (xs : List Bool) (p : Nat)
    (hp : p ≤ xs.length) (hn : xs.length ≤ 128) :
    (Round5.Round2.deleteBitRangePublic (vectorBits xs)
      ⟨int ((p + 1 : Nat) : Int), int p⟩).run (initWords (encodeBits xs)) =
        (.ok (vectorBits xs), initWords (encodeBits xs)) := by
  rw [← dequeWordStoreInitial]
  let count := numBitChunks (int xs.length)
  have hsource : int p + int 1 = int ((p + 1 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  have hcount : int xs.length - int p = int ((xs.length - p : Nat) : Int) := by
    rw [dequeIntSub]
    apply congrArg int
    omega
  have hlength : (mutableLength (vectorBits xs).chunks).run
      (dequeWordStore (encodeBits xs) 32) =
        (.ok count, dequeWordStore (encodeBits xs) 32) := by
    rw [show count = int (wordCount xs.length : Int) from resizeNumChunks xs.length (by omega)]
    have h := dequeWordLength (encodeBits xs) 32
    rw [packedEncoded_length] at h
    exact h
  apply rangeSingleDeleteFrom (vectorBits xs) (vectorBits xs)
    ⟨int ((p + 1 : Nat) : Int), int p⟩ (int xs.length) count
    (dequeWordStore (encodeBits xs) 32) (dequeWordStore (encodeBits xs) 32)
    (dequeWordStore (encodeBits xs) 32)
  · change ¬ (int ((p + 1 : Nat) : Int)).val < 1
    rw [packedInt_val (p + 1) (by omega)]
    omega
  · change ¬ (int xs.length).val < (int p).val
    rw [packedInt_val xs.length (by omega), packedInt_val p (by omega)]
    omega
  · change int xs.length - (int 1 + (int p - int ((p + 1 : Nat) : Int))) = int xs.length
    simp only [packedInt_add, dequeIntSub]
    exact congrArg int (by omega)
  · exact hlength
  · change (copyChunks 0 (int ((p + 1 : Nat) : Int)) 0 (int p + int 1)
      (int xs.length - int p)).run _ = _
    rw [hsource, hcount]
    exact rangeEmptyCopyRun xs p 32 hp hn
  · exact rangeEmptyFinishRun xs 32 (by omega)

/-- Native canonical empty endpoints satisfy the frozen empty-range assertion through two chunks. -/
theorem BitarraysDeleteatCanonicalEmpty_twoChunks (xs : List Bool) (p : Nat)
    (hp : p ≤ xs.length) (hn : xs.length ≤ 128) :
    Round5.Round2.DeleteatRangeAgrees xs (int ((p + 1 : Nat) : Int)) (int p) := by
  have horder : int ((p + 1 : Nat) : Int) > int p := by
    change (int p).val < (int ((p + 1 : Nat) : Int)).val
    rw [packedInt_val p (by omega), packedInt_val (p + 1) (by omega)]
    omega
  unfold Round5.Round2.DeleteatRangeAgrees
  dsimp only
  rw [if_pos horder, rangeEmptyInsideRun xs p hp hn]
  exact ⟨rfl, rfl⟩
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

/-- Logical storage after a prefix copy, before trimming the old trailing positions. -/
def prefixDeleteBits (xs : List Bool) (count : Nat) : List Bool :=
  xs.drop count ++ xs.drop (xs.length - count)

theorem prefixDeleteLength (xs : List Bool) (count : Nat) :
    (prefixDeleteBits xs count).length = xs.length := by
  simp only [prefixDeleteBits, List.length_append, List.length_drop]
  omega

theorem prefixDeleteTake (xs : List Bool) (count : Nat) :
    (prefixDeleteBits xs count).take (xs.length - count) = xs.drop count := by
  unfold prefixDeleteBits
  have hl : xs.length - count = (xs.drop count).length := by rw [List.length_drop]
  rw [hl]
  exact List.take_left

/-- The copied prefix reads the source suffix, and all later positions keep their old bits. -/
theorem prefixDeleteGet (xs : List Bool) (count bit : Nat) :
    (prefixDeleteBits xs count).getD bit false =
      if bit < xs.length - count then xs.getD (count + bit) false else xs.getD bit false := by
  unfold prefixDeleteBits
  by_cases hb : bit < xs.length - count
  · rw [if_pos hb, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp only [List.length_drop]; exact hb), List.getElem?_drop]
    rfl
  · rw [if_neg hb, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp only [List.length_drop]; omega), List.length_drop,
      List.getElem?_drop]
    have he : xs.length - count + (bit - (xs.length - count)) = bit := by omega
    rw [he]
    rfl

theorem prefixDeleteLowWord (xs : List Bool) (count : Nat)
    (hk : xs.length - count ≤ 64) :
    copyPairPaste (packedPrefix xs 0 64) (copyPairSlice xs count) 0 (xs.length - count) =
      packedPrefix (prefixDeleteBits xs count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb, packedWord_bit (prefixDeleteBits xs count) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  rw [prefixDeleteGet]
  by_cases hi : bit < xs.length - count
  · rw [if_pos hi, if_pos hi, copyPairSliceBit xs count bit hb]
  · rw [if_neg hi, if_neg hi, packedWord_bit xs 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add]

theorem prefixDeleteFullLowWord (xs : List Bool) (count : Nat)
    (hp : 64 ≤ xs.length - count) :
    copyPairSlice xs count = packedPrefix (prefixDeleteBits xs count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairSliceBit xs count bit hb, packedWord_bit (prefixDeleteBits xs count) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [prefixDeleteGet, if_pos (by omega)]

theorem prefixDeleteHighWord (xs : List Bool) (count : Nat)
    (hp : 64 ≤ xs.length - count) (hk : xs.length - count ≤ 128) :
    copyPairPaste (packedPrefix xs 1 64) (copyPairSlice xs (count + 64)) 0
      (xs.length - count - 64) = packedPrefix (prefixDeleteBits xs count) 1 64 := by
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb, packedWord_bit (prefixDeleteBits xs count) 1 bit hb]
  simp only [Nat.one_mul, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  rw [prefixDeleteGet]
  by_cases hi : 64 + bit < xs.length - count
  · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs (count + 64) bit hb]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedWord_bit xs 1 bit hb]

theorem prefixDeleteUnchangedWord (xs : List Bool) (count chunk : Nat)
    (hk : xs.length - count ≤ chunk * 64) :
    packedPrefix xs chunk 64 = packedPrefix (prefixDeleteBits xs count) chunk 64 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit xs chunk bit hb, packedWord_bit _ chunk bit hb, prefixDeleteGet,
    if_neg (by omega)]

/-- One in-place boundary write gives exactly the pre-trimming logical prefix-copy storage. -/
theorem prefixDeleteOneEncoding (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 64) :
    (encodeBits xs).set 0
      (copyPairPaste (packedPrefix xs 0 64) (copyPairSlice xs count) 0 (xs.length - count)) =
      encodeBits (prefixDeleteBits xs count) := by
  have hw : 0 < wordCount xs.length := by unfold wordCount; omega
  apply List.ext_getElem
  · simp only [List.length_set, packedEncoded_length, prefixDeleteLength]
  · intro chunk hj hj'
    have hb : chunk < wordCount xs.length := by simpa only [List.length_set, packedEncoded_length] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ 0 chunk _ (by rw [packedEncoded_length]; exact hw),
      shiftNearLeftEncodedGet (prefixDeleteBits xs count) chunk (by rw [prefixDeleteLength]; exact hb)]
    by_cases hz : chunk = 0
    · subst chunk
      rw [if_pos rfl]
      exact prefixDeleteLowWord xs count hk
    · rw [if_neg (by omega), shiftNearLeftEncodedGet xs chunk hb]
      exact prefixDeleteUnchangedWord xs count chunk (by omega)

/-- Two in-place boundary writes give the exact prefix-copy storage for up to 128 retained bits. -/
theorem prefixDeleteTwoEncoding (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hp : 64 < xs.length - count) (hk : xs.length - count ≤ 128) :
    ((encodeBits xs).set 0 (copyPairSlice xs count)).set 1
      (copyPairPaste (packedPrefix xs 1 64) (copyPairSlice xs (count + 64)) 0
        (xs.length - count - 64)) = encodeBits (prefixDeleteBits xs count) := by
  have hw : 1 < wordCount xs.length := by unfold wordCount; omega
  apply List.ext_getElem
  · simp only [List.length_set, packedEncoded_length, prefixDeleteLength]
  · intro chunk hj hj'
    have hb : chunk < wordCount xs.length := by simpa only [List.length_set, packedEncoded_length] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ 1 chunk _ (by simp only [List.length_set, packedEncoded_length]; exact hw),
      shiftNearLeftEncodedGet (prefixDeleteBits xs count) chunk (by rw [prefixDeleteLength]; exact hb)]
    by_cases h1 : chunk = 1
    · subst chunk
      rw [if_pos rfl]
      exact prefixDeleteHighWord xs count (by omega) hk
    · rw [if_neg (by omega), dequeWordGetSet _ 0 chunk _ (by rw [packedEncoded_length]; omega)]
      by_cases hz : chunk = 0
      · subst chunk
        rw [if_pos rfl]
        exact prefixDeleteFullLowWord xs count (by omega)
      · rw [if_neg (by omega), shiftNearLeftEncodedGet xs chunk hb]
        exact prefixDeleteUnchangedWord xs count chunk (by omega)
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

/-- Range cleanup factors through its optional packed suffix removal and its final mask. -/
theorem prefixDeleteFinishFrom (B : BitArray 1) (n nc : I64) (s trimmed out : State)
    (hd : ((if numBitChunks n - nc < int 0 then
      deleteChunkEnd B.chunks (-(numBitChunks n - nc)) else pure ()) : BitMutationM Unit).run s = (.ok (), trimmed))
    (ht : (resizeMaskTail B.chunks n).run trimmed = (.ok (), out)) :
    (rangeSingleFinish B n nc).run s = (.ok {B with len := n}, out) := by
  have he : rangeSingleFinish B n nc =
      ((if numBitChunks n - nc < int 0 then
        deleteChunkEnd B.chunks (-(numBitChunks n - nc)) else pure ()) >>= fun _ =>
        resizeMaskTail B.chunks n >>= fun _ => pure {B with len := n}) := by
    by_cases hdel : numBitChunks n - nc < int 0 <;> by_cases hpos : n > int 0 <;>
      simp only [rangeSingleFinish, resizeMaskTail, hdel, hpos, ite_true, ite_false,
        bind_assoc, pure_bind]
  rw [he, shape_run_bind, hd]
  simp only [shape_run_bind, ht, shape_run_pure]

/-- The in-place copy phase produces the exact logical intermediate list. -/
theorem prefixDeleteWordsEncode (xs : List Bool) (count : Nat)
    (hc : count < xs.length) (hk : xs.length - count ≤ 128) :
    prefixDeleteWords xs count = encodeBits (prefixDeleteBits xs count) := by
  by_cases hs : xs.length - count ≤ 64
  · rw [prefixDeleteWords, if_pos hs]
    exact prefixDeleteOneEncoding xs count hc hs
  · rw [prefixDeleteWords, if_neg hs]
    exact prefixDeleteTwoEncoding xs count hc (by omega) hk
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

/-- Trimming the copied buffer exposes exactly the retained prefix and original suffix. -/
theorem rangeBoundaryTake (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) :
    (rangeBoundaryBits xs first last).take (first + (xs.length - last)) = xs.take first ++ xs.drop last := by
  have hlen : (xs.take first ++ xs.drop last).length = first + (xs.length - last) := by
    simp only [List.length_append, List.length_take, List.length_drop, Nat.min_eq_left (show first ≤ xs.length by omega)]
  unfold rangeBoundaryBits
  rw [← hlen]
  exact List.take_left
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

/-- A canonical successful interval deletion has the precise logical values and invariant. -/
theorem boundaryDeleteObserve (xs : List Bool) (first last : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hf : first ≤ last) (hl : last ≤ xs.length)
    (hr : (Round5.Round2.deleteBitRangePublic (vectorBits xs)
      ⟨int ((first + 1 : Nat) : Int), int last⟩).run (initWords (encodeBits xs)) =
      (.ok {vectorBits xs with len := int ((first + (xs.length - last) : Nat) : Int)},
        dequeWordStore (encodeBits (xs.take first ++ xs.drop last))
          (32 + (wordCount xs.length - wordCount (first + (xs.length - last)))))) :
    ∃ B' out,
      (Round5.Round2.deleteBitRangePublic (vectorBits xs)
        ⟨int ((first + 1 : Nat) : Int), int last⟩).run (initWords (encodeBits xs)) = (.ok B', out) ∧
      B'.len = int ((first + (xs.length - last) : Nat) : Int) ∧
      bitValues out B' = xs.take first ++ xs.drop last ∧ Round5.Round2.PackedInvariant out B' := by
  let ys := xs.take first ++ xs.drop last
  let n := first + (xs.length - last)
  let B' : BitArray 1 := {vectorBits xs with len := int n}
  let out := dequeWordStore (encodeBits ys) (32 + (wordCount xs.length - wordCount n))
  have hlen : ys.length = n := by
    simp only [ys, List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left (show first ≤ xs.length by omega)]
    rfl
  have hb : ys.length ≤ 9223372036854775807 := by rw [hlen]; dsimp only [n]; omega
  have hnew : B'.len = int ys.length := by change int n = _; rw [hlen]
  have hm : out.contents B'.chunks = (encodeBits ys).map some :=
    dequeWordContents _ _ (packedEncoded_lengthBound _ hb)
  exact ⟨B', out, hr, rfl, scalar_bitValues_contents out B' ys hb hnew hm,
    scalar_invariant_of_contents out B' ys hb hnew hm⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The frozen mask callback enumerates selected zero-based positions in source order. -/
def ctor_mask_selected (mask : List Bool) : List Nat :=
  (List.range mask.length).filter (fun j => mask.getD j false)

/-- Selection membership records both its valid source index and true mask bit. -/
theorem ctor_mask_selected_mem (mask : List Bool) (j : Nat) :
    j ∈ ctor_mask_selected mask ↔ j < mask.length ∧ mask.getD j false = true := by
  simp only [ctor_mask_selected, List.mem_filter, List.mem_range]

/-- Filtering the ordered source range preserves strict order and excludes duplicates. -/
theorem ctor_mask_selected_pairwise (mask : List Bool) :
    (ctor_mask_selected mask).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

/-- Every selected position lies below sixty-four in the single-chunk domain. -/
theorem ctor_mask_selected_bound (mask : List Bool) (hn : mask.length ≤ 64) :
    ∀ j ∈ ctor_mask_selected mask, j < 64 := by
  intro j hj
  have hi := (ctor_mask_selected_mem mask j).mp hj
  omega

/-- The native one-based callback threshold is the strict successor relation on zero-based positions. -/
theorem ctor_mask_native_after (i j : Nat) (hi : i < 64) (hj : j < 64) :
    (int ((j + 1 : Nat) : Int) ≥ int ((i + 2 : Nat) : Int)) ↔ i < j := by
  change (int ((i + 2 : Nat) : Int)).val ≤ (int ((j + 1 : Nat) : Int)).val ↔ _
  rw [packedInt_val (i + 2) (by omega), packedInt_val (j + 1) (by omega)]
  omega

/-- In a strictly ordered list, filtering past an existing position leaves precisely its suffix. -/
theorem ctor_mask_ordered_after (selected before after : List Nat) (i : Nat)
    (hordered : selected.Pairwise (· < ·)) (hdecomp : selected = before ++ i :: after) :
    selected.filter (fun j => i < j) = after := by
  rw [hdecomp] at hordered ⊢
  have hp := List.pairwise_append.mp hordered
  have hbefore : before.filter (fun j => i < j) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj
    simp only [decide_eq_true_eq]
    have hji := hp.2.2 j hj i List.mem_cons_self
    omega
  have hafter : after.filter (fun j => i < j) = after := by
    apply List.filter_eq_self.mpr
    intro j hj
    exact decide_eq_true ((List.pairwise_cons.mp hp.2.1).1 j hj)
  simp only [List.filter_append, List.filter_cons, Nat.lt_irrefl, decide_false,
    Bool.false_eq_true, ite_false, hbefore, hafter, List.nil_append]

/-- The exact frozen next-mask search removes the prefix through the just-processed selection. -/
theorem ctor_mask_filter_after (selected before after : List Nat) (i : Nat)
    (hordered : selected.Pairwise (· < ·))
    (hbound : ∀ j ∈ selected, j < 64)
    (hdecomp : selected = before ++ i :: after) :
    selected.filter (fun j => int ((j + 1 : Nat) : Int) ≥ int ((i + 2 : Nat) : Int)) = after := by
  have hi : i < 64 := hbound i (by
    rw [hdecomp]
    exact List.mem_append_right _ List.mem_cons_self)
  have he : selected.filter (fun j => int ((j + 1 : Nat) : Int) ≥ int ((i + 2 : Nat) : Int)) =
      selected.filter (fun j => i < j) := by
    apply List.filter_congr
    intro j hj
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact ctor_mask_native_after i j hi (hbound j hj)
  exact he.trans (ctor_mask_ordered_after selected before after i hordered hdecomp)

/-- The next optional one-based index is the mapped head of that remaining suffix. -/
theorem ctor_mask_next_head (selected before after : List Nat) (i : Nat)
    (hordered : selected.Pairwise (· < ·))
    (hbound : ∀ j ∈ selected, j < 64)
    (hdecomp : selected = before ++ i :: after) :
    ((selected.filter (fun j => int ((j + 1 : Nat) : Int) ≥
      int ((i + 2 : Nat) : Int))).head?).map (fun j => int ((j + 1 : Nat) : Int)) =
        after.head?.map (fun j => int ((j + 1 : Nat) : Int)) := by
  rw [ctor_mask_filter_after selected before after i hordered hbound hdecomp]

/-- The frozen pure next-mask callback preserves the heap and returns exactly the remaining head. -/
theorem ctor_mask_next_run (selected before after : List Nat) (i : Nat) (s : State)
    (hordered : selected.Pairwise (· < ·))
    (hbound : ∀ j ∈ selected, j < 64)
    (hdecomp : selected = before ++ i :: after) :
    (pure (((selected.filter (fun j => int ((j + 1 : Nat) : Int) ≥
      int ((i + 2 : Nat) : Int))).head?).map (fun j => int ((j + 1 : Nat) : Int))) :
      BitMutationM (Option I64)).run s =
        (.ok (after.head?.map (fun j => int ((j + 1 : Nat) : Int))), s) := by
  rw [ctor_mask_next_head selected before after i hordered hbound hdecomp]
  rfl

/-- The original first-mask callback returns the first selected one-based position. -/
theorem ctor_mask_first_run (i : Nat) (after : List Nat) (s : State) :
    (pure (((i :: after).head?).map (fun j => int ((j + 1 : Nat) : Int))) :
      BitMutationM (Option I64)).run s = (.ok (some (int ((i + 1 : Nat) : Int))), s) := rfl

/-- The raw selection expression used by the frozen mask target satisfies the exact suffix law. -/
theorem ctor_mask_selected_after (mask : List Bool) (before after : List Nat) (i : Nat)
    (hn : mask.length ≤ 64)
    (hdecomp : ctor_mask_selected mask = before ++ i :: after) :
    ((List.range mask.length).filter (fun j => mask.getD j false)).filter
      (fun j => int ((j + 1 : Nat) : Int) ≥ int ((i + 2 : Nat) : Int)) = after :=
  ctor_mask_filter_after (ctor_mask_selected mask) before after i
    (ctor_mask_selected_pairwise mask) (ctor_mask_selected_bound mask hn) hdecomp

/-- The first mapped iterator item carries the original zero-based iterator state. -/
theorem ctor_mask_iterator_first (i : Nat) (after : List Nat) :
    Option.map (fun value : I64 => (value, (0 : Nat)))
      (((i :: after).map (fun j => int ((j + 1 : Nat) : Int))).head?) =
        some (int ((i + 1 : Nat) : Int), (0 : Nat)) := rfl
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

/-- The exact Boolean-mask deletion loop body, with its five registers exposed. -/
def scan_maskDelete_step (chunks : Nat) (next : I64 → BitMutationM (Option I64))
    (_ : Unit) (registers : scan_maskDelete_Registers) :
    BitMutationM (ForInStep scan_maskDelete_Registers) := do
  let newL := registers.1
  let y := registers.2.1
  let p := registers.2.2.1
  let s := registers.2.2.2.1
  let q := registers.2.2.2.2
  if y.isSome then
    let i := y.get!
    let s := i + int 1
    let newL := newL - int 1
    let p ← if i > q then do
        copyChunks chunks p chunks q (i - q)
        pure (p + i - q)
      else pure p
    let q := i + int 1
    let y ← next s
    pure (.yield (newL, y, p, s, q))
  else pure (.done (newL, y, p, s, q))

def scan_maskDelete_after (B : BitVector) (next : I64 → BitMutationM (Option I64))
    (registers : scan_maskDelete_Registers) : BitMutationM BitVector := do
  let result ← forIn ({} : Lean.Loop) registers (scan_maskDelete_step B.chunks next)
  scan_maskDelete_finish B result

/-- One abstract deletion iteration composes its optional interval copy and search. -/
theorem scan_maskDelete_step_from (chunks : Nat) (next : I64 → BitMutationM (Option I64))
    (newL p s q i : I64) (found : Option I64) (state copied : State)
    (hc : ((if i > q then copyChunks chunks p chunks q (i - q)
      else pure ()) : BitMutationM Unit).run state = (.ok (), copied))
    (hn : (next (i + int 1)).run copied = (.ok found, copied)) :
    (scan_maskDelete_step chunks next () (newL, some i, p, s, q)).run state =
      (.ok (.yield (newL - int 1, found, if i > q then p + i - q else p,
        i + int 1, i + int 1)), copied) := by
  by_cases hi : i > q
  · simp only [hi, ite_true] at hc ⊢
    simp only [scan_maskDelete_step, Option.isSome_some, ite_true, Option.get!_some,
      hi, shape_run_bind, hc, shape_run_pure, hn]
  · simp only [hi, ite_false, shape_run_pure] at hc ⊢
    have he : state = copied := congrArg Prod.snd hc
    rw [he]
    simp only [scan_maskDelete_step, Option.isSome_some, ite_true, Option.get!_some,
      hi, ite_false, shape_run_bind, shape_run_pure, hn]

/-- A completed yielding iteration composes directly with a loop's final continuation. -/
theorem scan_maskDelete_after_yield (B : BitVector) (next : I64 → BitMutationM (Option I64))
    (before after : scan_maskDelete_Registers) (state middle final : State) (output : BitVector)
    (hstep : (scan_maskDelete_step B.chunks next () before).run state = (.ok (.yield after), middle))
    (hrest : (scan_maskDelete_after B next after).run middle = (.ok output, final)) :
    (scan_maskDelete_after B next before).run state = (.ok output, final) := by
  unfold scan_maskDelete_after at *
  rw [resizeFrontLoopUnfold]
  simp only [bind_assoc, shape_run_bind, hstep]
  simpa only [shape_run_bind] using hrest

/-- A terminal loop iteration leaves only the final suffix-copy continuation. -/
theorem scan_maskDelete_after_done (B : BitVector) (next : I64 → BitMutationM (Option I64))
    (newL p s q : I64) (state final : State) (output : BitVector)
    (hfinish : (scan_maskDelete_finish B (newL, none, p, s, q)).run state = (.ok output, final)) :
    (scan_maskDelete_after B next (newL, none, p, s, q)).run state = (.ok output, final) := by
  have hloop := reverseLoopDone (scan_maskDelete_step B.chunks next)
    (newL, none, p, s, q) (newL, none, p, s, q) state state (by
      simp only [scan_maskDelete_step, Option.isSome_none, Bool.false_eq_true, ite_false,
        shape_run_pure])
  exact concat_bind_success _ _ state state final (newL, none, p, s, q) output hloop hfinish

/-- Arbitrarily many selected positions in one word are compacted in order. The
invariant relates the written prefix, untouched source suffix, and deleted count. -/
theorem scan_maskDelete_after_complete (xs kept : List Bool) (word : U64)
    (positions : List Nat) (start deleted spare : Nat)
    (next : I64 → BitMutationM (Option I64))
    (hn : xs.length ≤ 64) (hs : start ≤ xs.length)
    (hbalance : kept.length + deleted = start)
    (hordered : positions.Pairwise (· < ·))
    (hbound : ∀ i ∈ positions, start ≤ i ∧ i < xs.length)
    (hprefix : scan_maskDelete_prefix word kept)
    (hsuffix : scan_maskDelete_suffix word xs start)
    (hsearch : ∀ before i after, positions = before ++ i :: after → ∀ state : State,
      (next (int ((i + 2 : Nat) : Int))).run state =
        (.ok (after.head?.map (fun j => int ((j + 1 : Nat) : Int))), state)) :
    ∃ outState : State,
      (scan_maskDelete_after (vectorBits xs) next
        (int ((xs.length - deleted : Nat) : Int),
          positions.head?.map (fun j => int ((j + 1 : Nat) : Int)),
          int ((kept.length + 1 : Nat) : Int), int ((start + 1 : Nat) : Int),
          int ((start + 1 : Nat) : Int))).run (dequeWordStore [word] spare) =
        (.ok {vectorBits xs with len := int ((xs.length - deleted - positions.length : Nat) : Int)}, outState) ∧
      bitValues outState
        ({vectorBits xs with len := int ((xs.length - deleted - positions.length : Nat) : Int)} : BitVector) =
        kept ++ scan_maskDelete_blocks xs positions start := by
  cases positions with
  | nil =>
    obtain ⟨out, hclean, hbits⟩ := scan_maskDelete_cleanup_after_tail xs kept word
      start deleted spare hn hs hbalance hprefix hsuffix
    have hcopy := scan_maskDelete_tail_copy xs.length kept.length start spare word hn (by omega) hs
    have hlength := dequeWordLength
      [rangeSingleCopyWord word kept.length start (xs.length - start)] spare
    have hfinish := scan_maskDelete_finish_from (vectorBits xs)
      {vectorBits xs with len := int ((xs.length - deleted : Nat) : Int)}
      (int ((xs.length - deleted : Nat) : Int)) (int ((kept.length + 1 : Nat) : Int))
      (int ((start + 1 : Nat) : Int)) (int ((start + 1 : Nat) : Int)) none (int 1)
      _ _ out hcopy hlength hclean
    refine ⟨out, ?_, hbits⟩
    exact scan_maskDelete_after_done (vectorBits xs) next
      (int ((xs.length - deleted : Nat) : Int)) (int ((kept.length + 1 : Nat) : Int))
      (int ((start + 1 : Nat) : Int)) (int ((start + 1 : Nat) : Int)) _ out _ hfinish
  | cons i rest =>
    have hi := hbound i List.mem_cons_self
    have htail := List.pairwise_cons.mp hordered
    let retained := kept ++ (xs.drop start).take (i - start)
    let copiedWord := rangeSingleCopyWord word kept.length start (i - start)
    have hretained : retained.length = kept.length + (i - start) := by
      simp only [retained, List.length_append, List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega)]
    have hinvariants := scan_maskDelete_copy_invariant xs kept word start i hn
      (by omega) hi.1 (by omega) hprefix hsuffix
    have hnewbalance : retained.length + (deleted + 1) = i + 1 := by rw [hretained]; omega
    have hnewprefix : scan_maskDelete_prefix copiedWord retained := hinvariants.1
    have hnewsuffix : scan_maskDelete_suffix copiedWord xs (i + 1) := by
      intro j hj hjn
      exact hinvariants.2 j (by omega) hjn
    have hnewbound : ∀ j ∈ rest, i + 1 ≤ j ∧ j < xs.length := by
      intro j hj
      have hj' := htail.1 j hj
      have hjn := hbound j (List.mem_cons_of_mem i hj)
      omega
    have hnewsearch : ∀ before j after, rest = before ++ j :: after → ∀ state : State,
      (next (int ((j + 2 : Nat) : Int))).run state =
        (.ok (after.head?.map (fun k => int ((k + 1 : Nat) : Int))), state) := by
      intro before j after he state
      exact hsearch (i :: before) j after (by rw [he]; rfl) state
    have hcopy := scan_maskDelete_interval_copy kept.length start i spare word (by omega) hi.1 (by omega)
    have hinc : int ((i + 1 : Nat) : Int) + int 1 = int ((i + 2 : Nat) : Int) := by
      rw [packedInt_add]
      congr 1
    have hnext : (next (int ((i + 1 : Nat) : Int) + int 1)).run
        (dequeWordStore [copiedWord] spare) =
        (.ok (rest.head?.map (fun j => int ((j + 1 : Nat) : Int))), dequeWordStore [copiedWord] spare) := by
      rw [hinc]
      exact hsearch [] i rest rfl _
    have hnew : int ((xs.length - deleted : Nat) : Int) - int 1 =
        int ((xs.length - (deleted + 1) : Nat) : Int) := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    have hp : (if int ((i + 1 : Nat) : Int) > int ((start + 1 : Nat) : Int) then
        int ((kept.length + 1 : Nat) : Int) + int ((i + 1 : Nat) : Int) - int ((start + 1 : Nat) : Int)
      else int ((kept.length + 1 : Nat) : Int)) = int ((retained.length + 1 : Nat) : Int) := by
      have hcond : (int ((i + 1 : Nat) : Int) > int ((start + 1 : Nat) : Int)) ↔ start < i := by
        change (int ((start + 1 : Nat) : Int)).val < (int ((i + 1 : Nat) : Int)).val ↔ _
        rw [packedInt_val (start + 1) (by omega), packedInt_val (i + 1) (by omega)]
        omega
      by_cases hg : start < i
      · rw [if_pos (hcond.mpr hg), packedInt_add, dequeIntSub]
        apply congrArg int
        rw [hretained]
        omega
      · rw [if_neg (fun h => hg (hcond.mp h)), hretained]
        have hz : i - start = 0 := by omega
        rw [hz, Nat.add_zero]
    have hstep := scan_maskDelete_step_from 0 next
      (int ((xs.length - deleted : Nat) : Int)) (int ((kept.length + 1 : Nat) : Int))
      (int ((start + 1 : Nat) : Int)) (int ((start + 1 : Nat) : Int))
      (int ((i + 1 : Nat) : Int)) (rest.head?.map (fun j => int ((j + 1 : Nat) : Int)))
      _ _ hcopy hnext
    have hstep' : (scan_maskDelete_step 0 next ()
        (int ((xs.length - deleted : Nat) : Int), some (int ((i + 1 : Nat) : Int)),
          int ((kept.length + 1 : Nat) : Int), int ((start + 1 : Nat) : Int),
          int ((start + 1 : Nat) : Int))).run (dequeWordStore [word] spare) =
      (.ok (.yield (int ((xs.length - (deleted + 1) : Nat) : Int),
        rest.head?.map (fun j => int ((j + 1 : Nat) : Int)), int ((retained.length + 1 : Nat) : Int),
        int ((i + 1 + 1 : Nat) : Int), int ((i + 1 + 1 : Nat) : Int))),
        dequeWordStore [copiedWord] spare) := hstep.trans (by rw [hinc, hnew, hp])
    obtain ⟨out, hrun, hbits⟩ := scan_maskDelete_after_complete xs retained copiedWord rest
      (i + 1) (deleted + 1) spare next hn (by omega) hnewbalance htail.2 hnewbound
      hnewprefix hnewsuffix hnewsearch
    have hout : ({vectorBits xs with len := int ((xs.length - (deleted + 1) - rest.length : Nat) : Int)} : BitVector) =
        {vectorBits xs with len := int ((xs.length - deleted - (i :: rest).length : Nat) : Int)} := by
      have he : xs.length - (deleted + 1) - rest.length = xs.length - deleted - (i :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [he]
    refine ⟨out, ?_, ?_⟩
    · have hr := scan_maskDelete_after_yield (vectorBits xs) next _ _ _ _ out _ hstep' hrun
      exact hr.trans (congrArg (fun B : BitVector => ((Except.ok B : Except Error BitVector), out)) hout)
    · rw [← hout]
      simpa only [retained, scan_maskDelete_blocks, List.append_assoc] using hbits
termination_by xs.length - start
decreasing_by omega

/-- The exact pure next-selection callback in the frozen Boolean-mask target. -/
def scan_maskDelete_next (selected : List Nat) (start : I64) : BitMutationM (Option I64) :=
  pure (((selected.filter (fun i => int ((i + 1 : Nat) : Int) ≥ start)).head?).map
    (fun i => int ((i + 1 : Nat) : Int)))

/-- A mask selecting no positions returns the unchanged source immediately. -/
theorem scan_maskDelete_action_none (xs mask : List Bool) (hl : xs.length = mask.length)
    (hs : ctor_mask_selected mask = []) :
    copy_delete_mask_action xs mask = pure (vectorBits xs) := by
  unfold ctor_mask_selected at hs
  have hsize : (int mask.length != int xs.length) = false := by
    rw [← hl]
    exact bne_self_eq_false _
  unfold copy_delete_mask_action bitVectorDeleteAtBoolMask
  simp only [vectorBits, hs, hsize, Bool.false_eq_true, ite_false, List.head?_nil,
    Option.map_none, pure_bind, Option.isNone_none, ite_true]

/-- The frozen first and next searches initialize the generic compaction loop
at exactly the first selected bit and the remaining ordered selections. -/
theorem scan_maskDelete_action_nonempty (xs mask : List Bool) (i : Nat) (rest : List Nat)
    (hl : xs.length = mask.length) (hn : xs.length ≤ 64)
    (hs : ctor_mask_selected mask = i :: rest) :
    copy_delete_mask_action xs mask =
      scan_maskDelete_after (vectorBits xs) (scan_maskDelete_next (ctor_mask_selected mask))
        (int xs.length - int 1, rest.head?.map (fun j => int ((j + 1 : Nat) : Int)),
          int ((i + 1 : Nat) : Int), int ((i + 2 : Nat) : Int), int ((i + 2 : Nat) : Int)) := by
  have hi : i < xs.length := by
    have hm : i ∈ ctor_mask_selected mask := by rw [hs]; exact List.mem_cons_self
    have hh := (ctor_mask_selected_mem mask i).mp hm
    omega
  have hcheck : int 1 ≤ int ((i + 1 : Nat) : Int) ∧ int ((i + 1 : Nat) : Int) ≤ int xs.length := by
    change (int 1).val ≤ (int ((i + 1 : Nat) : Int)).val ∧
      (int ((i + 1 : Nat) : Int)).val ≤ (int xs.length).val
    rw [packedInt_val (i + 1) (by omega), packedInt_val xs.length (by omega)]
    change (1 : Int) ≤ (i + 1 : Nat) ∧ ((i + 1 : Nat) : Int) ≤ (xs.length : Int)
    omega
  have hsize : (int mask.length != int xs.length) = false := by
    rw [← hl]
    exact bne_self_eq_false _
  have hinc : int ((i + 1 : Nat) : Int) + int 1 = int ((i + 2 : Nat) : Int) := by
    rw [packedInt_add]
    congr 1
  have hnext := ctor_mask_next_head (ctor_mask_selected mask) [] rest i
    (ctor_mask_selected_pairwise mask) (ctor_mask_selected_bound mask (by omega)) hs
  have hcheck' : int 1 ≤ int (Int.ofNat (i + 1)) ∧
      int (Int.ofNat (i + 1)) ≤ int (Int.ofNat xs.length) := hcheck
  have hinc' : int (Int.ofNat (i + 1)) + int 1 = int (Int.ofNat (i + 2)) := hinc
  have hnext' : ((i :: rest).filter (fun j => int (Int.ofNat (j + 1)) ≥
      int (Int.ofNat (i + 2)))).head?.map (fun j => int (Int.ofNat (j + 1))) =
      rest.head?.map (fun j => int ((j + 1 : Nat) : Int)) := by
    rw [hs] at hnext
    exact hnext
  have hsraw := hs
  unfold ctor_mask_selected at hsraw
  unfold copy_delete_mask_action bitVectorDeleteAtBoolMask
  simp only [hsraw, vectorBits, hsize, Bool.false_eq_true, ite_false, List.head?_cons,
    Option.map_some, pure_bind, Option.isNone_some, Option.get!_some, hcheck',
    true_and, ite_true, hinc', hnext']
  unfold scan_maskDelete_after scan_maskDelete_step scan_maskDelete_finish rangeSingleFinish
    scan_maskDelete_next
  simp only [ctor_mask_selected, hsraw, bind_assoc, pure_bind]
  rfl

/-- The exact retained-value expression in the frozen Boolean-mask target. -/
def scan_maskDelete_expected (xs mask : List Bool) : List Bool :=
  (List.range xs.length).filterMap (fun i =>
    if mask.getD i false then none else some (xs.getD i false))

/-- Ordered selected-position blocks coincide with the frozen Boolean-mask result. -/
theorem scan_maskDelete_blocks_expected (xs mask : List Bool) (hl : xs.length = mask.length) :
    scan_maskDelete_blocks xs (ctor_mask_selected mask) 0 = scan_maskDelete_expected xs mask := by
  have hvalid : ∀ i ∈ ctor_mask_selected mask, i < xs.length := by
    intro i hi
    have h := (ctor_mask_selected_mem mask i).mp hi
    omega
  rw [ctor_mask_blocks_filterMap xs (ctor_mask_selected mask) (ctor_mask_selected_pairwise mask) hvalid]
  apply ctor_mask_filterMap_congr
  intro i hi
  have hin : i < mask.length := by have := List.mem_range.mp hi; omega
  have hm : (ctor_mask_selected mask).contains i = mask.getD i false := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem, ctor_mask_selected_mem, hin, true_and]
  rw [hm]

/-- The full frozen Boolean-mask deletion succeeds and returns exactly the stable
filtered source for every input and equal-length mask contained in one word. -/
theorem scan_maskDelete_single_chunk_success (xs mask : List Bool)
    (hl : xs.length = mask.length) (hn : xs.length ≤ 64) :
    ∃ output : BitVector, ∃ outState : State,
      (copy_delete_mask_action xs mask).run (initWords (encodeBits xs)) = (.ok output, outState) ∧
      bitValues outState output = scan_maskDelete_expected xs mask := by
  cases hs : ctor_mask_selected mask with
  | nil =>
    have haction := scan_maskDelete_action_none xs mask hl hs
    have hrun := congrArg (fun action : BitMutationM BitVector =>
      action.run (initWords (encodeBits xs))) haction
    have hexpected := scan_maskDelete_blocks_expected xs mask hl
    rw [hs, scan_maskDelete_blocks, List.drop_zero] at hexpected
    exact ⟨vectorBits xs, initWords (encodeBits xs), hrun,
      (scalar_bits_initial xs [int xs.length] (by omega)).trans hexpected⟩
  | cons i rest =>
    have hordered := ctor_mask_selected_pairwise mask
    have hi : i < xs.length := by
      have hm : i ∈ ctor_mask_selected mask := by rw [hs]; exact List.mem_cons_self
      have hh := (ctor_mask_selected_mem mask i).mp hm
      omega
    have hpair : ∀ j ∈ rest, i < j := by
      rw [hs] at hordered
      exact (List.pairwise_cons.mp hordered).1
    have htail : rest.Pairwise (· < ·) := by
      rw [hs] at hordered
      exact (List.pairwise_cons.mp hordered).2
    have hbound : ∀ j ∈ rest, i + 1 ≤ j ∧ j < xs.length := by
      intro j hj
      have ho := hpair j hj
      have hm : j ∈ ctor_mask_selected mask := by rw [hs]; exact List.mem_cons_of_mem i hj
      have hv := (ctor_mask_selected_mem mask j).mp hm
      omega
    have hprefLen : (xs.take i).length = i := by rw [List.length_take, Nat.min_eq_left (by omega)]
    have hsearch : ∀ before j after, rest = before ++ j :: after → ∀ state : State,
      (scan_maskDelete_next (ctor_mask_selected mask) (int ((j + 2 : Nat) : Int))).run state =
        (.ok (after.head?.map (fun k => int ((k + 1 : Nat) : Int))), state) := by
      intro before j after he state
      exact ctor_mask_next_run (ctor_mask_selected mask) (i :: before) after j state
        hordered (ctor_mask_selected_bound mask (by omega)) (by rw [hs, he]; rfl)
    obtain ⟨out, hloop, hbits⟩ := scan_maskDelete_after_complete xs (xs.take i)
      (packedPrefix xs 0 64) rest (i + 1) 1 32 (scan_maskDelete_next (ctor_mask_selected mask))
      hn (by omega) (by rw [hprefLen]) htail hbound
      (scan_maskDelete_initial_prefix xs i hn (by omega))
      (scan_maskDelete_initial_suffix xs (i + 1) hn) hsearch
    have hnew : int xs.length - int 1 = int ((xs.length - 1 : Nat) : Int) :=
      frontPopLengthPred xs.length (by omega)
    have haction : copy_delete_mask_action xs mask =
      scan_maskDelete_after (vectorBits xs) (scan_maskDelete_next (ctor_mask_selected mask))
        (int ((xs.length - 1 : Nat) : Int), rest.head?.map (fun j => int ((j + 1 : Nat) : Int)),
          int (((xs.take i).length + 1 : Nat) : Int), int ((i + 1 + 1 : Nat) : Int),
          int ((i + 1 + 1 : Nat) : Int)) := by
      rw [scan_maskDelete_action_nonempty xs mask i rest hl hn hs, hnew, hprefLen]
    have hfull := (congrArg (fun action : BitMutationM BitVector =>
      action.run (dequeWordStore [packedPrefix xs 0 64] 32)) haction).trans hloop
    have hsource := scan_maskDelete_initial_store xs (by omega) hn
    have hrun := (congrArg (fun state : State => (copy_delete_mask_action xs mask).run state)
      hsource.symm).trans hfull
    have hexpected := scan_maskDelete_blocks_expected xs mask hl
    rw [hs, scan_maskDelete_blocks, List.drop_zero, Nat.sub_zero] at hexpected
    exact ⟨{vectorBits xs with len := int ((xs.length - 1 - rest.length : Nat) : Int)}, out,
      hrun, hbits.trans hexpected⟩

/-- The frozen result observation, factored to keep execution transport closed. -/
def scan_maskDelete_outcome (expected : List Bool) (result : Except Error BitVector × State) : Prop :=
  match result.1 with
  | .ok output => bitValues result.2 output = expected
  | .error _ => False

/-- The exact frozen per-input mask-deletion observation holds throughout the
single-word domain, with arbitrary masks and arbitrary original bit contents. -/
theorem scan_maskDelete_single_chunk_observation (xs mask : List Bool)
    (hl : xs.length = mask.length) (hn : xs.length ≤ 64) :
    scan_maskDelete_outcome
      ((List.range xs.length).filterMap (fun i => if mask.getD i false then none else some (xs.getD i false)))
      ((copy_delete_mask_action xs mask).run (initWords (encodeBits xs))) := by
  obtain ⟨output, out, hrun, hbits⟩ := scan_maskDelete_single_chunk_success xs mask hl hn
  exact Eq.mpr (congrArg (scan_maskDelete_outcome (scan_maskDelete_expected xs mask)) hrun) hbits
end JuliaLean.ChatGPT.Batch5.Group2
end



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

/-- Independent scalar-conversion domain: Julia accepts only exact zero or one
from a machine Integer as a Boolean. This helper does not call the model's
conversion implementation. Julia source: base/bool.jl:170. -/
def scalarValue : JuliaLean.base.bitarray.Models1Group16.ScalarItem → Option Bool
  | .boolean value => some value
  | .integer _ value =>
      if value.val = 0 then some false
      else if value.val = 1 then some true
      else none

/-- For every Bool/machine-Integer item, prepend checks conversion first and
returns the original logical sequence preceded by the converted bit. A rejected
conversion leaves the entire heap unchanged. Input aliases and the full native
length domain remain included; overflow has not been excluded to ease a proof.
Julia source: base/bitarray.jl:839-859; base/array.jl pushfirst! documentation. -/
def PushFirstScalarContract : Prop :=
  ∀ (s : Heap) (B : BitVector) (item : JuliaLean.base.bitarray.Models1Group16.ScalarItem), Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.pushFirstScalar B item).run s
    match scalarValue item with
    | none => result.1 = .error .inexact ∧ result.2 = s
    | some value =>
        match result.1 with
        | .ok output =>
            output.chunks = B.chunks ∧ output.dims = B.dims ∧
            output.len.val = B.len.val + 1 ∧
            bits result.2 output = value :: bits s B ∧
            (Packed s B → Packed result.2 output)
        | .error _ => False

/-- Insertion converts the machine index, checks the source's native bounds,
then converts the item before mutation. Accepted input adds exactly one logical
value at the selected position and preserves the old prefix and suffix.
The length bound is evaluated with the source's native Int wrap at typemax;
the logical sequence specification itself uses mathematical list operations.
Julia source: base/bitarray.jl:884-911; base/array.jl insert! documentation. -/
def InsertMachineScalarContract : Prop :=
  ∀ (t : IntTy) (s : Heap) (B : BitVector) (i : JInt t) (item : JuliaLean.base.bitarray.Models1Group16.ScalarItem),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.insertMachineScalar B i item).run s
    if ¬ FitsNative i.val then result.1 = .error .inexact ∧ result.2 = s
    else if i.val < 1 ∨
        (if B.len.val = (2 : Int)^63 - 1 then -(2 : Int)^63 else B.len.val + 1) < i.val then
      result.1 = .error .bounds ∧ result.2 = s
    else
      match scalarValue item with
      | none => result.1 = .error .inexact ∧ result.2 = s
      | some value =>
          match result.1 with
          | .ok output =>
              output.chunks = B.chunks ∧ output.dims = B.dims ∧
              output.len.val = B.len.val + 1 ∧
              bits result.2 output =
                (bits s B).take (i.val - 1).toNat ++ [value] ++
                (bits s B).drop (i.val - 1).toNat ∧
              (Packed s B → Packed result.2 output)
          | .error _ => False


/-- Non-Bool machine-integer deletion removes exactly one selected element.
All ten widths, all values and both conversion/bounds errors are included.
Julia source: base/bitarray.jl:913-953.
Documentation: base/array.jl:1876-1881,1912-1919.
This is a useful specialization; the full Integer row remains blocked on Bool
deprecation and other Integer-family dispatch. -/
def DeleteAtMachineContract : Prop :=
  ∀ (t : IntTy) (s : Heap) (B : BitVector) (i : JInt t),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.deleteAtMachine B i).run s
    if ¬ FitsNative i.val then result.1 = .error .inexact ∧ result.2 = s
    else if i.val < 1 ∨ B.len.val < i.val then
      result.1 = .error .bounds ∧ result.2 = s
    else
      match result.1 with
      | .ok updated =>
          updated.chunks = B.chunks ∧ updated.len.val = B.len.val - 1 ∧
          updated.dims = B.dims ∧
          bits result.2 updated = (bits s B).eraseIdx (i.val - 1).toNat ∧
          (Packed s B → Packed result.2 updated)
      | .error _ => False

/-- Scalar splice returns the old selected value and exposes the shortened
header and shared chunk storage. Conversion and bounds failures leave state alone.
Julia source: base/bitarray.jl:1066-1078.
Documentation: base/array.jl:2015-2021.
The statement covers every input of the explicitly machine-Integer specialization. -/
def SpliceMachineContract : Prop :=
  ∀ (t : IntTy) (s : Heap) (B : BitVector) (i : JInt t),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.spliceMachine B i).run s
    if ¬ FitsNative i.val then result.1 = .error .inexact ∧ result.2 = s
    else if i.val < 1 ∨ B.len.val < i.val then
      result.1 = .error .bounds ∧ result.2 = s
    else
      match result.1 with
      | .ok (updated, removed) =>
          removed = bitAt s B (i.val - 1).toNat ∧
          updated.chunks = B.chunks ∧ updated.len.val = B.len.val - 1 ∧
          updated.dims = B.dims ∧
          bits result.2 updated = (bits s B).eraseIdx (i.val - 1).toNat ∧
          (Packed s B → Packed result.2 updated)
      | .error _ => False


/-- Independent documented validity of the first p tuple indices. -/
def NativeTuplePrefixOK (B : BitVector) (indices : List I64) (p : Nat) : Prop :=
  (∀ k ∈ indices.take p, 1 ≤ k.val ∧ k.val ≤ B.len.val) ∧
  (indices.take p).Pairwise (fun a b => a.val < b.val)

/-- Snapshot selection, independent of the bit operations used by keepat!. -/
def MaskSelected (s : Heap) (B mask : BitVector) : List Bool :=
  ((bits s B).zip (bits s mask)).filterMap
    (fun pair => if pair.2 then some pair.1 else none)

/-- Every constructible native-Int tuple, including the first failing order or
bounds check and the writes before that failure. Valid inputs retain exactly the
specified old elements in order. The maximum-length keep-all case is included:
source nextind wraps before its tail-range bounds check and throws BoundsError.

Julia source: base/bitarray.jl:1063; base/abstractarray.jl:3699-3715.
Documentation: base/array.jl:3105-3116. Tuple length is machine-sized, with no
arbitrary small-input cutoff. The full generic iterable method remains blocked. -/
def KeepNativeTupleContract : Prop :=
  ∀ (s : Heap) (B : BitVector) (indices : List I64),
    Readable s B → indices.length < 2 ^ 63 →
    let result := (JuliaLean.base.bitarray.Models1Group16.keepNativeTuple B indices).run s
    (∀ (p : Nat) (previous current : I64),
      0 < p → indices[p - 1]? = some previous → indices[p]? = some current →
      NativeTuplePrefixOK B indices p → current.val ≤ previous.val →
      result.1 = .error (.argument "indices must be unique and sorted") ∧
      MutationFrame s result.2 B.chunks) ∧
    (∀ (p : Nat) (current : I64),
      indices[p]? = some current → NativeTuplePrefixOK B indices p →
      (p = 0 ∨ ∃ previous, indices[p - 1]? = some previous ∧ previous.val < current.val) →
      (current.val < 1 ∨ B.len.val < current.val) →
      result.1 = .error .bounds ∧ MutationFrame s result.2 B.chunks) ∧
    (NativeTuplePrefixOK B indices indices.length →
      if indices.length = 2 ^ 63 - 1 then
        result.1 = .error .bounds ∧ result.2 = s
      else
        match result.1 with
        | .ok updated =>
            updated.chunks = B.chunks ∧ updated.dims = B.dims ∧
            updated.len.val = (indices.length : Int) ∧ Packed result.2 updated ∧
            bits result.2 updated = indices.map (fun k => bitAt s B (k.val - 1).toNat)
        | .error _ => False)

/-- Complete BitVector-mask specialization, retaining live shared-storage
behavior. For every overlap it either reports the source length/overflow error
or returns an ordered subsequence of the old BitVector. On nonoverlapping or
identical-start storage, the documented snapshot mask determines that subsequence
exactly. Arbitrary shifted overlaps are not silently snapshot-copied.

Julia source: base/bitarray.jl:1064; base/abstractarray.jl:3717-3729.
Documentation: base/array.jl:3109,3132-3137 and the Base aliasing warning.
The typemax keep-all case is an explicit source behavior, not an omitted input.
Other AbstractVector{Bool} implementations remain outside this specialization. -/
def KeepBitMaskContract : Prop :=
  ∀ (s : Heap) (B mask : BitVector),
    Readable s B → Readable s mask →
    let result := (JuliaLean.base.bitarray.Models1Group16.keepBitMask B mask).run s
    if mask.len ≠ B.len then
      result.1 = .error .bounds ∧ result.2 = s
    else if B.len.val = (2 : Int)^63 - 1 ∧ (bits s mask).all id = true then
      result.1 = .error .bounds ∧ result.2 = s
    else
      match result.1 with
      | .ok updated =>
          updated.chunks = B.chunks ∧ updated.dims = B.dims ∧
          updated.len.val.toNat ≤ B.len.val.toNat ∧ Packed result.2 updated ∧
          (bits result.2 updated).Sublist (bits s B) ∧
          (SnapshotSafe s B mask → bits result.2 updated = MaskSelected s B mask)
      | .error _ => False
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesPush1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-deque", juliaFile := "base/bitarray.jl", juliaFns := ["push!(::BitVector, x)", "pop!(::BitVector)", "pushfirst!(::BitVector, x)", "popfirst!(::BitVector)"],
    statement := "push! and pushfirst! add the converted Bool at the end or beginning; nonempty pop! and popfirst! return and remove the last or first bit. Empty pops and failed conversions leave state unchanged, and successful operations preserve packed padding.", source := "base/bitarray.jl:739-755,827-882; unused bits are zero (base/bitarray.jl:5-6)",
    status := .proven, prop := ``Round5.DequeAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group1.BitarraysDeque_proven },
  { id := "bitarrays-insert-deleteat", juliaFile := "base/bitarray.jl", juliaFns := ["insert!(::BitVector, i, x)", "deleteat!(::BitVector, i::Integer)"],
    statement := "For valid insertion and deletion positions, insert! and deleteat! preserve logical order and packed padding; failed Bool conversions leave state unchanged.", source := "base/bitarray.jl:884-953; unused bits are zero (base/bitarray.jl:5-6)",
    status := .proven, prop := ``Round5.InsertDeleteAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group1.BitarraysInsertDeleteat_proven },
  { id := "bitarrays-deleteat-empty-range", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!(::BitVector, ::AbstractUnitRange{Int})", "splice!(::BitVector, ::AbstractUnitRange{Int}, ins)"],
    statement := "Every empty UnitRange is a no-op, including 0:-1; valid nonempty ranges delete their bits and preserve packed padding.", source := "base/bitarray.jl:955-977; unused bits are zero (base/bitarray.jl:5-6)",
    status := .refuted, prop := ``Round5.DeleteatRangeAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group1.BitarraysDeleteatEmptyRange_refuted,
    issue := "none found" },
  { id := "bitarrays-deleteat-range-inside", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!(::BitVector, ::AbstractUnitRange{Int})", "copy_chunks!"],
    statement := "Deleting a valid nonempty UnitRange removes its bits and preserves zero padding in the final chunk.", source := "base/bitarray.jl:955-977; unused bits are zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``Round5.DeleteatRangeInsideAgrees, thm := none, notes := "No complete exact proof returned. the remaining exact target is blocked by copyChunks reading ks0+i-1 where the quoted Julia source reads ks0+i." }
]
def entriesPush2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-delete-at-indices-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!@979"],
    statement := "Deleting sorted unique valid indices removes exactly those elements.", source := "obvious invariant; base/bitarray.jl:979",
    status := .todo, prop := ``DeleteAtIndicesAgrees, thm := none, notes := "No complete exact proof returned. the complete multiword target remains blocked by the old forward-copy source-index mismatch." },
  { id := "bitarray-delete-at-mask-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!@1022"],
    statement := "Deleting a Boolean mask removes exactly the elements selected by true mask entries.", source := "obvious invariant; base/bitarray.jl:1022",
    status := .todo, prop := ``DeleteAtMaskAgrees, thm := none, notes := "No complete exact proof returned. the complete multiword target remains blocked by the old forward-copy source-index mismatch." }
]
def entriesPush3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-splice-removed-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["splice!@1126", "_splice_int!@1087", "splice!@1082", "empty!@1137", "splice!@1066"],
    statement := "splice! returns the elements covered by its range before replacing them.", source := "obvious invariant; base/bitarray.jl:1066",
    status := .todo, prop := ``SpliceRemovedAgrees, thm := none, notes := "Model treats fresh UInt64 chunk contents as undefined and can throw during read/modify/write; the same 65-bit public splice succeeds on release and nightly. Prop therefore describes a model defect." }
]
open JuliaLean JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

def PushConversionErrors : Prop :=
  ∀ (X : Type) (runtime : AllocationData) (target : Ref 1) (item : X)
    (convertBool : X → ObjectM Bool) (s final : ObjectState)
    (error : JuliaLean.base.array.Error),
    (convertBool item).run s = (.error error, final) →
    (pushConvert runtime convertBool target item).run s = (.error error, final)

def AppendIteratorConversionErrors : Prop :=
  ∀ (I : Type) (runtime : AllocationData) (target : Ref 1) (items : I)
    (toBitVector : I → ObjectM (Ref 1)) (s final : ObjectState)
    (error : JuliaLean.base.array.Error),
    (toBitVector items).run s = (.error error, final) →
    (appendIterableConvert runtime toBitVector target items).run s = (.error error, final)

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem pushConversionErrors : PushConversionErrors := by
  intro X runtime target item convertBool s final error h
  simp [Models1Group15.pushConvert, h]

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem appendIteratorConversionErrors : AppendIteratorConversionErrors := by
  intro I runtime target items toBitVector s final error h
  simp [Models1Group15.appendIterableConvert, h]

end Completion

/-- Selected index-collection methods may fail after mutating storage. Both
public keepat! overloads preserve that exception and its reached heap. -/
def KeepDispatchErrors : Prop :=
  ∀ (I : Type) (keep : BitVector → I → BitMutationM BitVector)
    (B : BitVector) (indices : I) (initial final : JuliaLean.base.array.MutableMemory U64)
    (error : JuliaLean.base.array.Error),
    (keep B indices).run initial = (.error error, final) →
    (bitVectorKeepAt keep B indices).run initial = (.error error, final) ∧
    (bitVectorKeepAtMask keep B indices).run initial = (.error error, final)

theorem KeepDispatchErrors_proven : KeepDispatchErrors := by
  intro I keep B indices initial final error h
  exact ⟨h, h⟩

def entriesPush4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-pushfirst-scalar", juliaFile := "base/bitarray.jl",
    juliaFns := ["pushfirst!(::BitVector, ::Union{Bool,BitInteger})"],
    statement := "Prepending a represented scalar converts before mutation, adds its exact Boolean value at the front, and preserves the previous logical sequence; conversion failures preserve all storage.",
    source := "base/bitarray.jl:839-859; base/bool.jl:170; base/number.jl:6-7", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.PushFirstScalarContract, thm := none,
    notes := "Statement defect: At logical length typemax(Int), a readable input needs 2^57 chunk words and the source increments its length with native wrap while the statement requires mathematical length + 1; Julia cannot construct this exabyte-sized input, so the statement needs length < typemax(Int) and sufficient growth-allocation headroom, or explicit allocation-error cases." },
  { id := "bitarray-insert-machine-scalar", juliaFile := "base/bitarray.jl",
    juliaFns := ["insert!(::BitVector, ::BitInteger, ::Union{Bool,BitInteger})", "_insert_int!(::BitVector, ::Int, ::Union{Bool,BitInteger})"],
    statement := "Insertion checks machine-index conversion, native bounds and scalar Boolean conversion in source order, then preserves the original logical prefix and suffix around the inserted bit.",
    source := "base/bitarray.jl:884-911; base/bool.jl:170", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.InsertMachineScalarContract, thm := none,
    notes := "Statement defect: A logical-empty vector with 2^60-1 initialized backing chunk words, offset 1, index 1, and value false requests growth to at least 2^60 words and returns an allocation ArgumentError; Julia cannot construct this roughly nine-exabyte input, so the statement needs the computed growth-allocation request < 2^60 or explicit allocation-error cases." },
  { id := "bitarray-deleteat-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["deleteat!(::BitVector, ::Integer)", "_deleteat!(::BitVector, ::Int)"],
    statement := "For all ten non-Bool machine Integer types, deleting an index removes precisely that logical bit, preserving the shared chunk handle and suffix order; conversion and bounds errors leave the heap unchanged.",
    source := "base/bitarray.jl:913-953; base/array.jl:1876-1881,1912-1919", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.DeleteAtMachineContract, thm := none,
    notes := "No complete exact proof returned. searchNativeInteger and deleteAtMachineConversionFailure establish native conversion and its unchanged-heap failure case; remaining goal: bounds behavior and the exact deletion shift with packing and mutation-frame preservation." },
  { id := "bitarray-keep-native-tuple", juliaFile := "base/bitarray.jl",
    juliaFns := ["keepat!(::BitVector, ::Tuple{Vararg{Int}})"],
    statement := "Keeping native tuple indices preserves the selected old logical values in order, retains earliest sorted/bounds errors and their mutation frame, and includes native nextind overflow.",
    source := "base/bitarray.jl:1063; base/abstractarray.jl:3699-3715", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.KeepNativeTupleContract, thm := none,
    notes := "Unproved and unchecked. Complete concrete specialization; full generic inventory row remains blocked. Actual live reads and source error order retained; no supplied implementation callback." },
  { id := "bitarray-keep-bit-mask", juliaFile := "base/bitarray.jl",
    juliaFns := ["keepat!(::BitVector, ::BitVector)"],
    statement := "A live BitVector mask retains an ordered subsequence, checks mask length before mutation, and agrees with snapshot-mask selection on documented safe aliases; all overlap and nextind-overflow cases remain represented.",
    source := "base/bitarray.jl:1064; base/abstractarray.jl:3717-3729", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.KeepBitMaskContract, thm := none,
    notes := "Unproved and unchecked. Complete concrete specialization; full generic inventory row remains blocked. Actual live reads and source error order retained; no supplied implementation callback." },
  { id := "bitarray-splice-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["splice!(::BitVector, ::Integer)"],
    statement := "For all ten non-Bool machine Integer types, scalar splice returns the previous selected Boolean and the shortened header; conversion and bounds errors precede mutation.",
    source := "base/bitarray.jl:1066-1078; base/array.jl:2015-2021", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.SpliceMachineContract, thm := none,
    notes := "No complete exact proof returned. searchNativeInteger and spliceMachineConversionFailure establish native conversion and its unchanged-heap failure case; remaining goal: bounds behavior, returned scalar, shortened header, and exact suffix preservation." },
  { id := "bitarray-push-conversion-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["push!(B::BitVector, item)"],
    statement := "Pushing propagates the item conversion's exception and preceding effects without subsequently growing storage or changing the target's length.",
    source := "base/bitarray.jl:739-755", status := .proven,
    prop := ``PushConversionErrors, thm := some ``Completion.pushConversionErrors },
  { id := "bitarray-append-iterator-conversion-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["append!(B::BitVector, items)"],
    statement := "Appending an arbitrary iterable propagates the exception and prior effects of constructing its BitVector before any subsequent target mutation.",
    source := "base/bitarray.jl:774", status := .proven,
    prop := ``AppendIteratorConversionErrors, thm := some ``Completion.appendIteratorConversionErrors },
  { id := "bitarray-keep-dispatch-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["keepat!(B::BitVector, inds)", "keepat!(B::BitVector, inds::AbstractVector{Bool})"],
    statement := "Both keepat! overloads preserve the selected index collection method's exception and every storage effect performed before that exception.",
    source := "base/bitarray.jl:1063-1064", status := .proven,
    prop := ``KeepDispatchErrors, thm := some ``KeepDispatchErrors_proven }
]
end JuliaLean.Proofs.base.bitarray

