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

namespace JuliaLean.CompletionState1

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


end JuliaLean.CompletionState1

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A concrete diagnostic of the frozen packed-copy loop, not a Julia bug claim. -/
theorem rangeDelete_model_middle_bit :
    (match (Round5.Round2.deleteBitRangePublic (vectorBits rangeDeleteWitnessBits)
      ⟨int 1, int 1⟩).run (initWords (encodeBits rangeDeleteWitnessBits)) with
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

/-- The documented deletion result has no true bit at public index 127. -/
theorem rangeDelete_expected_middle_bit :
    (deleteRangeList rangeDeleteWitnessBits ⟨int 1, int 1⟩).getD 126 false = false := by
  decide
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete packed output shows that the frozen fill model masks chunk one. -/
theorem fillModel65WrongSecondBit :
    let xs := List.replicate 65 false
    let B := vectorBits xs
    let result := (fillBitArray Round5.Round2.convertBoolMutation
      Round5.Round2.fillChunkVectorModel B true).run (initWords (encodeBits xs))
    bitAt result.2 B 1 = false := by
  rfl

/-- The second logical bit of the documented fill result is true. -/
theorem fillExpected65SecondBit :
    (List.replicate 65 true).getD 1 false = true := by
  rfl
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A small input with one true logical bit at index 65. -/
def shiftWitnessBits : List Bool :=
  List.replicate 64 false ++ [true] ++ List.replicate 65 false

theorem shiftWitnessEncoded : encodeBits shiftWitnessBits = [u64 0, u64 1, u64 0] := by
  decide

/-- The copied middle chunk exposes the frozen source-index discrepancy in left shift. -/
theorem shiftModelLeftMiddleBit :
    (match (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      Round5.Round2.shiftLeftUnsignedModel Round5.Round2.shiftRightSignedArgModel
      (vectorBits shiftWitnessBits) (int 1)).run (initWords (encodeBits shiftWitnessBits)) with
    | (.ok B, s) => bitAt s B 127
    | (.error _, _) => false) = true := by
  rw [shiftWitnessEncoded]
  unfold bitVectorShiftLeftSigned Round5.Round2.shiftLeftUnsignedModel bitVectorShiftLeftUnsigned
  simp only [copyChunks]
  decide

/-- The documented left shift has a false logical bit at index 128. -/
theorem shiftExpectedLeftMiddleBit :
    (shiftLeftBits shiftWitnessBits 1).getD 127 false = false := by
  decide
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Reading a backing memory uses only its indexed memory entry. -/
theorem growthMemoryRead (s : State) (mem : Nat) (slots : List (Option U64))
    (hm : s.memories[mem]? = some slots) :
    (memoryRead mem).run s = (.ok slots, s) := by
  simp only [memoryRead, shape_run_bind, shape_run_get, hm, shape_run_pure]

/-- The source prefix is copied exactly by the frozen memory-move implementation. -/
theorem growthMemoryMove (s : State) (src dest : Nat)
    (source destination : List (Option U64)) (n : Nat)
    (hsrc : s.memories[src]? = some source) (hdest : s.memories[dest]? = some destination)
    (hs : n ≤ source.length) (hd : n ≤ destination.length)
    (hn : destination.length ≤ 9223372036854775807) :
    (memoryMove dest one src one (int n)).run s =
      (.ok (), {s with memories := s.memories.set dest ((source.take n).zipIdx.foldl (fun (ws : List (Option U64)) (pair : Option U64 × Nat) =>
          ws.set pair.2 pair.1) destination)}) := by
  have hi := packedInt_val n (by omega)
  have hloop := growthCopyLoop s dest destination (source.take n) hdest
    (by rw [List.length_take, Nat.min_eq_left hs]; exact hd) hn
  have hbounds : 0 ≤ (int n).val ∧ 1 ≤ one.val ∧
      one.val - 1 + (int n).val ≤ (destination.length : Int) ∧
      1 ≤ one.val ∧ one.val - 1 + (int n).val ≤ (source.length : Int) := by
    rw [hi]
    change 0 ≤ (n : Int) ∧ 1 ≤ (1 : Int) ∧
      1 - 1 + (n : Int) ≤ (destination.length : Int) ∧
      1 ≤ (1 : Int) ∧ 1 - 1 + (n : Int) ≤ (source.length : Int)
    omega
  have hnat : 0 ≤ (n : Int) := by omega
  have hsrcBound : (n : Int) ≤ (source.length : Int) := by omega
  have hdestBound : (n : Int) ≤ (destination.length : Int) := by omega
  simp only [memoryMove, shape_run_bind, growthMemoryRead s src source hsrc,
    growthMemoryRead s dest destination hdest, hi, show one.val = 1 by rfl,
    Int.sub_self, Int.zero_add, hnat, hsrcBound, hdestBound,
    show (1 : Int) ≤ 1 by decide, and_self, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false,
    Int.toNat_zero, List.drop_zero, Int.toNat_natCast, hloop, shape_run_pure]

/-- Moving the old visible data into a fresh allocation keeps all unfilled slots unassigned. -/
theorem growthMemoryMoveFresh (s : State) (src dest : Nat)
    (values tail : List (Option U64)) (spare : Nat)
    (hsrc : s.memories[src]? = some (values ++ tail))
    (hdest : s.memories[dest]? = some (List.replicate (values.length + spare) none))
    (hn : values.length + spare ≤ 9223372036854775807) :
    (memoryMove dest one src one (int values.length)).run s =
      (.ok (), {s with memories := s.memories.set dest (values ++ List.replicate spare none)}) := by
  have hr := growthMemoryMove s src dest (values ++ tail)
    (List.replicate (values.length + spare) none) values.length hsrc hdest
    (by rw [List.length_append]; omega) (by rw [List.length_replicate]; omega)
    (by rwa [List.length_replicate])
  have hslots := growthInstallPrefix values [] spare
  simp only [List.length_nil, List.nil_append] at hslots
  rw [List.take_left, hslots] at hr
  exact hr

/-- Multiplying two nonnegative native values preserves their mathematical product modulo wrapping. -/
theorem growthIntMul (a b : Nat)
    (ha : a ≤ 9223372036854775807) (hb : b ≤ 9223372036854775807) :
    int a * int b = int ((a * b : Nat) : Int) := by
  apply Subtype.ext
  change wrapInt .i64 ((int a).val * (int b).val) = wrapInt .i64 ((a * b : Nat) : Int)
  rw [packedInt_val a ha, packedInt_val b hb, Int.natCast_mul]

/-- Native division by eight preserves nonnegative mathematical quotients. -/
theorem growthDivideEight (a : Nat) (ha : a ≤ 9223372036854775807) :
    JInt.wrap .i64 ((int a).val.tdiv (JInt.wrap .i64 8).val) =
      int ((a / 8 : Nat) : Int) := by
  rw [packedInt_val a ha]
  change int ((a : Int).tdiv 8) = _
  rw [Int.natCast_tdiv_eq_ediv]
  exact congrArg int (Int.natCast_ediv a 8).symm

/-- Mathematical form of the frozen vector allocation growth factor. -/
def growthCapacity (n : Nat) : Nat :=
  n + 2 ^ ((n.log2 + 1) * 7 / 8) * 3 + n / 8

/-- The array growth factor stays comfortably within the native byte-allocation limit here. -/
theorem growthCapacityBounds (n : Nat) (hp : 0 < n) (hn : n ≤ 144115188075855872) :
    n ≤ growthCapacity n ∧ growthCapacity n ≤ 576460752303423488 := by
  have hl : n.log2 < 64 := (Nat.log2_lt (by omega)).mpr (by omega)
  have he : (n.log2 + 1) * 7 / 8 ≤ 56 := by omega
  have hpow : 2 ^ ((n.log2 + 1) * 7 / 8) ≤ (72057594037927936 : Nat) := by
    exact Nat.pow_le_pow_right (by decide) he
  unfold growthCapacity
  omega

/-- The frozen overallocation callback returns the exact bounded growth factor. -/
theorem growthOverallocationRun (n : Nat) (s : State)
    (hp : 0 < n) (hn : n ≤ 144115188075855872) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).overallocation (int n)).run s =
      (.ok (int (growthCapacity n)), s) := by
  have hn64 : n ≤ 9223372036854775807 := by omega
  have hl : n.log2 < 64 := (Nat.log2_lt (by omega)).mpr (by omega)
  have he : (n.log2 + 1) * 7 / 8 ≤ 56 := by omega
  have hpow : 2 ^ ((n.log2 + 1) * 7 / 8) ≤ (72057594037927936 : Nat) :=
    Nat.pow_le_pow_right (by decide) he
  have hcap := growthCapacityBounds n hp hn
  have hctlz : JInt.wrap .i64
      (if (int n).val = 0 then 64 else 63 - ((int n).val.toNat.log2 : Int)) =
        int (63 - (n.log2 : Int)) := by
    rw [packedInt_val n hn64, if_neg (by omega), Int.toNat_natCast]
    rfl
  have hexp : JInt.wrap .i64 64 - int (63 - (n.log2 : Int)) =
      int ((n.log2 + 1 : Nat) : Int) := by
    change int 64 - int (63 - (n.log2 : Int)) = _
    rw [dequeIntSub]
    exact congrArg int (by omega)
  have hmul : int ((n.log2 + 1 : Nat) : Int) * JInt.wrap .i64 7 =
      int (((n.log2 + 1) * 7 : Nat) : Int) :=
    growthIntMul (n.log2 + 1) 7 (by omega) (by decide)
  have hdiv1 := growthDivideEight ((n.log2 + 1) * 7) (by omega)
  have hdiv2 := growthDivideEight n hn64
  have hshift : JInt.wrap .i64
      (one.val * (2 : Int) ^ (int (((n.log2 + 1) * 7 / 8 : Nat) : Int)).val.toNat) =
        int ((2 ^ ((n.log2 + 1) * 7 / 8) : Nat) : Int) := by
    rw [packedInt_val _ (by omega), Int.toNat_natCast]
    change int ((1 : Int) * 2 ^ ((n.log2 + 1) * 7 / 8)) = _
    rw [Int.one_mul, Int.natCast_pow]
    rfl
  have hextra : int ((2 ^ ((n.log2 + 1) * 7 / 8) : Nat) : Int) * JInt.wrap .i64 3 +
      int ((n / 8 : Nat) : Int) =
        int (((2 ^ ((n.log2 + 1) * 7 / 8) * 3 + n / 8 : Nat)) : Int) := by
    rw [show JInt.wrap .i64 3 = int ((3 : Nat) : Int) from rfl,
      growthIntMul _ 3 (by omega) (by decide), packedInt_add]
    exact congrArg int (by omega)
  let extra := 2 ^ ((n.log2 + 1) * 7 / 8) * 3 + n / 8
  have hextrab : extra ≤ 9223372036854775807 := by dsimp only [extra]; omega
  have htest : ¬ int n > JInt.typemax .i64 - int extra := by
    change ¬ (JInt.typemax .i64 - int extra).val < (int n).val
    have hmax : JInt.typemax .i64 = int 9223372036854775807 := rfl
    rw [hmax, dequeIntSub]
    have hdiff : (9223372036854775807 : Int) - (extra : Int) =
        ((9223372036854775807 - extra : Nat) : Int) := by omega
    rw [hdiff, packedInt_val _ (by omega), packedInt_val n hn64]
    dsimp only [extra] at *
    omega
  simp only [mutableStorage, overallocation, hctlz, hexp, hmul, shape_run_bind,
    hdiv1, hdiv2, hshift, hextra, shape_run_pure]
  change ((Except.ok (if int n > JInt.typemax .i64 - int extra then JInt.typemax .i64
    else int n + int extra) : Except Error I64), s) = _
  rw [if_neg htest, packedInt_add]
  apply congrArg (fun value => ((Except.ok (int value) : Except Error I64), s))
  unfold growthCapacity
  dsimp only [extra]
  omega

/-- Bounded natural addition succeeds in the storage callback. -/
theorem growthCheckedAdd (a b : Nat) (s : State)
    (h : a + b ≤ 9223372036854775807) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).checkedAdd (int a) (int b)).run s =
      (.ok (int ((a + b : Nat) : Int)), s) := by
  have ha := packedInt_val a (by omega)
  have hb := packedInt_val b (by omega)
  have hlow : IntTy.i64.min ≤ (a : Int) + (b : Int) := by
    change -9223372036854775808 ≤ (a : Int) + (b : Int)
    omega
  have hhigh : (a : Int) + (b : Int) ≤ IntTy.i64.max := by
    change (a : Int) + (b : Int) ≤ 9223372036854775807
    omega
  simp only [mutableStorage, ha, hb, hlow, hhigh, and_self, ite_true,
    shape_run_pure, packedInt_add, Int.natCast_add]

/-- Native maxima agree with natural maxima inside the native bound. -/
theorem growthMax (a b : Nat)
    (ha : a ≤ 9223372036854775807) (hb : b ≤ 9223372036854775807) :
    max (int a) (int b) = int ((max a b : Nat) : Int) := by
  apply Subtype.ext
  change max (int a).val (int b).val = (int ((max a b : Nat) : Int)).val
  rw [packedInt_val a ha, packedInt_val b hb, packedInt_val (max a b) (by omega)]
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

/-- Allocation growth is composed from primitive outcomes with all intermediate stores explicit. -/
theorem growthInternalPhases (st : Storage BitMutationM Nat Nat (Nat × I64))
    (s allocated copied out : State) (len delta newlen memlen capacity quarter : I64) (mem : Nat)
    (hm : st.memory (0, one) = 0) (ho : st.offset (0, one) = one)
    (hr : (st.ref 0).run s = (.ok (0, one), s))
    (hml : (st.memLength 0).run s = (.ok memlen, s))
    (hadd : (st.checkedAdd len delta).run s = (.ok newlen, s))
    (hvalid : (decide (one < one) || decide (one - one > memlen) ||
      decide (len > memlen - (one - one))) = false)
    (hadd0 : (st.checkedAdd (one - one) newlen).run s = (.ok newlen, s))
    (hdiv : (st.divide newlen (JInt.wrap .i64 4)).run s = (.ok quarter, s))
    (hfar : decide (one - one > newlen) = false)
    (hover : (st.overallocation memlen).run s = (.ok capacity, s))
    (ha : (st.allocate 0 (max capacity newlen)).run s = (.ok mem, allocated))
    (hmr : (st.memoryref mem one).run allocated = (.ok (mem, one), allocated))
    (hc : (st.copyRef (mem, one) (0, one) len).run allocated = (.ok (), copied))
    (hne : st.sameMem mem 0 = false)
    (hr' : (st.ref 0).run copied = (.ok (0, one), copied))
    (hsame : st.sameRef (0, one) (0, one) = true)
    (hset : (st.setRef 0 (mem, one)).run copied = (.ok (), out)) :
    (growendInternal st 0 delta len).run s = (.ok (), out) := by
  simp only [growendInternal, shape_run_bind, hr, hm, hml, hadd, ho, hvalid,
    Bool.false_eq_true, ite_false, hadd0, hdiv, hfar, Bool.false_and,
    hover, ha, shape_run_pure, hmr, hc, hne, hr', hsame, Bool.not_true, hset]

/-- The public chunk growth wrapper performs the internal growth then updates the visible size. -/
theorem growthOuterPhases (st : Storage BitMutationM Nat Nat (Nat × I64))
    (internal : Nat → I64 → I64 → BitMutationM Unit)
    (s mid out : State) (len delta memlen : I64)
    (hd : JuliaLean.base.array.zero ≤ delta)
    (hr : (st.ref 0).run s = (.ok (0, one), s))
    (hl : (st.length 0).run s = (.ok len, s))
    (hm : st.memory (0, one) = 0) (ho : st.offset (0, one) = one)
    (hml : (st.memLength 0).run s = (.ok memlen, s))
    (hroom : memlen - (one - one) - len < delta)
    (hi : (internal 0 delta len).run s = (.ok (), mid))
    (hsize : (st.setSize 0 (len + delta)).run mid = (.ok (), out)) :
    (growend st (fun d : I64 => pure d) internal 0 delta).run s = (.ok (), out) := by
  simp only [growend, shape_run_bind, shape_run_pure, hd, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, hr, hl, hm, ho, hml, hroom, ite_true, hi, hsize]

/-- The reference callback reads only the array header. -/
theorem growthRef (s : State) (mem : Nat) (n : I64)
    (ha : s.arrays[0]? = some ⟨(mem, one), n⟩) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).ref 0).run s = (.ok (mem, one), s) := by
  simp only [mutableStorage, mutableRef, shape_run_bind, shape_vector_run, ha, shape_run_pure]

theorem growthMemLength (s : State) (mem : Nat) (slots : List (Option U64))
    (hm : s.memories[mem]? = some slots) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).memLength mem).run s =
      (.ok (int slots.length), s) := by
  simp only [mutableStorage, shape_run_bind, growthMemoryRead s mem slots hm, shape_run_pure]
  rfl

theorem growthSetRef (s : State) (old mem : Nat) (n : I64)
    (ha : s.arrays[0]? = some ⟨(old, one), n⟩) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).setRef 0 (mem, one)).run s =
      (.ok (), {s with arrays := s.arrays.set 0 ⟨(mem, one), n⟩}) := by
  simp only [mutableStorage, shape_run_bind, shape_vector_run, ha, shape_run_modify]

theorem growthSetSize (s : State) (mem : Nat) (n k : I64)
    (ha : s.arrays[0]? = some ⟨(mem, one), n⟩) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).setSize 0 k).run s =
      (.ok (), {s with arrays := s.arrays.set 0 ⟨(mem, one), k⟩}) := by
  simp only [mutableStorage, shape_run_bind, shape_vector_run, ha, shape_run_modify]

theorem growthDivideFour (s : State) (n : I64) :
    ((mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)).divide n (JInt.wrap .i64 4)).run s =
      (.ok (JInt.wrap .i64 (n.val.tdiv 4)), s) := by rfl

/-- The new memory retains all old words, with unassigned capacity after them. -/
def growthReallocatedStore (words : List U64) (capacity n : Nat) : State :=
  ⟨[words.map some ++ List.replicate 32 none,
      words.map some ++ List.replicate (capacity - words.length) none],
    [⟨(1, one), int n⟩]⟩

/-- Growing beyond the initial spare space allocates a new memory and copies the exact old prefix. -/
theorem growthReallocateRun (words : List U64) (k : Nat)
    (hn : words.length + 32 ≤ 144115188075855872)
    (hk : k ≤ 144115188075855872) (hmore : words.length + 32 < k) :
    (growChunkVector 0 (int ((k - words.length : Nat) : Int))).run (initWords words) =
      (.ok (), growthReallocatedStore words (max (growthCapacity (words.length + 32)) k) k) := by
  let oldSlots := words.map some ++ List.replicate 32 none
  let capacity := max (growthCapacity (words.length + 32)) k
  let s := initWords words
  let allocated : State := ⟨[oldSlots, List.replicate capacity none], [⟨(0, one), int words.length⟩]⟩
  let copied : State := ⟨[oldSlots, words.map some ++ List.replicate (capacity - words.length) none],
    [⟨(0, one), int words.length⟩]⟩
  let mid := growthReallocatedStore words capacity words.length
  let out := growthReallocatedStore words capacity k
  let st : Storage BitMutationM Nat Nat (Nat × I64) :=
    mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)
  have hc := growthCapacityBounds (words.length + 32) (by omega) hn
  have hcap : capacity ≤ 576460752303423488 := by dsimp only [capacity]; omega
  have hkc : k ≤ capacity := by dsimp only [capacity]; omega
  have hwc : words.length ≤ capacity := by omega
  have hsum : (words.map some).length + (capacity - words.length) = capacity := by
    rw [List.length_map]
    omega
  have hsArray : s.arrays[0]? = some ⟨(0, one), int words.length⟩ := by
    simp only [s, initWords, MutableMemory.initial, List.length_map]
    rfl
  have hsMemory : s.memories[0]? = some oldSlots := rfl
  have hslots : oldSlots.length = words.length + 32 := by
    simp only [oldSlots, List.length_append, List.length_map, List.length_replicate]
  have hmax := growthMax (growthCapacity (words.length + 32)) k (by omega) (by omega)
  have halloc : (st.allocate 0 (max (int (growthCapacity (words.length + 32))) (int k))).run s =
      (.ok 1, allocated) := by
    rw [hmax]
    have hr := growthAllocate s 0 capacity hcap
    exact hr.trans (by
      simp only [s, initWords, MutableMemory.initial, allocated, oldSlots, List.length_map]
      rfl)
  have hcopy : (memoryMove 1 one 0 one (int words.length)).run allocated = (.ok (), copied) := by
    have hr := growthMemoryMoveFresh allocated 0 1 (words.map some) (List.replicate 32 none)
      (capacity - words.length) rfl (by rw [hsum]; rfl) (by rw [hsum]; omega)
    simpa only [List.length_map, allocated, copied, List.set_cons_succ, List.set_cons_zero] using hr
  have hcopiedArray : copied.arrays[0]? = some ⟨(0, one), int words.length⟩ := rfl
  have hmidArray : mid.arrays[0]? = some ⟨(1, one), int words.length⟩ := rfl
  have hlen : words.length + (k - words.length) = k := by omega
  have hchecked := growthCheckedAdd words.length (k - words.length) s (by omega)
  rw [hlen] at hchecked
  have hchecked0 : (st.checkedAdd (one - one) (int k)).run s = (.ok (int k), s) := by
    rw [shape_int_sub_self]
    have hr := growthCheckedAdd 0 k s (by omega)
    simpa only [Nat.zero_add, Int.natCast_zero] using hr
  have hml : (st.memLength 0).run s = (.ok (int ((words.length + 32 : Nat) : Int)), s) := by
    have hr := growthMemLength s 0 oldSlots hsMemory
    rw [hslots] at hr
    exact hr
  have hzero : one - one = int 0 := shape_int_sub_self one
  have hsub0 : int ((words.length + 32 : Nat) : Int) - int 0 =
      int ((words.length + 32 : Nat) : Int) := by rw [dequeIntSub, Int.sub_zero]
  have hmemnonneg : ¬ one - one > int ((words.length + 32 : Nat) : Int) := by
    rw [hzero]
    change ¬ (int ((words.length + 32 : Nat) : Int)).val < 0
    rw [packedInt_val _ (by omega)]
    omega
  have hfit : ¬ int words.length > int ((words.length + 32 : Nat) : Int) - (one - one) := by
    rw [hzero, hsub0]
    change ¬ (int ((words.length + 32 : Nat) : Int)).val < (int words.length).val
    rw [packedInt_val _ (by omega), packedInt_val _ (by omega)]
    omega
  have hvalid : (decide (one < one) || decide (one - one > int ((words.length + 32 : Nat) : Int)) ||
      decide (int words.length > int ((words.length + 32 : Nat) : Int) - (one - one))) = false := by
    simp only [show ¬ one < one by decide, hmemnonneg, hfit, decide_false, Bool.false_or]
  have hfar : decide (one - one > int k) = false := by
    apply decide_eq_false
    rw [hzero]
    change ¬ (int k).val < 0
    rw [packedInt_val k (by omega)]
    omega
  have hsetref : (st.setRef 0 (1, one)).run copied = (.ok (), mid) := by
    exact (growthSetRef copied 0 1 (int words.length) hcopiedArray).trans rfl
  have hinternal := growthInternalPhases st s allocated copied mid
    (int words.length) (int ((k - words.length : Nat) : Int)) (int k)
    (int ((words.length + 32 : Nat) : Int)) (int (growthCapacity (words.length + 32)))
    (JInt.wrap .i64 ((int k).val.tdiv 4)) 1 rfl rfl
    (growthRef s 0 (int words.length) hsArray) hml hchecked hvalid hchecked0
    (growthDivideFour s (int k)) hfar (growthOverallocationRun (words.length + 32) s (by omega) hn)
    halloc rfl hcopy rfl (growthRef copied 0 (int words.length) hcopiedArray) rfl hsetref
  have hnativeSum : int words.length + int ((k - words.length : Nat) : Int) = int k := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  have hsize : (st.setSize 0 (int words.length + int ((k - words.length : Nat) : Int))).run mid =
      (.ok (), out) := by
    rw [hnativeSum]
    exact (growthSetSize mid 1 (int words.length) (int k) hmidArray).trans rfl
  have hdelta : JuliaLean.base.array.zero ≤ int ((k - words.length : Nat) : Int) := by
    change 0 ≤ (int ((k - words.length : Nat) : Int)).val
    rw [packedInt_val _ (by omega)]
    omega
  have hroom : int ((words.length + 32 : Nat) : Int) - (one - one) - int words.length <
      int ((k - words.length : Nat) : Int) := by
    rw [hzero, hsub0, dequeIntSub]
    have he : ((words.length + 32 : Nat) : Int) - (words.length : Int) = 32 := by omega
    rw [he]
    change 32 < (int ((k - words.length : Nat) : Int)).val
    rw [packedInt_val _ (by omega)]
    omega
  have houter := growthOuterPhases st (growendInternal st) s mid out
    (int words.length) (int ((k - words.length : Nat) : Int))
    (int ((words.length + 32 : Nat) : Int)) hdelta
    (growthRef s 0 (int words.length) hsArray)
    (shape_length_run s (int words.length) hsArray) rfl rfl hml hroom hinternal hsize
  exact houter

/-- Arbitrary reallocation exposes a valid new header and retains the exact old word prefix. -/
theorem growthReallocatePreserves (words : List U64) (k : Nat)
    (hn : words.length + 32 ≤ 144115188075855872)
    (hk : k ≤ 144115188075855872) (hmore : words.length + 32 < k) :
    ∃ (out : State) (slots : List (Option U64)) (mem : Nat),
      (growChunkVector 0 (int ((k - words.length : Nat) : Int))).run (initWords words) = (.ok (), out) ∧
      out.arrays[0]? = some ⟨(mem, one), int k⟩ ∧
      out.memories[mem]? = some slots ∧
      k ≤ slots.length ∧ slots.length ≤ 9223372036854775807 ∧
      slots.take words.length = words.map some := by
  let capacity := max (growthCapacity (words.length + 32)) k
  let slots := words.map some ++ List.replicate (capacity - words.length) none
  have hc := growthCapacityBounds (words.length + 32) (by omega) hn
  have hkcap : k ≤ capacity := by dsimp only [capacity]; omega
  have hcap : capacity ≤ 576460752303423488 := by dsimp only [capacity]; omega
  have hlen : slots.length = capacity := by
    simp only [slots, List.length_append, List.length_map, List.length_replicate]
    omega
  refine ⟨growthReallocatedStore words capacity k, slots, 1,
    growthReallocateRun words k hn hk hmore, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hlen]
    exact hkcap
  · rw [hlen]
    omega
  · have htake : (words.map some ++ List.replicate (capacity - words.length) none).take
        (words.map some).length = words.map some := List.take_left
    simpa only [List.length_map] using htake
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

/-- Abstract suffix deletion is a word suffix removal followed by the final-word mask. -/
theorem resizeDeleteSuffixFrom (B : BitArray 1) (n rangeLength oldCount : I64)
    (s trimmed out : State)
    (hfirst : ¬ n + int 1 < int 1)
    (hnew : B.len - rangeLength = n)
    (hl : (mutableLength B.chunks).run s = (.ok oldCount, s))
    (hd : ((if numBitChunks n - oldCount < int 0 then
        deleteChunkEnd B.chunks (-(numBitChunks n - oldCount)) else pure ()) :
          BitMutationM Unit).run s = (.ok (), trimmed))
    (ht : (resizeMaskTail B.chunks n).run trimmed = (.ok (), out)) :
    (bitVectorDeleteRange (fun _ => rangeLength) B ⟨n + int 1, B.len⟩).run s =
      (.ok {B with len := n}, out) := by
  have hlast : ¬ B.len > B.len := Int.lt_irrefl _
  simp only [bitVectorDeleteRange, hfirst, hlast, ite_false, hnew,
    shape_run_bind, hl, shape_int_sub_self, resizeCopyZero, shape_run_pure]
  dsimp only [BitVector] at *
  by_cases hdlt : numBitChunks n - oldCount < int 0
  · simp only [hdlt, ite_true] at hd ⊢
    simp only [shape_run_bind, hd]
    by_cases hp : n > int 0
    · simp only [hp, ite_true]
      have he : ((do
          let last ← mutableGet B.chunks (← mutableLength B.chunks)
          mutableSet B.chunks (and_int last (maskEnd n)) (← mutableLength B.chunks)
          pure ({B with len := n} : BitArray 1)) : BitMutationM (BitArray 1)) =
          (resizeMaskTail B.chunks n >>= fun _ => pure {B with len := n}) := by
        simp only [resizeMaskTail, hp, ite_true, bind_assoc]
      rw [he, shape_run_bind, ht]
      rfl
    · simp only [resizeMaskTail, hp, ite_false, shape_run_pure] at ht
      have he : trimmed = out := congrArg Prod.snd ht
      simp only [hp, ite_false, shape_run_pure, he]
  · simp only [hdlt, ite_false, shape_run_pure] at hd ⊢
    have hs : s = trimmed := congrArg Prod.snd hd
    subst trimmed
    by_cases hp : n > int 0
    · simp only [hp, ite_true]
      have he : ((do
          let last ← mutableGet B.chunks (← mutableLength B.chunks)
          mutableSet B.chunks (and_int last (maskEnd n)) (← mutableLength B.chunks)
          pure ({B with len := n} : BitArray 1)) : BitMutationM (BitArray 1)) =
          (resizeMaskTail B.chunks n >>= fun _ => pure {B with len := n}) := by
        simp only [resizeMaskTail, hp, ite_true, bind_assoc]
      rw [he, shape_run_bind, ht]
      rfl
    · simp only [resizeMaskTail, hp, ite_false, shape_run_pure] at ht
      have he : s = out := congrArg Prod.snd ht
      simp only [hp, ite_false, shape_run_pure, he]

/-- At a fixed public range, the installed length callback can be replaced by its exact native value. -/
theorem rangeDeleteSpecializeLength (B : BitVector) (r : BitRange) :
    Round5.Round2.deleteBitRangePublic B r =
      bitVectorDeleteRange (fun _ => int 1 + (r.last - r.first)) B r := by
  rw [rangeDelete_public_eq]

/-- The canonical empty interval immediately after the final bit is an exact no-op at every supported length. -/
theorem rangeEmptyEndRun (xs : List Bool) (hn : xs.length < 9223372036854775807) :
    (Round5.Round2.deleteBitRangePublic (vectorBits xs)
      ⟨int xs.length + int 1, int xs.length⟩).run (initWords (encodeBits xs)) =
      (.ok (vectorBits xs), initWords (encodeBits xs)) := by
  let B := vectorBits xs
  let words := encodeBits xs
  let s := dequeWordStore words 32
  let count := int (wordCount xs.length : Int)
  let len := int 1 + (B.len - (B.len + int 1))
  have hfirst : ¬ B.len + int 1 < int 1 := by
    change ¬ int xs.length + int 1 < int 1
    rw [packedInt_add]
    change ¬ (int ((xs.length : Int) + 1)).val < 1
    have hv := packedInt_val (xs.length + 1) (by omega)
    simp only [Int.natCast_add, Int.natCast_one] at hv
    rw [hv]
    omega
  have hnew : B.len - len = B.len := by
    change int xs.length - (int 1 + (int xs.length - (int xs.length + int 1))) = int xs.length
    simp only [packedInt_add, dequeIntSub]
    exact congrArg int (by omega)
  have hl : (mutableLength B.chunks).run s = (.ok count, s) := by
    change (mutableLength 0).run (dequeWordStore (encodeBits xs) 32) =
      (.ok (int (wordCount xs.length : Int)), dequeWordStore (encodeBits xs) 32)
    have h := dequeWordLength (encodeBits xs) 32
    rw [packedEncoded_length] at h
    exact h
  have hd : ((if numBitChunks B.len - count < int 0 then
        deleteChunkEnd B.chunks (-(numBitChunks B.len - count)) else pure ()) : BitMutationM Unit).run s =
      (.ok (), s) := by
    change ((if numBitChunks (int xs.length) - int (wordCount xs.length : Int) < int 0 then
        deleteChunkEnd 0 (-(numBitChunks (int xs.length) - int (wordCount xs.length : Int))) else pure ()) :
          BitMutationM Unit).run s = _
    rw [resizeNumChunks xs.length (by omega), shape_int_sub_self]
    rfl
  have ht : (resizeMaskTail B.chunks B.len).run s = (.ok (), s) := by
    change (resizeMaskTail 0 (int xs.length)).run (dequeWordStore (encodeBits xs) 32) =
      (.ok (), dequeWordStore (encodeBits xs) 32)
    by_cases hp : 0 < xs.length
    · have h := resizeMaskPrefixRun xs xs.length 32 hp (Nat.le_refl _) (by omega)
      have htake : (encodeBits xs).take (wordCount xs.length) = encodeBits xs := by
        rw [← packedEncoded_length xs, List.take_length]
      simpa only [htake, List.take_length] using h
    · have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      rfl
  have hr := resizeDeleteSuffixFrom B B.len len count s s s hfirst hnew hl hd ht
  rw [rangeDeleteSpecializeLength]
  simpa only [B, s, words, len, vectorBits, dequeWordStoreInitial] using hr
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The installed copier changes the middle word even when copying the entire vector onto itself. -/
theorem rangeEmptyDiagnosticCopy :
    (copyChunks 0 (int 1) 0 (int 1) (int 129)).run
      (dequeWordStore [u64 0, u64 1, u64 0] 32) =
        (.ok (), dequeWordStore [u64 0, u64 0, u64 0] 32) := by
  rw [copyChunks]
  rfl

/-- Public deletion of the canonical empty interval 1:0 exposes the same frozen-model discrepancy. -/
theorem rangeEmptyDiagnosticPublic :
    (Round5.Round2.deleteBitRangePublic (vectorBits rangeEmptyDiagnosticBits)
      ⟨int 1, int 0⟩).run (initWords (encodeBits rangeEmptyDiagnosticBits)) =
        (.ok (vectorBits rangeEmptyDiagnosticBits), dequeWordStore [u64 0, u64 0, u64 0] 32) := by
  rw [rangeEmptyDiagnosticEncoding, ← dequeWordStoreInitial]
  rw [rangeDeleteSpecializeLength]
  unfold bitVectorDeleteRange
  simp only [copyChunks]
  rfl

/-- The canonical empty range changes its packed state in this three-word frozen execution. -/
theorem rangeEmptyDiagnosticStateChanged :
    ((Round5.Round2.deleteBitRangePublic (vectorBits rangeEmptyDiagnosticBits)
      ⟨int 1, int 0⟩).run (initWords (encodeBits rangeEmptyDiagnosticBits))).2 ≠
        initWords (encodeBits rangeEmptyDiagnosticBits) := by
  rw [rangeEmptyDiagnosticPublic, rangeEmptyDiagnosticEncoding, ← dequeWordStoreInitial]
  intro h
  have hb := congrArg (fun s : State => bitAt s (vectorBits rangeEmptyDiagnosticBits) 64) h
  change false = true at hb
  cases hb
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- The one or two destination boundary words changed by an interior suffix copy. -/
def boundaryDeleteWords (xs : List Bool) (first last : Nat) : List U64 :=
  let kept := xs.length - last
  let offset := first % 64
  let chunk := first / 64
  let low := copyPairPaste (packedPrefix xs chunk 64) (copyPairSlice xs last) offset (min kept (64 - offset))
  let lowWords := (encodeBits xs).set chunk low
  if offset + kept ≤ 64 then lowWords
  else lowWords.set (chunk + 1)
    (copyPairPaste (packedPrefix xs (chunk + 1) 64)
      (copyPairCarry (copyPairSlice xs last) (copyPairSlice xs (last + 64)) offset)
      0 (offset + kept - 64))
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

/-- The untrimmed copied buffer preserves the original number of logical storage positions. -/
theorem rangeBoundaryLength (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) :
    (rangeBoundaryBits xs first last).length = xs.length := by
  simp only [rangeBoundaryBits, List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega)]
  omega

/-- Interior copying changes precisely its destination interval and preserves all remaining old positions. -/
theorem rangeBoundaryGet (xs : List Bool) (first last bit : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) :
    (rangeBoundaryBits xs first last).getD bit false =
      if first ≤ bit ∧ bit < first + (xs.length - last) then xs.getD (last + (bit - first)) false
      else xs.getD bit false := by
  have hlen : (xs.take first ++ xs.drop last).length = first + (xs.length - last) := by
    simp only [List.length_append, List.length_take, List.length_drop, Nat.min_eq_left (show first ≤ xs.length by omega)]
  unfold rangeBoundaryBits
  by_cases hi : bit < first + (xs.length - last)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hi)]
    change (xs.take first ++ xs.drop last).getD bit false = _
    rw [rangeSingleLogicalGet xs first last bit hf hl]
    by_cases hp : bit < first
    · rw [if_pos hp, if_neg (by omega)]
    · rw [if_neg hp, if_pos (by omega)]
  · rw [if_neg (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hlen]; omega), hlen, List.getElem?_drop,
      show first + (xs.length - last) + (bit - (first + (xs.length - last))) = bit by omega]
    rfl

/-- The low boundary paste encodes every copied and preserved bit of its arbitrary destination chunk. -/
theorem rangeBoundaryLowWord (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) :
    copyPairPaste (packedPrefix xs (first / 64) 64) (copyPairSlice xs last) (first % 64)
      (min (xs.length - last) (64 - first % 64)) =
      packedPrefix (rangeBoundaryBits xs first last) (first / 64) 64 := by
  have ho : first % 64 < 64 := Nat.mod_lt first (by decide)
  have hd : first / 64 * 64 + first % 64 = first := by omega
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ _ _ bit (by omega) hb,
    packedWord_bit (rangeBoundaryBits xs first last) (first / 64) bit hb,
    rangeBoundaryGet xs first last _ hf hl]
  by_cases hi : first % 64 ≤ bit ∧ bit < first % 64 + min (xs.length - last) (64 - first % 64)
  · rw [if_pos hi, if_pos (by omega), copyPairSliceBit xs last (bit - first % 64) (by omega)]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedWord_bit xs (first / 64) bit hb]

/-- A spanning copy's high boundary word contains the carried source window followed by untouched old bits. -/
theorem rangeBoundaryHighWord (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length)
    (hp : 64 < first % 64 + (xs.length - last))
    (hn : first % 64 + (xs.length - last) ≤ 128) :
    copyPairPaste (packedPrefix xs (first / 64 + 1) 64)
      (copyPairCarry (copyPairSlice xs last) (copyPairSlice xs (last + 64)) (first % 64))
      0 (first % 64 + (xs.length - last) - 64) =
      packedPrefix (rangeBoundaryBits xs first last) (first / 64 + 1) 64 := by
  have ho : first % 64 < 64 := Nat.mod_lt first (by decide)
  have hd : first / 64 * 64 + first % 64 = first := by omega
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb,
    packedWord_bit (rangeBoundaryBits xs first last) (first / 64 + 1) bit hb,
    rangeBoundaryGet xs first last _ hf hl]
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and]
  by_cases hi : bit < first % 64 + (xs.length - last) - 64
  · rw [if_pos hi, if_pos (by omega), copyPairCarry,
      copyPairCarrySliceBit xs last (first % 64) bit (by omega) hb]
    congr 1
    omega
  · rw [if_neg hi, if_neg (by omega), packedWord_bit xs (first / 64 + 1) bit hb]

/-- Every chunk wholly outside the copied destination interval retains its exact encoded word. -/
theorem rangeBoundaryUnchangedWord (xs : List Bool) (first last chunk : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length)
    (hout : chunk * 64 + 64 ≤ first ∨ first + (xs.length - last) ≤ chunk * 64) :
    packedPrefix xs chunk 64 = packedPrefix (rangeBoundaryBits xs first last) chunk 64 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit xs chunk bit hb, packedWord_bit _ chunk bit hb,
    rangeBoundaryGet xs first last _ hf hl, if_neg (by omega)]

/-- One interior boundary write produces the exact untrimmed copied logical storage. -/
theorem rangeBoundaryOneEncoding (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last < xs.length)
    (hn : first % 64 + (xs.length - last) ≤ 64) :
    (encodeBits xs).set (first / 64)
      (copyPairPaste (packedPrefix xs (first / 64) 64) (copyPairSlice xs last) (first % 64)
        (min (xs.length - last) (64 - first % 64))) =
      encodeBits (rangeBoundaryBits xs first last) := by
  have ho : first % 64 < 64 := Nat.mod_lt first (by decide)
  have hd : first / 64 * 64 + first % 64 = first := by omega
  have hw : first / 64 < wordCount xs.length := by unfold wordCount; omega
  apply List.ext_getElem
  · simp only [List.length_set, packedEncoded_length, rangeBoundaryLength xs first last hf (by omega)]
  · intro chunk hj hj'
    have hb : chunk < wordCount xs.length := by simpa only [List.length_set, packedEncoded_length] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ (first / 64) chunk _ (by rw [packedEncoded_length]; exact hw),
      shiftNearLeftEncodedGet (rangeBoundaryBits xs first last) chunk
        (by rw [rangeBoundaryLength xs first last hf (by omega)]; exact hb)]
    by_cases he : chunk = first / 64
    · subst chunk
      rw [if_pos rfl]
      exact rangeBoundaryLowWord xs first last hf (by omega)
    · rw [if_neg (by omega), shiftNearLeftEncodedGet xs chunk hb]
      apply rangeBoundaryUnchangedWord xs first last chunk hf (by omega)
      by_cases hc : chunk < first / 64
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

/-- Two interior boundary writes produce exactly the copied logical storage across an arbitrary destination boundary. -/
theorem rangeBoundaryTwoEncoding (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last < xs.length)
    (hp : 64 < first % 64 + (xs.length - last))
    (hn : first % 64 + (xs.length - last) ≤ 128) :
    ((encodeBits xs).set (first / 64)
      (copyPairPaste (packedPrefix xs (first / 64) 64) (copyPairSlice xs last) (first % 64)
        (min (xs.length - last) (64 - first % 64)))).set (first / 64 + 1)
      (copyPairPaste (packedPrefix xs (first / 64 + 1) 64)
        (copyPairCarry (copyPairSlice xs last) (copyPairSlice xs (last + 64)) (first % 64))
        0 (first % 64 + (xs.length - last) - 64)) =
      encodeBits (rangeBoundaryBits xs first last) := by
  have ho : first % 64 < 64 := Nat.mod_lt first (by decide)
  have hd : first / 64 * 64 + first % 64 = first := by omega
  have hw : first / 64 + 1 < wordCount xs.length := by unfold wordCount; omega
  apply List.ext_getElem
  · simp only [List.length_set, packedEncoded_length, rangeBoundaryLength xs first last hf (by omega)]
  · intro chunk hj hj'
    have hb : chunk < wordCount xs.length := by simpa only [List.length_set, packedEncoded_length] using hj
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ (first / 64 + 1) chunk _ (by simp only [List.length_set, packedEncoded_length]; exact hw),
      shiftNearLeftEncodedGet (rangeBoundaryBits xs first last) chunk
        (by rw [rangeBoundaryLength xs first last hf (by omega)]; exact hb)]
    by_cases he : chunk = first / 64 + 1
    · subst chunk
      rw [if_pos rfl]
      exact rangeBoundaryHighWord xs first last hf (by omega) hp hn
    · rw [if_neg (by omega), dequeWordGetSet _ (first / 64) chunk _ (by rw [packedEncoded_length]; omega)]
      by_cases he' : chunk = first / 64
      · subst chunk
        rw [if_pos rfl]
        exact rangeBoundaryLowWord xs first last hf (by omega)
      · rw [if_neg (by omega), shiftNearLeftEncodedGet xs chunk hb]
        apply rangeBoundaryUnchangedWord xs first last chunk hf (by omega)
        by_cases hc : chunk < first / 64
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)

/-- The exact boundary-only word update encodes the complete copied storage before canonical trimming. -/
theorem boundaryDeleteEncoding (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last < xs.length)
    (hn : first % 64 + (xs.length - last) ≤ 128) :
    boundaryDeleteWords xs first last = encodeBits (rangeBoundaryBits xs first last) := by
  unfold boundaryDeleteWords
  by_cases hs : first % 64 + (xs.length - last) ≤ 64
  · rw [if_pos hs]
    exact rangeBoundaryOneEncoding xs first last hf hl hs
  · rw [if_neg hs]
    exact rangeBoundaryTwoEncoding xs first last hf hl (by omega) hn
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

/-- Every nonempty suffix has its first exact logical window under the installed source mask. -/
theorem rangeBoundaryFirstGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hr : ∀ chunk, chunk < wordCount xs.length →
      (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s)) :
    (glueSrcBitChunks chunks (int ((source / 64 + 1 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
      (copyPairSourceMask (int ((source / 64 + 1 : Nat) : Int))
        (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
        (int ((source % 64 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int)))
      (int ((source % 64 : Nat) : Int))).run s = (.ok (copyPairSlice xs source), s) := by
  by_cases hshort : xs.length - source ≤ 64
  · exact shiftNearGatherRun xs source chunks s hn hs hshort hr
  · rw [shiftWindowSourceMask xs source hn hs (by omega)]
    exact shiftWindowHighGatherRun xs source chunks s hn hs hr

/-- The optional following gather is the zero-padded next window, including short suffixes and overlap-safe read callbacks. -/
theorem rangeBoundaryNextGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hr : ∀ chunk, source / 64 + 1 ≤ chunk → chunk < wordCount xs.length →
      (mutableGet chunks (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s)) :
    ((if int (((xs.length - 1) / 64 + 1 : Nat) : Int) ≥ int ((source / 64 + 1 : Nat) : Int) + int 1 then
      glueSrcBitChunks chunks (int ((source / 64 + 1 : Nat) : Int) + int 1)
        (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
        (copyPairSourceMask (int ((source / 64 + 1 : Nat) : Int))
          (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
          (int ((source % 64 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int)))
        (int ((source % 64 : Nat) : Int)) else pure (u64 0)) : BitMutationM U64).run s =
      (.ok (copyPairSlice xs (source + 64)), s) := by
  let chunk := source / 64
  let last := (xs.length - 1) / 64
  let offset := source % 64
  have hoff : offset < 64 := Nat.mod_lt _ (by decide)
  have hsource : source = chunk * 64 + offset := by dsimp only [chunk, offset]; omega
  have hcount : wordCount xs.length = last + 1 := by unfold wordCount; dsimp only [last]; omega
  have horder : chunk ≤ last := by dsimp only [chunk, last]; omega
  have hplus : int ((chunk + 1 : Nat) : Int) + int 1 = int ((chunk + 2 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  change ((if int ((last + 1 : Nat) : Int) ≥ int ((chunk + 1 : Nat) : Int) + int 1 then
      glueSrcBitChunks chunks (int ((chunk + 1 : Nat) : Int) + int 1) (int ((last + 1 : Nat) : Int))
        (copyPairSourceMask (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
          (int offset) (int (((xs.length - 1) % 64 : Nat) : Int))) (int offset)
      else pure (u64 0)) : BitMutationM U64).run s = _
  rw [hplus]
  by_cases he : last = chunk
  · have hnot : ¬ int ((last + 1 : Nat) : Int) ≥ int ((chunk + 2 : Nat) : Int) := by
      change ¬ (int ((chunk + 2 : Nat) : Int)).val ≤ (int ((last + 1 : Nat) : Int)).val
      rw [packedInt_val (chunk + 2) (by dsimp only [chunk]; omega),
        packedInt_val (last + 1) (by dsimp only [last]; omega)]
      omega
    rw [if_neg hnot, shape_run_pure]
    have hz : copyPairSlice xs (source + 64) = u64 0 := by
      apply packedBit_ext
      intro bit hb
      rw [copyPairSliceBit xs _ bit hb, packedBit_zero, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by dsimp only [chunk, last] at he; omega), Option.getD_none]
    rw [hz]
  · have hgt : chunk < last := by omega
    have hyes : int ((last + 1 : Nat) : Int) ≥ int ((chunk + 2 : Nat) : Int) := by
      change (int ((chunk + 2 : Nat) : Int)).val ≤ (int ((last + 1 : Nat) : Int)).val
      rw [packedInt_val (chunk + 2) (by dsimp only [chunk]; omega),
        packedInt_val (last + 1) (by dsimp only [last]; omega)]
      omega
    have hdelta : int ((last + 1 : Nat) : Int) - int ((chunk + 1 : Nat) : Int) =
        int ((last - chunk : Nat) : Int) := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    have hmask : copyPairSourceMask (int ((chunk + 1 : Nat) : Int)) (int ((last + 1 : Nat) : Int))
        (int offset) (int (((xs.length - 1) % 64 : Nat) : Int)) = shl_int u64Max (int offset) := by
      rw [copyPairSourceMask, hdelta,
        fillPositiveLength (last - chunk) (by omega) (by dsimp only [last]; omega)]
      rfl
    rw [if_pos hyes, hmask]
    by_cases hnext : source + 64 < xs.length
    · have h := prefixDeleteHighGatherRun xs (source + 64) chunks s hn hnext (by
        intro j hlo hhi
        exact hr j (by omega) hhi)
      simpa only [show (source + 64) / 64 + 1 = chunk + 2 by dsimp only [chunk]; omega,
        show (source + 64) % 64 = offset by dsimp only [offset]; omega] using h
    · have heq : last = chunk + 1 := by dsimp only [last, chunk] at *; omega
      have hread := hr last (by dsimp only [chunk] at heq; omega) (by rw [hcount]; omega)
      have h := shiftNearGlueLastRun chunks (int ((last + 1 : Nat) : Int)) (int offset)
        (shl_int u64Max (int offset)) (packedPrefix xs last 64) s hread
      rw [shiftWindowTailSlice xs last offset hoff (by dsimp only [last]; omega)] at h
      have hpos : last * 64 + offset = source + 64 := by omega
      rw [hpos] at h
      simpa only [heq, show chunk + 1 + 1 = chunk + 2 by omega] using h

/-- Every in-place suffix copy spanning at most two destination words has exact boundary writes, including overlap. -/
theorem boundaryDeleteCopyRun (xs : List Bool) (first last spare : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hf : first ≤ last) (hl : last < xs.length)
    (hk : first % 64 + (xs.length - last) ≤ 128) :
    (copyChunks 0 (int ((first + 1 : Nat) : Int)) 0 (int ((last + 1 : Nat) : Int))
      (int ((xs.length - last : Nat) : Int))).run (dequeWordStore (encodeBits xs) spare) =
      (.ok (), dequeWordStore (boundaryDeleteWords xs first last) spare) := by
  let words := encodeBits xs
  let kept := xs.length - last
  let chunk := first / 64
  let offset := first % 64
  let low := copyPairPaste (packedPrefix xs chunk 64) (copyPairSlice xs last) offset
    (min kept (64 - offset))
  let high := copyPairPaste (packedPrefix xs (chunk + 1) 64)
    (copyPairCarry (copyPairSlice xs last) (copyPairSlice xs (last + 64)) offset)
    0 (offset + kept - 64)
  let lowWords := words.set chunk low
  let s := dequeWordStore words spare
  let middle := dequeWordStore lowWords spare
  have hmod : offset < 64 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div first 64
  have hkept : 0 < kept := by dsimp only [kept]; omega
  have hnew : first + kept ≤ xs.length := by dsimp only [kept]; omega
  have hwords : words.length = wordCount xs.length := packedEncoded_length xs
  have hnwords : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hchunk : chunk < words.length := by
    rw [hwords]
    dsimp only [chunk]
    unfold wordCount
    omega
  have hrs : ∀ j, j < wordCount xs.length →
      (mutableGet 0 (int ((j + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs j 64), s) := by
    intro j hj
    have h := dequeWordRead words spare j hnwords (by rw [hwords]; exact hj)
    rw [shiftNearLeftEncodedGet xs j hj] at h
    exact h
  have hr0 := hrs chunk (by rw [← hwords]; exact hchunk)
  have hg := rangeBoundaryFirstGatherRun xs last 0 s hn hl hrs
  have hw0 := dequeWordSet words spare chunk low hnwords hchunk
  have hforward : ¬ (0 = (0 : Nat) ∧ int ((first + 1 : Nat) : Int) > int ((last + 1 : Nat) : Int)) := by
    intro h
    have hv : (int ((last + 1 : Nat) : Int)).val < (int ((first + 1 : Nat) : Int)).val := h.2
    rw [packedInt_val (last + 1) (by omega), packedInt_val (first + 1) (by omega)] at hv
    omega
  have hendS : int ((last + 1 : Nat) : Int) + int kept - int 1 = int xs.length := by
    rw [packedInt_add, dequeIntSub]
    apply congrArg int
    dsimp only [kept]
    omega
  have hendD : int ((first + 1 : Nat) : Int) + int kept - int 1 = int ((first + kept : Nat) : Int) := by
    rw [packedInt_add, dequeIntSub]
    exact congrArg int (by omega)
  have hs0 := scalar_chunks_nat last (by omega)
  have hs1 : getChunksId (int ((last + 1 : Nat) : Int) + int kept - int 1) =
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int), int (((xs.length - 1) % 64 : Nat) : Int)) := by
    rw [hendS]
    have h := scalar_chunks_nat (xs.length - 1) (by omega)
    simpa only [show xs.length - 1 + 1 = xs.length by omega] using h
  have hd0 : getChunksId (int ((first + 1 : Nat) : Int)) =
      (int ((chunk + 1 : Nat) : Int), int offset) := scalar_chunks_nat first (by omega)
  have hfinal := scalar_chunks_nat (first + kept - 1) (by omega)
  rw [show first + kept - 1 + 1 = first + kept by omega] at hfinal
  by_cases hsmall : offset + kept ≤ 64
  · have hmin : min kept (64 - offset) = kept := Nat.min_eq_left (by omega)
    have heLow : low = copyPairPaste (packedPrefix xs chunk 64) (copyPairSlice xs last) offset kept := by
      change copyPairPaste _ _ _ (min kept (64 - offset)) = _
      rw [hmin]
    have hd1 : getChunksId (int ((first + 1 : Nat) : Int) + int kept - int 1) =
        (int ((chunk + 1 : Nat) : Int), int ((offset + kept - 1 : Nat) : Int)) := by
      rw [hendD, hfinal]
      have hq : (first + kept - 1) / 64 = chunk := by dsimp only [chunk, offset] at *; omega
      have hm : (first + kept - 1) % 64 = offset + kept - 1 := by dsimp only [chunk, offset] at *; omega
      rw [hq, hm]
    have hr := copyPairOneRun 0 0 _ _ kept offset (int ((chunk + 1 : Nat) : Int))
      (int ((last / 64 + 1 : Nat) : Int)) (int ((last % 64 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int))
      s middle (packedPrefix xs chunk 64) (copyPairSlice xs last) hkept hsmall hforward hd0 hd1 hs0 hs1 hg hr0
      (by rw [← heLow]; exact hw0)
    exact hr.trans (by
      rw [boundaryDeleteWords, if_pos (show first % 64 + (xs.length - last) ≤ 64 from hsmall)])
  · have hcross : 64 < offset + kept := by omega
    have hmin : min kept (64 - offset) = 64 - offset := Nat.min_eq_right (by omega)
    have heLow : low = copyPairPaste (packedPrefix xs chunk 64) (copyPairSlice xs last) offset (64 - offset) := by
      change copyPairPaste _ _ _ (min kept (64 - offset)) = _
      rw [hmin]
    have hchunk1 : chunk + 1 < words.length := by
      rw [hwords]
      dsimp only [chunk, offset] at *
      unfold wordCount
      omega
    have hrsm : ∀ j, last / 64 + 1 ≤ j → j < wordCount xs.length →
        (mutableGet 0 (int ((j + 1 : Nat) : Int))).run middle = (.ok (packedPrefix xs j 64), middle) := by
      intro j hjlo hjhi
      have h := dequeWordRead lowWords spare j (by rw [List.length_set]; exact hnwords)
        (by rw [List.length_set, hwords]; exact hjhi)
      have he : lowWords.getD j (u64 0) = packedPrefix xs j 64 := by
        rw [dequeWordGetSet words chunk j low hchunk, if_neg (by dsimp only [chunk]; omega)]
        exact shiftNearLeftEncodedGet xs j hjhi
      rw [he] at h
      exact h
    have hnext := rangeBoundaryNextGatherRun xs last 0 middle hn hl hrsm
    have hr1 : (mutableGet 0 (int ((chunk + 1 + 1 : Nat) : Int))).run middle =
        (.ok (packedPrefix xs (chunk + 1) 64), middle) := by
      have h := dequeWordRead lowWords spare (chunk + 1) (by rw [List.length_set]; exact hnwords)
        (by rw [List.length_set]; exact hchunk1)
      have he : lowWords.getD (chunk + 1) (u64 0) = packedPrefix xs (chunk + 1) 64 := by
        rw [dequeWordGetSet words chunk (chunk + 1) low hchunk, if_neg (by omega)]
        exact shiftNearLeftEncodedGet xs (chunk + 1) (by rw [← hwords]; exact hchunk1)
      rw [he] at h
      exact h
    have hw1 := dequeWordSet lowWords spare (chunk + 1) high
      (by rw [List.length_set]; exact hnwords) (by rw [List.length_set]; exact hchunk1)
    have hdiff : int ((chunk + 1 + 1 : Nat) : Int) - int ((chunk + 1 : Nat) : Int) = int 1 := by
      rw [dequeIntSub]
      exact congrArg int (by omega)
    have hd1 : getChunksId (int ((first + 1 : Nat) : Int) + int kept - int 1) =
        (int ((chunk + 1 + 1 : Nat) : Int), int ((offset + kept - 64 - 1 : Nat) : Int)) := by
      rw [hendD, hfinal]
      have hq : (first + kept - 1) / 64 = chunk + 1 := by dsimp only [chunk, offset, kept] at *; omega
      have hm : (first + kept - 1) % 64 = offset + kept - 64 - 1 := by dsimp only [chunk, offset, kept] at *; omega
      rw [hq, hm]
    have hr := shiftNearTwoRun 0 0 _ _ (int kept) offset (offset + kept - 64)
      (int ((chunk + 1 : Nat) : Int)) (int ((chunk + 1 + 1 : Nat) : Int))
      (int ((last / 64 + 1 : Nat) : Int)) (int ((last % 64 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int))
      s middle _ (packedPrefix xs chunk 64) (packedPrefix xs (chunk + 1) 64)
      (copyPairSlice xs last) (copyPairSlice xs (last + 64))
      (by omega) (by omega) (by dsimp only [offset, kept] at *; omega)
      (fillPositiveLength kept hkept (by dsimp only [kept]; omega)) hforward hdiff hd0 hd1 hs0 hs1 hg hr0
      (by rw [← heLow]; exact hw0) hnext hr1 hw1
    exact hr.trans (by
      rw [boundaryDeleteWords, if_neg (show ¬ first % 64 + (xs.length - last) ≤ 64 from hsmall)])

/-- The logical full-length buffer of a same-position suffix copy is the original sequence. -/
theorem rangeBoundaryEmptyBits (xs : List Bool) (p : Nat) (hp : p ≤ xs.length) :
    rangeBoundaryBits xs p p = xs := by
  simp only [rangeBoundaryBits, List.take_append_drop,
    show p + (xs.length - p) = xs.length by omega, List.drop_length, List.append_nil]

/-- A boundary-only same-position suffix copy preserves the complete canonical packed state. -/
theorem rangeBoundaryEmptyCopyRun (xs : List Bool) (p spare : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hp : p < xs.length)
    (hk : p % 64 + (xs.length - p) ≤ 128) :
    (copyChunks 0 (int ((p + 1 : Nat) : Int)) 0 (int ((p + 1 : Nat) : Int))
      (int ((xs.length - p : Nat) : Int))).run (dequeWordStore (encodeBits xs) spare) =
        (.ok (), dequeWordStore (encodeBits xs) spare) := by
  have h := boundaryDeleteCopyRun xs p p spare hn (Nat.le_refl _) hp hk
  rw [boundaryDeleteEncoding xs p p (Nat.le_refl _) hp hk,
    rangeBoundaryEmptyBits xs p (by omega)] at h
  exact h
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Pasting the complete partial last word into zero preserves exactly its canonical zero padding. -/
theorem frontLastPasteIntoZero (xs : List Bool) (hr : xs.length % 64 ≠ 0) :
    copyPairPaste (u64 0) (packedPrefix xs ((xs.length - 1) / 64) 64) 0 (xs.length % 64) =
      packedPrefix xs ((xs.length - 1) / 64) 64 := by
  have hm : xs.length % 64 < 64 := Nat.mod_lt xs.length (by decide)
  have hc := frontLastPackedClip xs hr
  apply packedBit_ext
  intro bit hb
  rw [copyPairPasteBit _ _ 0 _ bit (by omega) hb]
  by_cases hi : bit < xs.length % 64
  · rw [if_pos (by omega), Nat.sub_zero]
  · rw [if_neg (by omega), packedBit_zero]
    have he := congrArg (fun word => packedBit word bit) hc
    rw [resizeFrontPairClipBit _ _ bit (by omega) hb, if_neg hi] at he
    exact he
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096

/-- Circular shift computes a remainder modulo the empty length. -/
theorem circshift_empty_zero_error :
    (Round2.bitVectorCircshiftPublic (vectorBits [])
      (⟨1, int 0, [int 0]⟩ : BitVector) (int 0)).run (initWords []) =
        (.error .divide, initWords []) := by
  rfl
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Shared chunk storage gives identical public storage identities across ranks. -/
theorem metadata_dataids_alias {N M : Nat} (A : BitArray N) (B : BitArray M)
    (h : A.chunks = B.chunks) : Round5.dataIdsPublic A = Round5.dataIdsPublic B := by
  simp only [Round5.dataIdsPublic, bitArrayDataIds, h]

/-- The installed scalar bounds check depends only on the logical length. -/
theorem metadata_bounds_alias {N M : Nat} (A : BitArray N) (B : BitArray M)
    (i : I64) (hlen : A.len = B.len) :
    Round5.Round2.checkBitArrayBounds A i = Round5.Round2.checkBitArrayBounds B i := by
  simp only [Round5.Round2.checkBitArrayBounds,
    JuliaLean.base.abstractarray.checkboundsOne,
    JuliaLean.base.abstractarray.eachindexLinear, bind, Except.bind]
  rw [hlen]

/-- All reads through two aliases agree, including error outcomes and states. -/
theorem metadata_read_alias {N M : Nat} (A : BitArray N) (B : BitArray M)
    (i : I64) (hlen : A.len = B.len) (hchunks : A.chunks = B.chunks) :
    bitArrayGetIndex Round5.Round2.checkBitArrayBounds A i =
      bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i := by
  unfold bitArrayGetIndex
  rw [metadata_bounds_alias A B i hlen, hchunks]

/-- Successful rank-changing reshape exposes the original chunk handle and length. -/
theorem metadata_reshape_run {N M : Nat}
    (checked : List I64 → BitMutationM I64)
    (allocate : List I64 → BitMutationM (BitArray M))
    (B : BitArray N) (dims : List I64) (hdims : dims.length = M)
    (fresh : BitArray M) (s outState : State)
    (hchecked : (checked dims).run s = (.ok B.len, s))
    (hallocate : (allocate (List.replicate M (int 0))).run s = (.ok fresh, outState)) :
    (bitArrayReshapeAny checked allocate B dims hdims).run s =
      (.ok (⟨B.chunks, B.len, if M != 1 then dims else [B.len]⟩ : BitArray M), outState) := by
  have hne : (B.len != B.len) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := bne_iff_ne.mp h
    exact this rfl
  simp only [bitArrayReshapeAny, bitArrayReshapeInternal, shape_run_bind,
    hchecked, hne, Bool.false_eq_true, ite_false, hallocate, shape_run_pure]

/-- The returned reshape header has the public length and ranked dimensions. -/
theorem metadata_reshape_observations {N M : Nat} (B : BitArray N) (dims : List I64) :
    let output : BitArray M := ⟨B.chunks, B.len, if M != 1 then dims else [B.len]⟩
    bitArrayLength output = B.len ∧
    bitArraySizeRanked output = (if M = 1 then [B.len] else dims) ∧
    Round5.dataIdsPublic output = Round5.dataIdsPublic B := by
  dsimp only
  refine ⟨rfl, ?_, rfl⟩
  unfold bitArraySizeRanked
  by_cases hm : M = 1
  · simp only [hm, beq_self_eq_true, Bool.not_true, ite_true]
  · have hne : (M != 1) = true := bne_iff_ne.mpr hm
    simp only [hm, hne, ite_false, ite_true]
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A state-preserving operation may either return a value or raise an error. -/
def metadataReadOnly {α : Type} (action : BitMutationM α) : Prop :=
  ∀ s, (action.run s).2 = s

theorem metadataReadOnlyPure {α : Type} (x : α) :
    metadataReadOnly (pure x : BitMutationM α) := by
  intro s
  rfl

theorem metadataReadOnlyBind {α β : Type} (action : BitMutationM α)
    (next : α → BitMutationM β) (ha : metadataReadOnly action)
    (hn : ∀ x, metadataReadOnly (next x)) : metadataReadOnly (action >>= next) := by
  intro s
  rw [shape_run_bind]
  cases h : action.run s with
  | mk result state =>
    have hs : state = s := by simpa only [h] using ha s
    subst state
    cases result with
    | error e => rfl
    | ok x => exact hn x s

/-- Checked multiplication performs no store reads or writes in either outcome. -/
theorem metadataCheckedMultiplyReadOnly (a b : I64) :
    metadataReadOnly (checkedMultiplyMutation a b) := by
  intro s
  cases h : JuliaLean.base.checked.checkedMulBits a b with
  | ok value =>
    simp only [checkedMultiplyMutation, h, shape_run_pure]
  | error e =>
    simp only [checkedMultiplyMutation, h]
    rfl

theorem metadataCheckedLoopReadOnly (dims : List I64) (product : I64) :
    metadataReadOnly
      (forIn dims product (fun dim value => do
        let value ← checkedMultiplyMutation value dim
        pure (ForInStep.yield value))) := by
  induction dims generalizing product with
  | nil => exact metadataReadOnlyPure product
  | cons dim dims ih =>
    rw [List.forIn_cons]
    apply metadataReadOnlyBind
    · apply metadataReadOnlyBind
      · exact metadataCheckedMultiplyReadOnly product dim
      · intro value
        exact metadataReadOnlyPure (ForInStep.yield value)
    · intro step
      cases step with
      | done value => exact metadataReadOnlyPure value
      | yield value => exact ih value

/-- Successful dimension checking retains the incoming mutable state. -/
theorem metadataCheckedDimensionsReadOnly (dims : List I64) :
    metadataReadOnly (checkedDimensionsModel dims) := by
  unfold checkedDimensionsModel
  apply metadataReadOnlyBind
  · exact metadataCheckedLoopReadOnly dims (int 1)
  · exact metadataReadOnlyPure

theorem metadataCheckedDimensionsRun (dims : List I64) (s : State) (n : I64)
    (h : ((checkedDimensionsModel dims).run s).1 = .ok n) :
    (checkedDimensionsModel dims).run s = (.ok n, s) := by
  apply Prod.ext
  · exact h
  · exact metadataCheckedDimensionsReadOnly dims s

/-- The loop over zero dimensions has a zero product after the first factor. -/
theorem metadataZeroProductLoop (n : Nat) (s : State) :
    (forIn (List.replicate n (int 0)) (int 0) (fun dim value => do
      let value ← checkedMultiplyMutation value dim
      pure (ForInStep.yield value))).run s = (.ok (int 0), s) := by
  have hzero : (checkedMultiplyMutation (int 0) (int 0)).run s = (.ok (int 0), s) := rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.forIn_cons, shape_run_bind, hzero, shape_run_pure]
    exact ih

theorem metadataCheckedZeroDimensions (n : Nat) (s : State) :
    (checkedDimensionsModel (List.replicate (n + 1) (int 0))).run s = (.ok (int 0), s) := by
  have hfirst : (checkedMultiplyMutation (int 1) (int 0)).run s = (.ok (int 0), s) := rfl
  simp only [checkedDimensionsModel, List.replicate_succ, List.forIn_cons,
    shape_run_bind, hfirst, shape_run_pure, metadataZeroProductLoop]

/-- The nonnegative-dimension validation loop changes only its local counter. -/
theorem metadataZeroValidationLoop (n : Nat) (i : I64) (s : State) :
    ∃ j,
      (forIn (List.replicate n (int 0)) i (fun (d index : I64) => do
        if d.val < 0 then
          throw (Error.argument s!"dimension size must be ≥ 0, got {d.val} for dimension {index.val}")
        pure (ForInStep.yield (index + int 1))) : BitMutationM I64).run s = (.ok j, s) := by
  induction n generalizing i with
  | zero => exact ⟨i, rfl⟩
  | succ n ih =>
    obtain ⟨j, hj⟩ := ih (i + int 1)
    refine ⟨j, ?_⟩
    simp only [List.replicate_succ, List.forIn_cons,
      show ¬ (int 0).val < 0 by decide, ite_false, shape_run_pure]
    exact hj

/-- Zero-rank temporary construction initializes its sole new word. -/
theorem metadataAllocateRankZero (words : List U64) :
    (allocateBitArrayModel (N := 0) []).run (initWords words) =
      (.ok ⟨1, int 1, []⟩,
        ⟨(initWords words).memories ++ [[some (u64 0)]],
          (initWords words).arrays ++ [⟨(1, one), int 1⟩]⟩) := by
  rfl

/-- Construction with a positive rank and zero dimensions allocates no visible words. -/
theorem metadataAllocatePositiveRank (M : Nat) (words : List U64) :
    (allocateBitArrayModel (N := M + 1) (List.replicate (M + 1) (int 0))).run
      (initWords words) =
      (.ok ⟨1, int 0, List.replicate (M + 1) (int 0)⟩,
        ⟨(initWords words).memories ++ [[]],
          (initWords words).arrays ++ [⟨(1, one), int 0⟩]⟩) := by
  obtain ⟨j, hj⟩ := metadataZeroValidationLoop (M + 1) (int 1) (initWords words)
  simp only [allocateBitArrayModel, BitArrayUndef, shape_run_bind, hj,
    metadataCheckedZeroDimensions, show numBitChunks (int 0) = int 0 by rfl,
    show (int 0).val.toNat = 0 by rfl]
  rw [metadataAllocateZero]
  rfl

/-- Every temporary reshape allocation keeps the original memory and array header. -/
theorem metadataAllocatePreserves (M : Nat) (words : List U64) :
    ∃ (fresh : BitArray M) (s' : State),
      (Round5.Round2.allocateBitArrayModel (N := M) (List.replicate M (int 0))).run
        (initWords words) = (.ok fresh, s') ∧
      s'.arrays[0]? = some ⟨(0, one), int (words.map some).length⟩ ∧
      s'.memories[0]? = some (words.map some ++ List.replicate 32 none) := by
  cases M with
  | zero =>
    refine ⟨_, _, metadataAllocateRankZero words, ?_, ?_⟩ <;> rfl
  | succ M =>
    refine ⟨_, _, metadataAllocatePositiveRank M words, ?_, ?_⟩ <;> rfl
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

private theorem metadata_scalar_oneTo_check (n i : I64) (hn : 0 ≤ n.val) :
    JuliaLean.base.abstractarray.checkindexOneTo n i =
      decide (int 1 ≤ i ∧ i ≤ n) := by
  apply Bool.eq_iff_iff.mpr
  simp only [JuliaLean.base.abstractarray.checkindexOneTo, decide_eq_true_eq]
  change (wrapInt .u64 (wrapInt .i64 (i.val - wrapInt .i64 1)) <
    wrapInt .u64 n.val ↔ 1 ≤ i.val ∧ i.val ≤ n.val)
  have hi := i.property
  have hb := n.property
  simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi hb ⊢
  omega

theorem metadata_scalar_bounds_run {N : Nat} (B : BitArray N) (i : I64)
    (s : State) (hn : 0 ≤ B.len.val) :
    (Round5.Round2.checkBitArrayBounds B i).run s =
      (if int 1 ≤ i ∧ i ≤ B.len then (.ok (), s) else (.error .bounds, s)) := by
  have hc := metadata_scalar_oneTo_check B.len i hn
  unfold Round5.Round2.checkBitArrayBounds
  simp only [JuliaLean.base.abstractarray.eachindexLinear,
    JuliaLean.base.abstractarray.checkboundsOne, bind, pure, Except.bind, Except.pure]
  rw [hc]
  by_cases h : int 1 ≤ i ∧ i ≤ B.len
  · simp only [h, and_self, decide_true, ite_true]
    rfl
  · simp only [h, decide_false, ite_false]
    rfl

theorem metadata_scalar_div64_val (i : I64) : (div64 i).val = i.val / 64 := by
  rw [div64, JuliaLean.Proofs.base.int.ashr_int_val (by rfl)]
  rfl

theorem metadata_scalar_mod64_val (i : I64) : (mod64 i).val = i.val % 64 := by
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

theorem metadata_scalar_chunks_id (i : I64) (hi : int 1 ≤ i) :
    (getChunksId i).1.val = (i.val - 1) / 64 + 1 ∧
    (getChunksId i).2.val = (i.val - 1) % 64 := by
  have hb := i.property
  change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hb
  have hip : 1 ≤ i.val := hi
  have hs : (i - int 1).val = i.val - 1 := by
    change wrapInt .i64 (i.val - 1) = i.val - 1
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ i.val - 1 ∧ i.val - 1 ≤ 9223372036854775807
    omega
  constructor
  · change wrapInt .i64 ((div64 (i - int 1)).val + 1) = _
    rw [metadata_scalar_div64_val, hs]
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ (i.val - 1) / 64 + 1 ∧
      (i.val - 1) / 64 + 1 ≤ 9223372036854775807
    omega
  · exact (metadata_scalar_mod64_val (i - int 1)).trans (congrArg (fun z : Int => z % 64) hs)

theorem metadata_scalar_chunks_nat (i : Nat) (hi : i + 1 ≤ 9223372036854775807) :
    getChunksId (int ((i + 1 : Nat) : Int)) =
      (int ((i / 64 + 1 : Nat) : Int), int ((i % 64 : Nat) : Int)) := by
  have hv := packedInt_val (i + 1) hi
  have h := metadata_scalar_chunks_id (int ((i + 1 : Nat) : Int)) (by
    change 1 ≤ (int ((i + 1 : Nat) : Int)).val
    rw [hv]
    omega)
  rw [hv] at h
  apply Prod.ext
  · apply Subtype.ext
    rw [h.1, packedInt_val (i / 64 + 1) (by omega)]
    omega
  · apply Subtype.ext
    rw [h.2, packedInt_val (i % 64) (by omega)]
    omega

theorem metadata_scalar_internal_read_run (s : State) (chunks : Nat) (i chunk bit : I64)
    (word : U64) (ha : getChunksId i = (chunk, bit))
    (hg : (mutableGet chunks chunk).run s = (.ok word, s)) :
    (unsafeBitGetIndex chunks i).run s =
      (.ok (and_int word (shl_int (u64 1) bit) != u64 0), s) := by
  simp only [unsafeBitGetIndex, ha, shape_run_bind, hg, shape_run_pure]

theorem metadata_scalar_internal_write_run (s s' : State) (chunks : Nat) (i chunk bit : I64)
    (word : U64) (value : Bool) (ha : getChunksId i = (chunk, bit))
    (hg : (mutableGet chunks chunk).run s = (.ok word, s))
    (hs : (mutableSet chunks
      (if value then or_int word (shl_int (u64 1) bit)
       else and_int word (not_int (shl_int (u64 1) bit))) chunk).run s = (.ok (), s')) :
    (unsafeBitSetIndex chunks value i).run s = (.ok (), s') := by
  simp only [unsafeBitSetIndex, unsafeBitSetIndexAt, ha, shape_run_bind, hg, hs]

/-- The original chunk vector occupies the first array and first memory object. -/
def metadataStoredWords (words : List U64) (s : State) : Prop :=
  s.arrays[0]? = some ⟨(0, one), int words.length⟩ ∧
  s.memories[0]? = some (words.map some ++ List.replicate 32 none)

theorem metadataStoredWordsInitial (words : List U64) :
    metadataStoredWords words (initWords words) := by
  constructor
  · change some (⟨(0, one), int (words.map some).length⟩ : MutableVector) = _
    rw [List.length_map]
  · rfl

theorem metadataStoredVector (words : List U64) (s : State)
    (hs : metadataStoredWords words s) :
    (mutableVector 0).run s = (.ok ⟨(0, one), int words.length⟩, s) := by
  rw [shape_vector_run, hs.1]

theorem metadataStoredMemory (words : List U64) (s : State)
    (hs : metadataStoredWords words s) :
    (memoryRead 0).run s = (.ok (words.map some ++ List.replicate 32 none), s) := by
  simp only [memoryRead, shape_run_bind, shape_run_get, hs.2, shape_run_pure]

/-- Reading an original word is unaffected by other allocations in the store. -/
theorem metadataReadWord (words : List U64) (s : State) (j : Nat)
    (hs : metadataStoredWords words s)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableGet 0 (int ((j + 1 : Nat) : Int))).run s =
      (.ok (words.getD j (u64 0)), s) := by
  have hi := packedInt_val (j + 1) (by omega)
  have hsize := packedInt_val words.length hn
  have hb : 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      int ((j + 1 : Nat) : Int) ≤ int (words.length : Int) := by
    change 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      (int ((j + 1 : Nat) : Int)).val ≤ (int (words.length : Int)).val
    rw [hi, hsize]
    omega
  have hidx : (one.val + (int ((j + 1 : Nat) : Int)).val - 2).toNat = j := by
    rw [hi]
    change (1 + ((j + 1 : Nat) : Int) - 2).toNat = j
    omega
  have hget : (words.map some ++ List.replicate 32 none)[j]? =
      some (some (words.getD j (u64 0))) := by
    rw [List.getElem?_append_left (by simpa only [List.length_map] using hj)]
    rw [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem_eq_getD]
    rfl
  simp only [mutableGet, shape_run_bind, metadataStoredVector words s hs, hb.1, hb.2,
    and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    metadataStoredMemory words s hs, hidx, hget, shape_run_pure]

/-- Writing an original word preserves its header and all other allocated objects. -/
theorem metadataWriteWord (words : List U64) (s : State) (j : Nat) (word : U64)
    (hs : metadataStoredWords words s)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    ∃ s', (mutableSet 0 word (int ((j + 1 : Nat) : Int))).run s = (.ok (), s') ∧
      metadataStoredWords (words.set j word) s' := by
  let slots := words.map some ++ List.replicate 32 none
  let out : State := {s with memories := s.memories.set 0 (slots.set j (some word))}
  have hi := packedInt_val (j + 1) (by omega)
  have hsize := packedInt_val words.length hn
  have hidx : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by
    rw [hi]
    omega
  have hslots : slots.length = words.length + 32 := by
    simp only [slots, List.length_append, List.length_map, List.length_replicate]
  have hraw := metadataSetRaw s slots (int words.length) (int ((j + 1 : Nat) : Int)) word
    hs.1 hs.2 (by rw [hsize, hslots]; omega) (by rw [hi, hsize]; omega)
  rw [hidx] at hraw
  refine ⟨out, hraw, ?_, ?_⟩
  · change s.arrays[0]? = _
    rw [List.length_set]
    exact hs.1
  · change (s.memories.set 0 (slots.set j (some word)))[0]? = _
    have hmem : 0 < s.memories.length := (List.getElem?_eq_some_iff.mp hs.2).choose
    rw [List.getElem?_set_self hmem]
    apply congrArg some
    change (words.map some ++ List.replicate 32 none).set j (some word) = _
    rw [List.set_append_left _ _ (by simpa only [List.length_map] using hj), ← List.map_set]

/-- Public reads compose a bounds check with the successful internal bit read. -/
theorem metadataPublicReadFrom {N : Nat} (B : BitArray N) (i : I64) (s : State) (value : Bool)
    (hb : (Round5.Round2.checkBitArrayBounds B i).run s = (.ok (), s))
    (hr : (unsafeBitGetIndex B.chunks i).run s = (.ok value, s)) :
    (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s = (.ok value, s) := by
  simp only [bitArrayGetIndex, shape_run_bind, hb, hr]

/-- A failed bounds check produces the same public read error without a store update. -/
theorem metadataPublicReadErrorFrom {N : Nat} (B : BitArray N) (i : I64) (s : State)
    (hb : (Round5.Round2.checkBitArrayBounds B i).run s = (.error .bounds, s)) :
    (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s = (.error .bounds, s) := by
  simp only [bitArrayGetIndex, shape_run_bind, hb]

/-- Every valid logical index reads a successfully initialized packed word. -/
theorem metadataReadValid {N : Nat} (xs : List Bool) (dims : List I64) (s : State) (i : I64)
    (hs : metadataStoredWords (encodeBits xs) s)
    (hn : xs.length ≤ 9223372036854775807)
    (hi : int 1 ≤ i ∧ i ≤ int xs.length) :
    ∃ value,
      (bitArrayGetIndex Round5.Round2.checkBitArrayBounds
        (⟨0, int xs.length, dims⟩ : BitArray N) i).run s = (.ok value, s) := by
  have hlen := packedInt_val xs.length hn
  have hiv : 1 ≤ i.val ∧ i.val ≤ xs.length := by
    change 1 ≤ i.val ∧ i.val ≤ (int xs.length).val at hi
    rw [hlen] at hi
    exact hi
  let j := i.val.toNat - 1
  have hj : j < xs.length := by dsimp only [j]; omega
  have hei : i = int ((j + 1 : Nat) : Int) := by
    apply Subtype.ext
    rw [packedInt_val (j + 1) (by omega)]
    dsimp only [j]
    omega
  have hw : (encodeBits xs).length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hc : j / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hget := metadataReadWord (encodeBits xs) s (j / 64) hs hw hc
  have haddr := metadata_scalar_chunks_nat j (by omega)
  rw [← hei] at haddr
  have hread := metadata_scalar_internal_read_run s 0 i
    (int ((j / 64 + 1 : Nat) : Int)) (int ((j % 64 : Nat) : Int))
    ((encodeBits xs).getD (j / 64) (u64 0)) haddr hget
  refine ⟨and_int ((encodeBits xs).getD (j / 64) (u64 0))
    (shl_int (u64 1) (int ((j % 64 : Nat) : Int))) != u64 0, ?_⟩
  have hb := metadata_scalar_bounds_run
    (⟨0, int xs.length, dims⟩ : BitArray N) i s (by
      change 0 ≤ (int xs.length).val
      rw [hlen]
      omega)
  simp only [hi, ite_true] at hb
  exact metadataPublicReadFrom (⟨0, int xs.length, dims⟩ : BitArray N) i s _ hb hread

/-- Assignment metadata can be checked using abstract read outcomes. -/
theorem metadataAssignedReadFrom {N : Nat} (B : BitArray N) (i : I64)
    (rd : Id (Except Error Bool × MutableMemory U64))
    (hok : (int 1 ≤ i ∧ i ≤ B.len) → ∃ value, rd.1 = .ok value)
    (herr : ¬ (int 1 ≤ i ∧ i ≤ B.len) → rd.1 = .error .bounds) :
    bitArrayIsAssigned B i =
      Round5.BitArrayMetadataAgrees.match_1 (fun _ => Bool) rd.1
        (fun _ => true) (fun _ => false) := by
  by_cases hi : int 1 ≤ i ∧ i ≤ B.len
  · obtain ⟨value, hr⟩ := hok hi
    rw [hr]
    simp only [Round5.BitArrayMetadataAgrees.match_1, bitArrayIsAssigned, bitArrayLength, hi, and_self, decide_true]
  · rw [herr hi]
    simp only [Round5.BitArrayMetadataAgrees.match_1, bitArrayIsAssigned, bitArrayLength, hi, decide_false]

/-- Public assignment metadata is equivalent to success of a scalar read. -/
theorem metadataIsAssignedRead {N : Nat} (xs : List Bool) (dims : List I64) (s : State) (i : I64)
    (hs : metadataStoredWords (encodeBits xs) s)
    (hn : xs.length ≤ 9223372036854775807) :
    bitArrayIsAssigned (⟨0, int xs.length, dims⟩ : BitArray N) i =
      Round5.BitArrayMetadataAgrees.match_1 (fun _ => Bool)
        ((bitArrayGetIndex Round5.Round2.checkBitArrayBounds
          (⟨0, int xs.length, dims⟩ : BitArray N) i).run s).1
        (fun _ => true) (fun _ => false) := by
  refine metadataAssignedReadFrom (⟨0, int xs.length, dims⟩ : BitArray N) i
    ((bitArrayGetIndex Round5.Round2.checkBitArrayBounds
      (⟨0, int xs.length, dims⟩ : BitArray N) i).run s) ?_ ?_
  · intro hi
    obtain ⟨value, hr⟩ := metadataReadValid (N := N) xs dims s i hs hn hi
    exact ⟨value, congrArg Prod.fst hr⟩
  · intro hi
    have hb := metadata_scalar_bounds_run
      (⟨0, int xs.length, dims⟩ : BitArray N) i s (by
        change 0 ≤ (int xs.length).val
        rw [packedInt_val xs.length hn]
        omega)
    simp only [hi, ite_false] at hb
    have hr := metadataPublicReadErrorFrom (⟨0, int xs.length, dims⟩ : BitArray N) i s hb
    exact congrArg Prod.fst hr
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem metadataPackedAnd (a b : U64) (k : Nat) :
    packedBit (and_int a b) k = (packedBit a k && packedBit b k) := by
  simp only [and_int, jlAndInt, packedBit_toJInt, BitVec.getLsbD_and, packedBit_fromJInt]

theorem metadataPackedNot (word : U64) (k : Nat) (hk : k < 64) :
    packedBit (not_int word) k = !packedBit word k := by
  unfold not_int
  rw [packedBit_toJInt]
  simp only [jlNotInt, BitVec.getLsbD_not, packedBit_fromJInt]
  change (decide (k < 64) && !packedBit word k) = !packedBit word k
  simp only [hk, decide_true, Bool.true_and]

/-- Setting the low bit makes its subsequent mask test equal the requested Boolean. -/
theorem metadataSetFirstBitTest (word : U64) (value : Bool) :
    (and_int (if value then or_int word (u64 1) else and_int word (not_int (u64 1)))
      (u64 1) != u64 0) = value := by
  cases value with
  | false =>
    have hw : and_int (and_int word (not_int (u64 1))) (u64 1) = u64 0 := by
      apply packedBit_ext
      intro k hk
      rw [metadataPackedAnd, metadataPackedAnd, metadataPackedNot _ k hk, packedBit_zero]
      cases packedBit (u64 1) k <;> simp only [Bool.not_false, Bool.not_true,
        Bool.and_true, Bool.and_false]
    change (and_int (and_int word (not_int (u64 1))) (u64 1) != u64 0) = false
    rw [hw]
    rfl
  | true =>
    have hw : and_int (or_int word (u64 1)) (u64 1) = u64 1 := by
      apply packedBit_ext
      intro k hk
      rw [metadataPackedAnd, packedBit_or]
      cases packedBit (u64 1) k <;> simp only [Bool.or_false, Bool.or_true,
        Bool.and_false, Bool.and_true]
    change (and_int (or_int word (u64 1)) (u64 1) != u64 0) = true
    rw [hw]
    rfl

/-- Public Boolean writes compose the unchanged bounds/conversion state with one internal write. -/
theorem metadataPublicWriteFrom {N : Nat} (B : BitArray N) (i : I64) (s out : State) (value : Bool)
    (hb : (Round5.Round2.checkBitArrayBounds B i).run s = (.ok (), s))
    (hw : (unsafeBitSetIndex B.chunks value i).run s = (.ok (), out)) :
    (bitArraySetIndex Round5.Round2.checkBitArrayBounds Round5.Round2.convertBoolMutation
      B value i).run s = (.ok B, out) := by
  have hc : (Round5.Round2.convertBoolMutation value).run s = (.ok value, s) := rfl
  simp only [bitArraySetIndex, shape_run_bind, hb, hc, hw, shape_run_pure]

/-- A valid first index passes its bounds check in every store. -/
theorem metadataFirstBounds {N : Nat} (B : BitArray N) (s : State)
    (hlen : int 1 ≤ B.len) :
    (Round5.Round2.checkBitArrayBounds B (int 1)).run s = (.ok (), s) := by
  have hnonneg : 0 ≤ B.len.val := by
    have h : 1 ≤ B.len.val := hlen
    omega
  have hi : int 1 ≤ int 1 ∧ int 1 ≤ B.len := ⟨by decide, hlen⟩
  have h := metadata_scalar_bounds_run B (int 1) s hnonneg
  rw [if_pos hi] at h
  exact h

/-- Writing the first bit is observable through a subsequent public read. -/
theorem metadataWriteReadFirst {N : Nat} (B : BitArray N) (words : List U64)
    (s : State) (value : Bool) (hs : metadataStoredWords words s)
    (hchunks : B.chunks = 0) (hlen : int 1 ≤ B.len)
    (hp : 0 < words.length) (hn : words.length ≤ 9223372036854775807) :
    ∃ out,
      (bitArraySetIndex Round5.Round2.checkBitArrayBounds Round5.Round2.convertBoolMutation
        B value (int 1)).run s = (.ok B, out) ∧
      (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B (int 1)).run out = (.ok value, out) := by
  let word := words.getD 0 (u64 0)
  let written := if value then or_int word (u64 1) else and_int word (not_int (u64 1))
  have hmask : shl_int (u64 1) (int 0) = u64 1 := rfl
  have hr := metadataReadWord words s 0 hs hn hp
  obtain ⟨out, hw, hout⟩ := metadataWriteWord words s 0 written hs hn hp
  have hindex : int ((0 + 1 : Nat) : Int) = int 1 := rfl
  rw [hindex] at hw
  have hwrite := metadata_scalar_internal_write_run s out 0 (int 1) (int 1) (int 0)
    word value rfl hr (by simpa only [hmask, written] using hw)
  have hpublicWrite := metadataPublicWriteFrom B (int 1) s out value
    (metadataFirstBounds B s hlen) (by rw [hchunks]; exact hwrite)
  have hn' : (words.set 0 written).length ≤ 9223372036854775807 := by
    rw [List.length_set]
    exact hn
  have hp' : 0 < (words.set 0 written).length := by rw [List.length_set]; exact hp
  have hr' := metadataReadWord (words.set 0 written) out 0 hout hn' hp'
  have hget : (words.set 0 written).getD 0 (u64 0) = written := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hp, Option.getD_some]
  rw [hget] at hr'
  have hread := metadata_scalar_internal_read_run out 0 (int 1) (int 1) (int 0)
    written rfl hr'
  have hbit : (unsafeBitGetIndex B.chunks (int 1)).run out = (.ok value, out) := by
    rw [hchunks]
    exact hread.trans (by
      rw [hmask]
      exact congrArg (fun b => ((.ok b : Except Error Bool), out))
        (metadataSetFirstBitTest word value))
  exact ⟨out, hpublicWrite, metadataPublicReadFrom B (int 1) out value
    (metadataFirstBounds B out hlen) hbit⟩
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Metadata observations use the frozen read-success matcher. -/
def metadataHeaderObservation {N M : Nat} (xs : List Bool)
    (targetDims : List I64) (B : BitArray N) (output : BitArray M) (s : State) (i : I64) : Prop :=
  bitArrayLength output = int (Int.ofNat xs.length) ∧
  bitArraySizeRanked output = (if M = 1 then [int (Int.ofNat xs.length)] else targetDims) ∧
  bitArrayIsAssigned output i =
    Round5.BitArrayMetadataAgrees.match_1 (fun _ => Bool)
      ((bitArrayGetIndex Round5.Round2.checkBitArrayBounds output i).run s).1
      (fun _ => true) (fun _ => false) ∧
  bitArrayIndexStyle = JuliaLean.base.indices.IndexStyle.linear ∧
  Round5.dataIdsPublic output = Round5.dataIdsPublic B

/-- Successful writes must be observed identically through both reshape headers. -/
def metadataUpdateObservation {N M : Nat} (B : BitArray N) (output : BitArray M)
    (changed : Bool) (update : Id (Except Error (BitArray M) × MutableMemory U64)) : Prop :=
  @BitArrayReshapeKeepsBits.match_1 M (fun _ => Prop) update.1
    (fun _ =>
      ((bitArrayGetIndex Round5.Round2.checkBitArrayBounds B (int 1)).run update.2).1 = .ok changed ∧
      ((bitArrayGetIndex Round5.Round2.checkBitArrayBounds output (int 1)).run update.2).1 = .ok changed)
    (fun _ => False)

theorem metadataUpdateOf {N M : Nat} (B : BitArray N) (output result : BitArray M)
    (changed : Bool) (update : Id (Except Error (BitArray M) × MutableMemory U64))
    (s : State) (hu : update = (.ok result, s))
    (hold : (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B (int 1)).run s = (.ok changed, s))
    (hnew : (bitArrayGetIndex Round5.Round2.checkBitArrayBounds output (int 1)).run s = (.ok changed, s)) :
    metadataUpdateObservation B output changed update := by
  rw [hu]
  exact ⟨congrArg Prod.fst hold, congrArg Prod.fst hnew⟩

/-- Result abstraction for the exact frozen rank-changing reshape observation. -/
def metadataReshapeObservation {N M : Nat} (xs : List Bool) (targetDims : List I64)
    (B : BitArray N) (i : I64)
    (reshaped : Id (Except Error (BitArray M) × MutableMemory U64)) : Prop :=
  @Round2.BitArrayReshapeKeepsBits.match_1 M (fun _ => Prop) reshaped
    (fun output s =>
      metadataHeaderObservation xs targetDims B output s i ∧
      if xs.isEmpty then True else
        metadataUpdateObservation B output (!(xs.headD false))
          ((bitArraySetIndex Round5.Round2.checkBitArrayBounds Round5.Round2.convertBoolMutation
            output (!(xs.headD false)) (int 1)).run s))
    (fun _ _ => False)

theorem metadataReshapeOf {N M : Nat} (xs : List Bool) (targetDims : List I64)
    (B : BitArray N) (output : BitArray M) (i : I64)
    (reshaped : Id (Except Error (BitArray M) × MutableMemory U64))
    (s : State) (hr : reshaped = (.ok output, s))
    (hmeta : metadataHeaderObservation xs targetDims B output s i)
    (halias : if xs.isEmpty then True else
      metadataUpdateObservation B output (!(xs.headD false))
        ((bitArraySetIndex Round5.Round2.checkBitArrayBounds Round5.Round2.convertBoolMutation
          output (!(xs.headD false)) (int 1)).run s)) :
    metadataReshapeObservation xs targetDims B i reshaped := by
  rw [hr]
  exact ⟨hmeta, halias⟩

/-- The observation abstraction is definitionally the original frozen proposition. -/
theorem metadataFrozenBridge :
    (∀ {N M : Nat} (xs : List Bool) (oldDims targetDims : List I64) (i : I64),
      oldDims.length = N → (hTargetDims : targetDims.length = M) →
      (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ targetDims, int 0 ≤ d) →
      xs.length < Round5.maxVectorLength →
      let state := initWords (encodeBits xs)
      let oldChecked := (checkedDimensionsModel oldDims).run state
      let targetChecked := (checkedDimensionsModel targetDims).run state
      if oldChecked.1 = .ok (int (Int.ofNat xs.length)) ∧
          targetChecked.1 = .ok (int (Int.ofNat xs.length)) then
        let B : BitArray N := ⟨0, int xs.length, oldDims⟩
        metadataReshapeObservation xs targetDims B i
          ((bitArrayReshapeAny checkedDimensionsModel
            (Round5.Round2.allocateBitArrayModel (N := M))
            B targetDims hTargetDims).run state)
      else True) → Round5.BitArrayMetadataAgrees := by
  exact fun h => h

/-- Any two headers for the same initialized chunks observe the first write identically. -/
theorem metadataAliasObservation {N M : Nat} (xs : List Bool)
    (B : BitArray N) (output : BitArray M) (s : State)
    (hs : metadataStoredWords (encodeBits xs) s)
    (hchunksB : B.chunks = 0) (hchunksOut : output.chunks = 0)
    (hlenB : B.len = int xs.length) (hlenOut : output.len = int xs.length)
    (hn : xs.length ≤ 9223372036854775807) :
    (if xs.isEmpty then True else
      metadataUpdateObservation B output (!(xs.headD false))
        ((bitArraySetIndex Round5.Round2.checkBitArrayBounds Round5.Round2.convertBoolMutation
          output (!(xs.headD false)) (int 1)).run s)) := by
  split
  · trivial
  · next hnonempty =>
    have hpos : 0 < xs.length := by
      have hne : xs ≠ [] := by
        intro hz
        exact hnonempty (by rw [hz]; rfl)
      exact List.length_pos_iff.mpr hne
    have hp : 0 < (encodeBits xs).length := by
      rw [packedEncoded_length]
      unfold wordCount
      omega
    have hlen : int 1 ≤ output.len := by
      rw [hlenOut]
      change 1 ≤ (int xs.length).val
      rw [packedInt_val xs.length hn]
      omega
    obtain ⟨out, hwrite, hread⟩ := metadataWriteReadFirst output (encodeBits xs) s
      (!(xs.headD false)) hs hchunksOut hlen hp (packedEncoded_lengthBound xs hn)
    have halias := metadata_read_alias B output (int 1)
      (hlenB.trans hlenOut.symm) (hchunksB.trans hchunksOut.symm)
    have hold : (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B (int 1)).run out =
        (.ok (!(xs.headD false)), out) := by
      rw [halias]
      exact hread
    exact metadataUpdateOf B output output (!(xs.headD false))
      ((bitArraySetIndex Round5.Round2.checkBitArrayBounds Round5.Round2.convertBoolMutation
        output (!(xs.headD false)) (int 1)).run s) out hwrite hold hread

/-- The canonical aliased output satisfies all of the frozen observable conclusions. -/
theorem metadataPrepared {N M : Nat} (xs : List Bool) (oldDims targetDims : List I64)
    (i : I64) (s : State) (hs : metadataStoredWords (encodeBits xs) s)
    (hn : xs.length ≤ 9223372036854775807) :
    let B : BitArray N := ⟨0, int xs.length, oldDims⟩
    let output : BitArray M := ⟨0, int xs.length, if M != 1 then targetDims else [int xs.length]⟩
    metadataReshapeObservation xs targetDims B i (.ok output, s) := by
  dsimp only
  have hobs := metadata_reshape_observations (N := N) (M := M)
    (⟨0, int xs.length, oldDims⟩ : BitArray N) targetDims
  have hassign := metadataIsAssignedRead (N := M) xs
    (if M != 1 then targetDims else [int xs.length]) s i hs hn
  have halias := metadataAliasObservation (N := N) (M := M) xs
    (⟨0, int xs.length, oldDims⟩ : BitArray N)
    (⟨0, int xs.length, if M != 1 then targetDims else [int xs.length]⟩ : BitArray M)
    s hs rfl rfl rfl rfl hn
  refine ⟨?_, halias⟩
  exact ⟨hobs.1, hobs.2.1, hassign, rfl, hobs.2.2⟩

/-- Transport a prepared observation along an independently established result equation. -/
theorem metadataTransport {N M : Nat} (xs : List Bool) (targetDims : List I64)
    (B : BitArray N) (output : BitArray M) (i : I64)
    (reshaped : Id (Except Error (BitArray M) × MutableMemory U64))
    (s : State) (hr : reshaped = (.ok output, s))
    (hp : metadataReshapeObservation xs targetDims B i (.ok output, s)) :
    metadataReshapeObservation xs targetDims B i reshaped := by
  rw [hr]
  exact hp

/-- Rank-changing reshape reports the requested metadata and retains observable storage aliasing. -/
theorem BitarrayBitArrayMetadataAgrees_proven : Round5.BitArrayMetadataAgrees := by
  apply metadataFrozenBridge
  intro N M xs oldDims targetDims i hOldDims hTargetDims hOldNonneg hTargetNonneg hbound
  dsimp only
  split
  · next hchecked =>
    have hn : xs.length ≤ 9223372036854775807 := by
      change xs.length < 4611686018427387903 at hbound
      omega
    let B : BitArray N := ⟨0, int xs.length, oldDims⟩
    let output : BitArray M :=
      ⟨0, int xs.length, if M != 1 then targetDims else [int xs.length]⟩
    obtain ⟨fresh, s', hallocate, harray, hmemory⟩ := metadataAllocatePreserves M (encodeBits xs)
    have hs : metadataStoredWords (encodeBits xs) s' := by
      refine ⟨?_, hmemory⟩
      simpa only [List.length_map] using harray
    have htarget := metadataCheckedDimensionsRun targetDims (initWords (encodeBits xs))
      (int xs.length) hchecked.2
    have hreshape := metadata_reshape_run checkedDimensionsModel
      (Round5.Round2.allocateBitArrayModel (N := M)) B targetDims hTargetDims fresh
      (initWords (encodeBits xs)) s' htarget hallocate
    have hprepared := metadataPrepared (N := N) (M := M) xs oldDims targetDims i s' hs hn
    exact metadataTransport xs targetDims B output i
      ((bitArrayReshapeAny checkedDimensionsModel (Round5.Round2.allocateBitArrayModel (N := M))
        B targetDims hTargetDims).run (initWords (encodeBits xs))) s' hreshape hprepared
  · trivial
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


/-- The proof-parameterized matrix-vcat program is exactly the installed operation. -/
theorem concat_matrix_factor (arrays : List BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) :
    bitArrayVcatMatrices arrays sizeDim allocate = concat_matrix_program copyChunks arrays sizeDim allocate := rfl



/-- The UInt64 chunk runtime layout projects to the eight-byte inline allocation summary. -/
theorem uint64AllocationLayout :
    (MemoryLayoutMetadata.ofRuntime uint64Layout).allocation = some ⟨8, false, false⟩ := by
  decide

theorem concat_allocate_storage (s : State) (old n : Nat) (hn : n ≤ 576460752303423488) :
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

/-- A readonly dimension-validation loop reports the supplied mismatch whenever any visited dimension differs. -/
theorem concat_validate_dimensions_bad {α : Type} (indices : List α) (dimension : α → I64)
    (expected : I64) (message : String) (s : State)
    (hbad : ∃ i ∈ indices, dimension i ≠ expected) :
    (forIn indices () (fun i _ => (do
      if dimension i != expected then throw (.dimensionMismatch message)
      pure (ForInStep.yield ())) : α → Unit → BitMutationM (ForInStep Unit))).run s =
      (.error (.dimensionMismatch message), s) := by
  induction indices with
  | nil => obtain ⟨i, hi, _⟩ := hbad; cases hi
  | cons index indices ih =>
    by_cases he : dimension index = expected
    · have ht : ∃ i ∈ indices, dimension i ≠ expected := by
        obtain ⟨i, hi, hb⟩ := hbad
        rcases List.mem_cons.mp hi with hx | hx
        · subst i; exact False.elim (hb he)
        · exact ⟨i, hx, hb⟩
      simp only [List.forIn_cons, he, bne_self_eq_false, Bool.false_eq_true,
        ite_false, shape_run_bind, shape_run_pure]
      exact ih ht
    · simp only [List.forIn_cons, bne_iff_ne.mpr he, ite_true, shape_run_bind]
      rfl

/-- Every source with the wrong column count is visited by the installed matrix-vcat validation loop. -/
theorem concat_matrix_validation_bad (first : BitMatrix) (rest : List BitMatrix)
    (sizeDim : BitMatrix → I64 → I64) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hbad : ∃ A ∈ rest, sizeDim A (int 2) ≠ sizeDim first (int 2)) :
    (concat_matrix_validation (first :: rest) first sizeDim (sizeDim first (int 2))).run s =
      (.error (.dimensionMismatch "column lengths must match"), s) := by
  apply concat_validate_dimensions_bad
  obtain ⟨A, ha, hcols⟩ := hbad
  obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp ha
  refine ⟨int ((index + 2 : Nat) : Int), ?_, ?_⟩
  · rw [concat_intRange_two (first :: rest).length hcount]
    apply List.mem_map.mpr
    refine ⟨index, ?_, rfl⟩
    apply List.mem_range.mpr
    simpa only [List.length_cons, Nat.add_sub_cancel] using hi
  · have hindex : index + 2 ≤ 9223372036854775807 := by
      have hc : rest.length + 1 ≤ 9223372036854775807 := by simpa only [List.length_cons] using hcount
      omega
    have hj : (int ((index + 2 : Nat) : Int)).val.toNat - 1 = index + 1 := by
      rw [packedInt_val (index + 2) hindex, Int.toNat_natCast]
      omega
    rw [hj, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, heq]
    exact hcols

/-- The complete row-count scan is a pure fold and leaves every source and destination allocation untouched. -/
theorem concat_matrix_scan_fold (arrays : List BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (registers : I64 × List I64) (s : State) :
    (concat_matrix_scan arrays sizeDim registers).run s =
      (.ok (arrays.foldl (fun current A =>
        (current.1 + sizeDim A (int 1), current.2 ++ [sizeDim A (int 1)])) registers), s) := by
  induction arrays generalizing registers with
  | nil => rfl
  | cons A arrays ih =>
    simp only [concat_matrix_scan, List.forIn_cons, shape_run_bind, shape_run_pure, List.foldl_cons]
    exact ih (registers.1 + sizeDim A (int 1), registers.2 ++ [sizeDim A (int 1)])

/-- A successful phase followed by an arbitrary failed continuation preserves that error and its exact heap. -/
theorem concat_bind_following_error {α β : Type} (action : BitMutationM α)
    (continuation : α → BitMutationM β) (s middle finished : State) (value : α)
    (error : JuliaLean.base.array.Error)
    (hfirst : action.run s = (.ok value, middle))
    (hsecond : (continuation value).run middle = (.error error, finished)) :
    (action >>= continuation).run s = (.error error, finished) := by
  simp only [shape_run_bind, hfirst]
  exact hsecond

/-- Matrix-vcat reports an unequal column count before allocation and preserves the complete input heap. -/
theorem concat_matrix_bad_shape_run (first : BitMatrix) (rest : List BitMatrix)
    (sizeDim : BitMatrix → I64 → I64) (allocate : I64 → I64 → BitMutationM BitMatrix) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hbad : ∃ A ∈ rest, sizeDim A (int 2) ≠ sizeDim first (int 2)) :
    (bitArrayVcatMatrices (first :: rest) sizeDim allocate).run s =
      (.error (.dimensionMismatch "column lengths must match"), s) := by
  let arrays := first :: rest
  let info : I64 × List I64 := arrays.foldl (fun current A =>
    (current.1 + sizeDim A (int 1), current.2 ++ [sizeDim A (int 1)])) (int 0, [])
  have hscan := concat_matrix_scan_fold arrays sizeDim (int 0, []) s
  have hvalidate := concat_matrix_validation_bad first rest sizeDim s hcount hbad
  have hafter : (concat_matrix_after_scan copyChunks arrays first sizeDim allocate info).run s =
      (.error (.dimensionMismatch "column lengths must match"), s) := by
    exact concat_bind_first_error (concat_matrix_validation arrays first sizeDim (sizeDim first (int 2)))
      (fun _ => do
        let out ← allocate info.1 (sizeDim first (int 2))
        let _ ← concat_matrix_copies copyChunks arrays first info.2 (sizeDim first (int 2)) out
        pure out) s s (.dimensionMismatch "column lengths must match") hvalidate
  rw [concat_matrix_factor, concat_matrix_nonempty_factor]
  exact concat_bind_following_error (concat_matrix_scan arrays sizeDim (int 0, []))
    (concat_matrix_after_scan copyChunks arrays first sizeDim allocate)
    s s s info (.dimensionMismatch "column lengths must match") hscan hafter
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- A zero-length matrix shares the packed vector that grows on a vector push. -/
theorem BitarraysVecResizeAlias_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.VecAliasKeepsParentValid := by
  intro h
  have hsmall := (h [] false).1
  change (0 : Nat) = 1 at hsmall
  cases hsmall
end JuliaLean.ChatGPT.Batch4.Group8
end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

/-- Enumeration of the one-based logical extent agrees with the public query. -/
theorem BitarrayAssignedLogicalExtentFull_proven : JuliaLean.Proofs.base.bitarray.Archive20261102Round6.BitArrayAssignedLogicalExtentFull := by
  intro N B i hn
  change (decide (int 1 ≤ i ∧ i ≤ B.len) = true ↔ _)
  rw [decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨hi, hb⟩
    change 1 ≤ i.val at hi
    change i.val ≤ B.len.val at hb
    refine ⟨(i.val - 1).toNat, List.mem_range.mpr (by omega), ?_⟩
    omega
  · rintro ⟨n, hnmem, hni⟩
    have hbound := List.mem_range.mp hnmem
    constructor
    · change 1 ≤ i.val
      omega
    · change i.val ≤ B.len.val
      omega
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

/-- The signed chunk formula is bounded even when a supplied length is negative. -/
theorem ctor_num_chunks_val (n : I64) :
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

/-- Every modeled native logical length yields an allocator-safe chunk count. -/
theorem ctor_chunk_count_bound (n : I64) :
    (numBitChunks n).val.toNat ≤ 576460752303423488 := by
  have hb := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
  rw [ctor_num_chunks_val]
  omega

/-- Fresh backing storage exposes exactly its native header's slots. -/
theorem ctor_new_contents (s : State) (count : Nat) (slots : List (Option U64))
    (hc : count ≤ 9223372036854775807) (hl : slots.length = count) :
    (concat_new_chunks s count slots).contents s.arrays.length = slots := by
  simp only [MutableMemory.contents, concat_new_chunks_header, concat_new_chunks_memory]
  change (slots.drop 0).take (int count).val.toNat = slots
  rw [packedInt_val count hc, Int.toNat_natCast, List.drop_zero, ← hl, List.take_length]

/-- Constructor execution preserves arbitrary validated dimensions and its supplied length. -/
theorem ctor_undef_run {N : Nat} (dims : List I64) (s : State)
    (h : ∀ d ∈ dims, int 0 ≤ d) :
    ∃ (array : BitArray N) (out : State),
      (BitArrayUndef
        (fun ds => pure (ds.foldl (· * ·) (int 1)))
        (fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n)))
        dims).run s = (.ok array, out) ∧
      array.dims = dims ∧ array.len = dims.foldl (· * ·) (int 1) ∧
      (out.contents array.chunks).length = (numBitChunks array.len).val.toNat := by
  let len := dims.foldl (· * ·) (int 1)
  let count := (numBitChunks len).val.toNat
  have hc : count ≤ 576460752303423488 := ctor_chunk_count_bound len
  have ha := concat_allocate_chunks_general count hc s
  by_cases hp : 0 < (numBitChunks len).val
  · have hcount : int count = numBitChunks len := by
      apply Subtype.ext
      rw [packedInt_val count (by omega)]
      exact Int.toNat_of_nonneg (by omega)
    have hcpos : 0 < count := by dsimp only [count]; omega
    have hw := concat_initialize_last count hcpos (by omega) s
    rw [hcount] at hw
    let slots := (List.replicate count none).set (count - 1) (some (u64 0))
    refine ⟨⟨s.arrays.length, len, dims⟩, concat_new_chunks s count slots, ?_, rfl, rfl, ?_⟩
    · exact ctor_undef_positive _ _ dims len s.arrays.length s _ _ h rfl ha hp hw
    · rw [ctor_new_contents s count slots (by omega)
        (by simp only [slots, List.length_set, List.length_replicate])]
      simp only [slots, List.length_set, List.length_replicate]
      rfl
  · refine ⟨⟨s.arrays.length, len, dims⟩,
      concat_new_chunks s count (List.replicate count none), ?_, rfl, rfl, ?_⟩
    · exact ctor_undef_nonpositive _ _ dims len s.arrays.length s _ h rfl ha hp
    · rw [ctor_new_contents s count (List.replicate count none) (by omega)
        (List.length_replicate ..), List.length_replicate]

/-- The frozen constructor observes its requested shape and exact chunk allocation. -/
theorem BitarrayBitArrayConstructorShape_proven :
    JuliaLean.Proofs.base.bitarray.BitArrayConstructorShape := by
  intro dims hdim
  obtain ⟨array, out, hrun, hdims, hlen, hchunks⟩ :=
    ctor_undef_run (N := 2) dims (MutableMemory.initial []) hdim
  obtain ⟨vector, emptyState, hempty, hvdims, hvlen, _⟩ :=
    ctor_undef_run (N := 1) [int 0] (MutableMemory.initial [])
      (by intro d hd; rw [List.mem_singleton.mp hd]; exact Int.le_refl _)
  dsimp only
  rw [hrun]
  unfold bitVectorEmpty
  rw [hempty]
  exact ⟨hdims, hlen, hchunks, hvdims, hvlen⟩

/-- The visible original words survive an independent reshape allocation. -/
theorem ctor_stored_contents (words : List U64) (s : State)
    (hs : metadataStoredWords words s)
    (hn : words.length ≤ 9223372036854775807) :
    s.contents 0 = words.map some := by
  simp only [MutableMemory.contents, hs.1, hs.2, Option.getD_some]
  change ((words.map some ++ List.replicate 32 none).drop 0).take
    (int words.length).val.toNat = words.map some
  rw [packedInt_val words.length hn, Int.toNat_natCast, List.drop_zero]
  exact List.take_left' (List.length_map ..)

/-- A successful single-dimension check reports that dimension unchanged. -/
theorem ctor_singleton_checked (dims : List I64) (s : State) (len : I64)
    (hdims : dims.length = 1)
    (hchecked : ((checkedDimensionsModel dims).run s).1 = .ok len) :
    dims = [len] := by
  cases dims with
  | nil => cases hdims
  | cons dim dims =>
    cases dims with
    | nil =>
      have hc := concat_checked_dims_general dim s
      rw [hc] at hchecked
      have he : dim = len := Except.ok.inj hchecked
      rw [he]
    | cons next rest =>
      simp only [List.length_cons] at hdims
      omega

/-- The stored and public dimension tuples agree for checked input headers. -/
theorem ctor_ranked_dims {N : Nat} (dims : List I64) (s : State) (len : I64)
    (hdims : dims.length = N)
    (hchecked : ((checkedDimensionsModel dims).run s).1 = .ok len) :
    bitArraySizeRanked (⟨0, len, dims⟩ : BitArray N) = dims := by
  unfold bitArraySizeRanked
  by_cases hn : N = 1
  · simp only [hn, ite_true]
    exact (ctor_singleton_checked dims s len (hdims.trans hn) hchecked).symm
  · simp only [hn, ite_false]

/-- Rank-one reshape normalizes to precisely the checked requested shape. -/
theorem ctor_output_dims {N : Nat} (dims : List I64) (s : State) (len : I64)
    (hdims : dims.length = N)
    (hchecked : ((checkedDimensionsModel dims).run s).1 = .ok len) :
    (if N != 1 then dims else [len]) = dims := by
  by_cases hn : N = 1
  · simp only [hn, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact (ctor_singleton_checked dims s len (hdims.trans hn) hchecked).symm
  · simp only [bne_iff_ne.mpr hn, ite_true]

/-- The complete internal reshape preserves shape and all original logical bits. -/
theorem ctor_reshape_internal {N M : Nat} (xs : List Bool)
    (oldDims targetDims : List I64) (hdims : targetDims.length = M)
    (hn : xs.length ≤ 9223372036854775807)
    (hchecked : ((checkedDimensionsModel targetDims).run
      (initWords (encodeBits xs))).1 = .ok (int xs.length)) :
    match (bitArrayReshapeInternal checkedDimensionsModel
      (allocateBitArrayModel (N := M))
      (⟨0, int xs.length, oldDims⟩ : BitArray N) targetDims).run
      (initWords (encodeBits xs)) with
    | (.ok reshaped, state') =>
        bitArrayLength reshaped = int xs.length ∧
        bitArraySize reshaped = targetDims ∧ bitValues state' reshaped = xs
    | (.error _, _) => False := by
  obtain ⟨fresh, s', hallocate, harray, hmemory⟩ := metadataAllocatePreserves M (encodeBits xs)
  have hs : metadataStoredWords (encodeBits xs) s' := by
    refine ⟨?_, hmemory⟩
    simpa only [List.length_map] using harray
  have htarget := metadataCheckedDimensionsRun targetDims
    (initWords (encodeBits xs)) (int xs.length) hchecked
  have hreshape := metadata_reshape_run checkedDimensionsModel
    (allocateBitArrayModel (N := M)) (⟨0, int xs.length, oldDims⟩ : BitArray N)
    targetDims hdims fresh (initWords (encodeBits xs)) s' htarget hallocate
  change (bitArrayReshapeInternal _ _ _ _).run _ = _ at hreshape
  rw [hreshape]
  refine ⟨rfl, ?_, ?_⟩
  · exact ctor_output_dims targetDims (initWords (encodeBits xs)) (int xs.length) hdims hchecked
  · exact scalar_bitValues_contents s' _ xs hn rfl
      (ctor_stored_contents (encodeBits xs) s' hs (packedEncoded_lengthBound xs hn))

/-- Both public reshape methods preserve all logical bits and the checked shape. -/
theorem BitarrayBitArrayReshapeKeepsBits_proven :
    JuliaLean.Proofs.base.bitarray.Round5.BitArrayReshapeKeepsBits := by
  constructor
  · intro N xs oldDims targetDims hOld hTarget _ _
    dsimp only
    split
    · next hguard =>
      have hn : xs.length ≤ 9223372036854775807 := by
        have hb := hguard.1
        change xs.length < 4611686018427387903 at hb
        omega
      unfold bitArrayReshapeSameRank
      by_cases hsame : (targetDims == bitArraySizeRanked
        (⟨0, int xs.length, oldDims⟩ : BitArray N)) = true
      · have hsame' := beq_iff_eq.mp hsame
        rw [ctor_ranked_dims oldDims (initWords (encodeBits xs))
          (int xs.length) hOld hguard.2.1] at hsame'
        simp only [Int.ofNat_eq_natCast, hsame, ite_true, shape_run_pure]
        exact ⟨rfl, hsame'.symm, scalar_bits_initial xs oldDims hn⟩
      · simp only [Int.ofNat_eq_natCast, hsame]
        exact ctor_reshape_internal xs oldDims targetDims hTarget hn hguard.2.2
    · trivial
  · intro N M xs oldDims targetDims _ _ hTarget _ _
    dsimp only
    split
    · next hguard =>
      have hn : xs.length ≤ 9223372036854775807 := by
        have hb := hguard.1
        change xs.length < 4611686018427387903 at hb
        omega
      exact ctor_reshape_internal xs oldDims targetDims hTarget hn hguard.2.2
    · trivial

/-- The unchanged false constructor stores every zero word for any native logical length. -/
theorem ctor_false_constructor_run {N : Nat} (s : State) (dims : List I64) (n : Nat)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hproduct : dims.foldl (· * ·) (int 1) = int n)
    (hn : n ≤ 9223372036854775807) :
    let undef : List I64 → BitMutationM (BitArray N) :=
      BitArrayUndef (fun ds => pure (ds.foldl (· * ·) (int 1))) allocateChunkVectorModel
    let fill : BitArray N → Bool → BitMutationM (BitArray N) :=
      fillBitArray (fun b => pure b) fillVectorChunks
    (falsesIntegerDims undef fill dims).run s =
      (.ok ⟨s.arrays.length, int n, dims⟩,
        shiftFreshHeap s ((encodeBits (List.replicate n false)).map some)) := by
  dsimp only
  by_cases hp : 0 < n
  · have ha := ctor_native_undef_positive (N := N) dims n s hdims hproduct hp hn
    have hf := ctor_fill_false_positive (N := N) s n dims hp hn
    simp only [falsesIntegerDims, shape_run_bind, ha, hf]
  · have hz : n = 0 := by omega
    subst n
    have ha := ctor_native_undef_zero (N := N) dims s hdims hproduct
    have hf := fillEmptyFrom (fun b => pure b) fillVectorChunks
      (⟨s.arrays.length, int 0, dims⟩ : BitArray N) false false (shiftFreshHeap s []) rfl rfl
    simp only [falsesIntegerDims, shape_run_bind, ha, hf]
    rfl

/-- A fresh complete Boolean encoding also has zero unused padding. -/
theorem ctor_fresh_invariant {N : Nat} (s : State) (xs : List Bool) (dims : List I64)
    (hn : xs.length ≤ 9223372036854775807) :
    Round5.Round2.PackedInvariant
      (shiftFreshHeap s ((encodeBits xs).map some))
      (⟨s.arrays.length, int xs.length, dims⟩ : BitArray N) := by
  exact scalar_invariant_of_contents _ _ xs hn rfl
    (shiftFreshContents s ((encodeBits xs).map some)
      (by rw [List.length_map]; exact packedEncoded_lengthBound xs hn))

/-- A checked execution supplies the single-constructor logical observation. -/
theorem ctor_false_observation_from (dims : List I64) (n : Nat)
    (result : Except Error (BitArray 2) × State) (B : BitArray 2) (out : State)
    (hr : result = (.ok B, out)) (hdims : B.dims = dims) (hlen : B.len = int n)
    (hbits : bitValues out B = List.replicate B.len.val.toNat false)
    (hinv : Round5.Round2.PackedInvariant out B) :
    (match result.1 with
    | .ok filled =>
      filled.dims = dims ∧ filled.len = int n ∧
      bitValues result.2 filled = List.replicate filled.len.val.toNat false ∧
      Round5.Round2.PackedInvariant result.2 filled
    | .error _ => False) := by
  rw [hr]
  exact ⟨hdims, hlen, hbits, hinv⟩

/-- The false half of the frozen fill observation holds at every native size, including padding. -/
theorem ctor_false_constructor_native (dims : List I64) (n : Nat)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hproduct : dims.foldl (· * ·) (int 1) = int n)
    (hn : n ≤ 9223372036854775807) :
    let checked : List I64 → BitMutationM I64 := fun ds => pure (ds.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun n =>
      mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))
    let undef : List I64 → BitMutationM (BitArray 2) := BitArrayUndef checked allocate
    let fill : BitArray 2 → Bool → BitMutationM (BitArray 2) :=
      fun B value => fillBitArray (fun x => pure x) fillVectorChunks B value
    let result := (falsesIntegerDims undef fill dims).run (MutableMemory.initial [])
    match result.1 with
    | .ok filled =>
      filled.dims = dims ∧ filled.len = int n ∧
      bitValues result.2 filled = List.replicate filled.len.val.toNat false ∧
      Round5.Round2.PackedInvariant result.2 filled
    | .error _ => False := by
  have hr := ctor_false_constructor_run (N := 2) (MutableMemory.initial []) dims n
    hdims hproduct hn
  dsimp only at hr ⊢
  refine ctor_false_observation_from dims n _ _ _ hr rfl rfl ?_ ?_
  · simp only [packedInt_val n hn, Int.toNat_natCast]
    have h := ctor_fresh_bits (N := 2) (MutableMemory.initial [])
      (List.replicate n false) dims (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using h
  · have h := ctor_fresh_invariant (N := 2) (MutableMemory.initial [])
      (List.replicate n false) dims (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using h

/-- Scalar decoding is unchanged by independent allocation and writes elsewhere. -/
theorem ctor_array_read (xs : List Bool) (i : Nat) (s : State)
    (hs : metadataStoredWords (encodeBits xs) s)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))).run s =
      (.ok (xs.getD i false), s) := by
  have hw := packedEncoded_lengthBound xs hn
  have hc : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hr := metadataReadWord (encodeBits xs) s (i / 64) hs hw hc
  have he := scalar_internal_read_run s 0
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int))
    (int ((i % 64 : Nat) : Int)) ((encodeBits xs).getD (i / 64) (u64 0))
    (scalar_chunks_nat i (by omega)) hr
  rw [he, scalar_mask_test _ (i % 64) (Nat.mod_lt i (by decide))]
  rw [← List.getElem_eq_getD (h := hc)]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [packedWord_bit xs _ _ (Nat.mod_lt _ (by decide))]
  have heq : i / 64 * 64 + i % 64 = i := by omega
  rw [heq]

def ctor_array_cell (value : Bool) : Option U64 :=
  some (u64 (if value then 1 else 0))

def ctor_array_slots (xs : List Bool) (done : Nat) : List (Option U64) :=
  (xs.take done).map ctor_array_cell ++ List.replicate (xs.length - done) none

def ctor_array_state (xs : List Bool) (done : Nat) : State :=
  concat_new_chunks (initWords (encodeBits xs)) xs.length (ctor_array_slots xs done)

theorem ctor_array_slots_length (xs : List Bool) (done : Nat) (hd : done ≤ xs.length) :
    (ctor_array_slots xs done).length = xs.length := by
  simp only [ctor_array_slots, List.length_append, List.length_map, List.length_take,
    Nat.min_eq_left hd, List.length_replicate]
  omega

theorem ctor_array_slots_next (xs : List Bool) (done : Nat) (hd : done < xs.length) :
    (ctor_array_slots xs done).set done (ctor_array_cell (xs.getD done false)) =
      ctor_array_slots xs (done + 1) := by
  have hp : ((xs.take done).map ctor_array_cell).length = done := by
    simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hd)]
  have hn : xs.length - done = (xs.length - (done + 1)) + 1 := by omega
  unfold ctor_array_slots
  rw [List.set_append_right _ _ (by omega), hp, Nat.sub_self, hn,
    List.replicate_succ, List.set_cons_zero, List.take_succ_eq_append_getElem hd,
    List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rw [List.getElem_eq_getD]
  rfl

theorem ctor_array_source_preserved (xs : List Bool) (done : Nat) :
    metadataStoredWords (encodeBits xs) (ctor_array_state xs done) := by
  constructor
  · change some (⟨(0, one), int ((encodeBits xs).map some).length⟩ : MutableVector) = _
    rw [List.length_map]
  · rfl

/-- The next destination word is written while the packed source remains untouched. -/
theorem ctor_array_store (xs : List Bool) (done : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hd : done < xs.length) :
    (mutableSet 1 (u64 (if xs.getD done false then 1 else 0))
      (int ((done + 1 : Nat) : Int))).run (ctor_array_state xs done) =
      (.ok (), ctor_array_state xs (done + 1)) := by
  have ha : (ctor_array_state xs done).arrays[1]? =
      some ⟨(1, one), int xs.length⟩ := by
    exact concat_new_chunks_header (initWords (encodeBits xs)) xs.length (ctor_array_slots xs done)
  have hm : (ctor_array_state xs done).memories[1]? = some (ctor_array_slots xs done) := by
    exact concat_new_chunks_memory (initWords (encodeBits xs)) xs.length (ctor_array_slots xs done)
  have hwrite := concat_store_index (ctor_array_state xs done) 1 1 (int xs.length)
    (ctor_array_slots xs done) (done + 1) (u64 (if xs.getD done false then 1 else 0))
    ha hm (by omega) (by omega)
    (by rw [packedInt_val xs.length hn]; omega)
    (by rw [ctor_array_slots_length xs done (by omega)]; omega)
  apply hwrite.trans
  change ((Except.ok () : Except Error Unit),
      (⟨[(encodeBits xs).map some ++ List.replicate 32 none,
        (ctor_array_slots xs done).set (done + 1 - 1)
          (some (u64 (if xs.getD done false then 1 else 0)))],
        (ctor_array_state xs done).arrays⟩ : State)) = _
  rw [show done + 1 - 1 = done by omega]
  change ((Except.ok () : Except Error Unit),
      (⟨[(encodeBits xs).map some ++ List.replicate 32 none,
        (ctor_array_slots xs done).set done (ctor_array_cell (xs.getD done false))],
        (ctor_array_state xs done).arrays⟩ : State)) = _
  rw [ctor_array_slots_next xs done hd]
  rfl

def ctor_array_step (index : I64) (_ : PUnit) : BitMutationM (ForInStep PUnit) := do
  let bit ← unsafeBitGetIndex 0 index
  let _ ← (do
    mutableSet 1 (u64 (if bit then 1 else 0)) index
    pure (1 : Nat))
  pure (ForInStep.yield PUnit.unit)

theorem ctor_array_step_from (index : I64) (bit : Bool) (s out : State)
    (hr : (unsafeBitGetIndex 0 index).run s = (.ok bit, s))
    (hw : (mutableSet 1 (u64 (if bit then 1 else 0)) index).run s = (.ok (), out)) :
    (ctor_array_step index PUnit.unit).run s = (.ok (ForInStep.yield PUnit.unit), out) := by
  simp only [ctor_array_step, shape_run_bind, hr, hw, shape_run_pure]

theorem ctor_array_step_run (xs : List Bool) (done : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hd : done < xs.length) :
    (ctor_array_step (int ((done + 1 : Nat) : Int)) PUnit.unit).run
      (ctor_array_state xs done) =
      (.ok (ForInStep.yield PUnit.unit), ctor_array_state xs (done + 1)) := by
  have hr := ctor_array_read xs done (ctor_array_state xs done)
    (ctor_array_source_preserved xs done) hn hd
  have hw := ctor_array_store xs done hn hd
  exact ctor_array_step_from _ _ _ _ hr hw

/-- Native conversion visits every logical position once in increasing order. -/
theorem ctor_array_loop (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    (forIn (intRange (int 1) (int xs.length)) PUnit.unit ctor_array_step).run
      (ctor_array_state xs 0) = (.ok PUnit.unit, ctor_array_state xs xs.length) := by
  rw [packedObserve_intRange xs.length hn, List.forIn_map]
  have hloop := concat_range_loop 0 xs.length xs.length (fun _ => PUnit.unit)
    (ctor_array_state xs) (fun i _ => ctor_array_step (int ((i + 1 : Nat) : Int)) PUnit.unit)
    (fun i hi => ctor_array_step_run xs i hn hi) (by omega)
  simpa only [← List.range_eq_range', Nat.zero_add] using hloop

theorem ctor_array_contents_complete (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    (ctor_array_state xs xs.length).contents 1 = xs.map ctor_array_cell := by
  simp only [ctor_array_state, MutableMemory.contents,
    concat_new_chunks_header, concat_new_chunks_memory]
  change ((ctor_array_slots xs xs.length).drop 0).take (int xs.length).val.toNat = _
  rw [packedInt_val xs.length hn, Int.toNat_natCast, List.drop_zero]
  simp only [ctor_array_slots, List.take_length, Nat.sub_self, List.replicate_zero,
    List.append_nil]
  exact List.take_of_length_le (by simp only [List.length_map, Nat.le_refl])

theorem ctor_array_values_complete (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    arrayBoolValues (ctor_array_state xs xs.length) 1 xs.length = xs := by
  unfold arrayBoolValues
  rw [ctor_array_contents_complete xs hn]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, List.getElem?_map,
      List.getElem?_eq_getElem hi', Option.map_some]
    cases xs[i] <;> rfl

theorem ctor_array_one_mul (n : I64) : int 1 * n = n := by
  apply Subtype.ext
  change wrapInt .i64 (1 * n.val) = n.val
  rw [Int.one_mul]
  exact JuliaLean.Proofs.base.int.wrapInt_val n

/-- Allocation followed by the complete scalar read/write loop returns its array. -/
theorem ctor_array_run_from {N : Nat} {A : Type}
    (allocate : List I64 → BitMutationM A) (length : A → I64)
    (set : A → Bool → I64 → BitMutationM A) (B : BitArray N)
    (a : A) (s allocated out : State)
    (ha : (allocate B.dims).run s = (.ok a, allocated))
    (hl : (forIn (intRange (int 1) (length a)) PUnit.unit (fun i _ => do
      let bit ← unsafeBitGetIndex B.chunks i
      let _ ← set a bit i
      pure (ForInStep.yield PUnit.unit))).run allocated = (.ok PUnit.unit, out)) :
    (arrayFromBitArray allocate length set B).run s = (.ok a, out) := by
  simp only [arrayFromBitArray, shape_run_bind, ha, hl, shape_run_pure]

/-- The forward conversion's complete output is correct under an explicit allocation bound. -/
theorem ctor_array_conversion_forward (xs : List Bool)
    (hbound : xs.length ≤ 576460752303423488) :
    let B : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let allocate : List I64 → BitMutationM Nat := fun dims =>
      mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1))
    let set : Nat → Bool → I64 → BitMutationM Nat := fun handle bit i => do
      mutableSet handle (u64 (if bit then 1 else 0)) i
      pure handle
    let result := (arrayFromBitArray allocate (fun _ => int xs.length) set B).run
      (initWords (encodeBits xs))
    result.1 = .ok 1 ∧ arrayBoolValues result.2 1 xs.length = xs := by
  have hn : xs.length ≤ 9223372036854775807 := by omega
  let allocate : List I64 → BitMutationM Nat := fun dims =>
    mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1))
  let set : Nat → Bool → I64 → BitMutationM Nat := fun handle bit i => do
    mutableSet handle (u64 (if bit then 1 else 0)) i
    pure handle
  have ha : (allocate [int xs.length]).run (initWords (encodeBits xs)) =
      (.ok 1, ctor_array_state xs 0) := by
    simp only [allocate, List.foldl_cons, List.foldl_nil, ctor_array_one_mul]
    have h := concat_allocate_chunks_general xs.length hbound (initWords (encodeBits xs))
    simpa only [ctor_array_state, ctor_array_slots, List.take_zero, List.map_nil,
      Nat.sub_zero, List.nil_append, allocateChunkVectorModel, Int.ofNat_eq_natCast,
      show (initWords (encodeBits xs)).arrays.length = 1 from rfl] using h
  have hl : (forIn (intRange (int 1) (int xs.length)) PUnit.unit (fun i _ => do
      let bit ← unsafeBitGetIndex 0 i
      let _ ← set 1 bit i
      pure (ForInStep.yield PUnit.unit))).run (ctor_array_state xs 0) =
      (.ok PUnit.unit, ctor_array_state xs xs.length) := ctor_array_loop xs hn
  have hr := ctor_array_run_from allocate (fun _ => int xs.length) set
    (⟨0, int xs.length, [int xs.length]⟩ : BitArray 1) 1
    (initWords (encodeBits xs)) (ctor_array_state xs 0) (ctor_array_state xs xs.length) ha hl
  change ((arrayFromBitArray allocate (fun _ => int xs.length) set
    (⟨0, int xs.length, [int xs.length]⟩ : BitArray 1)).run
      (initWords (encodeBits xs))).1 = .ok 1 ∧ _
  rw [hr]
  exact ⟨rfl, ctor_array_values_complete xs hn⟩
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/- This fragment follows the checked Group2 packing and constructor helpers. -/

def ctor_rev_slots (xs : List Bool) (count : Nat) : List (Option U64) :=
  (List.range count).foldl
    (fun slots chunk => slots.set chunk (some (packedPrefix xs chunk 64)))
    (shiftFreshInitial xs.length)

theorem ctor_rev_slots_zero (xs : List Bool) :
    ctor_rev_slots xs 0 = shiftFreshInitial xs.length := rfl

theorem ctor_rev_slots_length (xs : List Bool) (count : Nat) :
    (ctor_rev_slots xs count).length = wordCount xs.length := by
  rw [ctor_rev_slots, shiftFreshFoldLength, shiftFreshInitialLength]

theorem ctor_rev_slots_succ (xs : List Bool) (count : Nat) :
    ctor_rev_slots xs (count + 1) =
      (ctor_rev_slots xs count).set count (some (packedPrefix xs count 64)) := by
  simp only [ctor_rev_slots, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem ctor_rev_slots_get (xs : List Bool) (count index : Nat)
    (hc : count ≤ wordCount xs.length) :
    (ctor_rev_slots xs count).getD index none =
      if index < count then some (packedPrefix xs index 64)
      else (shiftFreshInitial xs.length).getD index none := by
  unfold ctor_rev_slots
  rw [shiftFreshFoldGet (List.range count) (fun chunk => some (packedPrefix xs chunk 64))
    (shiftFreshInitial xs.length)
    (by intro i hi; rw [shiftFreshInitialLength]; have hb := List.mem_range.mp hi; omega)]
  simp only [List.mem_range]

theorem ctor_rev_slots_all (xs : List Bool) :
    ctor_rev_slots xs (wordCount xs.length) = (encodeBits xs).map some := by
  unfold ctor_rev_slots
  rw [← shiftFreshInitialLength xs.length, shiftFreshFoldAll]
  simp only [shiftFreshInitialLength, packedPrefix_eq_encode, List.map_map, Function.comp_def]

/-- Complete-word stores leave the constructor's initialized last chunk untouched. -/
theorem ctor_rev_last_zero (xs : List Bool) (hp : 0 < xs.length) :
    (ctor_rev_slots xs (wordCount xs.length - 1))[wordCount xs.length - 1]? =
      some (some (u64 0)) := by
  have hc : 0 < wordCount xs.length := by unfold wordCount; omega
  have hi : wordCount xs.length - 1 < (ctor_rev_slots xs (wordCount xs.length - 1)).length := by
    rw [ctor_rev_slots_length]
    omega
  rw [List.getElem?_eq_getElem hi]
  apply congrArg some
  rw [List.getElem_eq_getD (fallback := none), ctor_rev_slots_get xs _ _ (by omega),
    if_neg (Nat.lt_irrefl _)]
  have hb : wordCount xs.length - 1 <
      (List.replicate (wordCount xs.length) (none : Option U64)).length := by
    rw [List.length_replicate]
    omega
  simp only [shiftFreshInitial, List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_self hb, Option.getD_some]

def ctor_rev_full_step (handle : Nat) (xs : List Bool) (index cursor : I64) :
    BitMutationM (ForInStep I64) := do
  let result ← forIn (intRange (int 0) (int 63)) (cursor, u64 0) (abs_pack_step xs)
  mutableSet handle result.2 index
  pure (.yield result.1)

theorem ctor_rev_pack_store_from (handle : Nat) (pack : BitMutationM (I64 × U64))
    (index next : I64) (word : U64) (s middle out : State)
    (hp : pack.run s = (.ok (next, word), middle))
    (hw : (mutableSet handle word index).run middle = (.ok (), out)) :
    ((do
      let result ← pack
      mutableSet handle result.2 index
      pure (.yield result.1)) : BitMutationM (ForInStep I64)).run s =
      (.ok (.yield next), out) := by
  simp only [shape_run_bind, hp, hw, shape_run_pure]

theorem ctor_rev_full_step_run (xs : List Bool) (chunk : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807)
    (hchunk : chunk < wordCount xs.length - 1) :
    (ctor_rev_full_step s.arrays.length xs (int ((chunk + 1 : Nat) : Int))
      (int ((chunk * 64 + 1 : Nat) : Int))).run (shiftFreshHeap s (ctor_rev_slots xs chunk)) =
      (.ok (.yield (int (((chunk + 1) * 64 + 1 : Nat) : Int))),
        shiftFreshHeap s (ctor_rev_slots xs (chunk + 1))) := by
  have hc : wordCount xs.length ≤ 9223372036854775807 := by unfold wordCount; omega
  have hpack := abs_pack_loop_run xs chunk 64 (shiftFreshHeap s (ctor_rev_slots xs chunk))
    (by omega) (by unfold wordCount at hchunk; omega)
  have h63 : int ((64 : Nat) : Int) - int 1 = int 63 := by decide
  rw [h63] at hpack
  have hw := shiftFreshSet s (ctor_rev_slots xs chunk) chunk (packedPrefix xs chunk 64)
    (by rw [ctor_rev_slots_length]; exact hc)
    (by rw [ctor_rev_slots_length]; omega)
  rw [← ctor_rev_slots_succ xs chunk] at hw
  have hr := ctor_rev_pack_store_from s.arrays.length _
    (int ((chunk + 1 : Nat) : Int)) (int ((chunk * 64 + 64 + 1 : Nat) : Int))
    (packedPrefix xs chunk 64) _ _ _ hpack hw
  rw [show chunk * 64 + 64 + 1 = (chunk + 1) * 64 + 1 by omega] at hr
  exact hr

theorem ctor_rev_full_loop_run (xs : List Bool) (s : State)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (forIn (intRange (int 1) (int (wordCount xs.length) - int 1)) (int 1)
      (ctor_rev_full_step s.arrays.length xs)).run (shiftFreshHeap s (shiftFreshInitial xs.length)) =
      (.ok (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int)),
        shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1))) := by
  have hc : 0 < wordCount xs.length := by unfold wordCount; omega
  have hsub : int (wordCount xs.length) - int 1 =
      int ((wordCount xs.length - 1 : Nat) : Int) := by
    rw [concat_int_sub]
    apply congrArg int
    omega
  rw [hsub, packedObserve_intRange _ (by unfold wordCount; omega), List.forIn_map]
  have h := concat_range_loop 0 (wordCount xs.length - 1) (wordCount xs.length - 1)
    (fun chunk => int ((chunk * 64 + 1 : Nat) : Int))
    (fun chunk => shiftFreshHeap s (ctor_rev_slots xs chunk))
    (fun chunk cursor => ctor_rev_full_step s.arrays.length xs
      (int ((chunk + 1 : Nat) : Int)) cursor)
    (fun chunk hchunk => ctor_rev_full_step_run xs chunk s hn hchunk) (by omega)
  simpa only [← List.range_eq_range', Nat.zero_add, Nat.add_zero, Nat.zero_mul,
    Int.natCast_one, ctor_rev_slots_zero] using h

/-- The final fresh word has zero high bits, so masked packing is its complete encoding. -/
theorem ctor_rev_tail_word (xs : List Bool) (hp : 0 < xs.length) :
    or_int
      (and_int (packedPrefix xs (wordCount xs.length - 1) (abs_tail_count xs.length))
        (maskEnd (int (abs_tail_count xs.length))))
      (and_int (u64 0) (not_int (maskEnd (int (abs_tail_count xs.length))))) =
      packedPrefix xs (wordCount xs.length - 1) 64 := by
  have hc := abs_tail_counts xs.length hp
  apply packedBit_ext
  intro bit hb
  rw [packedBit_or, scalar_packedBit_and, scalar_packedBit_and, packedBit_zero]
  simp only [Bool.false_and, Bool.or_false]
  rw [packedPrefix_bit xs _ _ _ hc.2.1,
    rangeSingleEndMaskBit _ bit hc.1 hc.2.1 hb, packedWord_bit xs _ _ hb]
  by_cases hi : bit < abs_tail_count xs.length
  · simp only [hi, decide_true, Bool.true_and, Bool.and_true]
  · have hindex : xs.length ≤ (wordCount xs.length - 1) * 64 + bit := by omega
    simp only [hi, decide_false, Bool.false_and, Bool.and_false,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none hindex, Option.getD_none]

theorem ctor_rev_tail_read (xs : List Bool) (s : State)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (mutableGet s.arrays.length (int (wordCount xs.length))).run
      (shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1))) =
      (.ok (u64 0), shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1))) := by
  have hc : 0 < wordCount xs.length := by unfold wordCount; omega
  have hr := shiftFreshRead s (ctor_rev_slots xs (wordCount xs.length - 1))
    (wordCount xs.length - 1) (u64 0)
    (by rw [ctor_rev_slots_length]; unfold wordCount; omega)
    (by rw [ctor_rev_slots_length]; omega) (ctor_rev_last_zero xs hp)
  rw [show wordCount xs.length - 1 + 1 = wordCount xs.length by omega] at hr
  exact hr

theorem ctor_rev_tail_write (xs : List Bool) (s : State)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (mutableSet s.arrays.length (packedPrefix xs (wordCount xs.length - 1) 64)
      (int (wordCount xs.length))).run
      (shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1))) =
      (.ok (), shiftFreshHeap s ((encodeBits xs).map some)) := by
  have hc : 0 < wordCount xs.length := by unfold wordCount; omega
  have hw := shiftFreshSet s (ctor_rev_slots xs (wordCount xs.length - 1))
    (wordCount xs.length - 1) (packedPrefix xs (wordCount xs.length - 1) 64)
    (by rw [ctor_rev_slots_length]; unfold wordCount; omega)
    (by rw [ctor_rev_slots_length]; omega)
  rw [← ctor_rev_slots_succ,
    show wordCount xs.length - 1 + 1 = wordCount xs.length by omega,
    ctor_rev_slots_all] at hw
  exact hw

def ctor_rev_finish (handle : Nat) (pack : BitMutationM (I64 × U64))
    (index : I64) (mask : U64) (B : BitVector) : BitMutationM BitVector := do
  let result ← pack
  let old ← mutableGet handle index
  mutableSet handle (or_int (and_int result.2 mask) (and_int old (not_int mask))) index
  pure B

theorem ctor_rev_finish_from (handle : Nat) (pack : BitMutationM (I64 × U64))
    (index next : I64) (mask word old : U64) (B : BitVector) (s middle out : State)
    (hp : pack.run s = (.ok (next, word), middle))
    (hr : (mutableGet handle index).run middle = (.ok old, middle))
    (hw : (mutableSet handle (or_int (and_int word mask) (and_int old (not_int mask))) index).run
      middle = (.ok (), out)) :
    (ctor_rev_finish handle pack index mask B).run s = (.ok B, out) := by
  simp only [ctor_rev_finish, shape_run_bind, hp, hr, hw, shape_run_pure]

theorem ctor_rev_tail_run (xs : List Bool) (s : State)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (ctor_rev_finish s.arrays.length
      (forIn (intRange (int 0) (int (abs_tail_count xs.length) - int 1))
        (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int), u64 0) (abs_pack_step xs))
      (int (wordCount xs.length)) (maskEnd (int (abs_tail_count xs.length)))
      (⟨s.arrays.length, int xs.length, [int xs.length]⟩ : BitVector)).run
      (shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1))) =
      (.ok ⟨s.arrays.length, int xs.length, [int xs.length]⟩,
        shiftFreshHeap s ((encodeBits xs).map some)) := by
  have hc := abs_tail_counts xs.length hp
  have hpck := abs_pack_loop_run xs (wordCount xs.length - 1) (abs_tail_count xs.length)
    (shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1))) hc.2.1 (by omega)
  refine ctor_rev_finish_from s.arrays.length _ (int (wordCount xs.length))
    (int (((wordCount xs.length - 1) * 64 + abs_tail_count xs.length + 1 : Nat) : Int))
    (maskEnd (int (abs_tail_count xs.length)))
    (packedPrefix xs (wordCount xs.length - 1) (abs_tail_count xs.length)) (u64 0)
    _ _ _ _ hpck (ctor_rev_tail_read xs s hp hn) ?_
  rw [ctor_rev_tail_word xs hp]
  exact ctor_rev_tail_write xs s hp hn

def ctor_rev_copy_body_with (xs : List Bool) (handle : Nat) (count tail : I64) :
    BitMutationM BitVector := do
  let cursor ← forIn (intRange (int 1) (count - int 1)) (int 1) (ctor_rev_full_step handle xs)
  ctor_rev_finish handle
    (forIn (intRange (int 0) (tail - int 1)) (cursor, u64 0) (abs_pack_step xs))
    count (maskEnd tail) ⟨handle, int xs.length, [int xs.length]⟩

def ctor_rev_copy_body (xs : List Bool) (handle : Nat) : BitMutationM BitVector :=
  ctor_rev_copy_body_with xs handle (numBitChunks (int xs.length))
    (mod64 (int xs.length - int 1) + int 1)

theorem ctor_rev_copy_phases (xs : List Bool) (handle : Nat)
    (count tail cursor : I64) (s middle out : State)
    (hloop : (forIn (intRange (int 1) (count - int 1)) (int 1)
      (ctor_rev_full_step handle xs)).run s = (.ok cursor, middle))
    (htail : (ctor_rev_finish handle
      (forIn (intRange (int 0) (tail - int 1)) (cursor, u64 0) (abs_pack_step xs))
      count (maskEnd tail) (⟨handle, int xs.length, [int xs.length]⟩ : BitVector)).run middle =
      (.ok ⟨handle, int xs.length, [int xs.length]⟩, out)) :
    (ctor_rev_copy_body_with xs handle count tail).run s =
      (.ok ⟨handle, int xs.length, [int xs.length]⟩, out) := by
  unfold ctor_rev_copy_body_with
  exact concat_bind_success _ _ _ _ _ _ _ hloop htail

theorem ctor_rev_copy_factor (xs : List Bool) (handle : Nat)
    (hz : (int xs.length == int 0) = false) :
    copytoBitArrayFromAbstract (fun _ : List Bool => int xs.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false))
      (⟨handle, int xs.length, [int xs.length]⟩ : BitVector) xs = ctor_rev_copy_body xs handle := by
  have hsize : ¬ int xs.length > int xs.length := Int.lt_irrefl _
  simp only [copytoBitArrayFromAbstract, hz, Bool.false_eq_true, ite_false, hsize]
  rfl

theorem ctor_rev_copy_body_run (xs : List Bool) (s : State)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (ctor_rev_copy_body xs s.arrays.length).run (shiftFreshHeap s (shiftFreshInitial xs.length)) =
      (.ok ⟨s.arrays.length, int xs.length, [int xs.length]⟩,
        shiftFreshHeap s ((encodeBits xs).map some)) := by
  have he : ctor_rev_copy_body xs s.arrays.length =
      ctor_rev_copy_body_with xs s.arrays.length (int (wordCount xs.length))
        (int (abs_tail_count xs.length)) :=
    (congrArg (fun count => ctor_rev_copy_body_with xs s.arrays.length count
      (mod64 (int xs.length - int 1) + int 1)) (shiftFreshNumChunks xs.length hn)).trans
      (congrArg (ctor_rev_copy_body_with xs s.arrays.length (int (wordCount xs.length)))
        (abs_tail_native xs.length hp hn))
  have hr := ctor_rev_copy_phases xs s.arrays.length
    (int (wordCount xs.length)) (int (abs_tail_count xs.length))
    (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int))
    (shiftFreshHeap s (shiftFreshInitial xs.length))
    (shiftFreshHeap s (ctor_rev_slots xs (wordCount xs.length - 1)))
    (shiftFreshHeap s ((encodeBits xs).map some))
    (ctor_rev_full_loop_run xs s hp hn) (ctor_rev_tail_run xs s hp hn)
  exact (congrArg (fun action : BitMutationM BitVector =>
    action.run (shiftFreshHeap s (shiftFreshInitial xs.length))) he).trans hr

theorem ctor_rev_copy_run (xs : List Bool) (s : State)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (copytoBitArrayFromAbstract (fun _ : List Bool => int xs.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false))
      (⟨s.arrays.length, int xs.length, [int xs.length]⟩ : BitVector) xs).run
        (shiftFreshHeap s (shiftFreshInitial xs.length)) =
      (.ok ⟨s.arrays.length, int xs.length, [int xs.length]⟩,
        shiftFreshHeap s ((encodeBits xs).map some)) := by
  rw [ctor_rev_copy_factor xs s.arrays.length (fillPositiveLength xs.length hp hn)]
  exact ctor_rev_copy_body_run xs s hp hn

def ctor_rev_builder (xs : List Bool) (undef : List I64 → BitMutationM BitVector) :
    BitMutationM BitVector :=
  bitArrayFromAbstractTyped (fun _ => [int xs.length]) pure
    (fun dims _ => if dims == [int xs.length] then pure () else throw .bounds)
    undef (fun _ => int xs.length) (fun _ i => i + int 1) (fun _ => int 1)
    (fun values i => pure (values.getD (i.val.toNat - 1) false)) xs

theorem ctor_rev_builder_from (xs : List Bool) (undef : List I64 → BitMutationM BitVector)
    (B : BitVector) (s allocated out : State)
    (ha : (undef [int xs.length]).run s = (.ok B, allocated))
    (hdims : B.dims = [int xs.length])
    (hc : (copytoBitArrayFromAbstract (fun _ => int xs.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false)) B xs).run allocated =
      (.ok B, out)) :
    (ctor_rev_builder xs undef).run s = (.ok B, out) := by
  unfold ctor_rev_builder bitArrayFromAbstractTyped
  change ((pure [int xs.length] : BitMutationM (List I64)) >>= fun dims =>
    undef dims >>= fun current =>
    (if current.dims == [int xs.length] then pure () else throw Error.bounds) >>= fun _ =>
    copytoBitArrayFromAbstract (fun _ => int xs.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false)) current xs).run s = _
  rw [pure_bind]
  refine concat_bind_success _ _ _ _ _ _ _ ha ?_
  simp only [hdims, beq_self_eq_true, ite_true, pure_bind]
  exact hc

@[irreducible] def ctor_rev_build (xs : List Bool) : BitMutationM BitVector :=
  ctor_rev_builder xs
    (BitArrayUndef (fun dims => pure (dims.foldl (· * ·) (int 1))) allocateChunkVectorModel)

/-- Abstract-to-packed conversion initializes every fresh output chunk in source order. -/
theorem ctor_array_conversion_reverse_run (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    (ctor_rev_build xs).run (initWords []) =
      (.ok ⟨1, int xs.length, [int xs.length]⟩,
        shiftFreshHeap (initWords []) ((encodeBits xs).map some)) := by
  unfold ctor_rev_build
  by_cases hp : 0 < xs.length
  · have hdim : ∀ d ∈ [int xs.length], int 0 ≤ d := by
      intro d hd
      rw [List.mem_singleton.mp hd]
      change 0 ≤ (int xs.length).val
      rw [packedInt_val xs.length hn]
      omega
    have hproduct : [int xs.length].foldl (· * ·) (int 1) = int xs.length := by
      simp only [List.foldl_cons, List.foldl_nil, ctor_array_one_mul]
    have ha := ctor_native_undef_positive (N := 1) [int xs.length] xs.length
      (initWords []) hdim hproduct hp hn
    have hc := ctor_rev_copy_run xs (initWords []) hp hn
    exact ctor_rev_builder_from xs _ _ _ _ _ ha rfl hc
  · have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl

/-- The reverse conversion's complete logical result is correct at every native length. -/
theorem ctor_array_conversion_reverse (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    let result := (ctor_rev_build xs).run (initWords [])
    result.1 = .ok ⟨1, int xs.length, [int xs.length]⟩ ∧
      bitValues result.2 (⟨1, int xs.length, [int xs.length]⟩ : BitVector) = xs := by
  dsimp only
  rw [ctor_array_conversion_reverse_run xs hn]
  exact ⟨rfl, ctor_fresh_bits (initWords []) xs [int xs.length] hn⟩

/-- The frozen forward conversion, factored to keep observation proofs from reducing its loop. -/
@[irreducible] def ctor_conversion_forward_action (xs : List Bool) : BitMutationM Nat :=
  arrayFromBitArray
    (fun dims => mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1)))
    (fun _ => int xs.length)
    (fun handle bit i => do
      mutableSet handle (u64 (if bit then 1 else 0)) i
      pure handle)
    (⟨0, int xs.length, [int xs.length]⟩ : BitArray 1)

/-- This is the frozen conversion target's exact success/error matcher and logical observation. -/
def ctor_conversion_outcome (xs : List Bool)
    (forward : Except Error Nat × State) (reverse : Except Error BitVector × State) : Prop :=
  ArrayConversionsKeepBits.match_1 (fun _ _ => Prop) forward.1 reverse.1
    (fun handle result =>
      arrayBoolValues forward.2 handle xs.length = xs ∧ bitValues reverse.2 result = xs)
    (fun _ _ => False)

/-- Successful conversion observations combine without unfolding either mutation program. -/
theorem ctor_conversion_observation_from (xs : List Bool)
    (forward : Except Error Nat × State) (reverse : Except Error BitVector × State)
    (handle : Nat) (B : BitVector)
    (hf : forward.1 = .ok handle ∧ arrayBoolValues forward.2 handle xs.length = xs)
    (hr : reverse.1 = .ok B ∧ bitValues reverse.2 B = xs) :
    ctor_conversion_outcome xs forward reverse := by
  unfold ctor_conversion_outcome
  rw [hf.1, hr.1]
  exact ⟨hf.2, hr.2⟩

/-- Both frozen conversion paths preserve every logical bit within the output allocator's range. -/
theorem ctor_array_conversions_bounded (xs : List Bool)
    (hbound : xs.length ≤ 576460752303423488) :
    ctor_conversion_outcome xs
      ((ctor_conversion_forward_action xs).run (initWords (encodeBits xs)))
      ((ctor_rev_build xs).run (initWords [])) := by
  have hf : ((ctor_conversion_forward_action xs).run (initWords (encodeBits xs))).1 = .ok 1 ∧
      arrayBoolValues ((ctor_conversion_forward_action xs).run (initWords (encodeBits xs))).2
        1 xs.length = xs := by
    unfold ctor_conversion_forward_action
    exact ctor_array_conversion_forward xs hbound
  exact ctor_conversion_observation_from xs _ _ 1
    ⟨1, int xs.length, [int xs.length]⟩ hf (ctor_array_conversion_reverse xs (by omega))
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

theorem scan_bind_success {A B : Type} (action : BitMutationM A)
    (next : A → BitMutationM B) (s middle out : State) (a : A) (b : B)
    (ha : action.run s = (.ok a, middle))
    (hb : (next a).run middle = (.ok b, out)) :
    (action >>= next).run s = (.ok b, out) := by
  rw [shape_run_bind, ha]
  exact hb
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true


set_option backward.isDefEq.respectTransparency false

/-- Appending and updating a separate allocation preserves every source bit read. -/
theorem scan_read_source_fresh (xs : List Bool) (slots : List (Option U64)) (i : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) slots) =
        (.ok (xs.getD i false), shiftFreshHeap (initWords (encodeBits xs)) slots) := by
  have hw : (encodeBits xs).length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hk : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hg : (mutableGet 0 (int ((i / 64 + 1 : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) slots) =
        (.ok (encodeBits xs)[i / 64], shiftFreshHeap (initWords (encodeBits xs)) slots) := by
    rw [List.getElem_eq_getD (u64 0)]
    exact shiftFreshSource (encodeBits xs) slots (i / 64) hw hk
  have hr := scalar_internal_read_run (shiftFreshHeap (initWords (encodeBits xs)) slots) 0
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int)) (int ((i % 64 : Nat) : Int))
    (encodeBits xs)[i / 64] (scalar_chunks_nat i (by omega)) hg
  rw [hr, scalar_mask_test _ (i % 64) (Nat.mod_lt i (by decide))]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [packedWord_bit xs _ _ (Nat.mod_lt _ (by decide))]
  have hindex : i / 64 * 64 + i % 64 = i := by omega
  rw [hindex]

def scan_maskWord (b : Bool) : U64 := u64 (if b then 1 else 0)

def scan_maskSlots (xs : List Bool) : List (Option U64) :=
  xs.map (fun b => some (scan_maskWord b))

def scan_maskStep (i : Nat) : BitMutationM Unit := do
  let bit ← unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))
  mutableSet 1 (scan_maskWord bit) (int ((i + 1 : Nat) : Int))

theorem scan_maskStep_from (i : Nat) (b : Bool) (s s' : State)
    (hr : (unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))).run s = (.ok b, s))
    (hw : (mutableSet 1 (scan_maskWord b) (int ((i + 1 : Nat) : Int))).run s = (.ok (), s')) :
    (scan_maskStep i).run s = (.ok (), s') := by
  unfold scan_maskStep
  rw [shape_run_bind, hr]
  exact hw

/-- A mask write reads the original bit and changes exactly its result slot. -/
theorem scan_maskStep_run (xs : List Bool) (slots : List (Option U64)) (i : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hl : slots.length = xs.length)
    (hi : i < xs.length) :
    (scan_maskStep i).run (shiftFreshHeap (initWords (encodeBits xs)) slots) =
      (.ok (), shiftFreshHeap (initWords (encodeBits xs))
        (slots.set i (some (scan_maskWord (xs.getD i false))))) := by
  have hr := scan_read_source_fresh xs slots i hn hi
  have hw := shiftFreshSet (initWords (encodeBits xs)) slots i
    (scan_maskWord (xs.getD i false)) (by rw [hl]; exact hn) (by rw [hl]; exact hi)
  change (mutableSet 1 (scan_maskWord (xs.getD i false))
    (int ((i + 1 : Nat) : Int))).run _ = _ at hw
  exact scan_maskStep_from i (xs.getD i false) _ _ hr hw

/-- The mask loop has an exact slot-update invariant for every native input. -/
theorem scan_maskLoop_run (xs : List Bool) (indices : List Nat) (slots : List (Option U64))
    (hn : xs.length ≤ 9223372036854775807) (hl : slots.length = xs.length)
    (hi : ∀ i ∈ indices, i < xs.length) :
    (forIn indices PUnit.unit (fun i _ => do
      scan_maskStep i
      pure (ForInStep.yield PUnit.unit))).run
        (shiftFreshHeap (initWords (encodeBits xs)) slots) =
      (.ok PUnit.unit, shiftFreshHeap (initWords (encodeBits xs))
        (indices.foldl (fun ws i => ws.set i (some (scan_maskWord (xs.getD i false)))) slots)) := by
  exact dequeForInFold scan_maskStep
    (fun ws i => ws.set i (some (scan_maskWord (xs.getD i false))))
    (shiftFreshHeap (initWords (encodeBits xs))) (fun ws => ws.length = xs.length) indices
    (by intro ws hw i him; exact scan_maskStep_run xs ws i hn hw (hi i him))
    (by intro ws hw i _; rw [List.length_set]; exact hw) slots hl

/-- Visiting every input index constructs exactly its Boolean mask. -/
theorem scan_maskFold_all (xs : List Bool) :
    (List.range xs.length).foldl
      (fun ws i => ws.set i (some (scan_maskWord (xs.getD i false))))
      (List.replicate xs.length none) = scan_maskSlots xs := by
  have h := shiftFreshFoldAll (List.replicate xs.length (none : Option U64))
    (fun i => some (scan_maskWord (xs.getD i false)))
  simp only [List.length_replicate] at h
  rw [h]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, scan_maskSlots]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, scan_maskSlots]
    rw [List.getElem_eq_getD false]

def scan_makeMask (xs : List Bool) : BitMutationM Nat := do
  let mask ← mutableAllocate (some ⟨8, false, false⟩) 0 (int xs.length)
  for i in intRange (int 1) (int xs.length) do
    let bit ← unsafeBitGetIndex 0 i
    let keep ← pure bit
    mutableSet mask (scan_maskWord keep) i
  pure mask

/-- Full mask construction succeeds and preserves the packed source. -/
theorem scan_makeMask_run (xs : List Bool) (hn : xs.length ≤ 576460752303423488) :
    (scan_makeMask xs).run (initWords (encodeBits xs)) =
      (.ok 1, shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) := by
  have hsize : xs.length ≤ 9223372036854775807 := by omega
  have ha := shiftFreshAllocate (initWords (encodeBits xs)) xs.length hn
  change (mutableAllocate (some ⟨8, false, false⟩) 0 (int xs.length)).run
    (initWords (encodeBits xs)) =
      (.ok 1, shiftFreshHeap (initWords (encodeBits xs)) (List.replicate xs.length none)) at ha
  have hl := scan_maskLoop_run xs (List.range xs.length) (List.replicate xs.length none)
    hsize List.length_replicate (by intro i hi; exact List.mem_range.mp hi)
  rw [scan_maskFold_all] at hl
  simp only [scan_maskStep, bind_assoc] at hl
  unfold scan_makeMask
  apply scan_bind_success _ _ _ _ _ 1 1 ha
  refine scan_bind_success _ _ _
    (shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) _ PUnit.unit 1 ?_ rfl
  simp only [packedObserve_intRange xs.length hsize, List.forIn_map, pure_bind]
  exact hl

/-- Reading an initialized mask slot returns its encoded source Boolean. -/
theorem scan_maskRead_run (xs : List Bool) (i : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (mutableGet 1 (int ((i + 1 : Nat) : Int))).run
      (shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) =
        (.ok (scan_maskWord (xs.getD i false)),
          shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) := by
  apply shiftFreshRead (initWords (encodeBits xs)) (scan_maskSlots xs) i
    (scan_maskWord (xs.getD i false))
  · simpa only [scan_maskSlots, List.length_map] using hn
  · simpa only [scan_maskSlots, List.length_map] using hi
  · simp only [scan_maskSlots, List.getElem?_map, List.getElem?_eq_getElem hi]
    rw [List.getElem_eq_getD false]
    rfl

theorem scan_maskWord_test (b : Bool) : (scan_maskWord b == u64 1) = b := by
  cases b <;> decide

def scan_gatherStep (i : Nat) (kept : List Bool) : BitMutationM (ForInStep (List Bool)) := do
  if (← mutableGet 1 (int ((i + 1 : Nat) : Int))) == u64 1 then
    let bit ← unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))
    pure (ForInStep.yield (kept ++ [bit]))
  else
    pure (ForInStep.yield kept)

theorem scan_gatherStep_from (i : Nat) (kept : List Bool) (b : Bool) (s : State)
    (hm : (mutableGet 1 (int ((i + 1 : Nat) : Int))).run s = (.ok (scan_maskWord b), s))
    (hr : (unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))).run s = (.ok b, s)) :
    (scan_gatherStep i kept).run s =
      (.ok (ForInStep.yield (if b then kept ++ [b] else kept)), s) := by
  unfold scan_gatherStep
  apply scan_bind_success _ _ _ _ _ (scan_maskWord b) _ hm
  rw [scan_maskWord_test]
  cases b
  · rfl
  · exact scan_bind_success _ _ _ _ _ true _ hr rfl

/-- A gather iteration appends precisely the selected bit and changes no storage. -/
theorem scan_gatherStep_run (xs : List Bool) (i : Nat) (kept : List Bool)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (scan_gatherStep i kept).run
      (shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) =
        (.ok (ForInStep.yield
          (if xs.getD i false then kept ++ [xs.getD i false] else kept)),
          shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) := by
  have hm := scan_maskRead_run xs i hn hi
  have hr := scan_read_source_fresh xs (scan_maskSlots xs) i hn hi
  exact scan_gatherStep_from i kept (xs.getD i false) _ hm hr

/-- A loop of state-preserving steps executes its accumulator fold exactly. -/
theorem scan_readFold_run {I A : Type} (action : I → A → BitMutationM (ForInStep A))
    (step : A → I → A) (s : State) (indices : List I)
    (hr : ∀ i ∈ indices, ∀ a, (action i a).run s = (.ok (ForInStep.yield (step a i)), s)) :
    ∀ a, (forIn indices a action).run s = (.ok (indices.foldl step a), s) := by
  induction indices with
  | nil => intro a; rfl
  | cons i is ih =>
    intro a
    have hfirst := hr i List.mem_cons_self a
    have htail := ih (by intro j hj b; exact hr j (List.mem_cons_of_mem i hj) b) (step a i)
    simp only [List.forIn_cons, shape_run_bind, hfirst, List.foldl_cons]
    exact htail

/-- Appending accepted Boolean values computes stable filtering. -/
theorem scan_filterFold (values kept : List Bool) :
    values.foldl (fun acc b => if b then acc ++ [b] else acc) kept =
      kept ++ values.filter id := by
  induction values generalizing kept with
  | nil => simp only [List.foldl_nil, List.filter_nil, List.append_nil]
  | cons b bs ih =>
    cases b <;>
      simp only [List.foldl_cons, Bool.false_eq_true, ite_false, ite_true,
        List.filter_cons, id_eq, ih, List.append_assoc, List.singleton_append]

/-- Enumerating a list through all its valid lookups reconstructs that list. -/
theorem scan_map_range_get (xs : List Bool) :
    (List.range xs.length).map (fun i => xs.getD i false) = xs := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem_eq_getD false]

def scan_gather (xs : List Bool) : BitMutationM (List Bool) := do
  let mut kept : List Bool := []
  for i in intRange (int 1) (int xs.length) do
    if (← mutableGet 1 i) == u64 1 then
      let bit ← unsafeBitGetIndex 0 i
      kept := kept ++ [bit]
  pure kept

/-- The complete gather returns exactly the filtered source and preserves both arrays. -/
theorem scan_gather_run (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    (scan_gather xs).run
      (shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) =
        (.ok (xs.filter id), shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) := by
  have hr := scan_readFold_run scan_gatherStep
    (fun kept i => if xs.getD i false then kept ++ [xs.getD i false] else kept)
    (shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) (List.range xs.length)
    (by intro i hi kept; exact scan_gatherStep_run xs i kept hn (List.mem_range.mp hi)) []
  have hf : (List.range xs.length).foldl
      (fun kept i => if xs.getD i false then kept ++ [xs.getD i false] else kept) [] =
        xs.filter id := by
    have h := scan_filterFold ((List.range xs.length).map (fun i => xs.getD i false)) []
    rw [List.foldl_map, scan_map_range_get] at h
    simpa only [List.nil_append] using h
  rw [hf] at hr
  unfold scan_gatherStep at hr
  unfold scan_gather
  dsimp only
  simp only [packedObserve_intRange xs.length hn, List.forIn_map]
  exact scan_bind_success _ _ _ _ _ (xs.filter id) (xs.filter id) hr rfl

/-- The frozen filtering invocation, retaining its mask-generation and gather callbacks. -/
def scan_filterProgram (xs : List Bool) : BitMutationM (List Bool) :=
  let B := vectorBits xs
  let makeMask : (Bool → BitMutationM Bool) → BitArray 1 → BitMutationM BoolArray := fun f source => do
    let mask ← mutableAllocate (some ⟨8, false, false⟩) 0 source.len
    for i in intRange (int 1) source.len do
      let bit ← unsafeBitGetIndex source.chunks i
      let keep ← f bit
      mutableSet mask (u64 (if keep then 1 else 0)) i
    pure mask
  let gather : BitArray 1 → BoolArray → BitMutationM (List Bool) := fun source mask => do
    let mut kept : List Bool := []
    for i in intRange (int 1) source.len do
      if (← mutableGet mask i) == u64 1 then
        let bit ← unsafeBitGetIndex source.chunks i
        kept := kept ++ [bit]
    pure kept
  bitArrayFilter makeMask gather (fun bit => pure bit) B

/-- Filtering is exact for every input within the frozen mask allocator's bound. -/
theorem scan_filterProgram_run (xs : List Bool) (hn : xs.length ≤ 576460752303423488) :
    (scan_filterProgram xs).run (initWords (encodeBits xs)) =
      (.ok (xs.filter id), shiftFreshHeap (initWords (encodeBits xs)) (scan_maskSlots xs)) := by
  have hm := scan_makeMask_run xs hn
  have hg := scan_gather_run xs (by omega)
  unfold scan_filterProgram bitArrayFilter
  exact scan_bind_success _ _ _ _ _ 1 (xs.filter id) hm hg

/-- The bounded result retains the exact per-input logical filtering observation. -/
theorem scan_filter_bounded (xs : List Bool) (hn : xs.length ≤ 576460752303423488) :
    match (scan_filterProgram xs).run (initWords (encodeBits xs)) with
    | (.ok kept, _) => kept = xs.filter id
    | (.error _, _) => False := by
  rw [scan_filterProgram_run xs hn]
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

theorem scan_popBits_zero (n : Nat) : scan_popBits n 0 = 0 := rfl

/-- A word is empty precisely when its set-bit count is zero. -/
theorem scan_population_zero_iff (word : U64) : popcountWord word = 0 ↔ word = u64 0 := by
  constructor
  · intro hz
    by_cases hw : word = u64 0
    · exact hw
    · have h := scan_blsr_population word hw
      omega
  · intro hw
    subst word
    decide
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A scalar write into a fresh encoded vector installs exactly the updated encoding. -/
theorem scan_tuple_write (s : State) (ys : List Bool) (i : Nat) (value : Bool)
    (hn : ys.length ≤ 9223372036854775807) (hi : i < ys.length) :
    (unsafeBitSetIndex s.arrays.length value (int ((i + 1 : Nat) : Int))).run
      (shiftFreshHeap s ((encodeBits ys).map some)) =
        (.ok (), shiftFreshHeap s ((encodeBits (ys.set i value)).map some)) := by
  have hw : (encodeBits ys).length ≤ 9223372036854775807 := packedEncoded_lengthBound ys hn
  have hk : i / 64 < (encodeBits ys).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hg : (((encodeBits ys).map some)[i / 64]?) =
      some (some (packedPrefix ys (i / 64) 64)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hk]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rfl
  have hr := shiftFreshRead s ((encodeBits ys).map some) (i / 64)
    (packedPrefix ys (i / 64) 64)
    (by simpa only [List.length_map] using hw)
    (by simpa only [List.length_map] using hk) hg
  have hs := shiftFreshSet s ((encodeBits ys).map some) (i / 64)
    (scalar_set_word (packedPrefix ys (i / 64) 64) (i % 64) value)
    (by simpa only [List.length_map] using hw)
    (by simpa only [List.length_map] using hk)
  have hout : ((encodeBits ys).map some).set (i / 64)
      (some (scalar_set_word (packedPrefix ys (i / 64) 64) (i % 64) value)) =
        (encodeBits (ys.set i value)).map some := by
    rw [scalar_encode_set ys i value hi, List.map_set]
  rw [hout] at hs
  exact scalar_internal_write_run _ _ s.arrays.length
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int)) (int ((i % 64 : Nat) : Int))
    (packedPrefix ys (i / 64) 64) value (scalar_chunks_nat i (by omega)) hr hs

/-- Logical assignment preserves its length throughout every prefix. -/
theorem scan_tuple_fold_length (indices : List Nat) (ys xs : List Bool) :
    (indices.foldl (fun values i => values.set i (xs.getD i false)) ys).length = ys.length := by
  induction indices generalizing ys with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons, ih, List.length_set]

/-- The complete assignment loop has the exact logical-list update invariant. -/
theorem scan_tuple_assignment_loop (s : State) (xs ys : List Bool) (indices : List Nat)
    (hn : ys.length ≤ 9223372036854775807)
    (hi : ∀ i ∈ indices, i < ys.length) :
    (forIn indices PUnit.unit (fun i _ => do
      unsafeBitSetIndex s.arrays.length (xs.getD i false) (int ((i + 1 : Nat) : Int))
      pure (ForInStep.yield PUnit.unit))).run
        (shiftFreshHeap s ((encodeBits ys).map some)) =
      (.ok PUnit.unit, shiftFreshHeap s
        ((encodeBits (indices.foldl (fun values i => values.set i (xs.getD i false)) ys)).map some)) := by
  exact dequeForInFold
    (fun i => unsafeBitSetIndex s.arrays.length (xs.getD i false) (int ((i + 1 : Nat) : Int)))
    (fun values i => values.set i (xs.getD i false))
    (fun values => shiftFreshHeap s ((encodeBits values).map some))
    (fun values => values.length = ys.length) indices
    (by
      intro values hv i him
      exact scan_tuple_write s values i (xs.getD i false)
        (by rw [hv]; exact hn) (by rw [hv]; exact hi i him))
    (by intro values hv i _; rw [List.length_set]; exact hv) ys rfl

/-- A visited position contains the corresponding source bit; other positions are unchanged. -/
theorem scan_tuple_fold_get (indices : List Nat) (xs : List Bool) :
    ∀ ys : List Bool, (∀ i ∈ indices, i < ys.length) → ∀ j : Nat,
      (indices.foldl (fun values i => values.set i (xs.getD i false)) ys).getD j false =
        if j ∈ indices then xs.getD j false else ys.getD j false := by
  induction indices with
  | nil => intro ys _ j; simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons i is ih =>
    intro ys hi j
    have hib := hi i List.mem_cons_self
    have ht := ih (ys.set i (xs.getD i false))
      (by intro k hk; rw [List.length_set]; exact hi k (List.mem_cons_of_mem i hk)) j
    rw [List.foldl_cons, ht]
    by_cases hj : j ∈ is
    · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
    · rw [if_neg hj, scalar_getD_set ys i j (xs.getD i false) hib]
      by_cases he : i = j
      · subst j
        rw [if_pos rfl, if_pos List.mem_cons_self]
      · have hnot : ¬ j ∈ i :: is := by
          intro hmem
          rcases List.mem_cons.mp hmem with hmem | hmem
          · exact he hmem.symm
          · exact hj hmem
        rw [if_neg he, if_neg hnot]

/-- Assigning every source element replaces the complete destination contents. -/
theorem scan_tuple_fold_all (xs ys : List Bool) (hl : ys.length = xs.length) :
    (List.range xs.length).foldl (fun values i => values.set i (xs.getD i false)) ys = xs := by
  apply List.ext_getElem
  · rw [scan_tuple_fold_length, hl]
  · intro j hj hj'
    rw [List.getElem_eq_getD false, List.getElem_eq_getD false,
      scan_tuple_fold_get (List.range xs.length) xs ys
        (by intro i hi; rw [hl]; exact List.mem_range.mp hi) j,
      if_pos (List.mem_range.mpr hj')]

def scan_tupleAllocate (n : Nat) : BitMutationM BitVector := do
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (numBitChunks (int (Int.ofNat n)))
  let count ← mutableLength chunks
  for i in intRange (int 1) count do mutableSet chunks (u64 0) i
  pure ⟨chunks, int (Int.ofNat n), [int (Int.ofNat n)]⟩

/-- Tuple construction initializes every packed word, including all padding bits. -/
theorem scan_tupleAllocate_run (s : State) (n : Nat) (hn : n ≤ 9223372036854775807) :
    (scan_tupleAllocate n).run s =
      (.ok ⟨s.arrays.length, int n, [int n]⟩,
        shiftFreshHeap s ((encodeBits (List.replicate n false)).map some)) := by
  have hc : wordCount n ≤ 576460752303423488 := by unfold wordCount; omega
  have hw : wordCount n ≤ 9223372036854775807 := by omega
  have ha := shiftFreshAllocate s (wordCount n) hc
  change (mutableAllocate (some ⟨8, false, false⟩) 0 (int (wordCount n))).run s = _ at ha
  have hl := shiftFreshLength s (List.replicate (wordCount n) none)
  simp only [List.length_replicate] at hl
  have hf := shiftFreshWriteLoop s (List.range (wordCount n))
    (List.replicate (wordCount n) none) (fun _ => u64 0)
    (by simpa only [List.length_replicate] using hw)
    (by intro i hi; simpa only [List.length_replicate] using List.mem_range.mp hi)
  have hfold := shiftFreshFoldConstant (List.replicate (wordCount n) (none : Option U64)) (u64 0)
  simp only [List.length_replicate] at hfold
  rw [hfold] at hf
  rw [fillFalseEncoding, List.map_replicate]
  change ((do
    let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (numBitChunks (int n))
    let count ← mutableLength chunks
    for i in intRange (int 1) count do mutableSet chunks (u64 0) i
    pure (⟨chunks, int n, [int n]⟩ : BitArray 1)) : BitMutationM (BitArray 1)).run s = _
  rw [shiftFreshNumChunks n hn]
  apply concat_bind_success _ _ _ _ _ s.arrays.length _ ha
  apply concat_bind_success _ _ _ _ _ (int (wordCount n)) _ hl
  simp only [packedObserve_intRange (wordCount n) hw, List.forIn_map]
  exact concat_bind_success _ _ _ _ _ PUnit.unit _ hf rfl

def scan_tupleAssign (B : BitVector) (xs : List Bool) : BitMutationM BitVector := do
  for i in intRange (int 1) (int (Int.ofNat xs.length)) do
    unsafeBitSetIndex B.chunks (xs.getD (i.val.toNat - 1) false) i
  pure B

/-- Assignment of a whole tuple overwrites all logical bits in their original order. -/
theorem scan_tupleAssign_run (s : State) (xs ys : List Bool)
    (hn : xs.length ≤ 9223372036854775807) (hl : ys.length = xs.length) :
    (scan_tupleAssign ⟨s.arrays.length, int xs.length, [int xs.length]⟩ xs).run
      (shiftFreshHeap s ((encodeBits ys).map some)) =
        (.ok ⟨s.arrays.length, int xs.length, [int xs.length]⟩,
          shiftFreshHeap s ((encodeBits xs).map some)) := by
  have hloop := scan_tuple_assignment_loop s xs ys (List.range xs.length)
    (by rw [hl]; exact hn) (by intro i hi; rw [hl]; exact List.mem_range.mp hi)
  rw [scan_tuple_fold_all xs ys hl] at hloop
  have hindex : ∀ i ∈ List.range xs.length,
      ((int ((i + 1 : Nat) : Int)).val.toNat - 1) = i := by
    intro i hi
    have hb := List.mem_range.mp hi
    rw [packedInt_val (i + 1) (by omega)]
    omega
  change ((do
    for i in intRange (int 1) (int xs.length) do
      unsafeBitSetIndex s.arrays.length (xs.getD (i.val.toNat - 1) false) i
    pure (⟨s.arrays.length, int xs.length, [int xs.length]⟩ : BitArray 1)) :
      BitMutationM (BitArray 1)).run _ = _
  rw [packedObserve_intRange xs.length hn, List.forIn_map]
  have heq : (forIn (List.range xs.length) PUnit.unit (fun i _ => do
      unsafeBitSetIndex s.arrays.length
        (xs.getD ((int ((i + 1 : Nat) : Int)).val.toNat - 1) false)
        (int ((i + 1 : Nat) : Int))
      pure (ForInStep.yield PUnit.unit))) =
    (forIn (List.range xs.length) PUnit.unit (fun i _ => do
      unsafeBitSetIndex s.arrays.length (xs.getD i false) (int ((i + 1 : Nat) : Int))
      pure (ForInStep.yield PUnit.unit))) := by
    apply JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2.concat_forIn_congr
    intro i hi a
    rw [hindex i hi]
  rw [heq]
  exact concat_bind_success _ _ _ _ _ PUnit.unit _ hloop rfl

def scan_tupleProgram (xs : List Bool) : BitMutationM BitVector :=
  bitVectorFromTuple List.length scan_tupleAllocate scan_tupleAssign xs

/-- The complete frozen tuple program returns the exact canonical encoding under a native bound. -/
theorem scan_tupleProgram_run (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    (scan_tupleProgram xs).run (MutableMemory.initial []) =
      (.ok ⟨1, int xs.length, [int xs.length]⟩,
        shiftFreshHeap (MutableMemory.initial []) ((encodeBits xs).map some)) := by
  have ha := scan_tupleAllocate_run (MutableMemory.initial []) xs.length hn
  have hs := scan_tupleAssign_run (MutableMemory.initial []) xs (List.replicate xs.length false)
    hn List.length_replicate
  unfold scan_tupleProgram bitVectorFromTuple
  exact concat_bind_success _ _ _ _ _ _ _ ha hs

/-- All logical values are preserved by the frozen tuple constructor for native-sized tuples. -/
theorem scan_tuple_bounded (xs : List Bool) (hn : xs.length ≤ 9223372036854775807) :
    match (scan_tupleProgram xs).run (MutableMemory.initial []) with
    | (.ok B, state) => B.len = int (Int.ofNat xs.length) ∧ bitValues state B = xs
    | (.error _, _) => False := by
  rw [scan_tupleProgram_run xs hn]
  change int xs.length = int (Int.ofNat xs.length) ∧
    bitValues (shiftFreshHeap (MutableMemory.initial []) ((encodeBits xs).map some))
      (⟨1, int xs.length, [int xs.length]⟩ : BitVector) = xs
  refine ⟨rfl, ?_⟩
  have hc := shiftFreshContents (MutableMemory.initial []) ((encodeBits xs).map some)
    (by
      rw [List.length_map]
      exact packedEncoded_lengthBound xs hn)
  exact scalar_bitValues_contents _ _ xs hn rfl hc
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

/-- The frozen matrix allocator handles an empty total without any chunk access. -/
theorem mhcat_allocate_empty (rows : I64) (s : State) :
    (allocateMatrix rows (int 0)).run s =
      (.ok (⟨s.arrays.length, int 0, [rows, int 0]⟩ : BitMatrix), concat_extend_empty s) := by
  have hmul : rows * int 0 = int 0 := by
    apply Subtype.ext
    change wrapInt .i64 (rows.val * 0) = wrapInt .i64 0
    rw [Int.mul_zero]
  have hc : numBitChunks (int 0) = int 0 := rfl
  have ha := concat_allocate_empty_chunk s
  change (mutableAllocate (some ⟨8, false, false⟩) 0 (int 0)).run s =
    (.ok s.arrays.length, concat_extend_empty s) at ha
  have hh : (concat_extend_empty s).arrays[s.arrays.length]? =
      some (⟨(s.memories.length, one), int 0⟩ : MutableVector) := by
    simp only [concat_extend_empty, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  have hl := shiftSingleLengthFrom (concat_extend_empty s) s.arrays.length s.memories.length (int 0) hh
  have hrange : intRange (int 1) (int 0) = [] := rfl
  simp only [allocateMatrix, hmul, hc, shape_run_bind, ha, hl, hrange,
    List.forIn_nil, shape_run_pure]

/-- Empty matrix inputs have no source reads, for every row metadata value. -/
theorem mhcat_pair_empty_run (rows : I64) (s : State) :
    (mhcat_pair rows (int 0) (int 0) (int 0) (int 0) allocateMatrix).run s =
      (.ok (⟨s.arrays.length, int 0, [rows, int 0]⟩ : BitMatrix), concat_extend_empty s) := by
  apply mhcat_pair_from_runs rows (int 0) (int 0) (int 0) (int 0)
    allocateMatrix _ s (concat_extend_empty s) (concat_extend_empty s) (concat_extend_empty s)
  · exact mhcat_allocate_empty rows s
  · simp only [copyChunks, beq_self_eq_true, ite_true, shape_run_pure]
  · simp only [copyChunks, beq_self_eq_true, ite_true, shape_run_pure]

/-- The empty case includes the constructible zero-by-zero matrix input. -/
theorem mhcat_matrix_hcat_empty (rows : Nat) :
    mhcat_observation rows [] []
      ((mhcat_pair (int rows) (int 0) (int 0) (int 0) (int 0) allocateMatrix).run
        (concat_initial [[], []])) := by
  apply mhcat_observe_from rows [] [] _ _ _ _ (mhcat_pair_empty_run (int rows) (concat_initial [[], []]))
  · simp only [List.length_nil, Int.natCast_zero, Int.zero_add, Int.zero_ediv]
  · rfl
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

/-- Native conversion is injective on nonnegative representable dimensions. -/
theorem mtx_native_dimensions_distinct (rows columns : Nat)
    (hr : (rows : Int) ≤ IntTy.max .i64)
    (hc : (columns : Int) ≤ IntTy.max .i64)
    (hne : rows ≠ columns) : int rows ≠ int columns := by
  intro h
  have hv := congrArg (fun x : I64 => x.val) h
  have hr' : rows ≤ 9223372036854775807 := by
    change (rows : Int) ≤ 9223372036854775807 at hr
    omega
  have hc' : columns ≤ 9223372036854775807 := by
    change (columns : Int) ≤ 9223372036854775807 at hc
    omega
  rw [packedInt_val rows hr', packedInt_val columns hc'] at hv
  exact hne (by omega)

/-- Every nonsquare input fails before allocating or writing storage. -/
theorem mtx_nonsquare (s : State) (B : BitMatrix) (rows columns : Nat)
    (hinput : MatrixInput B rows columns) (hne : rows ≠ columns) :
    (oneMatrix B).run s =
      (.error (.dimensionMismatch "multiplicative identity defined only for square matrices"), s) := by
  rcases hinput with ⟨hr, hc, hd, _⟩
  have hsize := mtx_read_dimensions s B (int rows) (int columns) hd
  have hne' : (int rows != int columns) = true :=
    bne_iff_ne.mpr (mtx_native_dimensions_distinct rows columns hr hc hne)
  unfold oneMatrix bitMatrixOne
  rw [shape_run_bind, hsize]
  simp only [hne', ite_true]
  rfl

/-- Native tuple conversion preserves each already-native dimension. -/
theorem mtx_native_dimension (x : I64) : nativeDimension x = x := by
  unfold nativeDimension JuliaLean.base.int.convert JInt.convert
  rw [dif_pos x.property]
  rfl

/-- The zero-square constructor appends a fresh empty matrix. -/
theorem mtx_falses_zero (s : State) :
    (matrixFalses [int 0, int 0]).run s =
      (.ok ⟨s.arrays.length, int 0, [int 0, int 0]⟩, shiftEmptyExtend s) := by
  rfl

/-- The zero-square identity executes without entering the diagonal loop. -/
theorem mtx_zero_run (s : State) (B : BitMatrix)
    (hd : B.dims = [int 0, int 0]) :
    (oneMatrix B).run s =
      (.ok ⟨s.arrays.length, int 0, [int 0, int 0]⟩, shiftEmptyExtend s) := by
  unfold oneMatrix bitMatrixOne
  rw [shape_run_bind, mtx_read_dimensions s B (int 0) (int 0) hd]
  change (matrixFalses [int 0, int 0]).run s = _
  exact mtx_falses_zero s

/-- Empty fresh output has all the shape, representation, and preservation
properties required by the full matrix contract. -/
theorem mtx_zero_complete (s : State) (B : BitMatrix)
    (hinput : MatrixInput B 0 0) :
    let result := (oneMatrix B).run s
    ∃ identity, result.1 = .ok identity ∧
      identity.dims = [int 0, int 0] ∧ identity.len.val = (0 : Nat) ∧
      bitValues result.2 identity = [] ∧
      Round5.Round2.PackedInvariant result.2 identity ∧
      result.2.validVector identity.chunks ∧
      identity.chunks ≥ s.arrays.length ∧
      result.2.arrays.take s.arrays.length = s.arrays ∧
      result.2.memories.take s.memories.length = s.memories := by
  dsimp only
  rw [mtx_zero_run s B hinput.2.2.1]
  refine ⟨⟨s.arrays.length, int 0, [int 0, int 0]⟩, rfl, rfl, rfl,
    rfl, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · constructor
    · rw [shiftEmptyContents]
      change 0 = (numBitChunks (int 0)).val.toNat
      decide
    · trivial
  · have hm : (shiftEmptyExtend s).memories[s.memories.length]? = some [] := by
      simp only [shiftEmptyExtend, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
    simp only [MutableMemory.validVector, shiftEmptyHeader, hm]
    decide
  · exact List.take_left
  · exact List.take_left

/-- Checked native dimensions preserve a square product that fits. -/
theorem mtx_checked_square (s : State) (n : Nat)
    (hn : n < 9223372036854775807) (hprod : n * n ≤ 9223372036854775807) :
    (JuliaLean.base.array.checkedDims [int n, int n] : BitMutationM I64).run s =
      (.ok (int ((n * n : Nat) : Int)), s) := by
  have hv := packedInt_val n (by omega)
  have hg : ∀ x ∈ [int n, int n],
      ¬ JuliaLean.Proofs.base.array.opusGrowth.badDim x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst x
    unfold JuliaLean.Proofs.base.array.opusGrowth.badDim
    rw [hv]
    omega
  have hspec := (JuliaLean.Proofs.base.array.opusGrowth.checkedMulDims_spec
    [int n, int n] (by simp only [List.length_cons, List.length_nil, Nat.le_refl])).2 hg
  have hdp : JuliaLean.Proofs.base.array.opusGrowth.dimProd [int n, int n] =
      ((n * n : Nat) : Int) := by
    simp only [JuliaLean.Proofs.base.array.opusGrowth.dimProd, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, Int.mul_one, hv, Int.natCast_mul]
  have hflag : (checkedMulDims [int n, int n]).2 = false := by
    rw [hspec.1, hdp]
    exact decide_eq_false (by omega)
  have hlen : (checkedMulDims [int n, int n]).1 = int ((n * n : Nat) : Int) := by
    apply Subtype.ext
    rw [hspec.2 hflag, hdp, packedInt_val (n * n) hprod]
  simp only [JuliaLean.base.array.checkedDims, checkedDimsMany, hflag,
    Bool.false_eq_true, ite_false, hlen, shape_run_pure]

/-- A positive square constructor validates its dimensions, allocates fresh
chunks, and initializes the last chunk before the fill phase. -/
theorem mtx_undef_positive (s : State) (n : Nat) (hp : 0 < n)
    (hn : n < 9223372036854775807) (hprod : n * n ≤ 9223372036854775807) :
    let count := wordCount (n * n)
    (matrixUndef [int n, int n]).run s =
      (.ok ⟨s.arrays.length, int ((n * n : Nat) : Int), [int n, int n]⟩,
        concat_new_chunks s count
          ((List.replicate count none).set (count - 1) (some (u64 0)))) := by
  dsimp only
  have hnval := packedInt_val n (by omega)
  have hnneg : ¬ (int n).val < 0 := by rw [hnval]; omega
  have hsq : 0 < n * n := Nat.mul_pos hp hp
  have hcountpos : 0 < wordCount (n * n) := by unfold wordCount; omega
  have hcountbound : wordCount (n * n) ≤ 576460752303423488 := by unfold wordCount; omega
  have halloc :
      (mutableAllocate (some ⟨8, false, false⟩) 0 (int (wordCount (n * n)))).run s =
        (.ok s.arrays.length,
          concat_new_chunks s (wordCount (n * n)) (List.replicate (wordCount (n * n)) none)) :=
    concat_allocate_chunks_general _ hcountbound s
  simp only [matrixUndef, bitArrayUndefTuple, JuliaLean.base.tuple.mapOneTwo,
    mtx_native_dimension]
  exact concat_construct_pair_general JuliaLean.base.array.checkedDims
    (fun count => mutableAllocate (some ⟨8, false, false⟩) 0 (int count))
    (int n) (int n) (int ((n * n : Nat) : Int)) (wordCount (n * n)) s _ _ s.arrays.length
    hnneg hnneg (mtx_checked_square s n hn hprod)
    (concat_num_chunks_general (n * n) hprod) hcountpos (by omega) halloc
    (concat_initialize_last (wordCount (n * n)) hcountpos (by omega) s)

/-- Every bounded fresh allocation has a valid native vector header. -/
theorem mtx_fresh_valid (s : State) (slots : List (Option U64))
    (hn : slots.length ≤ 9223372036854775807) :
    (shiftFreshHeap s slots).validVector s.arrays.length := by
  simp only [MutableMemory.validVector, shiftFreshHeader, shiftFreshMemory]
  change 0 ≤ (int slots.length).val ∧ (1 : Int) ≤ 1 ∧
    (1 : Int) - 1 + (int slots.length).val ≤ (slots.length : Int) ∧ slots.length < 2 ^ 63
  rw [packedInt_val slots.length hn]
  omega
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

/-- Every successful constructor result has the intended logical Boolean values. -/
theorem spc_makeBitVector_values (s : State) (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    let result := (makeBitVector xs).run s
    ∃ out, result.1 = .ok out ∧ bitValues result.2 out = xs ∧ out.chunks = s.arrays.length := by
  rw [spc_makeBitVector_run s xs hn]
  refine ⟨⟨s.arrays.length, int xs.length, [int xs.length]⟩, rfl, ?_, rfl⟩
  exact scalar_bitValues_contents (N := 1)
    (shiftFreshHeap s ((encodeBits xs).map some))
    (⟨s.arrays.length, int xs.length, [int xs.length]⟩ : BitVector) xs hn rfl
    (shiftFreshContents s ((encodeBits xs).map some)
      (by rw [List.length_map]; exact packedEncoded_lengthBound xs hn))

/-- Fresh allocation leaves every earlier valid vector's visible cells unchanged. -/
theorem spc_fresh_preserves_contents (s : State) (slots : List (Option U64))
    (handle : Nat) (hv : s.validVector handle) :
    (shiftFreshHeap s slots).contents handle = s.contents handle := by
  cases ha : s.arrays[handle]? with
  | none => simp only [MutableMemory.validVector, ha] at hv
  | some a =>
    cases hm : s.memories[a.reference.1]? with
    | none => simp only [MutableMemory.validVector, ha, hm] at hv
    | some cells =>
      have hb := JuliaLean.ChatGPT.Batch4.Group8.group8_some_index_bound s.arrays handle a ha
      have hc := JuliaLean.ChatGPT.Batch4.Group8.group8_some_index_bound s.memories a.reference.1 cells hm
      simp only [MutableMemory.contents, shiftFreshHeap, List.getElem?_append_left hb,
        ha, List.getElem?_append_left hc, hm]

/-- Constructing the replacement or removed vector does not alter existing valid aliases. -/
theorem spc_makeBitVector_preserves_contents (s : State) (xs : List Bool)
    (handle : Nat) (hv : s.validVector handle) (hn : xs.length ≤ 9223372036854775807) :
    ((makeBitVector xs).run s).2.contents handle = s.contents handle := by
  rw [spc_makeBitVector_run s xs hn]
  exact spc_fresh_preserves_contents s _ handle hv
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

/-- Independent shape, storage accounting, freshness and zero-padding
specification. Every live chunk is a readable UInt64. Logical bits allocated
with undef remain unconstrained; only padding beyond the logical length is
required to be zero. No raw allocator contents are supplied as expected values. -/
def ConstructorPost {N : Nat} (runtime : AllocationData) (dims : Dims N)
    (before after : MutableMemory U64) (B : BitArray N) : Prop :=
  B.len.val = DimensionProduct dims.val ∧
  bitArraySizeRanked B = dims.val ∧
  B.chunks = before.arrays.length ∧
  after.arrays.length = before.arrays.length + 1 ∧
  OldHeapPreserved before after ∧
  ∃ (header : MutableVector) (slots : List (Option U64)),
    after.arrays[B.chunks]? = some header ∧
    after.memories[header.reference.1]? = some slots ∧
    header.reference.2.val = 1 ∧
    header.size.val = ((DimensionProduct dims.val).toNat + 63) / 64 ∧
    slots.length = ((DimensionProduct dims.val).toNat + 63) / 64 ∧
    (∀ slot ∈ slots, ∃ word : U64, slot = some word) ∧
    (if DimensionProduct dims.val = 0 then
      header.reference.1 = runtime.emptyMemory ∧ after.memories = before.memories
     else
      header.reference.1 = before.memories.length ∧
      after.memories.length = before.memories.length + 1) ∧
    (∀ (k bit : Nat) (word : U64), slots[k]? = some (some word) →
      bit < 64 → (DimensionProduct dims.val).toNat ≤ 64 * k + bit →
      (word.val / (2 : Int) ^ bit) % 2 = 0)

/-- Every native Int dimension tuple receives either a successful array with
exact mathematical shape, fresh chunk header, valid readable packed storage and
zero padding, or an ArgumentError with no heap changes. Success occurs exactly
on the accepted mathematical domain; errors cannot substitute for successful
construction. Runtime raw words are universally quantified and are never
assumed correct. For nonnegative rejected tuples, the diagnostic is the Core
invalid-dimensions ArgumentError.
Julia source: base/bitarray.jl:28-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/bitarray.jl:45-67; doc/src/manual/arrays.md:1236-1238.
Dimension-validation boundary: base/boot.jl:782-818. The strict multi-axis
maximum follows that installed validator; no broader promise is invented. -/
def UndefShapeStorageAndErrors : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (dims : Dims N) (s : MutableMemory U64),
    TupleCountFits N → AllocationInput runtime s →
    let result := (JuliaLean.base.bitarray.Models1Group15.undef runtime dims).run s
    match result.1 with
    | .ok B => AcceptedNativeDimensions dims ∧ ConstructorPost runtime dims s result.2 B
    | .error error =>
        ¬ AcceptedNativeDimensions dims ∧ result.2 = s ∧
        (∃ message, error = .argument message) ∧
        ((∀ d ∈ dims.val, 0 ≤ d.val) →
          error = .argument "invalid Array dimensions")

/-- A negative dimension is rejected before dimension multiplication or any
allocation. If several dimensions are negative, the first one's actual signed
value and one-based position determine the diagnostic. Previous nonnegative
entries may be arbitrarily large, so an earlier mathematical product overflow
cannot preempt this error. All later dimensions and the initial heap are free.
Julia source: base/bitarray.jl:28-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/bitarray.jl:45-51; obvious ordered-error invariant. -/
def UndefFirstNegativeDimension : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (dims : Dims N) (s : MutableMemory U64)
    (k : Nat) (d : I64),
    TupleCountFits N → dims.val[k]? = some d → d.val < 0 →
    (∀ (j : Nat) (e : I64), j < k → dims.val[j]? = some e → 0 ≤ e.val) →
    let result := (JuliaLean.base.bitarray.Models1Group15.undef runtime dims).run s
    result.1 = .error (.argument
      s!"dimension size must be ≥ 0, got {d.val} for dimension {(k + 1 : Nat)}") ∧
    result.2 = s

/-- BitVector() succeeds with zero logical elements and size (0,), creates a
fresh vector header referencing the runtime's shared empty chunk memory, and
preserves every existing memory object and header. This includes heaps already
containing other empty vectors or aliases of nonempty memory.
Julia source: base/bitarray.jl:76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/arrays.md:1236-1238; empty-constructor invariant. -/
def EmptyVectorFreshHeader : Prop :=
  ∀ (runtime : AllocationData) (s : MutableMemory U64), AllocationInput runtime s →
    let result := (JuliaLean.base.bitarray.Models1Group15.empty runtime).run s
    match result.1 with
    | .error _ => False
    | .ok B =>
        B.len.val = 0 ∧ bitVectorSize B = [int 0] ∧
        B.chunks = s.arrays.length ∧ result.2.arrays.length = s.arrays.length + 1 ∧
        result.2.memories = s.memories ∧ OldHeapPreserved s result.2 ∧
        result.2.contents B.chunks = [] ∧
        ∃ header : MutableVector, result.2.arrays[B.chunks]? = some header ∧
          header.reference = (runtime.emptyMemory, int 1) ∧ header.size.val = 0

/-- Every native Boolean tuple, including empty and singleton tuples and every
machine-representable field count, constructs a fresh BitVector with exactly
those values in tuple order. The constructor preserves all prior array headers
and memory objects, creates only the specified chunk storage, and clears every
padding bit. Raw initial chunk contents are arbitrary and universally quantified.
No shape, word-alignment, tuple-size convenience bound or caller correctness
law narrows this domain. The existing allocation boundary excludes resource
exhaustion and native pointer addresses; all errors inside this closed path are
covered by the requirement that construction succeeds on its native inputs.
Julia source: base/bitarray.jl:95-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/bitarray.jl:79-94; doc/src/manual/functions.md:1141-1143.
The independent expected values use mathematical bit extraction from the final
heap and the original tuple list, rather than the implementation's register pack. -/
def TupleConstructorValuesFreshStorage : Prop :=
  ∀ (runtime : AllocationData) (nt : BoolTuple) (before : MutableMemory U64),
    AllocationInput runtime before →
    let result := (fromBoolTuple runtime nt).run before
    match result.1 with
    | .error _ => False
    | .ok B =>
        B.len.val = (nt.values.length : Int) ∧
        ConstructorPost runtime (⟨[int nt.values.length], rfl⟩ : Dims 1)
          before result.2 B ∧
        ∀ (i : Nat) (inTuple : i < nt.values.length),
          ∃ word : U64,
            (result.2.contents B.chunks)[i / 64]? = some (some word) ∧
            (word.val / (2 : Int) ^ (i % 64)) % 2 =
              if nt.values.get ⟨i, inTuple⟩ then 1 else 0

/-- Independent allocation-result specification shared by the native public
allocation methods. Rejected inputs must report the first negative axis, when
one exists, or the Core invalid-dimensions error otherwise. -/
def NativeAllocationOutcome {N : Nat} (runtime : AllocationData) (dims : Dims N)
    (before : MutableMemory U64)
    (result : Except JuliaLean.base.array.Error (BitArray N) × MutableMemory U64) : Prop :=
  match result.1 with
  | .ok B => AcceptedNativeDimensions dims ∧ ConstructorPost runtime dims before result.2 B
  | .error error =>
      ¬ AcceptedNativeDimensions dims ∧ result.2 = before ∧
      (∃ message, error = .argument message) ∧
      ((∀ d ∈ dims.val, 0 ≤ d.val) → error = .argument "invalid Array dimensions") ∧
      (∀ (k : Nat) (d : I64), dims.val[k]? = some d → d.val < 0 →
        (∀ (j : Nat) (e : I64), j < k → dims.val[j]? = some e → 0 ≤ e.val) →
        error = .argument
          s!"dimension size must be ≥ 0, got {d.val} for dimension {(k + 1 : Nat)}")

/-- similar(B) uses the public shape of B, including the rank-one length
specialization, and allocates fresh packed storage with that shape. It does not
read input chunks, so the property imposes no validity or size condition on
B.chunks, the old chunk vector or the old contents. Negative and overflowing
shapes are included and must fail at the proper constructor check.
Julia source: base/bitarray.jl:359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:777-784; doc/src/manual/arrays.md:66. -/
def SimilarSameShapeFresh : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (B : BitArray N)
    (rank : (bitArraySizeRanked B).length = N) (s : MutableMemory U64),
    TupleCountFits N → AllocationInput runtime s →
    NativeAllocationOutcome runtime ⟨bitArraySizeRanked B, rank⟩ s
      ((JuliaLean.base.bitarray.Models1Group15.similar runtime B rank).run s)

/-- The native dimension-varargs, dimension-tuple and explicit Bool-element
similar overloads all return fresh packed arrays of the requested rank and
mathematical shape. All signed dimensions, overflow cases and ordered negative
errors are included. The input array's rank, dimensions, length, chunk contents
and possible chunk aliases do not constrain this allocation.
Julia source: base/bitarray.jl:360-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:777-784; doc/src/manual/arrays.md:66. -/
def SimilarSpecifiedShapeFresh : Prop :=
  ∀ (N R : Nat) (runtime : AllocationData) (B : BitArray N) (dims : Dims R)
    (s : MutableMemory U64), TupleCountFits R → AllocationInput runtime s →
    NativeAllocationOutcome runtime dims s
      ((JuliaLean.base.bitarray.Models1Group15.similarDims runtime B dims).run s) ∧
    NativeAllocationOutcome runtime dims s
      ((JuliaLean.base.bitarray.Models1Group15.similarDimsTuple runtime B dims).run s) ∧
    NativeAllocationOutcome runtime dims s
      ((JuliaLean.base.bitarray.Models1Group15.similarBool runtime B dims).run s)

/-- Full allocation contract plus the documented all-false or all-true contents. -/
def BooleanAllocationOutcome {N : Nat} (runtime : AllocationData) (dims : Dims N)
    (before : MutableMemory U64) (x : Bool)
    (result : Except JuliaLean.base.array.Error (BitArray N) × MutableMemory U64) : Prop :=
  NativeAllocationOutcome runtime dims before result ∧
  match result.1 with
  | .ok B => LogicalBitsEqual result.2 B x
  | .error _ => True

/-- Native Int-dimensional falses and trues construct the entire requested
Boolean array, with the exact shape, fresh storage and zero padding. Invalid
signed dimensions produce the correct ordered errors without heap mutation.
These are useful partial models of the broader Integer overloads; they make
no claim about conversion of arbitrary Integer subtypes.
Julia source: base/bitarray.jl:396,415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/bitarray.jl:381-393,400-412; doc/src/manual/arrays.md:61-62. -/
def FalsesTruesNativeValues : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (dims : Dims N) (s : MutableMemory U64),
    TupleCountFits N → AllocationInput runtime s →
    BooleanAllocationOutcome runtime dims s false
      ((JuliaLean.base.bitarray.Models1Group15.falsesNative runtime dims).run s) ∧
    BooleanAllocationOutcome runtime dims s true
      ((JuliaLean.base.bitarray.Models1Group15.truesNative runtime dims).run s)

/-- Empty dimension tuples construct zero-dimensional arrays with one Boolean
element, false for falses(()) and true for trues(()). Both methods must succeed,
preserve all old heap objects, and use fresh zero-padded packed storage.
Julia source: base/bitarray.jl:397,416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/bitarray.jl:381-393,400-412; doc/src/manual/arrays.md:61-62. -/
def EmptyDimensionsBooleanValues : Prop :=
  ∀ (runtime : AllocationData) (s : MutableMemory U64), AllocationInput runtime s →
    BooleanAllocationOutcome runtime (N := 0) ⟨[], rfl⟩ s false
      ((JuliaLean.base.bitarray.Models1Group15.falsesEmpty runtime).run s) ∧
    BooleanAllocationOutcome runtime (N := 0) ⟨[], rfl⟩ s true
      ((JuliaLean.base.bitarray.Models1Group15.truesEmpty runtime).run s)

/-- The metadata invariant of a native rank-two BitArray. Each axis and the
stored length already have Julia Int type; the exact mathematical product,
rather than a wrapped product, equals that stored length. No condition is imposed
on the old chunks: resizing a shared chunk vector does not change these fields.
There is no stricter per-axis bound, so zero-by-typemax shapes are included. -/
def NativeMatrixShape (B : BitMatrix) (rows columns : I64) : Prop :=
  B.dims = [rows, columns] ∧ 0 ≤ rows.val ∧ 0 ≤ columns.val ∧
  B.len.val = rows.val * columns.val

/-- Independent mathematical identity-matrix contents. Linear storage is
column-major: row + order*column is the zero-based location. Empty matrices
have no coordinates, while their shape and storage remain specified separately. -/
def IdentityMatrixValues (s : MutableMemory U64) (B : BitMatrix) (order : Nat) : Prop :=
  ∀ (row column : Nat), row < order → column < order →
    PackedBitValue s B (row + order * column) = some (if row = column then 1 else 0)

/-- For every constructible native BitMatrix shape, one either returns a fresh
same-shaped packed identity or rejects nonsquare dimensions before allocation.
The stored length certifies that the exact product is machine-representable;
no convenience bound on dimensions, data size, or number of chunks is added.
Input chunks need not be valid or readable, and may have been resized by aliases.
Square construction quantifies every raw allocation-data choice at the existing
runtime boundary and requires only that the shared empty memory really exists.
Nonsquare failure needs no allocator premise and preserves the entire heap.
Julia source: base/bitarray.jl:419-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:367-390; doc/src/base/numbers.md:102.
Storage and padding invariant: base/bitarray.jl:1-23. -/
def OneMatrixIdentityAndErrors : Prop :=
  ∀ (runtime : AllocationData) (B : BitMatrix) (rows columns : I64)
    (s : MutableMemory U64), NativeMatrixShape B rows columns →
    let result := (JuliaLean.base.bitarray.Models1Group15.oneMatrix runtime B).run s
    if rows = columns then
      AllocationInput runtime s →
        ∃ identity : BitMatrix, result.1 = .ok identity ∧
          identity.dims = B.dims ∧ identity.len = B.len ∧
          ConstructorPost runtime ⟨[rows, columns], rfl⟩ s result.2 identity ∧
          IdentityMatrixValues result.2 identity rows.val.toNat
    else
      result.1 = .error (.dimensionMismatch
        "multiplicative identity defined only for square matrices") ∧
      result.2 = s

/-- Same-rank reshape covers every native signed dimension tuple. Equal public
shape returns the exact original object and does not allocate or write anything.
All other shapes obey complete dimension checking, error order and fresh-header
sharing, including stale vector dims, aliased chunk growth/shrinkage and zero
sizes. No source chunk is read by the implementation or required readable here.
Julia source: base/bitarray.jl:472-474,476-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/reshapedarray.jl:67-79; doc/src/manual/arrays.md:63. -/
def ReshapeSameIdentityShapeAndErrors : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (source : Ref N) (original : BitArray N)
    (dims : Dims N) (state : ObjectState),
    TupleCountFits N → ObjectContains state source original → NativeHeaderShape original →
    let result := (JuliaLean.base.bitarray.Models1Group15.reshapeSame runtime source dims).run state
    if dims.val = bitArraySizeRanked original then
      result.1 = .ok source ∧ result.2 = state
    else
      ReshapeFreshOutcome runtime source original dims state result

/-- Changing rank must allocate a fresh BitArray object while retaining the
same underlying chunk vector, exact requested shape and old logical length.
The temporary zero-shaped allocation is retained, and all old objects and data
are preserved. Every signed requested dimension is covered: invalid multi-axis
checks take precedence over element-count mismatch, while a negative rank-one
request reaches DimensionMismatch. Failure makes no state changes. Source
chunk validity and readability are deliberately not preconditions.
Julia source: base/bitarray.jl:475-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/reshapedarray.jl:67-79; doc/src/manual/arrays.md:63. -/
def ReshapeOtherSharesStorageAndErrors : Prop :=
  ∀ (N R : Nat) (runtime : AllocationData) (source : Ref N) (original : BitArray N)
    (dims : Dims R) (differentRank : N ≠ R) (state : ObjectState),
    TupleCountFits N → TupleCountFits R →
    ObjectContains state source original → NativeHeaderShape original →
    ReshapeFreshOutcome runtime source original dims state
      ((JuliaLean.base.bitarray.Models1Group15.reshapeOther runtime source dims differentRank).run state)

/-- The public dimensions of a native BitArray have the declared rank,
nonnegative native values, and an exact mathematical product equal to its
machine-sized logical length. The source's physical chunks may have been grown
or shrunk through an alias; none of those physical facts is assumed here. -/
def CopySourceShape {N : Nat} (original : BitArray N) (dims : Dims N) : Prop :=
  bitArraySizeRanked original = dims.val ∧
  (∀ d ∈ dims.val, 0 ≤ d.val) ∧ original.len.val = DimensionProduct dims.val

/-- Exact allocation accounting and independence for a completed copy allocation.
This invariant deliberately does not assert zero padding: the following copyto!
may copy nonzero source padding after the source chunks have grown through an
alias. It also applies to retained fresh storage after a later copy-read error. -/
def FreshCopyAllocation {N : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims N) (before after : ObjectState) : Prop :=
  before.objects.length ≠ source.identity ∧
  after.objects.length = before.objects.length + 1 ∧
  OldObjectsPreserved before after ∧
  OldHeapPreserved before.memory after.memory ∧
  after.memory.arrays.length = before.memory.arrays.length + 1 ∧
  ∃ (header : BitArray N) (chunks : MutableVector) (slots : List (Option U64)),
    ObjectContains after ⟨before.objects.length⟩ header ∧
    header.chunks = before.memory.arrays.length ∧
    header.len = original.len ∧ bitArraySizeRanked header = dims.val ∧
    header.dims = (if N = 1 then [] else dims.val) ∧
    after.memory.arrays[header.chunks]? = some chunks ∧
    chunks.reference.2.val = 1 ∧
    chunks.size.val = (original.len.val.toNat + 63) / 64 ∧
    after.memory.memories[chunks.reference.1]? = some slots ∧
    slots.length = (original.len.val.toNat + 63) / 64 ∧
    (∀ slot ∈ slots, ∃ word : U64, slot = some word) ∧
    (if original.len.val = 0 then
      chunks.reference.1 = runtime.emptyMemory ∧
      after.memory.memories = before.memory.memories
     else
      chunks.reference.1 = before.memory.memories.length ∧
      after.memory.memories.length = before.memory.memories.length + 1)

/-- Exhaustive allocation/error frame for a native-shape copy. Rejected shapes
fail in similar's constructor without allocations. Accepted shapes allocate
and register a fresh object before touching source chunks; those allocations
survive a later physical bounds/unassigned-cell failure. The unassigned-cell
case describes only the installed Option heap boundary, not a claim that native
uninitialized UInt64 values throw UndefRefError. -/
def CopyAllocationOutcome {N : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims N) (before : ObjectState)
    (result : Except JuliaLean.base.array.Error (Ref N) × ObjectState) : Prop :=
  (AcceptedNativeDimensions dims → AllocationInput runtime before.memory →
    FreshCopyAllocation runtime source original dims before result.2 ∧
    (match result.1 with
     | .ok copied => copied.identity = before.objects.length ∧ copied ≠ source
     | .error error => error = .bounds ∨ error = .undefinedReference)) ∧
  (¬ AcceptedNativeDimensions dims →
    result.1 = .error (.argument "invalid Array dimensions") ∧ result.2 = before)

/-- Both same-type constructor spellings allocate a new object and a new chunk
array header and preserve every old object/header/cell, even when source aliases
have changed its physical chunk count. Later failed reads retain allocation and
preceding writes in the fresh object. Empty copies use the shared empty memory
but still have distinct object and chunk-array identities. All source dimension
sizes are covered, including zero-product multi-axis shapes with a typemax axis,
which similar's Core constructor rejects before allocating.
Julia source: base/bitarray.jl:535-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Callees: base/abstractarray.jl:1154-1157,1211-1214; base/bitarray.jl:359,429-447.
Julia documentation: doc/src/manual/arrays.md:64 (copy).
Unlike convert(::Type{T}, a::T) at base/abstractarray.jl:16, these constructors copy. -/
def CopyConstructorsAllocationAndErrors : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (source : Ref N) (original : BitArray N)
    (dims : Dims N) (before : ObjectState), TupleCountFits N →
    ObjectContains before source original → CopySourceShape original dims →
    CopyAllocationOutcome runtime source original dims before
      ((JuliaLean.base.bitarray.Models1Group15.typedCopy runtime source).run before) ∧
    CopyAllocationOutcome runtime source original dims before
      ((JuliaLean.base.bitarray.Models1Group15.copySame runtime source).run before)

/-- Physical source words available to a fresh same-shape packed copy. This
mathematical count allows extra chunks and underbacked aliases; it is not a
call to num_bit_chunks or to the implementation's min/length dispatch. -/
def CopyAvailableWords {N : Nat} (s : MutableMemory U64) (original : BitArray N) : Nat :=
  min ((original.len.val.toNat + 63) / 64) (s.contents original.chunks).length

/-- Only the prefix actually needed from the source must be readable. Extra
source chunks may contain arbitrary cells and are never inspected. -/
def ReadableCopyPrefix {N : Nat} (s : MutableMemory U64) (original : BitArray N) : Prop :=
  ∀ k : Nat, k < CopyAvailableWords s original →
    ∃ word : U64, (s.contents original.chunks)[k]? = some (some word)

/-- Independent successful-copy content specification. Every available packed
word is copied from the initial source snapshot, including any nonzero padding.
When the logical prefix is physically present, every logical bit is equal and
all source padding bits are preserved. With underbacking, only present words
are promised and the uncopied final destination word remains constructor-zero;
no default values are invented for the missing logical source elements. -/
def CopyPrefixOutcome {N : Nat} (runtime : AllocationData) (source : Ref N)
    (original : BitArray N) (dims : Dims N) (before : ObjectState)
    (result : Except JuliaLean.base.array.Error (Ref N) × ObjectState) : Prop :=
  ∃ (copied : Ref N) (header : BitArray N), result.1 = .ok copied ∧
    copied.identity = before.objects.length ∧ copied ≠ source ∧
    FreshCopyAllocation runtime source original dims before result.2 ∧
    ObjectContains result.2 copied header ∧
    header.chunks ≠ original.chunks ∧
    (result.2.memory.contents header.chunks).take (CopyAvailableWords before.memory original) =
      (before.memory.contents original.chunks).take (CopyAvailableWords before.memory original) ∧
    (let required := (original.len.val.toNat + 63) / 64
     if required ≤ (before.memory.contents original.chunks).length then
       result.2.memory.contents header.chunks =
         (before.memory.contents original.chunks).take required ∧
       (∀ i : Nat, i < original.len.val.toNat →
         PackedBitValue result.2.memory header i = PackedBitValue before.memory original i) ∧
       (∀ i : Nat, original.len.val.toNat ≤ i → i < 64 * required →
         PackedBitValue result.2.memory header i = PackedBitValue before.memory original i)
     else
       (result.2.memory.contents header.chunks)[required - 1]? = some (some (u64 0)))

/-- Same-type BitArray constructors produce independent copies whenever the
needed physical source prefix is readable. The source chunk count need not
match the logical length: extra chunks are ignored; too few readable chunks
still yield a fresh object containing the available prefix, with no promise
about unavailable logical values. Complete readable backing gives equality of
all logical bits and of raw final-word padding, without assuming that padding
was zero. Source storage and every old alias remain unchanged.
Julia source: base/bitarray.jl:535-536,429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Callees: base/abstractarray.jl:1154-1157,1211-1214.
Julia documentation: doc/src/manual/arrays.md:64 (copy); physical-prefix and
padding clauses describe the source's explicit packed-copy invariant. -/
def CopyConstructorsReadablePrefix : Prop :=
  ∀ (N : Nat) (runtime : AllocationData) (source : Ref N) (original : BitArray N)
    (dims : Dims N) (before : ObjectState), TupleCountFits N →
    ObjectContains before source original → CopySourceShape original dims →
    before.memory.validVector original.chunks → ReadableCopyPrefix before.memory original →
    (AcceptedNativeDimensions dims → AllocationInput runtime before.memory →
      CopyPrefixOutcome runtime source original dims before
        ((JuliaLean.base.bitarray.Models1Group15.typedCopy runtime source).run before) ∧
      CopyPrefixOutcome runtime source original dims before
        ((JuliaLean.base.bitarray.Models1Group15.copySame runtime source).run before)) ∧
    (¬ AcceptedNativeDimensions dims →
      ((JuliaLean.base.bitarray.Models1Group15.typedCopy runtime source).run before).1 =
        .error (.argument "invalid Array dimensions") ∧
      ((JuliaLean.base.bitarray.Models1Group15.copySame runtime source).run before).1 =
        .error (.argument "invalid Array dimensions"))

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15
open JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

private theorem emptyNativeMap :
    nativeMapDims (⟨[], rfl⟩ : Dims 0) = (⟨[], rfl⟩ : Dims 0) := rfl

private theorem emptyNativeUndef (runtime : AllocationData) (s : State) :
    (nativeTupleUndef runtime (⟨[], rfl⟩ : Dims 0)).run s =
      (.ok (⟨s.arrays.length, int 1, []⟩ : BitArray 0),
        shiftFreshHeap s [some (u64 0)]) := by
  rw [nativeTupleUndef, emptyNativeMap]
  exact rc_undef_rankZero runtime s

private theorem fillSingleWord (s : State) (old word : U64) :
    (fillChunkWord s.arrays.length word).run (shiftFreshHeap s [some old]) =
      (.ok (), shiftFreshHeap s [some word]) := by
  have hlength := shiftFreshLength s [some old]
  have hset : (mutableSet s.arrays.length word (int 1)).run (shiftFreshHeap s [some old]) =
      (.ok (), shiftFreshHeap s [some word]) := by
    simpa using shiftFreshSet s [some old] 0 word (by simp) (by simp)
  have hindices : (chunkIndices s.arrays.length).run (shiftFreshHeap s [some old]) =
      (.ok [int 1], shiftFreshHeap s [some old]) := by
    simp [chunkIndices, JuliaLean.base.abstractarray.eachindexDense, hlength]
    rfl
  simp [fillChunkWord, JuliaLean.base.array.fillBang, JuliaLean.base.array.fillTyped,
    hindices, hset]

private theorem fillChunkZero_eq (handle : Nat) :
    fillChunkZero handle = fillChunkWord handle (u64 0) := rfl

private theorem emptyFalseRun (runtime : AllocationData) (s : State) :
    (falsesEmpty runtime).run s =
      (.ok (⟨s.arrays.length, int 1, []⟩ : BitArray 0),
        shiftFreshHeap s [some (u64 0)]) := by
  simp [falsesEmpty, emptyNativeUndef, fillBool, fillConvert,
    JuliaLean.base.number.convertSame, fillChunkZero_eq, fillSingleWord,
    show (int 1).val ≠ (int 0).val from by decide]

private theorem emptyTrueRun (runtime : AllocationData) (s : State) :
    (truesEmpty runtime).run s =
      (.ok (⟨s.arrays.length, int 1, []⟩ : BitArray 0),
        shiftFreshHeap s [some (u64 1)]) := by
  have hlength : (mutableLength s.arrays.length).run (shiftFreshHeap s [some u64Max]) =
      (.ok (int 1), shiftFreshHeap s [some u64Max]) := by
    simpa using shiftFreshLength s [some u64Max]
  have hread : (mutableGet s.arrays.length (int 1)).run (shiftFreshHeap s [some u64Max]) =
      (.ok u64Max, shiftFreshHeap s [some u64Max]) := by
    simpa using shiftFreshRead s [some u64Max] 0 u64Max (by decide) (by decide) rfl
  have hset : (mutableSet s.arrays.length (u64 1) (int 1)).run
      (shiftFreshHeap s [some u64Max]) = (.ok (), shiftFreshHeap s [some (u64 1)]) := by
    simpa using shiftFreshSet s [some u64Max] 0 (u64 1) (by decide) (by decide)
  have hmask : and_int u64Max (maskEndArray (⟨s.arrays.length, int 1, []⟩ : BitArray 0)) =
      u64 1 := by
    change and_int u64Max (maskEnd (int 1)) = u64 1
    decide
  simp [truesEmpty, emptyNativeUndef, fillBool, fillConvert,
    JuliaLean.base.number.convertSame, fillSingleWord, hlength, hread, hmask, hset,
    show (int 1).val ≠ (int 0).val from by decide]

private theorem emptyPost (runtime : AllocationData) (s : State) (b : Bool) :
    let word := u64 (if b then 1 else 0)
    let B : BitArray 0 := ⟨s.arrays.length, int 1, []⟩
    ConstructorPost runtime (⟨[], rfl⟩ : Dims 0) s (shiftFreshHeap s [some word]) B ∧
      LogicalBitsEqual (shiftFreshHeap s [some word]) B b := by
  let word := u64 (if b then 1 else 0)
  let B : BitArray 0 := ⟨s.arrays.length, int 1, []⟩
  change ConstructorPost runtime (⟨[], rfl⟩ : Dims 0) s (shiftFreshHeap s [some word]) B ∧
    LogicalBitsEqual (shiftFreshHeap s [some word]) B b
  have hw : 0 ≤ word.val ∧ word.val ≤ 1 := by
    dsimp [word]
    cases b <;> decide
  constructor
  · unfold ConstructorPost
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [shiftFreshHeap]
    · simp [OldHeapPreserved, shiftFreshHeap]
    · refine ⟨⟨(s.memories.length, int 1), int 1⟩, [some word], ?_, ?_,
        rfl, rfl, rfl, ?_, ?_, ?_⟩
      · exact shiftFreshHeader s [some word]
      · exact shiftFreshMemory s [some word]
      · intro slot hslot
        simp only [List.mem_singleton] at hslot
        subst slot
        exact ⟨word, rfl⟩
      · simp [DimensionProduct, shiftFreshHeap]
      · intro k bit value hcell hbit htail
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hcell
          subst value
          have htail' : 1 ≤ bit := by simpa [DimensionProduct] using htail
          have hn : (2 : Nat) ≤ 2 ^ bit := by
            have h : (2 : Nat) ^ 1 ≤ 2 ^ bit := Nat.pow_le_pow_right (by decide) htail'
            simpa using h
          have hi : (2 : Int) ≤ (2 : Int) ^ bit := by
            change (2 : Int) ≤ ((2 ^ bit : Nat) : Int)
            omega
          have hd : word.val / (2 : Int) ^ bit = 0 :=
            Int.ediv_eq_zero_of_lt hw.1 (by omega)
          rw [hd]
          rfl
        | succ k => simp at hcell
  · intro i hi
    have hi0 : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    have hc := shiftFreshContents s [some word] (by simp)
    dsimp only [PackedBitValue, B]
    rw [hc]
    cases b <;> rfl

private theorem emptyOutcome (runtime : AllocationData) (s : State) (b : Bool) :
    BooleanAllocationOutcome runtime (⟨[], rfl⟩ : Dims 0) s b
      (.ok (⟨s.arrays.length, int 1, []⟩ : BitArray 0),
        shiftFreshHeap s [some (u64 (if b then 1 else 0))]) := by
  have hd : AcceptedNativeDimensions (⟨[], rfl⟩ : Dims 0) := by
    simp [AcceptedNativeDimensions, DimensionProduct, IntTy.max, IntTy.signed, IntTy.bits]
  have hp := emptyPost runtime s b
  exact ⟨⟨hd, hp.1⟩, hp.2⟩

theorem EmptyDimensionsBooleanValues_proven : EmptyDimensionsBooleanValues := by
  intro runtime s _
  constructor
  · rw [emptyFalseRun]
    exact emptyOutcome runtime s false
  · rw [emptyTrueRun]
    exact emptyOutcome runtime s true

end JuliaLean.Proofs.base.bitarray.Models1Group15



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

theorem Models1G15ReshapeRankSharing_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ReshapeOtherSharesStorageAndErrors := by
  intro N R runtime source original dims differentRank state hn hr hobj hshape
  exact Models1G15BitreshapeFreshAllocation_proven N R runtime source original dims state
    hn hr hobj hshape

theorem Models1G15ReshapeSameIdentity_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ReshapeSameIdentityShapeAndErrors := by
  intro N runtime source original dims state hn hobj hshape
  have hread := rc_readObject state source original hobj
  change if dims.val = bitArraySizeRanked original then _ else _
  by_cases hs : dims.val = bitArraySizeRanked original
  · rw [if_pos hs]
    simp only [reshapeSame, rc_run_bind, hread, hs, beq_self_eq_true, ite_true, rc_run_pure,
      and_self]
  · rw [if_neg hs]
    have hrun : (reshapeSame runtime source dims).run state =
        (bitreshape runtime source dims).run state := by
      simp only [reshapeSame, rc_run_bind, hread, beq_iff_eq, hs, ite_false]
    rw [hrun]
    exact Models1G15BitreshapeFreshAllocation_proven N N runtime source original dims state
      hn hn hobj hshape
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.ChatGPT.Batch5.Group2 JuliaLean.ChatGPT.Batch5.Group4

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false


theorem native9EmptyRun (runtime : JuliaLean.base.bitarray.Models1Group15.AllocationData) (s : State) :
    (JuliaLean.base.bitarray.Models1Group15.empty runtime).run s =
      (.ok ⟨s.arrays.length, int 0, []⟩,
       {s with arrays := s.arrays ++ [MutableVector.mk (runtime.emptyMemory, int 1) (int 0)]}) := by
  rfl

theorem Models1G15EmptyVector_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.EmptyVectorFreshHeader := by
  intro runtime s hinput
  dsimp only
  rw [native9EmptyRun]
  have hheader :
      (s.arrays ++ [MutableVector.mk (runtime.emptyMemory, int 1) (int 0)])[s.arrays.length]? =
        some (MutableVector.mk (runtime.emptyMemory, int 1) (int 0)) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine ⟨rfl, rfl, rfl, ?_, rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
  · exact List.take_left
  · exact List.take_length
  · simp only [MutableMemory.contents, hheader]
    rfl
  · exact ⟨_, hheader, rfl, rfl⟩


theorem native9NegativeLoop (dims : List I64) (start : Int) (s : State)
    (k : Nat) (d : I64) (hget : dims[k]? = some d) (hnegative : d.val < 0)
    (hprior : ∀ (j : Nat) (e : I64), j < k → dims[j]? = some e → 0 ≤ e.val) :
    (forIn dims (int start) (fun (value index : I64) => do
      if value.val < 0 then
        throw (Error.argument
          s!"dimension size must be ≥ 0, got {value.val} for dimension {index.val}")
      pure (ForInStep.yield (index + int 1))) : BitMutationM I64).run s =
      (.error (.argument
        s!"dimension size must be ≥ 0, got {d.val} for dimension {(int (start + k)).val}"), s) := by
  induction dims generalizing k start with
  | nil => simp only [List.getElem?_nil] at hget; contradiction
  | cons value rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst value
      simp only [List.forIn_cons, hnegative, ite_true, Int.natCast_zero, Int.add_zero]
      rfl
    | succ k =>
      have hvalue : ¬ value.val < 0 := by
        have hv := hprior 0 value (by omega) rfl
        omega
      have hrest : rest[k]? = some d := by
        simpa only [List.getElem?_cons_succ] using hget
      have hpriorRest : ∀ (j : Nat) (e : I64), j < k → rest[j]? = some e → 0 ≤ e.val := by
        intro j e hj he
        exact hprior (j + 1) e (by omega) he
      simp only [List.forIn_cons, hvalue, ite_false]
      change (forIn rest (int start + int 1) (fun (value index : I64) => do
        if value.val < 0 then
          throw (Error.argument
            s!"dimension size must be ≥ 0, got {value.val} for dimension {index.val}")
        pure (ForInStep.yield (index + int 1))) : BitMutationM I64).run s = _
      rw [packedInt_add]
      rw [ih (start + 1) k hrest hpriorRest]
      have he : start + 1 + (k : Int) = start + ((k + 1 : Nat) : Int) := by omega
      rw [he]

theorem Models1G15UndefNegativeOrder_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.UndefFirstNegativeDimension := by
  intro N runtime dims s k d hcount hget hnegative hprior
  have hlt : k < dims.val.length := (List.getElem?_eq_some_iff.mp hget).choose
  have hbound : k + 1 ≤ 9223372036854775807 := by
    have hrank := dims.property
    change (N : Int) ≤ 9223372036854775807 at hcount
    omega
  have hloop := native9NegativeLoop dims.val 1 s k d hget hnegative hprior
  have hposition : (int (1 + (k : Int))).val = ((k + 1 : Nat) : Int) := by
    rw [show (1 : Int) + k = ((k + 1 : Nat) : Int) by omega]
    exact packedInt_val (k + 1) hbound
  rw [hposition] at hloop
  dsimp only
  unfold JuliaLean.base.bitarray.Models1Group15.undef
  rw [shape_run_bind, hloop]
  exact ⟨rfl, rfl⟩
end JuliaLean.ChatGPT.Batch9.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

/-- The Colon offset is the zero-based start of whole-array indexing.
Julia source: base/bitarray.jl:695. -/
def ReusedColonOffsetZero : Prop := indexOffsetColon.val = 0

/-- Unconditional rejecting constructor branches neither inspect the iterator
nor mutate storage. All iterator values, target names, ranks and heaps are
included. Julia source: base/bitarray.jl:594,600-602. -/
def ReusedConstructorRejections : Prop :=
  ∀ (N : Nat) (Iterator : Type) (itr : Iterator) (name : String)
    (before : MutableMemory U64),
    ((genBitArrayInfinite (N := N) itr).run before).1 =
      .error (.argument "infinite-size iterable used in BitArray constructor") ∧
    ((genBitArrayInfinite (N := N) itr).run before).2 = before ∧
    (∀ result ∈ [
      (genBitArrayNVectorWrongShape N itr).run before,
      (genBitArrayNWrongShape (N := 1) (T := Unit) name itr).run before,
      (genBitArrayNGenericWrongShape (N := 1) (T := Unit) name itr).run before],
      (∃ message : String, result.1 = .error (.dimensionMismatch message)) ∧
      result.2 = before) ∧
    (∀ result ∈ [
      (genBitArrayNWrongShape (N := N) (T := Unit) name itr).run before,
      (genBitArrayNGenericWrongShape (N := N) (T := Unit) name itr).run before],
      (∃ message : String, result.1 = .error (.dimensionMismatch message)) ∧
      result.2 = before)
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.ChatGPT.Batch3.Group1

theorem Models1G15ReusedConstructorRejections_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedConstructorRejections := by
  intro N Iterator itr name before
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro result h
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      exact ⟨⟨_, rfl⟩, rfl⟩
    · rcases List.mem_cons.mp h with h | h
      · rw [h]
        exact ⟨⟨_, rfl⟩, rfl⟩
      · rw [List.mem_singleton.mp h]
        exact ⟨⟨_, rfl⟩, rfl⟩
  · intro result h
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      exact ⟨⟨_, rfl⟩, rfl⟩
    · rw [List.mem_singleton.mp h]
      exact ⟨⟨_, rfl⟩, rfl⟩

theorem Models1G15ReusedColonOffsetZero_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedColonOffsetZero := by
  rfl
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray


/-- A size hint changes capacity, while retaining the same BitVector and every
logical chunk. Non-native Integer arguments reach MethodError before mutation.
Julia source: base/bitarray.jl:120,798-801.
Documentation: base/array.jl:1577-1608; doc/src/manual/arrays.md:23-34. -/
def SizehintPreserves : Prop :=
  ∀ (s : Heap) (B : BitVector) (sz : JuliaLean.base.bitarray.Models1Group16.SizeHintArgument),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.sizehint B sz).run s
    match sz with
    | .native _ =>
        result.1 = .ok B ∧ result.2.contents B.chunks = s.contents B.chunks
    | .otherInteger _ =>
        result.1 = .error (.method "num_bit_chunks") ∧ result.2 = s


/-- Empty coordinate tails retain arbitrary scalar payloads without requiring
native integer or CartesianIndex conversion. Julia source: base/bitarray.jl:1674,1685. -/
def EmptyCoordinatePayload : Prop :=
  ∀ (I S : Type) (payload : I) (shape : S),
    let result := JuliaLean.base.bitarray.Models1Group16.overflowIndEmptyAny payload () shape
    result.1 = payload ∧
    JuliaLean.base.bitarray.Models1Group16.toIndEmptyAny payload result.2 = payload

theorem EmptyCoordinatePayload_proven : EmptyCoordinatePayload := by
  intro I S payload shape
  exact ⟨rfl, rfl⟩
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch3.Group1

theorem bh_num_chunks_value (n : I64) :
    (numBitChunks n).val = (n.val + 63) / 64 := by
  have hb := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
  have hm : (mod64 n == int 0) = decide (n.val % 64 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      rw [scalar_mod64_val] at hv
      exact hv
    · intro h
      apply Subtype.ext
      exact (scalar_mod64_val n).trans h
  unfold numBitChunks
  rw [hm]
  by_cases hz : n.val % 64 = 0
  · simp only [hz, decide_true, ite_true]
    change wrapInt .i64 ((div64 n).val + 0) = _
    rw [scalar_div64_val]
    have hw : wrapInt .i64 (n.val / 64 + 0) = n.val / 64 + 0 := by
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ n.val / 64 + 0 ∧
        n.val / 64 + 0 ≤ 9223372036854775807
      omega
    rw [hw]
    omega
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    change wrapInt .i64 ((div64 n).val + 1) = _
    rw [scalar_div64_val]
    have hw : wrapInt .i64 (n.val / 64 + 1) = n.val / 64 + 1 := by
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ n.val / 64 + 1 ∧
        n.val / 64 + 1 ≤ 9223372036854775807
      omega
    rw [hw]
    omega

theorem bh_num_chunks_bound (n : I64) :
    (numBitChunks n).val.toNat ≤ 144115188075855872 := by
  rw [bh_num_chunks_value]
  have hb := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
  omega

theorem bh_u64_memory_fits (n : Nat) (hn : n < 1152921504606846976) :
    memoryFits (allocationSummary uint64Layout) n := by
  change n < 9223372036854775806 ∧ n * 8 + 0 < 9223372036854775806
  omega

theorem bh_overallocation_bound (n : Nat) (hn : n < 144115188075855872) :
    overallocationNat n < 288230376151711744 := by
  have hexp : (if n = 0 then 0 else n.log2 + 1) ≤ 57 := by
    by_cases hz : n = 0
    · simp only [hz, ite_true]; omega
    · simp only [hz, ite_false]
      have hl : n.log2 < 57 := (Nat.log2_lt hz).mpr hn
      omega
  have hp : 2 ^ ((if n = 0 then 0 else n.log2 + 1) * 7 / 8) ≤ 2 ^ 49 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold overallocationNat
  rw [if_neg (by unfold typemaxNat; omega)]
  omega

theorem bh_sizehint_plan (g : VectorGeometry) (sz : Int)
    (hoff : 1 ≤ g.offset) (hlen : g.offset - 1 + g.length ≤ g.memlen)
    (hmem : g.memlen < 1152921504606846976)
    (hsz : sz.toNat ≤ 144115188075855872) :
    ∃ output, sizehintPlan (allocationSummary uint64Layout) g sz false true = .ok output := by
  have hlenmem : g.length ≤ g.memlen := by omega
  have hoffmem : g.offset ≤ g.memlen + 1 := by omega
  unfold sizehintPlan
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq,
    Bool.false_eq_true, ite_false, Bool.false_and]
  split
  · rename_i htarget
    split
    · exact ⟨_, rfl⟩
    · unfold allocationPlan
      rw [if_pos (bh_u64_memory_fits _ (by omega))]
      exact ⟨_, rfl⟩
  · rename_i htarget
    have ht : max sz.toNat g.length ≤ 144115188075855872 := by omega
    have hm : g.memlen < 144115188075855872 := by omega
    have hnew : g.length + (max sz.toNat g.length - g.length) =
        max sz.toNat g.length := by omega
    have hbig : g.offset - 1 + (g.length + (max sz.toNat g.length - g.length)) <
        288230376151711744 := by omega
    unfold growendPlan
    split
    · exact ⟨_, rfl⟩
    · unfold growendInternalPlan
      rw [if_neg (by unfold typemaxNat; omega)]
      split
      · exact ⟨_, rfl⟩
      · have ho := bh_overallocation_bound g.memlen hm
        unfold allocationPlan
        rw [if_pos (bh_u64_memory_fits _ (by omega))]
        exact ⟨_, rfl⟩


theorem Models1G16SizehintPreserves_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group16.SizehintPreserves := by
  intro s B sz hread
  cases sz with
  | otherInteger name => exact ⟨rfl, rfl⟩
  | native requested =>
    rcases hread with ⟨hvalid, hlen, hrank, hshape, hdims, hdimsmax,
      hprod, hcount, hinitialized, hmem⟩
    obtain ⟨memory, offset, count, slots, hvec⟩ := validVector_vecAt hvalid
    have hslots : slots.length < 1152921504606846976 :=
      hmem slots (List.mem_of_getElem? hvec.2.1)
    have hgeom := hvec.2.2
    obtain ⟨output, hplan⟩ := bh_sizehint_plan
      ⟨slots.length, offset.val.toNat, count.val.toNat⟩ (numBitChunks requested).val
      (by dsimp only; omega) (by dsimp only; omega) hslots (bh_num_chunks_bound requested)
    have hfollow := solArray.sizehint_native_follows uint64Layout s B.chunks memory
      offset count slots hvec (numBitChunks requested) false true
    rw [opusGrowth.VecAt.geometry hvec] at hfollow
    obtain ⟨result, after, hrun, hresult, hafter, hcontents, hothers⟩ := hfollow.2 output hplan
    subst result
    have hraw :
        (JuliaLean.base.array.sizehint
          JuliaLean.base.bitarray.Models1Group16.chunkStorage pure
          JuliaLean.base.bitarray.Models1Group16.growChunksAtFront growChunkVector
          B.chunks (numBitChunks requested) false true).run s = (.ok B.chunks, after) := hrun
    simp only [JuliaLean.base.bitarray.Models1Group16.sizehint, bitVectorSizehint,
      JuliaLean.base.bitarray.Models1Group16.reserveChunks, stateExcept_bind,
      hraw, stateExcept_pure]
    exact ⟨True.intro, hcontents⟩
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models2Group11

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models2Group11

/-- A BitArray's data-identity tuple contains exactly the stored native pointer
bits of its chunks' backing memory. Reading this identity leaves both the full
heap and the pointer snapshot unchanged. The only premises identify an existing
chunk-array header and its stored pointer, and align the runtime pointer table
with the memory-object table. No vector-window, size, shape, readability, address
alignment, nonzero-address, or pointer-uniqueness condition is imposed. In
particular, empty BitArrays and empty backing memories still return one UInt.
The expected address is independently observed field data, not an array handle,
a memory-object index, an offset-adjusted address, or a supplied dataids callee.
Julia source: base/bitarray.jl:110;
base/abstractarray.jl:1627-1628; base/boot.jl:1198
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/abstractarray.jl:1617-1625. -/
def DataIdsStoredAddress : Prop :=
  ∀ (N : Nat) (state : DataIdState) (B : BitArray N)
    (header : MutableVector) (address : U64),
    state.pointers.length = state.memory.memories.length →
    state.memory.arrays[B.chunks]? = some header →
    state.pointers[header.reference.1]? = some address →
    (dataIds B).run state = (.ok [address], state)

/-- Arrays whose chunk headers ultimately carry the same raw backing-memory
pointer report the same singleton identity without changing any state. The
headers may be distinct and may have different memory-reference offsets,
lengths, logical BitArray dimensions, or ranks. The two memory-object identities
may also differ: this property deliberately permits equal pointer bits in
different memory rows, including empty-storage cases. It does not mistake
coarse data-segment identity for a claim that two logical windows overlap.
Every referenced pointer and header is quantified; no disjointness or
injectivity assumption is made about the address snapshot.
Julia source: base/bitarray.jl:110;
base/abstractarray.jl:1627-1628; base/boot.jl:1198
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/abstractarray.jl:1617-1625, mutable data segments. -/
def DataIdsEqualBackingAddresses : Prop :=
  ∀ (N M : Nat) (state : DataIdState) (A : BitArray N) (B : BitArray M)
    (left right : MutableVector) (address : U64),
    state.pointers.length = state.memory.memories.length →
    state.memory.arrays[A.chunks]? = some left →
    state.memory.arrays[B.chunks]? = some right →
    state.pointers[left.reference.1]? = some address →
    state.pointers[right.reference.1]? = some address →
    (dataIds A).run state = (.ok [address], state) ∧
    (dataIds B).run state = (.ok [address], state)

theorem DataIdsStoredAddress_proven : DataIdsStoredAddress := by
  intro N state B header address _ hheader haddress
  have hread : (mutableVector B.chunks).run state.memory = (.ok header, state.memory) := by
    simp [mutableVector, hheader]
  have hlift : (liftDataIdMemory (mutableVector B.chunks)).run state = (.ok header, state) := by
    simp only [liftDataIdMemory, JuliaLean.CompletionState1.runBind,
      JuliaLean.CompletionState1.runGet, hread]
    rfl
  simp only [dataIds, bitArrayDataIds, chunkVectorDataIds,
    JuliaLean.CompletionState1.runBind, hlift]
  simp [JuliaLean.base.abstractarray.dataidsDense, memoryDataIds, haddress,
    JuliaLean.base.abstractarray.dataidsMemory]

theorem DataIdsEqualBackingAddresses_proven : DataIdsEqualBackingAddresses := by
  intro N M state A B left right address htable hleft hright haddressLeft haddressRight
  exact ⟨DataIdsStoredAddress_proven N state A left address htable hleft haddressLeft,
    DataIdsStoredAddress_proven M state B right address htable hright haddressRight⟩
end JuliaLean.Proofs.base.bitarray.Models2Group11



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesBitarray1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-vec-resize-alias", juliaFile := "base/bitarray.jl", juliaFns := ["reshape(::BitArray, dims)", "vec(::BitArray)", "push!(::BitVector, x)", "pop!(::BitVector)"],
    statement := "push!/pop! on v = vec(M) leave M a valid BitArray (num_bit_chunks(length(M)) chunks, unused bits zero).", source := "invariant: unused bits zero (base/bitarray.jl:5-6), relied on by ==, count, hash; reshape shares data (reshape docstring)",
    issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml",
    status := .refuted, prop := ``VecAliasKeepsParentValid, thm := some ``JuliaLean.ChatGPT.Batch4.Group8.BitarraysVecResizeAlias_refuted }
]
def entriesBitarray2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-constructor-shape", juliaFile := "base/bitarray.jl", juliaFns := ["BitArray@28", "similar@359", "similar@363", "similar@366", "_bitreshape@476", "BitArray@500", "BitArray@498", "falses@396", "falses@397", "trues@415", "trues@416", "fill_bitarray_from_itr!@634", "gen_bitarray@576", "gen_bitarray@585", "gen_bitarray@589", "gen_bitarrayN@598", "BitVector@76", "similar@360", "similar@361", "reshape@472", "BitArray{N}@567", "generated@1177"],
    statement := "Undefined bit-array constructors preserve requested dimensions and allocate enough packed chunks.", source := "obvious invariant; base/bitarray.jl:28",
    status := .proven, prop := ``BitArrayConstructorShape, thm := some ``JuliaLean.ChatGPT.Batch5.Group2.BitarrayBitArrayConstructorShape_proven }
]
def entriesBitarray3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-fill-constructors", juliaFile := "base/bitarray.jl", juliaFns := ["falses@398", "trues@417", "falses@394", "trues@413", "one@419"],
    statement := "falses and trues construct arrays with requested dimensions and uniform Boolean values.", source := "obvious invariant; base/bitarray.jl:394",
    status := .todo, prop := ``BitArrayFillConstructors, thm := none, notes := "No complete exact proof returned. nonnegative checked dimensions and the corrected fill model are needed." },
  { id := "bitarray-bit-array-filter-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["falses@395", "trues@414", "BitArray@68", "BitArray{N}@69", "BitArray@70", "BitArray{N}@71", "map@1756", "map@1757", "map@1758", "map@1759", "map!@1761", "map!@1762", "map!@1763", "map!@1764", "generated@1776", "generated@1777", "bit_map@1783", "bit_map!@1795", "bit_map!@1814", "filter@1839", "_cat@1925"],
    statement := "Filtering a BitArray returns, in order, exactly the elements accepted by the predicate.", source := "obvious invariant; base/bitarray.jl:68",
    status := .todo, prop := ``BitArrayFilterAgrees, thm := none, notes := "Statement defect: false for List.replicate (2^64) true, whose modeled native length wraps to zero and produces an empty filtered list; Julia cannot construct this input, and xs.length \u2264 2^59 is a sufficient bound for the installed mask allocator." },
  { id := "bitarray-bit-array-metadata-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["length@102", "_msk_end@119", "dumpbitcache@347", "iterate@352", "size@103", "size@104", "isassigned@106", "IndexStyle@108", "dataids@110", "all@1724", "any@1736"],
    statement := "Length, size, assignment bounds, linear index style, and storage identity match BitArray metadata; after rank-changing reshape, a write through the new shape remains visible through the parent.", source := "base/bitarray.jl:102-110,472-485",
    status := .proven, prop := ``Round5.BitArrayMetadataAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group2.BitarrayBitArrayMetadataAgrees_proven },
  { id := "bitarray-bit-array-reshape-keeps-bits", juliaFile := "base/bitarray.jl", juliaFns := ["reshape@475"],
    statement := "Valid same-rank and rank-changing reshapes preserve all logical bits and report the checked requested shape below the native-size bound.", source := "base/bitarray.jl:472-485; base/checked.jl:106-114",
    status := .proven, prop := ``Round5.BitArrayReshapeKeepsBits, thm := some ``JuliaLean.ChatGPT.Batch5.Group2.BitarrayBitArrayReshapeKeepsBits_proven },
  { id := "bitarray-bit-array-sizeof-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["sizeof@1939"],
    statement := "For valid BitArrays with length less than typemax(Int)/2, packed storage size is eight bytes per UInt64 chunk.", source := "base/bitarray.jl:1939-1940",
    status := .proven, prop := ``Round2.BitArraySizeofAgrees, thm := some ``Round2.BitArraySizeofAgrees_proven },
  { id := "bitarray-bit-find-all-spec", juliaFile := "base/bitarray.jl", juliaFns := ["allindices!@1652", "allindices!@1661", "allindices!@1666", "_overflowind@1674", "_overflowind@1675", "_toind@1685", "_toind@1686", "findall@1688", "findall@1717"],
    statement := "findall returns one index for each true bit and no indices for false bits.", source := "obvious invariant; base/bitarray.jl:1652",
    status := .todo, prop := ``BitFindAllSpec, thm := none }
]
def entriesBitarray4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-tuple-constructor-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["BitVector@95"],
    statement := "BitVector(tuple) stores the tuple Boolean elements in order.", source := "obvious invariant; base/bitarray.jl:95",
    status := .todo, prop := ``TupleConstructorAgrees, thm := none, notes := "Statement defect: false for a Boolean list of length 2^63 because every bitValues observation has length at most 2^63-1; Julia cannot construct that tuple, and the sufficient bound xs.length \u2264 2^63-1 is established by root9TupleSupported." },
  { id := "bitarray-assigned-logical-extent-full", juliaFile := "base/bitarray.jl",
    juliaFns := ["isassigned(::BitArray, ::Int)"],
    statement := "BitArray's public assignment query recognizes exactly the separately enumerated one-based logical positions, for every native index and nonnegative native logical length; it makes no claim about the physical chunk allocation.",
    source := "base/bitarray.jl:102-106", status := .proven,
    prop := ``Archive20261102Round6.BitArrayAssignedLogicalExtentFull, thm := some ``JuliaLean.ChatGPT.Batch4.Group8.BitarrayAssignedLogicalExtentFull_proven }
]
def entriesBitarray5 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-matrix-one-agrees", juliaFile := "base/bitarray.jl",
    juliaFns := ["one(::BitMatrix)"],
    statement := "The multiplicative identity of every square BitMatrix is a fresh packed matrix with exactly its diagonal true; nonsquare matrices throw DimensionMismatch.",
    source := "base/bitarray.jl:419-427", status := .todo,
    prop := ``Archive20261102Round6.BitMatrixOneFull, thm := none, notes := "The returned matrix construction certificate fails kernel checking at native9RangeValues with a deep-recursion error, including at maxRecDepth 20000. No complete kernel-checked certificate is installed." }
]
def entriesBitarray6 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-dataids-stored-pointer",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["dataids(B::BitArray)"],
    statement := "Every valid BitArray reference returns the singleton UInt stored in its backing memory's pointer field and preserves all state, independently of rank, dimensions, offsets, length or contents.",
    source := "base/bitarray.jl:110; base/abstractarray.jl:1617-1628; base/boot.jl:1198",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.DataIdsStoredAddress,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.DataIdsStoredAddress_proven },
  { id := "bitarray-dataids-alias-pointer",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["dataids(B::BitArray)"],
    statement := "BitArrays whose backing memory pointer fields have equal raw address bits return the same singleton data ID without state changes, even for distinct headers, differing offsets and sizes, empty arrays or distinct memory identities.",
    source := "base/bitarray.jl:110; base/abstractarray.jl:1617-1628",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.DataIdsEqualBackingAddresses,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.DataIdsEqualBackingAddresses_proven }
]
def entriesBitarray7 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-empty-coordinate-payload", juliaFile := "base/bitarray.jl",
    juliaFns := ["_overflowind(i1, ::Tuple{}, size)", "_toind(i1, ::Tuple{})"],
    statement := "Empty coordinate tails preserve arbitrary scalar payloads without conversion.",
    source := "base/bitarray.jl:1674,1685", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.EmptyCoordinatePayload, thm := some ``JuliaLean.Proofs.base.bitarray.Models1Group16.EmptyCoordinatePayload_proven,
    notes := "Independent helper payload invariant over the complete represented type domain. Unproved and unchecked." }
]
def entriesBitarray8 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-sizehint-preserves", juliaFile := "base/bitarray.jl",
    juliaFns := ["sizehint!(::BitVector, ::Integer)"],
    statement := "A BitVector size hint preserves its logical chunks and identity; Integer types other than native Int fail num_bit_chunks dispatch before mutation.",
    source := "base/bitarray.jl:120,798-801; base/array.jl:1577-1608", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.SizehintPreserves, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G16SizehintPreserves_proven,
    notes := "" }
]
def entriesBitarray9 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-undef-shape-storage", juliaFile := "base/bitarray.jl",
    juliaFns := ["BitArray{N}(::UndefInitializer, dims::Vararg{Int,N}) where N"],
    statement := "For every machine-sized native Int dimension tuple, construction succeeds exactly when dimensions pass the mathematical Core dimension constraints; success returns the exact shape and element count, a fresh chunk header, readable packed storage with zero padding, and preserves old heap objects. Rejection is an ArgumentError with no heap changes.",
    source := "base/bitarray.jl:28-67; base/boot.jl:782-818; doc/src/manual/arrays.md:1236-1238", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.UndefShapeStorageAndErrors, thm := none,
    notes := "No complete exact proof returned. nonnegative dimension classification and general fresh-storage and padding postconditions remain unverified." },
  { id := "bitarray-undef-negative-order", juliaFile := "base/bitarray.jl",
    juliaFns := ["BitArray{N}(::UndefInitializer, dims::Vararg{Int,N}) where N"],
    statement := "The first negative dimension determines the ArgumentError value and one-based position; the error precedes dimension multiplication and allocation, preserves the entire heap, and is unaffected by earlier large nonnegative dimensions or later negative dimensions.",
    source := "base/bitarray.jl:28-33,45-51 (ordered dimension-validation invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.UndefFirstNegativeDimension, thm := some ``JuliaLean.ChatGPT.Batch9.Group4.Models1G15UndefNegativeOrder_proven,
    notes := "All signed Int dimensions are included; the only size premise is the runtime tuple field-count bound. No allocator validity assumption is needed on this pre-allocation failure path." },
  { id := "bitarray-empty-vector", juliaFile := "base/bitarray.jl",
    juliaFns := ["BitVector()"],
    statement := "BitVector() succeeds with length zero and size (0,), creates a fresh chunk-array header referring to shared empty UInt64 memory, and preserves all pre-existing array headers and memory objects.",
    source := "base/bitarray.jl:76; doc/src/manual/arrays.md:1236-1238 (empty-constructor invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.EmptyVectorFreshHeader, thm := some ``JuliaLean.ChatGPT.Batch9.Group4.Models1G15EmptyVector_proven,
    notes := "Quantifies every initial heap and runtime allocation-data choice with an existing shared empty UInt64 memory." },
  { id := "bitarray-tuple-constructor-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["BitVector(nt::Tuple{Vararg{Bool}})"],
    statement := "For every native Boolean tuple, BitVector creates a fresh chunk-array header for exactly the tuple length and preserves each Boolean value in order, including empty, singleton and multiword cases. Nonempty results have fresh backing memory; empty results share the runtime empty memory. Every old header and memory object is preserved and all padding bits are zero, independently of arbitrary raw allocation contents.",
    source := "base/bitarray.jl:79-98; base/broadcast.jl:321-325,898,928-934,980,1035-1073; doc/src/manual/functions.md:1141-1143", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.TupleConstructorValuesFreshStorage, thm := none,
    notes := "No complete exact proof returned. broadcast packing, full-word and remainder loop invariants, and the complete constructor postcondition remain unverified." },
  { id := "bitarray-similar-shape", juliaFile := "base/bitarray.jl",
    juliaFns := ["similar(B::BitArray)"],
    statement := "similar(B) allocates a fresh packed array with B's public shape and exact mathematical element count, independently of old chunk contents or alias-induced chunk resizing. It preserves old heap objects, zeroes padding, and rejects invalid shapes with the ordered constructor errors.",
    source := "base/bitarray.jl:359; base/abstractarray.jl:777-784; doc/src/manual/arrays.md:66", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.SimilarSameShapeFresh, thm := none,
    notes := "No complete exact proof returned. The complete constructor outcome combination remains open." },
  { id := "bitarray-similar-dimensions", juliaFile := "base/bitarray.jl",
    juliaFns := ["similar(B::BitArray, dims::Int...)", "similar(B::BitArray, dims::Dims)", "similar(B::BitArray, T::Type{Bool}, dims::Dims)"],
    statement := "The native dimension-varargs, dimension-tuple and explicit Bool similar overloads create fresh packed arrays with the requested dimensions and rank, preserve existing heap objects and zero padding, and handle negative or overflowing dimensions with the correct ordered errors.",
    source := "base/bitarray.jl:360-363; base/abstractarray.jl:777-784; doc/src/manual/arrays.md:66", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.SimilarSpecifiedShapeFresh, thm := none,
    notes := "All signed Int dimensions are included. No restriction is imposed on the unused input array's chunk memory or shape." },
  { id := "bitarray-falses-trues-native", juliaFile := "base/bitarray.jl",
    juliaFns := ["falses(dims::NTuple{N,Integer}) where N (native Int specialization)", "trues(dims::NTuple{N,Integer}) where N (native Int specialization)"],
    statement := "For every native Int dimension tuple, falses and trues allocate fresh packed arrays of the exact requested shape with every logical element respectively false or true and zero padding; invalid dimensions produce the ordered constructor errors without heap mutation.",
    source := "base/bitarray.jl:381-396,400-415; doc/src/manual/arrays.md:61-62", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.FalsesTruesNativeValues, thm := none,
    notes := "No complete exact proof returned. Allocation outcomes must be combined with Boolean filling." },
  { id := "bitarray-empty-dimensions-bools", juliaFile := "base/bitarray.jl",
    juliaFns := ["falses(dims::Tuple{})", "trues(dims::Tuple{})"],
    statement := "falses(()) and trues(()) succeed with fresh zero-dimensional BitArrays containing exactly one element, respectively false and true, preserving all old heap objects and the zero-padding invariant.",
    source := "base/bitarray.jl:381-397,400-416; doc/src/manual/arrays.md:61-62", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.EmptyDimensionsBooleanValues,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models1Group15.EmptyDimensionsBooleanValues_proven }
]
def entriesBitarray10 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-one-matrix-identity", juliaFile := "base/bitarray.jl",
    juliaFns := ["one(x::BitMatrix)"],
    statement := "For every native rank-two shape with a machine-representable exact element count, one returns a fresh same-shaped BitMatrix whose entries are true exactly on the diagonal, with readable packed storage, zero padding and every old heap object preserved. Nonsquare shapes raise DimensionMismatch before allocation and leave the complete heap unchanged.",
    source := "base/bitarray.jl:419-427; base/number.jl:367-390; doc/src/base/numbers.md:102; base/bitarray.jl:1-23 (packed-storage invariant)", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.OneMatrixIdentityAndErrors, thm := none,
    notes := "No complete exact proof returned. The diagonal-setting loop and full identity/error contract remain open." }
]
def entriesBitarray11 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-reshape-same-identity", juliaFile := "base/bitarray.jl",
    juliaFns := ["reshape(B::BitArray{N}, dims::NTuple{N,Int}) where N"],
    statement := "Same-rank reshape returns the identical mutable object with no state changes for an equal public shape. Every other signed native shape follows the exact dimension-check/error partition or returns a fresh header sharing the original chunk vector, preserving all old headers and data and retaining the temporary zero-shaped allocation.",
    source := "base/bitarray.jl:472-474,476-485; base/reshapedarray.jl:67-79; base/boot.jl:782-818; doc/src/manual/arrays.md:63", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReshapeSameIdentityShapeAndErrors, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ReshapeSameIdentity_proven,
    notes := "Quantifies typed mutable object references and all native signed dimension tuples. Rank-one stale/unset dims are ignored. No source chunk-count, validity, readability or nonaliasing premise is imposed. AllocationInput is required only in the successful allocation branch, not on errors or the identity branch." },
  { id := "bitarray-reshape-rank-sharing", juliaFile := "base/bitarray.jl",
    juliaFns := ["reshape(B::BitArray, dims::Tuple{Vararg{Int}})"],
    statement := "A different-rank reshape either reports the appropriate dimension error without changing state or returns a fresh mutable header with the exact requested shape, unchanged logical element count and the exact shared source chunk-vector identity. All old objects and data remain intact; rank-zero temporary allocation retains one zeroed chunk and positive-rank temporary allocation retains an empty chunk-vector header.",
    source := "base/bitarray.jl:475-485; base/reshapedarray.jl:67-79; base/boot.jl:782-818; doc/src/manual/arrays.md:63", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReshapeOtherSharesStorageAndErrors, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ReshapeRankSharing_proven,
    notes := "The rank inequality is the Julia dispatch partition. Negative rank-one dimensions reach DimensionMismatch because Core.checked_dims returns a single signed dimension unchanged; invalid higher-rank tuples raise ArgumentError first. Underbacked aliases are included because reshape never reads source chunks." }
]
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def OtherSimilarErrors : Prop :=
  ∀ (World T A : Type) (N : Nat) (B : BitArray N) (target : T) (dims : List I64)
    (allocate : T → List I64 → ExceptT JuliaLean.base.array.Error (StateM World) A)
    (s final : World) (error : JuliaLean.base.array.Error),
    (allocate target dims).run s = (.error error, final) →
    (similarBitArrayOtherDispatch allocate B target dims).run s = (.error error, final)

def AbstractConstructorErrors : Prop :=
  ∀ (World A R : Type) (rank : Nat) (value : A)
    (construct : Nat → A → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (s final : World) (error : JuliaLean.base.array.Error),
    (construct rank value).run s = (.error error, final) →
    (bitArrayFromAbstractDispatch rank construct value).run s = (.error error, final)

def UnknownIteratorErrors : Prop :=
  ∀ (World I S R : Type) (size : S) (itr : I)
    (gen : I → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (s final : World) (error : JuliaLean.base.array.Error),
    (gen itr).run s = (.error error, final) →
    (genBitArrayUnknownDispatch gen size itr).run s = (.error error, final)

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem otherSimilarErrors : OtherSimilarErrors := by
  intro World T A N B target dims allocate s final error h
  exact h

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem abstractConstructorErrors : AbstractConstructorErrors := by
  intro World A R rank value construct s final error h
  exact h

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem unknownIteratorErrors : UnknownIteratorErrors := by
  intro World I S R size itr gen s final error h
  exact h

end Completion

def entriesBitarray12 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-similar-other-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["similar(B::BitArray, T::Type, dims::Dims)"],
    statement := "Non-Bool similar retains the requested element type and dimensions and propagates any allocation exception together with its prior effects.",
    source := "base/bitarray.jl:366", status := .proven,
    prop := ``OtherSimilarErrors, thm := some ``Completion.otherSimilarErrors },
  { id := "bitarray-abstract-constructor-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["BitArray(A::AbstractArray{<:Any,N}) where N"],
    statement := "Abstract-array construction preserves the input rank and propagates every exception and prior effect of the selected typed constructor.",
    source := "base/bitarray.jl:498", status := .proven,
    prop := ``AbstractConstructorErrors, thm := some ``Completion.abstractConstructorErrors },
  { id := "bitarray-unknown-iterator-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["gen_bitarray(isz::IteratorSize, itr)"],
    statement := "Unknown-size iterable construction propagates every exception and prior state change while preserving the original iterable value.",
    source := "base/bitarray.jl:573", status := .proven,
    prop := ``UnknownIteratorErrors, thm := some ``Completion.unknownIteratorErrors },
  { id := "bitarray-copy-constructors-allocation", juliaFile := "base/bitarray.jl",
    juliaFns := ["(::Type{T})(x::T) where {T<:BitArray}", "BitArray(x::BitArray)"],
    statement := "Both same-type BitArray constructor spellings allocate fresh object and chunk-array identities with the same shape and length, preserving all old objects and memory. Empty copies share only empty backing memory. Invalid constructor dimensions fail without mutation; later failed source reads retain fresh allocations and preceding writes.",
    source := "base/bitarray.jl:535-536,359,429-447; base/abstractarray.jl:1154-1157,1211-1214; doc/src/manual/arrays.md:64", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.CopyConstructorsAllocationAndErrors, thm := none,
    notes := "No complete exact proof returned. Registration and partial-copy failure outcomes remain open." },
  { id := "bitarray-copy-constructors-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["(::Type{T})(x::T) where {T<:BitArray}", "BitArray(x::BitArray)"],
    statement := "Both constructors succeed with independent storage and copy every available source-prefix word from the initial snapshot when that prefix is readable. Adequate backing gives equality of all logical bits; extra physical chunks are ignored. Raw final-word padding is preserved even when alias growth made it nonzero. Underbacked sources copy only their available prefix and leave the uncopied last destination word zero.",
    source := "base/bitarray.jl:535-536,429-447; base/abstractarray.jl:1154-1157,1211-1214; doc/src/manual/arrays.md:64", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.CopyConstructorsReadablePrefix, thm := none,
    notes := "No complete exact proof returned. Readable-prefix preservation and the full constructor value contract remain open." }
]
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def IteratorSizeErrors : Prop :=
  ∀ (World I S R : Type) (iteratorSize : I → ExceptT JuliaLean.base.array.Error (StateM World) S)
    (gen : S → I → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (genN : Nat → S → I → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (rank : Nat) (itr : I) (s final : World) (error : JuliaLean.base.array.Error),
    (iteratorSize itr).run s = (.error error, final) →
    (bitArrayFromIteratorDispatch iteratorSize gen itr).run s = (.error error, final) ∧
    (bitArrayNFromIteratorDispatch rank iteratorSize genN itr).run s = (.error error, final)

def RankedIteratorErrors : Prop :=
  ∀ (World I S R : Type)
    (gen : S → I → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (genShape : Unit → I → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (rank : Nat) (size : S) (itr : I) (s final : World) (error : JuliaLean.base.array.Error),
    ((gen size itr).run s = (.error error, final) →
      (genBitArrayNVectorDispatch gen size itr).run s = (.error error, final)) ∧
    ((genShape () itr).run s = (.error error, final) →
      (genBitArrayNVectorShapeOneDispatch genShape () itr).run s = (.error error, final) ∧
      (genBitArrayNRankDispatch rank genShape () itr).run s = (.error error, final))

def ConvertExistingPackedArray : Prop :=
  ∀ (N : Nat) (A V : Type) (B : BitArray N)
    (construct : A → BitMutationM V) (asTarget : V → Option (BitArray N))
    (s : MutableMemory U64),
    (convertToBitArrayDispatch construct asTarget (.inl B)).run s = (.ok B, s)

def IndexOffsetFirstError : Prop :=
  ∀ (World I A R : Type)
    (first : I → ExceptT JuliaLean.base.array.Error (StateM World) A)
    (subtract : A → I64 → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (value : I) (s final : World) (error : JuliaLean.base.array.Error),
    (first value).run s = (.error error, final) →
    (indexOffsetDispatch first subtract value).run s = (.error error, final)

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem rankedIteratorErrors : RankedIteratorErrors := by
  intro World I S R gen genShape rank size itr s final error
  exact ⟨fun h => h, fun h => ⟨h, h⟩⟩

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem iteratorSizeErrors : IteratorSizeErrors := by
  intro World I S R iteratorSize gen genN rank itr s final error h
  simp [bitArrayFromIteratorDispatch, bitArrayNFromIteratorDispatch, h]

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem indexOffsetFirstError : IndexOffsetFirstError := by
  intro World I A R first subtract value s final error h
  simp [indexOffsetDispatch, h]

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem convertExistingPackedArray : ConvertExistingPackedArray := by
  intro N A V B construct asTarget s
  rfl

end Completion

def entriesBitarray13 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-reused-colon-offset-zero", juliaFile := "base/bitarray.jl",
    juliaFns := ["indexoffset(::Colon)"],
    statement := "Colon indexing starts at zero offset.",
    source := "base/bitarray.jl:695", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedColonOffsetZero,
    thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ReusedColonOffsetZero_proven },
  { id := "bitarray-reused-constructor-rejections", juliaFile := "base/bitarray.jl",
    juliaFns := ["gen_bitarray(::IsInfinite, itr)", "gen_bitarrayN(::Type{BitVector}, itsz::HasShape{N}, itr) where N", "gen_bitarrayN(@nospecialize(T::Type), itsz::HasShape{N}, itr) where N", "gen_bitarrayN(@nospecialize(T::Type), itsz, itr)"],
    statement := "Infinite iterators reject with ArgumentError, and incompatible target/rank constructor branches reject with DimensionMismatch; every rejection preserves the heap for all iterator values and target names.",
    source := "base/bitarray.jl:594,600-602", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedConstructorRejections,
    thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ReusedConstructorRejections_proven },
  { id := "bitarray-iterator-size-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["BitArray(itr)", "BitArray{N}(itr) where N"],
    statement := "Iterator constructors propagate any exception and prior effects from the iterable's size-trait method without allocating or consuming iterator elements afterward.",
    source := "base/bitarray.jl:566-567", status := .proven,
    prop := ``IteratorSizeErrors, thm := some ``Completion.iteratorSizeErrors },
  { id := "bitarray-ranked-iterator-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["gen_bitarrayN(::Type{BitVector}, itsz, itr)",
      "gen_bitarrayN(::Type{BitVector}, itsz::HasShape{1}, itr)",
      "gen_bitarrayN(::Type{BitArray{N}}, itsz::HasShape{N}, itr) where N"],
    statement := "Compatible iterator-size branches retain every exception and prior state change from constructing the packed iterator result.",
    source := "base/bitarray.jl:596-598", status := .proven,
    prop := ``RankedIteratorErrors, thm := some ``Completion.rankedIteratorErrors },
  { id := "bitarray-convert-existing-packed-array", juliaFile := "base/bitarray.jl",
    juliaFns := ["convert(::Type{T}, a::AbstractArray) where T<:BitArray"],
    statement := "Converting an already target-typed packed array retains its length, dimensions and chunk storage without allocating or changing memory.",
    source := "base/bitarray.jl:569", status := .proven,
    prop := ``ConvertExistingPackedArray, thm := some ``Completion.convertExistingPackedArray },
  { id := "bitarray-indexoffset-first-error", juliaFile := "base/bitarray.jl",
    juliaFns := ["indexoffset(i)"],
    statement := "An index object's failure to provide its first element propagates the same exception and prior state changes when computing its offset.",
    source := "base/bitarray.jl:694", status := .proven,
    prop := ``IndexOffsetFirstError, thm := some ``Completion.indexOffsetFirstError }
]
end JuliaLean.Proofs.base.bitarray

