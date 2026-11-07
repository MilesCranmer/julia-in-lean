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
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Combining zero with a word leaves the word unchanged. -/
theorem reverseCoreOrZeroLeft (word : U64) : or_int (u64 0) word = word := by
  rw [reverseOrComm, dequePackedOrZero]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Copying into fresh memory installs the old logical prefix and leaves spare slots unassigned. -/
theorem growthCopyLoopFresh (s : State) (mem : Nat) (values : List (Option U64))
    (spare : Nat) (hm : s.memories[mem]? = some (List.replicate (values.length + spare) none))
    (hn : values.length + spare ≤ 9223372036854775807) :
    (forIn values.zipIdx PUnit.unit (fun (pair : Option U64 × Nat) _ => do
      memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1
      pure (ForInStep.yield PUnit.unit))).run s =
      (.ok PUnit.unit, {s with memories := s.memories.set mem (values ++ List.replicate spare none)}) := by
  have hr := growthCopyLoop s mem (List.replicate (values.length + spare) none) values hm
    (by rw [List.length_replicate]; omega) (by rwa [List.length_replicate])
  have hslots := growthInstallPrefix values [] spare
  simp only [List.length_nil, List.nil_append] at hslots
  rw [hslots] at hr
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

/-- Removing a half-open interval has the expected length. -/
theorem rangeSingleLogicalLength (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) :
    (xs.take first ++ xs.drop last).length = xs.length - (last - first) := by
  simp only [List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega)]
  omega

/-- Forward copying followed by the model's end mask encodes exact interval deletion. -/
theorem rangeSingleDeleteWord (xs : List Bool) (first last : Nat)
    (hf : first ≤ last) (hl : last ≤ xs.length) (hn : xs.length ≤ 64)
    (hp : 0 < xs.length - (last - first)) :
    and_int (rangeSingleCopyWord (packedPrefix xs 0 64) first last (xs.length - last))
      (maskEnd (int ((xs.length - (last - first) : Nat) : Int))) =
        packedPrefix (xs.take first ++ xs.drop last) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [dequePackedAnd, rangeSingleCopyBit _ _ _ _ bit (by omega) (by omega) hb,
    rangeSingleEndMaskBit _ bit hp (by omega) hb,
    packedWord_bit (xs.take first ++ xs.drop last) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  by_cases hin : bit < xs.length - (last - first)
  · simp only [hin, decide_true, Bool.and_true]
    rw [rangeSingleLogicalGet xs first last bit hf hl]
    by_cases hbefore : bit < first
    · rw [if_neg (by omega), if_pos hbefore, packedWord_bit _ _ _ hb]
      simp only [Nat.zero_mul, Nat.zero_add]
    · rw [if_pos (by omega), if_neg hbefore, packedWord_bit _ _ _ (by omega)]
      simp only [Nat.zero_mul, Nat.zero_add]
      congr 1
      omega
  · simp only [hin, decide_false, Bool.and_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · rw [rangeSingleLogicalLength xs first last hf hl]
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

/-- The next gather in a two-boundary suffix copy returns the following logical window. -/
theorem prefixDeleteNextGatherRun (xs : List Bool) (source chunks : Nat) (s : State)
    (hn : xs.length ≤ 9223372036854775807) (hs : source < xs.length)
    (hp : 64 < xs.length - source)
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
  have hplus : int ((source / 64 + 1 : Nat) : Int) + int 1 = int ((source / 64 + 2 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    omega
  have hge : int (((xs.length - 1) / 64 + 1 : Nat) : Int) ≥ int ((source / 64 + 2 : Nat) : Int) := by
    change (int ((source / 64 + 2 : Nat) : Int)).val ≤ (int (((xs.length - 1) / 64 + 1 : Nat) : Int)).val
    rw [packedInt_val (source / 64 + 2) (by omega), packedInt_val ((xs.length - 1) / 64 + 1) (by omega)]
    omega
  rw [hplus, if_pos hge, shiftWindowSourceMask xs source hn hs hp]
  have h := prefixDeleteHighGatherRun xs (source + 64) chunks s hn (by omega) (by
    intro chunk hlow hhigh
    exact hr chunk (by omega) hhigh)
  simpa only [show (source + 64) / 64 + 1 = source / 64 + 2 by omega,
    show (source + 64) % 64 = source % 64 by omega] using h

/-- In-place copying of a retained suffix of at most 128 bits reads each source before an overlapping destination write. -/
theorem prefixDeleteCopyRun (xs : List Bool) (count spare : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hc : count < xs.length)
    (hk : xs.length - count ≤ 128) :
    (copyChunks 0 (int 1) 0 (int ((count + 1 : Nat) : Int))
      (int ((xs.length - count : Nat) : Int))).run (dequeWordStore (encodeBits xs) spare) =
      (.ok (), dequeWordStore (prefixDeleteWords xs count) spare) := by
  let words := encodeBits xs
  let kept := xs.length - count
  let s := dequeWordStore words spare
  have hwords : words.length = wordCount xs.length := packedEncoded_length xs
  have hnwords : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hpositive : 0 < words.length := by rw [hwords]; unfold wordCount; omega
  have hp : 0 < kept := by dsimp only [kept]; omega
  have hrs : ∀ chunk, chunk < wordCount xs.length →
      (mutableGet 0 (int ((chunk + 1 : Nat) : Int))).run s = (.ok (packedPrefix xs chunk 64), s) := by
    intro chunk hchunk
    have h := dequeWordRead words spare chunk hnwords (by rw [hwords]; exact hchunk)
    rw [shiftNearLeftEncodedGet xs chunk hchunk] at h
    exact h
  have hr0 : (mutableGet 0 (int 1)).run s = (.ok (packedPrefix xs 0 64), s) :=
    hrs 0 (by rw [← hwords]; exact hpositive)
  have hf : ¬ (0 = (0 : Nat) ∧ int 1 > int ((count + 1 : Nat) : Int)) := by
    intro h
    have hv : (int ((count + 1 : Nat) : Int)).val < 1 := h.2
    rw [packedInt_val (count + 1) (by omega)] at hv
    omega
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
  by_cases hs : kept ≤ 64
  · have hg := shiftNearGatherRun xs count 0 s hn hc hs hrs
    have hd1 : getChunksId (int 1 + int kept - int 1) = (int 1, int ((0 + kept - 1 : Nat) : Int)) := by
      rw [hendD]
      have h := rangeSingleAddress (kept - 1) (by omega)
      simpa only [Nat.zero_add, show kept - 1 + 1 = kept by omega] using h
    have hw := dequeWordSet words spare 0
      (copyPairPaste (packedPrefix xs 0 64) (copyPairSlice xs count) 0 kept) hnwords hpositive
    rw [prefixDeleteWords, if_pos hs]
    exact copyPairOneRun 0 0 _ _ kept 0 (int 1)
      (int ((count / 64 + 1 : Nat) : Int)) (int ((count % 64 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int))
      s _ (packedPrefix xs 0 64) (copyPairSlice xs count) hp (by omega) hf rfl hd1 hs0 hs1 hg hr0 hw
  · have hlong : 64 < xs.length - count := by omega
    have htwo : 1 < words.length := by rw [hwords]; unfold wordCount; omega
    let lowWords := words.set 0 (copyPairSlice xs count)
    let middle := dequeWordStore lowWords spare
    have hg : (glueSrcBitChunks 0 (int ((count / 64 + 1 : Nat) : Int))
        (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
        (copyPairSourceMask (int ((count / 64 + 1 : Nat) : Int))
          (int (((xs.length - 1) / 64 + 1 : Nat) : Int))
          (int ((count % 64 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int)))
        (int ((count % 64 : Nat) : Int))).run s = (.ok (copyPairSlice xs count), s) := by
      rw [shiftWindowSourceMask xs count hn hc hlong]
      exact shiftWindowHighGatherRun xs count 0 s hn hc hrs
    have hw0 : (mutableSet 0 (copyPairPaste (packedPrefix xs 0 64) (copyPairSlice xs count) 0 64) (int 1)).run s =
        (.ok (), middle) := by
      rw [copyPairPasteFull]
      exact dequeWordSet words spare 0 (copyPairSlice xs count) hnwords hpositive
    have hrsm : ∀ chunk, count / 64 + 1 ≤ chunk → chunk < wordCount xs.length →
        (mutableGet 0 (int ((chunk + 1 : Nat) : Int))).run middle = (.ok (packedPrefix xs chunk 64), middle) := by
      intro chunk hstart hchunk
      have h := dequeWordRead lowWords spare chunk (by rw [List.length_set]; exact hnwords)
        (by rw [List.length_set, hwords]; exact hchunk)
      have he : lowWords.getD chunk (u64 0) = packedPrefix xs chunk 64 := by
        change (words.set 0 (copyPairSlice xs count)).getD chunk (u64 0) = _
        rw [dequeWordGetSet words 0 chunk _ hpositive, if_neg (by omega)]
        exact shiftNearLeftEncodedGet xs chunk hchunk
      rw [he] at h
      exact h
    have hnext := prefixDeleteNextGatherRun xs count 0 middle hn hc hlong hrsm
    have hr1 : (mutableGet 0 (int 2)).run middle = (.ok (packedPrefix xs 1 64), middle) := by
      have h := dequeWordRead lowWords spare 1 (by rw [List.length_set]; exact hnwords)
        (by rw [List.length_set]; exact htwo)
      have he : lowWords.getD 1 (u64 0) = packedPrefix xs 1 64 := by
        change (words.set 0 (copyPairSlice xs count)).getD 1 (u64 0) = _
        rw [dequeWordGetSet words 0 1 _ hpositive, if_neg (by decide)]
        exact shiftNearLeftEncodedGet xs 1 (by rw [← hwords]; exact htwo)
      rw [he] at h
      exact h
    have hw1 := dequeWordSet lowWords spare 1
      (copyPairPaste (packedPrefix xs 1 64) (copyPairSlice xs (count + 64)) 0 (kept - 64))
      (by rw [List.length_set]; exact hnwords) (by rw [List.length_set]; exact htwo)
    have hd1 : getChunksId (int 1 + int kept - int 1) =
        (int 2, int ((kept - 64 - 1 : Nat) : Int)) := by
      rw [hendD]
      simpa only [Nat.sub_sub] using copyPairFinalAddress kept hlong hk
    rw [prefixDeleteWords, if_neg hs]
    apply copyPairTwoRun 0 0 _ _ (int kept) 0 (kept - 64)
      (int ((count / 64 + 1 : Nat) : Int)) (int ((count % 64 : Nat) : Int))
      (int (((xs.length - 1) / 64 + 1 : Nat) : Int)) (int (((xs.length - 1) % 64 : Nat) : Int))
      s middle _ (packedPrefix xs 0 64) (packedPrefix xs 1 64) (copyPairSlice xs count) (copyPairSlice xs (count + 64))
      (by decide) (by omega) (by omega) (fillPositiveLength kept hp (by omega)) hf rfl hd1 hs0 hs1 hg hr0 hw0 hnext hr1
    rw [copyPairCarryZero]
    exact hw1

/-- Any successful invariant for one descending block lifts to the complete native-length loop, including its final partial block. -/
theorem frontCopyLoopNative (chunks : Nat) (posD posS : I64) (count : Nat)
    (stage : Nat → State) (hn : count ≤ 9223372036854775807)
    (hstep : ∀ left : Nat, 0 < left → left ≤ count →
      (frontCopyBlock chunks
        (posD + int ((left - min left 64 : Nat) : Int))
        (posS + int ((left - min left 64 : Nat) : Int)) (int ((min left 64 : Nat) : Int))).run
          (stage left) = (.ok (), stage (left - min left 64))) :
    (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (int count))).run
      (stage count) = (.ok (frontCopyRegisters posD posS (int 0)), stage 0) := by
  have hall : ∀ left : Nat, left ≤ count →
      (frontCopyLoop chunks posD posS (frontCopyRegisters posD posS (int left))).run
        (stage left) = (.ok (frontCopyRegisters posD posS (int 0)), stage 0) := by
    intro left
    induction left using Nat.strongRecOn with
    | ind left ih =>
      intro hl
      by_cases hz : left = 0
      · subst left
        exact frontCopyLoopDone chunks posD posS (frontCopyRegisters posD posS (int 0))
          (stage 0) (by change ¬ int 0 > int 0; decide)
      · have hp : 0 < left := by omega
        have hm : 0 < min left 64 := by omega
        have hsm : left - min left 64 < left := by omega
        have ht := ih (left - min left 64) hsm (by omega)
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
          hpos (hstep left hp hl) (by simpa only [hd] using ht)
  exact hall count (Nat.le_refl _)

/-- Native-length descending copying follows from any canonical block invariant, without requiring aligned source length. -/
theorem frontCopyRtolNative (chunks : Nat) (posD posS : I64) (count : Nat)
    (stage : Nat → State) (hn : count ≤ 9223372036854775807)
    (hne : (posD == posS) = false) (horder : ¬ posD < posS)
    (hstep : ∀ left : Nat, 0 < left → left ≤ count →
      (frontCopyBlock chunks
        (posD + int ((left - min left 64 : Nat) : Int))
        (posS + int ((left - min left 64 : Nat) : Int)) (int ((min left 64 : Nat) : Int))).run
          (stage left) = (.ok (), stage (left - min left 64))) :
    (copyChunksRtol chunks posD posS (int count)).run (stage count) =
      (.ok (), stage 0) := by
  exact frontCopyRtolFromLoop chunks posD posS (int count) (stage count) (stage 0)
    (frontCopyRegisters posD posS (int 0)) hne horder
    (frontCopyLoopNative chunks posD posS count stage hn hstep)

/-- The main copy dispatcher also follows the same invariant for a strictly rightward same-array move. -/
theorem frontCopyChunksNative (chunks : Nat) (posD posS : I64) (count : Nat)
    (stage : Nat → State) (hn : count ≤ 9223372036854775807)
    (horder : posD > posS)
    (hstep : ∀ left : Nat, 0 < left → left ≤ count →
      (frontCopyBlock chunks
        (posD + int ((left - min left 64 : Nat) : Int))
        (posS + int ((left - min left 64 : Nat) : Int)) (int ((min left 64 : Nat) : Int))).run
          (stage left) = (.ok (), stage (left - min left 64))) :
    (copyChunks chunks posD chunks posS (int count)).run (stage count) =
      (.ok (), stage 0) := by
  by_cases hz : count = 0
  · subst count
    exact rangeSingleCopyEmptyRun chunks posD posS (stage 0)
  · have hp : 0 < count := by omega
    have he : (posD == posS) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      subst posD
      exact Int.lt_irrefl _ horder
    have ho : ¬ posD < posS := by
      change ¬ posD.val < posS.val
      change posS.val < posD.val at horder
      omega
    have ht := frontCopyRtolNative chunks posD posS count stage hn he ho hstep
    simp only [copyChunks, fillPositiveLength count hp hn, Bool.false_eq_true, ite_false,
      show (chunks = chunks ∧ posD > posS) from ⟨rfl, horder⟩, dite_true]
    exact ht
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def concatWitness : List Bool := List.replicate 64 false ++ [true]

def concatWitnessRun :=
  (bitArrayVcatVectors [vectorBits concatWitness]
    (fun n => Round5.Round2.allocateBitArrayModel [n])).run
    (MutableMemory.initialMany [(encodeBits concatWitness).map some])

/-- The frozen model reads an unassigned destination chunk during vector vcat. -/
theorem concat_model_error : concatWitnessRun.1 = .error .undefinedReference := by
  unfold concatWitnessRun bitArrayVcatVectors
  simp only [copyChunks]
  rfl

/-- The same destination-read issue occurs for the one-column matrix route. -/
theorem matrixVcat_model_error :
    ((bitArrayVcatMatrices
      [(⟨0, int 65, [int 65, int 1]⟩ : BitMatrix)]
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      Round5.Round2.allocateMatrixModel).run
      (MutableMemory.initialMany [(encodeBits concatWitness).map some])).1 =
        .error .undefinedReference := by
  unfold bitArrayVcatMatrices
  simp only [copyChunks]
  rfl
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096

/-- Ceiling division is additive across a whole-word boundary. -/
theorem concat_wordCount_aligned (left right : Nat) (halign : left % 64 = 0) :
    wordCount (left + right) = wordCount left + wordCount right := by
  unfold wordCount
  omega

/-- Appending later bits does not change an earlier complete packed word. -/
theorem concat_prefix_left (left right : List Bool) (chunk : Nat)
    (hchunk : (chunk + 1) * 64 ≤ left.length) :
    packedPrefix (left ++ right) chunk 64 = packedPrefix left chunk 64 := by
  apply packedBit_ext
  intro bit hbit
  rw [packedWord_bit _ _ _ hbit, packedWord_bit _ _ _ hbit]
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : chunk * 64 + bit < left.length)]

/-- Whole-word-aligned append offsets preserve every right-hand packed word. -/
theorem concat_prefix_right (left right : List Bool) (chunk : Nat)
    (halign : left.length % 64 = 0) :
    packedPrefix (left ++ right) (wordCount left.length + chunk) 64 =
      packedPrefix right chunk 64 := by
  have hwords : wordCount left.length * 64 = left.length := by unfold wordCount; omega
  apply packedBit_ext
  intro bit hbit
  rw [packedWord_bit _ _ _ hbit, packedWord_bit _ _ _ hbit]
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : left.length ≤ (wordCount left.length + chunk) * 64 + bit)]
  congr 2
  omega

/-- Packing commutes with append whenever the left sequence ends on a word boundary. -/
theorem concat_encode_append (left right : List Bool) (halign : left.length % 64 = 0) :
    encodeBits (left ++ right) = encodeBits left ++ encodeBits right := by
  simp only [packedPrefix_eq_encode, List.length_append, concat_wordCount_aligned _ _ halign,
    List.range_add, List.map_append, List.map_map, Function.comp_def]
  congr 1
  · apply List.map_congr_left
    intro chunk hchunk
    apply concat_prefix_left
    have hc := List.mem_range.mp hchunk
    unfold wordCount at hc
    omega
  · apply List.map_congr_left
    intro chunk _
    exact concat_prefix_right left right chunk halign

/-- The flattened length remains word-aligned when each component does. -/
theorem concat_flatten_aligned (vectors : List (List Bool))
    (halign : ∀ xs ∈ vectors, xs.length % 64 = 0) : vectors.flatten.length % 64 = 0 := by
  induction vectors with
  | nil => rfl
  | cons xs vectors ih =>
    have hx := halign xs List.mem_cons_self
    have ht := ih (fun ys hy => halign ys (List.mem_cons_of_mem xs hy))
    simp only [List.flatten_cons, List.length_append]
    omega

/-- Arbitrarily many aligned logical vectors pack by flattening their encoded chunks. -/
theorem concat_encode_flatten (vectors : List (List Bool))
    (halign : ∀ xs ∈ vectors, xs.length % 64 = 0) :
    encodeBits vectors.flatten = vectors.flatMap encodeBits := by
  induction vectors with
  | nil => rfl
  | cons xs vectors ih =>
    simp only [List.flatten_cons, List.flatMap_cons]
    rw [concat_encode_append xs vectors.flatten (halign xs List.mem_cons_self),
      ih (fun ys hy => halign ys (List.mem_cons_of_mem xs hy))]

/-- Taking a whole number of words preserves every included packed word. -/
theorem concat_prefix_take (xs : List Bool) (words chunk : Nat) (hc : chunk < words) :
    packedPrefix (xs.take (words * 64)) chunk 64 = packedPrefix xs chunk 64 := by
  apply packedBit_ext
  intro bit hbit
  rw [packedWord_bit _ _ _ hbit, packedWord_bit _ _ _ hbit]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take,
    show chunk * 64 + bit < words * 64 by omega, ite_true]

/-- Dropping complete words shifts packed-word coordinates by exactly that amount. -/
theorem concat_prefix_drop (xs : List Bool) (words chunk : Nat) :
    packedPrefix (xs.drop (words * 64)) chunk 64 = packedPrefix xs (words + chunk) 64 := by
  apply packedBit_ext
  intro bit hbit
  rw [packedWord_bit _ _ _ hbit, packedWord_bit _ _ _ hbit]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

/-- The number of packed words after taking a whole-word prefix. -/
theorem concat_wordCount_take (length words : Nat) :
    wordCount (min (words * 64) length) = min words (wordCount length) := by
  unfold wordCount
  omega

/-- The number of packed words after dropping complete words. -/
theorem concat_wordCount_drop (length words : Nat) :
    wordCount (length - words * 64) = wordCount length - words := by
  unfold wordCount
  omega

/-- Logical whole-word take is exactly packed-list take, including a partial final word. -/
theorem concat_encode_take (xs : List Bool) (words : Nat) :
    encodeBits (xs.take (words * 64)) = (encodeBits xs).take words := by
  apply List.ext_getElem
  · simp only [packedPrefix_eq_encode, List.length_map, List.length_range,
      List.length_take, concat_wordCount_take]
  · intro chunk hleft hright
    have hc : chunk < words := by
      simp only [List.length_take] at hright
      omega
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range,
      List.getElem_take]
    exact concat_prefix_take xs words chunk hc

/-- Logical whole-word drop is exactly packed-list drop. -/
theorem concat_encode_drop (xs : List Bool) (words : Nat) :
    encodeBits (xs.drop (words * 64)) = (encodeBits xs).drop words := by
  apply List.ext_getElem
  · simp only [packedPrefix_eq_encode, List.length_map, List.length_range,
      List.length_drop, concat_wordCount_drop]
  · intro chunk hleft hright
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range,
      List.getElem_drop]
    exact concat_prefix_drop xs words chunk

/-- A whole-word logical slice is the corresponding slice of encoded storage. -/
theorem concat_encode_slice (xs : List Bool) (start words : Nat) :
    encodeBits ((xs.drop (start * 64)).take (words * 64)) =
      ((encodeBits xs).drop start).take words := by
  rw [concat_encode_take, concat_encode_drop]

/-- Packing commutes with any flat-map whose pieces are word-aligned. -/
theorem concat_encode_flatMap {α : Type} (items : List α) (f : α → List Bool)
    (halign : ∀ item ∈ items, (f item).length % 64 = 0) :
    encodeBits (items.flatMap f) = items.flatMap (fun item => encodeBits (f item)) := by
  induction items with
  | nil => simp only [List.flatMap_nil]; rfl
  | cons item items ih =>
    simp only [List.flatMap_cons]
    rw [concat_encode_append (f item) (items.flatMap f) (halign item List.mem_cons_self),
      ih (fun x hx => halign x (List.mem_cons_of_mem item hx))]

/-- An indexed, in-bounds logical block is precisely its drop/take slice. -/
theorem concat_slice_map (xs : List Bool) (start count : Nat)
    (hbound : start + count ≤ xs.length) :
    (List.range count).map (fun row => xs.getD (row + start) false) =
      (xs.drop start).take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro row hleft hright
    have hr : row < count := by simpa only [List.length_map, List.length_range] using hleft
    have hi : row + start < xs.length := by omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    congr 1
    omega

/-- Each source matrix contributes its contiguous column block in the frozen column-major specification. -/
theorem concat_column_slice (columns : Nat) (input : Nat × List Bool) (column : Nat)
    (hshape : input.2.length = input.1 * columns) (hcolumn : column < columns) :
    (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false) =
      (input.2.drop (column * input.1)).take input.1 := by
  apply concat_slice_map
  calc
    column * input.1 + input.1 = (column + 1) * input.1 := by simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ columns * input.1 := Nat.mul_le_mul_right input.1 (Nat.succ_le_of_lt hcolumn)
    _ = input.2.length := by rw [hshape, Nat.mul_comm]

/-- A matrix column with word-aligned row count is the corresponding packed storage slice. -/
theorem concat_column_encode (columns : Nat) (input : Nat × List Bool) (column : Nat)
    (hshape : input.2.length = input.1 * columns) (hcolumn : column < columns)
    (halign : input.1 % 64 = 0) :
    encodeBits ((List.range input.1).map (fun row => input.2.getD (row + column * input.1) false)) =
      ((encodeBits input.2).drop (column * (input.1 / 64))).take (input.1 / 64) := by
  rw [concat_column_slice columns input column hshape hcolumn]
  have hrows : input.1 / 64 * 64 = input.1 := by omega
  have hstart : column * (input.1 / 64) * 64 = column * input.1 := by
    rw [Nat.mul_assoc, hrows]
  have h := concat_encode_slice input.2 (column * (input.1 / 64)) (input.1 / 64)
  rw [hstart, hrows] at h
  exact h

/-- Pointwise equality on a list suffices to identify its concatenated blocks. -/
theorem concat_flatMap_congr {α β : Type} (items : List α) (f g : α → List β)
    (h : ∀ item ∈ items, f item = g item) : items.flatMap f = items.flatMap g := by
  induction items with
  | nil => simp only [List.flatMap_nil]
  | cons item items ih =>
    simp only [List.flatMap_cons, h item List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem item hx))]

/-- The complete frozen matrix-vcat specification decomposes into contiguous source-column slices. -/
theorem concat_matrix_slices (columns : Nat) (inputs : List (Nat × List Bool))
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns) :
    ((List.range columns).flatMap fun column => inputs.flatMap fun input =>
      (List.range input.1).map fun row => input.2.getD (row + column * input.1) false) =
    ((List.range columns).flatMap fun column => inputs.flatMap fun input =>
      (input.2.drop (column * input.1)).take input.1) := by
  apply concat_flatMap_congr
  intro column hcolumn
  apply concat_flatMap_congr
  intro input hinput
  exact concat_column_slice columns input column (hshape input hinput) (List.mem_range.mp hcolumn)

/-- Aligned matrix-vcat's entire logical output packs by joining the appropriate source-word slices. -/
theorem concat_matrix_encode (columns : Nat) (inputs : List (Nat × List Bool))
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (halign : ∀ input ∈ inputs, input.1 % 64 = 0) :
    encodeBits ((List.range columns).flatMap fun column => inputs.flatMap fun input =>
      (List.range input.1).map fun row => input.2.getD (row + column * input.1) false) =
    ((List.range columns).flatMap fun column => inputs.flatMap fun input =>
      ((encodeBits input.2).drop (column * (input.1 / 64))).take (input.1 / 64)) := by
  have halignColumn (column : Nat) :
      (inputs.flatMap fun input => (List.range input.1).map
        (fun row => input.2.getD (row + column * input.1) false)).length % 64 = 0 := by
    induction inputs with
    | nil => rfl
    | cons input inputs ih =>
      have ht := ih (fun x hx => hshape x (List.mem_cons_of_mem input hx))
        (fun x hx => halign x (List.mem_cons_of_mem input hx))
      have hh := halign input List.mem_cons_self
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range]
      omega
  rw [concat_encode_flatMap _ _ (fun column _ => halignColumn column)]
  apply concat_flatMap_congr
  intro column hcolumn
  rw [concat_encode_flatMap _ _ (by
    intro input hinput
    simpa only [List.length_map, List.length_range] using halign input hinput)]
  apply concat_flatMap_congr
  intro input hinput
  exact concat_column_encode columns input column (hshape input hinput) (List.mem_range.mp hcolumn)
    (halign input hinput)
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

/-- A logical right shift selects the higher source bits and zero-fills beyond the word. -/
theorem concat_lshr_bit (word : U64) (n bit : Nat) (hn : n < 64) :
    packedBit (lshr_int word (int n)) bit =
      (decide (bit < 64) && packedBit word (bit + n)) := by
  unfold lshr_int
  rw [packedBit_toJInt]
  unfold jlLshrInt
  rw [concat_shift_count n (by omega), if_neg (show ¬ n ≥ IntTy.u64.bits by exact Nat.not_le.mpr hn)]
  rw [BitVec.getLsbD_ofNat, packedFromJInt_nat, Nat.testBit_div_two_pow]
  rfl

/-- The exact single-word copy formula with independent source and destination words. -/
def concat_slice_copy_word (destination sourceWord : U64) (dest source count : Nat) : U64 :=
  let keep := concat_keep_mask dest count
  let selected := and_int (shl_int u64Max (int source))
    (not_int (shl_int u64Max (int ((source + count : Nat) : Int))))
  or_int (and_int destination keep)
    (and_int (shl_int (lshr_int (and_int sourceWord selected) (int source)) (int dest)) (not_int keep))

/-- One-chunk copying has exact source-offset semantics and preserves other positions. -/
theorem concat_slice_copy_bit (destination sourceWord : U64) (dest source count bit : Nat)
    (hd : dest + count ≤ 64) (hs : source + count ≤ 64) (hb : bit < 64) :
    packedBit (concat_slice_copy_word destination sourceWord dest source count) bit =
      if dest ≤ bit ∧ bit < dest + count then packedBit sourceWord (bit - dest + source)
      else packedBit destination bit := by
  simp only [concat_slice_copy_word, packedBit_or, concat_and_bit,
    concat_keep_mask_bit dest count bit hd hb, concat_not_bit _ bit hb]
  by_cases hi : dest ≤ bit ∧ bit < dest + count
  · have hout : ¬ (bit < dest ∨ dest + count ≤ bit) := by omega
    simp only [hi, hout, decide_false, Bool.not_false, Bool.and_false,
      Bool.and_true, Bool.false_or, ite_true]
    rw [concat_shl_bit _ dest bit (by omega) hb, if_pos hi.1,
      concat_lshr_bit _ source (bit - dest) (by omega)]
    simp only [show bit - dest < 64 by omega, decide_true, Bool.true_and]
    rw [concat_and_bit, concat_and_bit, concat_not_bit _ _ (by omega),
      concat_high_mask_bit _ _ (by omega) (by omega),
      concat_high_mask_bit _ _ hs (by omega)]
    simp only [show source ≤ bit - dest + source by omega,
      show ¬ source + count ≤ bit - dest + source by omega,
      decide_true, decide_false, Bool.not_false, Bool.true_and, Bool.and_true, and_self, ite_true]
  · have hout : bit < dest ∨ dest + count ≤ bit := by omega
    simp only [hi, hout, decide_true, Bool.not_true, Bool.and_false, Bool.and_true,
      Bool.or_false, ite_false]

/-- The frozen forward copier executes its exact one-word formula between independent source and destination handles. -/
theorem concat_slice_copy_run (destinationHandle sourceHandle dest source count : Nat) (s out : State)
    (destination sourceWord : U64) (hsep : destinationHandle ≠ sourceHandle)
    (hp : 0 < count) (hd : dest + count ≤ 64) (hs : source + count ≤ 64)
    (hg : (mutableGet sourceHandle (int 1)).run s = (.ok sourceWord, s))
    (hgd : (mutableGet destinationHandle (int 1)).run s = (.ok destination, s))
    (hw : (mutableSet destinationHandle (concat_slice_copy_word destination sourceWord dest source count) (int 1)).run s =
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
  have hstartD := concat_small_chunks dest (by omega)
  have hstartS := concat_small_chunks source (by omega)
  have hendD : int ((dest + 1 : Nat) : Int) + int count - int 1 = int ((dest + count : Nat) : Int) := by
    rw [packedInt_add, concat_int_sub]
    apply congrArg int
    omega
  have hendS : int ((source + 1 : Nat) : Int) + int count - int 1 = int ((source + count : Nat) : Int) := by
    rw [packedInt_add, concat_int_sub]
    apply congrArg int
    omega
  have hlastD : getChunksId (int ((dest + count : Nat) : Int)) =
      (int 1, int ((dest + count - 1 : Nat) : Int)) := by
    have h := concat_small_chunks (dest + count - 1) (by omega)
    rw [show dest + count - 1 + 1 = dest + count by omega] at h
    exact h
  have hlastS : getChunksId (int ((source + count : Nat) : Int)) =
      (int 1, int ((source + count - 1 : Nat) : Int)) := by
    have h := concat_small_chunks (source + count - 1) (by omega)
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
  simp only [concat_slice_copy_word, concat_keep_mask] at hw
  rw [hw]



/-- Copying an in-bounds source slice after an accumulated sequence constructs its exact packed append. -/
theorem concat_slice_copy_append (accum source : List Bool) (start count : Nat)
    (hdest : accum.length + count ≤ 64) (hsource : start + count ≤ source.length)
    (hsize : source.length ≤ 64) :
    concat_slice_copy_word (packedPrefix accum 0 64) (packedPrefix source 0 64)
      accum.length start count = packedPrefix (accum ++ (source.drop start).take count) 0 64 := by
  apply packedBit_ext
  intro bit hb
  rw [concat_slice_copy_bit _ _ _ _ _ _ hdest (by omega) hb,
    packedWord_bit (accum ++ (source.drop start).take count) 0 bit hb]
  simp only [Nat.zero_mul, Nat.zero_add]
  by_cases hl : bit < accum.length
  · rw [if_neg (by omega), packedWord_bit accum 0 bit hb]
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
  · have hle : accum.length ≤ bit := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
    by_cases hr : bit < accum.length + count
    · rw [if_pos ⟨hle, hr⟩, packedWord_bit source 0 (bit - accum.length + start) (by omega)]
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_take, show bit - accum.length < count by omega, ite_true, List.getElem?_drop]
      congr 2
      omega
    · rw [if_neg (by omega), packedWord_bit accum 0 bit hb]
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hle, List.getElem?_take,
        show ¬ bit - accum.length < count by omega, ite_false]

/-- Copying the next source block into an already-copied prefix extends that prefix exactly. -/
theorem concat_slice_copy_prefix (source : List Bool) (start count : Nat)
    (hsource : start + count ≤ source.length) (hsize : source.length ≤ 64) :
    concat_slice_copy_word (packedPrefix (source.take start) 0 64) (packedPrefix source 0 64)
      start start count = packedPrefix (source.take (start + count)) 0 64 := by
  have h := concat_slice_copy_append (source.take start) source start count
    (by simp only [List.length_take]; omega) hsource hsize
  have hs : (source.take start).length = start := by simp only [List.length_take]; omega
  rw [hs, ← List.take_add] at h
  exact h

/-- A concrete one-word source-offset copy extends a copied prefix in the fresh output heap. -/
theorem concat_copy_prefix_run (s : State) (sourceHandle : Nat) (source : List Bool) (start count : Nat)
    (hh : sourceHandle < s.arrays.length) (hp : 0 < count)
    (hsource : start + count ≤ source.length) (hsize : source.length ≤ 64)
    (hread : (mutableGet sourceHandle (int 1)).run
      (concat_extend s (packedPrefix (source.take start) 0 64)) =
      (.ok (packedPrefix source 0 64), concat_extend s (packedPrefix (source.take start) 0 64))) :
    (copyChunks s.arrays.length (int ((start + 1 : Nat) : Int)) sourceHandle
      (int ((start + 1 : Nat) : Int)) (int count)).run
      (concat_extend s (packedPrefix (source.take start) 0 64)) =
      (.ok (), concat_extend s (packedPrefix (source.take (start + count)) 0 64)) := by
  apply concat_slice_copy_run s.arrays.length sourceHandle start start count _ _
    (packedPrefix (source.take start) 0 64) (packedPrefix source 0 64) (by omega) hp
    (by omega) (by omega) hread (concat_extend_read s _)
  rw [concat_slice_copy_prefix source start count hsource hsize]
  exact concat_extend_store s _ _

/-- Zero is an identity for the installed wrapped signed addition. -/
theorem concat_zero_add (value : I64) : int 0 + value = value := by
  apply Subtype.ext
  change wrapInt .i64 (0 + value.val) = value.val
  rw [Int.zero_add]
  exact wrapInt_of_inRange .i64 value.val value.property

/-- One source matrix contributes one contiguous column block per outer iteration. -/
def concat_matrix_single_step (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dest source : Nat) (rows : I64) (registers : I64 × List I64) :
    BitMutationM (ForInStep (I64 × List I64)) := do
  let sourcePos := registers.2.getD 0 (int 1)
  copy dest registers.1 source sourcePos rows
  pure (ForInStep.yield (registers.1 + rows, registers.2.set 0 (sourcePos + rows)))

/-- A singleton-input matrix-vcat allocates the requested shape and copies its columns in order. -/
def concat_matrix_single_program (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (A : BitMatrix) (rows cols : I64) (allocate : I64 → I64 → BitMutationM BitMatrix) :
    BitMutationM BitMatrix := do
  let out ← allocate rows cols
  let _ ← forIn (intRange (int 1) cols) (int 1, [int 1])
    (fun (_ : I64) registers => concat_matrix_single_step copy out.chunks A.chunks rows registers)
  pure out

/-- The nested installed loops reduce to one column-copy step per column for a singleton input. -/
theorem concat_matrix_single_factor (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (A : BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) :
    concat_matrix_program copy [A] sizeDim allocate =
      concat_matrix_single_program copy A (sizeDim A (int 1)) (sizeDim A (int 2)) allocate := by
  unfold concat_matrix_program concat_matrix_single_program concat_matrix_single_step
  simp only [List.forIn_cons, List.forIn_nil, List.length_cons, List.length_nil,
    Nat.zero_add, Int.ofNat_one, pure_bind, bind_assoc, concat_zero_add, List.nil_append,
    show intRange (int 2) (int 1) = [] from rfl,
    show intRange (int 1) (int 1) = [int 1] from rfl,
    show (int 1).val.toNat - 1 = 0 from rfl, List.getD_cons_zero,
    List.replicate_succ, List.replicate_zero]

/-- One singleton matrix column step composes a successful copy with its exact register update. -/
theorem concat_matrix_step_from_copy (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dest source : Nat) (rows position sourcePos : I64) (s finished : State)
    (hcopy : (copy dest position source sourcePos rows).run s = (.ok (), finished)) :
    (concat_matrix_single_step copy dest source rows (position, [sourcePos])).run s =
      (.ok (ForInStep.yield (position + rows, [sourcePos + rows])), finished) := by
  simp only [concat_matrix_single_step, List.getD_cons_zero, List.set_cons_zero,
    shape_run_bind, hcopy, shape_run_pure]

/-- Abstract column iteration composes consecutive successful register/heap steps. -/
theorem concat_columns_loop {α : Type} (indices : List α) (start limit : Nat)
    (registers : Nat → I64 × List I64) (state : Nat → State)
    (step : (I64 × List I64) → BitMutationM (ForInStep (I64 × List I64)))
    (hstep : ∀ column, column < limit →
      (step (registers column)).run (state column) =
        (.ok (ForInStep.yield (registers (column + 1))), state (column + 1)))
    (hbound : start + indices.length ≤ limit) :
    (forIn indices (registers start) (fun _ current => step current)).run (state start) =
      (.ok (registers (start + indices.length)), state (start + indices.length)) := by
  induction indices generalizing start with
  | nil => simp only [List.forIn_nil, List.length_nil, Nat.add_zero, shape_run_pure]
  | cons index indices ih =>
    have hs : start < limit := by simp only [List.length_cons] at hbound; omega
    have ht := ih (start + 1) (by simp only [List.length_cons] at hbound; omega)
    have he : start + 1 + indices.length = start + (index :: indices).length := by
      simp only [List.length_cons]
      omega
    rw [he] at ht
    simp only [List.forIn_cons, shape_run_bind, hstep start hs]
    exact ht

/-- The source and destination cursors after copying a given number of singleton matrix columns. -/
def concat_matrix_registers (rows column : Nat) : I64 × List I64 :=
  (int ((column * rows + 1 : Nat) : Int), [int ((column * rows + 1 : Nat) : Int)])

/-- One installed matrix-column step copies the next exact logical prefix and advances both cursors. -/
theorem concat_matrix_column_run (s : State) (sourceHandle : Nat) (xs : List Bool)
    (rows cols column : Nat) (hshape : xs.length = rows * cols)
    (hrows : 0 < rows) (hcolumn : column < cols) (hsize : xs.length ≤ 64)
    (hready : concat_ready s (xs, sourceHandle)) :
    (concat_matrix_single_step copyChunks s.arrays.length sourceHandle (int rows)
      (concat_matrix_registers rows column)).run
      (concat_extend s (packedPrefix (xs.take (column * rows)) 0 64)) =
      (.ok (ForInStep.yield (concat_matrix_registers rows (column + 1))),
        concat_extend s (packedPrefix (xs.take ((column + 1) * rows)) 0 64)) := by
  have hstep : column * rows + rows = (column + 1) * rows := by
    simp only [Nat.add_mul, Nat.one_mul]
  have hsource : column * rows + rows ≤ xs.length := by
    rw [hstep, hshape, Nat.mul_comm rows cols]
    exact Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hcolumn)
  have hpos : 0 < xs.length := by omega
  have hcopy := concat_copy_prefix_run s sourceHandle xs (column * rows) rows hready.1 hrows
    hsource hsize (hready.2 hpos _)
  have hrun := concat_matrix_step_from_copy copyChunks s.arrays.length sourceHandle (int rows)
    (int ((column * rows + 1 : Nat) : Int)) (int ((column * rows + 1 : Nat) : Int)) _ _ hcopy
  have hposition : int ((column * rows + 1 : Nat) : Int) + int rows =
      int (((column + 1) * rows + 1 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    rw [← hstep]
    omega
  apply hrun.trans
  simp only [concat_matrix_registers, hposition, hstep]

/-- Allocation followed by a successful dependent copy returns the allocated output and the final heap. -/
theorem concat_two_stage_run {α β : Type} (allocate : BitMutationM α) (copy : α → BitMutationM β)
    (s allocated finished : State) (out : α) (register : β)
    (hallocate : allocate.run s = (.ok out, allocated))
    (hcopy : (copy out).run allocated = (.ok register, finished)) :
    ((do let out ← allocate; let _ ← copy out; pure out) : BitMutationM α).run s =
      (.ok out, finished) := by
  simp only [shape_run_bind, hallocate, hcopy, shape_run_pure]

/-- Singleton matrix-vcat composes its allocation and complete column-copy loop. -/
theorem concat_matrix_single_from_runs
    (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (A : BitMatrix) (rows cols : I64) (allocate : I64 → I64 → BitMutationM BitMatrix)
    (s allocated finished : State) (out : BitMatrix) (registers : I64 × List I64)
    (hallocate : (allocate rows cols).run s = (.ok out, allocated))
    (hcopy : (forIn (intRange (int 1) cols) (int 1, [int 1])
      (fun (_ : I64) current => concat_matrix_single_step copy out.chunks A.chunks rows current)).run allocated =
      (.ok registers, finished)) :
    (concat_matrix_single_program copy A rows cols allocate).run s = (.ok out, finished) :=
  concat_two_stage_run (allocate rows cols)
    (fun output => forIn (intRange (int 1) cols) (int 1, [int 1])
      (fun (_ : I64) current => concat_matrix_single_step copy output.chunks A.chunks rows current))
    s allocated finished out registers hallocate hcopy

/-- Singleton matrix-vcat copies all columns exactly when its logical data fit one initialized word. -/
theorem concat_matrix_single_ready (A : BitMatrix) (xs : List Bool) (rows cols : Nat) (s : State)
    (hshape : xs.length = rows * cols) (hpos : 0 < xs.length) (hbound : xs.length ≤ 64)
    (hready : concat_ready s (xs, A.chunks)) :
    (concat_matrix_single_program copyChunks A (int rows) (int cols) concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int xs.length, [int rows, int cols]⟩ : BitMatrix),
        concat_extend s (packedPrefix xs 0 64)) := by
  have hrpos : 0 < rows := by
    by_cases h : rows = 0
    · simp only [h, Nat.zero_mul] at hshape
      omega
    · omega
  have hcpos : 0 < cols := by
    by_cases h : cols = 0
    · simp only [h, Nat.mul_zero] at hshape
      omega
    · omega
  have hr : rows ≤ 64 := by
    have h := Nat.mul_le_mul_left rows (show 1 ≤ cols by omega)
    simp only [Nat.mul_one] at h
    omega
  have hc : cols ≤ 64 := by
    have h := Nat.mul_le_mul_right cols (show 1 ≤ rows by omega)
    simp only [Nat.one_mul] at h
    omega
  have halloc : (concat_allocate_matrix_fn (int rows) (int cols)).run s =
      (.ok (⟨s.arrays.length, int ((rows * cols : Nat) : Int), [int rows, int cols]⟩ : BitMatrix),
        concat_extend s (u64 0)) :=
    concat_allocate_matrix rows cols hr hc (by omega) (by omega) s
  rw [← hshape] at halloc
  have hindices : (intRange (int 1) (int cols)).length = cols := by
    rw [packedObserve_intRange cols (by omega), List.length_map, List.length_range]
  have hloop := concat_columns_loop (intRange (int 1) (int cols)) 0 cols
    (concat_matrix_registers rows)
    (fun column => concat_extend s (packedPrefix (xs.take (column * rows)) 0 64))
    (concat_matrix_single_step copyChunks s.arrays.length A.chunks (int rows))
    (fun column hc => concat_matrix_column_run s A.chunks xs rows cols column hshape hrpos hc hbound hready)
    (by rw [hindices]; omega)
  have hzero : packedPrefix [] 0 64 = u64 0 := (packedWord_zero_iff [] 0).mpr (fun _ _ => rfl)
  have htake : xs.take (cols * rows) = xs := by rw [Nat.mul_comm cols rows, ← hshape, List.take_length]
  simp only [hindices, Nat.zero_add, concat_matrix_registers, Nat.zero_mul, List.take_zero, hzero,
    Int.ofNat_one, htake] at hloop
  exact concat_matrix_single_from_runs copyChunks A (int rows) (int cols) concat_allocate_matrix_fn
    s _ _ _ _ halloc hloop

/-- A singleton frozen matrix-vcat input of any positive shape up to 64 bits preserves all data and padding. -/
theorem concat_matrix_single_correct (xs : List Bool) (rows cols : Nat)
    (hshape : xs.length = rows * cols) (hpos : 0 < xs.length) (hbound : xs.length ≤ 64) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices [(⟨0, int xs.length, [int rows, int cols]⟩ : BitMatrix)]
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run (concat_initial [xs]) = (.ok out, finished) ∧
      out.dims = [int rows, int cols] ∧ bitValues finished out = xs ∧
      Round5.Round2.PackedInvariant finished out := by
  let s := concat_initial [xs]
  let A : BitMatrix := ⟨0, int xs.length, [int rows, int cols]⟩
  let out : BitMatrix := ⟨s.arrays.length, int xs.length, [int rows, int cols]⟩
  let finished := concat_extend s (packedPrefix xs 0 64)
  have hready : concat_ready s (xs, A.chunks) :=
    concat_initial_ready [xs] (xs, 0) (by simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_singleton]) hbound
  have hrun := concat_matrix_single_ready A xs rows cols s hshape hpos hbound hready
  refine ⟨out, finished, ?_, rfl, ?_, ?_⟩
  · change (concat_matrix_program copyChunks [A]
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        concat_allocate_matrix_fn).run s = (.ok out, finished)
    rw [concat_matrix_single_factor]
    exact hrun
  · exact concat_word_bitValues s xs _ hbound
  · exact concat_word_invariant s xs _ hpos hbound


/-- The frozen column-major expected list for a single matrix is exactly its logical input. -/
theorem concat_matrix_single_expected (xs : List Bool) (rows cols : Nat)
    (hshape : xs.length = rows * cols) :
    ((List.range cols).flatMap fun column =>
      ([(rows, xs)] : List (Nat × List Bool)).flatMap fun input =>
        (List.range input.1).map fun row => input.2.getD (row + column * input.1) false) = xs := by
  simp only [List.flatMap_singleton]
  have h := packedGrouping_flatMapRange rows cols (fun index => xs.getD index false)
  simp only [Nat.add_comm] at h
  rw [h, Nat.mul_comm cols rows, ← hshape,
    packedGrouping_getDPadded xs false xs.length (Nat.le_refl _)]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]

/-- One-word copying of an arbitrary source interval appends its exact logical slice. -/
theorem concat_copy_slice_ready (source : List Bool) (sourceHandle : Nat)
    (accum : List Bool) (start count : Nat) (s : State)
    (hready : concat_ready s (source, sourceHandle))
    (hsource : start + count ≤ source.length) (hsize : source.length ≤ 64)
    (hbound : accum.length + count ≤ 64) :
    (copyChunks s.arrays.length (int ((accum.length + 1 : Nat) : Int)) sourceHandle
      (int ((start + 1 : Nat) : Int)) (int count)).run
      (concat_extend s (packedPrefix accum 0 64)) =
      (.ok (), concat_extend s (packedPrefix (accum ++ (source.drop start).take count) 0 64)) := by
  by_cases hp : 0 < count
  · have hspos : 0 < source.length := by omega
    have hrun := concat_slice_copy_run s.arrays.length sourceHandle accum.length start count
      (concat_extend s (packedPrefix accum 0 64))
      (concat_extend s (concat_slice_copy_word (packedPrefix accum 0 64) (packedPrefix source 0 64)
        accum.length start count))
      (packedPrefix accum 0 64) (packedPrefix source 0 64)
      (by have := hready.1; omega) hp hbound (by omega)
      (hready.2 hspos _) (concat_extend_read s _) (concat_extend_store s _ _)
    apply hrun.trans
    rw [concat_slice_copy_append accum source start count hbound hsource hsize]
  · have hz : count = 0 := by omega
    subst count
    simp only [List.take_zero, List.append_nil, Int.ofNat_zero]
    exact concat_copy_zero _ _ _ _ _


/-- Native-index iteration is the zero-based range iteration after decoding its public indices. -/
theorem concat_native_index_loop {α : Type} (count : Nat) (initial : α)
    (step : Nat → α → BitMutationM (ForInStep α)) (hbound : count ≤ 9223372036854775807) :
    forIn (intRange (int 1) (int count)) initial
      (fun i current => step (i.val.toNat - 1) current) =
      forIn (List.range count) initial step := by
  rw [packedObserve_intRange count hbound, List.forIn_map]
  apply concat_forIn_congr
  intro index hindex current
  have hi : index < count := List.mem_range.mp hindex
  have hv : (int ((index + 1 : Nat) : Int)).val.toNat - 1 = index := by
    rw [packedInt_val (index + 1) (by omega), Int.toNat_natCast]
    omega
  rw [hv]

/-- The source cursors during a column: processed matrices have advanced, the rest retain their old cursor. -/
def concat_matrix_cursors (rows : List Nat) (column processed : Nat) : List I64 :=
  rows.mapIdx fun index row =>
    if index < processed then int (((column + 1) * row + 1 : Nat) : Int)
    else int ((column * row + 1 : Nat) : Int)

/-- The current matrix's source cursor has not yet advanced within its column. -/
theorem concat_matrix_cursor_get (rows : List Nat) (column index : Nat) (hi : index < rows.length) :
    (concat_matrix_cursors rows column index).getD index (int 1) =
      int ((column * rows[index] + 1 : Nat) : Int) := by
  have hlen : index < (concat_matrix_cursors rows column index).length := by
    simpa only [concat_matrix_cursors, List.length_mapIdx] using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp only [concat_matrix_cursors, List.getElem_mapIdx, Nat.lt_irrefl, ite_false]

/-- Updating exactly the current cursor advances the processed prefix by one matrix. -/
theorem concat_matrix_cursor_set (rows : List Nat) (column index : Nat) (hi : index < rows.length) :
    (concat_matrix_cursors rows column index).set index
      (int (((column + 1) * rows[index] + 1 : Nat) : Int)) =
      concat_matrix_cursors rows column (index + 1) := by
  apply List.ext_getElem
  · simp only [concat_matrix_cursors, List.length_set, List.length_mapIdx]
  · intro j hleft hright
    simp only [List.getElem_set, concat_matrix_cursors, List.getElem_mapIdx]
    by_cases he : index = j
    · subst j
      simp only [ite_true, Nat.lt_succ_self]
    · have hc : (j < index + 1) = (j < index) := propext (by omega)
      simp only [he, ite_false, hc]

/-- Before the first column all source cursors are the installed one-based initial value. -/
theorem concat_matrix_cursors_initial (rows : List Nat) :
    concat_matrix_cursors rows 0 0 = List.replicate rows.length (int 1) := by
  unfold concat_matrix_cursors
  simp only [Nat.not_lt_zero, ite_false, Nat.zero_mul, Nat.zero_add, Int.ofNat_one]
  rw [List.mapIdx_eq_zipIdx_map]
  simp only [List.map_const', List.length_zipIdx]

/-- Finishing a column establishes the starting source cursors of the next column. -/
theorem concat_matrix_cursors_next (rows : List Nat) (column : Nat) :
    concat_matrix_cursors rows column rows.length = concat_matrix_cursors rows (column + 1) 0 := by
  apply List.ext_getElem
  · simp only [concat_matrix_cursors, List.length_mapIdx]
  · intro index hleft hright
    have hi : index < rows.length := by simpa only [concat_matrix_cursors, List.length_mapIdx] using hleft
    simp only [concat_matrix_cursors, List.getElem_mapIdx, hi, ite_true, Nat.not_lt_zero, ite_false]

/-- One source entry records its row count, column-major logical bits, and immutable source handle. -/
def concat_matrix_entry (columns : Nat) (entry : Nat × List Bool × Nat) : BitMatrix :=
  ⟨entry.2.2, int entry.2.1.length, [int entry.1, int columns]⟩

/-- The logical block contributed by one source matrix in a column. -/
def concat_matrix_slice (column : Nat) (entry : Nat × List Bool × Nat) : List Bool :=
  (entry.2.1.drop (column * entry.1)).take entry.1

/-- Column prefixes are the exact expected output order of variadic matrix vcat. -/
def concat_matrix_bits (entries : List (Nat × List Bool × Nat)) (columns : Nat) : List Bool :=
  (List.range columns).flatMap fun column => entries.flatMap (concat_matrix_slice column)

/-- A well-shaped source contributes exactly its row count in every valid column. -/
theorem concat_matrix_slice_length (entry : Nat × List Bool × Nat) (column columns : Nat)
    (hshape : entry.2.1.length = entry.1 * columns) (hc : column < columns) :
    (concat_matrix_slice column entry).length = entry.1 := by
  have hbound : column * entry.1 + entry.1 ≤ entry.2.1.length := by
    calc
      column * entry.1 + entry.1 = (column + 1) * entry.1 := by simp only [Nat.add_mul, Nat.one_mul]
      _ ≤ columns * entry.1 := Nat.mul_le_mul_right entry.1 (Nat.succ_le_of_lt hc)
      _ = entry.2.1.length := by rw [hshape, Nat.mul_comm]
  simp only [concat_matrix_slice, List.length_take, List.length_drop]
  omega

/-- Concatenating all source column slices sums their row counts. -/
theorem concat_matrix_column_length (entries : List (Nat × List Bool × Nat)) (column columns : Nat)
    (hshape : ∀ entry ∈ entries, entry.2.1.length = entry.1 * columns) (hc : column < columns) :
    (entries.flatMap (concat_matrix_slice column)).length = (entries.map Prod.fst).sum := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      concat_matrix_slice_length entry column columns (hshape entry List.mem_cons_self) hc,
      ih (fun e he => hshape e (List.mem_cons_of_mem entry he))]

/-- Every complete output-column prefix has its expected rectangular length. -/
theorem concat_matrix_bits_length (entries : List (Nat × List Bool × Nat)) (count columns : Nat)
    (hshape : ∀ entry ∈ entries, entry.2.1.length = entry.1 * columns) (hc : count ≤ columns) :
    (concat_matrix_bits entries count).length = count * (entries.map Prod.fst).sum := by
  induction count with
  | zero => simp only [concat_matrix_bits, List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | succ count ih =>
    unfold concat_matrix_bits
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
    change (concat_matrix_bits entries count).length + _ = _
    rw [ih (by omega), concat_matrix_column_length entries count columns hshape (by omega)]
    simp only [Nat.succ_mul]

/-- A mapped list's in-bounds defaulted lookup is exactly the mapped element. -/
theorem concat_getD_map_index {α β : Type} (items : List α) (f : α → β)
    (fallback : β) (index : Nat) (hi : index < items.length) :
    (items.map f).getD index fallback = f items[index] := by
  have hm : index < (items.map f).length := by simpa only [List.length_map] using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some, List.getElem_map]

/-- A source inner step exposes only its one copy and its deterministic register update. -/
theorem concat_matrix_raw_from_copy (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dest : Nat) (arrays : List BitMatrix) (heights : List I64) (fallback A : BitMatrix)
    (index : Nat) (position sourcePos rows : I64) (cursors : List I64) (s finished : State)
    (ha : arrays.getD index fallback = A) (hr : heights.getD index (int 0) = rows)
    (hs : cursors.getD index (int 1) = sourcePos)
    (hcopy : (copy dest position A.chunks sourcePos rows).run s = (.ok (), finished)) :
    (concat_matrix_raw_step copy dest arrays heights fallback index (position, cursors)).run s =
      (.ok (ForInStep.yield (position + rows, cursors.set index (sourcePos + rows))), finished) := by
  simp only [concat_matrix_raw_step, ha, hr, hs, shape_run_bind, hcopy, shape_run_pure]

/-- One installed inner matrix-vcat step appends its selected column slice and advances exactly its cursor. -/
theorem concat_matrix_entry_step (entries : List (Nat × List Bool × Nat))
    (columns column index : Nat) (fallback : BitMatrix) (accum : List Bool) (s : State)
    (hi : index < entries.length) (hc : column < columns)
    (hshape : ∀ entry ∈ entries, entry.2.1.length = entry.1 * columns)
    (hsize : ∀ entry ∈ entries, entry.2.1.length ≤ 64)
    (hready : ∀ entry ∈ entries, concat_ready s entry.2)
    (hbound : accum.length + (entries[index]).1 ≤ 64) :
    (concat_matrix_raw_step copyChunks s.arrays.length (entries.map (concat_matrix_entry columns))
      (entries.map fun entry => int entry.1) fallback index
      (int ((accum.length + 1 : Nat) : Int), concat_matrix_cursors (entries.map Prod.fst) column index)).run
      (concat_extend s (packedPrefix accum 0 64)) =
      (.ok (ForInStep.yield (int (((accum ++ concat_matrix_slice column entries[index]).length + 1 : Nat) : Int),
        concat_matrix_cursors (entries.map Prod.fst) column (index + 1))),
        concat_extend s (packedPrefix (accum ++ concat_matrix_slice column entries[index]) 0 64)) := by
  let entry := entries[index]
  have hm : entry ∈ entries := List.getElem_mem hi
  have hsource : column * entry.1 + entry.1 ≤ entry.2.1.length := by
    calc
      column * entry.1 + entry.1 = (column + 1) * entry.1 := by simp only [Nat.add_mul, Nat.one_mul]
      _ ≤ columns * entry.1 := Nat.mul_le_mul_right entry.1 (Nat.succ_le_of_lt hc)
      _ = entry.2.1.length := by rw [hshape entry hm, Nat.mul_comm]
  have hcursor := concat_matrix_cursor_get (entries.map Prod.fst) column index
    (by simpa only [List.length_map] using hi)
  simp only [List.getElem_map] at hcursor
  have hcopy := concat_copy_slice_ready entry.2.1 entry.2.2 accum (column * entry.1) entry.1 s
    (hready entry hm) hsource (hsize entry hm) hbound
  have hrun := concat_matrix_raw_from_copy copyChunks s.arrays.length
    (entries.map (concat_matrix_entry columns)) (entries.map fun entry => int entry.1)
    fallback (concat_matrix_entry columns entry) index
    (int ((accum.length + 1 : Nat) : Int)) (int ((column * entry.1 + 1 : Nat) : Int)) (int entry.1)
    (concat_matrix_cursors (entries.map Prod.fst) column index) _ _
    (concat_getD_map_index entries _ fallback index hi)
    (concat_getD_map_index entries (fun entry => int entry.1) (int 0) index hi)
    hcursor hcopy
  have hdest : int ((accum.length + 1 : Nat) : Int) + int entry.1 =
      int (((accum ++ concat_matrix_slice column entry).length + 1 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    rw [List.length_append, concat_matrix_slice_length entry column columns (hshape entry hm) hc]
    omega
  have hsrc : int ((column * entry.1 + 1 : Nat) : Int) + int entry.1 =
      int (((column + 1) * entry.1 + 1 : Nat) : Int) := by
    rw [packedInt_add]
    apply congrArg int
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hset := concat_matrix_cursor_set (entries.map Prod.fst) column index
    (by simpa only [List.length_map] using hi)
  simp only [List.getElem_map] at hset
  apply hrun.trans
  rw [hdest, hsrc, hset]
  rfl

/-- A prefix of the blocks in a flat-map has no more bits than the full flat-map. -/
theorem concat_flatMap_take_bound {α β : Type} (entries : List α) (f : α → List β) (count : Nat) :
    ((entries.take count).flatMap f).length ≤ (entries.flatMap f).length := by
  have he : (entries.take count).flatMap f ++ (entries.drop count).flatMap f = entries.flatMap f := by
    rw [← List.flatMap_append, List.take_append_drop]
  have hl := congrArg List.length he
  simp only [List.length_append] at hl
  omega

/-- Processing the next source matrix appends exactly its next column slice to the progressBits column. -/
theorem concat_matrix_partial_succ (entries : List (Nat × List Bool × Nat))
    (column index : Nat) (accum : List Bool) (hi : index < entries.length) :
    accum ++ (entries.take (index + 1)).flatMap (concat_matrix_slice column) =
      (accum ++ (entries.take index).flatMap (concat_matrix_slice column)) ++
        concat_matrix_slice column entries[index] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- The full installed inner loop appends one complete logical output column. -/
theorem concat_matrix_inner_run (entries : List (Nat × List Bool × Nat))
    (columns column : Nat) (fallback : BitMatrix) (accum : List Bool) (s : State)
    (hc : column < columns)
    (hshape : ∀ entry ∈ entries, entry.2.1.length = entry.1 * columns)
    (hsize : ∀ entry ∈ entries, entry.2.1.length ≤ 64)
    (hready : ∀ entry ∈ entries, concat_ready s entry.2)
    (hbound : accum.length + (entries.map Prod.fst).sum ≤ 64) :
    (forIn (List.range entries.length)
      (int ((accum.length + 1 : Nat) : Int), concat_matrix_cursors (entries.map Prod.fst) column 0)
      (concat_matrix_raw_step copyChunks s.arrays.length (entries.map (concat_matrix_entry columns))
        (entries.map fun entry => int entry.1) fallback)).run
      (concat_extend s (packedPrefix accum 0 64)) =
      (.ok (int (((accum ++ entries.flatMap (concat_matrix_slice column)).length + 1 : Nat) : Int),
        concat_matrix_cursors (entries.map Prod.fst) (column + 1) 0),
        concat_extend s (packedPrefix (accum ++ entries.flatMap (concat_matrix_slice column)) 0 64)) := by
  let progressBits := fun index => accum ++ (entries.take index).flatMap (concat_matrix_slice column)
  let registers := fun index => (int (((progressBits index).length + 1 : Nat) : Int),
    concat_matrix_cursors (entries.map Prod.fst) column index)
  let state := fun index => concat_extend s (packedPrefix (progressBits index) 0 64)
  let innerStep : Nat → (I64 × List I64) → BitMutationM (ForInStep (I64 × List I64)) :=
    concat_matrix_raw_step copyChunks s.arrays.length (entries.map (concat_matrix_entry columns))
      (entries.map fun entry => int entry.1) fallback
  have hstep (index : Nat) (hi : index < entries.length) :
      (innerStep index (registers index)).run (state index) =
        (.ok (ForInStep.yield (registers (index + 1))), state (index + 1)) := by
    have hs : (progressBits index).length + (entries[index]).1 ≤ 64 := by
      have ht := concat_flatMap_take_bound entries (concat_matrix_slice column) (index + 1)
      rw [concat_matrix_column_length entries column columns hshape hc] at ht
      have hp := congrArg List.length (concat_matrix_partial_succ entries column index accum hi)
      simp only [List.length_append, concat_matrix_slice_length entries[index] column columns
        (hshape _ (List.getElem_mem hi)) hc] at hp
      simp only [progressBits, List.length_append]
      omega
    have h := concat_matrix_entry_step entries columns column index fallback (progressBits index) s
      hi hc hshape hsize hready hs
    apply h.trans
    have he : progressBits (index + 1) = progressBits index ++ concat_matrix_slice column entries[index] :=
      concat_matrix_partial_succ entries column index accum hi
    change _ = (Except.ok (ForInStep.yield (int (((progressBits (index + 1)).length + 1 : Nat) : Int),
      concat_matrix_cursors (entries.map Prod.fst) column (index + 1))),
      concat_extend s (packedPrefix (progressBits (index + 1)) 0 64))
    rw [he]
  have h := concat_range_loop (α := I64 × List I64) 0 entries.length entries.length
    registers state innerStep hstep (by omega)
  have hn : entries.length = (entries.map Prod.fst).length := by simp only [List.length_map]
  simp only [← List.range_eq_range', Nat.zero_add, registers, state, progressBits,
    List.take_zero, List.flatMap_nil, List.append_nil, List.take_length] at h
  apply h.trans
  rw [hn, concat_matrix_cursors_next]

/-- Completing the next column appends exactly its source slices to the already copied columns. -/
theorem concat_matrix_bits_succ (entries : List (Nat × List Bool × Nat)) (column : Nat) :
    concat_matrix_bits entries (column + 1) =
      concat_matrix_bits entries column ++ entries.flatMap (concat_matrix_slice column) := by
  simp only [concat_matrix_bits, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- A successful loop action can be returned as a yielded outer-loop register. -/
theorem concat_yield_result {α : Type} (action : BitMutationM α) (s finished : State) (value : α)
    (hrun : action.run s = (.ok value, finished)) :
    ((do let value ← action; pure (ForInStep.yield value)) : BitMutationM (ForInStep α)).run s =
      (.ok (ForInStep.yield value), finished) := by
  simp only [shape_run_bind, hrun, shape_run_pure]

/-- The outer matrix-vcat step traverses all source matrices for its current column. -/
def concat_matrix_outer_step (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dest : Nat) (arrays : List BitMatrix) (heights : List I64) (fallback : BitMatrix)
    (registers : I64 × List I64) : BitMutationM (ForInStep (I64 × List I64)) := do
  let registers ← forIn (List.range arrays.length) registers
    (concat_matrix_raw_step copy dest arrays heights fallback)
  pure (ForInStep.yield registers)

/-- The complete installed nested-copy phase concatenates every input column in column-major order. -/
theorem concat_matrix_columns_run (entries : List (Nat × List Bool × Nat))
    (columns : Nat) (fallback : BitMatrix) (s : State)
    (hcols : columns ≤ 9223372036854775807)
    (hshape : ∀ entry ∈ entries, entry.2.1.length = entry.1 * columns)
    (hsize : ∀ entry ∈ entries, entry.2.1.length ≤ 64)
    (hready : ∀ entry ∈ entries, concat_ready s entry.2)
    (hbound : columns * (entries.map Prod.fst).sum ≤ 64) :
    (forIn (intRange (int 1) (int columns))
      (int 1, List.replicate entries.length (int 1))
      (fun (_ : I64) registers => concat_matrix_outer_step copyChunks s.arrays.length
        (entries.map (concat_matrix_entry columns)) (entries.map fun entry => int entry.1)
        fallback registers)).run (concat_extend s (u64 0)) =
      (.ok (int (((concat_matrix_bits entries columns).length + 1 : Nat) : Int),
        concat_matrix_cursors (entries.map Prod.fst) columns 0),
        concat_extend s (packedPrefix (concat_matrix_bits entries columns) 0 64)) := by
  let registers := fun column =>
    (int (((concat_matrix_bits entries column).length + 1 : Nat) : Int),
      concat_matrix_cursors (entries.map Prod.fst) column 0)
  let state := fun column => concat_extend s (packedPrefix (concat_matrix_bits entries column) 0 64)
  let step := concat_matrix_outer_step copyChunks s.arrays.length
    (entries.map (concat_matrix_entry columns)) (entries.map fun entry => int entry.1) fallback
  have hstep (column : Nat) (hc : column < columns) :
      (step (registers column)).run (state column) =
        (.ok (ForInStep.yield (registers (column + 1))), state (column + 1)) := by
    have hb : (concat_matrix_bits entries column).length + (entries.map Prod.fst).sum ≤ 64 := by
      rw [concat_matrix_bits_length entries column columns hshape (by omega)]
      have hm := Nat.mul_le_mul_right (entries.map Prod.fst).sum (Nat.succ_le_of_lt hc)
      simp only [Nat.succ_mul] at hm
      omega
    have hinner := concat_matrix_inner_run entries columns column fallback
      (concat_matrix_bits entries column) s hc hshape hsize hready hb
    have hrun := concat_yield_result _ _ _ _ hinner
    simp only [step, concat_matrix_outer_step, List.length_map]
    apply hrun.trans
    change _ = (Except.ok (ForInStep.yield
      (int (((concat_matrix_bits entries (column + 1)).length + 1 : Nat) : Int),
        concat_matrix_cursors (entries.map Prod.fst) (column + 1) 0)),
      concat_extend s (packedPrefix (concat_matrix_bits entries (column + 1)) 0 64))
    rw [concat_matrix_bits_succ]
  have hlength : (intRange (int 1) (int columns)).length = columns := by
    rw [packedObserve_intRange columns hcols, List.length_map, List.length_range]
  have hloop := concat_columns_loop (intRange (int 1) (int columns)) 0 columns registers state step
    hstep (by rw [hlength]; omega)
  have hzero : concat_matrix_bits entries 0 = [] := rfl
  have hpack : packedPrefix [] 0 64 = u64 0 := (packedWord_zero_iff [] 0).mpr (fun _ _ => rfl)
  simp only [hlength, Nat.zero_add, registers, state, hzero, List.length_nil, Nat.zero_add,
    Int.ofNat_one, hpack, concat_matrix_cursors_initial, List.length_map] at hloop
  exact hloop

/-- The matrix's public dimension observer returns the declared row count. -/
theorem concat_matrix_entry_rows (columns : Nat) (entry : Nat × List Bool × Nat) :
    (bitArraySizeRanked (concat_matrix_entry columns entry)).getD ((int 1).val.toNat - 1) (int 0) =
      int entry.1 := rfl

/-- The matrix's public dimension observer returns its shared declared column count. -/
theorem concat_matrix_entry_columns (columns : Nat) (entry : Nat × List Bool × Nat) :
    (bitArraySizeRanked (concat_matrix_entry columns entry)).getD ((int 2).val.toNat - 1) (int 0) =
      int columns := rfl

/-- The matrix-vcat row pass exactly sums all natural row counts and records them in source order. -/
theorem concat_matrix_scan_run (entries : List (Nat × List Bool × Nat)) (columns : Nat)
    (start : Int) (prior : List I64) (s : State) :
    (concat_matrix_scan (entries.map (concat_matrix_entry columns))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int start, prior)).run s =
      (.ok (int (start + (entries.map Prod.fst).sum), prior ++ entries.map (fun entry => int entry.1)), s) := by
  induction entries generalizing start prior with
  | nil => simp only [concat_matrix_scan, List.map_nil, List.forIn_nil, List.sum_nil,
      Int.ofNat_zero, Int.add_zero, List.append_nil, shape_run_pure]
  | cons entry entries ih =>
    simp only [concat_matrix_scan, List.map_cons, List.forIn_cons, shape_run_bind, shape_run_pure,
      concat_matrix_entry_rows, List.sum_cons]
    rw [packedInt_add]
    have h := ih (start + entry.1) (prior ++ [int entry.1])
    apply h.trans
    have hsum : int (start + entry.1 + (entries.map Prod.fst).sum) =
        int (start + ((entry.1 + (entries.map Prod.fst).sum : Nat) : Int)) := by
      apply congrArg int
      omega
    rw [hsum, List.append_assoc]
    rfl

/-- Validation succeeds without changing the heap whenever every defaulted lookup has the expected columns. -/
theorem concat_matrix_validation_run (indices : List I64) (lookup : I64 → I64)
    (columns : I64) (s : State) (hall : ∀ index ∈ indices, lookup index = columns) :
    (forIn indices () (fun index _ => (do
      if lookup index != columns then throw (.dimensionMismatch "column lengths must match")
      pure (ForInStep.yield ())) : I64 → Unit → BitMutationM (ForInStep Unit))).run s = (.ok (), s) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    simp only [List.forIn_cons, hall index List.mem_cons_self, bne_self_eq_false,
      Bool.false_eq_true, ite_false, shape_run_bind, shape_run_pure]
    exact ih (fun i hi => hall i (List.mem_cons_of_mem index hi))

/-- Defaulted lookup preserves a common declared matrix column count, even outside the input list. -/
theorem concat_matrix_lookup_columns (entries : List (Nat × List Bool × Nat))
    (first : Nat × List Bool × Nat) (columns index : Nat) :
    (bitArraySizeRanked ((entries.map (concat_matrix_entry columns)).getD index
      (concat_matrix_entry columns first))).getD ((int 2).val.toNat - 1) (int 0) = int columns := by
  by_cases hi : index < entries.length
  · rw [concat_getD_map_index entries (concat_matrix_entry columns) _ index hi]
    exact concat_matrix_entry_columns columns entries[index]
  · have hm : (entries.map (concat_matrix_entry columns)).length ≤ index := by
      simp only [List.length_map]
      omega
    have he : (entries.map (concat_matrix_entry columns)).getD index
        (concat_matrix_entry columns first) = concat_matrix_entry columns first := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hm, Option.getD_none]
    rw [he]
    exact concat_matrix_entry_columns columns first

/-- Decoding the installed native inner indices produces exactly the verified zero-based inner loop. -/
theorem concat_matrix_copies_factor (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (arrays : List BitMatrix) (fallback : BitMatrix) (heights : List I64)
    (columns : I64) (out : BitMatrix) (hbound : arrays.length ≤ 9223372036854775807) :
    concat_matrix_copies copy arrays fallback heights columns out =
      forIn (intRange (int 1) columns) (int 1, List.replicate arrays.length (int 1))
        (fun (_ : I64) registers => concat_matrix_outer_step copy out.chunks arrays heights fallback registers) := by
  unfold concat_matrix_copies concat_matrix_outer_step
  apply concat_forIn_congr
  intro index hi registers
  rw [concat_native_index_loop arrays.length registers
    (concat_matrix_raw_step copy out.chunks arrays heights fallback) hbound]

/-- Successful frozen matrix phases compose into the exact final output and heap. -/
theorem concat_matrix_from_runs (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (arrays : List BitMatrix) (first : BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) (rows : I64) (heights : List I64)
    (s allocated finished : State) (out : BitMatrix) (registers : I64 × List I64)
    (hscan : (concat_matrix_scan arrays sizeDim (int 0, [])).run s = (.ok (rows, heights), s))
    (hvalidation : (concat_matrix_validation arrays first sizeDim (sizeDim first (int 2))).run s = (.ok (), s))
    (hallocate : (allocate rows (sizeDim first (int 2))).run s = (.ok out, allocated))
    (hcopy : (concat_matrix_copies copy arrays first heights (sizeDim first (int 2)) out).run allocated =
      (.ok registers, finished)) :
    (concat_matrix_body copy arrays first sizeDim allocate).run s = (.ok out, finished) := by
  apply concat_bind_success (concat_matrix_scan arrays sizeDim (int 0, []))
    (concat_matrix_after_scan copy arrays first sizeDim allocate) s s finished (rows, heights) out hscan
  exact concat_three_stage_run (concat_matrix_validation arrays first sizeDim (sizeDim first (int 2)))
    (allocate rows (sizeDim first (int 2)))
    (concat_matrix_copies copy arrays first heights (sizeDim first (int 2)))
    s allocated finished out registers hvalidation hallocate hcopy

/-- The complete installed matrix-vcat operation succeeds for arbitrary ready sources with one-word total output. -/
theorem concat_matrix_multi_ready (first : Nat × List Bool × Nat)
    (rest : List (Nat × List Bool × Nat)) (columns : Nat) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hshape : ∀ entry ∈ first :: rest, entry.2.1.length = entry.1 * columns)
    (hsize : ∀ entry ∈ first :: rest, entry.2.1.length ≤ 64)
    (hready : ∀ entry ∈ first :: rest, concat_ready s entry.2)
    (hpos : 0 < columns * ((first :: rest).map Prod.fst).sum)
    (hbound : columns * ((first :: rest).map Prod.fst).sum ≤ 64) :
    (bitArrayVcatMatrices ((first :: rest).map (concat_matrix_entry columns))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int (concat_matrix_bits (first :: rest) columns).length,
        [int ((first :: rest).map Prod.fst).sum, int columns]⟩ : BitMatrix),
        concat_extend s (packedPrefix (concat_matrix_bits (first :: rest) columns) 0 64)) := by
  let entries := first :: rest
  let rows := (entries.map Prod.fst).sum
  let arrays := entries.map (concat_matrix_entry columns)
  let head := concat_matrix_entry columns first
  let heights := entries.map fun entry => int entry.1
  let bits := concat_matrix_bits entries columns
  let out : BitMatrix := ⟨s.arrays.length, int bits.length, [int rows, int columns]⟩
  have hrpos : 0 < rows := by
    by_cases h : rows = 0
    · change 0 < columns * rows at hpos
      simp only [h, Nat.mul_zero] at hpos
      omega
    · omega
  have hcpos : 0 < columns := by
    by_cases h : columns = 0
    · simp only [h, Nat.zero_mul] at hpos
      omega
    · omega
  have hr : rows ≤ 64 := by
    have hm := Nat.mul_le_mul_right rows (show 1 ≤ columns by omega)
    simp only [Nat.one_mul] at hm
    change columns * rows ≤ 64 at hbound
    omega
  have hc : columns ≤ 64 := by
    have hm := Nat.mul_le_mul_left columns (show 1 ≤ rows by omega)
    simp only [Nat.mul_one] at hm
    change columns * rows ≤ 64 at hbound
    omega
  have hbits : bits.length = rows * columns := by
    rw [Nat.mul_comm rows columns]
    exact concat_matrix_bits_length entries columns columns hshape (Nat.le_refl _)
  have hscan : (concat_matrix_scan arrays
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int 0, [])).run s =
      (.ok (int rows, heights), s) := by
    have h := concat_matrix_scan_run entries columns 0 [] s
    simpa only [Int.zero_add, List.nil_append] using h
  have hvalidation : (concat_matrix_validation arrays head
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int columns)).run s = (.ok (), s) := by
    apply concat_matrix_validation_run
    intro index hi
    exact concat_matrix_lookup_columns entries first columns (index.val.toNat - 1)
  have hallocate : (concat_allocate_matrix_fn (int rows) (int columns)).run s =
      (.ok (⟨s.arrays.length, int ((rows * columns : Nat) : Int), [int rows, int columns]⟩ : BitMatrix),
        concat_extend s (u64 0)) :=
    concat_allocate_matrix rows columns hr hc
      (by rw [Nat.mul_comm]; exact hpos) (by rw [Nat.mul_comm]; exact hbound) s
  rw [← hbits] at hallocate
  have hcopy : (concat_matrix_copies copyChunks arrays head heights (int columns) out).run
      (concat_extend s (u64 0)) =
      (.ok (int ((bits.length + 1 : Nat) : Int), concat_matrix_cursors (entries.map Prod.fst) columns 0),
        concat_extend s (packedPrefix bits 0 64)) := by
    rw [concat_matrix_copies_factor copyChunks arrays head heights (int columns) out
      (by simpa only [arrays, List.length_map] using hcount)]
    have h := concat_matrix_columns_run entries columns head s (by omega) hshape hsize hready hbound
    simpa only [arrays, List.length_map] using h
  have hrun := concat_matrix_from_runs copyChunks arrays head
    (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
    concat_allocate_matrix_fn (int rows) heights s _ _ out _ hscan hvalidation hallocate hcopy
  change (concat_matrix_program copyChunks
      (concat_matrix_entry columns first :: rest.map (concat_matrix_entry columns))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      concat_allocate_matrix_fn).run s = _
  rw [concat_matrix_nonempty_factor]
  exact hrun

/-- For arbitrary ready matrices, one-word matrix vcat preserves the full logical column-major specification and packing. -/
theorem concat_matrix_multi_correct (first : Nat × List Bool × Nat)
    (rest : List (Nat × List Bool × Nat)) (columns : Nat) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hshape : ∀ entry ∈ first :: rest, entry.2.1.length = entry.1 * columns)
    (hsize : ∀ entry ∈ first :: rest, entry.2.1.length ≤ 64)
    (hready : ∀ entry ∈ first :: rest, concat_ready s entry.2)
    (hpos : 0 < columns * ((first :: rest).map Prod.fst).sum)
    (hbound : columns * ((first :: rest).map Prod.fst).sum ≤ 64) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices ((first :: rest).map (concat_matrix_entry columns))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        concat_allocate_matrix_fn).run s = (.ok out, finished) ∧
      out.dims = [int ((first :: rest).map Prod.fst).sum, int columns] ∧
      bitValues finished out = concat_matrix_bits (first :: rest) columns ∧
      Round5.Round2.PackedInvariant finished out := by
  let bits := concat_matrix_bits (first :: rest) columns
  have hl : bits.length = columns * ((first :: rest).map Prod.fst).sum :=
    concat_matrix_bits_length (first :: rest) columns columns hshape (Nat.le_refl _)
  refine ⟨⟨s.arrays.length, int bits.length, [int ((first :: rest).map Prod.fst).sum, int columns]⟩,
    concat_extend s (packedPrefix bits 0 64),
    concat_matrix_multi_ready first rest columns s hcount hshape hsize hready hpos hbound, rfl, ?_, ?_⟩
  · exact concat_word_bitValues s bits _ (by omega)
  · exact concat_word_invariant s bits _ (by omega) (by omega)


/-- Add the frozen consecutive source handles to the logical matrix inputs. -/
def concat_matrix_indexed (inputs : List (Nat × List Bool)) : List (Nat × List Bool × Nat) :=
  inputs.zipIdx.map fun entry => (entry.1.1, entry.1.2, entry.2)

/-- Erasing assigned handles recovers exactly the logical matrix inputs. -/
theorem concat_matrix_indexed_inputs (inputs : List (Nat × List Bool)) :
    (concat_matrix_indexed inputs).map (fun entry => (entry.1, entry.2.1)) = inputs := by
  simp only [concat_matrix_indexed, List.map_map]
  exact List.zipIdx_map_fst 0 inputs

/-- Assigned matrix handles agree with the indexed list of all source bit vectors. -/
theorem concat_matrix_indexed_pairs (inputs : List (Nat × List Bool)) :
    (concat_matrix_indexed inputs).map Prod.snd = (inputs.map Prod.snd).zipIdx := by
  simp only [concat_matrix_indexed, List.map_map, List.zipIdx_map]
  rfl

/-- Indexing preserves the input row counts in their exact source order. -/
theorem concat_matrix_indexed_rows (inputs : List (Nat × List Bool)) :
    (concat_matrix_indexed inputs).map Prod.fst = inputs.map Prod.fst := by
  have h := congrArg (fun items : List (Nat × List Bool) => items.map Prod.fst)
    (concat_matrix_indexed_inputs inputs)
  simpa only [List.map_map, Function.comp_def] using h

/-- Indexing preserves the number of source matrices. -/
theorem concat_matrix_indexed_length (inputs : List (Nat × List Bool)) :
    (concat_matrix_indexed inputs).length = inputs.length := by
  simp only [concat_matrix_indexed, List.length_map, List.length_zipIdx]

/-- Every assigned source entry corresponds to its original logical input. -/
theorem concat_matrix_indexed_mem (inputs : List (Nat × List Bool)) (entry : Nat × List Bool × Nat)
    (he : entry ∈ concat_matrix_indexed inputs) : (entry.1, entry.2.1) ∈ inputs := by
  have h := List.mem_map_of_mem (f := fun entry : Nat × List Bool × Nat => (entry.1, entry.2.1)) he
  rw [concat_matrix_indexed_inputs] at h
  exact h

/-- Matrix input headers use exactly the frozen zip-with-range handle convention. -/
theorem concat_matrix_indexed_headers (inputs : List (Nat × List Bool)) (columns : Nat) :
    (concat_matrix_indexed inputs).map (concat_matrix_entry columns) =
      (inputs.zip (List.range inputs.length)).map (fun entry =>
        (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)) := by
  simp only [concat_matrix_indexed, List.map_map, List.zipIdx_eq_zip_range', ← List.range_eq_range']
  rfl

/-- A natural summand cannot exceed the sum of its source list. -/
theorem concat_member_le_sum (values : List Nat) (value : Nat) (hv : value ∈ values) :
    value ≤ values.sum := by
  induction values with
  | nil => cases hv
  | cons head values ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hv with he | ht
    · subst value
      omega
    · have h := ih ht
      omega

/-- The natural row sum is exactly the frozen left-fold row total. -/
theorem concat_matrix_rows_sum (inputs : List (Nat × List Bool)) :
    (inputs.map Prod.fst).sum = inputs.foldl (fun rows input => rows + input.1) 0 := by
  rw [List.sum_eq_foldl, List.foldl_map]

/-- Every well-shaped source fits one word if the complete matrix output fits one word. -/
theorem concat_matrix_input_size (inputs : List (Nat × List Bool)) (columns : Nat)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hbound : columns * (inputs.map Prod.fst).sum ≤ 64)
    (input : Nat × List Bool) (hi : input ∈ inputs) : input.2.length ≤ 64 := by
  have hr := concat_member_le_sum (inputs.map Prod.fst) input.1 (List.mem_map_of_mem (f := Prod.fst) hi)
  have hm := Nat.mul_le_mul_left columns hr
  rw [hshape input hi, Nat.mul_comm input.1 columns]
  omega

/-- The frozen initialMany heap supplies every indexed matrix source to the one-word copying invariant. -/
theorem concat_matrix_indexed_ready (inputs : List (Nat × List Bool)) (columns : Nat)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hbound : columns * (inputs.map Prod.fst).sum ≤ 64)
    (entry : Nat × List Bool × Nat) (he : entry ∈ concat_matrix_indexed inputs) :
    concat_ready (concat_initial (inputs.map Prod.snd)) entry.2 := by
  have hm := List.mem_map_of_mem (f := Prod.snd) he
  rw [concat_matrix_indexed_pairs] at hm
  exact concat_initial_ready (inputs.map Prod.snd) entry.2 hm
    (concat_matrix_input_size inputs columns hshape hbound (entry.1, entry.2.1)
      (concat_matrix_indexed_mem inputs entry he))

/-- Pointwise equality of column blocks preserves the corresponding complete concatenation. -/
theorem concat_matrix_flatMap_ext {α β : Type} (items : List α) (left right : α → List β)
    (he : ∀ item ∈ items, left item = right item) : items.flatMap left = items.flatMap right := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.flatMap_cons, he item List.mem_cons_self,
      ih (fun i hi => he i (List.mem_cons_of_mem item hi))]

/-- A source slice is exactly the frozen column-major row enumeration for that source. -/
theorem concat_matrix_slice_spec (entry : Nat × List Bool × Nat) (column columns : Nat)
    (hshape : entry.2.1.length = entry.1 * columns) (hc : column < columns) :
    concat_matrix_slice column entry =
      (List.range entry.1).map (fun row => entry.2.1.getD (row + column * entry.1) false) := by
  have hsource : column * entry.1 + entry.1 ≤ entry.2.1.length := by
    calc
      column * entry.1 + entry.1 = (column + 1) * entry.1 := by simp only [Nat.add_mul, Nat.one_mul]
      _ ≤ columns * entry.1 := Nat.mul_le_mul_right entry.1 (Nat.succ_le_of_lt hc)
      _ = entry.2.1.length := by rw [hshape, Nat.mul_comm]
  apply List.ext_getElem
  · rw [concat_matrix_slice_length entry column columns hshape hc, List.length_map, List.length_range]
  · intro row hleft hright
    have hr : row < entry.1 := by simpa only [List.length_map, List.length_range] using hright
    have hi : row + column * entry.1 < entry.2.1.length := by omega
    simp only [concat_matrix_slice, List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    congr 1
    omega

/-- Indexed source slices recover the frozen matrix-vcat expected logical output exactly. -/
theorem concat_matrix_indexed_expected (inputs : List (Nat × List Bool)) (columns : Nat)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns) :
    concat_matrix_bits (concat_matrix_indexed inputs) columns =
      (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) := by
  unfold concat_matrix_bits
  apply concat_matrix_flatMap_ext
  intro column hc
  have hcolumn : column < columns := List.mem_range.mp hc
  calc
    (concat_matrix_indexed inputs).flatMap (concat_matrix_slice column) =
        (concat_matrix_indexed inputs).flatMap (fun entry =>
          (List.range entry.1).map (fun row => entry.2.1.getD (row + column * entry.1) false)) := by
      apply concat_matrix_flatMap_ext
      intro entry he
      exact concat_matrix_slice_spec entry column columns
        (hshape (entry.1, entry.2.1) (concat_matrix_indexed_mem inputs entry he)) hcolumn
    _ = inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false)) := by
      have h := congrArg (fun items : List (Nat × List Bool) => items.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false)))
        (concat_matrix_indexed_inputs inputs)
      simpa only [List.flatMap_map] using h

/-- The concrete matrix source heap is the same initialMany heap used by the frozen statement. -/
theorem concat_matrix_initial_heap (inputs : List (Nat × List Bool)) :
    concat_initial (inputs.map Prod.snd) = MutableMemory.initialMany
      (inputs.map fun input => (encodeBits input.2).map some) := by
  simp only [concat_initial, List.map_map, Function.comp_def]

/-- The ready-source matrix theorem applies to every nonempty list, including zero-height components. -/
theorem concat_matrix_nonempty_correct (entries : List (Nat × List Bool × Nat))
    (columns : Nat) (s : State) (hne : entries ≠ [])
    (hcount : entries.length ≤ 9223372036854775807)
    (hshape : ∀ entry ∈ entries, entry.2.1.length = entry.1 * columns)
    (hsize : ∀ entry ∈ entries, entry.2.1.length ≤ 64)
    (hready : ∀ entry ∈ entries, concat_ready s entry.2)
    (hpos : 0 < columns * (entries.map Prod.fst).sum)
    (hbound : columns * (entries.map Prod.fst).sum ≤ 64) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices (entries.map (concat_matrix_entry columns))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        concat_allocate_matrix_fn).run s = (.ok out, finished) ∧
      out.dims = [int (entries.map Prod.fst).sum, int columns] ∧
      bitValues finished out = concat_matrix_bits entries columns ∧
      Round5.Round2.PackedInvariant finished out := by
  cases entries with
  | nil => exact False.elim (hne rfl)
  | cons first rest => exact concat_matrix_multi_correct first rest columns s hcount hshape hsize hready hpos hbound

/-- Every frozen variadic matrix-vcat instance with 1–64 output bits satisfies its full promised observations. -/
theorem concat_matrix_vcat_single_word_correct (columns : Nat) (inputs : List (Nat × List Bool))
    (hne : inputs ≠ []) (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hpos : 0 < columns * (inputs.foldl (fun rows input => rows + input.1) 0))
    (hbound : columns * (inputs.foldl (fun rows input => rows + input.1) 0) ≤ 64) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices
        ((inputs.zip (List.range inputs.length)).map (fun entry =>
          (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run
        (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some)) = (.ok out, finished) ∧
      out.dims = [int ((inputs.foldl (fun rows input => rows + input.1) 0 : Nat) : Int), int columns] ∧
      bitValues finished out = (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) ∧
      Round5.Round2.PackedInvariant finished out := by
  rw [← concat_matrix_rows_sum] at hpos hbound
  have hne' : concat_matrix_indexed inputs ≠ [] := by
    intro he
    have hl := concat_matrix_indexed_length inputs
    rw [he, List.length_nil] at hl
    exact hne (List.length_eq_zero_iff.mp hl.symm)
  have h := concat_matrix_nonempty_correct (concat_matrix_indexed inputs) columns
    (concat_initial (inputs.map Prod.snd)) hne'
    (by rw [concat_matrix_indexed_length]; exact hcount)
    (fun entry he => hshape (entry.1, entry.2.1) (concat_matrix_indexed_mem inputs entry he))
    (fun entry he => concat_matrix_input_size inputs columns hshape hbound
      (entry.1, entry.2.1) (concat_matrix_indexed_mem inputs entry he))
    (concat_matrix_indexed_ready inputs columns hshape hbound)
    (by rw [concat_matrix_indexed_rows]; exact hpos)
    (by rw [concat_matrix_indexed_rows]; exact hbound)
  rcases h with ⟨out, finished, hrun, hdims, hbits, hinv⟩
  refine ⟨out, finished, ?_, ?_, ?_, hinv⟩
  · rw [concat_matrix_initial_heap, concat_matrix_indexed_headers] at hrun
    exact hrun
  · rw [concat_matrix_indexed_rows, concat_matrix_rows_sum] at hdims
    exact hdims
  · rw [concat_matrix_indexed_expected inputs columns hshape] at hbits
    exact hbits


/-- A uniform list with the same fallback value has that value at every defaulted index. -/
theorem concat_getD_uniform {α : Type} (items : List α) (value : α) (index : Nat)
    (hall : ∀ item ∈ items, item = value) : items.getD index value = value := by
  induction items generalizing index with
  | nil => rfl
  | cons item items ih =>
    cases index with
    | zero => exact hall item List.mem_cons_self
    | succ index =>
      rw [List.getD_cons_succ]
      exact ih index (fun i hi => hall i (List.mem_cons_of_mem item hi))

/-- Replacing any entry in a constant cursor list by the same value leaves the list unchanged. -/
theorem concat_set_replicate_same {α : Type} (count : Nat) (value : α) (index : Nat) :
    (List.replicate count value).set index value = List.replicate count value := by
  induction count generalizing index with
  | zero => simp only [List.replicate_zero, List.set_nil]
  | succ count ih =>
    cases index with
    | zero => simp only [List.replicate_succ, List.set_cons_zero]
    | succ index => simp only [List.replicate_succ, List.set_cons_succ, ih]

/-- Every defaulted lookup in a replicated cursor list returns its common value. -/
theorem concat_getD_replicate_same {α : Type} (count : Nat) (value : α) (index : Nat) :
    (List.replicate count value).getD index value = value := by
  apply concat_getD_uniform
  intro item hi
  exact (List.mem_replicate.mp hi).2

/-- A zero-row inner matrix copy is an exact no-op on the heap and the constant source cursors. -/
theorem concat_matrix_zero_step (dest : Nat) (arrays : List BitMatrix) (heights : List I64)
    (fallback : BitMatrix) (index count : Nat) (position : I64) (s : State)
    (hz : heights.getD index (int 0) = int 0) :
    (concat_matrix_raw_step copyChunks dest arrays heights fallback index
      (position, List.replicate count (int 1))).run s =
      (.ok (ForInStep.yield (position, List.replicate count (int 1))), s) := by
  have h := concat_matrix_raw_from_copy copyChunks dest arrays heights fallback
    (arrays.getD index fallback) index position (int 1) (int 0) (List.replicate count (int 1)) s s
    rfl hz (concat_getD_replicate_same count (int 1) index)
    (concat_copy_zero dest (arrays.getD index fallback).chunks position (int 1) s)
  apply h.trans
  rw [concat_add_zero, concat_add_zero, concat_set_replicate_same]

/-- With no columns, the installed matrix copy phase immediately returns its initial cursors. -/
theorem concat_matrix_no_columns (arrays : List BitMatrix) (fallback : BitMatrix)
    (heights : List I64) (out : BitMatrix) (s : State) :
    (concat_matrix_copies copyChunks arrays fallback heights (int 0) out).run s =
      (.ok (int 1, List.replicate arrays.length (int 1)), s) := rfl

/-- With all row counts zero, both installed nested loops perform only no-op copies. -/
theorem concat_matrix_zero_rows (arrays : List BitMatrix) (fallback : BitMatrix)
    (heights : List I64) (columns : I64) (out : BitMatrix) (s : State)
    (hall : ∀ height ∈ heights, height = int 0) :
    (concat_matrix_copies copyChunks arrays fallback heights columns out).run s =
      (.ok (int 1, List.replicate arrays.length (int 1)), s) := by
  unfold concat_matrix_copies
  apply concat_forIn_unchanged
  intro column hc
  apply concat_yield_result
  apply concat_forIn_unchanged
  intro index hi
  exact concat_matrix_zero_step out.chunks arrays heights fallback (index.val.toNat - 1)
    arrays.length (int 1) s (concat_getD_uniform heights (int 0) (index.val.toNat - 1) hall)

/-- A zero total matrix size makes the installed copy phase a no-op in either the zero-column or zero-row case. -/
theorem concat_matrix_empty_copies (entries : List (Nat × List Bool × Nat)) (columns : Nat)
    (fallback out : BitMatrix) (s : State)
    (hz : (entries.map Prod.fst).sum * columns = 0) :
    (concat_matrix_copies copyChunks (entries.map (concat_matrix_entry columns)) fallback
      (entries.map fun entry => int entry.1) (int columns) out).run s =
      (.ok (int 1, List.replicate entries.length (int 1)), s) := by
  by_cases hc : columns = 0
  · subst columns
    have h := concat_matrix_no_columns (entries.map (concat_matrix_entry 0)) fallback
      (entries.map fun entry => int entry.1) out s
    simpa only [List.length_map, Int.ofNat_zero] using h
  · have hr : (entries.map Prod.fst).sum = 0 := (Nat.mul_eq_zero.mp hz).resolve_right hc
    let heights : List I64 := entries.map fun entry => int entry.1
    have hall : ∀ height ∈ heights, height = int 0 := by
      intro height hh
      obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hh
      have hb := concat_member_le_sum (entries.map Prod.fst) entry.1 (List.mem_map_of_mem (f := Prod.fst) he)
      have heq : entry.1 = 0 := by omega
      rw [heq]
      rfl
    have h := concat_matrix_zero_rows (entries.map (concat_matrix_entry columns)) fallback
      heights (int columns) out s hall
    simpa only [List.length_map] using h

/-- Empty matrix-vcat outputs preserve the exact representable shape, without reading any source chunks. -/
theorem concat_matrix_empty_ready (first : Nat × List Bool × Nat)
    (rest : List (Nat × List Bool × Nat)) (columns : Nat) (s : State)
    (hrows : ((first :: rest).map Prod.fst).sum ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hz : ((first :: rest).map Prod.fst).sum * columns = 0) :
    (bitArrayVcatMatrices ((first :: rest).map (concat_matrix_entry columns))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int 0,
        [int ((first :: rest).map Prod.fst).sum, int columns]⟩ : BitMatrix), concat_extend_empty s) := by
  let entries := first :: rest
  let rows := (entries.map Prod.fst).sum
  let arrays := entries.map (concat_matrix_entry columns)
  let head := concat_matrix_entry columns first
  let heights := entries.map fun entry => int entry.1
  let out : BitMatrix := ⟨s.arrays.length, int 0, [int rows, int columns]⟩
  have hscan : (concat_matrix_scan arrays
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int 0, [])).run s =
      (.ok (int rows, heights), s) := by
    have h := concat_matrix_scan_run entries columns 0 [] s
    simpa only [Int.zero_add, List.nil_append] using h
  have hvalidation : (concat_matrix_validation arrays head
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int columns)).run s = (.ok (), s) := by
    apply concat_matrix_validation_run
    intro index hi
    exact concat_matrix_lookup_columns entries first columns (index.val.toNat - 1)
  have hallocate : (concat_allocate_matrix_fn (int rows) (int columns)).run s =
      (.ok out, concat_extend_empty s) := concat_allocate_empty_matrix rows columns hrows hcols hz s
  have hcopy := concat_matrix_empty_copies entries columns head out (concat_extend_empty s) hz
  have hrun := concat_matrix_from_runs copyChunks arrays head
    (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
    concat_allocate_matrix_fn (int rows) heights s _ _ out _ hscan hvalidation hallocate hcopy
  change (concat_matrix_program copyChunks
      (concat_matrix_entry columns first :: rest.map (concat_matrix_entry columns))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      concat_allocate_matrix_fn).run s = _
  rw [concat_matrix_nonempty_factor]
  exact hrun


/-- The empty matrix execution theorem applies to every nonempty list of source headers. -/
theorem concat_matrix_empty_nonempty (entries : List (Nat × List Bool × Nat))
    (columns : Nat) (s : State) (hne : entries ≠ [])
    (hrows : (entries.map Prod.fst).sum ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807) (hz : (entries.map Prod.fst).sum * columns = 0) :
    (bitArrayVcatMatrices (entries.map (concat_matrix_entry columns))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      concat_allocate_matrix_fn).run s =
      (.ok (⟨s.arrays.length, int 0, [int (entries.map Prod.fst).sum, int columns]⟩ : BitMatrix),
        concat_extend_empty s) := by
  cases entries with
  | nil => exact False.elim (hne rfl)
  | cons first rest => exact concat_matrix_empty_ready first rest columns s hrows hcols hz

/-- Every well-shaped zero-size matrix concatenation has an empty expected logical output. -/
theorem concat_matrix_empty_expected (inputs : List (Nat × List Bool)) (columns : Nat)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hz : (inputs.map Prod.fst).sum * columns = 0) :
    (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
      (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) = [] := by
  rw [← concat_matrix_indexed_expected inputs columns hshape]
  apply List.length_eq_zero_iff.mp
  rw [concat_matrix_bits_length (concat_matrix_indexed inputs) columns columns
    (fun entry he => hshape (entry.1, entry.2.1) (concat_matrix_indexed_mem inputs entry he)) (Nat.le_refl _),
    concat_matrix_indexed_rows, Nat.mul_comm, hz]

/-- Frozen zero-output matrix-vcat preserves every representable zero-row or zero-column shape. -/
theorem concat_matrix_vcat_empty_correct (columns : Nat) (inputs : List (Nat × List Bool))
    (hne : inputs ≠ [])
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hz : inputs.foldl (fun rows input => rows + input.1) 0 * columns = 0) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices
        ((inputs.zip (List.range inputs.length)).map (fun entry =>
          (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run
        (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some)) = (.ok out, finished) ∧
      out.dims = [int ((inputs.foldl (fun rows input => rows + input.1) 0 : Nat) : Int), int columns] ∧
      bitValues finished out = (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) ∧
      Round5.Round2.PackedInvariant finished out := by
  let s := concat_initial (inputs.map Prod.snd)
  have hne' : concat_matrix_indexed inputs ≠ [] := by
    intro he
    have hl := concat_matrix_indexed_length inputs
    rw [he, List.length_nil] at hl
    exact hne (List.length_eq_zero_iff.mp hl.symm)
  have hrun := concat_matrix_empty_nonempty (concat_matrix_indexed inputs) columns s hne'
    (by rw [concat_matrix_indexed_rows, concat_matrix_rows_sum]; exact hrows) hcols
    (by rw [concat_matrix_indexed_rows, concat_matrix_rows_sum]; exact hz)
  have he : (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
      (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) = [] :=
    concat_matrix_empty_expected inputs columns hshape (by rw [concat_matrix_rows_sum]; exact hz)
  refine ⟨⟨s.arrays.length, int 0, [int ((concat_matrix_indexed inputs).map Prod.fst).sum, int columns]⟩,
    concat_extend_empty s, ?_, ?_, ?_, concat_empty_invariant s _⟩
  · change (bitArrayVcatMatrices _ _ _).run (concat_initial (inputs.map Prod.snd)) = _ at hrun
    rw [concat_matrix_initial_heap, concat_matrix_indexed_headers] at hrun
    exact hrun
  · rw [concat_matrix_indexed_rows, concat_matrix_rows_sum]
  · rw [concat_empty_bitValues, he]

/-- All nonempty frozen matrix-vcat inputs with representable dimensions and at most 64 output bits satisfy the full contract. -/
theorem concat_matrix_vcat_small_correct (columns : Nat) (inputs : List (Nat × List Bool))
    (hne : inputs ≠ []) (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 64) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices
        ((inputs.zip (List.range inputs.length)).map (fun entry =>
          (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run
        (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some)) = (.ok out, finished) ∧
      out.dims = [int ((inputs.foldl (fun rows input => rows + input.1) 0 : Nat) : Int), int columns] ∧
      bitValues finished out = (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) ∧
      Round5.Round2.PackedInvariant finished out := by
  by_cases hz : inputs.foldl (fun rows input => rows + input.1) 0 * columns = 0
  · exact concat_matrix_vcat_empty_correct columns inputs hne hshape hrows hcols hz
  · have hp : 0 < columns * inputs.foldl (fun rows input => rows + input.1) 0 := by
      rw [Nat.mul_comm]
      omega
    exact concat_matrix_vcat_single_word_correct columns inputs hne hcount hshape hp
      (by rw [Nat.mul_comm]; exact hbound)


/-- A successful run transports any output/heap observation to the frozen match-on-result formulation. -/
theorem concat_success_observation {α : Type} (result : Except JuliaLean.base.array.Error α × State)
    (out : α) (finished : State) (observation : State → α → Prop)
    (hrun : result = (.ok out, finished)) (hobs : observation finished out) :
    (match result.1 with | .ok value => observation result.2 value | .error _ => False) := by
  rw [hrun]
  exact hobs

/-- The exact frozen matrix-vcat observations hold throughout the supported total-size range 0–64. -/
theorem concat_frozen_matrix_contract_small (columns : Nat) (inputs : List (Nat × List Bool))
    (hne : inputs ≠ []) (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 64) :
    let arrays : List BitMatrix := (inputs.zip (List.range inputs.length)).map fun entry =>
      ⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩
    let state := MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some)
    let result := (bitArrayVcatMatrices arrays
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      Round5.Round2.allocateMatrixModel).run state
    match result.1 with
    | .ok output =>
      output.dims = [int ((inputs.foldl (fun rows input => rows + input.1) 0 : Nat) : Int), int columns] ∧
      bitValues result.2 output = (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) ∧
      Round5.Round2.PackedInvariant result.2 output
    | .error _ => False := by
  dsimp only
  obtain ⟨out, finished, hrun, hdims, hbits, hinv⟩ :=
    concat_matrix_vcat_small_correct columns inputs hne hcount hshape hrows hcols hbound
  rw [hrun]
  exact ⟨hdims, hbits, hinv⟩

/-- At zero source offset, glue reads only the first source word regardless of the ending chunk. -/
theorem concat_glue_first (source : Nat) (last : I64) (mask word : U64) (s : State)
    (hread : (mutableGet source (int 1)).run s = (.ok word, s)) :
    (glueSrcBitChunks source (int 1) last mask (int 0)).run s = (.ok (and_int word mask), s) := by
  have hzero : ¬ (int 0 : I64) > int 0 := by decide
  simp only [glueSrcBitChunks, shape_run_bind, hread, hzero, and_false, ite_false,
    concat_lshr_zero, shape_run_pure]

/-- The frozen copy operation reads its first destination chunk before writing, even for word-aligned copies. -/
theorem concat_copy_first_undefined (dest source : Nat) (count : I64) (word : U64) (s : State)
    (hnonzero : count ≠ int 0)
    (hsource : (mutableGet source (int 1)).run s = (.ok word, s))
    (hdest : (mutableGet dest (int 1)).run s = (.error .undefinedReference, s)) :
    (copyChunks dest (int 1) source (int 1) count).run s = (.error .undefinedReference, s) := by
  have hn : (count == int 0) = false := beq_eq_false_iff_ne.mpr hnonzero
  have hsame : ¬ (dest = source ∧ (int 1 : I64) > int 1) := by
    intro h
    exact (by decide : ¬ (int 1 : I64) > int 1) h.2
  have hstart : getChunksId (int 1) = (int 1, int 0) := rfl
  by_cases hd : ((getChunksId (int 1 + count - int 1)).1 - int 1 == int 0) = true
  all_goals simp only [copyChunks, hn, Bool.false_eq_true, hsame, hstart, dite_false,
    hd, ite_true, ite_false, shape_run_bind, shape_run_pure,
    concat_glue_first source _ _ word s hsource, hdest]

/-- A valid header whose first slot is unassigned raises precisely undefinedReference. -/
theorem concat_read_first_undefined (s : State) (handle mem : Nat) (length : I64)
    (slots : List (Option U64))
    (ha : s.arrays[handle]? = some ⟨(mem, one), length⟩)
    (hm : s.memories[mem]? = some slots) (hlen : 1 ≤ length.val)
    (hfirst : slots[0]? = some none) :
    (mutableGet handle (int 1)).run s = (.error .undefinedReference, s) := by
  have hb : 1 ≤ (int 1).val ∧ int 1 ≤ length := ⟨by decide, hlen⟩
  simp only [mutableGet, mutableVector, memoryRead, shape_run_bind, shape_run_get,
    ha, hm, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
  have haddress : (one.val + (int 1).val - 2).toNat = 0 := by decide
  rw [haddress, hfirst]
  rfl

/-- In any allocation of at least two chunks, initializing only the last leaves the first destination read undefined. -/
theorem concat_new_first_undefined (count : Nat) (hp : 1 < count) (hc : count ≤ 9223372036854775807)
    (s : State) :
    (mutableGet s.arrays.length (int 1)).run
      (concat_new_chunks s count ((List.replicate count none).set (count - 1) (some (u64 0)))) =
      (.error .undefinedReference,
        concat_new_chunks s count ((List.replicate count none).set (count - 1) (some (u64 0)))) := by
  apply concat_read_first_undefined _ s.arrays.length s.memories.length (int count) _
    (concat_new_chunks_header s count _) (concat_new_chunks_memory s count _)
    (by rw [packedInt_val count hc]; omega)
  rw [List.getElem?_set_ne (by omega : count - 1 ≠ 0), List.getElem?_replicate]
  simp only [show 0 < count by omega, ite_true]

/-- A positive constructor factors through arbitrary chunk counts and one final-chunk initialization. -/
theorem concat_construct_general {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (n : I64) (count : Nat) (s allocated initialized : State) (handle : Nat)
    (hneg : ¬ n.val < 0) (hchecked : (checked [n]).run s = (.ok n, s))
    (hcount : numBitChunks n = int count) (hp : 0 < count) (hc : count ≤ 9223372036854775807)
    (hallocate : (allocate count).run s = (.ok handle, allocated))
    (hwrite : (mutableSet handle (u64 0) (int count)).run allocated = (.ok (), initialized)) :
    (BitArrayUndef (N := N) checked allocate [n]).run s =
      (.ok ⟨handle, n, [n]⟩, initialized) := by
  have hnat : (int count).val.toNat = count := by rw [packedInt_val count hc, Int.toNat_natCast]
  have hpos : (int count).val > 0 := by rw [packedInt_val count hc]; omega
  simp only [BitArrayUndef, List.forIn_cons, List.forIn_nil, hneg, ite_false,
    shape_run_bind, shape_run_pure, hchecked, hcount, hnat, hallocate, hpos, ite_true, hwrite]

/-- Public vector allocation initializes just the final chunk, for every positive representable length. -/
theorem concat_allocate_vector_general (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) (s : State) :
    (concat_allocate_vector (int n)).run s =
      (.ok (⟨s.arrays.length, int n, [int n]⟩ : BitVector),
        concat_new_chunks s (wordCount n)
          ((List.replicate (wordCount n) none).set (wordCount n - 1) (some (u64 0)))) := by
  have hc : wordCount n ≤ 576460752303423488 := by unfold wordCount; omega
  have hpos : 0 < wordCount n := by unfold wordCount; omega
  exact concat_construct_general checkedDimensionsModel allocateChunkVectorModel (int n) (wordCount n)
    s _ _ s.arrays.length (by rw [packedInt_val n hn]; omega)
    (concat_checked_dims_general (int n) s) (concat_num_chunks_general n hn) hpos (by omega)
    (concat_allocate_chunks_general (wordCount n) hc s) (concat_initialize_last (wordCount n) hpos (by omega) s)

/-- The first packed chunk exists for every nonempty logical source, with no one-word restriction. -/
theorem concat_encoded_first (xs : List Bool) (hp : 0 < xs.length) :
    (encodeBits xs)[0]? = some (packedPrefix xs 0 64) := by
  have hc : 0 < (List.range (wordCount xs.length)).length := by
    rw [List.length_range]
    unfold wordCount
    omega
  rw [packedPrefix_eq_encode, List.getElem?_map, List.getElem?_eq_getElem hc,
    List.getElem_range, Option.map_some]

/-- A known assigned first slot can be observed without restricting the rest of its backing memory. -/
theorem concat_read_first_known (s : State) (handle mem : Nat) (length : I64)
    (slots : List (Option U64)) (word : U64)
    (ha : s.arrays[handle]? = some ⟨(mem, one), length⟩)
    (hm : s.memories[mem]? = some slots) (hlen : 1 ≤ length.val)
    (hfirst : slots[0]? = some (some word)) :
    (mutableGet handle (int 1)).run s = (.ok word, s) := by
  have hb : 1 ≤ (int 1).val ∧ int 1 ≤ length := ⟨by decide, hlen⟩
  simp only [mutableGet, mutableVector, memoryRead, shape_run_bind, shape_run_get,
    ha, hm, shape_run_pure, hb, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
  have haddress : (one.val + (int 1).val - 2).toNat = 0 := by decide
  rw [haddress, hfirst]
  rfl

/-- Every nonempty frozen source retains its initialized first word after arbitrary independent chunk allocation. -/
theorem concat_initial_first_after_new (vectors : List (List Bool)) (entry : List Bool × Nat)
    (he : entry ∈ vectors.zipIdx) (count : Nat) (slots : List (Option U64))
    (hp : 0 < entry.1.length) (hb : entry.1.length ≤ 9223372036854775807) :
    (mutableGet entry.2 (int 1)).run (concat_new_chunks (concat_initial vectors) count slots) =
      (.ok (packedPrefix entry.1 0 64), concat_new_chunks (concat_initial vectors) count slots) := by
  have hi : entry.2 < vectors.length := by
    have h := List.snd_lt_of_mem_zipIdx he
    simpa only [Nat.add_zero] using h
  have hh := concat_initial_header vectors entry he
  have hm := concat_initial_memory vectors entry he
  have hl := concat_initial_lengths vectors
  have hc : 0 < (encodeBits entry.1).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hn : (encodeBits entry.1).length ≤ 9223372036854775807 := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  apply concat_read_first_known _ entry.2 entry.2 (int (encodeBits entry.1).length)
    ((encodeBits entry.1).map some ++ List.replicate 32 none) (packedPrefix entry.1 0 64)
  · simpa only [concat_new_chunks, List.getElem?_append_left (show entry.2 < (concat_initial vectors).arrays.length by
      rw [hl.1]; exact hi)] using hh
  · simpa only [concat_new_chunks, List.getElem?_append_left (show entry.2 < (concat_initial vectors).memories.length by
      rw [hl.2]; exact hi)] using hm
  · rw [packedInt_val (encodeBits entry.1).length hn]
    omega
  · rw [List.getElem?_append_left (show 0 < ((encodeBits entry.1).map some).length by
      simpa only [List.length_map] using hc), List.getElem?_map, concat_encoded_first entry.1 hp]
    rfl

/-- A positive representable natural count remains nonzero after conversion to the native length type. -/
theorem concat_native_nonzero (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807) : int n ≠ int 0 := by
  intro he
  have hv := congrArg Subtype.val he
  rw [packedInt_val n hn] at hv
  change (n : Int) = 0 at hv
  omega

/-- The first nonempty source in a vcat copy pass triggers the first-destination undefined read. -/
theorem concat_vcat_copy_error (vectors : List BitVector) (dest : Nat) (s : State)
    (hdest : (mutableGet dest (int 1)).run s = (.error .undefinedReference, s))
    (hsource : ∀ vector ∈ vectors, vector.len ≠ int 0 → ∃ word,
      (mutableGet vector.chunks (int 1)).run s = (.ok word, s))
    (hpositive : ∃ vector ∈ vectors, vector.len ≠ int 0) :
    (forIn vectors (int 1) (fun (vector : BitVector) (position : I64) => do
      copyChunks dest position vector.chunks (int 1) vector.len
      pure (ForInStep.yield (position + vector.len)))).run s = (.error .undefinedReference, s) := by
  induction vectors with
  | nil => obtain ⟨vector, hv, _⟩ := hpositive; cases hv
  | cons vector vectors ih =>
    by_cases hz : vector.len = int 0
    · have ht : ∃ v ∈ vectors, v.len ≠ int 0 := by
        obtain ⟨v, hv, hn⟩ := hpositive
        rcases List.mem_cons.mp hv with he | hm
        · subst v
          exact False.elim (hn hz)
        · exact ⟨v, hm, hn⟩
      have htail := ih (fun v hv => hsource v (List.mem_cons_of_mem vector hv)) ht
      simp only [List.forIn_cons, shape_run_bind, hz, concat_copy_zero, concat_add_zero, shape_run_pure]
      exact htail
    · obtain ⟨word, hread⟩ := hsource vector List.mem_cons_self hz
      have hcopy := concat_copy_first_undefined dest vector.chunks vector.len word s hz hread hdest
      simp only [List.forIn_cons, shape_run_bind, hcopy]

/-- A failing vcat copy pass propagates its error and the exact allocation heap. -/
theorem concat_vcat_error_from_runs (vectors : List BitVector)
    (allocate : I64 → BitMutationM BitVector) (s allocated : State) (length : I64) (out : BitVector)
    (hsum : (forIn vectors (int 0) (fun (v : BitVector) (n : I64) =>
      (pure (ForInStep.yield (n + v.len)) : BitMutationM (ForInStep I64)))).run s = (.ok length, s))
    (hallocate : (allocate length).run s = (.ok out, allocated))
    (hcopy : (forIn vectors (int 1) (fun (v : BitVector) (position : I64) => do
      copyChunks out.chunks position v.chunks (int 1) v.len
      pure (ForInStep.yield (position + v.len)))).run allocated = (.error .undefinedReference, allocated)) :
    (concat_vcat_program copyChunks vectors allocate).run s = (.error .undefinedReference, allocated) := by
  simp only [concat_vcat_program, shape_run_bind, hsum, hallocate, hcopy]

/-- Every nonempty flattened list contains a component with at least one logical bit. -/
theorem concat_positive_component (vectors : List (List Bool)) (hp : 0 < vectors.flatten.length) :
    ∃ xs ∈ vectors, 0 < xs.length := by
  apply Classical.byContradiction
  intro h
  have hall : ∀ xs ∈ vectors, xs = [] := by
    intro xs hx
    apply List.length_eq_zero_iff.mp
    apply Classical.byContradiction
    intro hn
    exact h ⟨xs, hx, by omega⟩
  have he := List.flatten_eq_nil_iff.mpr hall
  rw [he, List.length_nil] at hp
  omega

/-- Every frozen vector-vcat input with more than one word of output fails at the fresh first destination chunk. -/
theorem concat_vcat_large_model_error (vectors : List (List Bool))
    (hlarge : 64 < vectors.flatten.length) (hbound : vectors.flatten.length ≤ 9223372036854775807) :
    (bitArrayVcatVectors
      ((vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
      (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors) =
      (.error .undefinedReference,
        concat_new_chunks (concat_initial vectors) (wordCount vectors.flatten.length)
          ((List.replicate (wordCount vectors.flatten.length) none).set
            (wordCount vectors.flatten.length - 1) (some (u64 0)))) := by
  let initial := concat_initial vectors
  let count := wordCount vectors.flatten.length
  let slots := (List.replicate count none).set (count - 1) (some (u64 0))
  let finished := concat_new_chunks initial count slots
  have hc : 1 < count := by dsimp only [count]; unfold wordCount; omega
  have hcmax : count ≤ 9223372036854775807 := by dsimp only [count]; unfold wordCount; omega
  have hdest := concat_new_first_undefined count hc hcmax initial
  have hsource : ∀ vector ∈ vectors.zipIdx.map concat_vector, vector.len ≠ int 0 → ∃ word,
      (mutableGet vector.chunks (int 1)).run finished = (.ok word, finished) := by
    intro vector hv hn
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hv
    have hp : 0 < entry.1.length := by
      apply Classical.byContradiction
      intro hz
      have hzero : entry.1.length = 0 := by omega
      apply hn
      rw [concat_vector_len, hzero]
      rfl
    have hb := Nat.le_trans (concat_component_length vectors entry.1 (List.fst_mem_of_mem_zipIdx he)) hbound
    exact ⟨packedPrefix entry.1 0 64, concat_initial_first_after_new vectors entry he count slots hp hb⟩
  have hpositive : ∃ vector ∈ vectors.zipIdx.map concat_vector, vector.len ≠ int 0 := by
    obtain ⟨xs, hxs, hp⟩ := concat_positive_component vectors (by omega)
    have hm : xs ∈ vectors.zipIdx.map Prod.fst := by rw [List.zipIdx_map_fst]; exact hxs
    obtain ⟨entry, he, heq⟩ := List.mem_map.mp hm
    refine ⟨concat_vector entry, List.mem_map_of_mem he, ?_⟩
    rw [concat_vector_len]
    exact concat_native_nonzero entry.1.length (by rw [heq]; exact hp)
      (Nat.le_trans (concat_component_length vectors entry.1 (List.fst_mem_of_mem_zipIdx he)) hbound)
  have hcopy := concat_vcat_copy_error (vectors.zipIdx.map concat_vector) initial.arrays.length finished
    hdest hsource hpositive
  have hsum := concat_sum_loop vectors.zipIdx 0 initial
  rw [concat_indexed_bits] at hsum
  simp only [Int.zero_add] at hsum
  have hallocate := concat_allocate_vector_general vectors.flatten.length (by omega) hbound initial
  have hrun := concat_vcat_error_from_runs (vectors.zipIdx.map concat_vector) concat_allocate_vector initial finished
    (int vectors.flatten.length) _ hsum hallocate hcopy
  rw [concat_indexed_handles] at hrun
  exact hrun

/-- Every positive representable matrix allocation initializes only the final chunk. -/
theorem concat_allocate_matrix_general (rows cols : Nat)
    (hr : rows ≤ 9223372036854775807) (hc : cols ≤ 9223372036854775807)
    (hp : 0 < rows * cols) (hn : rows * cols ≤ 9223372036854775807) (s : State) :
    (concat_allocate_matrix_fn (int rows) (int cols)).run s =
      (.ok (⟨s.arrays.length, int ((rows * cols : Nat) : Int), [int rows, int cols]⟩ : BitMatrix),
        concat_new_chunks s (wordCount (rows * cols))
          ((List.replicate (wordCount (rows * cols)) none).set (wordCount (rows * cols) - 1) (some (u64 0)))) := by
  have hcount : wordCount (rows * cols) ≤ 576460752303423488 := by unfold wordCount; omega
  have hpos : 0 < wordCount (rows * cols) := by unfold wordCount; omega
  exact concat_construct_pair_general checkedDimensionsModel allocateChunkVectorModel
    (int rows) (int cols) (int ((rows * cols : Nat) : Int)) (wordCount (rows * cols)) s _ _ s.arrays.length
    (by rw [packedInt_val rows hr]; omega) (by rw [packedInt_val cols hc]; omega)
    (concat_checked_pair_general rows cols hr hc hn s) (concat_num_chunks_general (rows * cols) hn)
    hpos (by omega) (concat_allocate_chunks_general (wordCount (rows * cols)) hcount s)
    (concat_initialize_last (wordCount (rows * cols)) hpos (by omega) s)

/-- The first nonempty hcat column encounters the undefined first destination chunk immediately. -/
theorem concat_hcat_copy_error (first : BitVector) (rest : List BitVector) (out : BitMatrix)
    (word : U64) (s : State) (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hpositive : first.len ≠ int 0)
    (hsource : (mutableGet first.chunks (int 1)).run s = (.ok word, s))
    (hdest : (mutableGet out.chunks (int 1)).run s = (.error .undefinedReference, s)) :
    (concat_hcat_copy copyChunks (first :: rest) first out).run s = (.error .undefinedReference, s) := by
  have hcopy := concat_copy_first_undefined out.chunks first.chunks first.len word s hpositive hsource hdest
  unfold concat_hcat_copy
  rw [packedObserve_intRange (first :: rest).length hcount]
  simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.zero_add, Int.ofNat_one,
    List.forIn_cons, shape_run_bind,
    show (int 1).val.toNat - 1 = 0 from rfl, List.getD_cons_zero, hcopy]

/-- An error in the copy phase propagates through successful validation and allocation. -/
theorem concat_three_stage_error {α β : Type} (validation : BitMutationM Unit)
    (allocate : BitMutationM α) (copy : α → BitMutationM β) (s allocated : State) (out : α)
    (hvalidation : validation.run s = (.ok (), s))
    (hallocate : allocate.run s = (.ok out, allocated))
    (hcopy : (copy out).run allocated = (.error .undefinedReference, allocated)) :
    ((do validation; let out ← allocate; let _ ← copy out; pure out) : BitMutationM α).run s =
      (.error .undefinedReference, allocated) := by
  simp only [shape_run_bind, hvalidation, hallocate, hcopy]

/-- A failed horizontal copy propagates its error after successful validation and allocation. -/
theorem concat_hcat_error_from_runs (vectors : List BitVector) (first : BitVector)
    (allocate : I64 → I64 → BitMutationM BitMatrix) (s allocated : State) (out : BitMatrix)
    (hvalidation : (concat_hcat_validation vectors first).run s = (.ok (), s))
    (hallocate : (allocate first.len (int vectors.length)).run s = (.ok out, allocated))
    (hcopy : (concat_hcat_copy copyChunks vectors first out).run allocated = (.error .undefinedReference, allocated)) :
    (concat_hcat_body copyChunks vectors first allocate).run s = (.error .undefinedReference, allocated) := by
  exact concat_three_stage_error (concat_hcat_validation vectors first)
    (allocate first.len (int vectors.length)) (concat_hcat_copy copyChunks vectors first)
    s allocated out hvalidation hallocate hcopy

/-- Every rectangular frozen hcat input with more than 64 output bits fails at its fresh first destination chunk. -/
theorem concat_hcat_large_model_error (vectors : List (List Bool))
    (hlarge : 64 < vectors.flatten.length) (hbound : vectors.flatten.length ≤ 9223372036854775807)
    (hall : ∀ xs ∈ vectors, xs.length = (vectors.headD []).length) :
    ((bitArrayHcatVectors
      ((vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
      (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors)).1 =
      .error .undefinedReference := by
  cases vectors with
  | nil => simp only [List.flatten_nil, List.length_nil] at hlarge; omega
  | cons first rest =>
    let vectors := first :: rest
    let initial := concat_initial vectors
    let headers := vectors.zipIdx.map concat_vector
    let head := concat_vector (first, 0)
    let count := wordCount vectors.flatten.length
    let slots := (List.replicate count none).set (count - 1) (some (u64 0))
    let finished := concat_new_chunks initial count slots
    let out : BitMatrix := ⟨initial.arrays.length, int vectors.flatten.length, [int first.length, int vectors.length]⟩
    change 64 < vectors.flatten.length at hlarge
    change vectors.flatten.length ≤ 9223372036854775807 at hbound
    have hrect : vectors.flatten.length = first.length * vectors.length :=
      concat_rectangular_length vectors first.length hall
    have hrpos : 0 < first.length := by
      by_cases hz : first.length = 0
      · rw [hrect, hz, Nat.zero_mul] at hlarge
        omega
      · omega
    have hr : first.length ≤ 9223372036854775807 :=
      Nat.le_trans (concat_component_length vectors first List.mem_cons_self) hbound
    have hc : vectors.length ≤ 9223372036854775807 := by
      have hm := Nat.mul_le_mul_right vectors.length (show 1 ≤ first.length by omega)
      simp only [Nat.one_mul] at hm
      omega
    have hhead : head.len ≠ int 0 := concat_native_nonzero first.length hrpos hr
    have hheaderCount : headers.length = vectors.length := by simp only [headers, List.length_map, List.length_zipIdx]
    have hfirst : (first, 0) ∈ vectors.zipIdx := by
      change (first, 0) ∈ (first, 0) :: rest.zipIdx 1
      exact List.mem_cons_self
    have hsource := concat_initial_first_after_new vectors (first, 0) hfirst count slots hrpos hr
    have hdest := concat_new_first_undefined count
      (by dsimp only [count]; unfold wordCount; omega)
      (by dsimp only [count]; unfold wordCount; omega) initial
    have hallHeaders : ∀ header ∈ headers, header.len = head.len := by
      intro header hh
      obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hh
      rw [concat_vector_len, hall entry.1 (List.fst_mem_of_mem_zipIdx he)]
      rfl
    have hvalidation : (concat_hcat_validation headers head).run initial = (.ok (), initial) := by
      apply concat_validate_heights
      intro index hi
      exact concat_getD_length headers head head.len hallHeaders rfl (index.val.toNat - 1)
    have halloc := concat_allocate_matrix_general first.length vectors.length hr hc
      (by rw [← hrect]; omega) (by rw [← hrect]; exact hbound) initial
    rw [← hrect] at halloc
    have hallocate : (concat_allocate_matrix_fn head.len (int headers.length)).run initial =
        (.ok out, finished) := by
      rw [hheaderCount]
      exact halloc
    have hcopy := concat_hcat_copy_error head ((rest.zipIdx 1).map concat_vector) out
      (packedPrefix first 0 64) finished
      (by simpa only [vectors, List.length_cons, List.length_map, List.length_zipIdx] using hc)
      hhead hsource hdest
    have hbody := concat_hcat_error_from_runs headers head concat_allocate_matrix_fn initial finished out
      hvalidation hallocate hcopy
    have hrun : (bitArrayHcatVectors headers concat_allocate_matrix_fn).run initial =
        (.error .undefinedReference, finished) := by
      change (concat_hcat_program copyChunks (head :: (rest.zipIdx 1).map concat_vector)
        concat_allocate_matrix_fn).run initial = _
      rw [concat_hcat_nonempty_factor]
      exact hbody
    dsimp only [headers] at hrun
    rw [concat_indexed_handles] at hrun
    exact congrArg Prod.fst hrun


/-- A loop whose steps either do nothing or raise the same error fails whenever one visited step raises it. -/
theorem concat_forIn_error {α β : Type} (items : List α) (value : β)
    (step : α → β → BitMutationM (ForInStep β)) (s : State)
    (hall : ∀ item ∈ items,
      (step item value).run s = (.ok (ForInStep.yield value), s) ∨
      (step item value).run s = (.error .undefinedReference, s))
    (hbad : ∃ item ∈ items, (step item value).run s = (.error .undefinedReference, s)) :
    (forIn items value step).run s = (.error .undefinedReference, s) := by
  induction items with
  | nil => obtain ⟨item, hi, _⟩ := hbad; cases hi
  | cons item items ih =>
    rcases hall item List.mem_cons_self with hgood | herror
    · have ht : ∃ i ∈ items, (step i value).run s = (.error .undefinedReference, s) := by
        obtain ⟨i, hi, he⟩ := hbad
        rcases List.mem_cons.mp hi with heq | hmem
        · subst i
          rw [hgood] at he
          cases he
        · exact ⟨i, hmem, he⟩
      simp only [List.forIn_cons, shape_run_bind, hgood]
      exact ih (fun i hi => hall i (List.mem_cons_of_mem item hi)) ht
    · simp only [List.forIn_cons, shape_run_bind, herror]

/-- Failure of the source's one copy prevents the inner matrix step from modifying either cursor. -/
theorem concat_matrix_raw_error_from_copy (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dest source : Nat) (arrays : List BitMatrix) (heights : List I64) (fallback A : BitMatrix)
    (index : Nat) (position sourcePos rows : I64) (cursors : List I64) (s : State)
    (ha : arrays.getD index fallback = A) (hr : heights.getD index (int 0) = rows)
    (hs : cursors.getD index (int 1) = sourcePos) (hchunks : A.chunks = source)
    (hcopy : (copy dest position source sourcePos rows).run s = (.error .undefinedReference, s)) :
    (concat_matrix_raw_step copy dest arrays heights fallback index (position, cursors)).run s =
      (.error .undefinedReference, s) := by
  simp only [concat_matrix_raw_step, ha, hr, hs, hchunks, shape_run_bind, hcopy]

/-- A positive total row count contains a source matrix with positive height. -/
theorem concat_positive_row (entries : List (Nat × List Bool × Nat))
    (hp : 0 < (entries.map Prod.fst).sum) : ∃ entry ∈ entries, 0 < entry.1 := by
  induction entries with
  | nil => simp only [List.map_nil, List.sum_nil] at hp; omega
  | cons entry entries ih =>
    by_cases he : 0 < entry.1
    · exact ⟨entry, List.mem_cons_self, he⟩
    · have ht : 0 < (entries.map Prod.fst).sum := by
        simp only [List.map_cons, List.sum_cons] at hp
        omega
      obtain ⟨e, hm, he⟩ := ih ht
      exact ⟨e, List.mem_cons_of_mem entry hm, he⟩

/-- Reading a matrix source header recovers its original assigned handle. -/
theorem concat_matrix_entry_chunks (columns : Nat) (entry : Nat × List Bool × Nat) :
    (concat_matrix_entry columns entry).chunks = entry.2.2 := rfl

/-- Indexed matrix-step errors depend only on the selected source copy, uniformly in the copy implementation. -/
theorem concat_matrix_index_error_from_copy (copy : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (entries : List (Nat × List Bool × Nat)) (columns dest : Nat) (fallback : BitMatrix)
    (index : Nat) (hi : index < entries.length) (s : State)
    (hcopy : (copy dest (int 1) (entries[index]).2.2 (int 1) (int (entries[index]).1)).run s =
      (.error .undefinedReference, s)) :
    (concat_matrix_raw_step copy dest (entries.map (concat_matrix_entry columns))
      (entries.map fun entry => int entry.1) fallback index
      (int 1, List.replicate entries.length (int 1))).run s = (.error .undefinedReference, s) := by
  simp only [concat_matrix_raw_step,
    concat_getD_map_index entries (concat_matrix_entry columns) fallback index hi,
    concat_getD_map_index entries (fun entry => int entry.1) (int 0) index hi,
    concat_getD_replicate_same entries.length (int 1) index,
    concat_matrix_entry_chunks, shape_run_bind, hcopy]

/-- The first positive-row source in the first matrix output column hits the undefined destination word. -/
theorem concat_matrix_inner_error (entries : List (Nat × List Bool × Nat))
    (columns dest : Nat) (fallback : BitMatrix) (s : State)
    (hrows : ∀ entry ∈ entries, entry.1 ≤ 9223372036854775807)
    (hpositive : 0 < (entries.map Prod.fst).sum)
    (hsource : ∀ entry ∈ entries, 0 < entry.1 → ∃ word,
      (mutableGet entry.2.2 (int 1)).run s = (.ok word, s))
    (hdest : (mutableGet dest (int 1)).run s = (.error .undefinedReference, s)) :
    (forIn (List.range entries.length) (int 1, List.replicate entries.length (int 1))
      (concat_matrix_raw_step copyChunks dest (entries.map (concat_matrix_entry columns))
        (entries.map fun entry => int entry.1) fallback)).run s = (.error .undefinedReference, s) := by
  let step := concat_matrix_raw_step copyChunks dest (entries.map (concat_matrix_entry columns))
    (entries.map fun entry => int entry.1) fallback
  let registers := (int 1, List.replicate entries.length (int 1))
  have herror (index : Nat) (hi : index < entries.length) (hp : 0 < (entries[index]).1) :
      (step index registers).run s = (.error .undefinedReference, s) := by
    let entry := entries[index]
    have he : entry ∈ entries := List.getElem_mem hi
    obtain ⟨word, hread⟩ := hsource entry he hp
    have hcopy := concat_copy_first_undefined dest entry.2.2 (int entry.1) word s
      (concat_native_nonzero entry.1 hp (hrows entry he)) hread hdest
    exact concat_matrix_index_error_from_copy copyChunks entries columns dest fallback index hi s hcopy
  have hall (index : Nat) (hi : index ∈ List.range entries.length) :
      (step index registers).run s = (.ok (ForInStep.yield registers), s) ∨
        (step index registers).run s = (.error .undefinedReference, s) := by
    have hb : index < entries.length := List.mem_range.mp hi
    by_cases hp : 0 < (entries[index]).1
    · exact Or.inr (herror index hb hp)
    · apply Or.inl
      apply concat_matrix_zero_step
      rw [concat_getD_map_index entries (fun entry => int entry.1) (int 0) index hb,
        show (entries[index]).1 = 0 by omega]
      rfl
  have hbad : ∃ index ∈ List.range entries.length,
      (step index registers).run s = (.error .undefinedReference, s) := by
    obtain ⟨entry, he, hp⟩ := concat_positive_row entries hpositive
    obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp he
    exact ⟨index, List.mem_range.mpr hi, herror index hi (by rw [heq]; exact hp)⟩
  exact concat_forIn_error (List.range entries.length) registers step s hall hbad

/-- An error in the first native output column propagates through the entire matrix copy phase. -/
theorem concat_matrix_copies_error (arrays : List BitMatrix) (fallback : BitMatrix)
    (heights : List I64) (columns : Nat) (out : BitMatrix) (s : State)
    (hcount : arrays.length ≤ 9223372036854775807)
    (hp : 0 < columns) (hc : columns ≤ 9223372036854775807)
    (hinner : (forIn (List.range arrays.length) (int 1, List.replicate arrays.length (int 1))
      (concat_matrix_raw_step copyChunks out.chunks arrays heights fallback)).run s = (.error .undefinedReference, s)) :
    (concat_matrix_copies copyChunks arrays fallback heights (int columns) out).run s =
      (.error .undefinedReference, s) := by
  have hstep : (concat_matrix_outer_step copyChunks out.chunks arrays heights fallback
      (int 1, List.replicate arrays.length (int 1))).run s = (.error .undefinedReference, s) := by
    simp only [concat_matrix_outer_step, shape_run_bind, hinner]
  rw [concat_matrix_copies_factor copyChunks arrays fallback heights (int columns) out hcount]
  cases columns with
  | zero => omega
  | succ columns =>
    rw [packedObserve_intRange (columns + 1) hc, List.range_succ_eq_map]
    simp only [List.map_cons, List.forIn_cons, shape_run_bind, hstep]

/-- A successful first phase followed by a failed continuation preserves that continuation's exact error state. -/
theorem concat_bind_error {α β : Type} (action : BitMutationM α)
    (continuation : α → BitMutationM β) (s middle finished : State) (value : α)
    (hfirst : action.run s = (.ok value, middle))
    (hsecond : (continuation value).run middle = (.error .undefinedReference, finished)) :
    (action >>= continuation).run s = (.error .undefinedReference, finished) := by
  simp only [shape_run_bind, hfirst]
  exact hsecond

/-- A matrix copy error propagates through successful row scanning, shape validation, and allocation. -/
theorem concat_matrix_error_from_runs (arrays : List BitMatrix) (first : BitMatrix)
    (sizeDim : BitMatrix → I64 → I64) (allocate : I64 → I64 → BitMutationM BitMatrix)
    (rows : I64) (heights : List I64) (s allocated : State) (out : BitMatrix)
    (hscan : (concat_matrix_scan arrays sizeDim (int 0, [])).run s = (.ok (rows, heights), s))
    (hvalidation : (concat_matrix_validation arrays first sizeDim (sizeDim first (int 2))).run s = (.ok (), s))
    (hallocate : (allocate rows (sizeDim first (int 2))).run s = (.ok out, allocated))
    (hcopy : (concat_matrix_copies copyChunks arrays first heights (sizeDim first (int 2)) out).run allocated =
      (.error .undefinedReference, allocated)) :
    (concat_matrix_body copyChunks arrays first sizeDim allocate).run s = (.error .undefinedReference, allocated) := by
  apply concat_bind_error (concat_matrix_scan arrays sizeDim (int 0, []))
    (concat_matrix_after_scan copyChunks arrays first sizeDim allocate) s s allocated (rows, heights) hscan
  exact concat_three_stage_error (concat_matrix_validation arrays first sizeDim (sizeDim first (int 2)))
    (allocate rows (sizeDim first (int 2)))
    (concat_matrix_copies copyChunks arrays first heights (sizeDim first (int 2)))
    s allocated out hvalidation hallocate hcopy

/-- Every frozen matrix-vcat input with more than 64 output bits fails at the first positive-row source copy. -/
theorem concat_matrix_vcat_large_model_error (columns : Nat) (inputs : List (Nat × List Bool))
    (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hlarge : 64 < inputs.foldl (fun rows input => rows + input.1) 0 * columns)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 9223372036854775807) :
    ((bitArrayVcatMatrices
      ((inputs.zip (List.range inputs.length)).map (fun entry =>
        (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      Round5.Round2.allocateMatrixModel).run
      (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some))).1 =
      .error .undefinedReference := by
  cases inputs with
  | nil => simp only [List.foldl_nil, Nat.zero_mul] at hlarge; omega
  | cons first rest =>
    let inputs := first :: rest
    let entries := concat_matrix_indexed inputs
    let rows := (inputs.map Prod.fst).sum
    let initial := concat_initial (inputs.map Prod.snd)
    let arrays := entries.map (concat_matrix_entry columns)
    let head := concat_matrix_entry columns (first.1, first.2, 0)
    let heights := entries.map fun entry => int entry.1
    let count := wordCount (rows * columns)
    let slots := (List.replicate count none).set (count - 1) (some (u64 0))
    let finished := concat_new_chunks initial count slots
    let out : BitMatrix := ⟨initial.arrays.length, int ((rows * columns : Nat) : Int), [int rows, int columns]⟩
    have hrowSum : (entries.map Prod.fst).sum = rows := by
      dsimp only [entries, rows]
      rw [concat_matrix_indexed_rows]
    have hl : 64 < rows * columns := by
      dsimp only [rows]
      rw [concat_matrix_rows_sum]
      exact hlarge
    have hb : rows * columns ≤ 9223372036854775807 := by
      dsimp only [rows]
      rw [concat_matrix_rows_sum]
      exact hbound
    have hrpos : 0 < rows := by
      by_cases h : rows = 0
      · rw [h, Nat.zero_mul] at hl
        omega
      · omega
    have hcpos : 0 < columns := by
      by_cases h : columns = 0
      · rw [h, Nat.mul_zero] at hl
        omega
      · omega
    have hr : rows ≤ 9223372036854775807 := by
      have hm := Nat.mul_le_mul_left rows (show 1 ≤ columns by omega)
      simp only [Nat.mul_one] at hm
      omega
    have hc : columns ≤ 9223372036854775807 := by
      have hm := Nat.mul_le_mul_right columns (show 1 ≤ rows by omega)
      simp only [Nat.one_mul] at hm
      omega
    have hrowBound (entry : Nat × List Bool × Nat) (he : entry ∈ entries) : entry.1 ≤ rows := by
      have h := concat_member_le_sum (entries.map Prod.fst) entry.1 (List.mem_map_of_mem (f := Prod.fst) he)
      rw [hrowSum] at h
      exact h
    have hsource : ∀ entry ∈ entries, 0 < entry.1 → ∃ word,
        (mutableGet entry.2.2 (int 1)).run finished = (.ok word, finished) := by
      intro entry he hp
      have hs := hshape (entry.1, entry.2.1) (concat_matrix_indexed_mem inputs entry he)
      change entry.2.1.length = entry.1 * columns at hs
      have hpositive : 0 < entry.2.1.length := by rw [hs]; exact Nat.mul_pos hp hcpos
      have hsize : entry.2.1.length ≤ 9223372036854775807 := by
        rw [hs]
        exact Nat.le_trans (Nat.mul_le_mul_right columns (hrowBound entry he)) hb
      have hpair := List.mem_map_of_mem (f := Prod.snd) he
      rw [concat_matrix_indexed_pairs] at hpair
      exact ⟨packedPrefix entry.2.1 0 64,
        concat_initial_first_after_new (inputs.map Prod.snd) entry.2 hpair count slots hpositive hsize⟩
    have hdest := concat_new_first_undefined count
      (by dsimp only [count]; unfold wordCount; omega)
      (by dsimp only [count]; unfold wordCount; omega) initial
    have hinner := concat_matrix_inner_error entries columns initial.arrays.length head finished
      (fun entry he => Nat.le_trans (hrowBound entry he) hr)
      (by rw [hrowSum]; exact hrpos) hsource hdest
    have hcopy : (concat_matrix_copies copyChunks arrays head heights (int columns) out).run finished =
        (.error .undefinedReference, finished) := by
      apply concat_matrix_copies_error arrays head heights columns out finished
        (by simpa only [arrays, List.length_map, entries, concat_matrix_indexed_length] using hcount) hcpos hc
      simpa only [arrays, List.length_map] using hinner
    have hscan : (concat_matrix_scan arrays
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int 0, [])).run initial =
        (.ok (int rows, heights), initial) := by
      have h := concat_matrix_scan_run entries columns 0 [] initial
      simpa only [Int.zero_add, List.nil_append, hrowSum] using h
    have hvalidation : (concat_matrix_validation arrays head
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) (int columns)).run initial = (.ok (), initial) := by
      apply concat_matrix_validation_run
      intro index hi
      exact concat_matrix_lookup_columns entries (first.1, first.2, 0) columns (index.val.toNat - 1)
    have hallocate := concat_allocate_matrix_general rows columns hr hc (by omega) hb initial
    have hbody := concat_matrix_error_from_runs arrays head
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      concat_allocate_matrix_fn (int rows) heights initial finished out hscan hvalidation hallocate hcopy
    have hrun : (bitArrayVcatMatrices arrays
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) concat_allocate_matrix_fn).run initial =
        (.error .undefinedReference, finished) := by
      change (concat_matrix_program copyChunks
        (head :: ((rest.zipIdx 1).map (fun entry => (entry.1.1, entry.1.2, entry.2))).map (concat_matrix_entry columns))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0)) concat_allocate_matrix_fn).run initial = _
      rw [concat_matrix_nonempty_factor]
      exact hbody
    dsimp only [arrays, entries, initial] at hrun
    rw [concat_matrix_initial_heap, concat_matrix_indexed_headers] at hrun
    exact congrArg Prod.fst hrun

/-- A successful result is possible exactly on the verified size range when all larger cases return the model error. -/
theorem concat_result_supported_iff {α : Type} (result : Except JuliaLean.base.array.Error α × State)
    (size : Nat)
    (hsmall : size ≤ 64 → ∃ out finished, result = (.ok out, finished))
    (hlarge : 64 < size → result.1 = .error .undefinedReference) :
    (∃ out, result.1 = .ok out) ↔ size ≤ 64 := by
  constructor
  · rintro ⟨out, hout⟩
    by_cases hb : size ≤ 64
    · exact hb
    · have he := hlarge (by omega)
      rw [he] at hout
      cases hout
  · intro hb
    obtain ⟨out, finished, hr⟩ := hsmall hb
    exact ⟨out, congrArg Prod.fst hr⟩

/-- With a representable total bit count, the frozen vcat execution succeeds exactly for outputs of at most 64 bits. -/
theorem concat_vcat_success_iff (vectors : List (List Bool))
    (hbound : vectors.flatten.length ≤ 9223372036854775807) :
    (∃ out : BitVector,
      ((bitArrayVcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors)).1 = .ok out) ↔
      vectors.flatten.length ≤ 64 := by
  apply concat_result_supported_iff
  · intro hb
    obtain ⟨out, finished, hr, _⟩ := concat_vcat_small_correct vectors hb
    exact ⟨out, finished, hr⟩
  · intro hl
    exact congrArg Prod.fst (concat_vcat_large_model_error vectors hl hbound)

/-- Rectangular, nonempty frozen hcat succeeds exactly for outputs of at most 64 bits, with representable source count and total size. -/
theorem concat_hcat_success_iff (vectors : List (List Bool))
    (hne : vectors ≠ []) (hcount : vectors.length ≤ 9223372036854775807)
    (hall : ∀ xs ∈ vectors, xs.length = (vectors.headD []).length)
    (hbound : vectors.flatten.length ≤ 9223372036854775807) :
    (∃ out : BitMatrix,
      ((bitArrayHcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors)).1 = .ok out) ↔
      vectors.flatten.length ≤ 64 := by
  apply concat_result_supported_iff
  · intro hb
    obtain ⟨out, finished, hr, _⟩ := concat_hcat_small_correct vectors hne hcount hb hall
    exact ⟨out, finished, hr⟩
  · intro hl
    exact concat_hcat_large_model_error vectors hl hbound hall

/-- Well-shaped, nonempty frozen matrix-vcat succeeds exactly for outputs of at most 64 bits within native bounds. -/
theorem concat_matrix_vcat_success_iff (columns : Nat) (inputs : List (Nat × List Bool))
    (hne : inputs ≠ []) (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 9223372036854775807) :
    (∃ out : BitMatrix,
      ((bitArrayVcatMatrices
        ((inputs.zip (List.range inputs.length)).map (fun entry =>
          (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run
        (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some))).1 = .ok out) ↔
      inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 64 := by
  apply concat_result_supported_iff
  · intro hb
    obtain ⟨out, finished, hr, _⟩ := concat_matrix_vcat_small_correct columns inputs hne hcount hshape hrows hcols hb
    exact ⟨out, finished, hr⟩
  · intro hl
    exact concat_matrix_vcat_large_model_error columns inputs hcount hshape hl hbound

/-- One mismatched source height makes the readonly validation loop return its exact dimension error. -/
theorem concat_validate_heights_bad (indices : List I64) (lookup : I64 → BitVector) (height : I64)
    (s : State) (hbad : ∃ i ∈ indices, (lookup i).len ≠ height) :
    (forIn indices () (fun i _ => (do
      if (lookup i).len != height then throw (.dimensionMismatch "dimensions must match")
      pure (ForInStep.yield ())) : I64 → Unit → BitMutationM (ForInStep Unit))).run s =
      (.error (.dimensionMismatch "dimensions must match"), s) := by
  induction indices with
  | nil => obtain ⟨i, hi, _⟩ := hbad; cases hi
  | cons index indices ih =>
    by_cases he : (lookup index).len = height
    · have ht : ∃ i ∈ indices, (lookup i).len ≠ height := by
        obtain ⟨i, hi, hb⟩ := hbad
        rcases List.mem_cons.mp hi with hx | hx
        · subst i; exact False.elim (hb he)
        · exact ⟨i, hx, hb⟩
      simp only [List.forIn_cons, he, bne_self_eq_false, Bool.false_eq_true,
        ite_false, shape_run_bind, shape_run_pure]
      exact ih ht
    · simp only [List.forIn_cons, bne_iff_ne.mpr he, ite_true, shape_run_bind]
      rfl

/-- Any mismatched vector in a representable nonempty source list is visited by hcat validation. -/
theorem concat_hcat_validation_bad (first : BitVector) (rest : List BitVector) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hbad : ∃ vector ∈ rest, vector.len ≠ first.len) :
    (concat_hcat_validation (first :: rest) first).run s =
      (.error (.dimensionMismatch "dimensions must match"), s) := by
  apply concat_validate_heights_bad
  obtain ⟨vector, hv, hlen⟩ := hbad
  obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hv
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
    exact hlen

/-- Hcat returns dimensionMismatch before allocation or copying whenever source heights differ. -/
theorem concat_hcat_bad_shape_run (first : BitVector) (rest : List BitVector)
    (allocate : I64 → I64 → BitMutationM BitMatrix) (s : State)
    (hcount : (first :: rest).length ≤ 9223372036854775807)
    (hbad : ∃ vector ∈ rest, vector.len ≠ first.len) :
    (bitArrayHcatVectors (first :: rest) allocate).run s =
      (.error (.dimensionMismatch "dimensions must match"), s) := by
  rw [concat_hcat_factor, concat_hcat_nonempty_factor]
  exact concat_bind_first_error (concat_hcat_validation (first :: rest) first)
    (fun _ => do
      let out ← allocate first.len (int (first :: rest).length)
      let _ ← concat_hcat_copy copyChunks (first :: rest) first out
      pure out) s s (.dimensionMismatch "dimensions must match")
    (concat_hcat_validation_bad first rest s hcount hbad)

/-- The frozen hcat entry point rejects a missing source list before inspecting the heap. -/
theorem concat_hcat_no_sources (allocate : I64 → I64 → BitMutationM BitMatrix) (s : State) :
    (bitArrayHcatVectors [] allocate).run s = (.error .bounds, s) := rfl

/-- Distinct natural sizes within the signed native range have distinct encoded header integers. -/
theorem concat_native_sizes_ne (a b : Nat) (ha : a ≤ 9223372036854775807)
    (hb : b ≤ 9223372036854775807) (hne : a ≠ b) : int a ≠ int b := by
  intro he
  have hv := congrArg (fun value : I64 => value.val) he
  rw [packedInt_val a ha, packedInt_val b hb] at hv
  exact hne (by omega)

/-- Unequal logical column lengths produce exactly the public hcat dimension error and preserve the initial heap. -/
theorem concat_hcat_nonrectangular_error (vectors : List (List Bool))
    (hcount : vectors.length ≤ 9223372036854775807)
    (hbound : vectors.flatten.length ≤ 9223372036854775807)
    (hbad : ¬ ∀ xs ∈ vectors, xs.length = (vectors.headD []).length) :
    (bitArrayHcatVectors
      ((vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
      (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors) =
      (.error (.dimensionMismatch "dimensions must match"), concat_initial vectors) := by
  cases vectors with
  | nil => exact False.elim (hbad (by intro xs hx; cases hx))
  | cons first rest =>
    let vectors := first :: rest
    let headers := vectors.zipIdx.map concat_vector
    let head := concat_vector (first, 0)
    let tail := (rest.zipIdx 1).map concat_vector
    have hb : ∀ xs ∈ vectors, xs.length ≤ 9223372036854775807 := by
      intro xs hx
      exact Nat.le_trans (concat_component_length vectors xs hx) hbound
    have hrest : ∃ xs ∈ rest, xs.length ≠ first.length := by
      apply Classical.byContradiction
      intro hn
      apply hbad
      intro xs hx
      rcases List.mem_cons.mp hx with he | he
      · subst xs; rfl
      · have heq : xs.length = first.length := by
          by_cases heq : xs.length = first.length
          · exact heq
          · exact False.elim (hn ⟨xs, he, heq⟩)
        exact heq
    have hwrong : ∃ vector ∈ tail, vector.len ≠ head.len := by
      obtain ⟨xs, hx, he⟩ := hrest
      obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hx
      let entry := (xs, index + 1)
      have hm : entry ∈ rest.zipIdx 1 := by
        apply List.mem_iff_getElem.mpr
        refine ⟨index, by simpa only [List.length_zipIdx] using hi, ?_⟩
        simp only [List.getElem_zipIdx, heq]
        exact congrArg (fun j => (xs, j)) (Nat.add_comm 1 index)
      refine ⟨concat_vector entry, List.mem_map_of_mem (f := concat_vector) hm, ?_⟩
      exact concat_native_sizes_ne xs.length first.length
        (hb xs (List.mem_cons_of_mem first hx)) (hb first List.mem_cons_self) he
    have hrun := concat_hcat_bad_shape_run head tail
      (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols]) (concat_initial vectors)
      (by simpa only [tail, List.length_cons, List.length_map, List.length_zipIdx] using hcount) hwrong
    change (bitArrayHcatVectors headers _).run _ = _ at hrun
    dsimp only [headers] at hrun
    rw [concat_indexed_handles] at hrun
    exact hrun

/-- The frozen horizontal-concatenation model succeeds exactly on nonempty, rectangular inputs of at most 64 total bits. -/
theorem concat_hcat_full_success_iff (vectors : List (List Bool))
    (hcount : vectors.length ≤ 9223372036854775807)
    (hbound : vectors.flatten.length ≤ 9223372036854775807) :
    (∃ out : BitMatrix,
      ((bitArrayHcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors)).1 = .ok out) ↔
      vectors ≠ [] ∧ (∀ xs ∈ vectors, xs.length = (vectors.headD []).length) ∧ vectors.flatten.length ≤ 64 := by
  constructor
  · rintro ⟨out, hout⟩
    have hne : vectors ≠ [] := by
      intro he
      subst vectors
      change (.error .bounds : Except JuliaLean.base.array.Error BitMatrix) = .ok out at hout
      cases hout
    have hrect : ∀ xs ∈ vectors, xs.length = (vectors.headD []).length := by
      apply Classical.byContradiction
      intro hb
      have herr := congrArg Prod.fst (concat_hcat_nonrectangular_error vectors hcount hbound hb)
      rw [herr] at hout
      cases hout
    exact ⟨hne, hrect, (concat_hcat_success_iff vectors hne hcount hrect hbound).mp ⟨out, hout⟩⟩
  · rintro ⟨hne, hrect, hsize⟩
    exact (concat_hcat_success_iff vectors hne hcount hrect hbound).mpr hsize

/-- The matrix-vcat entry point rejects a missing source list before scanning dimensions or touching the heap. -/
theorem concat_matrix_no_sources (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) (s : State) :
    (bitArrayVcatMatrices [] sizeDim allocate).run s = (.error .bounds, s) := rfl

/-- The frozen matrix-vcat model succeeds exactly on nonempty well-shaped inputs with at most 64 total bits. -/
theorem concat_matrix_vcat_full_success_iff (columns : Nat) (inputs : List (Nat × List Bool))
    (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 9223372036854775807) :
    (∃ out : BitMatrix,
      ((bitArrayVcatMatrices
        ((inputs.zip (List.range inputs.length)).map (fun entry =>
          (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run
        (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some))).1 = .ok out) ↔
      inputs ≠ [] ∧ inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 64 := by
  constructor
  · rintro ⟨out, hout⟩
    have hne : inputs ≠ [] := by
      intro he
      subst inputs
      change (.error .bounds : Except JuliaLean.base.array.Error BitMatrix) = .ok out at hout
      cases hout
    exact ⟨hne, (concat_matrix_vcat_success_iff columns inputs hne hcount hshape hrows hcols hbound).mp ⟨out, hout⟩⟩
  · rintro ⟨hne, hsize⟩
    exact (concat_matrix_vcat_success_iff columns inputs hne hcount hshape hrows hcols hbound).mpr hsize

/-- Every successful frozen vcat run within the native total-size bound satisfies all logical and packing observations. -/
theorem concat_vcat_success_correct (vectors : List (List Bool))
    (hbound : vectors.flatten.length ≤ 9223372036854775807) (out : BitVector) (finished : State)
    (hrun : (bitArrayVcatVectors
      ((vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
      (fun n => Round5.Round2.allocateBitArrayModel [n])).run (concat_initial vectors) = (.ok out, finished)) :
    out.dims = [int vectors.flatten.length] ∧ bitValues finished out = vectors.flatten ∧
      Round5.Round2.PackedInvariant finished out := by
  have hsmall := (concat_vcat_success_iff vectors hbound).mp ⟨out, congrArg Prod.fst hrun⟩
  obtain ⟨expected, verified, he, hobs⟩ := concat_vcat_small_correct vectors hsmall
  have hs := hrun.symm.trans he
  have hv : out = expected := Except.ok.inj (congrArg Prod.fst hs)
  have hm : finished = verified := congrArg Prod.snd hs
  rw [hv, hm]
  exact hobs

/-- Every successful frozen hcat run has the expected column-major contents, dimensions, and packed padding. -/
theorem concat_hcat_success_correct (vectors : List (List Bool))
    (hcount : vectors.length ≤ 9223372036854775807)
    (hbound : vectors.flatten.length ≤ 9223372036854775807) (out : BitMatrix) (finished : State)
    (hrun : (bitArrayHcatVectors
      ((vectors.zip (List.range vectors.length)).map (fun entry =>
        (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
      (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors) =
        (.ok out, finished)) :
    out.dims = [int (vectors.headD []).length, int vectors.length] ∧ bitValues finished out = vectors.flatten ∧
      Round5.Round2.PackedInvariant finished out := by
  obtain ⟨hne, hrect, hsmall⟩ := (concat_hcat_full_success_iff vectors hcount hbound).mp
    ⟨out, congrArg Prod.fst hrun⟩
  obtain ⟨expected, verified, he, hobs⟩ := concat_hcat_small_correct vectors hne hcount hsmall hrect
  have hs := hrun.symm.trans he
  have hv : out = expected := Except.ok.inj (congrArg Prod.fst hs)
  have hm : finished = verified := congrArg Prod.snd hs
  rw [hv, hm]
  exact hobs

/-- Every successful well-shaped frozen matrix-vcat run within native bounds satisfies its full columnwise contract. -/
theorem concat_matrix_vcat_success_correct (columns : Nat) (inputs : List (Nat × List Bool))
    (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 9223372036854775807)
    (out : BitMatrix) (finished : State)
    (hrun : (bitArrayVcatMatrices
      ((inputs.zip (List.range inputs.length)).map (fun entry =>
        (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      Round5.Round2.allocateMatrixModel).run
      (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some)) = (.ok out, finished)) :
    out.dims = [int ((inputs.foldl (fun rows input => rows + input.1) 0 : Nat) : Int), int columns] ∧
      bitValues finished out = (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) ∧
      Round5.Round2.PackedInvariant finished out := by
  obtain ⟨hne, hsmall⟩ := (concat_matrix_vcat_full_success_iff columns inputs hcount hshape hrows hcols hbound).mp
    ⟨out, congrArg Prod.fst hrun⟩
  obtain ⟨expected, verified, he, hobs⟩ := concat_matrix_vcat_small_correct columns inputs hne hcount hshape hrows hcols hsmall
  have hs := hrun.symm.trans he
  have hv : out = expected := Except.ok.inj (congrArg Prod.fst hs)
  have hm : finished = verified := congrArg Prod.snd hs
  rw [hv, hm]
  exact hobs
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

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

/-- Repeated full-word stores preserve the destination's physical length. -/
def abs_written_words (words : List U64) (value : Nat → U64) (count : Nat) : List U64 :=
  (List.range count).foldl (fun current j => current.set j (value j)) words

theorem abs_written_zero (words : List U64) (value : Nat → U64) :
    abs_written_words words value 0 = words := rfl

theorem abs_written_succ (words : List U64) (value : Nat → U64) (count : Nat) :
    abs_written_words words value (count + 1) =
      (abs_written_words words value count).set count (value count) := by
  simp only [abs_written_words, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem abs_written_length (words : List U64) (value : Nat → U64) (count : Nat) :
    (abs_written_words words value count).length = words.length := by
  induction count with
  | zero => rfl
  | succ count ih => rw [abs_written_succ, List.length_set, ih]

theorem abs_word_getD_set (words : List U64) (i j : Nat) (value : U64)
    (hi : i < words.length) :
    (words.set i value).getD j (u64 0) =
      if i = j then value else words.getD j (u64 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hi, and_self, ite_true]
  by_cases he : i = j <;> simp only [he, ite_true, ite_false, Option.getD_some]

/-- Every previously copied chunk has the source value; every later chunk is unchanged. -/
theorem abs_written_get (words : List U64) (value : Nat → U64) (count j : Nat)
    (hc : count ≤ words.length) :
    (abs_written_words words value count).getD j (u64 0) =
      if j < count then value j else words.getD j (u64 0) := by
  induction count with
  | zero => simp only [abs_written_zero, Nat.not_lt_zero, ite_false]
  | succ count ih =>
      rw [abs_written_succ, abs_word_getD_set _ count j (value count)
        (by rw [abs_written_length]; omega)]
      by_cases he : count = j
      · subst j
        simp only [ite_true, Nat.lt_add_one]
      · rw [if_neg he, ih (by omega)]
        by_cases hj : j < count
        · simp only [hj, show j < count + 1 by omega, ite_true]
        · simp only [hj, show ¬ j < count + 1 by omega, ite_false]

theorem abs_encoded_get (xs : List Bool) (chunk : Nat)
    (hc : chunk < wordCount xs.length) :
    (encodeBits xs).getD chunk (u64 0) = packedPrefix xs chunk 64 := by
  have hb : chunk < (encodeBits xs).length := by rw [packedEncoded_length]; exact hc
  rw [← List.getElem_eq_getD (h := hb)]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]

/-- Abstract-array copying replaces precisely a prefix of the logical sequence. -/
theorem abs_expected_get (xs dest : List Bool) (hcopy : xs.length ≤ dest.length) (i : Nat) :
    (xs ++ dest.drop xs.length).getD i false =
      if i < xs.length then xs.getD i false else dest.getD i false := by
  by_cases hi : i < xs.length
  · simp only [hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · have hle : xs.length ≤ i := by omega
    simp only [hi, ite_false, List.getD_eq_getElem?_getD, List.getElem?_append_right hle,
      List.getElem?_drop, Nat.add_sub_cancel' hle]

theorem abs_expected_length (xs dest : List Bool) (hcopy : xs.length ≤ dest.length) :
    (xs ++ dest.drop xs.length).length = dest.length := by
  simp only [List.length_append, List.length_drop]
  omega

/-- The final partial chunk combines copied low bits with untouched destination bits. -/
def abs_tail_word (xs dest : List Bool) : U64 :=
  let chunk := wordCount xs.length - 1
  let tail := abs_tail_count xs.length
  let mask := maskEnd (int tail)
  or_int (and_int (packedPrefix xs chunk tail) mask)
    (and_int (packedPrefix dest chunk 64) (not_int mask))

theorem abs_tail_word_bit (xs dest : List Bool) (hp : 0 < xs.length)
    (bit : Nat) (hb : bit < 64) :
    packedBit (abs_tail_word xs dest) bit =
      if (wordCount xs.length - 1) * 64 + bit < xs.length then
        xs.getD ((wordCount xs.length - 1) * 64 + bit) false
      else dest.getD ((wordCount xs.length - 1) * 64 + bit) false := by
  have hc := abs_tail_counts xs.length hp
  simp only [abs_tail_word, packedBit_or, scalar_packedBit_and,
    scalar_packedBit_not _ _ hb, packedPrefix_bit xs _ _ _ hc.2.1,
    packedWord_bit dest _ _ hb,
    rangeSingleEndMaskBit _ bit hc.1 hc.2.1 hb]
  by_cases hi : bit < abs_tail_count xs.length
  · have hpos : (wordCount xs.length - 1) * 64 + bit < xs.length := by omega
    simp only [hi, hpos, decide_true, Bool.true_and, Bool.and_true,
      Bool.not_true, Bool.and_false, Bool.or_false, ite_true]
  · have hneg : ¬ (wordCount xs.length - 1) * 64 + bit < xs.length := by omega
    simp only [hi, hneg, decide_false, Bool.false_and, Bool.and_false,
      Bool.not_false, Bool.and_true, Bool.false_or, ite_false]

/-- The whole physical copy result encodes the source followed by the untouched suffix. -/
theorem abs_output_encode (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) :
    (abs_written_words (encodeBits dest) (fun chunk => packedPrefix xs chunk 64)
      (wordCount xs.length - 1)).set (wordCount xs.length - 1) (abs_tail_word xs dest) =
      encodeBits (xs ++ dest.drop xs.length) := by
  have hlast : wordCount xs.length - 1 < wordCount dest.length := by
    unfold wordCount
    omega
  have hlast' : wordCount xs.length - 1 < (encodeBits dest).length := by
    rw [packedEncoded_length]
    exact hlast
  have hc := abs_tail_counts xs.length hp
  apply List.ext_getElem
  · simp only [List.length_set, abs_written_length, packedEncoded_length,
      abs_expected_length xs dest hcopy]
  · intro chunk hchunk hchunk'
    have hdest : chunk < wordCount dest.length := by
      simpa only [List.length_set, abs_written_length, packedEncoded_length] using hchunk
    have hout : chunk < wordCount (xs ++ dest.drop xs.length).length := by
      rw [abs_expected_length xs dest hcopy]
      exact hdest
    rw [List.getElem_eq_getD (fallback := u64 0), List.getElem_eq_getD (fallback := u64 0),
      abs_word_getD_set _ _ _ _ (by rw [abs_written_length]; exact hlast'),
      abs_written_get _ _ _ _ (by omega), abs_encoded_get _ _ hout]
    apply packedBit_ext
    intro bit hb
    rw [packedWord_bit _ chunk bit hb, abs_expected_get xs dest hcopy]
    by_cases he : wordCount xs.length - 1 = chunk
    · subst chunk
      rw [if_pos rfl, abs_tail_word_bit xs dest hp bit hb]
    · rw [if_neg he]
      by_cases hi : chunk < wordCount xs.length - 1
      · have hpast : chunk * 64 + bit < xs.length := by omega
        rw [if_pos hi, packedWord_bit xs chunk bit hb, if_pos hpast]
      · have hpast : ¬ chunk * 64 + bit < xs.length := by omega
        rw [if_neg hi, abs_encoded_get dest chunk hdest,
          packedWord_bit dest chunk bit hb, if_neg hpast]

/-- The full-chunk loop body of the frozen abstract-array copy. -/
def abs_full_step (xs : List Bool) (index : I64) (cursor : I64) :
    BitMutationM (ForInStep I64) := do
  let result ← forIn (intRange (int 0) (int 63)) (cursor, u64 0) (abs_pack_step xs)
  mutableSet 0 result.2 index
  pure (.yield result.1)

/-- Pack and store phases compose without reducing the finite packing loop. -/
theorem abs_pack_store_run (pack : BitMutationM (I64 × U64)) (index next : I64)
    (word : U64) (s middle out : State)
    (hp : pack.run s = (.ok (next, word), middle))
    (hw : (mutableSet 0 word index).run middle = (.ok (), out)) :
    ((do
      let result ← pack
      mutableSet 0 result.2 index
      pure (.yield result.1)) : BitMutationM (ForInStep I64)).run s =
      (.ok (.yield next), out) := by
  simp only [shape_run_bind, hp, hw, shape_run_pure]

theorem abs_full_step_run (xs : List Bool) (words : List U64) (chunk : Nat)
    (hwords : words.length ≤ 9223372036854775807) (hchunk : chunk < words.length)
    (hn : chunk * 64 + 64 ≤ 9223372036854775807) :
    (abs_full_step xs (int ((chunk + 1 : Nat) : Int))
      (int ((chunk * 64 + 1 : Nat) : Int))).run
      (initWords (abs_written_words words (fun k => packedPrefix xs k 64) chunk)) =
      (.ok (.yield (int (((chunk + 1) * 64 + 1 : Nat) : Int))),
        initWords (abs_written_words words (fun k => packedPrefix xs k 64) (chunk + 1))) := by
  have hp := abs_pack_loop_run xs chunk 64
    (initWords (abs_written_words words (fun k => packedPrefix xs k 64) chunk)) (by omega) hn
  have h63 : int ((64 : Nat) : Int) - int 1 = int 63 := by decide
  rw [h63] at hp
  have hw := scalar_initial_set
    (abs_written_words words (fun k => packedPrefix xs k 64) chunk) chunk
    (packedPrefix xs chunk 64) (by rw [abs_written_length]; exact hwords)
    (by rw [abs_written_length]; exact hchunk)
  have hnext : chunk * 64 + 64 + 1 = (chunk + 1) * 64 + 1 := by omega
  have hrun := abs_pack_store_run _ (int ((chunk + 1 : Nat) : Int))
    (int ((chunk * 64 + 64 + 1 : Nat) : Int)) (packedPrefix xs chunk 64) _ _ _ hp hw
  rw [hnext] at hrun
  rw [abs_written_succ]
  exact hrun

/-- The loop copies every complete source chunk and stops before the tail chunk. -/
theorem abs_full_loop_run (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (forIn (intRange (int 1) (int (wordCount xs.length) - int 1))
      (int 1) (abs_full_step xs)).run (initWords (encodeBits dest)) =
      (.ok (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int)),
        initWords (abs_written_words (encodeBits dest) (fun k => packedPrefix xs k 64)
          (wordCount xs.length - 1))) := by
  have hc := abs_tail_counts xs.length hp
  have hpos : 0 < wordCount xs.length := by unfold wordCount; omega
  have hsub : int (wordCount xs.length) - int 1 =
      int ((wordCount xs.length - 1 : Nat) : Int) := by
    rw [concat_int_sub]
    apply congrArg int
    omega
  have hbound : wordCount xs.length - 1 ≤ 9223372036854775807 := by
    unfold wordCount
    omega
  rw [hsub, packedObserve_intRange _ hbound, List.forIn_map]
  have h := concat_range_loop 0 (wordCount xs.length - 1) (wordCount xs.length - 1)
    (fun k => int ((k * 64 + 1 : Nat) : Int))
    (fun k => initWords (abs_written_words (encodeBits dest)
      (fun c => packedPrefix xs c 64) k))
    (fun k cursor => abs_full_step xs (int ((k + 1 : Nat) : Int)) cursor)
    (by
      intro k hk
      exact abs_full_step_run xs (encodeBits dest) k (packedEncoded_lengthBound dest hn)
        (by rw [packedEncoded_length]; unfold wordCount at *; omega) (by omega)) (by omega)
  simpa only [← List.range_eq_range', Nat.zero_add, Nat.add_zero, Nat.zero_mul, Int.natCast_one,
    abs_written_zero] using h

/-- The final read-modify-write preserves destination bits outside the copy mask. -/
def abs_finish (pack : BitMutationM (I64 × U64)) (index : I64) (mask : U64)
    (B : BitVector) : BitMutationM BitVector := do
  let result ← pack
  let old ← mutableGet 0 index
  mutableSet 0 (or_int (and_int result.2 mask) (and_int old (not_int mask))) index
  pure B

theorem abs_finish_run (pack : BitMutationM (I64 × U64)) (index next : I64)
    (mask word old : U64) (B : BitVector) (s middle out : State)
    (hp : pack.run s = (.ok (next, word), middle))
    (hr : (mutableGet 0 index).run middle = (.ok old, middle))
    (hw : (mutableSet 0 (or_int (and_int word mask) (and_int old (not_int mask))) index).run
      middle = (.ok (), out)) :
    (abs_finish pack index mask B).run s = (.ok B, out) := by
  simp only [abs_finish, shape_run_bind, hp, hr, hw, shape_run_pure]

/-- Both execution phases with their native counters supplied explicitly. -/
def abs_copy_body_with (xs : List Bool) (len : I64) (dims : List I64)
    (nc tail : I64) : BitMutationM BitVector := do
  let cursor ← forIn (intRange (int 1) (nc - int 1)) (int 1) (abs_full_step xs)
  abs_finish (forIn (intRange (int 0) (tail - int 1)) (cursor, u64 0) (abs_pack_step xs))
    nc (maskEnd tail) ⟨0, len, dims⟩

/-- The main copy computation with its two loop bodies factored out. -/
def abs_copy_body (xs : List Bool) (len : I64) (dims : List I64) : BitMutationM BitVector :=
  abs_copy_body_with xs len dims (numBitChunks (int xs.length))
    (mod64 (int xs.length - int 1) + int 1)

theorem abs_copy_phases_run (xs : List Bool) (len : I64) (dims : List I64)
    (nc tail cursor : I64) (s middle out : State)
    (hloop : (forIn (intRange (int 1) (nc - int 1)) (int 1) (abs_full_step xs)).run s =
      (.ok cursor, middle))
    (hfinish : (abs_finish
      (forIn (intRange (int 0) (tail - int 1)) (cursor, u64 0) (abs_pack_step xs))
      nc (maskEnd tail) (⟨0, len, dims⟩ : BitVector)).run middle =
      (.ok ⟨0, len, dims⟩, out)) :
    (abs_copy_body_with xs len dims nc tail).run s = (.ok ⟨0, len, dims⟩, out) := by
  unfold abs_copy_body_with
  rw [shape_run_bind, hloop]
  exact hfinish

theorem abs_copy_body_factor (xs : List Bool) (len : I64) (dims : List I64)
    (hz : (int xs.length == int 0) = false) (hsize : ¬ int xs.length > len) :
    copytoBitArrayFromAbstract (fun values : List Bool => int values.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false))
      (⟨0, len, dims⟩ : BitVector) xs = abs_copy_body xs len dims := by
  simp only [copytoBitArrayFromAbstract, hz, Bool.false_eq_true, ite_false, hsize]
  rfl

/-- The destination words after all complete source chunks have been copied. -/
def abs_prefix_words (xs dest : List Bool) : List U64 :=
  abs_written_words (encodeBits dest) (fun k => packedPrefix xs k 64) (wordCount xs.length - 1)

theorem abs_prefix_bounds (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (abs_prefix_words xs dest).length ≤ 9223372036854775807 ∧
    wordCount xs.length - 1 < (abs_prefix_words xs dest).length ∧
    wordCount xs.length - 1 + 1 = wordCount xs.length := by
  simp only [abs_prefix_words, abs_written_length, packedEncoded_length]
  unfold wordCount
  omega

/-- The tail chunk has not been touched by the complete-word loop. -/
theorem abs_last_read_run (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (mutableGet 0 (int (wordCount xs.length))).run (initWords (abs_prefix_words xs dest)) =
      (.ok (packedPrefix dest (wordCount xs.length - 1) 64),
        initWords (abs_prefix_words xs dest)) := by
  have hb := abs_prefix_bounds xs dest hp hcopy hn
  have hr := packedObserve_read (abs_prefix_words xs dest) hb.1 (wordCount xs.length - 1) hb.2.1
  rw [List.getElem_eq_getD (fallback := u64 0), hb.2.2] at hr
  have hlast : wordCount xs.length - 1 < wordCount dest.length := by unfold wordCount; omega
  have hword : (abs_prefix_words xs dest).getD (wordCount xs.length - 1) (u64 0) =
      packedPrefix dest (wordCount xs.length - 1) 64 := by
    unfold abs_prefix_words
    rw [abs_written_get _ _ _ _ (by rw [packedEncoded_length]; omega),
      if_neg (Nat.lt_irrefl _), abs_encoded_get dest _ hlast]
  rw [hword] at hr
  exact hr

/-- Updating the last copied word produces the final packed encoding. -/
theorem abs_last_write_run (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (mutableSet 0 (abs_tail_word xs dest) (int (wordCount xs.length))).run
      (initWords (abs_prefix_words xs dest)) =
      (.ok (), initWords (encodeBits (xs ++ dest.drop xs.length))) := by
  have hb := abs_prefix_bounds xs dest hp hcopy hn
  have hw := scalar_initial_set (abs_prefix_words xs dest) (wordCount xs.length - 1)
    (abs_tail_word xs dest) hb.1 hb.2.1
  have hout : (abs_prefix_words xs dest).set (wordCount xs.length - 1) (abs_tail_word xs dest) =
      encodeBits (xs ++ dest.drop xs.length) := abs_output_encode xs dest hp hcopy
  rw [hb.2.2, hout] at hw
  exact hw

/-- The bounded tail phase has its exact success result and heap. -/
theorem abs_tail_finish_run (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (abs_finish
      (forIn (intRange (int 0) (int (abs_tail_count xs.length) - int 1))
        (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int), u64 0) (abs_pack_step xs))
      (int (wordCount xs.length)) (maskEnd (int (abs_tail_count xs.length)))
      (⟨0, int dest.length, [int dest.length]⟩ : BitVector)).run
        (initWords (abs_prefix_words xs dest)) =
      (.ok ⟨0, int dest.length, [int dest.length]⟩,
        initWords (encodeBits (xs ++ dest.drop xs.length))) := by
  have hc := abs_tail_counts xs.length hp
  have hpack := abs_pack_loop_run xs (wordCount xs.length - 1) (abs_tail_count xs.length)
    (initWords (abs_prefix_words xs dest)) hc.2.1 (by omega)
  exact abs_finish_run _ (int (wordCount xs.length))
    (int (((wordCount xs.length - 1) * 64 + abs_tail_count xs.length + 1 : Nat) : Int))
    (maskEnd (int (abs_tail_count xs.length)))
    (packedPrefix xs (wordCount xs.length - 1) (abs_tail_count xs.length))
    (packedPrefix dest (wordCount xs.length - 1) 64)
    (⟨0, int dest.length, [int dest.length]⟩ : BitVector) _ _ _ hpack
    (abs_last_read_run xs dest hp hcopy hn) (abs_last_write_run xs dest hp hcopy hn)

/-- The complete and partial word phases compose into one successful copy. -/
theorem abs_copy_body_run (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (abs_copy_body xs (int dest.length) [int dest.length]).run (initWords (encodeBits dest)) =
      (.ok ⟨0, int dest.length, [int dest.length]⟩,
        initWords (encodeBits (xs ++ dest.drop xs.length))) := by
  have hsrc : xs.length ≤ 9223372036854775807 := by omega
  have he : abs_copy_body xs (int dest.length) [int dest.length] =
      abs_copy_body_with xs (int dest.length) [int dest.length]
        (int (wordCount xs.length)) (int (abs_tail_count xs.length)) :=
    (congrArg (fun nc => abs_copy_body_with xs (int dest.length) [int dest.length]
      nc (mod64 (int xs.length - int 1) + int 1)) (shiftFreshNumChunks xs.length hsrc)).trans
      (congrArg (abs_copy_body_with xs (int dest.length) [int dest.length]
        (int (wordCount xs.length))) (abs_tail_native xs.length hp hsrc))
  have hr := abs_copy_phases_run xs (int dest.length) [int dest.length]
    (int (wordCount xs.length)) (int (abs_tail_count xs.length))
    (int (((wordCount xs.length - 1) * 64 + 1 : Nat) : Int))
    (initWords (encodeBits dest)) (initWords (abs_prefix_words xs dest))
    (initWords (encodeBits (xs ++ dest.drop xs.length)))
    (abs_full_loop_run xs dest hp hcopy hn) (abs_tail_finish_run xs dest hp hcopy hn)
  exact (congrArg (fun action : BitMutationM BitVector => action.run (initWords (encodeBits dest))) he).trans hr

/-- Every positive native prefix copy reaches the exact copied encoding. -/
theorem abs_abstract_copy_positive_run (xs dest : List Bool) (hp : 0 < xs.length)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (copytoBitArrayFromAbstract (fun values : List Bool => int values.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false))
      (⟨0, int dest.length, [int dest.length]⟩ : BitVector) xs).run
      (initWords (encodeBits dest)) =
      (.ok ⟨0, int dest.length, [int dest.length]⟩,
        initWords (encodeBits (xs ++ dest.drop xs.length))) := by
  have hsrc : xs.length ≤ 9223372036854775807 := by omega
  have hzero : (int xs.length == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val xs.length hsrc] at hv
    change (xs.length : Int) = 0 at hv
    omega
  have hsize : ¬ int xs.length > int dest.length := by
    change ¬ (int dest.length).val < (int xs.length).val
    rw [packedInt_val dest.length hn, packedInt_val xs.length hsrc]
    omega
  rw [abs_copy_body_factor xs (int dest.length) [int dest.length] hzero hsize]
  exact abs_copy_body_run xs dest hp hcopy hn

/-- Complete abstract-array copy execution under the missing native-size guard. -/
theorem abs_abstract_copy_run (xs dest : List Bool)
    (hcopy : xs.length ≤ dest.length) (hn : dest.length ≤ 9223372036854775807) :
    (copytoBitArrayFromAbstract (fun values : List Bool => int values.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false))
      (⟨0, int dest.length, [int dest.length]⟩ : BitVector) xs).run
      (initWords (encodeBits dest)) =
      (.ok ⟨0, int dest.length, [int dest.length]⟩,
        initWords (encodeBits (xs ++ dest.drop xs.length))) := by
  by_cases hp : 0 < xs.length
  · exact abs_abstract_copy_positive_run xs dest hp hcopy hn
  · have he : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => simp only [List.length_cons] at hp; omega
    subst xs
    simp only [copytoBitArrayFromAbstract, List.length_nil, Int.natCast_zero, beq_self_eq_true,
      ite_true, shape_run_pure, List.nil_append, List.drop_zero]

/-- The frozen abstract-array observations hold for every representable destination length. -/
theorem abs_abstractArrayCopy_bounded (xs destValues : List Bool)
    (hcopy : xs.length ≤ destValues.length) (hn : destValues.length ≤ 9223372036854775807) :
    let B : BitArray 1 := ⟨0, int destValues.length, [int destValues.length]⟩
    let state := initWords (encodeBits destValues)
    let result := (copytoBitArrayFromAbstract (fun values : List Bool => int values.length)
      (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false)) B xs).run state
    match result.1 with
    | .ok output => bitValues result.2 output = xs ++ destValues.drop xs.length
    | .error _ => False := by
  dsimp only
  rw [abs_abstract_copy_run xs destValues hcopy hn]
  have hlength := abs_expected_length xs destValues hcopy
  have hbits := scalar_bits_initial (N := 1) (xs ++ destValues.drop xs.length)
    [int destValues.length] (by rw [hlength]; exact hn)
  simpa only [hlength] using hbits
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Writing the destination word leaves the independent source vector intact. -/
theorem copy_destination_set (destination source : List U64) (j : Nat) (word : U64)
    (hn : destination.length ≤ 9223372036854775807) (hj : j < destination.length) :
    (mutableSet 0 word (int ((j + 1 : Nat) : Int))).run (cmpInitialState destination source) =
      (.ok (), cmpInitialState (destination.set j word) source) := by
  have hi := packedInt_val (j + 1) (by omega)
  have hsize := packedInt_val destination.length hn
  have hidx : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by
    rw [hi]
    omega
  have ha : (cmpInitialState destination source).arrays[0]? =
      some ⟨(0, one), int destination.length⟩ := by
    change some (⟨(0, one), int (destination.map some).length⟩ : MutableVector) = _
    rw [List.length_map]
  have hraw := scalar_set_run (cmpInitialState destination source)
    (destination.map some ++ List.replicate 32 none) (int destination.length) ha rfl
    (by rw [hsize]; simp only [List.length_append, List.length_map, List.length_replicate]; omega)
    (int ((j + 1 : Nat) : Int)) word (by rw [hi, hsize]; omega)
  rw [hraw, hidx]
  change ((Except.ok (), MutableMemory.mk
      [(destination.map some ++ List.replicate 32 none).set j (some word),
        source.map some ++ List.replicate 32 none]
      [⟨(0, one), int (destination.map some).length⟩,
        ⟨(1, one), int (source.map some).length⟩]) : Except Error Unit × State) =
    (Except.ok (), MutableMemory.mk
      [(destination.set j word).map some ++ List.replicate 32 none,
        source.map some ++ List.replicate 32 none]
      [⟨(0, one), int ((destination.set j word).map some).length⟩,
        ⟨(1, one), int (source.map some).length⟩])
  rw [List.set_append_left _ _ (by simpa only [List.length_map] using hj)]
  rw [← List.map_set]
  simp only [List.length_map, List.length_set]

/-- A source read followed by a destination write has the expected list-update effect. -/
theorem copy_step_run (destination source : List U64) (j : Nat)
    (hd : destination.length ≤ 9223372036854775807)
    (hs : source.length ≤ 9223372036854775807)
    (hjd : j < destination.length) (hjs : j < source.length) :
    ((do
      let word ← mutableGet 1 (int ((j + 1 : Nat) : Int))
      mutableSet 0 word (int ((j + 1 : Nat) : Int))) : BitMutationM Unit).run
        (cmpInitialState destination source) =
      (.ok (), cmpInitialState (destination.set j (source.getD j (u64 0))) source) := by
  have hword : source[j] = source.getD j (u64 0) := List.getElem_eq_getD (u64 0)
  have hr := (cmp_initial_read_right destination source hs j hjs).trans
    (congrArg (fun word : U64 => ((Except.ok word : Except Error U64),
      cmpInitialState destination source)) hword)
  exact concat_bind_success
    (mutableGet 1 (int ((j + 1 : Nat) : Int)))
    (fun word => mutableSet 0 word (int ((j + 1 : Nat) : Int)))
    (cmpInitialState destination source) (cmpInitialState destination source)
    (cmpInitialState (destination.set j (source.getD j (u64 0))) source)
    (source.getD j (u64 0)) () hr
    (copy_destination_set destination source j (source.getD j (u64 0)) hd hjd)

/-- A destination shorter than its source rejects before any memory access. -/
theorem copy_short_destination {N : Nat} (destination source : BitArray N) (state : State)
    (hshort : source.len > destination.len) :
    (bitArrayCopyto destination source).run state = (.error .bounds, state) := by
  simp only [bitArrayCopyto, hshort, ite_true]
  rfl

/-- The chunk-copy fold preserves destination length. -/
theorem copy_fold_length (indices : List Nat) (destination source : List U64) :
    (indices.foldl (fun words j => words.set j (source.getD j (u64 0))) destination).length =
      destination.length := by
  induction indices generalizing destination with
  | nil => rfl
  | cons j indices ih => rw [List.foldl_cons, ih, List.length_set]

/-- Each completed source-to-destination chunk loop has an exact list-fold interpretation. -/
theorem copy_loop_run (indices : List Nat) (destination source : List U64)
    (hd : destination.length ≤ 9223372036854775807)
    (hs : source.length ≤ 9223372036854775807)
    (hi : ∀ j ∈ indices, j < destination.length ∧ j < source.length) :
    (forIn (indices.map (fun j => int ((j + 1 : Nat) : Int))) PUnit.unit
      (fun i _ => do
        let word ← mutableGet 1 i
        mutableSet 0 word i
        pure (ForInStep.yield PUnit.unit))).run (cmpInitialState destination source) =
      (.ok PUnit.unit, cmpInitialState
        (indices.foldl (fun words j => words.set j (source.getD j (u64 0))) destination) source) := by
  let action : Nat → BitMutationM Unit := fun j => do
    let word ← mutableGet 1 (int ((j + 1 : Nat) : Int))
    mutableSet 0 word (int ((j + 1 : Nat) : Int))
  have h := dequeForInFold action
    (fun words j => words.set j (source.getD j (u64 0)))
    (fun words => cmpInitialState words source)
    (fun words => words.length = destination.length) indices
    (by
      intro words hw j hj
      have hr := copy_step_run words source j (by rw [hw]; exact hd) hs
        (by rw [hw]; exact (hi j hj).1) (hi j hj).2
      exact hr)
    (by intro words hw j _; rw [List.length_set]; exact hw) destination rfl
  rw [List.forIn_map]
  simpa only [action, bind_assoc] using h

/-- The chunk-copy fold replaces precisely the visited positions. -/
theorem copy_fold_get (indices : List Nat) (source : List U64) :
    ∀ (destination : List U64), (∀ j ∈ indices, j < destination.length) → ∀ k : Nat,
    (indices.foldl (fun words j => words.set j (source.getD j (u64 0))) destination).getD k (u64 0) =
      if k ∈ indices then source.getD k (u64 0) else destination.getD k (u64 0) := by
  induction indices with
  | nil =>
    intro destination _ k
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons j indices ih =>
    intro destination hi k
    have hj := hi j List.mem_cons_self
    have hr := ih (destination.set j (source.getD j (u64 0)))
      (by intro i h; rw [List.length_set]; exact hi i (List.mem_cons_of_mem j h)) k
    rw [List.foldl_cons, hr]
    by_cases hk : k ∈ indices
    · rw [if_pos hk, if_pos (List.mem_cons_of_mem j hk)]
    · rw [if_neg hk, dequeWordGetSet destination j k _ hj]
      by_cases he : j = k
      · subst k
        rw [if_pos rfl, if_pos List.mem_cons_self]
      · have hnot : ¬ k ∈ j :: indices := by
          intro h
          rcases List.mem_cons.mp h with h | h
          · exact he h.symm
          · exact hk h
        rw [if_neg he, if_neg hnot]

/-- Distinctly allocated chunk copying factors through its bulk loop and final boundary word. -/
theorem copy_from_runs {N : Nat} (destination source : BitArray N)
    (dn sn : I64) (wordD wordS : U64) (state middle finished : State)
    (hsize : ¬ source.len > destination.len)
    (hcounts : ¬ dn < sn) (hpositive : (sn == int 0) = false)
    (hd : (mutableLength destination.chunks).run state = (.ok dn, state))
    (hs : (mutableLength source.chunks).run state = (.ok sn, state))
    (hloop : (forIn (intRange (int 1) (sn - int 1)) PUnit.unit (fun i _ => do
      let word ← mutableGet source.chunks i
      mutableSet destination.chunks word i
      pure (ForInStep.yield PUnit.unit))).run state = (.ok PUnit.unit, middle))
    (hrd : (mutableGet destination.chunks sn).run middle = (.ok wordD, middle))
    (hrs : (mutableGet source.chunks sn).run middle = (.ok wordS, middle))
    (hw : (mutableSet destination.chunks
      (if source.len == destination.len then wordS else
        or_int (and_int (not_int (maskEndArray source)) wordD)
          (and_int (maskEndArray source) wordS)) sn).run middle = (.ok (), finished)) :
    (bitArrayCopyto destination source).run state = (.ok destination, finished) := by
  simp only [bitArrayCopyto, hsize, ite_false, shape_run_bind, hd, hs, hcounts,
    hpositive, Bool.false_eq_true, hloop, shape_run_pure]
  by_cases he : (source.len == destination.len) = true
  · simp only [he, ite_true] at hw ⊢
    simp only [shape_run_bind, hrs, hw, shape_run_pure]
  · have he' : (source.len == destination.len) = false := Bool.eq_false_iff.mpr he
    simp only [he', Bool.false_eq_true, ite_false] at hw ⊢
    simp only [shape_run_bind, hrd, hrs, hw, shape_run_pure]

/-- The final boundary word combines the copied prefix with the untouched suffix. -/
def copy_boundary_word (destination source : List U64) (destinationLength sourceLength : I64) : U64 :=
  let j := source.length - 1
  if sourceLength == destinationLength then source.getD j (u64 0) else
    or_int (and_int (not_int (maskEnd sourceLength)) (destination.getD j (u64 0)))
      (and_int (maskEnd sourceLength) (source.getD j (u64 0)))

/-- The exact output chunks of the public no-offset copy operation. -/
def copy_output_words (destination source : List U64) (destinationLength sourceLength : I64) : List U64 :=
  ((List.range (source.length - 1)).foldl
    (fun words j => words.set j (source.getD j (u64 0))) destination).set
      (source.length - 1) (copy_boundary_word destination source destinationLength sourceLength)

/-- Public copying executes a complete chunk-level specification for any positive native source size. -/
theorem copy_words_run (destination source : List U64) (destinationLength sourceLength : I64)
    (hlen : sourceLength ≤ destinationLength)
    (hcount : source.length ≤ destination.length) (hpositive : 0 < source.length)
    (hbound : destination.length ≤ 9223372036854775807) :
    (bitArrayCopyto
      (⟨0, destinationLength, [destinationLength]⟩ : BitVector)
      (⟨1, sourceLength, [sourceLength]⟩ : BitVector)).run (cmpInitialState destination source) =
      (.ok ⟨0, destinationLength, [destinationLength]⟩,
        cmpInitialState (copy_output_words destination source destinationLength sourceLength) source) := by
  let j := source.length - 1
  let middle := (List.range j).foldl
    (fun words i => words.set i (source.getD i (u64 0))) destination
  have hsource : source.length ≤ 9223372036854775807 := by omega
  have hmid : middle.length = destination.length := copy_fold_length _ _ _
  have hj : j < source.length := by dsimp only [j]; omega
  have hlast : int ((j + 1 : Nat) : Int) = int source.length := congrArg int (by dsimp only [j]; omega)
  have hsub : int source.length - int 1 = int j := by
    rw [concat_int_sub]
    apply congrArg int
    dsimp only [j]
    omega
  have hrange := packedObserve_intRange j (by dsimp only [j]; omega)
  have hloop := copy_loop_run (List.range j) destination source hbound hsource
    (by intro i hi; have := List.mem_range.mp hi; exact ⟨by omega, by omega⟩)
  have hloop' :
      (forIn (intRange (int 1) (int source.length - int 1)) PUnit.unit (fun i _ => do
        let word ← mutableGet 1 i
        mutableSet 0 word i
        pure (ForInStep.yield PUnit.unit))).run (cmpInitialState destination source) =
          (.ok PUnit.unit, cmpInitialState middle source) := by
    rw [hsub, hrange]
    exact hloop
  have hgetD : middle.getD j (u64 0) = destination.getD j (u64 0) := by
    rw [copy_fold_get (List.range j) source destination
      (by intro i hi; have := List.mem_range.mp hi; omega) j]
    rw [if_neg (by simpa only [List.mem_range] using Nat.lt_irrefl j)]
  have hrd := cmp_initial_read_left middle source (by rw [hmid]; exact hbound) j (by rw [hmid]; omega)
  have hrs := cmp_initial_read_right middle source hsource j hj
  rw [List.getElem_eq_getD (fallback := u64 0), hgetD, hlast] at hrd
  rw [List.getElem_eq_getD (fallback := u64 0), hlast] at hrs
  have hw := copy_destination_set middle source j
    (copy_boundary_word destination source destinationLength sourceLength)
    (by rw [hmid]; exact hbound) (by rw [hmid]; omega)
  rw [hlast] at hw
  apply copy_from_runs _ _ (int destination.length) (int source.length)
    (destination.getD j (u64 0)) (source.getD j (u64 0))
    (cmpInitialState destination source) (cmpInitialState middle source) _
  · change ¬ sourceLength.val > destinationLength.val
    change sourceLength.val ≤ destinationLength.val at hlen
    omega
  · change ¬ (int destination.length).val < (int source.length).val
    rw [packedInt_val destination.length hbound, packedInt_val source.length hsource]
    omega
  · apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val source.length hsource] at hv
    change (source.length : Int) = 0 at hv
    omega
  · exact (cmp_initial_lengths destination source).1
  · exact (cmp_initial_lengths destination source).2
  · exact hloop'
  · exact hrd
  · exact hrs
  · exact hw
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Prefix replacement keeps the original destination length when the source fits. -/
theorem copy_overlay_length (destination source : List Bool)
    (hsize : source.length ≤ destination.length) :
    (source ++ destination.drop source.length).length = destination.length := by
  simp only [List.length_append, List.length_drop]
  omega

/-- Logical prefix replacement copies exactly the source positions. -/
theorem copy_overlay_get (destination source : List Bool) (k : Nat) :
    (source ++ destination.drop source.length).getD k false =
      if k < source.length then source.getD k false else destination.getD k false := by
  by_cases hk : k < source.length
  · rw [if_pos hk]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  · rw [if_neg hk]
    have hle : source.length ≤ k := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle,
      List.getElem?_drop, Nat.add_sub_of_le hle]

/-- Each complete copied chunk before the boundary equals its source encoding. -/
theorem copy_overlay_early_word (destination source : List Bool) (chunk : Nat)
    (hchunk : chunk < wordCount source.length - 1) :
    packedPrefix (source ++ destination.drop source.length) chunk 64 =
      packedPrefix source chunk 64 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ chunk bit hb, packedWord_bit _ chunk bit hb,
    copy_overlay_get]
  rw [if_pos (by unfold wordCount at hchunk; omega)]

/-- Every destination chunk after the source boundary is unchanged. -/
theorem copy_overlay_late_word (destination source : List Bool) (chunk : Nat)
    (hchunk : wordCount source.length ≤ chunk) :
    packedPrefix (source ++ destination.drop source.length) chunk 64 =
      packedPrefix destination chunk 64 := by
  apply packedBit_ext
  intro bit hb
  rw [packedWord_bit _ chunk bit hb, packedWord_bit _ chunk bit hb,
    copy_overlay_get]
  rw [if_neg (by unfold wordCount at hchunk; omega)]

/-- The final packed source mask selects exactly the prefix replacement boundary. -/
theorem copy_overlay_boundary_word (destination source : List Bool)
    (hpos : 0 < source.length) (hn : source.length ≤ 9223372036854775807) :
    or_int
      (and_int (not_int (maskEnd (int source.length)))
        (packedPrefix destination (wordCount source.length - 1) 64))
      (and_int (maskEnd (int source.length))
        (packedPrefix source (wordCount source.length - 1) 64)) =
      packedPrefix (source ++ destination.drop source.length)
        (wordCount source.length - 1) 64 := by
  apply packedBit_ext
  intro bit hb
  rw [packedBit_or, concat_and_bit, concat_and_bit, concat_not_bit _ bit hb,
    packedMask_last_bit source.length bit hpos hn,
    packedWord_bit _ _ bit hb, packedWord_bit _ _ bit hb,
    packedWord_bit _ _ bit hb, copy_overlay_get]
  by_cases hi : (wordCount source.length - 1) * 64 + bit < source.length
  · simp only [hi, decide_true, Bool.not_true, Bool.false_and, Bool.true_and,
      Bool.false_or, ite_true]
  · simp only [hi, decide_false, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.or_false, ite_false]


/-- The public final-word computation is the encoding of logical prefix replacement. -/
theorem copy_boundary_encoding (destination source : List Bool)
    (hp : 0 < source.length) (hsize : source.length ≤ destination.length)
    (hn : destination.length ≤ 9223372036854775807) :
    copy_boundary_word (encodeBits destination) (encodeBits source)
      (int destination.length) (int source.length) =
      packedPrefix (source ++ destination.drop source.length)
        (wordCount source.length - 1) 64 := by
  have hs : source.length ≤ 9223372036854775807 := by omega
  have hc : wordCount source.length - 1 < wordCount source.length := by unfold wordCount; omega
  have hd : wordCount source.length - 1 < wordCount destination.length := by unfold wordCount at *; omega
  unfold copy_boundary_word
  rw [packedEncoded_length]
  dsimp only
  rw [dequeEncodedGet source _ hc, dequeEncodedGet destination _ hd]
  by_cases he : source.length = destination.length
  · rw [he, beq_self_eq_true, if_pos rfl]
    rw [List.drop_length, List.append_nil]
  · have hb : (int source.length == int destination.length) = false :=
      beq_eq_false_iff_ne.mpr (concat_native_sizes_ne _ _ hs hn he)
    rw [hb, if_neg (by decide)]
    exact copy_overlay_boundary_word destination source hp hs

/-- The complete copied chunk vector encodes the source followed by the untouched suffix. -/
theorem copy_output_encoding (destination source : List Bool)
    (hp : 0 < source.length) (hsize : source.length ≤ destination.length)
    (hn : destination.length ≤ 9223372036854775807) :
    copy_output_words (encodeBits destination) (encodeBits source)
      (int destination.length) (int source.length) =
      encodeBits (source ++ destination.drop source.length) := by
  have hlogical := copy_overlay_length destination source hsize
  have hlast : (encodeBits source).length - 1 < (encodeBits destination).length := by
    rw [packedEncoded_length, packedEncoded_length]
    unfold wordCount
    omega
  have hlastWord : wordCount source.length - 1 < wordCount destination.length := by
    rw [packedEncoded_length, packedEncoded_length] at hlast
    exact hlast
  apply List.ext_getElem
  · rw [copy_output_words, List.length_set, copy_fold_length,
      packedEncoded_length, packedEncoded_length, hlogical]
  · intro k hk hk'
    have hkdest : k < wordCount destination.length := by
      rw [packedEncoded_length, hlogical] at hk'
      exact hk'
    rw [List.getElem_eq_getD (u64 0), List.getElem_eq_getD (u64 0)]
    rw [copy_output_words, dequeWordGetSet _ _ _ _
      (by rw [copy_fold_length]; exact hlast)]
    rw [dequeEncodedGet _ k (by rw [hlogical]; exact hkdest)]
    by_cases he : (encodeBits source).length - 1 = k
    · rw [if_pos he]
      rw [← he, packedEncoded_length]
      exact copy_boundary_encoding destination source hp hsize hn
    · rw [if_neg he, copy_fold_get _ _ _
        (by intro j hj; have := List.mem_range.mp hj; omega) k]
      by_cases hi : k < (encodeBits source).length - 1
      · rw [if_pos (List.mem_range.mpr hi), dequeEncodedGet source k
          (by rw [packedEncoded_length] at hi; omega)]
        exact (copy_overlay_early_word destination source k
          (by rw [packedEncoded_length] at hi; exact hi)).symm
      · rw [if_neg (by simpa only [List.mem_range] using hi), dequeEncodedGet destination k hkdest]
        exact (copy_overlay_late_word destination source k
          (by rw [packedEncoded_length] at hi he; omega)).symm

/-- With no source chunks, copyto returns the destination without reading or writing a word. -/
theorem copy_empty_from {N : Nat} (destination source : BitArray N) (state : State) (count : I64)
    (hlen : ¬ source.len > destination.len) (hcount : ¬ count < int 0)
    (hd : (mutableLength destination.chunks).run state = (.ok count, state))
    (hs : (mutableLength source.chunks).run state = (.ok (int 0), state)) :
    (bitArrayCopyto destination source).run state = (.ok destination, state) := by
  simp only [bitArrayCopyto, hlen, ite_false, shape_run_bind, hd, hs, hcount,
    beq_self_eq_true, ite_true, shape_run_pure]

/-- Native no-offset copy reaches the exact source-prefix and destination-suffix encoding. -/
theorem copy_native_run (destination source : List Bool)
    (hsize : source.length ≤ destination.length)
    (hd : destination.length ≤ 9223372036854775807) :
    (bitArrayCopyto
      (⟨0, int destination.length, [int destination.length]⟩ : BitArray 1)
      (⟨1, int source.length, [int source.length]⟩ : BitArray 1)).run
      (MutableMemory.initialMany [(encodeBits destination).map some, (encodeBits source).map some]) =
      (.ok ⟨0, int destination.length, [int destination.length]⟩,
        MutableMemory.initialMany
          [(encodeBits (source ++ destination.drop source.length)).map some, (encodeBits source).map some]) := by
  let d : BitArray 1 := ⟨0, int destination.length, [int destination.length]⟩
  let s : BitArray 1 := ⟨1, int source.length, [int source.length]⟩
  let initial := cmpInitialState (encodeBits destination) (encodeBits source)
  have hs : source.length ≤ 9223372036854775807 := by omega
  have hdwords := packedEncoded_lengthBound destination hd
  have hlen : int source.length ≤ int destination.length := by
    change (int source.length).val ≤ (int destination.length).val
    rw [packedInt_val source.length hs, packedInt_val destination.length hd]
    omega
  by_cases hempty : source = []
  · have hz : source.length = 0 := by rw [hempty]; rfl
    have hzeroCount : int (encodeBits source).length = int 0 := by
      rw [packedEncoded_length, hz]
      rfl
    have hsourceRead := (cmp_initial_lengths (encodeBits destination) (encodeBits source)).2
    have hsourceZero := hsourceRead.trans
      (congrArg (fun n : I64 => ((Except.ok n : Except Error I64), initial)) hzeroCount)
    have hlenNeg : ¬ int source.length > int destination.length := by
      change ¬ (int destination.length).val < (int source.length).val
      change (int source.length).val ≤ (int destination.length).val at hlen
      omega
    have hcountNeg : ¬ int (encodeBits destination).length < int 0 := by
      change ¬ (int (encodeBits destination).length).val < (int 0).val
      rw [packedInt_val (encodeBits destination).length hdwords]
      change ¬ (_ : Int) < 0
      omega
    have hrun := copy_empty_from d s initial (int (encodeBits destination).length)
      hlenNeg hcountNeg
      (cmp_initial_lengths (encodeBits destination) (encodeBits source)).1 hsourceZero
    have hexpected : destination = source ++ destination.drop source.length := by
      rw [hempty]
      rfl
    exact hrun.trans (congrArg (fun values : List Bool =>
      ((Except.ok d : Except Error (BitArray 1)), cmpInitialState (encodeBits values) (encodeBits source))) hexpected)
  · have hp : 0 < source.length := by
      have : source.length ≠ 0 := fun h => hempty (List.length_eq_zero_iff.mp h)
      omega
    have hwords : (encodeBits source).length ≤ (encodeBits destination).length := by
      rw [packedEncoded_length, packedEncoded_length]
      unfold wordCount
      omega
    have hposwords : 0 < (encodeBits source).length := by
      rw [packedEncoded_length]
      unfold wordCount
      omega
    have hrun := copy_words_run (encodeBits destination) (encodeBits source)
      (int destination.length) (int source.length) hlen hwords hposwords hdwords
    exact hrun.trans (congrArg (fun words : List U64 =>
      ((Except.ok d : Except Error (BitArray 1)), cmpInitialState words (encodeBits source)))
      (copy_output_encoding destination source hp hsize hd))

/-- The exact frozen copyto observation holds whenever both Boolean lists have native lengths. -/
theorem copyto_native_bounded (destination source : List Bool)
    (hd : destination.length ≤ 9223372036854775807)
    (hs : source.length ≤ 9223372036854775807) :
    let d : BitArray 1 := ⟨0, int destination.length, [int destination.length]⟩
    let s : BitArray 1 := ⟨1, int source.length, [int source.length]⟩
    let state := MutableMemory.initialMany [(encodeBits destination).map some, (encodeBits source).map some]
    let result := (bitArrayCopyto d s).run state
    if source.length ≤ destination.length then
      match result.1 with
      | .ok output => bitValues result.2 output = source ++ destination.drop source.length
      | .error _ => False
    else (match result.1 with | .error .bounds => True | _ => False) := by
  dsimp only
  by_cases hsize : source.length ≤ destination.length
  · rw [if_pos hsize]
    erw [copy_native_run destination source hsize hd]
    change bitValues
      (MutableMemory.initialMany
        [(encodeBits (source ++ destination.drop source.length)).map some, (encodeBits source).map some])
      (⟨0, int destination.length, [int destination.length]⟩ : BitArray 1) =
        source ++ destination.drop source.length
    have hout := copy_overlay_length destination source hsize
    apply scalar_bitValues_contents
    · rw [hout]; exact hd
    · change int destination.length = int (source ++ destination.drop source.length).length
      rw [hout]
    · apply equalityInitialLeft
      rw [packedEncoded_length, hout]
      have hbound := packedEncoded_lengthBound destination hd
      change (encodeBits destination).length ≤ 9223372036854775807 at hbound
      simpa only [packedEncoded_length] using hbound
  · rw [if_neg hsize]
    have hgt : int source.length > int destination.length := by
      change (int destination.length).val < (int source.length).val
      rw [packedInt_val source.length hs, packedInt_val destination.length hd]
      omega
    erw [copy_short_destination
      (⟨0, int destination.length, [int destination.length]⟩ : BitArray 1)
      (⟨1, int source.length, [int source.length]⟩ : BitArray 1)
      (MutableMemory.initialMany [(encodeBits destination).map some, (encodeBits source).map some]) hgt]
    trivial
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

/-- An index iterator with no first element returns the original vector and heap. -/
theorem copy_delete_indices_none {I S : Type} (iterate : I → Option (I64 × S))
    (next : I → S → Option (I64 × S)) (check : BitVector → I64 → BitMutationM Unit)
    (isBool : I64 → Bool) (toInt : I64 → I64) (B : BitVector) (inds : I) (state : State)
    (hfirst : iterate inds = none) :
    (bitVectorDeleteAtIndices iterate next check isBool toInt B inds).run state = (.ok B, state) := by
  simp only [bitVectorDeleteAtIndices, hfirst]
  rfl

/-- An all-false mask returns the original vector immediately after its read-only first search. -/
theorem copy_delete_mask_none {I : Type} (length : I → I64)
    (first : I → BitMutationM (Option I64)) (next : I → I64 → BitMutationM (Option I64))
    (check : BitVector → I64 → BitMutationM Unit) (B : BitVector) (mask : I) (state : State)
    (hsize : length mask = B.len)
    (hfirst : (first mask).run state = (.ok none, state)) :
    (bitVectorDeleteAtBoolMask length first next check B mask).run state = (.ok B, state) := by
  simp only [bitVectorDeleteAtBoolMask, hsize, bne_self_eq_false, Bool.false_eq_true,
    ite_false, shape_run_bind, hfirst, Option.isNone_none, ite_true, shape_run_pure]

/-- The frozen sorted-index deletion observation holds for every bounded vector and an empty index list. -/
theorem copy_delete_empty_indices_observation (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    let B := vectorBits xs
    let iterate : List I64 → Option (I64 × Nat) := fun values => values.head?.map fun value => (value, 0)
    let next : List I64 → Nat → Option (I64 × Nat) := fun values index => values[index + 1]?.map fun value => (value, index + 1)
    let check : BitVector → I64 → BitMutationM Unit := fun _ i =>
      if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then pure () else throw .bounds
    let result := (bitVectorDeleteAtIndices iterate next check (fun _ => false) id B []).run (initWords (encodeBits xs))
    let expected := (List.range xs.length).filterMap fun i =>
      if ([] : List I64).contains (int (Int.ofNat (i+1))) then none else some (xs.getD i false)
    match result.1 with | .ok output => bitValues result.2 output = expected | .error _ => False := by
  dsimp only
  rw [copy_delete_indices_none _ _ _ _ _ _ _ _ rfl]
  change bitValues (initWords (encodeBits xs)) (vectorBits xs) = _
  erw [scalar_bits_initial xs [int xs.length] hn]
  simp only [List.contains_nil, Bool.false_eq_true, ite_false, List.filterMap_eq_map']
  simpa only [Nat.sub_self, List.replicate_zero, List.append_nil] using
    (packedGrouping_getDPadded xs false xs.length (Nat.le_refl _)).symm


/-- A replicated false mask has no selected positions, including defaulted lookups. -/
theorem copy_false_mask_indices (n : Nat) :
    (List.range n).filter (fun i => (List.replicate n false).getD i false) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i _
  rw [JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2.concat_getD_replicate_same]
  decide

/-- The all-false mask action is the pure return of its input header. -/
theorem copy_delete_false_mask_action (xs : List Bool) :
    copy_delete_mask_action xs (List.replicate xs.length false) = pure (vectorBits xs) := by
  unfold copy_delete_mask_action
  simp only [List.length_replicate, copy_false_mask_indices, List.head?_nil, Option.map_none,
    List.filter_nil, bitVectorDeleteAtBoolMask, vectorBits, bne_self_eq_false,
    Bool.false_eq_true, ite_false, pure_bind, Option.isNone_none, ite_true]

/-- A concrete successful deletion run transports its output contract without unfolding the action. -/
theorem copy_delete_observation_from_run (action : BitMutationM BitVector)
    (s outState : State) (out : BitVector) (expected : List Bool)
    (hrun : action.run s = (.ok out, outState))
    (hout : bitValues outState out = expected) :
    match (action.run s).1 with
    | .ok output => bitValues (action.run s).2 output = expected
    | .error _ => False := by
  rw [hrun]
  exact hout

/-- All-false deletion has the exact successful output requested by the frozen mask target. -/
theorem copy_delete_false_mask_success (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807) :
    ∃ output outState,
      (copy_delete_mask_action xs (List.replicate xs.length false)).run
        (initWords (encodeBits xs)) = (.ok output, outState) ∧
      bitValues outState output = (List.range xs.length).filterMap fun i =>
        if (List.replicate xs.length false).getD i false then none else some (xs.getD i false) := by
  let expected := (List.range xs.length).filterMap fun i =>
    if (List.replicate xs.length false).getD i false then none else some (xs.getD i false)
  have he : xs = expected := by
    simp only [expected, JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2.concat_getD_replicate_same,
      Bool.false_eq_true, ite_false, List.filterMap_eq_map']
    simpa only [Nat.sub_self, List.replicate_zero, List.append_nil] using
      (packedGrouping_getDPadded xs false xs.length (Nat.le_refl _)).symm
  have hrun : (copy_delete_mask_action xs (List.replicate xs.length false)).run
      (initWords (encodeBits xs)) = (.ok (vectorBits xs), initWords (encodeBits xs)) :=
    congrArg (fun action : BitMutationM BitVector => action.run (initWords (encodeBits xs)))
      (copy_delete_false_mask_action xs)
  have hbits : bitValues (initWords (encodeBits xs)) (vectorBits xs) = expected :=
    (scalar_bits_initial xs [int xs.length] hn).trans he
  exact ⟨vectorBits xs, initWords (encodeBits xs), hrun, hbits⟩
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

/-- The full pair of successful concatenation contracts in the frozen one-word domain. -/
theorem copy_concatenation_single_chunk (vectors : List (List Bool))
    (hne : vectors ≠ []) (hcount : vectors.length ≤ 9223372036854775807)
    (hbound : vectors.flatten.length ≤ 64) :
    ∃ (vertical : BitVector) (verticalState : State),
      (bitArrayVcatVectors
        ((vectors.zip (List.range vectors.length)).map (fun entry =>
          (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
        (fun n => Round5.Round2.allocateBitArrayModel [n])).run
        (MutableMemory.initialMany (vectors.map fun xs => (encodeBits xs).map some)) =
          (.ok vertical, verticalState) ∧
      vertical.dims = [int vectors.flatten.length] ∧
      bitValues verticalState vertical = vectors.flatten ∧
      Round5.Round2.PackedInvariant verticalState vertical ∧
      ((∀ xs ∈ vectors, xs.length = (vectors.headD []).length) →
        ∃ (horizontal : BitMatrix) (horizontalState : State),
          (bitArrayHcatVectors
            ((vectors.zip (List.range vectors.length)).map (fun entry =>
              (⟨entry.2, int entry.1.length, [int entry.1.length]⟩ : BitVector)))
            (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run
            (MutableMemory.initialMany (vectors.map fun xs => (encodeBits xs).map some)) =
              (.ok horizontal, horizontalState) ∧
          horizontal.dims = [int (vectors.headD []).length, int vectors.length] ∧
          bitValues horizontalState horizontal = vectors.flatten ∧
          Round5.Round2.PackedInvariant horizontalState horizontal) := by
  obtain ⟨v, sv, hv, hd, hb, hi⟩ := concat_vcat_small_correct vectors hbound
  refine ⟨v, sv, hv, hd, hb, hi, ?_⟩
  intro hrect
  exact concat_hcat_small_correct vectors hne hcount hbound hrect

/-- Matrix vcat has the requested shape, column-major contents, and padding whenever its output fits one word. -/
theorem copy_matrix_vcat_single_chunk (columns : Nat) (inputs : List (Nat × List Bool))
    (hne : inputs ≠ []) (hcount : inputs.length ≤ 9223372036854775807)
    (hshape : ∀ input ∈ inputs, input.2.length = input.1 * columns)
    (hrows : inputs.foldl (fun rows input => rows + input.1) 0 ≤ 9223372036854775807)
    (hcols : columns ≤ 9223372036854775807)
    (hbound : inputs.foldl (fun rows input => rows + input.1) 0 * columns ≤ 64) :
    ∃ (out : BitMatrix) (finished : State),
      (bitArrayVcatMatrices
        ((inputs.zip (List.range inputs.length)).map (fun entry =>
          (⟨entry.2, int entry.1.2.length, [int entry.1.1, int columns]⟩ : BitMatrix)))
        (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
        Round5.Round2.allocateMatrixModel).run
        (MutableMemory.initialMany (inputs.map fun input => (encodeBits input.2).map some)) = (.ok out, finished) ∧
      out.dims = [int ((inputs.foldl (fun rows input => rows + input.1) 0 : Nat) : Int), int columns] ∧
      bitValues finished out = (List.range columns).flatMap (fun column => inputs.flatMap (fun input =>
        (List.range input.1).map (fun row => input.2.getD (row + column * input.1) false))) ∧
      Round5.Round2.PackedInvariant finished out := by
  exact concat_matrix_vcat_small_correct columns inputs hne hcount hshape hrows hcols hbound
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The exact frozen sorted-index deletion action, with its input-dependent public bounds check. -/
@[irreducible] def copy_delete_indices_action (xs : List Bool) (indices : List I64) : BitMutationM BitVector :=
  let iterate : List I64 → Option (I64 × Nat) := fun values => values.head?.map fun value => (value, 0)
  let next : List I64 → Nat → Option (I64 × Nat) := fun values index =>
    values[index + 1]?.map fun value => (value, index + 1)
  let check : BitVector → I64 → BitMutationM Unit := fun _ i =>
    if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then pure () else throw .bounds
  bitVectorDeleteAtIndices iterate next check (fun _ => false) id (vectorBits xs) indices

/-- With one selected index, the iterator loop is empty and the remaining actions are a suffix copy and cleanup. -/
theorem copy_delete_singleton_from (B output : BitVector) (i count : I64)
    (check : BitVector → I64 → BitMutationM Unit) (s copied outState : State)
    (hcheck : (check B i).run s = (.ok (), s))
    (hcopy : ((if i + int 1 ≤ B.len then
        copyChunks B.chunks i B.chunks (i + int 1) (B.len - (i + int 1) + int 1)
      else pure ()) : BitMutationM Unit).run s = (.ok (), copied))
    (hlength : (mutableLength B.chunks).run copied = (.ok count, copied))
    (hfinish : (rangeSingleFinish B (B.len - int 1) count).run copied = (.ok output, outState)) :
    (bitVectorDeleteAtIndices
      (fun (values : List I64) => values.head?.map fun value => (value, 0))
      (fun (values : List I64) (index : Nat) => values[index + 1]?.map fun value => (value, index + 1))
      check (fun _ => false) id B [i]).run s = (.ok output, outState) := by
  unfold bitVectorDeleteAtIndices
  simp only [List.head?_cons, Option.map_some, pure_bind, id_eq,
    Bool.false_eq_true, ite_false, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_none]
  rw [resizeFrontLoopUnfold]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, pure_bind]
  simp only [shape_run_bind, hcheck]
  change ((do
    if i + int 1 ≤ B.len then
      copyChunks B.chunks i B.chunks (i + int 1) (B.len - (i + int 1) + int 1)
    let count ← mutableLength B.chunks
    rangeSingleFinish B (B.len - int 1) count) : BitMutationM BitVector).run s = _
  have htail := concat_bind_success (mutableLength B.chunks)
    (rangeSingleFinish B (B.len - int 1)) copied copied outState count output hlength hfinish
  by_cases hq : i + int 1 ≤ B.len
  · simp only [hq, ite_true] at hcopy ⊢
    exact concat_bind_success _
      (fun _ : Unit => mutableLength B.chunks >>= rangeSingleFinish B (B.len - int 1))
      s copied outState () output hcopy htail
  · simp only [hq, ite_false, shape_run_pure] at hcopy ⊢
    have he : s = copied := congrArg Prod.snd hcopy
    rw [he]
    exact htail

/-- The optional singleton-deletion suffix move realizes the one-word deletion formula, even at the final bit. -/
theorem copy_delete_singleton_copy (xs : List Bool) (p spare : Nat)
    (hp : p < xs.length) (hn : xs.length ≤ 64) :
    ((if int ((p + 1 : Nat) : Int) + int 1 ≤ int xs.length then
        copyChunks 0 (int ((p + 1 : Nat) : Int)) 0 (int ((p + 1 : Nat) : Int) + int 1)
          (int xs.length - (int ((p + 1 : Nat) : Int) + int 1) + int 1)
      else pure ()) : BitMutationM Unit).run
      (dequeWordStore [packedPrefix xs 0 64] spare) =
      (.ok (), dequeWordStore
        [rangeSingleCopyWord (packedPrefix xs 0 64) p (p + 1) (xs.length - (p + 1))] spare) := by
  have hinc : int ((p + 1 : Nat) : Int) + int 1 = int ((p + 1 + 1 : Nat) : Int) := by
    rw [packedInt_add]
    exact congrArg int (by omega)
  have hcount : int xs.length - (int ((p + 1 : Nat) : Int) + int 1) + int 1 =
      int ((xs.length - (p + 1) : Nat) : Int) := by
    rw [hinc, dequeIntSub, packedInt_add]
    exact congrArg int (by omega)
  have hcond : (int ((p + 1 : Nat) : Int) + int 1 ≤ int xs.length) ↔ p + 1 < xs.length := by
    rw [hinc]
    change (int ((p + 1 + 1 : Nat) : Int)).val ≤ (int xs.length).val ↔ _
    rw [packedInt_val (p + 1 + 1) (by omega), packedInt_val xs.length (by omega)]
    omega
  by_cases ht : p + 1 < xs.length
  · rw [if_pos (hcond.mpr ht), hcount, hinc]
    exact rangeSingleCopyStore (packedPrefix xs 0 64) p (p + 1) (xs.length - (p + 1)) spare
      (by omega) (by omega)
  · rw [if_neg (fun h => ht (hcond.mp h))]
    have hz : xs.length - (p + 1) = 0 := by omega
    rw [hz, rangeSingleCopyZero _ p (p + 1) (by omega) (by omega)]
    rfl

/-- A nonempty singleton-deletion result is stored as the exact packed prefix followed by the remaining suffix. -/
theorem copy_delete_singleton_finish (xs : List Bool) (p spare : Nat)
    (hpos : 2 ≤ xs.length) (hp : p < xs.length) (hn : xs.length ≤ 64) :
    (rangeSingleFinish (vectorBits xs) (int ((xs.length - 1 : Nat) : Int)) (int 1)).run
      (dequeWordStore
        [rangeSingleCopyWord (packedPrefix xs 0 64) p (p + 1) (xs.length - (p + 1))] spare) =
      (.ok {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)},
        dequeWordStore [packedPrefix (xs.take p ++ xs.drop (p + 1)) 0 64] spare) := by
  let word := rangeSingleCopyWord (packedPrefix xs 0 64) p (p + 1) (xs.length - (p + 1))
  have he : and_int word (maskEnd (int ((xs.length - 1 : Nat) : Int))) =
      packedPrefix (xs.take p ++ xs.drop (p + 1)) 0 64 := by
    have h := rangeSingleDeleteWord xs p (p + 1) (by omega) (by omega) hn (by omega)
    simpa only [Nat.add_sub_cancel_left] using h
  have hlength : (mutableLength 0).run (dequeWordStore [word] spare) =
      (.ok (int 1), dequeWordStore [word] spare) := dequeWordLength [word] spare
  have hread : (mutableGet 0 (int 1)).run (dequeWordStore [word] spare) =
      (.ok word, dequeWordStore [word] spare) := by
    simpa only [List.getD_cons_zero, Nat.zero_add, Int.ofNat_one] using
      dequeWordRead [word] spare 0 (by simp only [List.length_singleton]; decide)
        (by simp only [List.length_singleton]; decide)
  have hwrite : (mutableSet 0 (and_int word (maskEnd (int ((xs.length - 1 : Nat) : Int)))) (int 1)).run
      (dequeWordStore [word] spare) =
      (.ok (), dequeWordStore [packedPrefix (xs.take p ++ xs.drop (p + 1)) 0 64] spare) := by
    have h := dequeWordSet [word] spare 0 (and_int word (maskEnd (int ((xs.length - 1 : Nat) : Int))))
      (by simp only [List.length_singleton]; decide) (by simp only [List.length_singleton]; decide)
    simpa only [List.set_cons_zero, Nat.zero_add, Int.ofNat_one, he] using h
  exact rangeSingleFinishPositive (vectorBits xs) (xs.length - 1) word _ _
    (by omega) (by omega) hlength hread hwrite

/-- Every singleton deletion in a vector of two to sixty-four bits runs to its exact logical encoding. -/
theorem copy_delete_singleton_single_chunk_run (xs : List Bool) (p : Nat)
    (hpos : 2 ≤ xs.length) (hp : p < xs.length) (hn : xs.length ≤ 64) :
    (copy_delete_indices_action xs [int ((p + 1 : Nat) : Int)]).run
      (initWords (encodeBits xs)) =
      (.ok {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)},
        initWords (encodeBits (xs.take p ++ xs.drop (p + 1)))) := by
  let B := vectorBits xs
  let i := int ((p + 1 : Nat) : Int)
  let initial := dequeWordStore [packedPrefix xs 0 64] 32
  let copied := dequeWordStore
    [rangeSingleCopyWord (packedPrefix xs 0 64) p (p + 1) (xs.length - (p + 1))] 32
  let final := dequeWordStore [packedPrefix (xs.take p ++ xs.drop (p + 1)) 0 64] 32
  let check : BitVector → I64 → BitMutationM Unit := fun _ i =>
    if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then pure () else throw .bounds
  have hi : int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) := by
    change (int 1).val ≤ (int ((p + 1 : Nat) : Int)).val ∧
      (int ((p + 1 : Nat) : Int)).val ≤ (int xs.length).val
    rw [packedInt_val (p + 1) (by omega), packedInt_val xs.length (by omega)]
    change (1 : Int) ≤ (p + 1 : Nat) ∧ ((p + 1 : Nat) : Int) ≤ (xs.length : Int)
    omega
  have hc : (check B i).run initial = (.ok (), initial) := by
    simp only [check, hi, true_and, ite_true, shape_run_pure]
  have hlen : (mutableLength B.chunks).run copied = (.ok (int 1), copied) :=
    dequeWordLength _ 32
  have hnativ : B.len - int 1 = int ((xs.length - 1 : Nat) : Int) :=
    frontPopLengthPred xs.length (by omega)
  have hfin : (rangeSingleFinish B (B.len - int 1) (int 1)).run copied =
      (.ok {B with len := int ((xs.length - 1 : Nat) : Int)}, final) := by
    rw [hnativ]
    exact copy_delete_singleton_finish xs p 32 hpos hp hn
  have hrun := copy_delete_singleton_from B {B with len := int ((xs.length - 1 : Nat) : Int)} i (int 1)
    check initial copied final hc (copy_delete_singleton_copy xs p 32 hp hn) hlen hfin
  have hsource : initial = initWords (encodeBits xs) := by
    rw [rangeSingleEncoding xs (by omega) hn]
    exact dequeWordStoreInitial _
  have hlogical : (xs.take p ++ xs.drop (p + 1)).length = xs.length - 1 := by
    have h := rangeSingleLogicalLength xs p (p + 1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel_left] using h
  have hfinal : final = initWords (encodeBits (xs.take p ++ xs.drop (p + 1))) := by
    rw [rangeSingleEncoding _ (by rw [hlogical]; omega) (by rw [hlogical]; omega)]
    exact dequeWordStoreInitial _
  have haction : (copy_delete_indices_action xs [i]).run initial =
      (.ok {B with len := int ((xs.length - 1 : Nat) : Int)}, final) := by
    unfold copy_delete_indices_action
    exact hrun
  exact (congrArg (fun state => (copy_delete_indices_action xs [i]).run state) hsource.symm).trans
    (haction.trans (congrArg (fun state =>
      ((Except.ok {B with len := int ((xs.length - 1 : Nat) : Int)} : Except Error BitVector), state)) hfinal))

/-- Filtering the natural enumeration at one position is exactly list deletion at that position. -/
theorem copy_filterMap_remove_index {α : Type} (xs : List α) (fallback : α) (p : Nat)
    (hp : p < xs.length) :
    (List.range xs.length).filterMap (fun i => if i = p then none else some (xs.getD i fallback)) =
      xs.take p ++ xs.drop (p + 1) := by
  induction xs generalizing p with
  | nil => simp only [List.length_nil] at hp; omega
  | cons head tail ih =>
    cases p with
    | zero =>
      simp only [List.length_cons, List.range_succ_eq_map, List.filterMap_cons,
        ite_true, List.filterMap_map, Function.comp_def, Nat.succ_ne_zero,
        ite_false, List.getD_cons_succ, List.filterMap_eq_map', List.take_zero,
        Nat.zero_add, List.drop_succ_cons, List.drop_zero, List.nil_append]
      simpa only [Nat.sub_self, List.replicate_zero, List.append_nil] using
        packedGrouping_getDPadded tail fallback tail.length (Nat.le_refl _)
    | succ p =>
      simp only [List.length_cons, List.range_succ_eq_map, List.filterMap_cons,
        Nat.zero_ne_add_one, ite_false, List.getD_cons_zero, List.filterMap_map,
        Function.comp_def, Nat.succ.injEq, List.getD_cons_succ,
        List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih p (by simp only [List.length_cons] at hp; omega)

/-- Native one-based singleton membership agrees with natural zero-based index equality. -/
theorem copy_native_singleton_contains (p i : Nat)
    (hp : p + 1 ≤ 9223372036854775807) (hi : i + 1 ≤ 9223372036854775807) :
    ([int ((p + 1 : Nat) : Int)] : List I64).contains (int ((i + 1 : Nat) : Int)) = decide (i = p) := by
  by_cases he : i = p
  · subst i
    simp only [List.contains_cons, beq_self_eq_true, Bool.true_or, decide_true]
  · have hne := concat_native_sizes_ne (i + 1) (p + 1) hi hp (by omega)
    simp only [List.contains_cons, List.contains_nil, Bool.or_false,
      beq_eq_false_iff_ne.mpr hne, he, decide_false]

/-- Pointwise equality on a list suffices to identify its filtered map. -/
theorem copy_filterMap_congr {α β : Type} (items : List α) (f g : α → Option β)
    (h : ∀ item ∈ items, f item = g item) : items.filterMap f = items.filterMap g := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.filterMap_cons, h head List.mem_cons_self]
    rw [ih (fun item hi => h item (List.mem_cons_of_mem head hi))]

/-- The exact expected list in the frozen target specializes to singleton deletion. -/
theorem copy_singleton_expected (xs : List Bool) (p : Nat)
    (hp : p < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (List.range xs.length).filterMap (fun i =>
      if ([int ((p + 1 : Nat) : Int)] : List I64).contains (int (Int.ofNat (i+1))) then none
      else some (xs.getD i false)) = xs.take p ++ xs.drop (p + 1) := by
  have hfun : ∀ i ∈ List.range xs.length,
      (if ([int ((p + 1 : Nat) : Int)] : List I64).contains (int (Int.ofNat (i+1))) then none
       else some (xs.getD i false)) = (if i = p then none else some (xs.getD i false)) := by
    intro i hi
    erw [copy_native_singleton_contains p i (by omega) (by have := List.mem_range.mp hi; omega)]
    simp only [decide_eq_true_eq]
  calc
    _ = (List.range xs.length).filterMap (fun i => if i = p then none else some (xs.getD i false)) := by
      exact copy_filterMap_congr _ _ _ hfun
    _ = _ := copy_filterMap_remove_index xs false p hp

/-- Singleton deletion satisfies the frozen expected-list contract and preserves the packed invariant in the one-word domain. -/
theorem copy_delete_singleton_single_chunk_correct (xs : List Bool) (p : Nat)
    (hpos : 2 ≤ xs.length) (hp : p < xs.length) (hn : xs.length ≤ 64) :
    ∃ output outState,
      (copy_delete_indices_action xs [int ((p + 1 : Nat) : Int)]).run
        (initWords (encodeBits xs)) = (.ok output, outState) ∧
      bitValues outState output = (List.range xs.length).filterMap (fun i =>
        if ([int ((p + 1 : Nat) : Int)] : List I64).contains (int (Int.ofNat (i+1))) then none
        else some (xs.getD i false)) ∧
      Round5.Round2.PackedInvariant outState output := by
  let ys := xs.take p ++ xs.drop (p + 1)
  let output : BitVector := {vectorBits xs with len := int ((xs.length - 1 : Nat) : Int)}
  let outState := initWords (encodeBits ys)
  have hlen : ys.length = xs.length - 1 := by
    have h := rangeSingleLogicalLength xs p (p + 1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel_left] using h
  have hbound : ys.length ≤ 9223372036854775807 := by rw [hlen]; omega
  have hheader : output.len = int ys.length := by change int ((xs.length - 1 : Nat) : Int) = _; rw [hlen]
  have hcontents : outState.contents output.chunks = (encodeBits ys).map some :=
    scalar_initial_contents (encodeBits ys) (packedEncoded_lengthBound ys hbound)
  refine ⟨output, outState, copy_delete_singleton_single_chunk_run xs p hpos hp hn, ?_, ?_⟩
  · rw [copy_singleton_expected xs p hp (by omega)]
    exact scalar_bitValues_contents outState output ys hbound hheader hcontents
  · exact scalar_invariant_of_contents outState output ys hbound hheader hcontents
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Decode valid one-based native deletion indices into zero-based logical positions. -/
def ctor_mask_decode_indices (indices : List I64) : List Nat :=
  indices.map (fun i => i.val.toNat - 1)

/-- A valid single-chunk index decodes within the source and re-encodes exactly. -/
theorem ctor_mask_decode_index (n : Nat) (hn : n ≤ 64) (index : I64)
    (hi : int 1 ≤ index ∧ index ≤ int n) :
    index.val.toNat - 1 < n ∧ int ((index.val.toNat - 1 + 1 : Nat) : Int) = index := by
  change 1 ≤ index.val ∧ index.val ≤ (int n).val at hi
  rw [packedInt_val n (by omega)] at hi
  constructor
  · omega
  · apply Subtype.ext
    rw [packedInt_val (index.val.toNat - 1 + 1) (by omega)]
    omega

/-- Every decoded list member lies within the logical source length. -/
theorem ctor_mask_decode_bounds (indices : List I64) (n : Nat) (hn : n ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int n) :
    ∀ j ∈ ctor_mask_decode_indices indices, j < n := by
  intro j hj
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hj
  rw [← he]
  exact (ctor_mask_decode_index n hn i (hvalid i hi)).1

/-- Strict native index order becomes strict natural-position order without duplicates. -/
theorem ctor_mask_decode_pairwise (indices : List I64) (n : Nat) (_hn : n ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int n)
    (hordered : indices.Pairwise (· < ·)) :
    (ctor_mask_decode_indices indices).Pairwise (· < ·) := by
  unfold ctor_mask_decode_indices
  apply List.pairwise_map.mpr
  refine List.Pairwise.imp_of_mem ?_ hordered
  intro a b ha hb hab
  have ha' := hvalid a ha
  have hb' := hvalid b hb
  change 1 ≤ a.val ∧ a.val ≤ (int n).val at ha'
  change 1 ≤ b.val ∧ b.val ≤ (int n).val at hb'
  change a.val < b.val at hab
  omega

/-- Encoding the decoded list recovers the exact original native iterator values. -/
theorem ctor_mask_decode_roundtrip (indices : List I64) (n : Nat) (hn : n ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int n) :
    (ctor_mask_decode_indices indices).map (fun j => int ((j + 1 : Nat) : Int)) = indices := by
  unfold ctor_mask_decode_indices
  rw [List.map_map]
  calc
    _ = indices.map id := by
      apply List.map_congr_left
      intro i hi
      exact (ctor_mask_decode_index n hn i (hvalid i hi)).2
    _ = indices := List.map_id indices

/-- The frozen list iterator advances from the current selected index to the remaining head. -/
theorem ctor_mask_iterator_next (selected before after : List Nat) (i : Nat)
    (hdecomp : selected = before ++ i :: after) :
    Option.map (fun value : I64 => (value, before.length + 1))
      ((selected.map (fun j => int ((j + 1 : Nat) : Int)))[before.length + 1]?) =
        after.head?.map (fun j => (int ((j + 1 : Nat) : Int), before.length + 1)) := by
  rw [hdecomp, List.map_append, List.map_cons,
    List.getElem?_append_right (by rw [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem?_cons_succ,
    List.getElem?_map, Option.map_map, List.head?_eq_getElem?, Function.comp_def]

/-- Native re-encoding introduces no membership collisions in the single-chunk domain. -/
theorem ctor_mask_native_contains (selected : List Nat) (j : Nat)
    (hbound : ∀ i ∈ selected, i < 64) (hj : j < 64) :
    (selected.map (fun i => int ((i + 1 : Nat) : Int))).contains
      (int ((j + 1 : Nat) : Int)) = selected.contains j := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := h
    have hival := hbound i hi
    have hv := congrArg Subtype.val he
    rw [packedInt_val (i + 1) (by omega), packedInt_val (j + 1) (by omega)] at hv
    have hij : i = j := by omega
    rw [hij] at hi
    exact hi
  · intro h
    exact ⟨j, h, rfl⟩

/-- The original native membership test agrees with membership in the decoded natural selection. -/
theorem ctor_mask_decode_contains (indices : List I64) (n : Nat) (hn : n ≤ 64)
    (hvalid : ∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int n) (j : Nat) (hj : j < n) :
    indices.contains (int ((j + 1 : Nat) : Int)) = (ctor_mask_decode_indices indices).contains j := by
  have hr := ctor_mask_decode_roundtrip indices n hn hvalid
  calc
    _ = ((ctor_mask_decode_indices indices).map
        (fun i => int ((i + 1 : Nat) : Int))).contains (int ((j + 1 : Nat) : Int)) :=
      congrArg (fun values : List I64 => values.contains (int ((j + 1 : Nat) : Int))) hr.symm
    _ = _ := ctor_mask_native_contains (ctor_mask_decode_indices indices) j
      (by intro i hi; have hb := ctor_mask_decode_bounds indices n hn hvalid i hi; omega) (by omega)
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

abbrev copy_indices_Registers := I64 × Option (I64 × Nat) × I64 × I64

/-- The exact sorted-index deletion loop, with its iterator and compaction registers exposed. -/
def copy_indices_step (n : I64) (chunks : Nat) (indices : List I64)
    (_ : Unit) (registers : copy_indices_Registers) :
    BitMutationM (ForInStep copy_indices_Registers) := do
  let newL := registers.1
  let y := registers.2.1
  let p := registers.2.2.1
  let q := registers.2.2.2
  if y.isSome then
    bitVectorDeleteAtIndices.match_3
      (fun _ => BitMutationM (ForInStep copy_indices_Registers)) y
      (fun _ => pure (.yield (newL, y, p, q))) (fun i s => do
      if !(q ≤ i ∧ i ≤ n) then
        if i < q then throw (Error.argument "indices must be unique and sorted")
        throw Error.bounds
      let newL := newL - int 1
      let p ← if i > q then do
          copyChunks chunks p chunks q (i - q)
          pure (p + i - q)
        else pure p
      let q := i + int 1
      let y := indices[s + 1]?.map fun value => (value, s + 1)
      pure (.yield (newL, y, p, q)))
  else pure (.done (newL, y, p, q))

/-- The post-loop sorted-index operations are its suffix move and common cleanup. -/
def copy_indices_finish (B : BitVector) (registers : copy_indices_Registers) : BitMutationM BitVector := do
  let newL := registers.1
  let p := registers.2.2.1
  let q := registers.2.2.2
  if q ≤ B.len then copyChunks B.chunks p B.chunks q (B.len - q + int 1)
  let count ← mutableLength B.chunks
  rangeSingleFinish B newL count

def copy_indices_after (B : BitVector) (indices : List I64) (registers : copy_indices_Registers) :
    BitMutationM BitVector := do
  let result ← forIn ({} : Lean.Loop) registers (copy_indices_step B.len B.chunks indices)
  copy_indices_finish B result

/-- The frozen nonempty iterator initializes exactly the exposed loop registers. -/
theorem copy_indices_action_nonempty (xs : List Bool) (i : I64) (rest : List I64)
    (hi : int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length)) :
    copy_delete_indices_action xs (i :: rest) =
      copy_indices_after (vectorBits xs) (i :: rest)
        (int xs.length - int 1, rest.head?.map (fun value => (value, 1)), i, i + int 1) := by
  unfold copy_delete_indices_action bitVectorDeleteAtIndices
  simp only [List.head?_cons, Option.map_some, pure_bind, id_eq,
    hi, true_and, ite_true, Bool.false_eq_true, ite_false,
    List.getElem?_cons_succ, Nat.zero_add]
  unfold copy_indices_after copy_indices_step copy_indices_finish rangeSingleFinish
  simp only [bind_assoc, pure_bind, List.getElem?_cons_succ, Nat.zero_add, List.head?_eq_getElem?]
  unfold vectorBits
  rfl

/-- One valid sorted-index iteration composes its optional interval copy and pure iterator successor. -/
theorem copy_indices_step_from (n : I64) (chunks : Nat) (indices : List I64)
    (newL p q i : I64) (index : Nat) (found : Option (I64 × Nat)) (state copied : State)
    (hv : q ≤ i ∧ i ≤ n)
    (hnext : indices[index + 1]?.map (fun value => (value, index + 1)) = found)
    (hc : ((if i > q then copyChunks chunks p chunks q (i - q)
      else pure ()) : BitMutationM Unit).run state = (.ok (), copied)) :
    (copy_indices_step n chunks indices () (newL, some (i, index), p, q)).run state =
      (.ok (.yield (newL - int 1, found, if i > q then p + i - q else p, i + int 1)), copied) := by
  by_cases hi : i > q
  · simp only [hi, ite_true] at hc ⊢
    simp only [copy_indices_step, Option.isSome_some, ite_true, hv, true_and,
      decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
      hi, ite_true, shape_run_bind, hc, shape_run_pure, hnext]
  · simp only [hi, ite_false, shape_run_pure] at hc ⊢
    have he : state = copied := congrArg Prod.snd hc
    rw [he]
    simp only [copy_indices_step, Option.isSome_some, ite_true, hv, true_and,
      decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
      hi, ite_false, shape_run_bind, shape_run_pure, hnext]
end JuliaLean.ChatGPT.Batch5.Group2
end

