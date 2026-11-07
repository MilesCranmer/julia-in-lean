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

/-- Empty vectors return before the reversal loop or any memory access. -/
theorem reverseEmptyRun (B : BitVector) (s : State) (hn : B.len = int 0) :
    (bitVectorReverseInPlace JuliaLean.base.int.bitreverse
      Round5.Round2.isOddIntegerModel B).run s = (.ok B, s) := by
  simp only [bitVectorReverseInPlace, hn, beq_self_eq_true, ite_true]
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
set_option maxHeartbeats 800000

/-- The integer bit predicate agrees with packed unsigned-word inspection. -/
theorem reverseBitOfPacked (word : U64) (k : Nat) :
    JuliaLean.Proofs.base.int.bitOf word k = packedBit word k := by
  unfold JuliaLean.Proofs.base.int.bitOf JuliaLean.Proofs.base.int.bitOfInt packedBit
  have hw : 0 ≤ word.val ∧ word.val < 18446744073709551616 := by
    have h := word.property
    change 0 ≤ word.val ∧ word.val ≤ 18446744073709551615 at h
    omega
  change (word.val % 18446744073709551616).toNat.testBit k = word.val.toNat.testBit k
  rw [Int.emod_eq_of_lt hw.1 hw.2]

/-- Bit reversal of a packed word reflects each valid bit about position 63. -/
theorem reversePackedWordBit (word : U64) (k : Nat) (hk : k < 64) :
    packedBit (JuliaLean.base.int.bitreverse word) k = packedBit word (63 - k) := by
  have h := JuliaLean.Proofs.base.int.bitReverse_proven .u64 word k hk
  rw [reverseBitOfPacked, reverseBitOfPacked] at h
  exact h

/-- Reading a reversed logical sequence selects its reflected source index. -/
theorem reverseGetD (xs : List Bool) (k : Nat) (hk : k < xs.length) :
    xs.reverse.getD k false = xs.getD (xs.length - 1 - k) false := by
  rw [← List.getElem_eq_getD (h := by rw [List.length_reverse]; exact hk),
    List.getElem_reverse]
  exact List.getElem_eq_getD false

/-- Reversal and alignment of one partial chunk gives the exact reversed encoding. -/
theorem reverseSinglePackedWord (xs : List Bool)
    (hp : 0 < xs.length) (hn : xs.length ≤ 64) :
    lshr_int (JuliaLean.base.int.bitreverse (packedPrefix xs 0 64))
      (int ((64 - xs.length : Nat) : Int)) = packedPrefix xs.reverse 0 64 := by
  apply packedBit_ext
  intro k hk
  rw [dequePackedShiftRight _ (64 - xs.length) k (by omega),
    packedWord_bit xs.reverse 0 k hk]
  simp only [hk, decide_true, Bool.true_and, Nat.zero_mul, Nat.zero_add]
  by_cases hi : k < xs.length
  · have hshift : k + (64 - xs.length) < 64 := by omega
    rw [reversePackedWordBit _ _ hshift,
      packedWord_bit xs 0 (63 - (k + (64 - xs.length))) (by omega), reverseGetD xs k hi]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [show 63 - (k + (64 - xs.length)) = xs.length - 1 - k by omega]
  · rw [dequePackedBitHigh _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [List.length_reverse]
      omega), Option.getD_none]

/-- The entire frozen reversal contract holds for the empty input. -/
theorem reverseEmptyFrozen : Round5.Round2.ReverseAgrees [] := by
  have hr : (bitVectorReverseInPlace JuliaLean.base.int.bitreverse
      Round5.Round2.isOddIntegerModel (vectorBits [])).run (initWords (encodeBits [])) =
        (.ok (vectorBits []), initWords (encodeBits [])) := by
    simp only [bitVectorReverseInPlace, vectorBits, List.length_nil,
      beq_self_eq_true, ite_true]
    rfl
  unfold Round5.Round2.ReverseAgrees
  dsimp only
  rw [hr]
  exact ⟨scalar_bits_initial (N := 1) [] [int 0] (by decide),
    scalar_initial_invariant (N := 1) [] [int 0] (by decide)⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Shifting a zero word leaves it zero, for every machine shift count. -/
theorem reverseShiftZero (k : I64) : shl_int (u64 0) k = u64 0 := by
  unfold shl_int jlShlInt
  have hz : (fromJInt (u64 0)).toNat = 0 := rfl
  rw [hz, Nat.zero_mul]
  split <;> rfl

/-- The aligned result word after reflecting the packed source words. -/
def reverseOutputWord (words : List U64) (k h : I64) (d : Nat) : U64 :=
  or_int (lshr_int (JuliaLean.base.int.bitreverse (words.getD (words.length - 1 - d) (u64 0))) h)
    (if d + 1 < words.length then
      shl_int (JuliaLean.base.int.bitreverse (words.getD (words.length - 2 - d) (u64 0))) k
    else u64 0)

/-- All packed words in the completed in-place reversal. -/
def reverseOutputWords (words : List U64) (k h : I64) : List U64 :=
  (List.range words.length).map (reverseOutputWord words k h)

/-- The left source word retained between two completed reversal iterations. -/
def reverseLoopU (words : List U64) (t : Nat) : U64 :=
  if t = 0 then u64 0 else JuliaLean.base.int.bitreverse (words.getD (t - 1) (u64 0))

/-- The right source word retained between two completed reversal iterations. -/
def reverseLoopV (words : List U64) (t : Nat) : U64 :=
  JuliaLean.base.int.bitreverse (words.getD (words.length - t - 1) (u64 0))

/-- The word invariant after exactly t completed two-ended iterations. -/
def reverseStageWord (words : List U64) (k h : I64) (t d : Nat) : U64 :=
  if d < t ∨ words.length - t ≤ d then reverseOutputWord words k h d
  else if d = words.length - t - 1 then shl_int (reverseLoopU words t) k
  else words.getD d (u64 0)

/-- The complete packed store invariant at a reversal loop boundary. -/
def reverseStageWords (words : List U64) (k h : I64) (t : Nat) : List U64 :=
  (List.range words.length).map (reverseStageWord words k h t)

theorem reverseOutputLength (words : List U64) (k h : I64) :
    (reverseOutputWords words k h).length = words.length := by
  simp only [reverseOutputWords, List.length_map, List.length_range]

theorem reverseStageLength (words : List U64) (k h : I64) (t : Nat) :
    (reverseStageWords words k h t).length = words.length := by
  simp only [reverseStageWords, List.length_map, List.length_range]

theorem reverseOutputGet (words : List U64) (k h : I64) (d : Nat) (hd : d < words.length) :
    (reverseOutputWords words k h).getD d (u64 0) = reverseOutputWord words k h d := by
  rw [← List.getElem_eq_getD (h := by rw [reverseOutputLength]; exact hd)]
  simp only [reverseOutputWords, List.getElem_map, List.getElem_range]

theorem reverseStageGet (words : List U64) (k h : I64) (t d : Nat) (hd : d < words.length) :
    (reverseStageWords words k h t).getD d (u64 0) = reverseStageWord words k h t d := by
  rw [← List.getElem_eq_getD (h := by rw [reverseStageLength]; exact hd)]
  simp only [reverseStageWords, List.getElem_map, List.getElem_range]

/-- The next held left source is the reversed next untouched source word. -/
theorem reverseLoopUSucc (words : List U64) (t : Nat) :
    reverseLoopU words (t + 1) = JuliaLean.base.int.bitreverse (words.getD t (u64 0)) := by
  simp only [reverseLoopU, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]

/-- The left output combines the held right word and the next right source. -/
theorem reverseOutputLeft (words : List U64) (k h : I64) (t : Nat)
    (ht : t + 1 < words.length) :
    reverseOutputWord words k h t =
      or_int (lshr_int (reverseLoopV words t) h) (shl_int (reverseLoopV words (t + 1)) k) := by
  unfold reverseOutputWord reverseLoopV
  rw [if_pos ht]
  have h1 : words.length - 1 - t = words.length - t - 1 := by omega
  have h2 : words.length - 2 - t = words.length - (t + 1) - 1 := by omega
  rw [h1, h2]

/-- The symmetric right output combines the new left source and the held carry. -/
theorem reverseOutputRight (words : List U64) (k h : I64) (t : Nat)
    (ht : t < words.length) :
    reverseOutputWord words k h (words.length - t - 1) =
      or_int (lshr_int (JuliaLean.base.int.bitreverse (words.getD t (u64 0))) h)
        (shl_int (reverseLoopU words t) k) := by
  unfold reverseOutputWord
  have h1 : words.length - 1 - (words.length - t - 1) = t := by omega
  rw [h1]
  by_cases hz : t = 0
  · subst t
    rw [if_neg (by omega)]
    simp only [reverseLoopU, ite_true, reverseShiftZero]
  · rw [if_pos (by omega)]
    have h2 : words.length - 2 - (words.length - t - 1) = t - 1 := by omega
    rw [h2]
    simp only [reverseLoopU, hz, ite_false]

/-- A stage's untouched interior still contains the original source word. -/
theorem reverseStageInterior (words : List U64) (k h : I64) (t d : Nat)
    (ht : t ≤ d) (hd : d < words.length - t - 1) :
    (reverseStageWords words k h t).getD d (u64 0) = words.getD d (u64 0) := by
  rw [reverseStageGet words k h t d (by omega), reverseStageWord]
  rw [if_neg (by omega), if_neg (by omega)]

/-- The active right boundary contains precisely the carried left high bits. -/
theorem reverseStageBoundary (words : List U64) (k h : I64) (t : Nat)
    (ht : 2 * t < words.length) :
    (reverseStageWords words k h t).getD (words.length - t - 1) (u64 0) =
      shl_int (reverseLoopU words t) k := by
  rw [reverseStageGet words k h t _ (by omega), reverseStageWord]
  rw [if_neg (by omega), if_pos rfl]

/-- A completed prefix or suffix word equals its final packed result. -/
theorem reverseStageCompleted (words : List U64) (k h : I64) (t d : Nat)
    (hd : d < words.length) (hc : d < t ∨ words.length - t ≤ d) :
    (reverseStageWords words k h t).getD d (u64 0) = reverseOutputWord words k h d := by
  rw [reverseStageGet words k h t d hd, reverseStageWord, if_pos hc]

/-- Clearing the last source word creates the initial reversal loop invariant. -/
theorem reverseStageInitial (words : List U64) (k h : I64) (hp : 0 < words.length) :
    reverseStageWords words k h 0 = words.set (words.length - 1) (u64 0) := by
  apply List.ext_getElem
  · rw [reverseStageLength, List.length_set]
  · intro d hd hd'
    have hdw : d < words.length := by simpa only [reverseStageLength] using hd
    rw [List.getElem_eq_getD (fallback := u64 0), reverseStageGet words k h 0 d hdw,
      List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet words (words.length - 1) d _ (by omega)]
    rw [reverseStageWord, if_neg (show ¬ (d < 0 ∨ words.length - 0 ≤ d) by omega)]
    simp only [Nat.sub_zero, reverseLoopU, ite_true, reverseShiftZero]
    by_cases he : d = words.length - 1
    · subst d
      simp only [ite_true]
    · simp only [he, Ne.symm he, ite_false]

/-- One complete reversal iteration extends both completed ends by one word. -/
theorem reverseStageWordStep (words : List U64) (k h : I64) (t d : Nat)
    (ht : 2 * t + 2 < words.length) :
    reverseStageWord words k h (t + 1) d =
      if words.length - t - 2 = d then
        shl_int (JuliaLean.base.int.bitreverse (words.getD t (u64 0))) k
      else if t = d then reverseOutputWord words k h t
      else if words.length - t - 1 = d then
        reverseOutputWord words k h (words.length - t - 1)
      else reverseStageWord words k h t d := by
  by_cases hn : words.length - t - 2 = d
  · subst d
    rw [if_pos rfl, reverseStageWord,
      if_neg (show ¬ (words.length - t - 2 < t + 1 ∨
        words.length - (t + 1) ≤ words.length - t - 2) by omega),
      if_pos (show words.length - t - 2 = words.length - (t + 1) - 1 by omega),
      reverseLoopUSucc]
  · rw [if_neg hn]
    by_cases hl : t = d
    · subst d
      rw [if_pos rfl, reverseStageWord,
        if_pos (show t < t + 1 ∨ words.length - (t + 1) ≤ t by omega)]
    · rw [if_neg hl]
      by_cases hr : words.length - t - 1 = d
      · subst d
        rw [if_pos rfl, reverseStageWord,
          if_pos (show words.length - t - 1 < t + 1 ∨
            words.length - (t + 1) ≤ words.length - t - 1 by omega)]
      · rw [if_neg hr]
        by_cases hc : d < t ∨ words.length - t ≤ d
        · rw [reverseStageWord, if_pos (show d < t + 1 ∨ words.length - (t + 1) ≤ d by omega),
            reverseStageWord, if_pos hc]
        · rw [reverseStageWord,
            if_neg (show ¬ (d < t + 1 ∨ words.length - (t + 1) ≤ d) by omega),
            if_neg (show d ≠ words.length - (t + 1) - 1 by omega),
            reverseStageWord, if_neg hc, if_neg (show d ≠ words.length - t - 1 by omega)]

/-- The normalized right, left, and next-boundary writes produce the next loop stage. -/
theorem reverseStageStep (words : List U64) (k h : I64) (t : Nat)
    (ht : 2 * t + 2 < words.length) :
    (((reverseStageWords words k h t).set (words.length - t - 1)
      (reverseOutputWord words k h (words.length - t - 1))).set t
        (reverseOutputWord words k h t)).set (words.length - t - 2)
          (shl_int (JuliaLean.base.int.bitreverse (words.getD t (u64 0))) k) =
      reverseStageWords words k h (t + 1) := by
  have hs : (reverseStageWords words k h t).length = words.length := reverseStageLength words k h t
  apply List.ext_getElem
  · simp only [List.length_set, reverseStageLength]
  · intro d hd hd'
    have hdw : d < words.length := by simpa only [List.length_set, hs] using hd
    rw [List.getElem_eq_getD (fallback := u64 0)]
    rw [dequeWordGetSet _ (words.length - t - 2) d _ (by simp only [List.length_set, hs]; omega),
      dequeWordGetSet _ t d _ (by simp only [List.length_set, hs]; omega),
      dequeWordGetSet _ (words.length - t - 1) d _ (by rw [hs]; omega)]
    rw [reverseStageGet words k h t d hdw,
      List.getElem_eq_getD (fallback := u64 0), reverseStageGet words k h (t + 1) d hdw,
      reverseStageWordStep words k h t d ht]

/-- With one active center word, its final low bits complete the packed result. -/
theorem reverseOddFinishWord (words : List U64) (k h : I64) (t : Nat)
    (hw : words.length = 2 * t + 1) :
    or_int ((reverseStageWords words k h t).getD t (u64 0))
      (lshr_int (reverseLoopV words t) h) = reverseOutputWord words k h t := by
  have hb := reverseStageBoundary words k h t (by omega)
  have hi : words.length - t - 1 = t := by omega
  rw [hi] at hb
  rw [hb, reverseLoopV, hi, reverseOrComm]
  have hr := reverseOutputRight words k h t (by omega)
  rw [hi] at hr
  exact hr.symm

/-- Filling the one remaining center word completes every output word. -/
theorem reverseStageSingleFinish (words : List U64) (k h : I64) (t : Nat)
    (hw : words.length = 2 * t + 1) :
    (reverseStageWords words k h t).set t (reverseOutputWord words k h t) =
      reverseOutputWords words k h := by
  apply List.ext_getElem
  · simp only [List.length_set, reverseStageLength, reverseOutputLength]
  · intro d hd hd'
    have hdw : d < words.length := by simpa only [List.length_set, reverseStageLength] using hd
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ t d _ (by rw [reverseStageLength]; omega),
      List.getElem_eq_getD (fallback := u64 0), reverseOutputGet words k h d hdw]
    by_cases he : t = d
    · subst d
      rw [if_pos rfl]
    · rw [if_neg he]
      exact reverseStageCompleted words k h t d hdw (by omega)

/-- With two active words, the final high carry completes the left center word. -/
theorem reverseEvenFinishWord (words : List U64) (k h : I64) (t : Nat)
    (hw : words.length = 2 * t + 2) :
    or_int (lshr_int (reverseLoopV words t) h)
      (shl_int (JuliaLean.base.int.bitreverse (words.getD t (u64 0))) k) =
        reverseOutputWord words k h t := by
  rw [reverseOutputLeft words k h t (by omega)]
  simp only [reverseLoopV]
  have hi : words.length - (t + 1) - 1 = t := by omega
  rw [hi]

/-- Filling the two remaining center words completes every output word. -/
theorem reverseStagePairFinish (words : List U64) (k h : I64) (t : Nat)
    (hw : words.length = 2 * t + 2) :
    ((reverseStageWords words k h t).set (t + 1) (reverseOutputWord words k h (t + 1))).set t
      (reverseOutputWord words k h t) = reverseOutputWords words k h := by
  apply List.ext_getElem
  · simp only [List.length_set, reverseStageLength, reverseOutputLength]
  · intro d hd hd'
    have hdw : d < words.length := by simpa only [List.length_set, reverseStageLength] using hd
    rw [List.getElem_eq_getD (fallback := u64 0),
      dequeWordGetSet _ t d _ (by simp only [List.length_set, reverseStageLength]; omega),
      dequeWordGetSet _ (t + 1) d _ (by rw [reverseStageLength]; omega),
      List.getElem_eq_getD (fallback := u64 0), reverseOutputGet words k h d hdw]
    by_cases he : t = d
    · subst d
      rw [if_pos rfl]
    · rw [if_neg he]
      by_cases he' : t + 1 = d
      · subst d
        rw [if_pos rfl]
      · rw [if_neg he']
        exact reverseStageCompleted words k h t d hdw (by omega)

/-- Number of logical bits in the final nonempty source chunk. -/
def reverseValidBits (n : Nat) : Nat := n - (wordCount n - 1) * 64

/-- High padding bits that must be removed after reflecting a source chunk. -/
def reversePadding (n : Nat) : Nat := wordCount n * 64 - n

/-- A nonempty packed sequence has between one and sixty-four final logical bits. -/
theorem reversePackingBounds (n : Nat) (hn : 0 < n) :
    0 < wordCount n ∧ 0 < reverseValidBits n ∧ reverseValidBits n ≤ 64 ∧
      reversePadding n < 64 ∧ reverseValidBits n + reversePadding n = 64 ∧
      n = (wordCount n - 1) * 64 + reverseValidBits n := by
  unfold reversePadding reverseValidBits wordCount
  omega

/-- Reflecting then right-aligning a word reads its reflected nonpadding source bit. -/
theorem reversePackedRight (word : U64) (amount bit : Nat)
    (ha : amount < 64) (hb : bit < 64) :
    packedBit (lshr_int (JuliaLean.base.int.bitreverse word) (int amount)) bit =
      if bit + amount < 64 then packedBit word (63 - (bit + amount)) else false := by
  rw [dequePackedShiftRight _ amount bit ha]
  simp only [hb, decide_true, Bool.true_and]
  by_cases hi : bit + amount < 64
  · rw [if_pos hi, reversePackedWordBit _ _ hi]
  · rw [if_neg hi, dequePackedBitHigh _ _ (by omega)]

/-- Each aligned reversed chunk is exactly the corresponding reversed logical chunk. -/
theorem reverseOutputWordEncode (xs : List Bool) (d : Nat)
    (hp : 0 < xs.length) (hd : d < wordCount xs.length) :
    reverseOutputWord (encodeBits xs) (int (reverseValidBits xs.length))
      (int (reversePadding xs.length)) d = packedPrefix xs.reverse d 64 := by
  let m := wordCount xs.length
  let k := reverseValidBits xs.length
  let h := reversePadding xs.length
  obtain ⟨hm, hkpos, hkbound, hhbound, hkh, hshape⟩ := reversePackingBounds xs.length hp
  change 0 < m at hm
  change 0 < k at hkpos
  change k ≤ 64 at hkbound
  change h < 64 at hhbound
  change k + h = 64 at hkh
  change xs.length = (m - 1) * 64 + k at hshape
  change d < m at hd
  unfold reverseOutputWord
  rw [packedEncoded_length]
  change or_int
    (lshr_int (JuliaLean.base.int.bitreverse ((encodeBits xs).getD (m - 1 - d) (u64 0))) (int h))
    (if d + 1 < m then
      shl_int (JuliaLean.base.int.bitreverse ((encodeBits xs).getD (m - 2 - d) (u64 0))) (int k)
    else u64 0) = _
  rw [dequeEncodedGet xs (m - 1 - d) (by change m - 1 - d < m; omega)]
  by_cases hn : d + 1 < m
  · rw [if_pos hn, dequeEncodedGet xs (m - 2 - d) (by change m - 2 - d < m; omega)]
    apply packedBit_ext
    intro bit hb
    rw [packedBit_or, reversePackedRight _ h bit hhbound hb,
      reversePackedLeft _ k bit hkbound hb, packedWord_bit xs.reverse d bit hb]
    have hlogical : d * 64 + bit < xs.length := by omega
    by_cases hbsmall : bit < k
    · rw [if_pos (show bit + h < 64 by omega), if_neg (show ¬ k ≤ bit by omega)]
      simp only [Bool.or_false]
      rw [packedWord_bit xs (m - 1 - d) (63 - (bit + h)) (by omega),
        reverseGetD xs (d * 64 + bit) hlogical]
      have hi : (m - 1 - d) * 64 + (63 - (bit + h)) = xs.length - 1 - (d * 64 + bit) := by omega
      rw [hi]
    · rw [if_neg (show ¬ bit + h < 64 by omega), if_pos (show k ≤ bit by omega)]
      simp only [Bool.false_or]
      rw [reversePackedWordBit _ (bit - k) (by omega),
        packedWord_bit xs (m - 2 - d) (63 - (bit - k)) (by omega),
        reverseGetD xs (d * 64 + bit) hlogical]
      have hi : (m - 2 - d) * 64 + (63 - (bit - k)) = xs.length - 1 - (d * 64 + bit) := by omega
      rw [hi]
  · rw [if_neg hn, dequePackedOrZero]
    apply packedBit_ext
    intro bit hb
    rw [reversePackedRight _ h bit hhbound hb, packedWord_bit xs.reverse d bit hb]
    by_cases hbsmall : bit < k
    · rw [if_pos (show bit + h < 64 by omega),
        packedWord_bit xs (m - 1 - d) (63 - (bit + h)) (by omega),
        reverseGetD xs (d * 64 + bit) (by omega)]
      have hi : (m - 1 - d) * 64 + (63 - (bit + h)) = xs.length - 1 - (d * 64 + bit) := by omega
      rw [hi]
    · rw [if_neg (show ¬ bit + h < 64 by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [List.length_reverse]
        omega), Option.getD_none]

/-- The complete reflected and aligned word sequence encodes logical reversal. -/
theorem reverseOutputWordsEncode (xs : List Bool) (hp : 0 < xs.length) :
    reverseOutputWords (encodeBits xs) (int (reverseValidBits xs.length))
      (int (reversePadding xs.length)) = encodeBits xs.reverse := by
  apply List.ext_getElem
  · rw [reverseOutputLength, packedEncoded_length, packedEncoded_length xs.reverse,
      List.length_reverse]
  · intro d hd hd'
    have hdc : d < wordCount xs.length := by
      simpa only [reverseOutputLength, packedEncoded_length] using hd
    rw [List.getElem_eq_getD (fallback := u64 0), reverseOutputGet _ _ _ d
      (by rw [packedEncoded_length]; exact hdc), reverseOutputWordEncode xs d hp hdc]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
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

abbrev ReverseRegisters := I64 × I64 × U64 × U64

/-- The first half of a reversal iteration transfers the low reversed blocks. -/
def reverseLowPhase (chunks : Nat) (rev : U64 → U64) (i j h : I64) (v : U64) :
    BitMutationM U64 := do
  let u := rev (← mutableGet chunks i)
  mutableSet chunks (u64 0) i
  let oldJ ← mutableGet chunks j
  mutableSet chunks (or_int oldJ (lshr_int u h)) j
  let oldI ← mutableGet chunks i
  mutableSet chunks (or_int oldI (lshr_int v h)) i
  pure u

/-- The second half transfers the high blocks and retains the next reversed source word. -/
def reverseHighPhase (chunks : Nat) (rev : U64 → U64) (i j k : I64) (u : U64) :
    BitMutationM U64 := do
  let v := rev (← mutableGet chunks j)
  mutableSet chunks (u64 0) j
  let oldI ← mutableGet chunks i
  mutableSet chunks (or_int oldI (shl_int v k)) i
  let oldJ ← mutableGet chunks j
  mutableSet chunks (or_int oldJ (shl_int u k)) j
  pure v

/-- One reversal iteration, with exactly the register order of the frozen loop. -/
def reverseLoopStep (chunks : Nat) (rev : U64 → U64) (h k : I64)
    (r : ReverseRegisters) : BitMutationM (ForInStep ReverseRegisters) := do
  let i := r.1 + int 1
  let j := r.2.1
  let u := r.2.2.1
  let v := r.2.2.2
  if i == j then return .done (i, j, u, v)
  let u ← reverseLowPhase chunks rev i j h v
  let j := j - int 1
  if i == j then return .done (i, j, u, v)
  let v ← reverseHighPhase chunks rev i j k u
  return .yield (i, j, u, v)

/-- The reversal loop itself is the installed monadic loop over the four registers. -/
def reverseLoop (chunks : Nat) (rev : U64 → U64) (h k : I64)
    (r : ReverseRegisters) : BitMutationM ReverseRegisters :=
  forIn ({} : Lean.Loop) r (fun _ r => reverseLoopStep chunks rev h k r)

/-- The final center block is completed according to the word-count parity. -/
def reverseFinish (B : BitArray 1) (isOdd : I64 → Bool) (h k : I64)
    (r : ReverseRegisters) : BitMutationM (BitArray 1) := do
  let last ← mutableGet B.chunks r.1
  let nc ← mutableLength B.chunks
  if isOdd nc then
    mutableSet B.chunks (or_int last (lshr_int r.2.2.2 h)) r.1
  else
    mutableSet B.chunks (or_int last (shl_int r.2.2.1 k)) r.1
  return B

/-- Factoring the frozen reversal into preparation, loop, and center completion preserves its action. -/
theorem reverseFactor (rev : U64 → U64) (isOdd : I64 → Bool) (B : BitArray 1)
    (hz : (B.len == int 0) = false) :
    bitVectorReverseInPlace rev isOdd B = (do
      let k := mod64 (B.len + int 63) + int 1
      let h := int 64 - k
      let j ← mutableLength B.chunks
      let word ← mutableGet B.chunks j
      mutableSet B.chunks (u64 0) j
      let r ← reverseLoop B.chunks rev h k (int 0, j, u64 0, rev word)
      reverseFinish B isOdd h k r) := by
  simp only [bitVectorReverseInPlace, hz, Bool.false_eq_true, ite_false,
    reverseLoop, reverseLoopStep, reverseLowPhase, reverseHighPhase, reverseFinish,
    ite_true, bind_assoc, pure_bind]
  rfl

/-- Primitive preparation, loop, and completion outcomes compose to the full reversal. -/
theorem reverseRunFrom (rev : U64 → U64) (isOdd : I64 → Bool) (B outB : BitArray 1)
    (h k nc : I64) (last : U64) (r : ReverseRegisters) (s cleared mid out : State)
    (hz : (B.len == int 0) = false)
    (hk : mod64 (B.len + int 63) + int 1 = k) (hh : int 64 - k = h)
    (hl : (mutableLength B.chunks).run s = (.ok nc, s))
    (hg : (mutableGet B.chunks nc).run s = (.ok last, s))
    (hc : (mutableSet B.chunks (u64 0) nc).run s = (.ok (), cleared))
    (hloop : (reverseLoop B.chunks rev h k (int 0, nc, u64 0, rev last)).run cleared =
      (.ok r, mid))
    (hfinish : (reverseFinish B isOdd h k r).run mid = (.ok outB, out)) :
    (bitVectorReverseInPlace rev isOdd B).run s = (.ok outB, out) := by
  rw [reverseFactor rev isOdd B hz]
  dsimp only [BitVector] at *
  simp only [hk, hh, shape_run_bind, hl, hg, hc, hloop, hfinish]

/-- ORing zero on the left preserves a packed word. -/
theorem reverseOrZeroLeft (word : U64) : or_int (u64 0) word = word := by
  apply packedBit_ext
  intro k _
  rw [packedBit_or, packedBit_zero, Bool.false_or]

/-- A low-block transfer follows from its six primitive outcomes. -/
theorem reverseLowFrom (chunks : Nat) (rev : U64 → U64) (i j h : I64)
    (v word oldJ : U64) (s zeroed written out : State)
    (hr : (mutableGet chunks i).run s = (.ok word, s))
    (hz : (mutableSet chunks (u64 0) i).run s = (.ok (), zeroed))
    (hrj : (mutableGet chunks j).run zeroed = (.ok oldJ, zeroed))
    (hwj : (mutableSet chunks (or_int oldJ (lshr_int (rev word) h)) j).run zeroed =
      (.ok (), written))
    (hri : (mutableGet chunks i).run written = (.ok (u64 0), written))
    (hwi : (mutableSet chunks (lshr_int v h) i).run written = (.ok (), out)) :
    (reverseLowPhase chunks rev i j h v).run s = (.ok (rev word), out) := by
  simp only [reverseLowPhase, shape_run_bind, hr, hz, hrj, hwj, hri,
    reverseOrZeroLeft, hwi, shape_run_pure]

/-- A high-block transfer follows from its six primitive outcomes. -/
theorem reverseHighFrom (chunks : Nat) (rev : U64 → U64) (i j k : I64)
    (u word oldI : U64) (s zeroed written out : State)
    (hr : (mutableGet chunks j).run s = (.ok word, s))
    (hz : (mutableSet chunks (u64 0) j).run s = (.ok (), zeroed))
    (hri : (mutableGet chunks i).run zeroed = (.ok oldI, zeroed))
    (hwi : (mutableSet chunks (or_int oldI (shl_int (rev word) k)) i).run zeroed =
      (.ok (), written))
    (hrj : (mutableGet chunks j).run written = (.ok (u64 0), written))
    (hwj : (mutableSet chunks (shl_int u k) j).run written = (.ok (), out)) :
    (reverseHighPhase chunks rev i j k u).run s = (.ok (rev word), out) := by
  simp only [reverseHighPhase, shape_run_bind, hr, hz, hri, hwi, hrj,
    reverseOrZeroLeft, hwj, shape_run_pure]

/-- A center write follows from the selected parity branch and primitive outcomes. -/
theorem reverseFinishFrom (B : BitArray 1) (isOdd : I64 → Bool) (h k nc : I64)
    (r : ReverseRegisters) (last : U64) (s out : State)
    (hr : (mutableGet B.chunks r.1).run s = (.ok last, s))
    (hl : (mutableLength B.chunks).run s = (.ok nc, s))
    (hw : (mutableSet B.chunks
      (if isOdd nc then or_int last (lshr_int r.2.2.2 h)
        else or_int last (shl_int r.2.2.1 k)) r.1).run s = (.ok (), out)) :
    (reverseFinish B isOdd h k r).run s = (.ok B, out) := by
  by_cases ho : isOdd nc = true
  · simp only [ho, ite_true] at hw
    simp only [reverseFinish, shape_run_bind, hr, hl, ho, ite_true, hw, shape_run_pure]
  · simp only [ho, Bool.false_eq_true, ite_false] at hw
    simp only [reverseFinish, shape_run_bind, hr, hl, ho, Bool.false_eq_true, ite_false, hw, shape_run_pure]

/-- The normalized word-list effect of a reversal low-block transfer. -/
def reverseLowWords (words : List U64) (rev : U64 → U64) (i j : Nat) (h : I64) (v : U64) : List U64 :=
  (words.set j (or_int (words.getD j (u64 0)) (lshr_int (rev (words.getD i (u64 0))) h))).set i
    (lshr_int v h)

/-- The normalized word-list effect of a reversal high-block transfer. -/
def reverseHighWords (words : List U64) (rev : U64 → U64) (i j : Nat) (k : I64) (u : U64) : List U64 :=
  (words.set i (or_int (words.getD i (u64 0)) (shl_int (rev (words.getD j (u64 0))) k))).set j
    (shl_int u k)

/-- A low-block transfer preserves capacity and implements its two normalized word updates. -/
theorem reverseLowWordsRun (words : List U64) (rev : U64 → U64) (i j spare : Nat)
    (h : I64) (v : U64) (hn : words.length ≤ 9223372036854775807)
    (hi : i < words.length) (hj : j < words.length) (hne : i ≠ j) :
    (reverseLowPhase 0 rev (int ((i + 1 : Nat) : Int)) (int ((j + 1 : Nat) : Int)) h v).run
      (dequeWordStore words spare) =
        (.ok (rev (words.getD i (u64 0))),
          dequeWordStore (reverseLowWords words rev i j h v) spare) := by
  let zeroed := words.set i (u64 0)
  let right := or_int (words.getD j (u64 0)) (lshr_int (rev (words.getD i (u64 0))) h)
  let written := zeroed.set j right
  have hzl : zeroed.length = words.length := List.length_set
  have hwl : written.length = words.length := List.length_set.trans hzl
  have hzj : zeroed.getD j (u64 0) = words.getD j (u64 0) := by
    rw [dequeWordGetSet words i j (u64 0) hi, if_neg hne]
  have hwi0 : written.getD i (u64 0) = u64 0 := by
    rw [dequeWordGetSet zeroed j i right (by rw [hzl]; exact hj), if_neg (Ne.symm hne),
      dequeWordGetSet words i i (u64 0) hi, if_pos rfl]
  have hread := dequeWordRead words spare i hn hi
  have hzero := dequeWordSet words spare i (u64 0) hn hi
  have hreadJ := dequeWordRead zeroed spare j (by rw [hzl]; exact hn) (by rw [hzl]; exact hj)
  rw [hzj] at hreadJ
  have hwriteJ := dequeWordSet zeroed spare j right (by rw [hzl]; exact hn)
    (by rw [hzl]; exact hj)
  have hreadI := dequeWordRead written spare i (by rw [hwl]; exact hn) (by rw [hwl]; exact hi)
  rw [hwi0] at hreadI
  have hwriteI := dequeWordSet written spare i (lshr_int v h) (by rw [hwl]; exact hn)
    (by rw [hwl]; exact hi)
  have hrun := reverseLowFrom 0 rev (int ((i + 1 : Nat) : Int)) (int ((j + 1 : Nat) : Int))
    h v (words.getD i (u64 0)) (words.getD j (u64 0)) _ _ _ _
    hread hzero hreadJ hwriteJ hreadI hwriteI
  have hout : written.set i (lshr_int v h) = reverseLowWords words rev i j h v := by
    change ((words.set i (u64 0)).set j right).set i (lshr_int v h) = _
    rw [List.set_comm (u64 0) right hne, List.set_set]
    rfl
  exact hrun.trans (congrArg (fun ws : List U64 =>
    ((.ok (rev (words.getD i (u64 0))) : Except Error U64), dequeWordStore ws spare)) hout)

/-- A high-block transfer preserves capacity and implements its two normalized word updates. -/
theorem reverseHighWordsRun (words : List U64) (rev : U64 → U64) (i j spare : Nat)
    (k : I64) (u : U64) (hn : words.length ≤ 9223372036854775807)
    (hi : i < words.length) (hj : j < words.length) (hne : i ≠ j) :
    (reverseHighPhase 0 rev (int ((i + 1 : Nat) : Int)) (int ((j + 1 : Nat) : Int)) k u).run
      (dequeWordStore words spare) =
        (.ok (rev (words.getD j (u64 0))),
          dequeWordStore (reverseHighWords words rev i j k u) spare) := by
  let zeroed := words.set j (u64 0)
  let left := or_int (words.getD i (u64 0)) (shl_int (rev (words.getD j (u64 0))) k)
  let written := zeroed.set i left
  have hzl : zeroed.length = words.length := List.length_set
  have hwl : written.length = words.length := List.length_set.trans hzl
  have hzi : zeroed.getD i (u64 0) = words.getD i (u64 0) := by
    rw [dequeWordGetSet words j i (u64 0) hj, if_neg (Ne.symm hne)]
  have hwj0 : written.getD j (u64 0) = u64 0 := by
    rw [dequeWordGetSet zeroed i j left (by rw [hzl]; exact hi), if_neg hne,
      dequeWordGetSet words j j (u64 0) hj, if_pos rfl]
  have hread := dequeWordRead words spare j hn hj
  have hzero := dequeWordSet words spare j (u64 0) hn hj
  have hreadI := dequeWordRead zeroed spare i (by rw [hzl]; exact hn) (by rw [hzl]; exact hi)
  rw [hzi] at hreadI
  have hwriteI := dequeWordSet zeroed spare i left (by rw [hzl]; exact hn)
    (by rw [hzl]; exact hi)
  have hreadJ := dequeWordRead written spare j (by rw [hwl]; exact hn) (by rw [hwl]; exact hj)
  rw [hwj0] at hreadJ
  have hwriteJ := dequeWordSet written spare j (shl_int u k) (by rw [hwl]; exact hn)
    (by rw [hwl]; exact hj)
  have hrun := reverseHighFrom 0 rev (int ((i + 1 : Nat) : Int)) (int ((j + 1 : Nat) : Int))
    k u (words.getD j (u64 0)) (words.getD i (u64 0)) _ _ _ _
    hread hzero hreadI hwriteI hreadJ hwriteJ
  have hout : written.set j (shl_int u k) = reverseHighWords words rev i j k u := by
    change ((words.set j (u64 0)).set i left).set j (shl_int u k) = _
    rw [List.set_comm (u64 0) left (Ne.symm hne), List.set_set]
    rfl
  exact hrun.trans (congrArg (fun ws : List U64 =>
    ((.ok (rev (words.getD j (u64 0))) : Except Error U64), dequeWordStore ws spare)) hout)

/-- Equality of representable natural indices is reflected by their machine Boolean test. -/
theorem reverseNatBeq (a b : Nat) (ha : a ≤ 9223372036854775807)
    (hb : b ≤ 9223372036854775807) :
    (int (a : Int) == int (b : Int)) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [packedInt_val a ha, packedInt_val b hb] at hv
    omega
  · intro h
    exact congrArg (fun n : Nat => int (n : Int)) h

/-- Decrementing a positive natural index agrees with the wrapped machine operation. -/
theorem reverseNatPred (n : Nat) (hp : 0 < n) :
    int (n : Int) - int 1 = int ((n - 1 : Nat) : Int) := by
  rw [dequeIntSub]
  exact congrArg int (by omega)

/-- The frozen oddness callback tests ordinary parity for a native word count. -/
theorem reverseMachineOdd (n : Nat) (hn : n ≤ 9223372036854775807) :
    Round5.Round2.isOddIntegerModel (int (n : Int)) = decide (n % 2 = 1) := by
  simp only [Round5.Round2.isOddIntegerModel, JuliaLean.base.int.isodd_Real,
    JuliaLean.base.number.isintegerInteger, id_eq, Bool.not_not, Bool.true_and]
  rw [JuliaLean.Proofs.base.int.remBoolParity_proven, packedInt_val n hn]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

/-- The low block in a nonempty packed vector contains one through sixty-four bits. -/
theorem reverseBlockSizes (n : Nat) (hp : 0 < n) :
    1 ≤ n - (wordCount n - 1) * 64 ∧
    n - (wordCount n - 1) * 64 ≤ 64 ∧
    wordCount n * 64 - n < 64 ∧
    (n - (wordCount n - 1) * 64) + (wordCount n * 64 - n) = 64 := by
  unfold wordCount
  omega

/-- The model's low-block expression agrees with the natural final-chunk width. -/
theorem reverseMachineK (n : Nat) (hp : 0 < n) (hn : n < Round5.maxVectorLength) :
    mod64 (int (n : Int) + int 63) + int 1 =
      int ((n - (wordCount n - 1) * 64 : Nat) : Int) := by
  have hbound : n + 63 ≤ 9223372036854775807 := by
    change n < 4611686018427387903 at hn
    omega
  have hsum : int (n : Int) + int 63 = int ((n + 63 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  have hmod : mod64 (int ((n + 63 : Nat) : Int)) = int (((n + 63) % 64 : Nat) : Int) := by
    apply Subtype.ext
    rw [scalar_mod64_val, packedInt_val (n + 63) hbound,
      packedInt_val ((n + 63) % 64) (by omega)]
    omega
  rw [hsum, hmod, packedInt_add]
  apply congrArg int
  unfold wordCount
  omega

/-- The complementary model shift equals the number of padded high bits. -/
theorem reverseMachineH (n : Nat) (hp : 0 < n) :
    int 64 - int ((n - (wordCount n - 1) * 64 : Nat) : Int) =
      int ((wordCount n * 64 - n : Nat) : Int) := by
  have h := reverseBlockSizes n hp
  rw [dequeIntSub]
  exact congrArg int (by omega)

/-- Natural loop-stage indices paired with their two retained reversed source words. -/
def reverseLoopRegisters (words : List U64) (t : Nat) : ReverseRegisters :=
  (int (t : Int), int ((words.length - t : Nat) : Int), reverseLoopU words t, reverseLoopV words t)

/-- The first half-stage has completed the right word and written the left low block. -/
def reverseLowStageWords (words : List U64) (k h : I64) (t : Nat) : List U64 :=
  ((reverseStageWords words k h t).set (words.length - t - 1)
    (reverseOutputWord words k h (words.length - t - 1))).set t
      (lshr_int (reverseLoopV words t) h)

/-- Meeting before the low phase terminates the reversal iteration without mutation. -/
theorem reverseStepDoneFirst (chunks : Nat) (rev : U64 → U64) (h k i j : I64)
    (u v : U64) (s : State) (he : (i + int 1 == j) = true) :
    (reverseLoopStep chunks rev h k (i, j, u, v)).run s =
      (.ok (.done (i + int 1, j, u, v)), s) := by
  simp only [reverseLoopStep, he, ite_true, shape_run_pure]

/-- Meeting after the low phase terminates with its new left source word retained. -/
theorem reverseStepDoneSecond (chunks : Nat) (rev : U64 → U64) (h k i j : I64)
    (u v u' : U64) (s mid : State) (hfirst : (i + int 1 == j) = false)
    (hlow : (reverseLowPhase chunks rev (i + int 1) j h v).run s = (.ok u', mid))
    (hsecond : (i + int 1 == j - int 1) = true) :
    (reverseLoopStep chunks rev h k (i, j, u, v)).run s =
      (.ok (.done (i + int 1, j - int 1, u', v)), mid) := by
  simp only [reverseLoopStep, hfirst, Bool.false_eq_true, ite_false, shape_run_bind,
    hlow, hsecond, ite_true, shape_run_pure]

/-- A full iteration yields after both block transfers. -/
theorem reverseStepYieldFrom (chunks : Nat) (rev : U64 → U64) (h k i j : I64)
    (u v u' v' : U64) (s mid out : State) (hfirst : (i + int 1 == j) = false)
    (hlow : (reverseLowPhase chunks rev (i + int 1) j h v).run s = (.ok u', mid))
    (hsecond : (i + int 1 == j - int 1) = false)
    (hhigh : (reverseHighPhase chunks rev (i + int 1) (j - int 1) k u').run mid =
      (.ok v', out)) :
    (reverseLoopStep chunks rev h k (i, j, u, v)).run s =
      (.ok (.yield (i + int 1, j - int 1, u', v')), out) := by
  simp only [reverseLoopStep, hfirst, Bool.false_eq_true, ite_false, shape_run_bind,
    hlow, hsecond, hhigh, shape_run_pure]

/-- The low phase realizes the half-stage invariant and retains the next left source. -/
theorem reverseLowStageRun (words : List U64) (k h : I64) (t spare : Nat)
    (ht : 2 * t + 1 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (reverseLowPhase 0 JuliaLean.base.int.bitreverse
      (int ((t + 1 : Nat) : Int)) (int ((words.length - t : Nat) : Int)) h
      (reverseLoopV words t)).run (dequeWordStore (reverseStageWords words k h t) spare) =
        (.ok (reverseLoopU words (t + 1)), dequeWordStore (reverseLowStageWords words k h t) spare) := by
  let stage := reverseStageWords words k h t
  have hlen : stage.length = words.length := reverseStageLength words k h t
  have hleft : stage.getD t (u64 0) = words.getD t (u64 0) :=
    reverseStageInterior words k h t t (Nat.le_refl _) (by omega)
  have hright : stage.getD (words.length - t - 1) (u64 0) =
      shl_int (reverseLoopU words t) k := reverseStageBoundary words k h t (by omega)
  have hword : or_int (stage.getD (words.length - t - 1) (u64 0))
      (lshr_int (JuliaLean.base.int.bitreverse (stage.getD t (u64 0))) h) =
        reverseOutputWord words k h (words.length - t - 1) := by
    rw [hleft, hright, reverseOrComm]
    exact (reverseOutputRight words k h t (by omega)).symm
  have hp := reverseLowWordsRun stage JuliaLean.base.int.bitreverse t
    (words.length - t - 1) spare h (reverseLoopV words t)
    (by rw [hlen]; exact hn) (by rw [hlen]; omega) (by rw [hlen]; omega) (by omega)
  have hind : words.length - t - 1 + 1 = words.length - t := by omega
  rw [hind] at hp
  exact hp.trans (by
    rw [hleft, ← reverseLoopUSucc]
    unfold reverseLowWords
    rw [hword]
    rfl)

/-- The half-stage preserves every still-unread interior source word. -/
theorem reverseLowStageInterior (words : List U64) (k h : I64) (t d : Nat)
    (ht : t < d) (hd : d < words.length - t - 1) :
    (reverseLowStageWords words k h t).getD d (u64 0) = words.getD d (u64 0) := by
  unfold reverseLowStageWords
  rw [dequeWordGetSet _ t d _ (by simp only [List.length_set, reverseStageLength]; omega),
    if_neg (by omega),
    dequeWordGetSet _ (words.length - t - 1) d _ (by rw [reverseStageLength]; omega),
    if_neg (by omega)]
  exact reverseStageInterior words k h t d (by omega) hd

/-- The left word of the half-stage contains exactly the retained low block. -/
theorem reverseLowStageLeft (words : List U64) (k h : I64) (t : Nat)
    (ht : t < words.length) :
    (reverseLowStageWords words k h t).getD t (u64 0) =
      lshr_int (reverseLoopV words t) h := by
  unfold reverseLowStageWords
  rw [dequeWordGetSet _ t t _ (by simp only [List.length_set, reverseStageLength]; exact ht),
    if_pos rfl]

/-- The high phase advances the packed reversal stage and retains the next right source. -/
theorem reverseHighStageRun (words : List U64) (k h : I64) (t spare : Nat)
    (ht : 2 * t + 2 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (reverseHighPhase 0 JuliaLean.base.int.bitreverse
      (int ((t + 1 : Nat) : Int)) (int ((words.length - t - 1 : Nat) : Int)) k
      (reverseLoopU words (t + 1))).run (dequeWordStore (reverseLowStageWords words k h t) spare) =
        (.ok (reverseLoopV words (t + 1)), dequeWordStore (reverseStageWords words k h (t + 1)) spare) := by
  let low := reverseLowStageWords words k h t
  have hlen : low.length = words.length := by
    simp only [low, reverseLowStageWords, List.length_set, reverseStageLength]
  have hleft : low.getD t (u64 0) = lshr_int (reverseLoopV words t) h :=
    reverseLowStageLeft words k h t (by omega)
  have hsource : JuliaLean.base.int.bitreverse (low.getD (words.length - t - 2) (u64 0)) =
      reverseLoopV words (t + 1) := by
    rw [reverseLowStageInterior words k h t (words.length - t - 2) (by omega) (by omega)]
    unfold reverseLoopV
    rw [show words.length - t - 2 = words.length - (t + 1) - 1 by omega]
  have hp := reverseHighWordsRun low JuliaLean.base.int.bitreverse t
    (words.length - t - 2) spare k (reverseLoopU words (t + 1))
    (by rw [hlen]; exact hn) (by rw [hlen]; omega) (by rw [hlen]; omega) (by omega)
  have hind : words.length - t - 2 + 1 = words.length - t - 1 := by omega
  rw [hind] at hp
  have hout : reverseHighWords low JuliaLean.base.int.bitreverse t
      (words.length - t - 2) k (reverseLoopU words (t + 1)) =
        reverseStageWords words k h (t + 1) := by
    unfold reverseHighWords
    rw [hleft, hsource, ← reverseOutputLeft words k h t (by omega)]
    change ((((reverseStageWords words k h t).set (words.length - t - 1)
      (reverseOutputWord words k h (words.length - t - 1))).set t
      (lshr_int (reverseLoopV words t) h)).set t (reverseOutputWord words k h t)).set
        (words.length - t - 2) (shl_int (reverseLoopU words (t + 1)) k) = _
    rw [List.set_set, reverseLoopUSucc]
    exact reverseStageStep words k h t ht
  exact hp.trans (by rw [hsource, hout])

/-- The odd center completion turns a single active stage word into the entire packed output. -/
theorem reverseSingleFinishRun (words : List U64) (k h : I64) (t spare : Nat)
    (B : BitArray 1) (hb : B.chunks = 0)
    (hw : words.length = 2 * t + 1) (hn : words.length ≤ 9223372036854775807) :
    (reverseFinish B Round5.Round2.isOddIntegerModel h k
      (int ((t + 1 : Nat) : Int), int ((words.length - t : Nat) : Int),
        reverseLoopU words t, reverseLoopV words t)).run
      (dequeWordStore (reverseStageWords words k h t) spare) =
        (.ok B, dequeWordStore (reverseOutputWords words k h) spare) := by
  let stage := reverseStageWords words k h t
  have hlen : stage.length = words.length := reverseStageLength words k h t
  have hodd : Round5.Round2.isOddIntegerModel (int (words.length : Int)) = true := by
    rw [reverseMachineOdd words.length hn]
    simp only [show words.length % 2 = 1 by omega, decide_true]
  have hr : (mutableGet B.chunks (int ((t + 1 : Nat) : Int))).run (dequeWordStore stage spare) =
      (.ok (stage.getD t (u64 0)), dequeWordStore stage spare) := by
    rw [hb]
    exact dequeWordRead stage spare t (by rw [hlen]; exact hn) (by rw [hlen]; omega)
  have hl : (mutableLength B.chunks).run (dequeWordStore stage spare) =
      (.ok (int words.length), dequeWordStore stage spare) := by
    rw [hb]
    have hh := dequeWordLength stage spare
    rw [hlen] at hh
    exact hh
  have hs := dequeWordSet stage spare t (reverseOutputWord words k h t)
    (by rw [hlen]; exact hn) (by rw [hlen]; omega)
  have hs' : (mutableSet B.chunks
      (if Round5.Round2.isOddIntegerModel (int words.length) then
        or_int (stage.getD t (u64 0)) (lshr_int (reverseLoopV words t) h)
      else or_int (stage.getD t (u64 0)) (shl_int (reverseLoopU words t) k))
      (int ((t + 1 : Nat) : Int))).run (dequeWordStore stage spare) =
        (.ok (), dequeWordStore (reverseOutputWords words k h) spare) := by
    rw [hb, hodd, if_pos rfl, reverseOddFinishWord words k h t hw]
    exact hs.trans (congrArg (fun ws : List U64 =>
      ((.ok () : Except Error Unit), dequeWordStore ws spare)) (reverseStageSingleFinish words k h t hw))
  exact reverseFinishFrom B Round5.Round2.isOddIntegerModel h k (int words.length) _ _ _ _ hr hl hs'

/-- The even center completion fills the last missing high block of the half-stage. -/
theorem reversePairFinishRun (words : List U64) (k h : I64) (t spare : Nat)
    (B : BitArray 1) (hb : B.chunks = 0)
    (hw : words.length = 2 * t + 2) (hn : words.length ≤ 9223372036854775807) :
    (reverseFinish B Round5.Round2.isOddIntegerModel h k
      (int ((t + 1 : Nat) : Int), int ((words.length - t - 1 : Nat) : Int),
        reverseLoopU words (t + 1), reverseLoopV words t)).run
      (dequeWordStore (reverseLowStageWords words k h t) spare) =
        (.ok B, dequeWordStore (reverseOutputWords words k h) spare) := by
  let low := reverseLowStageWords words k h t
  have hlen : low.length = words.length := by
    simp only [low, reverseLowStageWords, List.length_set, reverseStageLength]
  have heven : Round5.Round2.isOddIntegerModel (int (words.length : Int)) = false := by
    rw [reverseMachineOdd words.length hn]
    simp only [show ¬ words.length % 2 = 1 by omega, decide_false]
  have hr : (mutableGet B.chunks (int ((t + 1 : Nat) : Int))).run (dequeWordStore low spare) =
      (.ok (lshr_int (reverseLoopV words t) h), dequeWordStore low spare) := by
    rw [hb]
    have hh := dequeWordRead low spare t (by rw [hlen]; exact hn) (by rw [hlen]; omega)
    rw [reverseLowStageLeft words k h t (by omega)] at hh
    exact hh
  have hl : (mutableLength B.chunks).run (dequeWordStore low spare) =
      (.ok (int words.length), dequeWordStore low spare) := by
    rw [hb]
    have hh := dequeWordLength low spare
    rw [hlen] at hh
    exact hh
  have hs := dequeWordSet low spare t (reverseOutputWord words k h t)
    (by rw [hlen]; exact hn) (by rw [hlen]; omega)
  have hout : low.set t (reverseOutputWord words k h t) = reverseOutputWords words k h := by
    unfold low reverseLowStageWords
    rw [List.set_set, show words.length - t - 1 = t + 1 by omega]
    exact reverseStagePairFinish words k h t hw
  have hs' : (mutableSet B.chunks
      (if Round5.Round2.isOddIntegerModel (int words.length) then
        or_int (lshr_int (reverseLoopV words t) h) (lshr_int (reverseLoopV words t) h)
      else or_int (lshr_int (reverseLoopV words t) h) (shl_int (reverseLoopU words (t + 1)) k))
      (int ((t + 1 : Nat) : Int))).run (dequeWordStore low spare) =
        (.ok (), dequeWordStore (reverseOutputWords words k h) spare) := by
    simp only [hb, heven, Bool.false_eq_true, ite_false, reverseLoopUSucc]
    rw [reverseEvenFinishWord words k h t hw]
    exact hs.trans (congrArg (fun ws : List U64 =>
      ((.ok () : Except Error Unit), dequeWordStore ws spare)) hout)
  exact reverseFinishFrom B Round5.Round2.isOddIntegerModel h k (int words.length) _ _ _ _ hr hl hs'

/-- The low phase uses the model's incremented left register. -/
theorem reverseLowStageIncRun (words : List U64) (k h : I64) (t spare : Nat)
    (ht : 2 * t + 1 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (reverseLowPhase 0 JuliaLean.base.int.bitreverse
      (int (t : Int) + int 1) (int ((words.length - t : Nat) : Int)) h
      (reverseLoopV words t)).run (dequeWordStore (reverseStageWords words k h t) spare) =
        (.ok (reverseLoopU words (t + 1)), dequeWordStore (reverseLowStageWords words k h t) spare) := by
  have hi := congrArg (fun i : I64 =>
    (reverseLowPhase 0 JuliaLean.base.int.bitreverse i
      (int ((words.length - t : Nat) : Int)) h (reverseLoopV words t)).run
      (dequeWordStore (reverseStageWords words k h t) spare)) (dequeNatAddOne t)
  exact hi.trans (reverseLowStageRun words k h t spare ht hn)

/-- The high phase uses the model's incremented left and decremented right registers. -/
theorem reverseHighStageIncRun (words : List U64) (k h : I64) (t spare : Nat)
    (ht : 2 * t + 2 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (reverseHighPhase 0 JuliaLean.base.int.bitreverse
      (int (t : Int) + int 1) (int ((words.length - t : Nat) : Int) - int 1) k
      (reverseLoopU words (t + 1))).run (dequeWordStore (reverseLowStageWords words k h t) spare) =
        (.ok (reverseLoopV words (t + 1)), dequeWordStore (reverseStageWords words k h (t + 1)) spare) := by
  have he : reverseHighPhase 0 JuliaLean.base.int.bitreverse
      (int (t : Int) + int 1) (int ((words.length - t : Nat) : Int) - int 1) k
      (reverseLoopU words (t + 1)) =
        reverseHighPhase 0 JuliaLean.base.int.bitreverse
          (int ((t + 1 : Nat) : Int)) (int ((words.length - t - 1 : Nat) : Int)) k
          (reverseLoopU words (t + 1)) := by
    rw [dequeNatAddOne, reverseNatPred (words.length - t) (by omega)]
  exact (congrArg (fun action : BitMutationM U64 =>
    action.run (dequeWordStore (reverseLowStageWords words k h t) spare)) he).trans
    (reverseHighStageRun words k h t spare ht hn)

/-- A one-word active interval terminates at the first loop check. -/
theorem reverseSingleStepRun (words : List U64) (k h : I64) (t spare : Nat)
    (hw : words.length = 2 * t + 1) (hn : words.length ≤ 9223372036854775807) :
    (reverseLoopStep 0 JuliaLean.base.int.bitreverse h k (reverseLoopRegisters words t)).run
      (dequeWordStore (reverseStageWords words k h t) spare) =
        (.ok (.done (int ((t + 1 : Nat) : Int), int ((words.length - t : Nat) : Int),
          reverseLoopU words t, reverseLoopV words t)),
          dequeWordStore (reverseStageWords words k h t) spare) := by
  have he : (int (t : Int) + int 1 == int ((words.length - t : Nat) : Int)) = true := by
    rw [dequeNatAddOne, reverseNatBeq (t + 1) (words.length - t) (by omega) (by omega)]
    simp only [show t + 1 = words.length - t by omega, decide_true]
  have hs := reverseStepDoneFirst 0 JuliaLean.base.int.bitreverse h k
    (int (t : Int)) (int ((words.length - t : Nat) : Int))
    (reverseLoopU words t) (reverseLoopV words t)
    (dequeWordStore (reverseStageWords words k h t) spare) he
  exact hs.trans (by rw [dequeNatAddOne])

/-- A two-word active interval terminates after completing its low transfer. -/
theorem reversePairStepRun (words : List U64) (k h : I64) (t spare : Nat)
    (hw : words.length = 2 * t + 2) (hn : words.length ≤ 9223372036854775807) :
    (reverseLoopStep 0 JuliaLean.base.int.bitreverse h k (reverseLoopRegisters words t)).run
      (dequeWordStore (reverseStageWords words k h t) spare) =
        (.ok (.done (int ((t + 1 : Nat) : Int), int ((words.length - t - 1 : Nat) : Int),
          reverseLoopU words (t + 1), reverseLoopV words t)),
          dequeWordStore (reverseLowStageWords words k h t) spare) := by
  have he1 : (int (t : Int) + int 1 == int ((words.length - t : Nat) : Int)) = false := by
    rw [dequeNatAddOne, reverseNatBeq (t + 1) (words.length - t) (by omega) (by omega)]
    simp only [show ¬ t + 1 = words.length - t by omega, decide_false]
  have he2 : (int (t : Int) + int 1 == int ((words.length - t : Nat) : Int) - int 1) = true := by
    rw [dequeNatAddOne, reverseNatPred (words.length - t) (by omega),
      reverseNatBeq (t + 1) (words.length - t - 1) (by omega) (by omega)]
    simp only [show t + 1 = words.length - t - 1 by omega, decide_true]
  have hl := reverseLowStageIncRun words k h t spare (by omega) hn
  have hs := reverseStepDoneSecond 0 JuliaLean.base.int.bitreverse h k
    (int (t : Int)) (int ((words.length - t : Nat) : Int))
    (reverseLoopU words t) (reverseLoopV words t) (reverseLoopU words (t + 1))
    (dequeWordStore (reverseStageWords words k h t) spare)
    (dequeWordStore (reverseLowStageWords words k h t) spare) he1 hl he2
  exact hs.trans (by rw [dequeNatAddOne, reverseNatPred (words.length - t) (by omega)])

/-- Every wider active interval performs a full step to the next packed stage. -/
theorem reverseFullStepRun (words : List U64) (k h : I64) (t spare : Nat)
    (hw : 2 * t + 2 < words.length) (hn : words.length ≤ 9223372036854775807) :
    (reverseLoopStep 0 JuliaLean.base.int.bitreverse h k (reverseLoopRegisters words t)).run
      (dequeWordStore (reverseStageWords words k h t) spare) =
        (.ok (.yield (reverseLoopRegisters words (t + 1))),
          dequeWordStore (reverseStageWords words k h (t + 1)) spare) := by
  have he1 : (int (t : Int) + int 1 == int ((words.length - t : Nat) : Int)) = false := by
    rw [dequeNatAddOne, reverseNatBeq (t + 1) (words.length - t) (by omega) (by omega)]
    simp only [show ¬ t + 1 = words.length - t by omega, decide_false]
  have he2 : (int (t : Int) + int 1 == int ((words.length - t : Nat) : Int) - int 1) = false := by
    rw [dequeNatAddOne, reverseNatPred (words.length - t) (by omega),
      reverseNatBeq (t + 1) (words.length - t - 1) (by omega) (by omega)]
    simp only [show ¬ t + 1 = words.length - t - 1 by omega, decide_false]
  have hl := reverseLowStageIncRun words k h t spare (by omega) hn
  have hh := reverseHighStageIncRun words k h t spare hw hn
  have hs := reverseStepYieldFrom 0 JuliaLean.base.int.bitreverse h k
    (int (t : Int)) (int ((words.length - t : Nat) : Int))
    (reverseLoopU words t) (reverseLoopV words t) (reverseLoopU words (t + 1)) (reverseLoopV words (t + 1))
    (dequeWordStore (reverseStageWords words k h t) spare)
    (dequeWordStore (reverseLowStageWords words k h t) spare)
    (dequeWordStore (reverseStageWords words k h (t + 1)) spare) he1 hl he2 hh
  exact hs.trans (by
    rw [dequeNatAddOne, reverseNatPred (words.length - t) (by omega), Nat.sub_sub]
    rfl)

/-- The reversal loop terminates from every active stage and its center completion produces all output words. -/
theorem reverseLoopStages (words : List U64) (k h : I64) (spare t : Nat)
    (B : BitArray 1) (hb : B.chunks = 0)
    (ht : 2 * t < words.length) (hn : words.length ≤ 9223372036854775807) :
    ∃ (r : ReverseRegisters) (mid : State),
      (reverseLoop 0 JuliaLean.base.int.bitreverse h k (reverseLoopRegisters words t)).run
        (dequeWordStore (reverseStageWords words k h t) spare) = (.ok r, mid) ∧
      (reverseFinish B Round5.Round2.isOddIntegerModel h k r).run mid =
        (.ok B, dequeWordStore (reverseOutputWords words k h) spare) := by
  by_cases hsingle : words.length = 2 * t + 1
  · let r : ReverseRegisters :=
      (int ((t + 1 : Nat) : Int), int ((words.length - t : Nat) : Int),
        reverseLoopU words t, reverseLoopV words t)
    refine ⟨r, dequeWordStore (reverseStageWords words k h t) spare, ?_,
      reverseSingleFinishRun words k h t spare B hb hsingle hn⟩
    exact reverseLoopDone (fun _ r => reverseLoopStep 0 JuliaLean.base.int.bitreverse h k r)
      (reverseLoopRegisters words t) r _ _ (reverseSingleStepRun words k h t spare hsingle hn)
  · by_cases hpair : words.length = 2 * t + 2
    · let r : ReverseRegisters :=
        (int ((t + 1 : Nat) : Int), int ((words.length - t - 1 : Nat) : Int),
          reverseLoopU words (t + 1), reverseLoopV words t)
      refine ⟨r, dequeWordStore (reverseLowStageWords words k h t) spare, ?_,
        reversePairFinishRun words k h t spare B hb hpair hn⟩
      exact reverseLoopDone (fun _ r => reverseLoopStep 0 JuliaLean.base.int.bitreverse h k r)
        (reverseLoopRegisters words t) r _ _ (reversePairStepRun words k h t spare hpair hn)
    · have hwide : 2 * t + 2 < words.length := by omega
      obtain ⟨r, mid, hloop, hfinish⟩ :=
        reverseLoopStages words k h spare (t + 1) B hb (by omega) hn
      refine ⟨r, mid, ?_, hfinish⟩
      exact reverseLoopYield (fun _ r => reverseLoopStep 0 JuliaLean.base.int.bitreverse h k r)
        (reverseLoopRegisters words t) (reverseLoopRegisters words (t + 1)) r _ _ _
        (reverseFullStepRun words k h t spare hwide hn) hloop
termination_by words.length - 2 * t
decreasing_by omega

/-- The initialized reversal loop and its center completion compute the complete packed output. -/
theorem reverseLoopComplete (words : List U64) (k h : I64) (spare : Nat)
    (B : BitArray 1) (hb : B.chunks = 0)
    (hp : 0 < words.length) (hn : words.length ≤ 9223372036854775807) :
    ∃ (r : ReverseRegisters) (mid : State),
      (reverseLoop 0 JuliaLean.base.int.bitreverse h k
        (int 0, int words.length, u64 0,
          JuliaLean.base.int.bitreverse (words.getD (words.length - 1) (u64 0)))).run
        (dequeWordStore (words.set (words.length - 1) (u64 0)) spare) = (.ok r, mid) ∧
      (reverseFinish B Round5.Round2.isOddIntegerModel h k r).run mid =
        (.ok B, dequeWordStore (reverseOutputWords words k h) spare) := by
  obtain ⟨r, mid, hloop, hfinish⟩ := reverseLoopStages words k h spare 0 B hb (by omega) hn
  refine ⟨r, mid, ?_, hfinish⟩
  have hargs :
      ((int 0, int words.length, u64 0,
        JuliaLean.base.int.bitreverse (words.getD (words.length - 1) (u64 0))),
        dequeWordStore (words.set (words.length - 1) (u64 0)) spare) =
      (reverseLoopRegisters words 0, dequeWordStore (reverseStageWords words k h 0) spare) := by
    rw [reverseStageInitial words k h hp]
    simp only [reverseLoopRegisters, reverseLoopU, reverseLoopV, Nat.sub_zero, ite_true]
    rfl
  exact (congrArg (fun rs : ReverseRegisters × State =>
    (reverseLoop 0 JuliaLean.base.int.bitreverse h k rs.1).run rs.2) hargs).trans hloop
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Completed reversal on a canonical store is assembled from preparation and loop completion. -/
theorem reverseWordRun (words : List U64) (k h : I64) (spare : Nat) (B : BitArray 1)
    (hb : B.chunks = 0) (hp : 0 < words.length) (hn : words.length ≤ 9223372036854775807)
    (hz : (B.len == int 0) = false)
    (hk : mod64 (B.len + int 63) + int 1 = k) (hh : int 64 - k = h) :
    (bitVectorReverseInPlace JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel B).run
      (dequeWordStore words spare) =
        (.ok B, dequeWordStore (reverseOutputWords words k h) spare) := by
  obtain ⟨r, mid, hloop, hfinish⟩ := reverseLoopComplete words k h spare B hb hp hn
  have hlast : words.length - 1 + 1 = words.length := by omega
  have hread := dequeWordRead words spare (words.length - 1) hn (by omega)
  have hclear := dequeWordSet words spare (words.length - 1) (u64 0) hn (by omega)
  rw [hlast] at hread hclear
  apply reverseRunFrom JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel B B
    h k (int words.length) (words.getD (words.length - 1) (u64 0)) r
    (dequeWordStore words spare)
    (dequeWordStore (words.set (words.length - 1) (u64 0)) spare) mid
    (dequeWordStore (reverseOutputWords words k h) spare) hz hk hh
  · rw [hb]
    exact dequeWordLength words spare
  · rw [hb]
    exact hread
  · rw [hb]
    exact hclear
  · rw [hb]
    exact hloop
  · exact hfinish

/-- Complete successful execution installs precisely the encoding of logical reversal. -/
theorem reverseRunCanonical (xs : List Bool) (hp : 0 < xs.length)
    (hn : xs.length < Round5.maxVectorLength) :
    (bitVectorReverseInPlace JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel
      (vectorBits xs)).run (initWords (encodeBits xs)) =
        (.ok (vectorBits xs), initWords (encodeBits xs.reverse)) := by
  have hbits : xs.length ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hn
    omega
  have hpos : 0 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hwords : (encodeBits xs).length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hbits
  have hz : ((vectorBits xs).len == int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    change (int xs.length).val = 0 at hv
    rw [packedInt_val xs.length hbits] at hv
    omega
  have hr := reverseWordRun (encodeBits xs) (int (reverseValidBits xs.length))
    (int (reversePadding xs.length)) 32 (vectorBits xs) rfl hpos hwords hz
    (reverseMachineK xs.length hp hn) (reverseMachineH xs.length hp)
  rw [reverseOutputWordsEncode xs hp] at hr
  simpa only [dequeWordStoreInitial] using hr

/-- Successful reversal preserves the exact logical bits and zero padding. -/
theorem reverseSuccess (xs : List Bool) (hp : 0 < xs.length)
    (hn : xs.length < Round5.maxVectorLength) :
    ∃ s',
      (bitVectorReverseInPlace JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel
        (vectorBits xs)).run (initWords (encodeBits xs)) = (.ok (vectorBits xs), s') ∧
      bitValues s' (vectorBits xs) = xs.reverse ∧ Round5.Round2.PackedInvariant s' (vectorBits xs) := by
  have hbits : xs.reverse.length ≤ 9223372036854775807 := by
    rw [List.length_reverse]
    change xs.length < 4611686018427387903 at hn
    omega
  refine ⟨initWords (encodeBits xs.reverse), reverseRunCanonical xs hp hn, ?_, ?_⟩
  · simpa only [List.length_reverse, vectorBits] using
      scalar_bits_initial (N := 1) xs.reverse [int xs.length] hbits
  · simpa only [List.length_reverse, vectorBits] using
      scalar_initial_invariant (N := 1) xs.reverse [int xs.length] hbits

/-- The frozen reversal observations, with its execution pair held abstract. -/
def reverseObservation (xs : List Bool) (B : BitVector)
    (result : Id (Except Error BitVector × MutableMemory U64)) : Prop :=
  JuliaLean.Proofs.base.bitarray.DeleteatRangeInsideAgrees.match_1 (fun _ => Prop) result
    (fun _ state' => bitValues state' B = xs.reverse ∧ Round5.Round2.PackedInvariant state' B)
    (fun _ _ => False)

/-- A successful abstract reversal result supplies the frozen observations. -/
theorem reverseObservationOk (xs : List Bool) (B : BitVector)
    (result : Id (Except Error BitVector × MutableMemory U64)) (out : State)
    (hr : result = (.ok B, out))
    (hv : bitValues out B = xs.reverse) (hi : Round5.Round2.PackedInvariant out B) :
    reverseObservation xs B result := by
  rw [hr]
  exact ⟨hv, hi⟩
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The frozen reversal observation, retaining its operation dependency so both definitions reduce together. -/
def reverseHighObservation (xs : List Bool) (B : BitVector)
    (result : Id (Except Error BitVector × MutableMemory U64)) : Prop :=
  let _operation := bitVectorReverseInPlace JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel
  JuliaLean.Proofs.base.bitarray.DeleteatRangeInsideAgrees.match_1 (fun _ => Prop) result
    (fun _ state' => bitValues state' B = xs.reverse ∧ Round5.Round2.PackedInvariant state' B)
    (fun _ _ => False)

set_option linter.constructorNameAsVariable false in
theorem reverseHighBridge (xs : List Bool) :
    reverseHighObservation xs (vectorBits xs)
      ((bitVectorReverseInPlace JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel
        (vectorBits xs)).run (initWords (encodeBits xs))) →
      Round5.Round2.ReverseAgrees xs := by
  intro h
  assumption

/-- A successful abstract result supplies the height-balanced reversal observations. -/
theorem reverseHighObservationOk (xs : List Bool) (B : BitVector)
    (result : Id (Except Error BitVector × MutableMemory U64)) (out : State)
    (hr : result = (.ok B, out))
    (hv : bitValues out B = xs.reverse) (hi : Round5.Round2.PackedInvariant out B) :
    reverseHighObservation xs B result := by
  rw [hr]
  exact ⟨hv, hi⟩

/-- Reversal has the canonical packed result for empty and nonempty vectors alike. -/
theorem reverseRunAll (xs : List Bool) (hn : xs.length < Round5.maxVectorLength) :
    (bitVectorReverseInPlace JuliaLean.base.int.bitreverse Round5.Round2.isOddIntegerModel
      (vectorBits xs)).run (initWords (encodeBits xs)) =
        (.ok (vectorBits xs), initWords (encodeBits xs.reverse)) := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    exact reverseRunCanonical (b :: xs) (by simp only [List.length_cons]; omega) hn

/-- In-place reversal reverses every logical bit while preserving its exact packed representation. -/
theorem BitarraysReverse_proven : JuliaLean.Proofs.base.bitarray.Round5.ReverseAgrees := by
  intro xs hn
  have hb : xs.reverse.length ≤ 9223372036854775807 := by
    rw [List.length_reverse]
    change xs.length < 4611686018427387903 at hn
    omega
  have hv : bitValues (initWords (encodeBits xs.reverse)) (vectorBits xs) = xs.reverse := by
    simpa only [List.length_reverse, vectorBits] using
      scalar_bits_initial (N := 1) xs.reverse [int xs.length] hb
  have hi : Round5.Round2.PackedInvariant (initWords (encodeBits xs.reverse)) (vectorBits xs) := by
    simpa only [List.length_reverse, vectorBits] using
      scalar_initial_invariant (N := 1) xs.reverse [int xs.length] hb
  with_reducible exact (@reverseHighBridge xs
    (@reverseHighObservationOk xs (vectorBits xs) _
      (initWords (encodeBits xs.reverse)) (reverseRunAll xs hn) hv hi))
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesReverse1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-reverse-dims-empty", juliaFile := "base/bitarray.jl", juliaFns := ["reverse(::BitArray; dims)", "_reverse(::BitArray, ::Int)"],
    statement := "reverse(A; dims=d) on a BitArray of any size agrees with Array{Bool}, including empty arrays.", source := "reverse docstring (base/arraymath.jl: reverse A along dimension dims); invariant: BitArray behaves as Array{Bool}",
    status := .todo, prop := ``ReverseDimsAgrees, thm := none, notes := "No complete exact proof returned. dims=[-1,-1], xs=[true], axis=1 is an additional impossible-shape witness, so nonnegative native-shape bounds alone do not repair the target and general reverseAxisBits agreement remains unproved." },
  { id := "bitarrays-reverse-dims", juliaFile := "base/bitarray.jl", juliaFns := ["reverse(::BitArray; dims)", "_reverse(::BitArray, ::Int)", "copy_chunks!"],
    statement := "For BitArrays without an empty dimension, reverse(A; dims=d) agrees with Array{Bool} and returns a valid BitArray.", source := "reverse docstring; unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``ReverseDimsNonemptyAgrees, thm := none, notes := "No complete exact proof returned. complete positive-shape reversal remains blocked by the source-index mismatch for a 130-by-2 matrix reversed along dimension 2." },
  { id := "bitarrays-reverse", juliaFile := "base/bitarray.jl", juliaFns := ["reverse!(::BitVector)", "_reverse!(::BitVector, ::Colon)"],
    statement := "reverse! reverses logical bits and preserves the chunk count and zero padding.", source := "base/bitarray.jl:1272-1325; unused bits are zero (base/bitarray.jl:5-6)",
    status := .proven, prop := ``Round5.ReverseAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group1.BitarraysReverse_proven }
]
end JuliaLean.Proofs.base.bitarray

