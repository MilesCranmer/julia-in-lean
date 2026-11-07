import JuliaLean.base.rawbigfloats
import JuliaLean.base.gmp
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.rawbigfloats

open JuliaLean JuliaLean.base.rawbigfloats

/-- Word and bit access contracts for the installed source model, including
machine-Int wraparound and the complete out-of-range bit domain. -/
def RawCountingAndIndexingCorrect : Prop :=
  ∀ (Word R : Type) (ops : Ops Word R),
    (∀ x : BigFloatData Word, elemCountWords x = JInt.wrap .i64 (x.length : Int)) ∧
    (∀ x : BigFloatData Word, elemCountDataBits ops x =
      (ops.wordBytes * int 8) * JInt.wrap .i64 (x.length : Int)) ∧
    (∀ (x : BigFloatData Word) (i : I),
      getElemDescending (fun data (_ : Unit) => elemCountWords data)
        (fun data index (_ : Unit) => getElemWordsAscending ops data index) x i () =
      ops.wordAtUnchecked x (elemCountWords x - i - int 1 + int 1)) ∧
    (∀ (x : BigFloatData Word) (i : I),
      (i < int 0 ∨ elemCountDataBits ops x ≤ i) →
        getElemDataBitAscending ops x i = .ok false) ∧
    (∀ n i : I, reversedIndexInt n i = n - i - int 1) ∧
    (∀ (x : BigFloatData Word) (i : I),
      splitBitIndex ops x i = ops.divremToZero i (ops.wordBytes * int 8))

theorem rawCountingAndIndexingCorrect : RawCountingAndIndexingCorrect := by
  intro Word R ops
  refine ⟨by intro; rfl, by intro; rfl, by intros; rfl, ?_, by intros; rfl,
    by intros; rfl⟩
  intro x i h
  unfold getElemDataBitAscending
  split
  · rename_i hin
    change i.val < (int 0).val ∨ (elemCountDataBits ops x).val ≤ i.val at h
    change (int 0).val ≤ i.val ∧ i.val < (elemCountDataBits ops x).val at hin
    omega
  · rfl

/-- The tail scan preserves short-circuiting and propagates division errors. -/
def RawTailCorrect : Prop :=
  ∀ (Word R : Type) (ops : Ops Word R),
    (∀ (x : BigFloatData Word) (len : I),
      tailWordsNonzero ops x len =
        ops.anyIntRange (fun i => !ops.wordIsZero
          (ops.wordAtUnchecked x (i + int 1))) (int 0) (len - int 1)) ∧
    (∀ (x : BigFloatData Word) (len : I),
      tailBitsNonzero ops x len =
        if int 0 < len then do
          let (q, r) ← ops.divremToZero len (ops.wordBytes * int 8)
          if r != int 0 && !ops.wordIsZero
              (ops.wordShiftLeft (ops.wordAtUnchecked x (q + int 1))
                (ops.wordBytes * int 8 - r)) then pure true
          else pure (tailWordsNonzero ops x q)
        else pure false)

theorem rawTailCorrect : RawTailCorrect := by
  intro Word R ops
  exact ⟨by intros; rfl, by intros; rfl⟩

/-- Chunked word truncation must agree with consuming descending bits, with
zero extension. The cached bits and sticky tail use machine-Int indexing. -/
def RawTruncationAndRoundingCorrect : Prop :=
  (∀ (ops : Ops (JInt .u64) JuliaLean.base.gmp.BigInt)
      (x : BigFloatData (JInt .u64)) (len : I),
    (truncated ops x len).map (fun result => result.val) =
      (List.range len.val.toNat).foldlM (fun acc i => do
        let bit ← getElemDataBitAscending ops x
          (elemCountDataBits ops x - int (Int.ofNat i) - int 1)
        pure (2 * acc + if bit then 1 else 0)) (0 : Int)) ∧
  (∀ (Word R : Type) (ops : Ops Word R)
      (x : BigFloatData Word) (len : I) (h : BigFloatDataRoundingIncrementHelper Word),
    roundingHelperInner ops x len = .ok h →
      h.n = x ∧ h.truncLen = len ∧
      getElemDataBitAscending ops x
        (elemCountDataBits ops x - (len - int 1) - int 1) = .ok h.finalBit ∧
      getElemDataBitAscending ops x
        (elemCountDataBits ops x - len - int 1) = .ok h.roundBit ∧
      roundingFinalBit h = h.finalBit ∧ roundingRoundBit h = h.roundBit ∧
      roundingStickyBit ops h =
        tailBitsNonzero ops x (elemCountDataBits ops x - len - int 1))

open JuliaLean.Registry

def entries : List Entry := [
  { id := "bignumscov-raw-count-index", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["elem_count", "word_length", "reversed_index", "split_bit_index", "get_elem words", "get_elem bits"]
    statement := "Raw BigFloat word and bit counts, zero-based ascending access, descending reversal, and out-of-range bit behavior follow the source formulas."
    source := "base/rawbigfloats.jl:5-24,66-81"
    status := .proven, prop := ``RawCountingAndIndexingCorrect, thm := some ``rawCountingAndIndexingCorrect },
  { id := "bignumscov-raw-tail", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["word_is_nonzero", "tail_is_nonzero words", "tail_is_nonzero word", "tail_is_nonzero bits"]
    statement := "Raw BigFloat tail predicates scan exactly the requested least-significant words and the quotient/remainder bit tail, returning false for a zero bit length."
    source := "base/rawbigfloats.jl:26-60"
    status := .proven, prop := ``RawTailCorrect, thm := some ``rawTailCorrect },
  { id := "bignumscov-raw-trunc-round", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["truncated", "BigFloatDataRoundingIncrementHelper", "FinalBit", "RoundBit", "StickyBit"]
    statement := "Truncation consumes descending significant bits with zero extension, and the rounding helper caches the final and round bits while computing sticky bits from the remaining tail."
    source := "base/rawbigfloats.jl:89-142"
    status := .todo, prop := ``RawTruncationAndRoundingCorrect, thm := none
    notes := "Retired JuliaLean.BigNumsCov.Raw.rawTruncationAndRoundingCorrect at a2fd59b64fda5264fda1337c1534d56a17b98872; the installed chunked word fold needs a proof of equivalence to the old bit-at-a-time specification, including the native Ops installation." }
]

end JuliaLean.Proofs.base.rawbigfloats
