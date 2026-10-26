import JuliaLean.BigNumsCov.Common

/-!
Behavioral model of `base/rawbigfloats.jl` at master `bbfa0ce4150`.
Words are represented by natural numbers and the platform word width is the
64-bit width used by the pinned Linux build.  Zero-based indexing and the
descending-to-ascending conversion follow the Julia source directly.
-/

namespace JuliaLean.BigNumsCov.Raw

def wordBits : Nat := 64

/-- `elem_count(x, Val(:words))`, lines 5 and 8. -/
def elemCountWords (x : List Nat) : Nat := x.length

/-- `elem_count(x, Val(:bits))`, lines 6-8. -/
def elemCountBits (x : List Nat) : Nat := wordBits * elemCountWords x

/-- `reversed_index(n, i) = n - i - 1`, line 9, on valid natural indices. -/
def reversedIndex (n i : Nat) : Nat := n - i - 1

/-- Machine-Int form of `reversed_index`, including wrapping subtraction. -/
def reversedIndex64 (n i : JInt64) : JInt64 := n - i - JInt.lit .i64 1

/-- `split_bit_index`, line 11. -/
def splitBitIndex (i : Nat) : Nat × Nat := (i / wordBits, i % wordBits)

def splitBitIndex64 (i : JInt64) : Int × Int := (i.val.tdiv 64, i.val.tmod 64)

/-- Ascending zero-based word access, lines 17-19. -/
def getWordAscending (x : List Nat) (i : Nat) : Option Nat := x[i]?

/-- Descending word access after `reversed_index`, lines 21-24. -/
def getWordDescending (x : List Nat) (i : Nat) : Option Nat :=
  getWordAscending x (reversedIndex x.length i)

/-- The zero-based bit method for an unsigned word, lines 66-68. -/
def getUnsignedBit (x i : Nat) : Bool :=
  x / 2 ^ i % 2 == 1

/-- Checked BigFloatData bit access, lines 73-81. -/
def getDataBitAscending (x : List Nat) (i : Nat) : Bool :=
  if i < elemCountBits x then
    let (wordIndex, bitIndex) := splitBitIndex i
    match getWordAscending x wordIndex with
    | some word => getUnsignedBit word bitIndex
    | none => false
  else false

def getDataBitAscendingInt (x : List Nat) (i : Int) : Bool :=
  if i < 0 then false else getDataBitAscending x i.toNat

/-- Descending bit access obtained through lines 9-10 and 21-24. -/
def getDataBitDescending (x : List Nat) (i : Nat) : Bool :=
  if i < elemCountBits x then
    getDataBitAscending x (reversedIndex (elemCountBits x) i)
  else false

/-- `word_is_nonzero`, lines 26-30. -/
def wordIsNonzero (x : List Nat) (i : Nat) (descending : Bool) : Bool :=
  let word := if descending then getWordDescending x i else getWordAscending x i
  word.any (· != 0)

/-- Least-significant-word scan, lines 36-38. -/
def tailWordsNonzero (x : List Nat) (len : Nat) : Bool :=
  (List.range len).any (wordIsNonzero x · false)

/-- Least-significant-bit scan within one word, lines 44-47. -/
def tailWordNonzero (x : List Nat) (len i : Nat) : Bool :=
  if len = 0 then false
  else match getWordAscending x i with
    | none => false
    | some word => word % 2 ^ len != 0

/-- Least-significant-bit scan of the whole data, lines 53-60. -/
def tailBitsNonzero (x : List Nat) (len : Nat) : Bool :=
  if len = 0 then false
  else
    let (wordCount, bitCount) := splitBitIndex len
    tailWordNonzero x bitCount wordCount || tailWordsNonzero x wordCount

def tailBitsNonzeroInt (x : List Nat) (len : Int) : Bool :=
  if 0 < len then tailBitsNonzero x len.toNat else false

/-- `truncated`, lines 89-114: take descending high bits and zero-extend. -/
def truncated (x : List Nat) (len : Nat) : Nat :=
  (List.range len).foldl
    (fun acc i => 2 * acc + if getDataBitDescending x i then 1 else 0) 0

def truncatedInt (x : List Nat) (len : Int) : Nat :=
  if 0 < len then truncated x len.toNat else 0

/-- Cached final/round bits and sticky callback, lines 116-142. -/
structure RoundingHelper where
  data : List Nat
  truncLen : Nat
  finalBit : Bool
  roundBit : Bool
  deriving Repr, DecidableEq

def roundingHelper (x : List Nat) (len : Nat) : RoundingHelper :=
  { data := x
    truncLen := len
    finalBit := if len = 0 then false else getDataBitDescending x (len - 1)
    roundBit := getDataBitDescending x len }

def stickyBit (h : RoundingHelper) : Bool :=
  tailBitsNonzero h.data (elemCountBits h.data - h.truncLen - 1)

def RawCountingAndIndexingCorrect : Prop :=
  (∀ x, elemCountWords x = x.length) ∧
  (∀ x, elemCountBits x = 64 * x.length) ∧
  (∀ x i, getWordDescending x i = x[x.length - i - 1]?) ∧
  (∀ x i, elemCountBits x ≤ i → getDataBitAscending x i = false) ∧
  (∀ n i, reversedIndex64 n i = n - i - JInt.lit .i64 1) ∧
  (∀ i, splitBitIndex64 i = (i.val.tdiv 64, i.val.tmod 64)) ∧
  (∀ x i, i < 0 → getDataBitAscendingInt x i = false)

theorem rawCountingAndIndexingCorrect : RawCountingAndIndexingCorrect := by
  refine ⟨by intro; rfl, by intro; rfl, by intro x i; rfl, ?_, by intros; rfl,
    by intros; rfl, ?_⟩
  intro x i h
  simp only [getDataBitAscending]
  split
  · omega
  · rfl
  · intro x i h
    simp [getDataBitAscendingInt, h]

def RawTailCorrect : Prop :=
  (∀ x len, tailWordsNonzero x len =
    (List.range len).any (fun i => (x[i]?).any (· != 0))) ∧
  (∀ x len, tailBitsNonzero x len =
    if len = 0 then false else
      let q := len / 64
      let r := len % 64
      tailWordNonzero x r q || tailWordsNonzero x q) ∧
  (∀ x len, tailBitsNonzeroInt x len =
    if 0 < len then tailBitsNonzero x len.toNat else false)

theorem rawTailCorrect : RawTailCorrect := by
  refine ⟨?_, ?_, by intros; rfl⟩
  · intro x len
    rfl
  · intro x len
    simp [tailBitsNonzero, splitBitIndex, wordBits]

def RawTruncationAndRoundingCorrect : Prop :=
  (∀ x len, truncated x len =
    (List.range len).foldl
      (fun acc i => 2 * acc + if getDataBitDescending x i then 1 else 0) 0) ∧
  (∀ x len,
    let h := roundingHelper x len
    h.finalBit = (if len = 0 then false else getDataBitDescending x (len - 1)) ∧
    h.roundBit = getDataBitDescending x len ∧
    stickyBit h = tailBitsNonzero x (elemCountBits x - len - 1)) ∧
  (∀ x len, truncatedInt x len = if 0 < len then truncated x len.toNat else 0)

theorem rawTruncationAndRoundingCorrect : RawTruncationAndRoundingCorrect := by
  refine ⟨?_, ?_, by intros; rfl⟩
  · intro x len
    rfl
  · intro x len
    simp [roundingHelper, stickyBit]

end JuliaLean.BigNumsCov.Raw
