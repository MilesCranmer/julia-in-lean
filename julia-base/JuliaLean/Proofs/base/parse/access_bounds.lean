import JuliaLean.Proofs.base.abstractarray.common.input_invariants
import JuliaLean.base.parse

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Byte reads performed by `skipspace`, including its ASCII and decoded
Unicode whitespace branches, `base/parse.jl:68-82`. -/
def skipspaceAccessesLoop (s : ParsePrint.IntParse.Bytes) (j : Int) : Nat → Int → List Int
  | 0, _ => []
  | fuel + 1, i =>
    if i ≤ j then
      let b := ParsePrint.IntParse.cu s i
      i :: if ParsePrint.IntParse.isspaceAscii b then
        skipspaceAccessesLoop s j fuel (i + 1)
      else if b.val ≥ 0x80 ∧ ParsePrint.IntParse.skipspacechar s i > i then
        skipspaceAccessesLoop s j fuel (ParsePrint.IntParse.skipspacechar s i)
      else []
    else []

def skipspaceAccesses (s : ParsePrint.IntParse.Bytes) (i j : Int) : List Int :=
  skipspaceAccessesLoop s j (s.length + 1) i

/-- Byte reads performed by `skipspace_back`, `base/parse.jl:84-97`. -/
def skipspaceBackAccessesLoop (s : ParsePrint.IntParse.Bytes) (lo : Int) : Nat → Int → List Int
  | 0, _ => []
  | fuel + 1, j =>
    if j ≥ lo then
      let b := ParsePrint.IntParse.cu s j
      j :: if ParsePrint.IntParse.isspaceAscii b then
        skipspaceBackAccessesLoop s lo fuel (j - 1)
      else if b.val ≥ 0x80 ∧ ParsePrint.IntParse.skipspacecharBack s lo j < j then
        skipspaceBackAccessesLoop s lo fuel (ParsePrint.IntParse.skipspacecharBack s lo j)
      else []
    else []

def skipspaceBackAccesses (s : ParsePrint.IntParse.Bytes) (i j : Int) : List Int :=
  skipspaceBackAccessesLoop s i (s.length + 1) j

/-- Reads made by `parseint_preamble` after the `skipspace` calls compute its
current index, `base/parse.jl:99-123`. -/
def preambleAccesses (signed : Bool) (base : Int) (s : ParsePrint.IntParse.Bytes)
    (start stop : Int) : List Int :=
  let firstReads := skipspaceAccesses s start stop
  let i1 := ParsePrint.IntParse.skipspace s start stop
  let signReads := if signed ∧ i1 ≤ stop then [i1] else []
  let secondReads := skipspaceAccesses s (i1 + 1) stop
  let i2 := ParsePrint.IntParse.skipspace s (i1 + 1) stop
  let prefixReads1 := if base = 0 ∧ i1 < stop then [i1, i1 + 1] else []
  let prefixReads2 := if base = 0 ∧ i2 < stop then [i2, i2 + 1] else []
  firstReads ++ signReads ++ secondReads ++ prefixReads1 ++ prefixReads2

/-- Candidate trailing-scan reads for a digit position computed by a preamble
branch. The source calls the scan only for a nonzero in-range digit position. -/
def guardedParseBackReads (s : ParsePrint.IntParse.Bytes) (d j : Int) : List Int :=
  if 1 ≤ d ∧ d ≤ j then skipspaceBackAccesses s d j else []

/-- All reads at the eight listed sites in `parseint_utf8`, starting from the
public `parse`/`tryparse` inputs `i = 1`, `j = ncodeunits(s)`. This is the union
of the fast path, unsigned and signed preamble paths, prefix branches, and
their possible trailing scans. -/
def integerParseAccesses (t : IntTy) (s : ParsePrint.IntParse.Bytes) (base : Int) : List Int :=
  let j : Int := s.length
  let fastReads := if 1 ≤ j then [1, j] ++ if 2 ≤ j then [2] else [] else []
  let i1 := ParsePrint.IntParse.skipspace s 1 j
  let i2 := ParsePrint.IntParse.skipspace s (i1 + 1) j
  fastReads ++ preambleAccesses t.signed base s 1 j ++
    guardedParseBackReads s i1 j ++ guardedParseBackReads s (i1 + 2) j ++
    guardedParseBackReads s i2 j ++ guardedParseBackReads s (i2 + 2) j

def IntegerParseSafe : Prop :=
  ∀ (t : IntTy) (s : ParsePrint.IntParse.Bytes) base i,
    i ∈ integerParseAccesses t s base → inAxis 1 s.length i

private theorem skipspaceLoop_result_lower (s : ParsePrint.IntParse.Bytes) (j : Int) :
    ∀ (fuel : Nat) (i : Int), 1 ≤ i →
      1 ≤ ParsePrint.IntParse.skipspaceLoop s j fuel i
  | 0, _, h1 => h1
  | fuel + 1, i, h1 => by
      simp only [ParsePrint.IntParse.skipspaceLoop]
      split
      · split
        · exact skipspaceLoop_result_lower s j fuel (i + 1) (by omega)
        · split
          · rename_i hnext
            exact skipspaceLoop_result_lower s j fuel
              (ParsePrint.IntParse.skipspacechar s i) (by omega)
          · exact h1
      · exact h1

private theorem skipspace_result_lower (s : ParsePrint.IntParse.Bytes) (i j : Int)
    (h1 : 1 ≤ i) : 1 ≤ ParsePrint.IntParse.skipspace s i j := by
  exact skipspaceLoop_result_lower s j (s.length + 1) i h1

private theorem skipspaceAccessesLoop_safe (s : ParsePrint.IntParse.Bytes) (j : Int)
    (hj : j ≤ s.length) : ∀ (fuel : Nat) (i q : Int), 1 ≤ i →
      q ∈ skipspaceAccessesLoop s j fuel i → inAxis 1 s.length q
  | 0, _, q, _, hq => by simp [skipspaceAccessesLoop] at hq
  | fuel + 1, i, q, h1, hq => by
      simp only [skipspaceAccessesLoop] at hq
      split at hq
      · rename_i hij
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · unfold inAxis
          omega
        · split at hq
          · exact skipspaceAccessesLoop_safe s j hj fuel (i + 1) q
              (by omega) hq
          · split at hq
            · rename_i hnext
              exact skipspaceAccessesLoop_safe s j hj fuel
                (ParsePrint.IntParse.skipspacechar s i) q (by omega) hq
            · simp at hq
      · simp at hq

private theorem skipspaceAccesses_safe (s : ParsePrint.IntParse.Bytes) (i j q : Int)
    (h1 : 1 ≤ i) (hj : j ≤ s.length)
    (hq : q ∈ skipspaceAccesses s i j) : inAxis 1 s.length q :=
  skipspaceAccessesLoop_safe s j hj (s.length + 1) i q h1 hq

private theorem skipspacecharBack_lower (s : ParsePrint.IntParse.Bytes) (lo j : Int)
    (h : lo ≤ j) :
    lo - 1 ≤ ParsePrint.IntParse.skipspacecharBack s lo j := by
  unfold ParsePrint.IntParse.skipspacecharBack
  dsimp only
  split <;> omega

private theorem skipspaceBackAccessesLoop_safe (s : ParsePrint.IntParse.Bytes) (lo : Int)
    (hlo : 1 ≤ lo) : ∀ (fuel : Nat) (j q : Int), j ≤ s.length →
      q ∈ skipspaceBackAccessesLoop s lo fuel j → inAxis 1 s.length q
  | 0, _, q, _, hq => by simp [skipspaceBackAccessesLoop] at hq
  | fuel + 1, j, q, hj, hq => by
      simp only [skipspaceBackAccessesLoop] at hq
      split at hq
      · rename_i hji
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · unfold inAxis
          omega
        · split at hq
          · exact skipspaceBackAccessesLoop_safe s lo hlo fuel (j - 1) q (by omega) hq
          · split at hq
            · have hb := skipspacecharBack_lower s lo j hji
              exact skipspaceBackAccessesLoop_safe s lo hlo fuel
                (ParsePrint.IntParse.skipspacecharBack s lo j) q (by omega) hq
            · simp at hq
      · simp at hq

private theorem skipspaceBackAccesses_safe (s : ParsePrint.IntParse.Bytes) (lo j q : Int)
    (hlo : 1 ≤ lo) (hj : j ≤ s.length) (hq : q ∈ skipspaceBackAccesses s lo j) :
    inAxis 1 s.length q :=
  skipspaceBackAccessesLoop_safe s lo hlo (s.length + 1) j q hj hq

private theorem preambleAccesses_safe (signed : Bool) (base : Int)
    (s : ParsePrint.IntParse.Bytes) (q : Int)
    (hq : q ∈ preambleAccesses signed base s 1 s.length) : inAxis 1 s.length q := by
  have hi1 := skipspace_result_lower s 1 s.length (by omega)
  have hi2 := skipspace_result_lower s
    (ParsePrint.IntParse.skipspace s 1 s.length + 1) s.length (by omega)
  unfold preambleAccesses at hq
  dsimp only at hq
  simp only [List.mem_append] at hq
  rcases hq with (((hfirst | hsign) | hsecond) | hprefix1) | hprefix2
  · exact skipspaceAccesses_safe s 1 s.length q (by omega) (by omega) hfirst
  · split at hsign
    · simp only [List.mem_singleton] at hsign
      subst q
      unfold inAxis
      omega
    · simp at hsign
  · exact skipspaceAccesses_safe s _ s.length q (by omega) (by omega) hsecond
  · split at hprefix1
    · simp only [List.mem_cons] at hprefix1
      rcases hprefix1 with rfl | hprefix1
      · unfold inAxis
        omega
      · rcases hprefix1 with rfl | hnil
        · unfold inAxis
          omega
        · cases hnil
    · simp at hprefix1
  · split at hprefix2
    · simp only [List.mem_cons] at hprefix2
      rcases hprefix2 with rfl | hprefix2
      · unfold inAxis
        omega
      · rcases hprefix2 with rfl | hnil
        · unfold inAxis
          omega
        · cases hnil
    · simp at hprefix2

theorem integerParseSafe_proven : IntegerParseSafe := by
  intro t s base q hq
  unfold integerParseAccesses at hq
  dsimp only at hq
  simp only [List.mem_append] at hq
  rcases hq with (((((hfast | hpreamble) | hback1) | hback2) | hback3) | hback4)
  · by_cases hlen : 1 ≤ (s.length : Int)
    · by_cases htwo : 2 ≤ (s.length : Int)
      · simp [hlen, htwo] at hfast
        rcases hfast with rfl | rfl | rfl <;> unfold inAxis <;> omega
      · simp [hlen, htwo] at hfast
        rcases hfast with rfl | rfl <;> unfold inAxis <;> omega
    · simp [hlen] at hfast
  · exact preambleAccesses_safe t.signed base s q hpreamble
  all_goals
    unfold guardedParseBackReads at *
    split at *
    · rename_i hguard
      exact skipspaceBackAccesses_safe s _ s.length q hguard.1 (by omega) ‹_›
    · simp_all

end JuliaLean.MemSafety.G3
