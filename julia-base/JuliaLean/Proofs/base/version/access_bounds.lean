import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-! ## `base/version.jl` -/

/-- Comparison outcomes for one `VersionRange`. The functions stand for the
two source comparisons at version.jl:548 and 553 on the actual versions. -/
structure VersionRangeComparisons where
  lowerAccepts : Nat → Bool
  upperAccepts : Nat → Bool

inductive VersionMatchAccess where
  | version (index : Nat)
  | dest (index : Nat)

mutual
  /-- The first `while` at version.jl:547-550. The `i ≤ n` check occurs before
  each recorded access. -/
  def versionLowerScan (range : VersionRangeComparisons) :
      Nat → Nat → Nat → List VersionMatchAccess
    | 0, _, _ => []
    | fuel + 1, n, i =>
      if i ≤ n then
        .version i :: if range.lowerAccepts i then versionUpperScan range (fuel + 1) n i
          else versionLowerScan range fuel n (i + 1)
      else []

  /-- The marking `while` at lines 552-556, including its read and write. -/
  def versionUpperScan (range : VersionRangeComparisons) :
      Nat → Nat → Nat → List VersionMatchAccess
    | 0, _, _ => []
    | fuel + 1, n, i =>
      if i ≤ n then
        .version i :: if range.upperAccepts i then
          .dest i :: versionUpperScan range fuel n (i + 1)
        else []
      else []
end

/-- All accesses beneath the line-545 `@inbounds` loop after both assertions.
The outer list traversal is `for range in spec.ranges`; every inner scan starts at one. -/
def versionMatchesAccesses (versionsLength destLength n : Nat)
    (ranges : List VersionRangeComparisons) : List VersionMatchAccess :=
  if versionsLength = n ∧ n ≤ destLength then
    ranges.flatMap (fun range => versionLowerScan range (n + 1) n 1)
  else []

def VersionMatchesAccessesInBounds : Prop :=
  ∀ versionsLength destLength n ranges access,
    access ∈ versionMatchesAccesses versionsLength destLength n ranges →
    match access with
    | .version i => OneBasedInBounds versionsLength i
    | .dest i => OneBasedInBounds destLength i

private theorem versionUpperScan_safe (range : VersionRangeComparisons) :
    ∀ fuel n i access, 1 ≤ i → access ∈ versionUpperScan range fuel n i →
      match access with
      | .version j => OneBasedInBounds n j
      | .dest j => OneBasedInBounds n j := by
  intro fuel
  induction fuel with
  | zero => intro; simp [versionUpperScan]
  | succ fuel ih =>
    intro n i access hi hmem
    simp only [versionUpperScan] at hmem
    split at hmem
    · rename_i hin
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨hi, hin⟩
      · split at hmem
        · simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ⟨hi, hin⟩
          · exact ih n (i + 1) access (by omega) hmem
        · contradiction
    · contradiction

private theorem versionLowerScan_safe (range : VersionRangeComparisons) :
    ∀ fuel n i access, 1 ≤ i → access ∈ versionLowerScan range fuel n i →
      match access with
      | .version j => OneBasedInBounds n j
      | .dest j => OneBasedInBounds n j := by
  intro fuel
  induction fuel with
  | zero => intro; simp [versionLowerScan]
  | succ fuel ih =>
    intro n i access hi hmem
    simp only [versionLowerScan] at hmem
    split at hmem
    · rename_i hin
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨hi, hin⟩
      · split at hmem
        · exact versionUpperScan_safe range (fuel + 1) n i access hi hmem
        · exact ih n (i + 1) access (by omega) hmem
    · contradiction

theorem versionMatchesAccessesInBounds : VersionMatchesAccessesInBounds := by
  intro versionsLength destLength n ranges access hmem
  unfold versionMatchesAccesses at hmem
  split at hmem
  · rename_i checks
    simp only [List.mem_flatMap] at hmem
    obtain ⟨range, _, hmem⟩ := hmem
    have hs := versionLowerScan_safe range (n + 1) n 1 access (by omega) hmem
    cases access with
    | version i => simpa [checks.1] using hs
    | dest i =>
      simp only [OneBasedInBounds] at hs ⊢
      omega
  · contradiction

/-- The one-based counter values produced by the nested loops at
version.jl:570-578. There is one write for each pair and the allocation has the
same product length. -/
def versionIntersectAccesses (aRanges bRanges : List Nat) : List Nat :=
  oneBasedLoop (aRanges.length * bRanges.length)

def VersionIntersectAccessesInBounds : Prop :=
  ∀ aRanges bRanges i, i ∈ versionIntersectAccesses aRanges bRanges →
    OneBasedInBounds (aRanges.length * bRanges.length) i

theorem versionIntersectAccessesInBounds : VersionIntersectAccessesInBounds := by
  intro aRanges bRanges i hi
  simp only [versionIntersectAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [OneBasedInBounds]
  omega


end JuliaLean.MemSafety.G5
