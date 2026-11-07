import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-- Descending word requests made by `truncated`, including the partial word.
Each request is kept only after the source's `w < lenx` check. -/
def truncatedWordRequests (wordCount bitCount : Nat) : List Nat :=
  let whole := (List.range (bitCount / 64)).filter (· < wordCount)
  let lastPart := if bitCount % 64 ≠ 0 ∧ bitCount / 64 < wordCount
    then [bitCount / 64] else []
  whole ++ lastPart

/-- A checked zero-based bit request becomes a descending zero-based word
request, matching rawbigfloats.jl:73-80. -/
def bitWordRequest (wordCount bitIndex : Nat) : List Nat :=
  if bitIndex < 64 * wordCount then [bitIndex / 64] else []

/-- The final-bit and round-bit requests at lines 123-127. A zero `len` makes
`len-1` negative in Julia and therefore produces no final-bit word access. -/
def roundingWordRequests (wordCount len : Nat) : List Nat :=
  (if 0 < len then bitWordRequest wordCount (len - 1) else []) ++
    bitWordRequest wordCount len

/-- Descending zero-based word indices become the one-based `i+1` access after
`reversed_index`, lines 9-23. -/
def descendingWordLoads (wordCount : Nat) (requests : List Nat) : List Nat :=
  requests.map (wordCount - ·)

/-- Sticky-bit accesses at lines 53-57 and 139-142. `tailBits` is positive
exactly when the public Float conversion asks for bits below the round bit. -/
def stickyWordLoads (wordCount len : Nat) : List Nat :=
  let tailBits := 64 * wordCount - len - 1
  if tailBits = 0 then [] else
    let whole := tailBits / 64
    (if tailBits % 64 = 0 then [] else [whole + 1]) ++ oneBasedLoop whole

/-- All word-array accesses reached from public BigFloat-to-Float conversion:
`truncated`, final/round bit construction, and the sticky-bit callback. -/
def rawBigFloatWordLoads (wordCount len : Nat) : List Nat :=
  descendingWordLoads wordCount (truncatedWordRequests wordCount len) ++
  descendingWordLoads wordCount (roundingWordRequests wordCount len) ++
  stickyWordLoads wordCount len

def RawBigFloatAccessesInBounds : Prop :=
  ∀ wordCount len index, index ∈ rawBigFloatWordLoads wordCount len →
    OneBasedInBounds wordCount index

private theorem truncatedWordRequests_safe (wordCount bitCount request : Nat) :
    request ∈ truncatedWordRequests wordCount bitCount → request < wordCount := by
  intro h
  simp only [truncatedWordRequests, List.mem_append, List.mem_filter,
    List.mem_range] at h
  rcases h with ⟨_, hr⟩ | h
  · exact of_decide_eq_true hr
  · split at h
    · rename_i hc
      simp at h
      subst request
      exact hc.2
    · contradiction

private theorem bitWordRequest_safe (wordCount bitIndex request : Nat) :
    request ∈ bitWordRequest wordCount bitIndex → request < wordCount := by
  intro h
  unfold bitWordRequest at h
  split at h
  · rename_i hb
    simp at h
    subst request
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 64)).2 (by simpa [Nat.mul_comm] using hb)
  · contradiction

private theorem roundingWordRequests_safe (wordCount len request : Nat) :
    request ∈ roundingWordRequests wordCount len → request < wordCount := by
  intro h
  simp only [roundingWordRequests, List.mem_append] at h
  rcases h with h | h
  · split at h
    · exact bitWordRequest_safe wordCount (len - 1) request h
    · contradiction
  · exact bitWordRequest_safe wordCount len request h

private theorem descendingWordLoads_safe (wordCount : Nat) (requests : List Nat)
    (hrequests : ∀ request ∈ requests, request < wordCount) (index : Nat) :
    index ∈ descendingWordLoads wordCount requests → OneBasedInBounds wordCount index := by
  intro h
  simp only [descendingWordLoads, List.mem_map] at h
  obtain ⟨request, hr, rfl⟩ := h
  have hs := hrequests request hr
  simp only [OneBasedInBounds]
  omega

private theorem stickyWordLoads_safe (wordCount len index : Nat) :
    index ∈ stickyWordLoads wordCount len → OneBasedInBounds wordCount index := by
  intro h
  let tailBits := 64 * wordCount - len - 1
  change index ∈ (if tailBits = 0 then [] else
    (if tailBits % 64 = 0 then [] else [tailBits / 64 + 1]) ++
      oneBasedLoop (tailBits / 64)) at h
  by_cases hz : tailBits = 0
  · simp [hz] at h
  · rw [if_neg hz] at h
    have htail : tailBits < 64 * wordCount := by
      dsimp [tailBits]
      omega
    have hwhole : tailBits / 64 < wordCount :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 64)).2 (by simpa [Nat.mul_comm] using htail)
    by_cases hr : tailBits % 64 = 0
    · simp only [hr, ↓reduceIte, List.nil_append] at h
      have hs := oneBasedLoop_safe _ _ h
      simp only [OneBasedInBounds] at hs ⊢
      omega
    · simp only [hr, ↓reduceIte, List.mem_append, List.mem_singleton] at h
      rcases h with rfl | h
      · simp only [OneBasedInBounds]
        omega
      · have hs := oneBasedLoop_safe _ _ h
        simp only [OneBasedInBounds] at hs ⊢
        omega

theorem rawBigFloatAccessesInBounds : RawBigFloatAccessesInBounds := by
  intro wordCount len index h
  simp only [rawBigFloatWordLoads, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · exact descendingWordLoads_safe wordCount _
        (truncatedWordRequests_safe wordCount len) index h
    · exact descendingWordLoads_safe wordCount _
        (roundingWordRequests_safe wordCount len) index h
  · exact stickyWordLoads_safe wordCount len index h


end JuliaLean.MemSafety.G5
