import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- One sequential column of `mapreduce_impl`: indices 1 through K. -/
def scartColumn (K j : Nat) : List (Nat × Nat) :=
  (List.range K).map fun i => (i + 1, j)

/-- The exact sequential/pairwise branch tree of `mapreduce_impl`,
`base/reinterpretarray.jl:953-978`. Fuel is a totality device; the public
wrapper supplies `n+1`, more than the number of possible column splits. -/
def reinterpretMapreduceAccesses (K firstJ lastJ block : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | fuel + 1 =>
      if 2 ≤ K ∧ 1 ≤ firstJ ∧ firstJ ≤ lastJ then
        if lastJ - firstJ < block then
          (List.range (lastJ - firstJ + 1)).flatMap fun dj => scartColumn K (firstJ + dj)
        else
          let mid := firstJ + (lastJ - firstJ) / 2
          reinterpretMapreduceAccesses K firstJ mid block fuel ++
            reinterpretMapreduceAccesses K (mid + 1) lastJ block fuel
      else []

def reinterpretMapreduceProgram (K n block : Nat) : List (Nat × Nat) :=
  if 2 ≤ K ∧ 0 < n ∧ 0 < block then
    reinterpretMapreduceAccesses K 1 n block (n + 1)
  else []

def ReinterpretMapreduceInBounds : Prop :=
  ∀ (K n block : Nat) (a : Nat × Nat), a ∈ reinterpretMapreduceProgram K n block →
    1 ≤ a.1 ∧ a.1 ≤ K ∧ 1 ≤ a.2 ∧ a.2 ≤ n

/-- `_totuple` checks `length(itr) ≥ N+32`, forms exactly that view, then
loads its single tuple element at index one, `base/reinterpretarray.jl:984-995`. -/
def reinterpretTupleIndex (N itrLen : Nat) : Option (Nat × Int) :=
  if N + 32 ≤ itrLen then some (1, 1) else none

def ReinterpretTupleInBounds : Prop :=
  ∀ (N itrLen len : Nat) (i : Int), reinterpretTupleIndex N itrLen = some (len, i) →
    InBounds len i


theorem reinterpretMapreduceInBounds : ReinterpretMapreduceInBounds := by
  have safe : ∀ fuel K firstJ lastJ block n, 2 ≤ K → 1 ≤ firstJ → firstJ ≤ lastJ →
      lastJ ≤ n → 0 < block → ∀ a ∈ reinterpretMapreduceAccesses K firstJ lastJ block fuel,
        1 ≤ a.1 ∧ a.1 ≤ K ∧ 1 ≤ a.2 ∧ a.2 ≤ n := by
    intro fuel
    induction fuel with
    | zero => simp [reinterpretMapreduceAccesses]
    | succ fuel ih =>
        intro K firstJ lastJ block n hK hf hfl hln hb a ha
        simp only [reinterpretMapreduceAccesses, hK, hf, hfl, true_and, ↓reduceIte] at ha
        by_cases hs : lastJ - firstJ < block
        · simp only [hs, ↓reduceIte, List.mem_flatMap, List.mem_range, scartColumn,
            List.mem_map] at ha
          rcases ha with ⟨dj, hdj, i, hi, rfl⟩
          omega
        · simp only [hs, ↓reduceIte, List.mem_append] at ha
          let mid := firstJ + (lastJ - firstJ) / 2
          have hm0 : firstJ ≤ mid := by dsimp [mid]; omega
          have hml : mid < lastJ := by
            dsimp [mid]
            have hd : 0 < lastJ - firstJ := by omega
            have hh : (lastJ - firstJ) / 2 < lastJ - firstJ := by omega
            omega
          rcases ha with ha | ha
          · exact ih K firstJ mid block n hK hf hm0 (by omega) hb a ha
          · exact ih K (mid + 1) lastJ block n hK (by omega) (by omega) hln hb a ha
  intro K n block a ha
  unfold reinterpretMapreduceProgram at ha
  split at ha
  · rename_i h
    exact safe (n + 1) K 1 n block n h.1 (by omega) (by omega) (by omega) h.2.2 a ha
  · contradiction

theorem reinterpretTupleInBounds : ReinterpretTupleInBounds := by
  intro N itrLen len i h
  unfold reinterpretTupleIndex at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨by decide, by decide⟩
  · contradiction

end JuliaLean.MemSafety.G4
