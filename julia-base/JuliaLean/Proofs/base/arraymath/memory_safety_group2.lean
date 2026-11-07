import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/arraymath.jl:107-130`: `_reverse!` -/

def validReverseDims (rank : Nat) (dims : List Nat) : Bool :=
  !dims.isEmpty && dims.length ≤ rank &&
    (List.range rank).countP (fun k => dims.contains (k + 1)) == dims.length

def reverseAxisPass (a : Axis) (reverse leading : Bool) : List Access :=
  let count := if leading then a.len / 2 else a.len
  (List.range count).flatMap fun (k : Nat) =>
    let original : Int := (k : Int) + 1
    let reflected : Int := if reverse then (a.len : Int) - k else original
    [⟨a.len, original⟩, ⟨a.len, reflected⟩]

def middleViewAxes (axes : List Axis) (leadingDim : Nat) : List Axis :=
  axes.zipIdx.map fun (a, k) => Axis.oneTo (if k + 1 == leadingDim then 1 else a.len)

def reverseAccessesFuel : Nat → List Axis → List Nat → List Access
  | 0, _, _ => []
  | fuel + 1, axes, dims =>
      if h : validReverseDims axes.length dims then
        let leading := dims.headD 0
        let here := axes.zipIdx.flatMap fun (a, k) =>
          reverseAxisPass a (dims.contains (k + 1)) (k + 1 == leading)
        if dims.length > 1 &&
            ((axes.getD (leading - 1) (Axis.oneTo 0)).len % 2 == 1) then
          here ++ reverseAccessesFuel fuel (middleViewAxes axes leading) dims.tail
        else here
      else []

def reverseAccesses (axes : List Axis) (dims : List Nat) : List Access :=
  reverseAccessesFuel dims.length axes dims

def ReverseInBounds : Prop := ∀ axes dims, AllInBounds (reverseAccesses axes dims)





private theorem reverseAxisPass_safe (a : JuliaLean.AbstractArrays.Axis) (r l : Bool) :
    AllInBounds (reverseAxisPass a r l) := by
  intro access ha
  simp only [reverseAxisPass, List.mem_flatMap, List.mem_range] at ha
  split at ha
  all_goals
    obtain ⟨k, hk, hmem⟩ := ha
    simp at hmem
    rcases hmem with rfl | rfl
    · simp only [Access.inBounds]
      omega
    · simp only [Access.inBounds]
      split <;> omega

private theorem reverseFuel_safe : ∀ fuel axes dims,
    AllInBounds (reverseAccessesFuel fuel axes dims)
  | 0, axes, dims => by simp [reverseAccessesFuel, AllInBounds]
  | fuel + 1, axes, dims => by
      intro access ha
      simp only [reverseAccessesFuel] at ha
      split at ha
      · split at ha
        · rw [List.mem_append] at ha
          rcases ha with ha | ha
          · simp only [List.mem_flatMap] at ha
            obtain ⟨pair, hpair, ha⟩ := ha
            exact reverseAxisPass_safe pair.1 (dims.contains (pair.2 + 1))
              (pair.2 + 1 == dims.headD 0) access ha
          · exact reverseFuel_safe fuel (middleViewAxes axes (dims.headD 0)) dims.tail access ha
        · simp only [List.mem_flatMap] at ha
          obtain ⟨pair, hpair, ha⟩ := ha
          exact reverseAxisPass_safe pair.1 (dims.contains (pair.2 + 1))
            (pair.2 + 1 == dims.headD 0) access ha
      · simp at ha

theorem reverseInBounds : ReverseInBounds := by
  intro axes dims
  exact reverseFuel_safe dims.length axes dims

end JuliaLean.MemSafety.G2
