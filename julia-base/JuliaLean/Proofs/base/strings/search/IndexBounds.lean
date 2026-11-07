import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- Valid character positions are a representation invariant of an
`AbstractString`. `nextind` and `prevind` move through this list,
`base/strings/search.jl:342-353,667-678`. -/
def stringSearchPositions (validPositions : List Int) (start : Int) (forward : Bool) : List Int :=
  if forward then validPositions.filter (start ≤ ·)
  else validPositions.reverse.filter (· ≤ start)

def stringSearchIndex (validPositions : List Int) (start : Int) (forward : Bool) (k : Nat) : Option Int :=
  (stringSearchPositions validPositions start forward)[k]?

def StringSearchInBounds : Prop :=
  ∀ (validPositions : List Int) (start : Int) (forward : Bool) (k : Nat) (i : Int),
    stringSearchIndex validPositions start forward k = some i → i ∈ validPositions


theorem stringSearchInBounds : StringSearchInBounds := by
  intro positions start forward k i h
  have hk' : k < (stringSearchPositions positions start forward).length :=
    List.getElem?_eq_some_iff.mp h |>.1
  have hi : (stringSearchPositions positions start forward)[k] = i := by
    simpa [stringSearchIndex, List.getElem?_eq_getElem hk'] using h
  have hm : i ∈ stringSearchPositions positions start forward := by
    rw [← hi]
    exact List.getElem_mem hk'
  unfold stringSearchPositions at hm
  split at hm <;> simp_all

end JuliaLean.MemSafety.G4
