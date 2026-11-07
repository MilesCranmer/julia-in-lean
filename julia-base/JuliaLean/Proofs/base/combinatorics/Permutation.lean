import JuliaLean.base.combinatorics
import JuliaLean.Proofs.base.permuteddimsarray.permutation

/-!
List models of the vector permutation helpers in `base/combinatorics.jl`.
The existing `ReinterpretArrays` source model and proof are reused for
`isperm` and `invperm`.
-/

namespace JuliaLean.Combinatorics

open JuliaLean


def permutationDefinition (p : List Int) : Bool :=
  (List.range p.length).all (fun k => p.count ((k : Int) + 1) = 1)

def IspermDefinition : Prop := ∀ p : List Int, isperm p = permutationDefinition p

theorem ispermDefinition_proven : IspermDefinition := by
  intro p
  rfl


def IspermTypedDefinition : Prop := ∀ (t : IntTy) (p : List (JInt t)),
  ispermTyped p = permutationDefinition (p.map (·.val))

theorem ispermTypedDefinition_proven : IspermTypedDefinition := by
  unfold IspermTypedDefinition
  intro t p
  rfl

/-- Reuse the established source-level theorem: construction accepts exactly
permutations, and the computed inverse reverses every index mapping. -/
def InvpermInverse : Prop := JuliaLean.ReinterpretArrays.PermutedCorrect

theorem invpermInverse_proven : InvpermInverse :=
  JuliaLean.ReinterpretArrays.permutedCorrect


def InvpermEveryPermutation : Prop := ∀ (first : Int) (p : List Int),
  isperm p = true → ∃ ip, invpermWithFirstIndex first p = .ok ip

theorem invpermEveryPermutation_refuted : ¬ InvpermEveryPermutation := by
  intro h
  obtain ⟨ip, e⟩ := h 0 [2, 3, 1] rfl
  simp [invpermWithFirstIndex] at e


/-- The two vector helpers implement their documented gather and scatter
assignments for all vectors, including duplicates and invalid indices. -/
def PermuteSemantics : Prop := ∀ (v p : List Int),
  permuteBang v p = (do
    let rhs ← gathered v p
    if rhs.length = v.length then .ok rhs else .error .dimensionMismatch) ∧
  invpermuteBang v p = scattered v p

theorem permuteSemantics_proven : PermuteSemantics := by
  unfold PermuteSemantics
  intro v p
  exact ⟨rfl, rfl⟩


/-- Applying a permutation and then its inverse restores every vector. -/
def PermuteRoundtrip : Prop := ∀ (n : Nat) (v : Fin n → Int)
    (p pinv : Fin n → Fin n), (∀ i, p (pinv i) = i) →
    invpermuteFin (permuteFin v p) pinv = v

theorem permuteRoundtrip_proven : PermuteRoundtrip := by
  intro n v p pinv h
  funext i
  simp [invpermuteFin, permuteFin, h]

end JuliaLean.Combinatorics
