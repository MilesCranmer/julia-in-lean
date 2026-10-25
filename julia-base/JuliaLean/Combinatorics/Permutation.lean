import JuliaLean.ReinterpretArrays.ProofIndex

/-!
List models of the vector permutation helpers in `base/combinatorics.jl`.
The existing `ReinterpretArrays` source model and proof are reused for
`isperm` and `invperm`.
-/

namespace JuliaLean.Combinatorics

open JuliaLean

abbrev isperm := JuliaLean.ReinterpretArrays.isperm
abbrev invperm := JuliaLean.ReinterpretArrays.invperm

def permutationDefinition (p : List Int) : Bool :=
  (List.range p.length).all (fun k => p.count ((k : Int) + 1) = 1)

def IspermDefinition : Prop := ∀ p : List Int, isperm p = permutationDefinition p

theorem ispermDefinition_proven : IspermDefinition := by
  intro p
  rfl

def ispermTyped {t : IntTy} (p : List (JInt t)) : Bool :=
  isperm (p.map (·.val))

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

/-- `require_one_based_indexing(a)`, `base/combinatorics.jl:287`, before the
value-level `invperm` model. -/
def invpermWithFirstIndex (first : Int) (p : List Int) : Jl (List Int) :=
  if first = 1 then invperm p
  else .error (.argumentError "offset arrays are not supported")

def InvpermEveryPermutation : Prop := ∀ (first : Int) (p : List Int),
  isperm p = true → ∃ ip, invpermWithFirstIndex first p = .ok ip

theorem invpermEveryPermutation_refuted : ¬ InvpermEveryPermutation := by
  intro h
  obtain ⟨ip, e⟩ := h 0 [2, 3, 1] rfl
  simp [invpermWithFirstIndex] at e

inductive PermuteError where
  | bounds
  | dimensionMismatch
  deriving Repr, DecidableEq

abbrev PermuteResult (α : Type) := Except PermuteError α

def gathered (v : List Int) (p : List Int) : PermuteResult (List Int) :=
  if p.all (fun i => 1 ≤ i ∧ i ≤ v.length) then
    .ok (p.map fun i => v.getD (i - 1).toNat 0)
  else .error .bounds

/-- `permute!(v,p) = (v .= v[p])`, `base/combinatorics.jl:184-214`.
The indexed right-hand side is completed before the destination shape check. -/
def permuteBang (v p : List Int) : PermuteResult (List Int) := do
  let rhs ← gathered v p
  if rhs.length = v.length then .ok rhs else .error .dimensionMismatch

private def scatterPairs (out : List Int) : List (Int × Int) → List Int
  | [] => out
  | (i, x) :: rest => scatterPairs (out.set (i - 1).toNat x) rest

def scattered (v p : List Int) : PermuteResult (List Int) :=
  if p.length ≠ v.length then .error .dimensionMismatch
  else if p.all (fun i => 1 ≤ i ∧ i ≤ v.length) then
    .ok (scatterPairs v (p.zip v))
  else .error .bounds

/-- `invpermute!(v,p) = (v[p] = v; v)`, `base/combinatorics.jl:216-243`. -/
def invpermuteBang (v p : List Int) : PermuteResult (List Int) := scattered v p

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

def permuteFin {n : Nat} (v : Fin n → Int) (p : Fin n → Fin n) : Fin n → Int :=
  fun i => v (p i)

def invpermuteFin {n : Nat} (v : Fin n → Int) (pinv : Fin n → Fin n) : Fin n → Int :=
  fun i => v (pinv i)

/-- Applying a permutation and then its inverse restores every vector. -/
def PermuteRoundtrip : Prop := ∀ (n : Nat) (v : Fin n → Int)
    (p pinv : Fin n → Fin n), (∀ i, p (pinv i) = i) →
    invpermuteFin (permuteFin v p) pinv = v

theorem permuteRoundtrip_proven : PermuteRoundtrip := by
  intro n v p pinv h
  funext i
  simp [invpermuteFin, permuteFin, h]

end JuliaLean.Combinatorics
