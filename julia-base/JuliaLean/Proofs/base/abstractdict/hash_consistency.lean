import JuliaLean.base.abstractdict
import JuliaLean.base.abstractset

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- AbstractDict and AbstractSet hashing is independent of iteration order. -/
def UnorderedHashConsistency : Prop :=
  (∀ a b : List (Nat × Nat), a.Perm b → ∀ h, dictHash a h = dictHash b h) ∧
  (∀ a b : List Nat, a.Perm b → ∀ h, setHash a h = setHash b h)

private theorem foldl_xor_perm (xs ys : List Nat) (h : xs.Perm ys) (seed : Nat) :
    xs.foldl Nat.xor seed = ys.foldl Nat.xor seed := by
  induction h generalizing seed with
  | nil => rfl
  | cons x h ih =>
      simp only [List.foldl]
      exact ih _
  | swap x y l =>
      simp only [List.foldl]
      congr 1
      calc
        (Nat.xor seed y).xor x = Nat.xor seed (Nat.xor y x) := Nat.xor_assoc _ _ _
        _ = Nat.xor seed (Nat.xor x y) := congrArg (Nat.xor seed) (Nat.xor_comm y x)
        _ = (Nat.xor seed x).xor y := (Nat.xor_assoc _ _ _).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ seed).trans (ih₂ seed)

private theorem map_perm {α β : Type} (f : α → β) {xs ys : List α} (h : xs.Perm ys) :
    (xs.map f).Perm (ys.map f) := h.map f

private theorem dictHash_perm (a b : List (Nat × Nat)) (h : a.Perm b) (seed : Nat) :
    dictHash a seed = dictHash b seed := by
  unfold dictHash
  congr 1
  simpa [List.foldl_map] using
    foldl_xor_perm (a.map pairContribution) (b.map pairContribution) (map_perm pairContribution h)
      0x6d35bb51952d5539

private theorem setHash_perm (a b : List Nat) (h : a.Perm b) (seed : Nat) :
    setHash a seed = setHash b seed := by
  unfold setHash
  congr 1
  let f := fun x => mixNat x 0
  simpa [List.foldl_map, f] using
    foldl_xor_perm (a.map f) (b.map f) (map_perm f h) 0x852ada37cfe8e0ce

theorem unorderedHashConsistency_proven : UnorderedHashConsistency := by
  constructor
  · intro a b hp h; exact dictHash_perm a b hp h
  · intro a b hp h; exact setHash_perm a b hp h

end JuliaLean.HashOps
