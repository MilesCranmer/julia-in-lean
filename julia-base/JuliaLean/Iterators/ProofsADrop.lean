import JuliaLean.Iterators.ProofsAList

namespace JuliaLean.Iterators
open JuliaLean ProofsAList

namespace ProofsADrop
attribute [local simp] Bind.bind Pure.pure Except.bind Except.pure
theorem iter_drop_none (fuel : Nat) (it : Itr) (n : JInt64) :
    iter fuel (.drop it n) none = (do
      dropLoop (fun s => iter fuel it (some s)) n.val.toNat (← iter fuel it none)) := rfl

theorem iter_drop_some (fuel : Nat) (it : Itr) (n : JInt64) (s : St) :
    iter fuel (.drop it n) (some s) = iter fuel it (some s) := rfl


theorem dropLoop_nextAt (xs : List Val) (st : Nat → St)
    (step : St → M (Option (Val × St)))
    (hs : ∀ p, step (st p) = nextAt xs p st) (n p : Nat) :
    (do dropLoop step n (← nextAt xs p st)) = nextAt xs (p + n) st := by
  induction n generalizing p with
  | zero => cases h : nextAt xs p st <;> simp [dropLoop, h]
  | succ n ih =>
    cases hd : xs.drop p with
    | nil =>
      have he : xs.drop (p + (n + 1)) = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hl := List.length_drop (i := p) (l := xs)
        simp only [hd, List.length_nil] at hl
        rw [List.length_drop]
        omega
      simp [nextAt, hd, he, dropLoop]
    | cons x ys =>
      rw [show nextAt xs p st = .ok (some (x, st (p + 1))) by simp [nextAt, hd]]
      simp only [Bind.bind, Except.bind, dropLoop]
      rw [hs]
      have hi := ih (p + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

theorem elems_drop_vec (xs : List Val) (n : JInt64) (fuel : Nat)
    (hf : xs.length < fuel) :
    elems fuel (.drop (.vec .int xs) n) = .ok (xs.drop n.val.toNat) := by
  unfold elems
  simp only [iter_drop_none, iter_drop_some, iter_vec]
  rw [idxIter_start]
  have hd := dropLoop_nextAt xs (fun q => .int (q + 1))
    (fun s => idxIter xs (some s)) (idxIter_at xs) n.val.toNat 0
  simp only [Nat.zero_add] at hd
  rw [hd]
  exact runFrom_nextAt xs _ _ (fun p _ => idxIter_at xs p) _ _ (by
    rw [List.length_drop]
    omega)

end ProofsADrop
end JuliaLean.Iterators
