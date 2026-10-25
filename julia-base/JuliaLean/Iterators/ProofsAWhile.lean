import JuliaLean.Iterators.ProofsAList

set_option maxRecDepth 4096
namespace JuliaLean.Iterators
open JuliaLean ProofsAList
namespace ProofsAWhile
attribute [local simp] Bind.bind Pure.pure Except.bind Except.pure
theorem iter_takeWhile (fuel : Nat) (pred : Val → Bool) (it : Itr) (st : Option St) :
    iter fuel (.takeWhile pred it) st = (do
      match ← iter fuel it st with
      | none => pure none
      | some (x, s) => if pred x then pure (some (x, s)) else pure none) := rfl

theorem iter_dropWhile_none (fuel : Nat) (pred : Val → Bool) (it : Itr) :
    iter fuel (.dropWhile pred it) none = (do
      whileLoop (fun s => iter fuel it (some s)) pred fuel (← iter fuel it none)) := rfl

theorem iter_dropWhile_some (fuel : Nat) (pred : Val → Bool) (it : Itr) (s : St) :
    iter fuel (.dropWhile pred it) (some s) = iter fuel it (some s) := rfl


def whileAt (xs : List Val) (p : Nat) (pred : Val → Bool) : M (Option (Val × St)) := do
  match ← nextAt xs p (fun q => .int (q + 1)) with
  | none => pure none
  | some (x, s) => if pred x then pure (some (x, s)) else pure none

theorem iter_while_at (xs : List Val) (lim p : Nat) (pred : Val → Bool) :
    iter lim (.takeWhile pred (.vec .int xs)) (some (.int (p + 1))) = whileAt xs p pred := by
  simp only [iter_takeWhile, iter_vec]
  rw [idxIter_at]
  rfl

theorem run_whileAt (xs : List Val) (lim : Nat) (pred : Val → Bool) (fuel p : Nat)
    (hf : (xs.drop p).length ≤ fuel) :
    (do
      runFrom (fun s => iter lim (.takeWhile pred (.vec .int xs)) (some s)) fuel
        (← whileAt xs p pred)) = .ok ((xs.drop p).takeWhile pred) := by
  induction fuel generalizing p with
  | zero =>
    have hd : xs.drop p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [whileAt, nextAt, hd, runFrom]
  | succ fuel ih =>
    cases hd : xs.drop p with
    | nil => simp [whileAt, nextAt, hd, runFrom]
    | cons x ys =>
      have hdrop : xs.drop (p + 1) = ys := by rw [← List.drop_drop, hd]; rfl
      have hf' : (xs.drop (p + 1)).length ≤ fuel := by
        simp only [hdrop]
        simp only [hd, List.length_cons] at hf
        omega
      cases hx : pred x with
      | false => simp [whileAt, nextAt, hd, hx, runFrom]
      | true =>
        have hi := ih (p + 1) hf'
        rw [hdrop] at hi
        rw [show whileAt xs p pred = .ok (some (x, .int ((p + 1 : Nat) + 1))) by
          simp [whileAt, nextAt, hd, hx]]
        simp only [Bind.bind, Except.bind, runFrom]
        rw [iter_while_at]
        simp only [List.takeWhile_cons, hx, ↓reduceIte]
        cases hn : whileAt xs (p + 1) pred with
        | error e => simp only [hn, Bind.bind, Except.bind] at hi; contradiction
        | ok v =>
          simp only [hn, Bind.bind, Except.bind] at hi ⊢
          rw [hi]
          rfl

theorem run_dropWhile (xs : List Val) (pred : Val → Bool) (fuel budget p : Nat)
    (hf : (xs.drop p).length ≤ fuel) (hb : (xs.drop p).length ≤ budget) :
    (do
      runFrom (fun s => idxIter xs (some s)) budget
        (← whileLoop (fun s => idxIter xs (some s)) pred fuel
          (← nextAt xs p (fun q => .int (q + 1))))) =
      .ok ((xs.drop p).dropWhile pred) := by
  induction fuel generalizing p with
  | zero =>
    have hd : xs.drop p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [nextAt, hd, whileLoop, runFrom]
  | succ fuel ih =>
    cases hd : xs.drop p with
    | nil => simp [nextAt, hd, whileLoop, runFrom]
    | cons x ys =>
      have hdrop : xs.drop (p + 1) = ys := by rw [← List.drop_drop, hd]; rfl
      have hf' : (xs.drop (p + 1)).length ≤ fuel := by
        simp only [hdrop]
        simp only [hd, List.length_cons] at hf
        omega
      have hb' : (xs.drop (p + 1)).length ≤ budget := by
        simp only [hdrop]
        simp only [hd, List.length_cons] at hb
        omega
      cases hx : pred x with
      | false =>
        have hi := runFrom_nextAt xs (fun q => .int (q + 1))
          (fun s => idxIter xs (some s)) (fun q _ => idxIter_at xs q) p budget hb
        simpa [nextAt, hd, whileLoop, hx] using hi
      | true =>
        have hi := ih (p + 1) hf' hb'
        rw [hdrop] at hi
        rw [show nextAt xs p (fun q => .int (q + 1)) =
            .ok (some (x, .int ((p + 1 : Nat) + 1))) by simp [nextAt, hd]]
        simp only [Bind.bind, Except.bind, whileLoop, hx, ↓reduceIte, idxIter_at,
          List.dropWhile_cons]
        cases hn : nextAt xs (p + 1) (fun q => .int (q + 1)) with
        | error e => simpa only [hn, Bind.bind, Except.bind] using hi
        | ok v => simpa only [hn, Bind.bind, Except.bind] using hi

end ProofsAWhile
end JuliaLean.Iterators
