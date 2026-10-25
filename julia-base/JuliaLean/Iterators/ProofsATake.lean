import JuliaLean.Iterators.ProofsAList

set_option maxRecDepth 4096
namespace JuliaLean.Iterators
open JuliaLean ProofsAList
namespace ProofsATake
attribute [local simp] Bind.bind Pure.pure Except.bind Except.pure
theorem iter_take (lim : Nat) (it : Itr) (n : JInt64) (st : Option St) :
    iter lim (.take it n) st = (do
      let (m, rest) ← splitCountState st n
      if m ≤ i64 0 then pure none else
      match ← iter lim it rest with
      | none => pure none
      | some (x, s) => pure (some (x, .tup [.int (m - i64 1).val, s]))) := rfl


def takeAt (xs : List Val) (p : Nat) (m : JInt64) : M (Option (Val × St)) :=
  if m.val ≤ 0 then .ok none else do
    match ← nextAt xs p (fun q => .int (q + 1)) with
    | none => pure none
    | some (x, s) => pure (some (x, .tup [.int (m - i64 1).val, s]))

theorem iter_take_at (xs : List Val) (lim p : Nat) (n m : JInt64) :
    iter lim (.take (.vec .int xs) n) (some (.tup [.int m.val, .int (p + 1)])) =
      takeAt xs p m := by
  simp only [iter_take, iter_vec, splitCountState, i64_val_self, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  rw [idxIter_at]
  rfl

theorem iter_take_start (xs : List Val) (lim : Nat) (n : JInt64) :
    iter lim (.take (.vec .int xs) n) none = takeAt xs 0 n := by
  simp only [iter_take, iter_vec, splitCountState, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [idxIter_start]
  rfl

theorem run_takeAt (xs : List Val) (lim : Nat) (n : JInt64) (fuel p : Nat)
    (m : JInt64) (hm : 0 ≤ m.val) (hf : (xs.drop p).length ≤ fuel) :
    (do
      runFrom (fun s => iter lim (.take (.vec .int xs) n) (some s)) fuel
        (← takeAt xs p m)) = .ok ((xs.drop p).take m.val.toNat) := by
  induction fuel generalizing p m with
  | zero =>
    have hd : xs.drop p = [] := List.eq_nil_of_length_eq_zero (by omega)
    by_cases hz : m.val ≤ 0 <;> simp [takeAt, nextAt, hd, hz, runFrom]
  | succ fuel ih =>
    by_cases hz : m.val ≤ 0
    · have hm0 : m.val.toNat = 0 := by omega
      simp [takeAt, hz, runFrom, hm0]
    · cases hd : xs.drop p with
      | nil => simp [takeAt, nextAt, hd, hz, runFrom]
      | cons x ys =>
        have hpos : 0 < m.val := by omega
        have hm' := sub_one_val m hpos
        have ht : m.val.toNat = (m - i64 1).val.toNat + 1 := by omega
        have hdrop : xs.drop (p + 1) = ys := by rw [← List.drop_drop, hd]; rfl
        have hf' : (xs.drop (p + 1)).length ≤ fuel := by
          simp only [hdrop]
          simp only [hd, List.length_cons] at hf
          omega
        have hi := ih (p + 1) (m - i64 1) (by omega) hf'
        rw [hdrop] at hi
        have hcur : takeAt xs p m = .ok (some (x,
            .tup [.int (m - i64 1).val, .int ((p + 1 : Nat) + 1)])) := by
          simp [takeAt, nextAt, hz, hd]
        rw [hcur]
        simp only [Bind.bind, Except.bind, runFrom]
        rw [iter_take_at]
        rw [ht]
        simp only [List.take_succ_cons]
        cases hn : takeAt xs (p + 1) (m - i64 1) with
        | error e => simp only [hn, Bind.bind, Except.bind] at hi; contradiction
        | ok v =>
          simp only [hn, Bind.bind, Except.bind] at hi ⊢
          rw [hi]
          rfl

theorem elems_take_vec (xs : List Val) (n : JInt64) (fuel : Nat)
    (hn : 0 ≤ n.val) (hf : xs.length < fuel) :
    elems fuel (.take (.vec .int xs) n) = .ok (xs.take n.val.toNat) := by
  unfold elems
  rw [iter_take_start]
  simpa using run_takeAt xs fuel n fuel 0 n hn (by simpa using Nat.le_of_lt hf)

end ProofsATake
end JuliaLean.Iterators
