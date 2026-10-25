import JuliaLean.Iterators.Spec

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace JuliaLean.Iterators
open JuliaLean

@[simp] private theorem bp_pure {α : Type} (a : α) : (pure a : M α) = .ok a := rfl
@[simp] private theorem bp_bind {α β : Type} (a : α) (f : α → M β) :
    ((.ok a : M α) >>= f) = f a := rfl

private theorem bp_idx (xs : List Val) (n : Nat) :
    idxIter xs (some (.int (n + 1))) =
      match xs.drop n with
      | [] => .ok none
      | x :: _ => .ok (some (x, .int (n + 2))) := by
  have hg : xs.getD n .undef = (xs.drop n).headD .undef := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih => cases n <;> simp_all [List.getD]
  simp only [idxIter]
  have hn : (1 : Int) ≤ (n : Int) + 1 := by omega
  have he : ((n : Int) + 1 - 1).toNat = n := by omega
  simp only [hn, true_and, he]
  cases hd : xs.drop n with
  | nil =>
    have : xs.length ≤ n := List.drop_eq_nil_iff.mp hd
    simp [show ¬ ((n : Int) + 1 ≤ xs.length) by omega]
  | cons x xt =>
    have : n < xs.length := by
      have hh := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hh
      omega
    simp only [show (n : Int) + 1 ≤ xs.length by omega, ite_true, bp_pure]
    rw [hg, hd]
    simp [Int.add_assoc]

@[simp] private theorem bp_idx_zero (xs : List Val) :
    idxIter xs (some (.int 1)) = match xs with
      | [] => .ok none
      | x :: _ => .ok (some (x, .int 2)) := by
  simpa using bp_idx xs 0

private theorem bp_drop_next (xs : List Val) (i : Nat) (x : Val) (xt : List Val)
    (h : xs.drop i = x :: xt) : xs.drop (i + 1) = xt := by
  have := congrArg (List.drop 1) h
  simpa [List.drop_drop, Nat.add_comm] using this

private def bpState (x y : Val) (i j : Nat) : St :=
  .tup [.tup [.val x, .int (i + 1)], .tup [.val y, .int (j + 1)]]

private theorem bp_start (xs : List Val) :
    idxIter xs none = idxIter xs (some (.int ((0 : Nat) + 1))) := by
  cases xs with
  | nil => simp [idxIter]
  | cons x xt =>
    have h : (1 : Int) ≤ (xt.length : Int) + 1 := by omega
    simp [idxIter, List.getD, h]

private theorem bp_vec (fuel : Nat) (xs : List Val) (s : Option St) :
    iter fuel (.vec .int xs) s = idxIter xs s := rfl

private theorem bp_prod_s (fuel : Nat) (a : Itr) (its : List Itr) (ss : List St) :
    iter fuel (.product (a :: its)) (some (.tup ss)) = (do
      if (← pisdone (a :: its) ss) = some true then pure none else
      match ← pIterate1 fuel (a :: its) ss with
      | none => pure none
      | some nx => pure (some (.tup (nx.map (·.1)),
          .tup (nx.map (fun p => .tup [.val p.1, p.2]))))) := rfl

private theorem bp_prod_0 (fuel : Nat) (a b : Itr) :
    iter fuel (.product [a,b]) none = (do
      if (← anyIsdone0 [a,b]) = some true then pure none else
      match ← pIterate fuel [a,b] with
      | none => pure none
      | some nx => pure (some (.tup (nx.map (·.1)),
          .tup (nx.map (fun p => .tup [.val p.1, p.2]))))) := rfl

private theorem bp_step (xs ys : List Val) (fuel i j : Nat) (x y : Val) :
    iter fuel (.product [.vec .int xs, .vec .int ys]) (some (bpState x y i j)) =
      match xs.drop i with
      | a :: _ => .ok (some (.tup [a, y], bpState a y (i + 1) j))
      | [] => match ys.drop j with
        | [] => .ok none
        | b :: _ => match xs with
          | [] => .ok none
          | a :: _ => .ok (some (.tup [a, b], bpState a b 1 (j + 1))) := by
  simp only [bpState, bp_prod_s]
  simp [pisdone, pairState, isdoneS, pIterate1, statefulCur, isdone0,
    bp_vec, bp_start, bp_idx]
  cases hx : xs.drop i <;> cases hy : ys.drop j <;>
    cases xs <;> simp_all [bpState, Int.add_assoc]

private theorem bp_run (xs ys : List Val) (hn : xs ≠ []) (budget fuel i j : Nat)
    (x y : Val)
    (hb : (xs.drop i).length + xs.length * (ys.drop j).length ≤ budget) :
    (do
      let next ← iter fuel (.product [.vec .int xs, .vec .int ys])
        (some (bpState x y i j))
      runFrom (fun s => iter fuel (.product [.vec .int xs, .vec .int ys]) (some s))
        budget next) =
      .ok ((xs.drop i).map (fun a => .tup [a, y]) ++
        (ys.drop j).flatMap (fun b => xs.map (fun a => .tup [a, b]))) := by
  induction budget generalizing i j x y with
  | zero =>
    have hx : xs.drop i = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    have hy : ys.drop j = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hp : 0 < xs.length := List.length_pos_iff.mpr hn
      have hh : xs.length * (ys.drop j).length = 0 := by omega
      exact (Nat.mul_eq_zero.mp hh).resolve_left (by omega)
    simp [bp_step, hx, hy, runFrom]
  | succ k ih =>
    rw [bp_step]
    cases hx : xs.drop i with
    | cons a xtail =>
      have hx' := bp_drop_next xs i a xtail hx
      have hk : (xs.drop (i + 1)).length + xs.length * (ys.drop j).length ≤ k := by
        simp only [hx, List.length_cons] at hb
        rw [hx']
        omega
      simpa [runFrom, hx, hx', List.map_cons] using
        congrArg (fun r : M (List Val) => (do pure (Val.tup [a, y] :: (← r)) : M (List Val)))
          (ih (i + 1) j a y hk)
    | nil =>
      cases hy : ys.drop j with
      | nil => simp [hx, hy, runFrom]
      | cons b bt =>
        have hy' := bp_drop_next ys j b bt hy
        cases xs with
        | nil => exact False.elim (hn rfl)
        | cons a xtail =>
          have hk : ((a :: xtail).drop 1).length +
              (a :: xtail).length * (ys.drop (j + 1)).length ≤ k := by
            simp only [hx, hy, List.length_nil, List.length_cons, Nat.zero_add,
              Nat.mul_add, Nat.mul_one] at hb
            simp only [List.drop_succ_cons, List.drop_zero, hy', List.length_cons]
            omega
          simpa [runFrom, hx, hy, hy', List.map_cons, List.flatMap_cons] using
            congrArg (fun r : M (List Val) => (do pure (Val.tup [a, b] :: (← r)) : M (List Val)))
              (ih 1 (j + 1) a b hk)

private theorem bp_initial (xs ys : List Val) (fuel : Nat) :
    iter fuel (.product [.vec .int xs, .vec .int ys]) none =
      match xs, ys with
      | a :: _, b :: _ => .ok (some (.tup [a, b], bpState a b 1 1))
      | _, _ => .ok none := by
  simp only [bp_prod_0]
  simp [anyIsdone0, isdone0, pIterate, bp_vec, bp_start, bp_idx]
  cases xs <;> cases ys <;> simp [bpState]

theorem productCorrect : ProductCorrect := by
  intro xs ys fuel _ _ hf
  constructor
  · cases xs with
    | nil => simp [elems, bp_initial, runFrom]
    | cons a xtail =>
      cases ys with
      | nil => simp [elems, bp_initial, runFrom]
      | cons b bt =>
        cases fuel with
        | zero => omega
        | succ k =>
          have hk : ((a :: xtail).drop 1).length +
              (a :: xtail).length * ((b :: bt).drop 1).length ≤ k := by
            simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hf
            simp only [List.drop_succ_cons, List.drop_zero, List.length_cons]
            omega
          have hr := bp_run (a :: xtail) (b :: bt) (by simp) k (k + 1) 1 1 a b hk
          simpa [elems, bp_initial, runFrom, List.flatMap_cons, List.map_cons]
            using congrArg (fun r : M (List Val) => (do pure (Val.tup [a, b] :: (← r)) : M (List Val))) hr
  · simp [size, prodSize, isz]

end JuliaLean.Iterators
