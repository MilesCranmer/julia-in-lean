import JuliaLean.Iterators.Spec
set_option maxRecDepth 4096

namespace JuliaLean.Iterators
open JuliaLean

namespace ProofsAList
attribute [local simp] Bind.bind Pure.pure Except.bind Except.pure
theorem iter_vec (fuel : Nat) (et : Ty) (xs : List Val) (st : Option St) :
    iter fuel (.vec et xs) st = idxIter xs st := rfl

theorem iter_tuple (fuel : Nat) (xs : List Val) (st : Option St) :
    iter fuel (.tuple xs) st = idxIter xs st := rfl


def nextAt (xs : List Val) (p : Nat) (st : Nat → St) : M (Option (Val × St)) :=
  match xs.drop p with
  | [] => .ok none
  | x :: _ => .ok (some (x, st (p + 1)))

theorem getD_head_drop (xs : List Val) (p : Nat) :
    xs.getD p .undef = (xs.drop p).headD .undef := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    cases p with
    | zero => rfl
    | succ p => simpa using ih p

theorem idxIter_at (xs : List Val) (p : Nat) :
    idxIter xs (some (.int (p + 1))) = nextAt xs p (fun q => .int (q + 1)) := by
  have hg := getD_head_drop xs p
  have hl := List.length_drop (i := p) (l := xs)
  simp only [idxIter, nextAt]
  have hnat : ((↑p + 1 : Int) - 1).toNat = p := by omega
  rw [hnat]
  cases hd : xs.drop p with
  | nil =>
    simp only [hd, List.length_nil] at hl
    simp [show ¬ (1 ≤ (↑p + 1 : Int) ∧ (↑p + 1 : Int) ≤ xs.length) by omega]
  | cons x ys =>
    simp only [hd, List.length_cons] at hl
    have hb : 1 ≤ (↑p + 1 : Int) ∧ (↑p + 1 : Int) ≤ xs.length := by omega
    simp only [hb, ↓reduceIte]
    rw [hg, hd]
    simp only [List.headD_cons]
    congr 3

theorem idxIter_start (xs : List Val) :
    idxIter xs none = nextAt xs 0 (fun q => .int (q + 1)) := by
  cases xs <;> simp [idxIter, nextAt, List.getD]

theorem runFrom_nextAt (xs : List Val) (st : Nat → St)
    (step : St → M (Option (Val × St)))
    (hs : ∀ p, p ≤ xs.length → step (st p) = nextAt xs p st)
    (p fuel : Nat) (hf : (xs.drop p).length ≤ fuel) :
    (do runFrom step fuel (← nextAt xs p st)) = .ok (xs.drop p) := by
  induction fuel generalizing p with
  | zero =>
    have hd : xs.drop p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [nextAt, hd, runFrom]
  | succ fuel ih =>
    cases hd : xs.drop p with
    | nil => simp [nextAt, hd, runFrom]
    | cons x ys =>
      have hdrop : xs.drop (p + 1) = ys := by
        rw [← List.drop_drop, hd]
        rfl
      have hh : (xs.drop (p + 1)).length ≤ fuel := by
        rw [hdrop]
        simp only [hd, List.length_cons] at hf
        omega
      have hp' : p + 1 ≤ xs.length := by
        have := List.length_drop (i := p) (l := xs)
        simp only [hd, List.length_cons] at this
        omega
      have hi := ih (p + 1) hh
      rw [hdrop] at hi
      rw [show nextAt xs p st = .ok (some (x, st (p + 1))) by simp [nextAt, hd]]
      simp only [Bind.bind, Except.bind, runFrom]
      rw [hs _ hp']
      cases hn : nextAt xs (p + 1) st with
      | error e => simp only [hn, Bind.bind, Except.bind] at hi; contradiction
      | ok v =>
        simp only [hn, Bind.bind, Except.bind] at hi ⊢
        rw [hi]
        rfl

theorem stateful_at (xs : List Val) (p : Nat) :
    (if xs.length ≤ p then (pure none : M (Option (Val × St)))
     else pure (some (xs.getD p .undef, .nat (p + 1)))) =
      nextAt xs p St.nat := by
  have hl := List.length_drop (i := p) (l := xs)
  have hg := getD_head_drop xs p
  unfold nextAt
  cases hd : xs.drop p with
  | nil =>
    simp only [hd, List.length_nil] at hl
    simp [show xs.length ≤ p by omega]
  | cons x ys =>
    simp only [hd, List.length_cons] at hl
    rw [hg, hd]
    simp [show ¬ xs.length ≤ p by omega]

theorem elems_stateful (xs : List Val) (pos fuel : Nat) (hf : xs.length < fuel) :
    elems fuel (.stateful .int xs pos) = .ok (xs.drop pos) := by
  let step := fun s => iter fuel (.stateful .int xs pos) (some s)
  have hs : ∀ p, step (.nat p) = nextAt xs p St.nat := by
    intro p
    change (if xs.length ≤ p then (pure none : M (Option (Val × St))) else pure (some (xs.getD p .undef, St.nat (p + 1)))) = _
    exact stateful_at xs p
  have hstart : iter fuel (.stateful .int xs pos) none = nextAt xs pos St.nat :=
    stateful_at xs pos
  unfold elems
  rw [hstart]
  exact runFrom_nextAt xs St.nat step (fun p _ => hs p) pos fuel (by
    have := List.length_drop (i := pos) (l := xs)
    omega)

theorem i64_val (x : Int) (h : -(2 ^ 63) ≤ x ∧ x ≤ 2 ^ 63 - 1) :
    (i64 x).val = x := by
  exact wrapInt_of_inRange .i64 x h

theorem i64_val_self (n : JInt64) : i64 n.val = n := by
  apply Subtype.ext
  exact wrapInt_of_inRange _ _ n.property

theorem toInt_self (n : JInt64) : toInt n = .ok n := by
  cases n with
  | mk v h => simp [toInt, liftJ, JInt.convert, h]

theorem sub_one_val (n : JInt64) (hn : 0 < n.val) :
    (n - i64 1).val = n.val - 1 := by
  change wrapInt .i64 (n.val - (i64 1).val) = _
  rw [i64_val 1 (by decide)]
  apply wrapInt_of_inRange .i64
  have hb := n.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
  omega

theorem mkTake_ok (it : Itr) (n : JInt64) (hn : 0 ≤ n.val) :
    mkTake it n = .ok (.take it n) := by
  change (if n.val < (i64 0).val then _ else _) = _
  have hzero : (i64 0).val = 0 := rfl
  rw [hzero, if_neg (by omega)]
  rfl

theorem mkDrop_ok (it : Itr) (n : JInt64) (hn : 0 ≤ n.val) :
    mkDrop it n = .ok (.drop it n) := by
  change (if n.val < (i64 0).val then _ else _) = _
  have hzero : (i64 0).val = 0 := rfl
  rw [hzero, if_neg (by omega)]
  rfl

theorem take_vec (xs : List Val) (n : JInt64) (hn : 0 ≤ n.val) :
    take (.vec .int xs) n = .ok (.take (.vec .int xs) n) := by
  change (do mkTake (.vec .int xs) (← toInt n)) = _
  rw [toInt_self]
  exact mkTake_ok _ n hn

theorem drop_vec (xs : List Val) (n : JInt64) (hn : 0 ≤ n.val) :
    drop (.vec .int xs) n = .ok (.drop (.vec .int xs) n) := by
  change (do mkDrop (.vec .int xs) (← toInt n)) = _
  rw [toInt_self]
  exact mkDrop_ok _ n hn

theorem jmin_val (a b : JInt64) : (jmin a b).val = min a.val b.val := by
  unfold jmin
  change (if b.val < a.val then b else a).val = _
  split <;> simp only [Int.min_def] <;> split <;> omega

theorem jmin_eq (a b : JInt64) : jmin a b = i64 (min a.val b.val) := by
  have h := i64_val_self (jmin a b)
  rw [jmin_val] at h
  exact h.symm

theorem fits_i64_length (xs : List α) (h : Fits xs) : (i64 xs.length).val = xs.length := by
  apply i64_val
  unfold Fits at h
  omega

end ProofsAList
end JuliaLean.Iterators
