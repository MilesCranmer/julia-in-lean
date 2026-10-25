import JuliaLean.Iterators.Spec

namespace JuliaLean.Iterators

open JuliaLean

private def countWrap (x : Int) : Int := wrapInt .i64 x

private theorem countWrap_add (x y : Int) :
    countWrap (countWrap x + y) = countWrap (x + y) := by
  simp only [countWrap, wrapInt, IntTy.signed, IntTy.bits, ite_true]
  omega

private theorem countWrap_right (x y : Int) :
    countWrap (x + countWrap y) = countWrap (x + y) := by
  rw [Int.add_comm x, countWrap_add, Int.add_comm y]

private theorem countWrap_mul (x y : Int) :
    countWrap (countWrap x * y) = countWrap (x * y) := by
  have h : countWrap x = x - 18446744073709551616 *
      ((x + 9223372036854775808) / 18446744073709551616) := by
    simp only [countWrap, wrapInt, IntTy.signed, IntTy.bits, ite_true]
    have := Int.emod_add_mul_ediv (x + 9223372036854775808) 18446744073709551616
    omega
  rw [h]
  simp only [countWrap, wrapInt, IntTy.signed, IntTy.bits, ite_true]
  rw [Int.sub_mul, Int.mul_assoc]
  omega

private theorem count_step (s d : JInt64) (i : Nat) :
    (i64 (s + i64 (i : Int) * d).val + d).val =
      (s + i64 ((i + 1 : Nat) : Int) * d).val := by
  change countWrap (countWrap (countWrap (s.val + countWrap (countWrap (i : Int) * d.val))) + d.val) =
    countWrap (s.val + countWrap (countWrap ((i + 1 : Nat) : Int) * d.val))
  simp only [countWrap_add, countWrap_right, countWrap_mul]
  simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
  rw [Int.add_assoc]

private theorem count_zero (s d : JInt64) :
    (s + i64 (0 : Int) * d).val = s.val := by
  change countWrap (s.val + countWrap (countWrap 0 * d.val)) = s.val
  simp only [countWrap_right, countWrap_mul, Int.zero_mul, Int.add_zero]
  exact wrapInt_of_inRange .i64 s.val s.property

private theorem count_prefix (s d : JInt64) (fuel k i : Nat) :
    prefixElems.runPrefix (fun st => iter fuel (.count s d) (some st)) k
      (some (.int (s + i64 (i : Int) * d).val, .int (s + i64 (i : Int) * d).val)) =
    .ok ((List.range k).map fun j => .int (s + i64 ((i + j : Nat) : Int) * d).val) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [prefixElems.runPrefix]
    change (do
      let tail ← prefixElems.runPrefix (fun st => iter fuel (.count s d) (some st)) k
        (some (.int (i64 (s + i64 (i : Int) * d).val + d).val,
          .int (i64 (s + i64 (i : Int) * d).val + d).val))
      pure (Val.int (s + i64 (i : Int) * d).val :: tail)) = _
    rw [count_step, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    apply congrArg (fun xs : List Val =>
      (Except.ok (Val.int (s + i64 (i : Int) * d).val :: xs) : M (List Val)))
    apply List.map_congr_left
    intro j hj
    have h : i + 1 + j = i + Nat.succ j := by omega
    exact congrArg (fun n : Nat => Val.int (s + i64 (n : Int) * d).val) h

theorem countfromCorrect : CountfromCorrect := by
  intro s d k fuel
  unfold prefixElems
  change prefixElems.runPrefix (fun st => iter fuel (.count s d) (some st)) k
    (some (.int s.val, .int s.val)) = _
  rw [← count_zero s d]
  simpa only [Nat.zero_add, Int.natCast_zero] using count_prefix s d fuel k 0

end JuliaLean.Iterators
