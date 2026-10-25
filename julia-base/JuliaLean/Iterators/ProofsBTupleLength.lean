import JuliaLean.Iterators.Spec

set_option maxRecDepth 4096

namespace JuliaLean.Iterators
open JuliaLean

private theorem btl_mul_ok (x y z : JInt64)
    (hr : IntTy.i64.min ≤ x.val * y.val ∧ x.val * y.val ≤ IntTy.i64.max)
    (hz : z.val = x.val * y.val) : checkedMul64 x y = .ok z := by
  have hm := IntArith.Checked.intrinsicMulExact .i64 x y (by decide) (by decide)
  simp only [IntArith.Checked.ExactOrOverflow, hr, ite_true] at hm
  obtain ⟨v, hv, he⟩ := hm
  have hsame : v = z := Subtype.ext (he.trans hz.symm)
  unfold checkedMul64
  rw [hv, hsame]
  rfl

private theorem btl_mul_error (x y : JInt64)
    (hr : ¬ (IntTy.i64.min ≤ x.val * y.val ∧ x.val * y.val ≤ IntTy.i64.max)) :
    checkedMul64 x y = .error (.jl (.overflowError "")) := by
  have hm := IntArith.Checked.intrinsicMulExact .i64 x y (by decide) (by decide)
  simp only [IntArith.Checked.ExactOrOverflow, hr, ite_false] at hm
  unfold checkedMul64
  rw [hm]
  rfl

private theorem btl_len_raw (ts : List Ty) (xs : List Val) :
    len (.flatten (.vec (.tuple ts) xs)) =
      (do checkedMul64 (i64 ts.length) (← len (.vec (.tuple ts) xs))) := rfl

private theorem btl_len_vec (t : Ty) (xs : List Val) :
    len (.vec t xs) = .ok (i64 xs.length) := rfl

private theorem btl_ok_bind {α β : Type} (a : α) (f : α → M β) :
    ((.ok a : M α) >>= f) = f a := rfl

private theorem btl_len (ts : List Ty) (xs : List Val) :
    len (.flatten (.vec (.tuple ts) xs)) = checkedMul64 (i64 ts.length) (i64 xs.length) := by
  rw [btl_len_raw, btl_len_vec]
  exact btl_ok_bind _ _

private theorem btl_literal (n : Nat) (h : n < 2 ^ 62) : (i64 n).val = n := by
  apply wrapInt_of_inRange .i64
  change -(2 ^ 63) ≤ (n : Int) ∧ (n : Int) ≤ 2 ^ 63 - 1
  omega

theorem flattenTupleLength : FlattenTupleLength := by
  intro k xs hxs hk
  rw [btl_len, List.length_replicate]
  have hx : (i64 xs.length).val = xs.length :=
    btl_literal xs.length (by unfold Fits at hxs; omega)
  have hkv : (i64 k).val = k := btl_literal k hk
  constructor
  · intro h
    have hr : IntTy.i64.min ≤ (k : Int) * xs.length ∧
        (k : Int) * xs.length ≤ IntTy.i64.max := by
      change -(2 ^ 63) ≤ (k : Int) * xs.length ∧ (k : Int) * xs.length ≤ 2 ^ 63 - 1
      have hp := Int.mul_nonneg (Int.natCast_nonneg k) (Int.natCast_nonneg xs.length)
      unfold maxIntVal at h
      omega
    apply btl_mul_ok
    · simpa only [hkv, hx] using hr
    · rw [hkv, hx]
      exact wrapInt_of_inRange .i64 _ hr
  · intro h
    refine ⟨"", btl_mul_error _ _ ?_⟩
    rw [hkv, hx]
    change ¬ (-(2 ^ 63) ≤ (k : Int) * xs.length ∧ (k : Int) * xs.length ≤ 2 ^ 63 - 1)
    unfold maxIntVal at h
    omega

end JuliaLean.Iterators
