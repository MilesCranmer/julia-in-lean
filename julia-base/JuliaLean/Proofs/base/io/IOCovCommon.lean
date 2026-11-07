import JuliaLean.base.io

set_option linter.unusedSimpArgs false

namespace JuliaLean.IOCov

open JuliaLean

theorem take_length_succ_append {α} (l : List α) (x : α) (rest : List α) :
    (l ++ x :: rest).take (l.length + 1) = l ++ [x] := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.take_succ_cons, ih]

theorem toInt_ok (t : IntTy) (x : Int) (h1 : t.min ≤ x) (h2 : x ≤ t.max) : toInt t x = .ok x := by
  unfold toInt; rw [if_pos ⟨h1, h2⟩]

theorem toInt_err (t : IntTy) (x : Int) (h : ¬ (t.min ≤ x ∧ x ≤ t.max)) :
    toInt t x = .error (.jl (.inexactError t.name)) := by
  unfold toInt; rw [if_neg h]

@[simp] theorem i32_min : IntTy.i32.min = -2147483648 := rfl
@[simp] theorem i32_max : IntTy.i32.max = 2147483647 := rfl
@[simp] theorem u32_min : IntTy.u32.min = 0 := rfl
@[simp] theorem u32_max : IntTy.u32.max = 4294967295 := rfl
@[simp] theorem i64_min : IntTy.i64.min = -9223372036854775808 := rfl
@[simp] theorem i64_max : IntTy.i64.max = 9223372036854775807 := rfl
@[simp] theorem u64_min : IntTy.u64.min = 0 := rfl
@[simp] theorem u64_max : IntTy.u64.max = 18446744073709551615 := rfl
@[simp] theorem u8_min : IntTy.u8.min = 0 := rfl
@[simp] theorem u8_max : IntTy.u8.max = 255 := rfl
@[simp] theorem i32_name : IntTy.i32.name = "Int32" := rfl
@[simp] theorem u32_name : IntTy.u32.name = "UInt32" := rfl
@[simp] theorem i64_name : IntTy.i64.name = "Int64" := rfl
@[simp] theorem u64_name : IntTy.u64.name = "UInt64" := rfl

/-- `toInt` on in-range values, for rewriting. -/
theorem toInt_i32 (x : Int) (h1 : -2147483648 ≤ x) (h2 : x ≤ 2147483647) : toInt .i32 x = .ok x :=
  toInt_ok _ _ (by simpa using h1) (by simpa using h2)
theorem toInt_u32 (x : Int) (h1 : 0 ≤ x) (h2 : x ≤ 4294967295) : toInt .u32 x = .ok x :=
  toInt_ok _ _ (by simpa using h1) (by simpa using h2)
theorem toInt_i64 (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    toInt .i64 x = .ok x := toInt_ok _ _ (by simpa using h1) (by simpa using h2)
theorem toInt_u64 (x : Int) (h1 : 0 ≤ x) (h2 : x ≤ 18446744073709551615) : toInt .u64 x = .ok x :=
  toInt_ok _ _ (by simpa using h1) (by simpa using h2)
theorem toInt_u32_neg (x : Int) (h : x < 0 ∨ 4294967295 < x) :
    toInt .u32 x = .error (.jl (.inexactError "UInt32")) :=
  toInt_err _ _ (by simp; omega)
theorem toInt_u64_neg (x : Int) (h : x < 0) : toInt .u64 x = .error (.jl (.inexactError "UInt64")) :=
  toInt_err _ _ (by simp; omega)

end JuliaLean.IOCov
