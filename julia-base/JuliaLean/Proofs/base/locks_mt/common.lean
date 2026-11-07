import JuliaLean.base.locks_mt

/-! Shared proof helpers for retained concurrency declarations. -/

namespace JuliaLean.ConcurrencyCov

open JuliaLean


@[simp] theorem upd_same {β : Type} (f : Nat → β) (t : Nat) (v : β) : upd f t v t = v := by
  simp [upd]

@[simp] theorem upd_other {β : Type} (f : Nat → β) (t u : Nat) (v : β) (h : u ≠ t) :
    upd f t v u = f u := by
  simp [upd, h]

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem i64_val (x : Int) (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) : (i64 x).val = x :=
  wrapInt_of_inRange .i64 x ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

theorem i64_nat_val (n : Nat) (h : n < 2 ^ 63) : (i64 n).val = n := i64_val n (by omega) (by omega)

theorem i16_val (x : Int) (h1 : -2 ^ 15 ≤ x) (h2 : x < 2 ^ 15) : (JInt.lit .i16 x).val = x :=
  wrapInt_of_inRange .i16 x ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

theorem i64_one : (i64 1).val = 1 := i64_val 1 (by omega) (by omega)

@[simp] theorem i8_zero_val : (i8 0).val = 0 := rfl
@[simp] theorem i8_one_val : (i8 1).val = 1 := rfl
@[simp] theorem i8_neg_one_val : (i8 (-1)).val = -1 := rfl

end JuliaLean.ConcurrencyCov
