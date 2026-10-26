import JuliaLean.Core

/-!
Shared vocabulary of the `ConcurrencyCov` area (Julia master `bbfa0ce4150`).

Exceptions are modelled by type, with the message only where a property or a
branch of the source depends on it. Opaque Julia values (task results, user
objects, function results) are natural numbers: equal numbers stand for `===`
objects.
-/

namespace JuliaLean.ConcurrencyCov

open JuliaLean

abbrev I64 := JInt .i64
abbrev U64 := JInt .u64
abbrev I32 := JInt .i32
abbrev I16 := JInt .i16
abbrev I8 := JInt .i8
abbrev U32 := JInt .u32
abbrev U8 := JInt .u8

def i64 (x : Int) : I64 := JInt.lit .i64 x
def i32 (x : Int) : I32 := JInt.lit .i32 x
def i8 (x : Int) : I8 := JInt.lit .i8 x
def u32 (x : Int) : U32 := JInt.lit .u32 x
def u64 (x : Int) : U64 := JInt.lit .u64 x

/-- Exceptions thrown by the modelled methods. -/
inductive Exn where
  | errorException (msg : String)
  | argumentError (msg : String)
  | inexactError
  | domainError
  | boundsError
  | methodError
  | concurrencyViolation
  | assertionError (msg : String)
  /-- `TypeError` of a failed type assertion. -/
  | typeError
  | undefVarError (name : String)
  /-- `InvalidStateException(msg, state)`. -/
  | invalidState (msg : String) (state : String)
  /-- `TaskFailedException(t)` for the task numbered `t`. -/
  | taskFailed (t : Nat)
  /-- `CompositeException` of `TaskFailedException`s of the listed tasks. -/
  | composite (ts : List Nat)
  /-- `CancellationRequest(sev)`. -/
  | cancellation (sev : Nat)
  /-- A user exception, e.g. thrown by a callback. -/
  | user (n : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev R (α : Type) := Except Exn α

/-- Outcome of user code: a value or a thrown exception. -/
abbrev Outcome := R Nat

/-- A per-task table with the entry of task `t` replaced by `v`. -/
def upd {β : Type} (f : Nat → β) (t : Nat) (v : β) : Nat → β := fun u => if u = t then v else f u

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
