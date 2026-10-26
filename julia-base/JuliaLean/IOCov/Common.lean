import JuliaLean.Core

set_option linter.unusedSimpArgs false

/-!
Shared vocabulary of the `IOCov` area: the exceptions thrown by the I/O, path,
environment, libc, libdl and command files of Base, and small byte helpers.

Foreign calls (`ccall`) are modelled as function arguments: a model receives
the C function's result and mirrors the Julia code around it (argument
conversions, error checks, result conversions).
-/

namespace JuliaLean.IOCov

open JuliaLean

deriving instance DecidableEq for Except

/-- Exceptions raised by the modelled methods. -/
inductive Err where
  /-- An exception already in `JuliaLean.JlError` (`ArgumentError`, `InexactError`, ...). -/
  | jl (e : JlError)
  /-- `SystemError(prefix, errno)` from `systemerror(prefix, cond)`. -/
  | systemError (pfx : String)
  /-- `IOError` from `uv_error(prefix, rc)` / `Base.uv_error`. -/
  | uvError (pfx : String)
  /-- `EOFError()`. -/
  | eofError
  /-- `KeyError(k)`. -/
  | keyError (k : List UInt8)
  /-- `ErrorException(msg)` from `error(...)`. -/
  | errorException (msg : String)
  /-- `FieldError`: access to a field the type does not have. -/
  | fieldError (field : String)
  /-- `TypeError`. -/
  | typeError (ctx : String)
  /-- `MethodError(f, args)`. -/
  | methodError (f : String)
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except Err α

/-- `throw(ArgumentError(msg))`. -/
def argErr {α} (msg : String) : R α := .error (.jl (.argumentError msg))

/-- `systemerror(p, cond)`: throws `SystemError(p)` when `cond` holds. -/
def systemerror (p : String) (cond : Bool) : R Unit :=
  if cond then .error (.systemError p) else .ok ()

/-- `Base.uv_error(p, rc)`: throws when the libuv return code is negative. -/
def uvError (p : String) (rc : Int) : R Unit :=
  if rc < 0 then .error (.uvError p) else .ok ()

/-- `T(x)` for a Julia integer type `T`: `InexactError` when `x` is out of range. -/
def toInt (t : IntTy) (x : Int) : R Int :=
  if t.min ≤ x ∧ x ≤ t.max then .ok x else .error (.jl (.inexactError t.name))

/-- `x % T` for a Julia integer type `T` (two's-complement wrap). -/
def wrapTo (t : IntTy) (x : Int) : Int := wrapInt t x

/-- A C string: `none` is `C_NULL`, `some bytes` the bytes before the NUL. -/
abbrev CStr := Option (List UInt8)

/-- `p == C_NULL ? "" : unsafe_string(p)`. -/
def cstrOrEmpty : CStr → List UInt8
  | none => []
  | some s => s

theorem take_length_succ_append {α} (l : List α) (x : α) (rest : List α) :
    (l ++ x :: rest).take (l.length + 1) = l ++ [x] := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.take_succ_cons, ih]

/-- Bytes of an ASCII string literal. -/
def bs (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)

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
