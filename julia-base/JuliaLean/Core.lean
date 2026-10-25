/-!
Shared model of Julia's primitive integer types and errors.

Every area builds on these definitions; extend them here only when the new
definition is a Julia primitive (an intrinsic or a one-line method in
`base/int.jl`) that several areas need.

* A Julia exception is a `JlError`; a Julia call that may throw returns
  `Jl α = Except JlError α`.
* `IntTy` enumerates the ten `BitInteger` types. A value of type `t` is a
  mathematical integer in `[t.min, t.max]` (`JInt t`).
* `wrap t x` is two's-complement reduction of `x` into `t`, i.e. Julia's
  `x % t`. The wrapping operators `+ - *` and unary `-` on `BitInteger` are
  `wrap` of the exact result.
* `sdiv`/`srem`/`udiv`/`urem` are the checked intrinsics behind `div` and `rem`
  on same-type `BitInteger` arguments (`checked_sdiv_int` etc.,
  `base/int.jl`): division by zero throws `DivideError`, and signed
  `div(typemin(T), -1)` throws `DivideError`. `rem(typemin(T), -1) == 0`.
-/

namespace JuliaLean

inductive JlError where
  | overflowError (msg : String)
  | argumentError (msg : String)
  | boundsError
  | inexactError (fn : String)
  | divideError
  | domainError (msg : String)
  | methodError (fn : String)
  deriving Repr, DecidableEq, Inhabited

abbrev Jl (α : Type) := Except JlError α

/-- Julia's `BitInteger` types. -/
inductive IntTy where
  | i8 | i16 | i32 | i64 | i128
  | u8 | u16 | u32 | u64 | u128
  deriving Repr, DecidableEq, Inhabited

namespace IntTy

def signed : IntTy → Bool
  | i8 | i16 | i32 | i64 | i128 => true
  | u8 | u16 | u32 | u64 | u128 => false

def bits : IntTy → Nat
  | i8 | u8 => 8
  | i16 | u16 => 16
  | i32 | u32 => 32
  | i64 | u64 => 64
  | i128 | u128 => 128

/-- `typemin(T)` as a mathematical integer. -/
def min (t : IntTy) : Int := if t.signed then -(2 ^ (t.bits - 1) : Int) else 0

/-- `typemax(T)` as a mathematical integer. -/
def max (t : IntTy) : Int := if t.signed then (2 ^ (t.bits - 1) : Int) - 1 else (2 ^ t.bits : Int) - 1

/-- `signed(T)` and `unsigned(T)`. -/
def toSigned : IntTy → IntTy
  | u8 => i8 | u16 => i16 | u32 => i32 | u64 => i64 | u128 => i128 | t => t
def toUnsigned : IntTy → IntTy
  | i8 => u8 | i16 => u16 | i32 => u32 | i64 => u64 | i128 => u128 | t => t

/-- Integer promotion rules, `base/int.jl:809-822`: wider wins, unsigned breaks ties. -/
def promote (t s : IntTy) : IntTy :=
  if t.bits > s.bits then t
  else if s.bits > t.bits then s
  else if t.signed then s else t

def name : IntTy → String
  | i8 => "Int8" | i16 => "Int16" | i32 => "Int32" | i64 => "Int64" | i128 => "Int128"
  | u8 => "UInt8" | u16 => "UInt16" | u32 => "UInt32" | u64 => "UInt64" | u128 => "UInt128"

end IntTy

/-- A value of the Julia integer type `t`. -/
abbrev JInt (t : IntTy) := { x : Int // t.min ≤ x ∧ x ≤ t.max }

/-- Julia's `Int` on 64-bit platforms. -/
abbrev JInt64 := JInt .i64

/-- Two's-complement reduction of `x` into the range of `t` (Julia `x % T`). -/
def wrapInt (t : IntTy) (x : Int) : Int :=
  if t.signed then
    (x + 2 ^ (t.bits - 1)) % (2 ^ t.bits) - 2 ^ (t.bits - 1)
  else
    x % (2 ^ t.bits)

theorem wrapInt_bounds (t : IntTy) (x : Int) : t.min ≤ wrapInt t x ∧ wrapInt t x ≤ t.max := by
  cases t <;> simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_of_inRange (t : IntTy) (x : Int) (h : t.min ≤ x ∧ x ≤ t.max) :
    wrapInt t x = x := by
  cases t <;> simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h ⊢ <;> omega

namespace JInt

variable {t : IntTy}

def wrap (t : IntTy) (x : Int) : JInt t := ⟨wrapInt t x, wrapInt_bounds t x⟩

/-- `T(x)` / `convert(T, x)`: exact conversion, `InexactError` when out of range. -/
def convert (t : IntTy) (x : Int) : Jl (JInt t) :=
  if h : t.min ≤ x ∧ x ≤ t.max then .ok ⟨x, h⟩ else .error (.inexactError t.name)

def typemin (t : IntTy) : JInt t := wrap t t.min
def typemax (t : IntTy) : JInt t := wrap t t.max

/-- Literal of type `t` (wraps, like `x % T`). -/
def lit (t : IntTy) (x : Int) : JInt t := wrap t x

instance : Add (JInt t) := ⟨fun a b => wrap t (a.val + b.val)⟩
instance : Sub (JInt t) := ⟨fun a b => wrap t (a.val - b.val)⟩
instance : Mul (JInt t) := ⟨fun a b => wrap t (a.val * b.val)⟩
instance : Neg (JInt t) := ⟨fun a => wrap t (-a.val)⟩
instance : LT (JInt t) := ⟨fun a b => a.val < b.val⟩
instance : LE (JInt t) := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : JInt t) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : JInt t) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))

/-- `x % T2` for a value of another integer type. -/
def rem (t' : IntTy) (a : JInt t) : JInt t' := wrap t' a.val

/-- Signed/unsigned `div` intrinsic (`checked_sdiv_int`/`checked_udiv_int`), truncating. -/
def div (a b : JInt t) : Jl (JInt t) :=
  if b.val = 0 then .error .divideError
  else if t.signed ∧ a.val = t.min ∧ b.val = -1 then .error .divideError
  else .ok (wrap t (a.val.tdiv b.val))

/-- Signed/unsigned `rem` intrinsic (`checked_srem_int`/`checked_urem_int`), truncating. -/
def remInt (a b : JInt t) : Jl (JInt t) :=
  if b.val = 0 then .error .divideError else .ok (wrap t (a.val.tmod b.val))

/-- Same-type floored division, `base/div.jl:460-464`, with wrapping correction. -/
def fld (a b : JInt t) : Jl (JInt t) := do
  let d ← div a b
  if t.signed then
    pure (d - lit t (if ((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
        (d * b).val ≠ a.val then 1 else 0))
  else pure d

/-- Same-type ceiled division, `base/div.jl:467-474`, with wrapping correction. -/
def cld (a b : JInt t) : Jl (JInt t) := do
  let d ← div a b
  pure (d + lit t (if (¬ t.signed ∨ (a.val > 0 ↔ b.val > 0)) ∧
      (d * b).val ≠ a.val then 1 else 0))

/-- Same-type modulus, `base/int.jl:331-351`; `-1` bypasses quotient overflow. -/
def mod (a b : JInt t) : Jl (JInt t) :=
  if t.signed then
    if b.val = -1 then pure (lit t 0)
    else do
      let d ← fld a b
      pure (a - d * b)
  else remInt a b

end JInt

end JuliaLean
