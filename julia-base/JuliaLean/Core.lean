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
  /-- Julia's `EOFError()` (`base/io.jl:12-17`): no more data was available to read. -/
  | eofError
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
def convert (functionName : String) (t : IntTy) (x : Int) : Jl (JInt t) :=
  if h : t.min ≤ x ∧ x ≤ t.max then .ok ⟨x, h⟩
  else .error (.inexactError functionName)

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

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- Julia exception types thrown by the modelled functions. -/
inductive Err where
  | dimensionMismatch
  | boundsError
  | inexactError
  | methodError
  | argumentError
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call that may throw. -/
abbrev R (α : Type) := Except Err α

deriving instance DecidableEq for Except

/-- Julia `Int`. -/
abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

end JuliaLean.BroadcastViews

namespace JuliaLean.Multidim

/-- Julia exception types thrown by the modelled functions. -/
inductive Err where
  | argumentError
  | boundsError
  | dimensionMismatch
  | divideError
  | overflowError
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call that may throw. -/
abbrev R (α : Type) := Except Err α

deriving instance DecidableEq for Except

/-- Exception type of an outcome, or `none` when the call returns. -/
def errKind {α : Type} : R α → Option Err
  | .ok _ => none
  | .error e => some e

/-- Julia `Int`. -/
abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

end JuliaLean.Multidim

namespace JuliaLean.Printf

open JuliaLean

/-- Code units, as natural numbers below 256. -/
abbrev Bytes := List Nat
/-- Julia `Int`. -/
abbrev I := JInt64

/-- An `Int` literal. -/
def ix (n : Int) : I := JInt.lit .i64 n

/-- Exceptions and undefined behaviour of Printf. -/
inductive Error where
  /-- `Printf.InvalidFormatStringError`. -/
  | invalidFormat
  /-- A Base exception. -/
  | julia (e : JlError)
  /-- A failed `::Integer` type assertion, `Printf.jl:300,304`. -/
  | typeError
  /-- A store outside the buffer where bounds checks are off (`@inbounds`, or C code
  writing through a pointer). Julia does not throw; the heap is corrupted. -/
  | unsafeWrite
  /-- An argument/conversion combination outside the model. -/
  | unmodelled
  deriving DecidableEq, Repr

abbrev Result (α : Type) := Except Error α

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

end JuliaLean.Printf

namespace JuliaLean.MissingChar

inductive JV (α : Type) where
  | missing
  | nothing
  | some (v : JV α)
  | val (a : α)
  deriving Repr

end JuliaLean.MissingChar

/-!
Bit-level helpers for unsigned `BitInteger` values, as Julia evaluates them.

All helpers take unsigned `JInt` operands, whose values are nonnegative, and
return the bit pattern Julia's intrinsics produce:

* `shr x k` is `x >> k` for a nonnegative count (`lshr_int`; a count of at
  least the width gives zero), `shl x k` is `x << k` (`shl_int`, wrapping).
* `shrI x k` is `x >> k` for an `Int` count: a negative count shifts left,
  `base/int.jl:542-560`.
* `band`, `bor`, `bxor` are `&`, `|`, `xor` (`and_int`, `or_int`, `xor_int`).
* `ofBool b` is `T(b)`, the value Julia uses for `x + b` with `b::Bool`.
-/

namespace JuliaLean.ParsePrint

open JuliaLean

variable {t : IntTy}

/-- `x >> k` with a nonnegative count on an unsigned value (`lshr_int`). -/
def shr (x : JInt t) (k : Nat) : JInt t := JInt.wrap t (x.val.toNat / 2^k)

/-- `x << k` with a nonnegative count (`shl_int`), wrapping. -/
def shl (x : JInt t) (k : Nat) : JInt t := JInt.wrap t (x.val.toNat * 2^k)

/-- `x >> k` for an `Int` count on an unsigned value, `base/int.jl:542-560`. -/
def shrI (x : JInt t) (k : Int) : JInt t :=
  if k ≥ 0 then shr x k.toNat else shl x (-k).toNat

/-- `x << k` for an `Int` count on an unsigned value, `base/int.jl:542-560`. -/
def shlI (x : JInt t) (k : Int) : JInt t :=
  if k ≥ 0 then shl x k.toNat else shr x (-k).toNat

/-- `x & y` (`and_int`) on unsigned values. -/
def band (x y : JInt t) : JInt t := JInt.wrap t (Nat.land x.val.toNat y.val.toNat)

/-- `x | y` (`or_int`) on unsigned values. -/
def bor (x y : JInt t) : JInt t := JInt.wrap t (Nat.lor x.val.toNat y.val.toNat)

/-- `x ⊻ y` (`xor_int`) on unsigned values. -/
def bxor (x y : JInt t) : JInt t := JInt.wrap t (Nat.xor x.val.toNat y.val.toNat)

/-- `T(b)` for `b::Bool`: Julia promotes a `Bool` operand to `0` or `1`. -/
def ofBool (t : IntTy) (b : Bool) : JInt t := JInt.lit t (if b then 1 else 0)

/-- Unsigned truncated division by a nonzero literal (`udiv_int`); no error is possible. -/
def udivLit (x : JInt t) (d : Nat) : JInt t := JInt.wrap t (x.val.toNat / d)

end JuliaLean.ParsePrint

namespace JuliaLean.IntArith.Rational

/-- `Rational{T}` and `unsafe_rational`; base/rational.jl:9-18. -/
structure Rat (t : IntTy) where
  num : JInt t
  den : JInt t
  deriving DecidableEq

/-- Rounding modes accepted by integer `div`; base/div.jl:326-373,415-416. -/
inductive Rounding where
  | toZero | down | up | nearest | nearestAway | nearestUp | fromZero
  deriving DecidableEq

end JuliaLean.IntArith.Rational

namespace JuliaLean.AbstractArraySpecs

abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

inductive AxKind where
  /-- `Base.OneTo{Int}`. -/
  | oneTo
  /-- A non-OneTo unit range, represented only by its endpoint values. -/
  | unit
  deriving DecidableEq, Repr

/-- A unit-range axis `lo:hi`. -/
structure Ax where
  kind : AxKind
  lo : I64
  hi : I64
  deriving DecidableEq, Repr

end JuliaLean.AbstractArraySpecs

/-!
Shared definitions of the `ReduceCov` area: the exceptions thrown by the modelled
methods of `base/reduce.jl`, `base/reducedim.jl`, `base/indices.jl`, `base/some.jl`
and `base/missing.jl` (master `bbfa0ce4150`).
-/

namespace JuliaLean.ReduceCov

/-- Julia exceptions of this area: the shared `JlError`s and the exception types
`JlError` does not have. -/
inductive Err where
  | jl (e : JlError)
  | dimensionMismatch (msg : String)
  | missingException (msg : String)
  | errorException (msg : String)
  | typeError
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call of this area that may throw. -/
abbrev RJ (α : Type) := Except Err α

instance instDecidableEqRJ {α : Type} [DecidableEq α] : DecidableEq (RJ α) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .error x, .error y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)

/-- `ArgumentError(msg)`. -/
def argErr (msg : String) : Err := .jl (.argumentError msg)

/-- `BoundsError`. -/
def boundsErr : Err := .jl .boundsError

abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

end JuliaLean.ReduceCov

namespace JuliaLean.Reduce

/-- Julia exception types thrown by the modelled reductions. -/
inductive Err where
  | argumentError
  | inexactError
  | typeError
  | methodError
  | dimensionMismatch
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call that may throw. -/
abbrev R (α : Type) := Except Err α

deriving instance DecidableEq for Except

end JuliaLean.Reduce

namespace JuliaLean.MiscCov

/-- The exception types thrown by the modelled methods. Messages are kept only
where a property is about them. -/
inductive Err where
  | errorException (msg : String)
  | argumentError (msg : String)
  | typeError
  | methodError
  | inexactError
  | overflowError
  | boundsError
  | undefRefError
  | assertionError
  | fieldError
  | other (name : String)
  deriving Repr, DecidableEq, Inhabited

deriving instance DecidableEq for Except

/-- A Julia computation that returns a value or throws. -/
abbrev M (α : Type) := Except Err α

/-- Julia syntax values: `Symbol`s, literals, `QuoteNode`, `GlobalRef`,
`LineNumberNode`, other runtime values (by a descriptive tag) and `Expr`. -/
inductive Ex where
  | sym (name : String)
  | str (value : String)
  | int (value : Int)
  | bool (value : Bool)
  | nothing
  | qn (value : Ex)
  | gref (mod name : String)
  | lnn
  | val (tag : String)
  | expr (head : String) (args : List Ex)
  deriving Repr, Inhabited

namespace Ex

/-- `Meta.isexpr(ex, head)`. -/
def isExpr (ex : Ex) (head : String) : Bool :=
  match ex with
  | .expr h _ => h == head
  | _ => false

/-- `ex.args` of an `Expr`; `none` for other values (a `FieldError` in Julia). -/
def args? : Ex → Option (List Ex)
  | .expr _ a => some a
  | _ => none

/-- `ex isa LineNumberNode`. -/
def isLnn : Ex → Bool
  | .lnn => true
  | _ => false

/-- `ex === :name`. -/
def isSym (name : String) : Ex → Bool
  | .sym s => s == name
  | _ => false

/-- `esc(ex)`, `base/essentials.jl`. -/
def esc (ex : Ex) : Ex := .expr "escape" [ex]

end Ex

end JuliaLean.MiscCov

namespace JuliaLean.ShellCmd

open JuliaLean

/-- Exceptions thrown by the modelled functions. `error` is the
`ErrorException` thrown by `error(msg)`; `typeError` is the `TypeError` of a
failed `x::T` assertion; `fuel` marks a loop bound that is never reached. -/
inductive ShErr where
  | jl (e : JlError)
  | error (msg : String)
  | stringIndex
  | typeError
  | outOfMemory
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev SH (α : Type) := Except ShErr α

deriving instance DecidableEq for Except

/-- A Julia `Char`: its raw bits. -/
abbrev JC := UInt32
/-- A Julia string: the characters iteration yields. -/
abbrev JS := List UInt32

end JuliaLean.ShellCmd
