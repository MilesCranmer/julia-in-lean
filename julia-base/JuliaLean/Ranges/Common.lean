import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.Ranges

deriving instance DecidableEq for Except

/-- `base/int.jl:10-36`, `base/bool.jl:3-6`: built-in integer scalar types. -/
inductive NType where
  | bool
  | bit (t : IntTy)
  deriving DecidableEq, Repr

/-- `base/bool.jl:3`, `base/int.jl:10-36`: scalar storage uses Core's fixed-width integers. -/
def NVal : NType → Type
  | .bool => Bool
  | .bit t => JInt t

instance (t : NType) : DecidableEq (NVal t) := by
  cases t <;> unfold NVal <;> infer_instance

/-- `base/int.jl:10-36`, `base/bool.jl:3`: a dynamically typed built-in integer. -/
structure Num where
  ty : NType
  value : NVal ty
  deriving DecidableEq

namespace NType

/-- `base/int.jl:26-36`: signed integer classification. -/
def signed : NType → Bool
  | .bool => false
  | .bit t => t.signed

/-- `base/int.jl:10-24`: machine integer widths; Bool occupies one byte. -/
def bits : NType → Nat
  | .bool => 8
  | .bit t => t.bits

/-- `base/range.jl:810-814`: the small-integer specialization on 64-bit Julia. -/
def small : NType → Bool
  | .bool => false
  | .bit t => t.bits < 64

/-- `base/int.jl:74-80,256-273`: unsigned reinterpretation type. -/
def unsigned : NType → NType
  | .bool => .bit .u64
  | .bit t => .bit t.toUnsigned

/-- `base/int.jl:74-80`: signed reinterpretation type. -/
def signedType : NType → NType
  | .bool => .bit .i64
  | .bit t => .bit t.toSigned

/-- `base/int.jl:911-918`: widening of inputs in the BitInteger64 specialization. -/
def widen64 (ty : NType) (h : ty.bits ≤ 64) : NType :=
  match ty with
  | .bool => .bool
  | .bit .i8 => .bit .i16
  | .bit .i16 => .bit .i32
  | .bit .i32 => .bit .i64
  | .bit .i64 => .bit .i128
  | .bit .u8 => .bit .u16
  | .bit .u16 => .bit .u32
  | .bit .u32 => .bit .u64
  | .bit .u64 => .bit .u128
  | .bit .i128 => False.elim (by simp [NType.bits, IntTy.bits] at h)
  | .bit .u128 => False.elim (by simp [NType.bits, IntTy.bits] at h)

end NType

namespace Num

/-- `base/int.jl:10-36`, `base/bool.jl:166-170`: mathematical interpretation. -/
def val (x : Num) : Int :=
  match x with
  | ⟨.bool, b⟩ => if (show Bool from b) then 1 else 0
  | ⟨.bit _, n⟩ => n.val

/-- `base/int.jl:632-648,694-701`: `% T` wrapping conversion, including parity for Bool. -/
def lit (ty : NType) (x : Int) : Num :=
  match ty with
  | .bool => ⟨.bool, decide (x % 2 ≠ 0)⟩
  | .bit t => ⟨.bit t, JInt.wrap t x⟩

/-- `base/int.jl:97`, `base/bool.jl:170`: exact conversion can throw InexactError. -/
def cast (ty : NType) (x : Num) : Jl Num :=
  match ty with
  | .bool => if x.val = 0 ∨ x.val = 1 then .ok (lit .bool x.val)
      else .error (.inexactError "Bool")
  | .bit t => do
      let n ← JInt.convert t x.val
      pure ⟨.bit t, n⟩

/-- `base/int.jl:809-825`, `base/bool.jl:6`: wider type wins; unsigned wins ties. -/
def promote (a b : NType) : NType :=
  match a, b with
  | .bool, t | t, .bool => t
  | .bit s, .bit t => .bit (IntTy.promote s t)

/-- `base/number.jl:364`, `base/bool.jl:8`: integer zero. -/
def zero (ty : NType) : Num := lit ty 0

/-- `base/number.jl:405,430-431`, `base/bool.jl:9`: integer unit. -/
def one (ty : NType) : Num := lit ty 1

/-- `base/int.jl:85-94,1093-1100`, `base/bool.jl:145-148`: wrapping addition. -/
def add (a b : Num) : Num :=
  let ty := if a.ty = .bool ∧ b.ty = .bool then .bit .i64 else promote a.ty b.ty
  match ty with
  | .bool => lit ty (a.val + b.val)
  | .bit t => ⟨.bit t, JInt.wrap t a.val + JInt.wrap t b.val⟩

/-- `base/int.jl:85-94,1093-1100`, `base/bool.jl:146-148`: wrapping subtraction. -/
def sub (a b : Num) : Num :=
  let ty := if a.ty = .bool ∧ b.ty = .bool then .bit .i64 else promote a.ty b.ty
  match ty with
  | .bool => lit ty (a.val - b.val)
  | .bit t => ⟨.bit t, JInt.wrap t a.val - JInt.wrap t b.val⟩

/-- `base/int.jl:85-94,1093-1100`, `base/bool.jl:149-150`: Bool product remains Bool. -/
def mul (a b : Num) : Num :=
  match promote a.ty b.ty with
  | .bool => lit .bool (a.val * b.val)
  | .bit t => ⟨.bit t, JInt.wrap t a.val * JInt.wrap t b.val⟩

/-- `base/int.jl:85`, `base/bool.jl:142-143`: unary minus wraps; Bool yields Int. -/
def neg (a : Num) : Num :=
  match a.ty with
  | .bool => ⟨.bit .i64, -(JInt.wrap .i64 a.val)⟩
  | .bit t => ⟨.bit t, -(JInt.wrap t a.val)⟩

/-- `base/bool.jl:140-141`: unary plus converts Bool to Int. -/
def pos (a : Num) : Num := if a.ty = .bool then lit (.bit .i64) a.val else a

/-- `base/int.jl:96-97`, `base/boot.jl:1206-1214`: negate unsigned exactly as signed. -/
def negate (a : Num) : Jl Num := do
  if a.ty = .bool ∨ a.ty.signed then pure (neg a)
  else
    let s ← cast a.ty.signedType a
    pure (neg s)

/-- `base/int.jl:256-273`: unsigned reinterprets the bit pattern. -/
def unsigned (a : Num) : Num := lit a.ty.unsigned a.val

/-- `base/int.jl:193-201`, `base/number.jl:255`: flipsign retains integer width; Bool becomes Int. -/
def flipsign (a s : Num) : Num := if s.val < 0 then neg a else pos a

/-- `base/int.jl:203-207`: sign-copying for integer unit steps. -/
def copysign (a s : Num) : Num :=
  if decide (a.val < 0) != decide (s.val < 0) then neg a else pos a


/-- `base/int.jl:357-360,1085-1090`, `base/bool.jl:166-168`: same-sign scalar intrinsic. -/
def primitiveDivRem (remainder : Bool) (a b : Num) : Jl Num := do
  let ty := promote a.ty b.ty
  let a ← cast ty a
  let b ← cast ty b
  match ty with
  | .bool =>
      if b.val = 0 then .error .divideError
      else pure (if remainder then zero .bool else a)
  | .bit t =>
      let x := JInt.wrap t a.val
      let y := JInt.wrap t b.val
      let z ← if remainder then JInt.remInt x y else JInt.div x y
      pure ⟨.bit t, z⟩

/-- `base/int.jl:275-279`: mixed sign division first divides unsigned absolute values. -/
def div (a b : Num) : Jl Num := do
  if a.ty = .bool ∨ b.ty = .bool ∨ a.ty.signed = b.ty.signed then
    primitiveDivRem false a b
  else if a.ty.signed then
    let q ← primitiveDivRem false (unsigned (flipsign a a)) b
    pure (flipsign (lit q.ty.signedType q.val) a)
  else
    let q ← primitiveDivRem false a (unsigned (flipsign b b))
    pure (unsigned (flipsign (lit q.ty.signedType q.val) b))

/-- `base/int.jl:278-279`: mixed sign remainder retains the dividend's signedness. -/
def rem (a b : Num) : Jl Num := do
  if a.ty = .bool ∨ b.ty = .bool ∨ a.ty.signed = b.ty.signed then
    primitiveDivRem true a b
  else if a.ty.signed then
    let r ← primitiveDivRem true (unsigned (flipsign a a)) b
    pure (flipsign (lit r.ty.signedType r.val) a)
  else primitiveDivRem true a (unsigned (flipsign b b))

/-- `base/int.jl:331-352`: mixed-sign modulus follows the explicit rem/correction branches. -/
def mod (a b : Num) : Jl Num := do
  if a.ty = .bool ∨ b.ty = .bool ∨ a.ty.signed = b.ty.signed then
    let ty := promote a.ty b.ty
    let a ← cast ty a
    let b ← cast ty b
    match ty with
    | .bool => rem a b
    | .bit t => do
        let z ← JInt.mod (JInt.wrap t a.val) (JInt.wrap t b.val)
        pure ⟨.bit t, z⟩
  else if a.ty.signed then
    let r ← rem a b
    pure (unsigned (add r (mul (lit .bool (if r.val < 0 then 1 else 0)) b)))
  else
    let r ← rem a b
    let r := lit r.ty.signedType r.val
    pure (add r (mul (lit .bool (if r.val ≠ 0 ∧ b.val < 0 then 1 else 0)) b))

/-- `base/checked.jl:26-27,166-175,228-234`: checked arithmetic uses exact promotion. -/
def checkedBinary (subtract : Bool) (a b : Num) : Jl Num := do
  let ty := promote a.ty b.ty
  let a ← cast ty a
  let b ← cast ty b
  let z := if subtract then a.val - b.val else a.val + b.val
  match ty with
  | .bool => pure (if subtract then sub a b else add a b)
  | .bit t =>
      if t.min ≤ z ∧ z ≤ t.max then pure (if subtract then sub a b else add a b)
      else .error (.overflowError "checked arithmetic")

/-- `base/checked.jl:26,166-175`: checked addition. -/
def checkedAdd : Num → Num → Jl Num := checkedBinary false

/-- `base/checked.jl:27,228-234`: checked subtraction. -/
def checkedSub : Num → Num → Jl Num := checkedBinary true

/-- `base/int.jl:596-597`, `base/promotion.jl:526,677`: mixed min returns the signed type. -/
def min (a b : Num) : Num :=
  let ty := if a.ty ≠ .bool ∧ b.ty ≠ .bool ∧ a.ty.signed ≠ b.ty.signed then
      if a.ty.signed then a.ty else b.ty
    else promote a.ty b.ty
  lit ty (if a.val < b.val then a.val else b.val)

/-- `base/int.jl:591-594`, `base/promotion.jl:525,676`: max wraps to the promoted type. -/
def max (a b : Num) : Num :=
  lit (promote a.ty b.ty) (if a.val < b.val then b.val else a.val)

/-- `base/int.jl:575-588`, `base/bool.jl:135-136`: exact mixed integer equality. -/
def eq (a b : Num) : Bool := decide (a.val = b.val)

/-- `base/int.jl:911-929`, `base/number.jl:327`: widened multiplication for BitInteger64 inputs. -/
def widemul64 (a b : Num) (ha : a.ty.bits ≤ 64) (hb : b.ty.bits ≤ 64) : Num :=
  if a.ty = .bool ∨ b.ty = .bool then mul a b
  else
    let aty := a.ty.widen64 ha
    let bty := b.ty.widen64 hb
    let ty := if a.ty.signed ≠ b.ty.signed then (promote aty bty).signedType
      else promote aty bty
    mul (lit ty a.val) (lit ty b.val)

theorem sub_one_bits_le64 (i : Num) (h : i.ty.bits ≤ 64) :
    (sub i (one i.ty)).ty.bits ≤ 64 := by
  rcases i with ⟨ty, v⟩
  cases ty with
  | bool => cases v <;> decide
  | bit t =>
      cases t <;> simp_all [sub, one, lit, promote, IntTy.promote, NType.bits, IntTy.bits]

end Num
end JuliaLean.Ranges
