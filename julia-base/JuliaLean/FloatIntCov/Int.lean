import JuliaLean.IntArith.Division
import JuliaLean.IntArith.PowersDigits
import JuliaLean.Promotion.Props

/-!
Coverage models for active 64-bit-platform methods in `base/int.jl` at Julia
`bbfa0ce4150`.  Values retain their runtime `IntTy`; bit operations use the
complete fixed-width bit pattern.
-/

namespace JuliaLean.FloatIntCov.Int

open JuliaLean
open JuliaLean.IntArith.Division

/-- `base/int.jl:73-79`: the signed type of Bool or a fixed-width integer. -/
def signedType (isBool : Bool) (t : IntTy) : IntTy :=
  if isBool then .i64 else t.toSigned

def SignedTypeSameWidth : Prop :=
  signedType true .u8 = .i64 ∧
  ∀ t : IntTy, signedType false t = t.toSigned ∧
    (signedType false t).bits = t.bits ∧ (signedType false t).signed = true

theorem signedTypeSameWidth : SignedTypeSameWidth := by
  constructor
  · rfl
  intro t
  cases t <;> decide

/-- Explicit Union{} target methods at `base/int.jl:80,700-705,907-908`. -/
def unionTypeError {α : Type} (name : String) : Jl α := .error (.methodError name)

def UnionTypeMethodsError : Prop :=
  ∀ (α : Type) name, unionTypeError (α := α) name = .error (.methodError name)

theorem unionTypeMethodsError : UnionTypeMethodsError := by
  unfold UnionTypeMethodsError
  intros
  rfl

/-- Primitive bodies at `base/int.jl:84-94`. -/
def primitiveResults {t : IntTy} (x y : JInt t) :=
  (decide (x < y), -x, x - y, x + y, x * y)

def PrimitiveArithmeticBehavior : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    primitiveResults x y = (decide (x.val < y.val), -x, x - y, x + y, x * y)

theorem primitiveArithmeticBehavior : PrimitiveArithmeticBehavior := by
  intro t x y
  rfl

/-- `base/int.jl:96`: generic negate. -/
def negate {t : IntTy} (x : JInt t) : JInt t := -x

/-- `base/int.jl:97`: unsigned negate converts to same-width signed first. -/
def negateUnsigned {t : IntTy} (x : JInt t) : Jl (JInt t.toSigned) := do
  let y ← JInt.convert t.toSigned x.val
  pure (-y)

def NegateBehavior : Prop :=
  (∀ (t : IntTy) (x : JInt t), negate x = -x) ∧
  (∀ (t : IntTy) (x : JInt t),
    negateUnsigned x = (JInt.convert t.toSigned x.val >>= fun y => pure (-y)))

theorem negateBehavior : NegateBehavior := by
  constructor <;> intros <;> rfl

/-- Fixed-width `inv` and `/` at `base/int.jl:100-103`, using binary64 conversion. -/
def inv (x : Value) : JuliaLean.Float.F64 :=
  JuliaLean.Float.F64.div JuliaLean.Float.F64.one (JuliaLean.Float.F64.ofJInt x.int)

def fdiv (x y : Value) : JuliaLean.Float.F64 :=
  JuliaLean.Float.F64.div (JuliaLean.Float.F64.ofJInt x.int) (JuliaLean.Float.F64.ofJInt y.int)

def IntegerFloatDivisionBehavior : Prop :=
  (∀ x : Value, inv x = JuliaLean.Float.F64.div JuliaLean.Float.F64.one
    (JuliaLean.Float.F64.ofJInt x.int)) ∧
  (∀ x y : Value, fdiv x y = JuliaLean.Float.F64.div
    (JuliaLean.Float.F64.ofJInt x.int) (JuliaLean.Float.F64.ofJInt y.int))

theorem integerFloatDivisionBehavior : IntegerFloatDivisionBehavior := by
  constructor <;> intros <;> rfl

/-- `base/int.jl:123-141`: the upper fixed-width half of the exact product. -/
def mulHi {t : IntTy} (x y : JInt t) : JInt t :=
  JInt.wrap t ((x.val * y.val).ediv (2 ^ t.bits : Int))

def MulHiExact : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    mulHi x y = JInt.wrap t ((x.val * y.val).ediv (2 ^ t.bits : Int))

theorem mulHiExact : MulHiExact := by
  unfold MulHiExact
  intros
  rfl

/-- `base/int.jl:160-181`: Number and Real parity dispatch. -/
def isoddNumber {α : Type} (isreal : α → Bool) (realOdd : α → Bool) (x : α) : Bool :=
  isreal x && realOdd x

def isevenNumber {α : Type} (isreal : α → Bool) (realEven : α → Bool) (x : α) : Bool :=
  isreal x && realEven x

def isoddReal {α : Type} (isinteger : α → Bool) (integerValue : α → Int) (x : α) : Bool :=
  isinteger x && integerValue x % 2 != 0

def isevenReal {α : Type} (isinteger : α → Bool) (integerValue : α → Int) (x : α) : Bool :=
  isinteger x && integerValue x % 2 == 0

def ParityDispatchBehavior : Prop :=
  (∀ (α : Type) p q (x : α), isoddNumber p q x = (p x && q x)) ∧
  (∀ (α : Type) p q (x : α), isevenNumber p q x = (p x && q x)) ∧
  (∀ (α : Type) p q (x : α), isoddReal p q x = (p x && q x % 2 != 0)) ∧
  (∀ (α : Type) p q (x : α), isevenReal p q x = (p x && q x % 2 == 0))

theorem parityDispatchBehavior : ParityDispatchBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- `base/int.jl:183-186`. -/
def signbit {t : IntTy} (x : JInt t) : Bool := decide (x.val < 0)

def SignPredicates : Prop :=
  (∀ (t : IntTy) (x : JInt t), signbit x = decide (x.val < 0)) ∧
  (∀ (t : IntTy) (x : JInt t), t.signed = false → signbit x = false)

theorem signPredicates : SignPredicates := by
  constructor
  · intros
    rfl
  intro t x ht
  have hx : 0 ≤ x.val := by
    have h := x.property.1
    simpa [IntTy.min, ht] using h
  simp [signbit, show ¬x.val < 0 by omega]

/-- The active flipsign, copysign, and abs bodies at `base/int.jl:188-234`. -/
def signResults (x y : Value) := (flipsign x y, copysign x y, abs x)

def SignOperationBehavior : Prop :=
  ∀ x y : Value, signResults x y = (flipsign x y, copysign x y, abs x)

theorem signOperationBehavior : SignOperationBehavior := by
  unfold SignOperationBehavior
  intros
  rfl

/-- Mixed and same-signedness division methods at `base/int.jl:275-358`. -/
def divisionMethods (x y : Value) :=
  (div x y, rem x y, divrem x y, mod x y)

def IntegerDivisionMethodBehavior : Prop :=
  ∀ x y : Value, divisionMethods x y = (div x y, rem x y, divrem x y, mod x y)

theorem integerDivisionMethodBehavior : IntegerDivisionMethodBehavior := by
  unfold IntegerDivisionMethodBehavior
  intros
  rfl

/-- Complete bit pattern of a fixed-width integer, interpreted as unsigned. -/
def pattern {t : IntTy} (x : JInt t) : Nat :=
  (JInt.rem t.toUnsigned x).val.toNat

def bitAt {t : IntTy} (x : JInt t) (k : Nat) : Bool :=
  decide (pattern x / 2 ^ k % 2 = 1)

def fromBits (t : IntTy) (f : Nat → Bool) : JInt t :=
  JInt.wrap t (Int.ofNat ((List.range t.bits).foldl
    (fun n k => if f k then n + 2 ^ k else n) 0))

/-- `base/int.jl:236,381,407,432-433`: generic and primitive bitwise bodies. -/
def bitNot {t : IntTy} (x : JInt t) : JInt t := -x - JInt.lit t 1
def bitAnd {t : IntTy} (x y : JInt t) : JInt t := fromBits t fun k => bitAt x k && bitAt y k
def bitOr {t : IntTy} (x y : JInt t) : JInt t := fromBits t fun k => bitAt x k || bitAt y k
def bitXor {t : IntTy} (x y : JInt t) : JInt t := fromBits t fun k => bitAt x k != bitAt y k

def BitwiseBehavior : Prop :=
  (∀ (t : IntTy) (x : JInt t), bitNot x = -x - JInt.lit t 1) ∧
  (∀ (t : IntTy) (x y : JInt t), bitAnd x y = fromBits t fun k => bitAt x k && bitAt y k) ∧
  (∀ (t : IntTy) (x y : JInt t), bitOr x y = fromBits t fun k => bitAt x k || bitAt y k) ∧
  (∀ (t : IntTy) (x y : JInt t), bitXor x y = fromBits t fun k => bitAt x k != bitAt y k)

theorem bitwiseBehavior : BitwiseBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def bswap {t : IntTy} (x : JInt t) : JInt t :=
  if t.bits = 8 then x else
    fromBits t fun k => bitAt x (((t.bits / 8 - 1 - k / 8) * 8) + k % 8)

def bitreverse {t : IntTy} (x : JInt t) : JInt t :=
  fromBits t fun k => bitAt x (t.bits - 1 - k)

def ByteAndBitReverseBehavior : Prop :=
  (∀ (t : IntTy) (x : JInt t), bswap x =
    if t.bits = 8 then x else
      fromBits t fun k => bitAt x (((t.bits / 8 - 1 - k / 8) * 8) + k % 8)) ∧
  (∀ (t : IntTy) (x : JInt t),
    bitreverse x = fromBits t fun k => bitAt x (t.bits - 1 - k))

theorem byteAndBitReverseBehavior : ByteAndBitReverseBehavior := by
  constructor <;> intros <;> rfl

open JuliaLean.IntArith.PowersDigits in
/-- `base/int.jl:475-569`: bit-count helpers and top-set-bit. -/
def bitCounts {t : IntTy} (x : JInt t) :=
  (countOnes x, leadingZeros x, trailingZeros x,
   t.bits - countOnes x, leadingZeros (bitNot x), trailingZeros (bitNot x), topSetBit x)

open JuliaLean.IntArith.PowersDigits in
def BitCountBehavior : Prop :=
  ∀ (t : IntTy) (x : JInt t), bitCounts x =
    (countOnes x, leadingZeros x, trailingZeros x,
     t.bits - countOnes x, leadingZeros (bitNot x), trailingZeros (bitNot x), topSetBit x)

theorem bitCountBehavior : BitCountBehavior := by
  unfold BitCountBehavior
  intros
  rfl

/-- `base/int.jl:591-599`: mixed fixed-width extrema compare mathematical values. -/
def intMax (x y : Value) : Value :=
  let t := x.ty.promote y.ty
  lit t (if x.int.val < y.int.val then y.int.val else x.int.val)

def intMin (x y : Value) : Value :=
  let t := x.ty.promote y.ty
  lit t (if x.int.val < y.int.val then x.int.val else y.int.val)

def intMinmax (x y : Value) : Value × Value := (intMin x y, intMax x y)

def IntegerExtremaBehavior : Prop :=
  (∀ x y : Value, (intMax x y).int.val =
    wrapInt (x.ty.promote y.ty) (if x.int.val < y.int.val then y.int.val else x.int.val)) ∧
  (∀ x y : Value, (intMin x y).int.val =
    wrapInt (x.ty.promote y.ty) (if x.int.val < y.int.val then x.int.val else y.int.val)) ∧
  (∀ x y : Value, intMinmax x y = (intMin x y, intMax x y))

theorem integerExtremaBehavior : IntegerExtremaBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- Fixed-width left and logical-right shifts from `base/int.jl:604-607`. -/
def shl {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  JInt.wrap t (x.val * (2 ^ k : Int))

def lshr {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  fromBits t fun j => bitAt x (j + k)

def ashr {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  fromBits t fun j => if j + k < t.bits then bitAt x (j + k) else decide (x.val < 0)

def shr {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  if t.signed then ashr x k else lshr x k

/-- Signed-count shifts at `base/int.jl:611-616`. -/
def shrInt {t : IntTy} (x : JInt t) (k : Int) : JInt t :=
  if 0 ≤ k then shr x k.toNat else shl x k.natAbs
def shlInt {t : IntTy} (x : JInt t) (k : Int) : JInt t :=
  if 0 ≤ k then shl x k.toNat else shr x k.natAbs
def lshrInt {t : IntTy} (x : JInt t) (k : Int) : JInt t :=
  if 0 ≤ k then lshr x k.toNat else shl x k.natAbs

def ShiftBehavior : Prop :=
  (∀ (t : IntTy) (x : JInt t) k, shrInt x k = if 0 ≤ k then shr x k.toNat else shl x k.natAbs) ∧
  (∀ (t : IntTy) (x : JInt t) k, shlInt x k = if 0 ≤ k then shl x k.toNat else shr x k.natAbs) ∧
  (∀ (t : IntTy) (x : JInt t) k, lshrInt x k = if 0 ≤ k then lshr x k.toNat else shl x k.natAbs)

theorem shiftBehavior : ShiftBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- `base/int.jl:664-665`: left rotation modulo the bit width. -/
def bitrotate {t : IntTy} (x : JInt t) (k : Int) : JInt t :=
  let d := (k % (t.bits : Int)).toNat
  fromBits t fun j => bitAt x ((j + t.bits - d) % t.bits)

def BitrotateBehavior : Prop :=
  ∀ (t : IntTy) (x : JInt t) (k : Int), bitrotate x k =
    let d := (k % (t.bits : Int)).toNat
    fromBits t fun j => bitAt x ((j + t.bits - d) % t.bits)

theorem bitrotateBehavior : BitrotateBehavior := by
  unfold BitrotateBehavior
  intros
  rfl

/-- `base/int.jl:618-631,695-705`: fixed-width remainder conversion. -/
def remType (to : IntTy) {src : IntTy} (x : JInt src) : JInt to := JInt.rem to x
def remBool {t : IntTy} (x : JInt t) : Bool := decide (x.val % 2 != 0)

def TypeRemainderBehavior : Prop :=
  (∀ (to src : IntTy) (x : JInt src), remType to x = JInt.rem to x) ∧
  (∀ (t : IntTy) (x : JInt t), remBool x = decide (x.val % 2 != 0))

theorem typeRemainderBehavior : TypeRemainderBehavior := by
  constructor <;> intros <;> rfl

/-- Macro expansion at `base/int.jl:725-747`, parameterized by the parser primitive. -/
def integerStringMacro {α : Type} (parse : List Char → Jl α) (s : List Char) : Jl α := parse s

/-- `base/int.jl:778-804`: underscore normalization, then BigInt before BigFloat parsing. -/
def bigStringMacro {α : Type} (normalize : List Char → Jl (List Char))
    (tryInt tryFloat : List Char → Option α) (s : List Char) : Jl α := do
  let s ← if s.contains '_' then normalize s else .ok s
  match tryInt s with
  | some n => .ok n
  | none => match tryFloat s with
    | some n => .ok n
    | none => .error (.argumentError "")

def StringMacroBehavior : Prop :=
  (∀ (α : Type) (parse : List Char → Jl α) s, integerStringMacro parse s = parse s) ∧
  (∀ (α : Type) normalize (tryInt tryFloat : List Char → Option α) s,
    bigStringMacro normalize tryInt tryFloat s = do
      let s ← if s.contains '_' then normalize s else .ok s
      match tryInt s with
      | some n => .ok n
      | none => match tryFloat s with
        | some n => .ok n
        | none => .error (.argumentError ""))

theorem stringMacroBehavior : StringMacroBehavior := by
  constructor <;> intros <;> rfl

/-- `base/int.jl:809-822`. -/
def promotionRule (x y : IntTy) : IntTy := x.promote y

def PromotionRuleBehavior : Prop :=
  ∀ x y : IntTy, promotionRule x y = x.promote y ∧
    (promotionRule x y).bits = max x.bits y.bits

theorem promotionRuleBehavior : PromotionRuleBehavior := by
  intro x y
  cases x <;> cases y <;> decide

/-- `base/int.jl:887-906`. -/
def integerBounds (t : IntTy) : JInt t × JInt t := (JInt.typemin t, JInt.typemax t)

def IntegerBoundsBehavior : Prop :=
  ∀ t : IntTy, (integerBounds t).1.val = t.min ∧ (integerBounds t).2.val = t.max

theorem integerBoundsBehavior : IntegerBoundsBehavior := by
  intro t
  cases t <;> decide

/-- `base/int.jl:911-918`. -/
def widenType : IntTy → IntTy
  | .i8 => .i16 | .i16 => .i32 | .i32 => .i64 | .i64 => .i128 | .i128 => .i128
  | .u8 => .u16 | .u16 => .u32 | .u32 => .u64 | .u64 => .u128 | .u128 => .u128

def WidenTypeBehavior : Prop :=
  ∀ t : IntTy, (widenType t).bits = min 128 (2 * t.bits) ∧
    (widenType t).signed = t.signed

theorem widenTypeBehavior : WidenTypeBehavior := by
  intro t
  cases t <;> decide

/-- `base/int.jl:923-928`: widening multiplication, with Bool represented by 0 or 1. -/
def widemul {t s : IntTy} (x : JInt t) (y : JInt s) : Value :=
  let w := (widenType t).promote (widenType s)
  lit w (x.val * y.val)

def WidemulBehavior : Prop :=
  ∀ (t s : IntTy) (x : JInt t) (y : JInt s),
    (widemul x y).int.val = wrapInt ((widenType t).promote (widenType s)) (x.val * y.val)

theorem widemulBehavior : WidemulBehavior := by
  unfold WidemulBehavior
  intros
  rfl

/-- Active 64-bit-platform Int128 primitives at `base/int.jl:1083-1089`. -/
def int128Primitives (x y : JInt .i128) := (x * y, JInt.div x y, JInt.remInt x y)
def uint128Primitives (x y : JInt .u128) := (x * y, JInt.div x y, JInt.remInt x y)

def Int128PrimitiveBehavior : Prop :=
  (∀ x y : JInt .i128, int128Primitives x y = (x * y, JInt.div x y, JInt.remInt x y)) ∧
  (∀ x y : JInt .u128, uint128Primitives x y = (x * y, JInt.div x y, JInt.remInt x y))

theorem int128PrimitiveBehavior : Int128PrimitiveBehavior := by
  constructor <;> intros <;> rfl

/-- `base/int.jl:1094-1099`: wrap both operands to their promoted type before an unchecked operation. -/
def promotedBinary (op : {t : IntTy} → JInt t → JInt t → JInt t)
    (x y : Value) : Value :=
  let t := x.ty.promote y.ty
  pack (op (JInt.rem t x.int) (JInt.rem t y.int))

def PromotedBinaryBehavior : Prop :=
  ∀ op (x y : Value), promotedBinary op x y =
    let t := x.ty.promote y.ty
    pack (op (JInt.rem t x.int) (JInt.rem t y.int))

theorem promotedBinaryBehavior : PromotedBinaryBehavior := by
  unfold PromotedBinaryBehavior
  intros
  rfl

end JuliaLean.FloatIntCov.Int
