import JuliaLean.Core
import JuliaLean.Promotion.IEEE

/-!
# Miscellaneous numeric and Base models

Models for selected branches of `base/parsers/floats.jl`, `base/irrationals.jl`,
`base/fastmath.jl`, `base/special/hyperbolic.jl`, `base/views.jl`,
`base/pointer.jl`, and `base/refpointer.jl` at master `bbfa0ce4150`.
-/

namespace JuliaLean.NumMisc

/-! ## Float NaN payload grammar -/

abbrev Byte := Nat

def asciiLower (b : Byte) : Byte := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- `isnanchar`, `base/parsers/floats.jl:319-321`. -/
def isNanChar (b : Byte) : Bool :=
  (48 ≤ b && b ≤ 57) || (97 ≤ asciiLower b && asciiLower b ≤ 122) || b == 95

def digitValue (b : Byte) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then some (b - 48)
  else
    let b := asciiLower b
    if 97 ≤ b ∧ b ≤ 102 then some (b - 87) else none

def validDigits (base : Nat) (s : List Byte) : Bool :=
  !s.isEmpty && s.all fun b => (digitValue b).any (· < base)

/-- The numeric payload grammar documented at `base/parsers/Parsers.jl:66-71`. -/
def documentedNanPayload : List Byte → Bool
  | 48 :: x :: xs =>
      if asciiLower x == 120 then validDigits 16 xs
      else validDigits 8 (48 :: x :: xs)
  | s => validDigits 10 s

/-- `nanpayload`, `base/parsers/floats.jl:326-343`, at the acceptance level.
Allowed characters make the call succeed; a failed integer parse supplies payload zero. -/
def sourceNanPayload (s : List Byte) : Option Nat :=
  if s.all isNanChar then some (if documentedNanPayload s then 1 else 0) else none

/-- NaN payload acceptance agrees with the documented unsigned-integer grammar. -/
def FloatGrammarExact : Prop :=
  ∀ s : List Byte, (sourceNanPayload s).isSome = documentedNanPayload s

/-- `fromdecimal(T, w, 0, neg)`, `base/parsers/floats.jl:143-151`, for nonnegative
integers exactly representable in binary64. The model records the exact integer value. -/
def fromDecimalInteger (w : Nat) : Option Nat :=
  if w ≤ 2^53 then some w else none

/-- Every nonnegative integer through `2^53` takes the exact fast path and is unchanged. -/
def FloatExactIntegerRounding : Prop :=
  ∀ w : Nat, w ≤ 2^53 → fromDecimalInteger w = some w

/-! ## AbstractIrrational conversion -/

inductive RoundMode where
  | nearest | down | up | toZero
  deriving DecidableEq, Repr

inductive Side where
  | below | equal | above
  deriving DecidableEq, Repr

/-- An exact positive irrational close to 1. `separationBits = p` means its
distance from 1 is below the resolution of a `p`-bit intermediate. -/
structure IrrationalNearOne where
  side : Side
  separationBits : Nat
  deriving DecidableEq, Repr

inductive UnitFloat where
  | prev | one | next
  deriving DecidableEq, Repr

def roundNearOne : Side → RoundMode → UnitFloat
  | .equal, _ => .one
  | .above, .up => .next
  | .above, _ => .one
  | .below, .down => .prev
  | .below, .toZero => .prev
  | .below, _ => .one

/-- `BigFloat(x)` inside a 256-bit precision scope, `base/irrationals.jl:101-104`.
Values closer than that resolution collapse to exactly 1. -/
def bigAt256 (x : IrrationalNearOne) : Side :=
  if x.separationBits > 256 then .equal else x.side

def sourceIrrationalConvert (x : IrrationalNearOne) (r : RoundMode) : UnitFloat :=
  roundNearOne (bigAt256 x) r

def exactIrrationalConvert (x : IrrationalNearOne) (r : RoundMode) : UnitFloat :=
  roundNearOne x.side r

/-- The generic rounding-mode conversion returns the requested rounding of the exact value. -/
def IrrationalRoundingCorrect : Prop :=
  ∀ x : IrrationalNearOne, ∀ r : RoundMode,
    sourceIrrationalConvert x r = exactIrrationalConvert x r

/-- The fixed intermediate is sufficient when it can still distinguish the side of 1. -/
def IrrationalSeparatedRoundingCorrect : Prop :=
  ∀ x : IrrationalNearOne, x.separationBits ≤ 256 → ∀ r : RoundMode,
    sourceIrrationalConvert x r = exactIrrationalConvert x r

/-! ## FastMath method coverage -/

/-- `hypot(x::Number)` and `hypot(x::Number, y::Number, xs::Number...)`,
`base/math.jl:729-731`. -/
def hypotSupportsArity (n : Nat) : Bool := n ≥ 1

/-- The only direct `hypot_fast` implementation takes two arguments,
`base/fastmath.jl:327`; the fallback loops at lines 371-395 add no other arity. -/
def hypotFastSupportsArity (n : Nat) : Bool := n == 2

/-- Rewriting `hypot` under `@fastmath` preserves every supported public arity. -/
def FastMathCoverage : Prop :=
  ∀ n : Nat, hypotSupportsArity n = true → hypotFastSupportsArity n = true

/-! ## Hyperbolic special values and symmetries -/

abbrev NF32 := JuliaLean.Promotion.Fl JuliaLean.Promotion.single

def nf32 (bits : Nat) : NF32 := JuliaLean.Promotion.Fl.ofBits bits

/-- One correctly rounded Float32 multiplication, as used by `x*x` and the final
`x*tanh_kernel(x*x)` in `base/special/hyperbolic.jl:174`. -/
def nf32Mul (x y : NF32) : NF32 :=
  if x.isfinite && y.isfinite then
    let a := x.toRat
    let b := y.toRat
    JuliaLean.Promotion.Fl.roundRat (a.1 * b.1) (a.2 * b.2) (x.signbit != y.signbit)
  else JuliaLean.Promotion.Fl.nan

/-- Float32 `muladd(x,y,z)` for the generated Horner form of `evalpoly`,
`base/math.jl:75-82`. -/
def nf32Fma (x y z : NF32) : NF32 :=
  if x.isfinite && y.isfinite && z.isfinite then
    let a := x.toRat
    let b := y.toRat
    let c := z.toRat
    let abDen := a.2 * b.2
    JuliaLean.Promotion.Fl.roundRat
      (a.1 * b.1 * (c.2 : Int) + c.1 * (abDen : Int))
      (abDen * c.2) false
  else JuliaLean.Promotion.Fl.nan

def nf32Horner (x : NF32) : List NF32 → NF32
  | [] => JuliaLean.Promotion.Fl.zero
  | [c] => c
  | c :: cs => nf32Fma x (nf32Horner x cs) c

/-- The Float32 coefficients at `base/special/hyperbolic.jl:157-159`. -/
def tanhCoefficients32 : List NF32 :=
  [nf32 0x3f800000, nf32 0xbeaaaa63, nf32 0x3e087aa6,
   nf32 0xbd5b2657, nf32 0x3ca3a310, nf32 0xbba58fa2]

/-- The small Float32 branch at `base/special/hyperbolic.jl:174`. -/
def tanhSmall32 (x : NF32) : NF32 :=
  nf32Mul x (nf32Horner (nf32Mul x x) tanhCoefficients32)

def takesTanhSmall32 (x : NF32) : Bool :=
  x.isfinite && !x.signbit &&
    JuliaLean.Promotion.Fl.le (JuliaLean.Promotion.Fl.add x x) (nf32 0x3fb17218)

/-- The Float32 small branch of tanh is nondecreasing on ordered nonnegative inputs. -/
def TanhMonotone : Prop :=
  ∀ x y : NF32,
    takesTanhSmall32 x = true → takesTanhSmall32 y = true →
    JuliaLean.Promotion.Fl.le x y = true →
    JuliaLean.Promotion.Fl.le (tanhSmall32 x) (tanhSmall32 y) = true

inductive HVal where
  | negInf | negFinite | negZero | posZero | posFinite | posInf | nan
  deriving DecidableEq, Repr

def HVal.neg : HVal → HVal
  | .negInf => .posInf
  | .negFinite => .posFinite
  | .negZero => .posZero
  | .posZero => .negZero
  | .posFinite => .negFinite
  | .posInf => .negInf
  | .nan => .nan

/-- Sign and special-value branches of `sinh`, `base/special/hyperbolic.jl:58-80`. -/
def hsinh : HVal → HVal
  | .negInf => .negInf
  | .posInf => .posInf
  | .negZero => .negZero
  | .posZero => .posZero
  | .negFinite => .negFinite
  | .posFinite => .posFinite
  | .nan => .nan

/-- Sign and special-value branches of `cosh`, lines 103-125. -/
def hcosh : HVal → HVal
  | .negInf | .posInf => .posInf
  | .negZero | .posZero => .posFinite
  | .negFinite | .posFinite => .posFinite
  | .nan => .nan

/-- Sign and special-value branches of `tanh`, lines 161-177. -/
def htanh : HVal → HVal
  | .negInf => .negFinite
  | .posInf => .posFinite
  | .negZero => .negZero
  | .posZero => .posZero
  | .negFinite => .negFinite
  | .posFinite => .posFinite
  | .nan => .nan

/-- Sign and special-value branches of `asinh`, lines 183-219. -/
def hasinh : HVal → HVal
  | .negInf => .negInf
  | .posInf => .posInf
  | .negZero => .negZero
  | .posZero => .posZero
  | .negFinite => .negFinite
  | .posFinite => .posFinite
  | .nan => .nan

/-- Exact odd/even symmetries for every modelled class. -/
def HyperbolicSymmetry : Prop :=
  ∀ x : HVal,
    hsinh x.neg = (hsinh x).neg ∧
    hcosh x.neg = hcosh x ∧
    htanh x.neg = (htanh x).neg ∧
    hasinh x.neg = (hasinh x).neg

inductive InvSpecial where
  | negInf | negOne | negZero | posZero | posOne | posInf | nan
  deriving DecidableEq, Repr

inductive InvResult where
  | negInf | negZero | posZero | posInf | nan | domainError
  deriving DecidableEq, Repr

def InvResult.neg : InvResult → InvResult
  | .negInf => .posInf
  | .negZero => .posZero
  | .posZero => .negZero
  | .posInf => .negInf
  | .nan => .nan
  | .domainError => .domainError

def InvSpecial.neg : InvSpecial → InvSpecial
  | .negInf => .posInf
  | .negOne => .posOne
  | .negZero => .posZero
  | .posZero => .negZero
  | .posOne => .negOne
  | .posInf => .negInf
  | .nan => .nan

/-- `atanh` special branches, `base/special/hyperbolic.jl:259-286`. -/
def hatanh : InvSpecial → InvResult
  | .negInf | .posInf => .domainError
  | .negOne => .negInf
  | .posOne => .posInf
  | .negZero => .negZero
  | .posZero => .posZero
  | .nan => .nan

/-- `acosh` special branches, `base/special/hyperbolic.jl:221-257`. -/
def hacosh : InvSpecial → InvResult
  | .negInf | .negOne | .negZero | .posZero => .domainError
  | .posOne => .posZero
  | .posInf => .posInf
  | .nan => .nan

def HyperbolicSpecialValues : Prop :=
  ∀ x : InvSpecial,
    hatanh x.neg = (hatanh x).neg ∧
    (x = .posOne → hacosh x = .posZero) ∧
    (x = .posInf → hacosh x = .posInf) ∧
    (x = .nan → hacosh x = .nan)

/-! ## `@views` rewriting -/

inductive ViewFn where
  | maybeview | getindex | other
  deriving DecidableEq, Repr

inductive ViewExpr where
  | atom (id : Nat)
  | ref (array : ViewExpr) (indices : List ViewExpr)
  | call (fn : ViewFn) (args : List ViewExpr)
  | assign (lhs rhs : ViewExpr)
  | block (items : List ViewExpr)

/-- `_views`, `base/views.jl:247-294`, for references, plain assignment, calls,
blocks, and leaves. -/
def rewriteViews : ViewExpr → ViewExpr
  | .atom id => .atom id
  | .ref a is => .call .maybeview (rewriteViews a :: is.map rewriteViews)
  | .call fn args => .call fn (args.map rewriteViews)
  | .assign (.ref a is) rhs =>
      .assign (.ref (rewriteViews a) (is.map rewriteViews)) (rewriteViews rhs)
  | .assign lhs rhs => .assign (rewriteViews lhs) (rewriteViews rhs)
  | .block items => .block (items.map rewriteViews)

def ViewsDocumentedRewrite : Prop :=
  (∀ a is, rewriteViews (.ref a is) =
      .call .maybeview (rewriteViews a :: is.map rewriteViews)) ∧
  (∀ args, ∃ args', rewriteViews (.call .getindex args) = .call .getindex args') ∧
  (∀ a is rhs, rewriteViews (.assign (.ref a is) rhs) =
      .assign (.ref (rewriteViews a) (is.map rewriteViews)) (rewriteViews rhs)) ∧
  (∀ id, rewriteViews (.atom id) = .atom id)

/-! ## Pointer arithmetic and Ref construction -/

abbrev Ptr64 := JInt .u64

/-- `+(::Ptr, ::Integer)`, `base/pointer.jl:315`. -/
def ptrAdd (p : Ptr64) (offset : Int) : Ptr64 := JInt.wrap .u64 (p.val + offset)

/-- `-(::Ptr, ::Integer)`, `base/pointer.jl:316`. -/
def ptrSub (p : Ptr64) (offset : Int) : Ptr64 := JInt.wrap .u64 (p.val - offset)

/-- `Ref(x::Ptr{T}, i)`, `base/refpointer.jl:150`. -/
def refPointer (p : Ptr64) (elementBytes index : Int) : Ptr64 :=
  ptrAdd p ((index - 1) * elementBytes)

/-- `RefArray` construction defers the array bounds check until `getindex`,
`base/refpointer.jl:116-125,193`. The returned natural is the zero-based slot. -/
def derefArray (len : Nat) (index : Int) : Jl Nat :=
  if 1 ≤ index ∧ index ≤ len then .ok (index - 1).toNat else .error .boundsError

/-- `cconvert(Ref{T}, t::NTuple{N,T})`, `base/refpointer.jl:182`: the rooted Ref
contains the whole tuple. -/
def tupleRef {α : Type} (xs : List α) : List α := xs

def PointerRefSemantics : Prop :=
  (∀ p : Ptr64, ∀ offset : Int,
      (ptrAdd p offset).val = wrapInt .u64 (p.val + offset) ∧
      (ptrSub p offset).val = wrapInt .u64 (p.val - offset)) ∧
  (∀ p : Ptr64, ∀ elementBytes index : Int,
      refPointer p elementBytes index = ptrAdd p ((index - 1) * elementBytes)) ∧
  (∀ len index slot, derefArray len index = .ok slot ↔
      1 ≤ index ∧ index ≤ len ∧ slot = (index - 1).toNat) ∧
  (∀ xs : List Nat, tupleRef xs = xs)

end JuliaLean.NumMisc
