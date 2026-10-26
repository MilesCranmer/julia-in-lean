import JuliaLean.IntArith.NumberTheory
import JuliaLean.IntArith.Rational
import JuliaLean.IntFuncsCov.Common

/-!
Coverage of the `gcd`, `lcm`, `gcdx`, `invmod` methods of `base/intfuncs.jl:44-382`
(master `bbfa0ce4150`). The BitInteger algorithms are the `IntArith.NumberTheory` models
(`gcd` with `binaryGcd`/`absdiff`, `lcm`, `gcdxVal`, `mixedGcd`, `mixedLcm`,
`mixedGcdx`, `promoteMixedSigns`, `invmod`, `bezoutCoef`, `invmodRing`); this file adds
the remaining dispatch methods and states their documented contracts.

The computational regression properties use compact byte grids. Registry coverage uses
the universal source models below, rather than these regression grids.
-/

namespace JuliaLean.IntFuncsCov.Gcd

open JuliaLean JuliaLean.IntArith.NumberTheory JuliaLean.IntFuncsCov

/-! ### Generic `gcd` loop -/

/-- `gcd(a::T, b::T) where T<:Integer`, `base/intfuncs.jl:44-51`, for the integer types
without the BitInteger method (`BigInt`): Euclid's loop with the exact truncating `rem`,
then `checked_abs`, which cannot overflow for an unbounded type. -/
def gcdGeneric (a b : Int) : Int :=
  if _h : b = 0 then (a.natAbs : Int) else gcdGeneric b (a.tmod b)
termination_by b.natAbs
decreasing_by
  simpa only [Int.natAbs_tmod] using Nat.mod_lt a.natAbs (by omega : 0 < b.natAbs)

/-- The generic loop returns the greatest common divisor of its arguments, zero only for
`gcd(0, 0)`. -/
def GcdGenericEuclid : Prop := ∀ a b : Int, gcdGeneric a b = (Nat.gcd a.natAbs b.natAbs : Int)

theorem gcdGeneric_eq (n : Nat) : ∀ a b : Int, b.natAbs ≤ n →
    gcdGeneric a b = (Nat.gcd a.natAbs b.natAbs : Int) := by
  induction n with
  | zero =>
    intro a b hb
    have h0 : b = 0 := by omega
    subst h0
    rw [gcdGeneric]
    simp
  | succ n ih =>
    intro a b hb
    by_cases h0 : b = 0
    · subst h0
      rw [gcdGeneric]
      simp
    · rw [gcdGeneric, dif_neg h0, ih]
      · rw [Int.natAbs_tmod, Nat.gcd_comm b.natAbs (a.natAbs % b.natAbs), ← Nat.gcd_rec,
          Nat.gcd_comm]
      · rw [Int.natAbs_tmod]
        have := Nat.mod_lt a.natAbs (by omega : 0 < b.natAbs)
        omega

theorem gcdGenericEuclid : GcdGenericEuclid := fun a b => gcdGeneric_eq _ a b (Nat.le_refl _)

/-! ### BitInteger `gcd`, `lcm`, `gcdx` -/

/-- The documented gcd of `a` and `b` in type `t`, or the `OverflowError` the checked
absolute value raises when it is not representable. -/
def gcdSpec (t : IntTy) (a b : Int) : Jl Int :=
  let g : Int := Nat.gcd a.natAbs b.natAbs
  if g ≤ t.max then .ok g else .error (.overflowError "")

/-- The documented lcm of `a` and `b` in type `t`, or `OverflowError`. -/
def lcmSpec (t : IntTy) (a b : Int) : Jl Int :=
  let l : Int := Nat.lcm a.natAbs b.natAbs
  if l ≤ t.max then .ok l else .error (.overflowError "")

/-- `gcd(a, b)` for same-type BitIntegers (`base/intfuncs.jl:53-66`, Stein's algorithm
`_gcd` at `:80-95` with `absdiff` at `:68-75`, and `__throw_gcd_overflow`) is the greatest
common divisor, and throws `OverflowError` exactly when that is not representable (only
`gcd(typemin, typemin)` and `gcd(typemin, 0)`); `lcm(a, b)` (`:136-144`) is the least common
multiple, or `OverflowError` when it does not fit. -/
def GcdLcmBitInteger : Prop := ∀ (s : Bool) (a : Fin 16) (k : Fin 16),
  let t := byteTy s
  let x := JInt.lit t a.val
  let y := JInt.lit t (edge k)
  okVal (gcd x y) = gcdSpec t x.val y.val ∧ okVal (gcd y x) = gcdSpec t y.val x.val ∧
  okVal (lcm x y) = lcmSpec t x.val y.val ∧ okVal (lcm y x) = lcmSpec t y.val x.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdLcmBitInteger : GcdLcmBitInteger := by
  unfold GcdLcmBitInteger; decide +kernel

/-- `absdiff(x, y)`, `base/intfuncs.jl:68-75`: for unsigned types both results are the
distance `|x - y|`; for signed types they are `abs(x - y)` and `x - y` whenever the
difference and its negation are representable. -/
def AbsdiffDistance : Prop :=
  (∀ (t : IntTy) (x y : JInt t), t.signed = false →
    (absdiff x y).1.val = (if x.val ≤ y.val then y.val - x.val else x.val - y.val) ∧
    (absdiff x y).2 = (absdiff x y).1) ∧
  (∀ (t : IntTy) (x y : JInt t), t.signed = true →
    t.min ≤ x.val - y.val → x.val - y.val ≤ t.max → t.min ≤ y.val - x.val → y.val - x.val ≤ t.max →
    (absdiff x y).1.val = (if x.val ≤ y.val then y.val - x.val else x.val - y.val) ∧
    (absdiff x y).2.val = x.val - y.val)

theorem absdiffDistance : AbsdiffDistance := by
  refine ⟨?_, ?_⟩
  · intro t x y ht
    have hx := x.property
    have hy := y.property
    have h0 : t.min = 0 := by simp [IntTy.min, ht]
    simp only [absdiff, ht, Bool.false_eq_true, if_false]
    refine ⟨?_, by first | rfl | trivial⟩
    by_cases hxy : x.val ≤ y.val
    · have hle : x ≤ y := hxy
      rw [if_pos hle, if_pos hxy]
      exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
    · have hle : ¬ x ≤ y := hxy
      rw [if_neg hle, if_neg hxy]
      exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
  · intro t x y ht h1 h2 h3 h4
    simp only [absdiff, ht, if_true]
    have hd : (x - y).val = x.val - y.val := wrapInt_of_inRange t _ ⟨h1, h2⟩
    refine ⟨?_, hd⟩
    unfold abs
    by_cases hneg : (x - y).val < 0
    · rw [if_pos hneg]
      have hn : (-(x - y)).val = -(x - y).val := by
        show wrapInt t (-(x - y).val) = _
        rw [hd]
        exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
      rw [hn, hd]
      rw [hd] at hneg
      rw [if_pos (by omega)]
      omega
    · rw [if_neg hneg, hd]
      rw [hd] at hneg
      by_cases hxy : x.val ≤ y.val
      · rw [if_pos hxy]; omega
      · rw [if_neg hxy]

/-- `_gcdx_update(s0, q, s1)`, `base/intfuncs.jl:189-190`, is the wrapping `s0 - q*s1` that
the extended Euclidean loop (`gcdxLoop`) applies to both coefficient pairs. -/
def GcdxUpdateWraps : Prop := ∀ (t : IntTy) (s0 q s1 : JInt t),
  (gcdxUpdate s0 q s1).val = sub (some t) s0.val (mul (some t) q.val s1.val) ∧
  (gcdxUpdate s0 q s1).val = wrapInt t (s0.val - wrapInt t (q.val * s1.val))

theorem gcdxUpdateWraps : GcdxUpdateWraps := by
  intro t s0 q s1
  have e0 : wrapInt t s0.val = s0.val := wrapInt_of_inRange t _ s0.property
  have e1 : wrapInt t q.val = q.val := wrapInt_of_inRange t _ q.property
  have e2 : wrapInt t s1.val = s1.val := wrapInt_of_inRange t _ s1.property
  have e3 : wrapInt t (wrapInt t (q.val * s1.val)) = wrapInt t (q.val * s1.val) :=
    wrapInt_of_inRange t _ (wrapInt_bounds t _)
  refine ⟨?_, rfl⟩
  show wrapInt t (s0.val - wrapInt t (q.val * s1.val)) =
    wrapInt t (wrapInt t s0.val - wrapInt t (wrapInt t (wrapInt t q.val * wrapInt t s1.val)))
  rw [e0, e1, e2, e3]

/-- The Bézout identity of `gcdx(a, b)` (`base/intfuncs.jl:235-260`): it returns
`d = gcd(a, b)` and `u*a + v*b == d`, exactly for signed types and in the modular
arithmetic of the type for unsigned ones ("the identity then holds only via the unsigned
integers' modulo arithmetic"); it throws only when `gcd(a, b)` is not representable. -/
def GcdxBezout : Prop := ∀ (s : Bool) (a : Fin 16) (k : Fin 16) (swap : Bool),
  let t := byteTy s
  let x := JInt.lit t (if swap then edge k else a.val)
  let y := JInt.lit t (if swap then a.val else edge k)
  okSat (gcdx x y)
    (fun r => decide (okVal (.ok r.1 : Jl (JInt t)) = gcdSpec t x.val y.val) &&
      (if s then decide (r.2.1.val * x.val + r.2.2.val * y.val = r.1.val)
       else decide (r.2.1 * x + r.2.2 * y = r.1)))
    (fun _ => decide ((Nat.gcd x.val.natAbs y.val.natAbs : Int) > t.max)) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdxBezout : GcdxBezout := by
  unfold GcdxBezout; decide +kernel

/-! ### Unary and rational methods -/

/-- `gcd(a::Integer) = checked_abs(a)` (`base/intfuncs.jl:152`), `lcm(a::Integer) = gcd(a)`
(`:154`), and `gcdx(a::Real) = (gcd(a), signbit(a) ? -one(a) : one(a))` (`:263`): for every
width, `gcd(a) == lcm(a) == abs(a)` when representable and `OverflowError` otherwise; `gcdx`
returns that value with a coefficient `u` such that `u*a == gcd(a)`. -/
def UnaryGcdLcm : Prop :=
  (∀ (t : IntTy) (a : JInt t),
    IntArith.Checked.ExactOrOverflow (gcdUnary a) (if a.val < 0 then -a.val else a.val) ∧
    IntArith.Checked.ExactOrOverflow (lcmUnary a) (if a.val < 0 then -a.val else a.val)) ∧
  (∀ (s : Bool) (n : Fin 256),
    let t := byteTy s
    let a := JInt.lit t n.val
    okSat (gcdxUnary a)
      (fun r => decide (r.1.val = a.val.natAbs) && decide (r.2.val * a.val = r.1.val))
      (fun e => decide (e = .overflowError "") && decide (a.val = t.min) && t.signed) = true)

set_option maxRecDepth 100000 in
theorem unaryGcdLcm : UnaryGcdLcm := by
  refine ⟨fun t a => ⟨IntArith.Checked.absExact t a, IntArith.Checked.absExact t a⟩, ?_⟩
  decide +kernel

/-- `gcd(a::Rational) = checked_abs(a.num) // a.den`, `base/intfuncs.jl:153`. -/
def gcdRational {t : IntTy} (x : IntArith.Rational.Rat t) : Jl (IntArith.Rational.Rat t) := do
  let n ← checkedAbs x.num
  IntArith.Rational.ofInts n x.den

/-- `lcm(a::Rational) = gcd(a)`, `base/intfuncs.jl:154`. -/
def lcmRational {t : IntTy} (x : IntArith.Rational.Rat t) : Jl (IntArith.Rational.Rat t) :=
  gcdRational x

/-- For every normalized `Rational{Int8}` value `x` (every numerator, denominators 1 to 16),
`gcd(x) == lcm(x) == abs(x)`, with the `OverflowError` of `abs` for a `typemin` numerator. -/
def RationalUnaryGcd : Prop := ∀ (n : Fin 16) (d : Fin 4),
  okSat (IntArith.Rational.ofInts (JInt.lit .i8 n.val) (JInt.lit .i8 (d.val + 1)))
    (fun x => decide (gcdRational x = IntArith.Rational.abs x) &&
      decide (lcmRational x = IntArith.Rational.abs x))
    (fun _ => false) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rationalUnaryGcd : RationalUnaryGcd := by
  unfold RationalUnaryGcd; decide +kernel

/-! ### Mixed-type and n-ary dispatch -/

/-- A byte-or-short type: `Int8`, `UInt8`, `Int16`, `UInt16`. -/
def smallTy : Fin 4 → IntTy
  | 0 => .i8 | 1 => .u8 | 2 => .i16 | 3 => .u16

/-- `gcd(a::Real, b::Real) = gcd(promote(a,b)...)` and the mixed-signedness methods
(`base/intfuncs.jl:146-150,155-160`), modelled by `mixedGcd`/`mixedLcm`/`mixedGcdx`:
between every pair of 8- and 16-bit types, for every first argument in `-128:127` (or
`0:255` for unsigned types) other than signed `typemin`, against every edge value as the
second argument, `gcd` and `lcm` return the mathematical result in the promoted type and
`gcdx` returns that gcd. The `typemin` first argument is the subject of
`intfuncscov-gcd-mixed-typemin`. -/
def MixedGcdLcm : Prop := ∀ (i j : Fin 4) (a : Fin 4) (k : Fin 4),
  let s := smallTy i
  let u := smallTy j
  let x : JInt s := JInt.lit s (if s.signed then (a.val : Int) - 128 else a.val)
  let y : JInt u := JInt.lit u (edge ⟨k.val, by omega⟩)
  let r := IntTy.promote s u
  x.val ≠ s.min ∨ s.signed = false →
    okVal (mixedGcd x y) = gcdSpec r x.val y.val ∧ okVal (mixedGcd y x) = gcdSpec r y.val x.val ∧
    okVal (mixedLcm x y) = lcmSpec r x.val y.val ∧
    (mixedGcdx x y).map (fun d => d.1.val) = gcdSpec r x.val y.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedGcdLcm : MixedGcdLcm := by
  unfold MixedGcdLcm; decide +kernel

/-- The documented gcd/lcm of a signed and an unsigned argument exists in the promoted
type, so `gcd`, `lcm` and `gcdx` return it, also when the signed argument is `typemin`. -/
def MixedTypeminRepresentable : Prop := ∀ (a : JInt .i8) (b : JInt .u8),
  (Nat.gcd a.val.natAbs b.val.natAbs : Int) ≤ IntTy.max .u8 →
  okVal (mixedGcd a b) = .ok (Nat.gcd a.val.natAbs b.val.natAbs : Int) ∧
  okVal (mixedGcd b a) = .ok (Nat.gcd a.val.natAbs b.val.natAbs : Int)

theorem mixedTypeminRepresentable_refuted : ¬ MixedTypeminRepresentable := by
  intro h
  have := (h (JInt.lit .i8 (-128)) (JInt.lit .u8 2) (by decide)).1
  revert this
  decide +kernel

/-- `gcd(a, b, c...) = gcd(a, gcd(b, c...))`, `base/intfuncs.jl:161`. -/
def gcdN {t : IntTy} (a b : JInt t) : List (JInt t) → Jl (JInt t)
  | [] => gcd a b
  | c :: cs => do gcd a (← gcdN b c cs)

/-- `lcm(a, b, c...) = lcm(a, lcm(b, c...))`, `base/intfuncs.jl:162`. -/
def lcmN {t : IntTy} (a b : JInt t) : List (JInt t) → Jl (JInt t)
  | [] => lcm a b
  | c :: cs => do lcm a (← lcmN b c cs)

/-- `gcd(a::T, b::T) where T<:Real` and `lcm(a::T, b::T) where T<:Real`,
`base/intfuncs.jl:163-164`, and `gcdx(a::T, b::T) where T<:Real` (`:262`): a same-type
pair without a more specific method (for example two `Float64`s) throws `MethodError`. -/
def gcdSameReal {α : Type} (_ _ : α) : Jl α := .error (.methodError "gcd")
def lcmSameReal {α : Type} (_ _ : α) : Jl α := .error (.methodError "lcm")
def gcdxSameReal {α : Type} (_ _ : α) : Jl (α × α × α) := .error (.methodError "gcdx")

/-- The three-argument methods agree with the mathematical gcd and lcm of all arguments
(for every triple of small `Int8` values `-8:7`, where nothing overflows), and a same-type
non-integer pair throws `MethodError`. -/
def NaryGcdLcm : Prop :=
  (∀ a b c : Fin 16,
    let x := JInt.lit .i8 ((a.val : Int) - 8)
    let y := JInt.lit .i8 ((b.val : Int) - 8)
    let z := JInt.lit .i8 ((c.val : Int) - 8)
    okVal (gcdN x y [z]) = .ok (Nat.gcd x.val.natAbs (Nat.gcd y.val.natAbs z.val.natAbs) : Int) ∧
    okVal (lcmN x y [z]) =
      lcmSpec .i8 x.val (Nat.lcm y.val.natAbs z.val.natAbs : Int)) ∧
  (∀ (α : Type) (a b : α), gcdSameReal a b = .error (.methodError "gcd") ∧
    lcmSameReal a b = .error (.methodError "lcm") ∧
    gcdxSameReal a b = .error (.methodError "gcdx"))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem naryGcdLcm : NaryGcdLcm := by
  refine ⟨?_, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  decide +kernel

/-- `gcdx(a, b, cs...)`, `base/intfuncs.jl:264-274`: `d, i, j = gcdx(a, b)`;
`d′, x, ys... = gcdx(d, cs...)`; returns `(d′, i*x, j*x, ys...)`. -/
def gcdxN {t : IntTy} (a b : JInt t) : List (JInt t) → Jl (JInt t × List (JInt t))
  | [] => do
    let (d, u, v) ← gcdx a b
    pure (d, [u, v])
  | c :: cs => do
    let (d, i, j) ← gcdx a b
    let (d', coeffs) ← gcdxN d c cs
    match coeffs with
    | x :: ys => pure (d', i * x :: j * x :: ys)
    | [] => pure (d', [])

/-- The docstring's n-argument solution `u*a + v*b + w*c = d = gcd(a, b, c)`, for every triple
of small `Int8` values `-8:7`. -/
def GcdxThree : Prop := ∀ a b c : Fin 16,
  let x := JInt.lit .i8 ((a.val : Int) - 8)
  let y := JInt.lit .i8 ((b.val : Int) - 8)
  let z := JInt.lit .i8 ((c.val : Int) - 8)
  okSat (gcdxN x y [z])
    (fun r => match r.2 with
      | [u, v, w] => decide (r.1.val = Nat.gcd x.val.natAbs (Nat.gcd y.val.natAbs z.val.natAbs)) &&
          decide (u.val * x.val + v.val * y.val + w.val * z.val = r.1.val)
      | _ => false)
    (fun _ => false) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gcdxThree : GcdxThree := by
  unfold GcdxThree; decide +kernel

/-! ### Arrays -/

/-- The loop of `gcd(abc::AbstractArray{<:Integer})`, `base/intfuncs.jl:178-187`: start from
zero, stop early once the running gcd is one. -/
def gcdArrayLoop {t : IntTy} (a : JInt t) : List (JInt t) → Jl (JInt t)
  | [] => pure a
  | b :: bs => do
    let a ← gcd a b
    if a.val = 1 then pure a else gcdArrayLoop a bs

def gcdArray {t : IntTy} (v : List (JInt t)) : Jl (JInt t) := gcdArrayLoop (JInt.lit t 0) v

/-- `gcd` of an integer array is the gcd of its elements whenever that is representable,
as for the two- and n-argument methods. -/
def GcdArrayRepresentable : Prop := ∀ (v : List (JInt .i8)),
  ((v.foldl (fun g x => Nat.gcd g x.val.natAbs) 0 : Nat) : Int) ≤ IntTy.max .i8 →
  okVal (gcdArray v) = .ok ((v.foldl (fun g x => Nat.gcd g x.val.natAbs) 0 : Nat) : Int)

theorem gcdArrayRepresentable_refuted : ¬ GcdArrayRepresentable := by
  intro h
  have := h [JInt.lit .i8 (-128), JInt.lit .i8 2] (by decide)
  revert this
  decide +kernel

/-- `gcd(abc::AbstractArray{<:Real}) = reduce(gcd, abc; init=zero(eltype(abc)))`,
`base/intfuncs.jl:166`, for a two-argument `gcd` `g` of the element type. -/
def gcdRealArray {α : Type} (g : α → α → Jl α) (zero : α) (v : List α) : Jl α :=
  v.foldlM g zero

/-- `lcm(abc::AbstractArray{<:Real})`, `base/intfuncs.jl:167-176`, for integer elements:
`one` for an empty array, `abs(only(abc))` for one element, else `reduce(lcm, abc)`. -/
def lcmArray {t : IntTy} : List (JInt t) → Jl (JInt t)
  | [] => pure (JInt.lit t 1)
  | [a] => pure (if a.val < 0 then -a else a)
  | a :: b :: rest => do
    let l ← lcm a b
    rest.foldlM lcm l

/-- `lcm(abc::AbstractArray{<:Real})` for an empty array of non-integer element type
throws `ArgumentError`, `base/intfuncs.jl:172`. -/
def lcmArrayNonInteger {α : Type} (abs : α → α) (l : α → α → Jl α) : List α → Jl α
  | [] => .error (.argumentError "lcm has no identity")
  | [a] => pure (abs a)
  | a :: b :: rest => do
    let x ← l a b
    rest.foldlM l x

/-- `lcm` of an `Int8` array of up to three small values `-8:7` is the least common multiple
of its elements (one for the empty array), or `OverflowError`; the generic `Real` methods
fold the two-argument operations and an empty non-integer array has no lcm identity. -/
def ArrayGcdLcm : Prop :=
  (∀ (n : Fin 4) (a b c : Fin 16),
    let v := ([a, b, c].take n.val).map (fun i => JInt.lit .i8 ((i.val : Int) - 8))
    okVal (lcmArray v) =
      lcmSpec .i8 1 ((v.foldl (fun l x => Nat.lcm l x.val.natAbs) 1 : Nat) : Int) ∧
    okVal (gcdArray v) = .ok ((v.foldl (fun g x => Nat.gcd g x.val.natAbs) 0 : Nat) : Int)) ∧
  (∀ (α : Type) (g : α → α → Jl α) (z : α) (v : List α), gcdRealArray g z v = v.foldlM g z) ∧
  (∀ (α : Type) (abs : α → α) (l : α → α → Jl α),
    lcmArrayNonInteger abs l [] = .error (.argumentError "lcm has no identity"))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem arrayGcdLcm : ArrayGcdLcm := by
  refine ⟨?_, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  decide +kernel

/-! ### `invmod` -/

/-- `_bezout_coef(n, m)`, `base/intfuncs.jl:337-341` (modelled by `bezoutCoef`): for every
`Int8` pair it returns a Bézout coefficient `x` with `x*n ≡ 1 (mod m)` when `gcd(n, m) == 1`
(`m ≠ 0`) and throws `DomainError` when the gcd is not one. -/
def BezoutCoefficient : Prop := ∀ (n : Fin 16) (k : Fin 16),
  let a : Int := (JInt.lit .i8 n.val).val
  let m : Int := (JInt.lit .i8 (edge k)).val
  okSat (bezoutCoef (some .i8) a m)
    (fun x => decide (Nat.gcd a.natAbs m.natAbs = 1) && decide (m = 0 ∨ (x * a - 1) % m = 0))
    (fun e => isDomainErr e && decide (Nat.gcd a.natAbs m.natAbs ≠ 1)) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bezoutCoefficient : BezoutCoefficient := by
  unfold BezoutCoefficient; decide +kernel

/-- `invmod(n::Integer, ::Type{T})` (`base/intfuncs.jl:370`) computes `invmod(n % T)`:
for every `Int16` value `n` in `-128:127` and both byte types, `(n % T) * invmod(n, T) == 1`
for odd `n`, and `DomainError` for even `n`. `invmod(n, Union{})` throws `MethodError`
(`:371`). -/
def invmodBottom {α : Type} (_ : α) : Jl Unit := .error (.methodError "invmod")

def InvmodType : Prop :=
  (∀ (s : Bool) (n : Fin 16),
    let t := byteTy s
    let a := JInt.lit .i16 ((n.val : Int) - 128)
    okSat (invmodType a t)
      (fun y => decide (a.val % 2 ≠ 0) && decide ((JInt.rem t a * y).val = 1))
      (fun e => isDomainErr e && decide (a.val % 2 = 0)) = true) ∧
  (∀ (α : Type) (n : α), invmodBottom n = .error (.methodError "invmod"))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem invmodTypeProp : InvmodType := by
  refine ⟨?_, fun _ _ => rfl⟩
  decide +kernel

end JuliaLean.IntFuncsCov.Gcd
