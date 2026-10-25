import JuliaLean.Promotion.RationalFloat
import JuliaLean.IntArith.Checked

/-!
`rationalize(T, x::Float64, 0)` and `Rational{T}(x::Float64)` at master `bbfa0ce4150`
(`base/rational.jl:217-221,256-319`), on the shared binary64 model.
-/

namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational
open JuliaLean.IntArith.Checked

/-- `abs(x)` on a `BitInteger`, wrapping at `typemin`; `base/int.jl:181-183`. -/
def jabs {t : IntTy} (x : JInt t) : JInt t := if x.val < 0 then -x else x

/-- `min(a, b)` on one integer type. -/
def jmin {t : IntTy} (a b : JInt t) : JInt t := if b.val < a.val then b else a

/-- Errors caught by the `try` blocks of `rationalize`: `InexactError` and `OverflowError`;
`base/rational.jl:282,309`. -/
def caught : JlError → Bool
  | .inexactError _ | .overflowError _ => true
  | _ => false

/-- Best semiconvergent fallback after a failed step; `base/rational.jl:283-288,310-315`. -/
def semiconvergent {t : IntTy} (a : F64) (p q pp qq : JInt t) : Jl (Rat t) :=
  if F64.le a (F64.ofInt 2) || ((-p).val == p.val && p.val < 0) then ofInts p q
  else do
    let tmax := JInt.typemax t
    let iaP ← if p.val == 0 then pure tmax else JInt.fld (tmax - jabs pp) (jabs p)
    let iaQ ← if q.val == 0 then pure tmax else JInt.fld (tmax - qq) q
    let ia := jmin iaP iaQ
    if cmpFI .lt (T := .f64) (Fl.ofF64 (F64.div a (F64.ofInt 2))) ia then
      ofInts (ia * p + pp) (ia * q + qq)
    else ofInts p q

/-- One convergent step inside `try`; `base/rational.jl:276-280`. -/
def convergentStep {t : IntTy} (a : F64) (p q pp qq : JInt t) : Jl (JInt t × JInt t) := do
  let ia ← F64.int t a
  let np ← checkedAdd (← checkedMul ia p) pp
  let nq ← checkedAdd (← checkedMul ia q) qq
  return (np, nq)

/-- Loop state `(x, y, a, r, nt, t, tt, p, q, pp, qq)` of `base/rational.jl:262-304`. -/
structure RState (t : IntTy) where
  x : F64
  y : F64
  a : F64
  r : F64
  nt : F64
  t1 : F64
  tt : F64
  p : JInt t
  q : JInt t
  pp : JInt t
  qq : JInt t

/-- Either a returned result or the next loop state. -/
inductive Step (t : IntTy) where
  | done (r : Jl (Rat t))
  | next (s : RState t)

/-- The continued-fraction loop; `base/rational.jl:273-304`. Each iteration either returns
or performs one `divrem`; `fuel` bounds the number of iterations. -/
def ratLoop {t : IntTy} : Nat → RState t → Step t
  | 0, s => .next s
  | fuel + 1, s =>
    if F64.lt s.nt s.r then
      match convergentStep s.a s.p s.q s.pp s.qq with
      | .error e => if caught e then .done (semiconvergent s.a s.p s.q s.pp s.qq) else .done (.error e)
      | .ok (np, nq) =>
        let x := s.y
        let y := s.r
        let a := F64.divInteger x y .RoundToZero
        let r := F64.rem x y
        let tt := s.t1
        let t1 := s.nt
        let nt := F64.add (F64.mul a t1) tt
        ratLoop fuel ⟨x, y, a, r, nt, t1, tt, np, nq, s.p, s.q⟩
    else .next s

/-- `rationalize(T, x, tol=0)`; `base/rational.jl:256-319`. A binary64 continued fraction
has fewer than 1500 terms, which bounds the loop. -/
def rationalize (t : IntTy) (x : F64) : Jl (Rat t) := do
  if !t.signed && F64.lt x (F64.zero false) then throw (.overflowError "cannot negate unsigned number")
  if F64.isnan x then
    return (← ofInts (← F64.int t x) (JInt.lit t 1))
  if F64.isinf x then return ⟨JInt.lit t (if F64.lt x (F64.zero false) then -1 else 1), JInt.lit t 0⟩
  let p := JInt.lit t (if F64.lt x (F64.zero false) then -1 else 1)
  let x := F64.abs x
  let a := F64.trunc x
  let s : RState t := ⟨x, F64.one, a, F64.sub x a, F64.zero false, F64.zero false,
    F64.zero false, p, JInt.lit t 0, JInt.lit t 0, JInt.lit t 1⟩
  match ratLoop 1500 s with
  | .done r => r
  | .next s =>
    let aMin := F64.cld (F64.sub s.x s.tt) (F64.add s.y s.t1)
    let attempt : Jl (Rat t) := do
      let (np, nq) ← convergentStep aMin s.p s.q s.pp s.qq
      ofInts np nq
    match attempt with
    | .error e => if caught e then semiconvergent s.a s.p s.q s.pp s.qq else .error e
    | .ok r => .ok r

/-- `Float64(x::Rational{S})`: `Float64(num)/Float64(den)`; `base/rational.jl:196-199`. -/
def ratToF64 {t : IntTy} (r : Rat t) : F64 := F64.div (F64.ofJInt r.num) (F64.ofJInt r.den)

/-- `Rational{T}(x::Float64)`; `base/rational.jl:217-221`. -/
def rationalOfF64 (t : IntTy) (x : F64) : Jl (Rat t) := do
  let r ← rationalize t x
  if F64.eq x (ratToF64 r) then return r
  throw (.inexactError "Rational")

end JuliaLean.Promotion
