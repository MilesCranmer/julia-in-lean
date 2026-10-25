import JuliaLean.Core
import JuliaLean.IntArith.NumberTheory

/-!
Model of `Base.MultiplicativeInverses` (`base/multinverses.jl`, master).
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `mul_hi(a, b)`, `base/int.jl:123-141`: the high half of the exact double-width product. -/
def mulHi {t : IntTy} (a b : JInt t) : JInt t :=
  JInt.wrap t ((a.val * b.val) / (2 ^ t.bits : Int))

/-- Arithmetic (signed) or logical (unsigned) right shift `x >> k`, `base/int.jl:597-605`. -/
def shr {t : IntTy} (x : JInt t) (k : Nat) : JInt t :=
  JInt.wrap t (x.val / (2 ^ k : Int))

/-- Left shift `x << 1`, `base/int.jl:606`. -/
def shl1 {t : IntTy} (x : JInt t) : JInt t := JInt.wrap t (x.val * 2)

/-- `flipsign(x, y)` for same-type `BitSigned`, `base/int.jl:188`. -/
def flipsign {t : IntTy} (x y : JInt t) : JInt t := if y.val < 0 then -x else x

/-- `abs(x)` on `BitInteger`, `base/int.jl:176-180` (wraps at `typemin`). -/
def jabs {t : IntTy} (x : JInt t) : JInt t := if x.val < 0 then -x else x

/-- Fields of `SignedMultiplicativeInverse{T}`, `base/multinverses.jl:47-51`. -/
structure SignedMI (t : IntTy) where
  divisor : JInt t
  multiplier : JInt t
  addmul : JInt .i8
  shift : JInt .u8
  deriving DecidableEq, Repr

/-- Loop state of the signed constructor, `base/multinverses.jl:62-64`. -/
structure SmiState (t : IntTy) where
  p : JInt .i64
  q1 : JInt t.toUnsigned
  r1 : JInt t.toUnsigned
  q2 : JInt t.toUnsigned
  r2 : JInt t.toUnsigned
  deriving DecidableEq, Repr

/-- Inputs computed before the loop, `base/multinverses.jl:54-64`: `anc`, `ad` and the
initial state. -/
def smiPre {t : IntTy} (d : JInt t) : Jl (JInt t.toUnsigned × JInt t.toUnsigned × SmiState t) := do
  if d.val = 0 then throw (.argumentError "cannot compute magic for d == 0")
  let signedmin : JInt t.toUnsigned := JInt.rem t.toUnsigned (JInt.typemin t)
  let ad : JInt t.toUnsigned := JInt.rem t.toUnsigned (jabs d)
  let tt : JInt t.toUnsigned := signedmin + JInt.lit t.toUnsigned (if d.val < 0 then 1 else 0)
  let anc := tt - JInt.lit t.toUnsigned 1 - (← JInt.remInt tt ad)
  let p : JInt .i64 := JInt.lit .i64 ((t.bits : Int) - 1)
  let q1 ← JInt.div signedmin anc
  let r1 ← JInt.remInt signedmin anc
  let q2 ← JInt.div signedmin ad
  let r2 ← JInt.remInt signedmin ad
  pure (anc, ad, ⟨p, q1, r1, q2, r2⟩)

/-- One pass of the loop body, `base/multinverses.jl:66-80`. -/
def smiStep {t : IntTy} (anc ad : JInt t.toUnsigned) (s : SmiState t) : SmiState t :=
  let one := JInt.lit t.toUnsigned 1
  let q1 := shl1 s.q1
  let r1 := shl1 s.r1
  let (q1, r1) := if r1 ≥ anc then (q1 + one, r1 - anc) else (q1, r1)
  let q2 := shl1 s.q2
  let r2 := shl1 s.r2
  let (q2, r2) := if r2 ≥ ad then (q2 + one, r2 - ad) else (q2, r2)
  ⟨s.p + JInt.lit .i64 1, q1, r1, q2, r2⟩

/-- Loop condition, `base/multinverses.jl:81-82`. -/
def smiContinue {t : IntTy} (ad : JInt t.toUnsigned) (s : SmiState t) : Prop :=
  let delta := ad - s.r2
  s.q1 < delta ∨ (s.q1 = delta ∧ s.r1.val = 0)

instance {t : IntTy} (ad : JInt t.toUnsigned) (s : SmiState t) : Decidable (smiContinue ad s) := by
  unfold smiContinue; infer_instance

/-- The `while true` loop, `base/multinverses.jl:65-83`, as a big-step relation: `SmiLoop anc ad s r`
holds when the loop started in state `s` terminates in state `r`. -/
inductive SmiLoop {t : IntTy} (anc ad : JInt t.toUnsigned) : SmiState t → SmiState t → Prop
  | stop (s : SmiState t) : ¬ smiContinue ad (smiStep anc ad s) → SmiLoop anc ad s (smiStep anc ad s)
  | next (s r : SmiState t) : smiContinue ad (smiStep anc ad s) →
      SmiLoop anc ad (smiStep anc ad s) r → SmiLoop anc ad s r

/-- Result fields, `base/multinverses.jl:85-87`. -/
def smiFinish {t : IntTy} (d : JInt t) (s : SmiState t) : Jl (SignedMI t) := do
  let m := flipsign (JInt.rem t (s.q2 + JInt.lit t.toUnsigned 1)) d
  let sh := s.p - JInt.lit .i64 (t.bits : Int)
  let addmul : JInt .i8 :=
    if d.val > 0 ∧ m.val < 0 then JInt.lit .i8 1
    else if d.val < 0 ∧ m.val > 0 then JInt.lit .i8 (-1) else JInt.lit .i8 0
  let shift ← JInt.convert .u8 sh.val
  pure ⟨d, m, addmul, shift⟩

/-- `SignedMultiplicativeInverse{T}(d)`, `base/multinverses.jl:53-88`: `SmiNew d mi` holds when the
constructor returns `mi`. -/
def SmiNew {t : IntTy} (d : JInt t) (mi : SignedMI t) : Prop :=
  ∃ anc ad s0 s, smiPre d = .ok (anc, ad, s0) ∧ SmiLoop anc ad s0 s ∧ smiFinish d s = .ok mi

/-- Bounded evaluator of the constructor; `smiNewEval_sound` shows every result it returns is the
constructor's. -/
def smiLoopEval {t : IntTy} (anc ad : JInt t.toUnsigned) : Nat → SmiState t → Option (SmiState t)
  | 0, _ => none
  | fuel + 1, s =>
    let s' := smiStep anc ad s
    if smiContinue ad s' then smiLoopEval anc ad fuel s' else some s'

def smiNewEval {t : IntTy} (d : JInt t) (fuel : Nat := 400) : Option (Jl (SignedMI t)) :=
  match smiPre d with
  | .error e => some (.error e)
  | .ok (anc, ad, s0) => (smiLoopEval anc ad fuel s0).map (smiFinish d)

theorem smiLoopEval_sound {t : IntTy} (anc ad : JInt t.toUnsigned) :
    ∀ (fuel : Nat) (s r : SmiState t), smiLoopEval anc ad fuel s = some r → SmiLoop anc ad s r
  | 0, _, _, h => by simp [smiLoopEval] at h
  | fuel + 1, s, r, h => by
    simp only [smiLoopEval] at h
    split at h
    · exact .next _ _ (by assumption) (smiLoopEval_sound anc ad fuel _ _ h)
    · cases h; exact .stop _ (by assumption)

theorem smiNewEval_sound {t : IntTy} (d : JInt t) (fuel : Nat) (mi : SignedMI t)
    (h : smiNewEval d fuel = some (.ok mi)) : SmiNew d mi := by
  unfold smiNewEval at h
  split at h
  · simp at h
  · rename_i anc ad s0 hpre
    cases hl : smiLoopEval anc ad fuel s0 with
    | none => simp [hl] at h
    | some s =>
      simp [hl] at h
      exact ⟨anc, ad, s0, s, hpre, smiLoopEval_sound anc ad fuel s0 s hl, h⟩

/-- `div(a, b::SignedMultiplicativeInverse)`, `base/multinverses.jl:137-141`. `a *% b.addmul`
promotes the `Int8` to `T`; `signbit(x) + (x >> shift)` promotes the `Bool` to `T`. -/
def smiDiv {t : IntTy} (a : JInt t) (b : SignedMI t) : JInt t :=
  let x := mulHi a b.multiplier
  let x := x + JInt.rem t (a * JInt.rem t b.addmul)
  if (jabs b.divisor).val = 1 then a * b.divisor
  else JInt.rem t (JInt.lit t (if x.val < 0 then 1 else 0) + shr x b.shift.val.toNat)

/-- `rem(a, b::MultiplicativeInverse)`, `base/multinverses.jl:148-149`. -/
def smiRem {t : IntTy} (a : JInt t) (b : SignedMI t) : JInt t := a - smiDiv a b * b.divisor

/-- `mod(a, b::SignedMultiplicativeInverse)`, `base/multinverses.jl:158-161`. -/
def smiMod {t : IntTy} (a : JInt t) (b : SignedMI t) : JInt t :=
  let r := smiRem a b
  if r.val = 0 ∨ (decide (r.val < 0) = decide (b.divisor.val < 0)) then r else r + b.divisor

/-- `div(a, b::UnsignedMultiplicativeInverse)`, `base/multinverses.jl:142-146`, on the constructor
model `IntArith.NumberTheory.unsignedMI` (`base/multinverses.jl:98-133`). -/
def umiDiv {t : IntTy} (a : JInt t) (b : IntArith.NumberTheory.UnsignedMI t) : JInt t :=
  let x := mulHi a b.multiplier
  let x := if b.add then shr (a - x) 1 + x else x
  if b.divisor.val = 1 then a else shr x b.shift

/-- `rem(a, b)` and `mod(a, b)` for an unsigned inverse, `base/multinverses.jl:148-149,156`. -/
def umiRem {t : IntTy} (a : JInt t) (b : IntArith.NumberTheory.UnsignedMI t) : JInt t :=
  a - umiDiv a b * b.divisor

end JuliaLean.ReinterpretArrays
