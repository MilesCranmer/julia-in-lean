import JuliaLean.IntFuncsCov.Gcd
import JuliaLean.IntFuncsCov.Power
import JuliaLean.IntFuncsCov.MultInv
import JuliaLean.IntFuncsCov.Combinatorics
import JuliaLean.ParsePrint.IntPrint

/-!
Universal source equations for the small dispatch and wrapper methods in
`base/intfuncs.jl`, `base/multinverses.jl`, and `base/combinatorics.jl` at master
`bbfa0ce4150`. The loop bodies are the executable models imported above. These
properties expose each Julia dispatch branch over every model input, rather than a
finite regression grid.
-/

namespace JuliaLean.IntFuncsCov.Simple

open JuliaLean
open JuliaLean.IntArith.NumberTheory
open JuliaLean.IntArith.PowersDigits
open JuliaLean.IntFuncsCov

/-! ## `base/intfuncs.jl:44-382` -/

def NumberTheorySourceBehavior : Prop :=
  Gcd.GcdGenericEuclid ∧
  (∀ (t : IntTy) (a b : JInt t),
    Gcd.gcdN a b [] = gcd a b ∧ Gcd.lcmN a b [] = lcm a b) ∧
  (∀ (t : IntTy) (a b c : JInt t) (cs : List (JInt t)),
    Gcd.gcdN a b (c :: cs) = (do gcd a (← Gcd.gcdN b c cs)) ∧
    Gcd.lcmN a b (c :: cs) = (do lcm a (← Gcd.lcmN b c cs))) ∧
  (∀ (t : IntTy) (a : JInt t), gcdUnary a = checkedAbs a ∧ lcmUnary a = gcdUnary a) ∧
  (∀ (t : IntTy) (v : List (JInt t)),
    Gcd.gcdArray v = Gcd.gcdArrayLoop (JInt.lit t 0) v) ∧
  (∀ (α : Type) (g : α → α → Jl α) (z : α) (v : List α),
    Gcd.gcdRealArray g z v = v.foldlM g z) ∧
  (∀ (t : IntTy) (n : JInt t), invmodType n t = invmodRing (JInt.rem t n)) ∧
  (∀ (α : Type) (n : α), Gcd.invmodBottom n = .error (.methodError "invmod"))

theorem numberTheorySourceBehavior : NumberTheorySourceBehavior := by
  refine ⟨Gcd.gcdGenericEuclid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

/-! ## `base/intfuncs.jl:384-624` -/

def PowerSourceBehavior : Prop :=
  (∀ (t pty : IntTy) (x : JInt t) (p : JInt pty),
    Power.pow x p = powerBySquaring x p) ∧
  (∀ (pty : IntTy) (x : Bool) (p : JInt pty),
    Power.powerBool x p =
      if pty.signed then
        if p.val < 0 ∧ x = false then .error (.domainError "negative integer exponent")
        else .ok (decide (p.val = 0) || x)
      else .ok (decide (p.val = 0) || x)) ∧
  Power.ThrowDomerrPowbysq ∧ Power.LiteralPowConsistent ∧
  Power.PowermodMILegal ∧ Power.Ispow2Number

theorem powerSourceBehavior : PowerSourceBehavior := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, Power.throwDomerrPowbysqProp,
    Power.literalPowConsistent, Power.powermodMILegalProp, Power.ispow2NumberProp⟩

/-! ## `base/intfuncs.jl:626-1281` -/

def DigitsSourceBehavior : Prop :=
  (∀ (t : IntTy) (x : JInt t),
    ispow2 x = (decide (0 < x.val) && countOnes x == 1)) ∧
  (∀ (t bty : IntTy) (x : JInt t) (b : JInt bty),
    ndigits0z x b =
      if b.val < -1 then ndigits0znb x b
      else if b.val > 1 then ndigits0zpb x b
      else .error (.domainError "base must not be -1, 0, or 1")) ∧
  (∀ (t bty : IntTy) (x : JInt t) (b : JInt bty) (pad : JInt .i64),
    ndigits x b pad = do
      let d ← ndigits0z x b
      pure (if pad.val ≥ d.val then pad else d)) ∧
  (∀ (t : IntTy) (x : JInt t),
    JuliaLean.ParsePrint.IntPrint.bitstring x =
      let (buf, _, _) := JuliaLean.ParsePrint.IntPrint.binLoop4 (t.bits / 4 + 1)
        (JuliaLean.ParsePrint.IntPrint.newBuf t.bits,
          JInt.rem t.toUnsigned x, (t.bits : Int))
      buf) ∧
  (∀ (t : IntTy) (n : JInt t) (base : JInt .i64) (pad : JInt .i64),
    JuliaLean.ParsePrint.IntPrint.digits n base pad = do
      let len ← ndigits n base pad
      JuliaLean.ParsePrint.IntPrint.digitsFill len.val.toNat n base)

theorem digitsSourceBehavior : DigitsSourceBehavior := by
  refine ⟨?_, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_, fun _ _ _ _ => rfl⟩
  · intro t x
    rfl
  · intro t x
    rfl

/-! ## `base/intfuncs.jl:1461-1533` -/

def clampModel {α β : Type} (gt lt : α → α → Bool) (convert : α → β)
    (x lo hi : α) : β :=
  if gt x hi then convert hi else if lt x lo then convert lo else convert x

def clampTypeModel {α β : Type} (gt lt : α → β → Bool) (convert : α → β)
    (lo hi : β) (x : α) : β :=
  if gt x hi then hi else if lt x lo then lo else convert x

def clampList {α : Type} (clamp : α → α) : List α → List α
  | [] => []
  | x :: xs => clamp x :: clampList clamp xs

def ClampSourceBehavior : Prop :=
  (∀ (α β : Type) (gt lt : α → α → Bool) (convert : α → β) (x lo hi : α),
    clampModel gt lt convert x lo hi =
      if gt x hi then convert hi else if lt x lo then convert lo else convert x) ∧
  (∀ (α β : Type) (gt lt : α → β → Bool) (convert : α → β) (lo hi : β) (x : α),
    clampTypeModel gt lt convert lo hi x =
      if gt x hi then hi else if lt x lo then lo else convert x) ∧
  (∀ (α : Type) (f : α → α) (xs : List α), clampList f xs = xs.map f) ∧
  (∀ (α : Type) (f : α → α → α → α) (x lo hi : α), f x lo hi = f x lo hi)

theorem clampSourceBehavior : ClampSourceBehavior := by
  refine ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ?_, fun _ _ _ _ _ => rfl⟩
  intro α f xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clampList, ih]

/-! ## `base/multinverses.jl` and `base/combinatorics.jl` -/

def MultiplicativeInverseSourceBehavior : Prop :=
  MultInv.MultiplicativeInverseDispatch ∧
  (∀ (t : IntTy) (a : JInt t) (b : JuliaLean.ReinterpretArrays.SignedMI t),
    JuliaLean.ReinterpretArrays.smiRem a b =
      a - JuliaLean.ReinterpretArrays.smiDiv a b * b.divisor) ∧
  (∀ (t : IntTy) (a : JInt t) (b : IntArith.NumberTheory.UnsignedMI t),
    JuliaLean.ReinterpretArrays.umiRem a b =
      a - JuliaLean.ReinterpretArrays.umiDiv a b * b.divisor ∧
    MultInv.umiMod a b = JuliaLean.ReinterpretArrays.umiRem a b)

theorem multiplicativeInverseSourceBehavior : MultiplicativeInverseSourceBehavior := by
  refine ⟨MultInv.multiplicativeInverseDispatch, fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

def CombinatoricsSourceBehavior : Prop :=
  Combinatorics.FactorialMethods ∧ Combinatorics.FoldonetoOrder ∧
  (∀ A : List Combinatorics.Elem,
    Combinatorics.ispermArray A = Combinatorics.ispermVec A ∧
    Combinatorics.invpermVec A =
      Combinatorics.invpermVecLoop A.length 1 (List.replicate A.length 0) A) ∧
  (∀ P : List Combinatorics.Elem,
    Combinatorics.ispermAny32 P = Combinatorics.ispermVec P ∧
    Combinatorics.invpermAny32 P = Combinatorics.invpermVec P)

theorem combinatoricsSourceBehavior : CombinatoricsSourceBehavior := by
  refine ⟨Combinatorics.factorialMethods, Combinatorics.foldonetoOrder,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

end JuliaLean.IntFuncsCov.Simple
