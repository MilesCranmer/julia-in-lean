import JuliaLean.ReinterpretArrays.MultInv

/-!
Properties of `Base.MultiplicativeInverses` (`base/multinverses.jl`).
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `div(a, SignedMultiplicativeInverse(d))` agrees with `div(a, d)` (value or exception) for every
dividend and every nonzero divisor. -/
def SmiDivAll : Prop :=
  ∀ t : IntTy, t.signed = true → ∀ (a d : JInt t), d.val ≠ 0 →
    ∀ mi : SignedMI t, SmiNew d mi → (.ok (smiDiv a mi) : Jl (JInt t)) = JInt.div a d

/-- The signed constructor terminates for every nonzero divisor, and `div(a, mi)` equals `div(a, d)`
whenever `div(a, d)` does not throw (every input except `div(typemin(T), -1)`). -/
def SmiDivCorrect : Prop :=
  ∀ t : IntTy, t.signed = true → ∀ (a d : JInt t), d.val ≠ 0 → ¬ (a.val = t.min ∧ d.val = -1) →
    (∃ mi : SignedMI t, SmiNew d mi) ∧
    ∀ mi : SignedMI t, SmiNew d mi → (.ok (smiDiv a mi) : Jl (JInt t)) = JInt.div a d

/-- `rem(a, mi)` and `mod(a, mi)` for a signed inverse agree with `rem(a, d)` and `mod(a, d)` for every
dividend and every nonzero divisor. -/
def SmiRemModCorrect : Prop :=
  ∀ t : IntTy, t.signed = true → ∀ (a d : JInt t), d.val ≠ 0 →
    ∀ mi : SignedMI t, SmiNew d mi →
      (.ok (smiRem a mi) : Jl (JInt t)) = JInt.remInt a d ∧ (.ok (smiMod a mi) : Jl (JInt t)) = JInt.mod a d

/-- The unsigned constructor returns for every nonzero divisor, and `div(a, mi)` and `rem(a, mi)`
equal `div(a, d)` and `rem(a, d)` for every dividend. -/
def UmiDivCorrect : Prop :=
  ∀ t : IntTy, t.signed = false → ∀ (a d : JInt t), d.val ≠ 0 →
    ∃ mi, IntArith.NumberTheory.unsignedMI d = .ok mi ∧
      (.ok (umiDiv a mi) : Jl (JInt t)) = JInt.div a d ∧ (.ok (umiRem a mi) : Jl (JInt t)) = JInt.remInt a d

end JuliaLean.ReinterpretArrays
