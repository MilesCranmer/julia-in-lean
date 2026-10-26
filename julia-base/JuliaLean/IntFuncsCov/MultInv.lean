import JuliaLean.ReinterpretArrays.ProofSmi
import JuliaLean.ReinterpretArrays.ProofUmi

/-!
Coverage of the remaining methods of `base/multinverses.jl` (master `bbfa0ce4150`):
the `unsigned(::Type)` methods of the module, the outer constructors,
`multiplicativeinverse`, and `mod` for an unsigned inverse. The inner constructors and
`div`/`rem` are the `ReinterpretArrays` models (`SmiNew`, `unsignedMI`, `smiDiv`,
`umiDiv`, `umiRem`), whose correctness theorems are reused here.
-/

namespace JuliaLean.IntFuncsCov.MultInv

open JuliaLean JuliaLean.ReinterpretArrays

/-- The type argument of `unsigned(::Type)`: `Bool`, a `BitInteger` type, or `Union{}`. -/
inductive TypeArg where
  | bool
  | int (t : IntTy)
  | bottom
  deriving DecidableEq

/-- The eight `unsigned(::Type)` methods, `base/multinverses.jl:8-15`. `Bool` maps to
`UInt`, which is `UInt64` on the 64-bit platforms modelled here. -/
def unsignedType : TypeArg → Jl IntTy
  | .bool => .ok .u64
  | .int .i8 => .ok .u8
  | .int .i16 => .ok .u16
  | .int .i32 => .ok .u32
  | .int .i64 => .ok .u64
  | .int .i128 => .ok .u128
  | .int t => .ok t
  | .bottom => .error (.methodError "unsigned")

instance instDecEqJl {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- `unsigned(T)` is the unsigned type of the same width for every `BitInteger` type, the
identity on unsigned types, `UInt` for `Bool`, and a `MethodError` for `Union{}`. -/
def UnsignedTypeSameWidth : Prop :=
  (∀ t : IntTy, ∃ u, unsignedType (.int t) = .ok u ∧ u.signed = false ∧ u.bits = t.bits ∧
      u = t.toUnsigned ∧ (t.signed = false → u = t)) ∧
  unsignedType .bool = .ok .u64 ∧
  unsignedType .bottom = .error (.methodError "unsigned")

theorem unsignedTypeSameWidth : UnsignedTypeSameWidth := by
  refine ⟨?_, rfl, rfl⟩
  intro t
  cases t <;> exact ⟨_, rfl, by decide, by decide, by decide, by decide⟩

/-- `SignedMultiplicativeInverse(x::Signed)`, `base/multinverses.jl:90`: the inner
constructor at `typeof(x)`; `SmiNew x mi` holds when it returns `mi`. -/
def signedMIOuter {t : IntTy} (x : JInt t) (mi : SignedMI t) : Prop := SmiNew x mi

/-- `UnsignedMultiplicativeInverse(x::Unsigned)`, `base/multinverses.jl:135`. -/
def unsignedMIOuter {t : IntTy} (x : JInt t) : Jl (IntArith.NumberTheory.UnsignedMI t) :=
  IntArith.NumberTheory.unsignedMI x

/-- `multiplicativeinverse(x::Signed)`, `base/multinverses.jl:163`. -/
def multiplicativeinverseSigned {t : IntTy} (x : JInt t) (mi : SignedMI t) : Prop :=
  signedMIOuter x mi

/-- `multiplicativeinverse(x::Unsigned)`, `base/multinverses.jl:164`. -/
def multiplicativeinverseUnsigned {t : IntTy} (x : JInt t) :
    Jl (IntArith.NumberTheory.UnsignedMI t) :=
  unsignedMIOuter x

/-- `mod(a::T, b::UnsignedMultiplicativeInverse{T})`, `base/multinverses.jl:156`. -/
def umiMod {t : IntTy} (a : JInt t) (b : IntArith.NumberTheory.UnsignedMI t) : JInt t :=
  umiRem a b

/-- `multiplicativeinverse(x)` returns an inverse for every nonzero divisor of every
`BitInteger` type, and `div`, `rem` and `mod` with it agree with the same operations on `x`
(signed `div(typemin, -1)` excepted, which is refuted separately); a zero divisor throws
`ArgumentError`. -/
def MultiplicativeInverseDispatch : Prop :=
  (∀ t : IntTy, t.signed = true → ∀ (x a : JInt t), x.val ≠ 0 →
    ¬ (a.val = t.min ∧ x.val = -1) →
    (∃ mi, multiplicativeinverseSigned x mi) ∧
    ∀ mi, multiplicativeinverseSigned x mi →
      (.ok (smiDiv a mi) : Jl (JInt t)) = JInt.div a x ∧
      (.ok (smiRem a mi) : Jl (JInt t)) = JInt.remInt a x ∧
      (.ok (smiMod a mi) : Jl (JInt t)) = JInt.mod a x) ∧
  (∀ t : IntTy, t.signed = false → ∀ (x a : JInt t), x.val ≠ 0 →
    ∃ mi, multiplicativeinverseUnsigned x = .ok mi ∧
      (.ok (umiDiv a mi) : Jl (JInt t)) = JInt.div a x ∧
      (.ok (umiRem a mi) : Jl (JInt t)) = JInt.remInt a x ∧
      (.ok (umiMod a mi) : Jl (JInt t)) = JInt.mod a x) ∧
  (∀ (t : IntTy) (x : JInt t), x.val = 0 →
    (∀ mi, ¬ multiplicativeinverseSigned x mi) ∧
    multiplicativeinverseUnsigned x = .error (.argumentError ""))

theorem multiplicativeInverseDispatch : MultiplicativeInverseDispatch := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x a hx hnot
    refine ⟨(smiDivCorrect t ht a x hx hnot).1, fun mi hmi => ?_⟩
    exact ⟨(smiDivCorrect t ht a x hx hnot).2 mi hmi, (smiRemModCorrect t ht a x hx mi hmi).1,
      (smiRemModCorrect t ht a x hx mi hmi).2⟩
  · intro t ht x a hx
    obtain ⟨mi, h1, h2, h3⟩ := umiDivCorrect t ht a x hx
    refine ⟨mi, h1, h2, h3, ?_⟩
    show (.ok (umiRem a mi) : Jl (JInt t)) = JInt.mod a x
    rw [h3]
    simp [JInt.mod, ht]
  · intro t x hx
    refine ⟨?_, ?_⟩
    · intro mi hmi
      obtain ⟨anc, ad, s0, s, hpre, -, -⟩ := hmi
      unfold smiPre at hpre
      simp [hx] at hpre
      cases hpre
    · show IntArith.NumberTheory.unsignedMI x = _
      unfold IntArith.NumberTheory.unsignedMI
      simp [hx]

end JuliaLean.IntFuncsCov.MultInv
