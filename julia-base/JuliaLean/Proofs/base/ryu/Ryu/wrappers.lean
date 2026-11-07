import JuliaLean.base.ryu.Ryu

/-! Wrapper methods from `base/ryu/Ryu.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.MiscCov.RyuWrap

open JuliaLean.MiscCov
open JuliaLean.MiscCov.RyuUtils


def DigitCounts : Prop := ∀ ft : FT,
  neededdigits ft = (match ft with | .f64 => 326 | .f32 => 50 | .f16 => 23) ∧
  neededfloatdigits ft = (match ft with | .f64 => 24 | .f32 => 17 | .f16 => 20)

theorem digitCounts_proven : DigitCounts := by
  intro ft
  cases ft <;> decide

def WrapperContract : Prop :=
  (∀ (X : Type) (write : Writer X ShortOpts) ft x opts,
    writeshortest write ft x (-2) opts = .error (.argumentError "precision must be at least -1")) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x opts p, ¬ p < -1 →
    writeshortest write ft x p opts = .ok (finish (write
      (if p < 0 then neededdigits ft else p.toNat + neededdigits ft) x p opts))) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, p < 0 →
    writefixed write ft x p opts = .error (.argumentError "precision must be non-negative")) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, ¬ p < 0 →
    writefixed write ft x p opts = .ok (finish (write (p.toNat + neededdigits ft) x p opts))) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, p < 0 →
    writeexp write ft x p opts = .error (.argumentError "precision must be non-negative")) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, ¬ p < 0 →
    writeexp write ft x p opts = .ok (finish (write (p.toNat + neededdigits ft) x p opts))) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x compact force fromprint same isF32,
    showFloat write ft x compact force fromprint same isF32 =
      finish (write (neededfloatdigits ft) x (-1)
        { hash := true, expchar := if isF32 && !fromprint then 0x66 else 0x65,
          typed := !force && !compact && !same, compact := compact })) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x,
    stringFloat write ft x = finish (write (neededfloatdigits ft) x (-1) {})) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x compact same isF32,
    printFloat write ft x compact same isF32 = showFloat write ft x compact true true same isF32)

theorem wrapperContract_proven : WrapperContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ _ _ _ => rfl⟩
  · intro X write ft x opts
    rfl
  · intro X write ft x opts p hp
    simp [writeshortest, hp]
  · intro X write ft x opts p hp
    simp [writefixed, hp]
  · intro X write ft x opts p hp
    simp [writefixed, hp]
  · intro X write ft x opts p hp
    simp [writeexp, hp]
  · intro X write ft x opts p hp
    simp [writeexp, hp]
  · intro X write ft x compact force fromprint same isF32
    rfl
  · intro X write ft x
    rfl

end JuliaLean.MiscCov.RyuWrap
