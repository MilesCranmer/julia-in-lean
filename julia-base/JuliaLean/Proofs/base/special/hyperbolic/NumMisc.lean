import JuliaLean.base.special.hyperbolic
import JuliaLean.Registry.Types

namespace JuliaLean.NumMisc

/-- The Float32 small branch of tanh is nondecreasing on ordered nonnegative inputs. -/
def TanhMonotone : Prop :=
  ∀ x y : NF32,
    takesTanhSmall32 x = true → takesTanhSmall32 y = true →
    JuliaLean.Promotion.Fl.le x y = true →
    JuliaLean.Promotion.Fl.le (tanhSmall32 x) (tanhSmall32 y) = true

/-- Exact odd/even symmetries for every modelled class. -/
def HyperbolicSymmetry : Prop :=
  ∀ x : HVal,
    hsinh x.neg = (hsinh x).neg ∧
    hcosh x.neg = hcosh x ∧
    htanh x.neg = (htanh x).neg ∧
    hasinh x.neg = (hasinh x).neg

def HyperbolicSpecialValues : Prop :=
  ∀ x : InvSpecial,
    hatanh x.neg = (hatanh x).neg ∧
    (x = .posOne → hacosh x = .posZero) ∧
    (x = .posInf → hacosh x = .posInf) ∧
    (x = .nan → hacosh x = .nan)

def tanhX32 : NF32 := nf32 0x3efbfa81

def tanhY32 : NF32 := nf32 0x3efbfa82

theorem tanhX32_value : tanhSmall32 tanhX32 = nf32 0x3ee96e0c := by decide +kernel

theorem tanhY32_value : tanhSmall32 tanhY32 = nf32 0x3ee96e0b := by decide +kernel

theorem tanhResultsNotOrdered :
    JuliaLean.Promotion.Fl.le (nf32 0x3ee96e0c) (nf32 0x3ee96e0b) = false := by
  decide +kernel

theorem tanhMonotone_refuted : ¬ TanhMonotone := by
  intro h
  have hm := h tanhX32 tanhY32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [tanhX32_value, tanhY32_value, tanhResultsNotOrdered] at hm
  cases hm

theorem hyperbolicSymmetry_proven : HyperbolicSymmetry := by
  intro x
  cases x <;> decide

theorem hyperbolicSpecialValues_proven : HyperbolicSpecialValues := by
  intro x
  cases x <;> decide

namespace Coverage

def HyperbolicForwardBehavior : Prop :=
  (∀ absx small large, sinhBranch absx small large =
    if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp) ∧
  (∀ absx small large, coshBranch absx small large =
    if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp) ∧
  (∀ abs2x small large, tanhBranch abs2x small large =
    if abs2x ≥ large then .saturated else if abs2x ≤ small then .kernel else .expFormula) ∧
  (∀ absx large, reciprocalHyperbolicBranch absx large = decide (absx ≥ large)) ∧
  (∀ x : HVal, hsinh x.neg = (hsinh x).neg ∧ hcosh x.neg = hcosh x ∧
    htanh x.neg = (htanh x).neg)

theorem hyperbolicForwardBehavior : HyperbolicForwardBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x; cases x <;> decide

def HyperbolicInverseBehavior : Prop :=
  (∀ finite absx two tiny large, asinhBranch finite absx two tiny large =
    if !finite then .nonfinite else if absx < tiny then .tiny else if absx < two then .belowTwo
    else if absx < large then .medium else .large) ∧
  (∀ nan x one two large, acoshBranch nan x one two large =
    if nan then .nan else if x < one then .domain else if x == one then .one
    else if x < two then .belowTwo else if x < large then .medium else .large) ∧
  (∀ nan absx half one, atanhBranch nan absx half one =
    if nan then .nan else if absx > one then .domain else if absx < half then .belowHalf else .upper) ∧
  (∀ x : InvSpecial, hatanh x.neg = (hatanh x).neg)

theorem hyperbolicInverseBehavior : HyperbolicInverseBehavior := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x; cases x <;> decide

end Coverage

end JuliaLean.NumMisc
