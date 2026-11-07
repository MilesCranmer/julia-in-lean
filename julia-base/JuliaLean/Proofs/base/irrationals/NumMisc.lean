import JuliaLean.base.irrationals
import JuliaLean.Registry.Types

namespace JuliaLean.NumMisc

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

def tinyAboveOne : IrrationalNearOne := ⟨.above, 1000⟩

def tinyBelowOne : IrrationalNearOne := ⟨.below, 1000⟩

theorem tinyAbove_source : sourceIrrationalConvert tinyAboveOne .up = .one := by decide +kernel

theorem tinyAbove_exact : exactIrrationalConvert tinyAboveOne .up = .next := by decide +kernel

theorem irrationalRoundingCorrect_refuted : ¬ IrrationalRoundingCorrect := by
  intro h
  have hs := h tinyAboveOne .up
  rw [tinyAbove_source, tinyAbove_exact] at hs
  cases hs

theorem irrationalSeparatedRoundingCorrect_proven : IrrationalSeparatedRoundingCorrect := by
  intro x hx r
  unfold sourceIrrationalConvert exactIrrationalConvert bigAt256
  simp [show ¬x.separationBits > 256 by omega]

namespace Coverage

def IrrationalCoreBehavior : Prop :=
  (∀ value, irrationalBound value = value) ∧
  irrationalDefaultFloat = .f64 ∧
  (∀ kind, irrationalWiden kind = kind) ∧
  (∀ tag, irrationalPromotion tag = match tag with
    | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | _ => .promoted) ∧
  (∀ samples, firstStableRational samples = match samples with
    | [] => .error (.argumentError "precision search did not converge")
    | none :: rest => firstStableRational rest
    | some value :: _ => .ok value) ∧
  (∀ left right, irrationalCompare left right =
    if left == right then .error (.methodError "<") else .ok (left < right)) ∧
  (∀ below approx rational, irrationalRationalLess below approx rational =
    if below then decide (approx < rational) else decide (approx ≤ rational)) ∧
  (∀ op left right, irrationalBinary op left right = op left right) ∧
  (∀ x : IrrationalNearOne, ∀ mode, sourceIrrationalConvert x mode =
    roundNearOne (bigAt256 x) mode) ∧
  (∀ left right, irrationalSameEq left right = true) ∧
  (∀ left right, irrationalCrossEq left right = false) ∧
  (∀ value, irrationalPredicates value = (true, false, false, false)) ∧
  irrationalZero = false ∧ irrationalOne = true ∧
  (∀ negative, irrationalSign negative = if negative then -1 else 1) ∧
  (∀ convert op x, irrationalUnary convert op x = op (convert x))

theorem irrationalCoreBehavior : IrrationalCoreBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · rfl
  · intros; rfl
  · intro tag; cases tag <;> rfl
  · intro samples
    cases samples with
    | nil => rfl
    | cons head tail => cases head <;> rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · rfl
  · rfl
  · intros; rfl
  · intros; rfl

def IrrationalMacroBehavior : Prop :=
  (∀ symbolDefinition, irrationalDeclaration symbolDefinition =
    [.constant, .bigMethod, .float64Method, .float32Method, .assertBig, .assert64, .assert32]) ∧
  (∀ compact symbol digits, irrationalShow compact symbol digits =
    if compact then symbol else symbol ++ " = " ++ digits.take 15 ++ "...") ∧
  (∀ before after matched, irrationalAlignment before after matched =
    if matched then (before, after) else (before + after, 0)) ∧
  (∀ x : Int, (1 / x : Int) = 1 / x)

theorem irrationalMacroBehavior : IrrationalMacroBehavior := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

end Coverage

end JuliaLean.NumMisc
