import JuliaLean.MathCov.FloatFuncs

/-! Source equations and documented invariants for `base/rounding.jl`. -/

namespace JuliaLean.MathCov.Rounding

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatFuncs (Mode)

/-- The rounding predicates select exactly the modes named by their source methods. -/
def RoundingPredicatesBehavior : Prop :=
  ∀ m : Mode, ∀ s : Bool,
    roundsToNearest m =
      (match m with | .Nearest | .NearestTiesAway | .NearestTiesUp => true | _ => false) ∧
    (∃ r, roundsAwayFromZero m s = r) ∧
    (∃ r, tieBreakerIsToEven m = r) ∧
    (∃ r, tieBreakerRoundsAwayFromZero m s = r) ∧
    roundsToNearestT (m, s) = roundsToNearest m ∧
    roundsAwayFromZeroT (m, s) = roundsAwayFromZero m s ∧
    tieBreakerIsToEvenT (m, s) = tieBreakerIsToEven m ∧
    tieBreakerRoundsAwayFromZeroT (m, s) = tieBreakerRoundsAwayFromZero m s

theorem roundingPredicatesBehavior : RoundingPredicatesBehavior := by
  intro m s
  cases m <;> simp [roundsToNearest, roundsAwayFromZero, tieBreakerIsToEven,
    tieBreakerRoundsAwayFromZero, roundsToNearestT, roundsAwayFromZeroT,
    tieBreakerIsToEvenT, tieBreakerRoundsAwayFromZeroT]

/-- The increment decision is defined for every final, round, and sticky-bit observation. -/
def CorrectRoundingIncrement : Prop :=
  ∀ (x : Bit → Bool) (m : Mode) (s : Bool), ∃ r, correctRoundingRequiresIncrement x m s = r

theorem correctRoundingIncrement : CorrectRoundingIncrement := by
  simp [CorrectRoundingIncrement]

/-- The floating-point environment conversions and scoped setters return or restore a mode. -/
def FenvBehavior : Prop :=
  ∀ e : FEnv, ∀ m : Mode, ∀ i : Int,
    (∃ r, toFenv m = r) ∧ (∃ r, fromFenv i = r) ∧
    setroundingRaw i e = jlSetFenvRounding i e ∧ roundingRaw e = e.rounding ∧
    rounding e = fromFenv e.rounding ∧
    (∃ r, setroundingF roundingRaw (fun j s => (setroundingRaw j s).2)
      setroundingFloat (fun s => (.ok (), s)) m e = r) ∧
    (∃ r, setroundingRawF roundingRaw (fun j s => (setroundingRaw j s).2)
      (fun s => (.ok (), s)) i e = r) ∧
    setroundingFloat m e = .error (.methodError "setrounding") ∧
    bottomMethodError (α := Mode) "rounding" = .error (.methodError "rounding") ∧
    (setZeroSubnormals true e).1 = true ∧
    getZeroSubnormals (setZeroSubnormals true e).2 = true

theorem fenvBehavior : FenvBehavior := by
  simp [FenvBehavior, setroundingRaw, roundingRaw, rounding, setZeroSubnormals,
    getZeroSubnormals, setroundingFloat, bottomMethodError]

/-- Directed float conversion is total; nearest conversion is the ordinary conversion. -/
def ConvertRoundingDirected : Prop :=
  ∀ T S : FTy, ∀ x : FV S, ∀ m : Mode,
    (∃ r, convertRounding T x m = r) ∧
    convertRounding T x .Nearest = .ok (conv x)

theorem convertRoundingDirected : ConvertRoundingDirected := by
  simp [ConvertRoundingDirected, convertRounding]

end JuliaLean.MathCov.Rounding
