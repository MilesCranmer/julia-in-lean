import JuliaLean.base.cartesian
import JuliaLean.Proofs.base.cartesian.LegacyProofs

namespace JuliaLean.ExprReflect

open JuliaLean

def CartesianMacroBodies : Prop := ∀ kind dimensions,
  cartesianGeneratedCount kind dimensions ≤ dimensions ∧
  (cartesianIndexSequence dimensions).length = dimensions ∧
  (∀ fixed stem, (ncallArguments dimensions fixed stem).length = fixed.length + dimensions) ∧
  (∀ stem source, (nextractShape dimensions stem source).length = dimensions)

theorem cartesianMacroBodies_proven : CartesianMacroBodies := by
  intro kind dimensions
  constructor
  · cases kind <;> by_cases h : dimensions = 0 <;> simp [cartesianGeneratedCount, h]
  constructor
  · simp [cartesianIndexSequence]
  constructor
  · intros; simp [ncallArguments, cartesianIndexSequence]
  · intros; simp [nextractShape, cartesianIndexSequence]

def CartesianSubstitutionBodies : Prop :=
  (∀ stem extension, indexedSymbol stem extension = stem ++ "_" ++ toString extension) ∧
  (∀ a b, resolveArithmetic (.add (.value a) (.value b)) = some (a + b)) ∧
  (∀ a, resolveArithmetic (.neg (.value a)) = some (-a)) ∧
  (∀ symbol pattern value, replaceSymbolModel .quoted symbol pattern value = symbol) ∧
  (∀ only, popLineBlock [only] = some only) ∧
  (∀ whenTrue whenFalse, resolveConditional (some true) whenTrue whenFalse = some whenTrue)

theorem cartesianSubstitutionBodies_proven : CartesianSubstitutionBodies := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.ExprReflect
