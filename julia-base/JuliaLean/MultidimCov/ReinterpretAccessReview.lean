import JuliaLean.ArrayCov.ReinterpretAccess
import JuliaLean.ReinterpretArrays.BytesProps
import JuliaLean.ReinterpretArrays.ProofBytes
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry
open JuliaLean.ArrayCov
open JuliaLean.ReinterpretArrays

def RAGetReviewProperty : Prop := ReinterpretGetRoutesCorrect ∧ RaGetCorrect
theorem raGetReviewProperty : RAGetReviewProperty :=
  ⟨reinterpretGetRoutesCorrect, raGetCorrect⟩

def RASetReviewProperty : Prop := ReinterpretSetRoutesCorrect ∧ RaSetCorrect
theorem raSetReviewProperty : RASetReviewProperty :=
  ⟨reinterpretSetRoutesCorrect, raSetCorrect⟩

def RASetZeroProperty : Prop := ∀ scalar convert reinterpret parentSet first set target source array value,
  reinterpret569SetZero scalar convert reinterpret parentSet first set target source array value =
  if scalar target source then do
    let value ← convert value
    let parent ← parentSet array.parent (reinterpret source value)
    pure ⟨parent⟩
  else set array value (first array)
theorem raSetZeroProperty : RASetZeroProperty := by
  simp [RASetZeroProperty, reinterpret569SetZero]

private def raAccessEntry (id fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/reinterpretarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def reinterpretAccessReviewEntries : List Entry := []

end JuliaLean.MultidimCov
