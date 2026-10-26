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

def reinterpretAccessReviewEntries : List Entry := [
  raAccessEntry "multidimcov-reinterpretarray-get-access" "getindex and _getindex methods" "Every get route checks readability and bounds in source order, selects pointer, scalar, or byte assembly, and returns exactly the target element bytes." "base/reinterpretarray.jl:433-567" ``RAGetReviewProperty ``raGetReviewProperty,
  raAccessEntry "multidimcov-reinterpretarray-set-zero" "setindex!(::NonReshapedReinterpretArray{T,0})" "Zero-dimensional assignment selects scalar parent reinterpretation or the first-index route after conversion." "base/reinterpretarray.jl:569-575" ``RASetZeroProperty ``raSetZeroProperty,
  raAccessEntry "multidimcov-reinterpretarray-set-access" "setindex! and _setindex! methods" "Every set route checks writability and bounds, converts the value, selects pointer, scalar, or byte assembly, changes exactly the target bytes, and returns the view." "base/reinterpretarray.jl:577-731" ``RASetReviewProperty ``raSetReviewProperty
]

end JuliaLean.MultidimCov
