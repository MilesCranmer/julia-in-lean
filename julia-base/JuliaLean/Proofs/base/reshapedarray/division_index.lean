import JuliaLean.Proofs.base.reshapedarray.index_properties
import JuliaLean.Proofs.base.multinverses.signed

namespace JuliaLean.ReinterpretArrays

/-- `ReshapedArray` index conversion with `SignedMultiplicativeInverse` division is correct. -/
theorem ind2subCorrect : Ind2subCorrect := ind2subCorrect_of smiDivCorrect

end JuliaLean.ReinterpretArrays
