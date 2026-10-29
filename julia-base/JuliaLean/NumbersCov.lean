import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.NumbersCov.Proofs
import JuliaLean.NumbersCov.Rows.NumberEntries
import JuliaLean.NumbersCov.Rows.OperatorsEntries
import JuliaLean.NumbersCov.Rows.PromotionEntries
import JuliaLean.NumbersCov.Rows.RationalEntries
import JuliaLean.NumbersCov.Rows.ComplexEntries

namespace JuliaLean.NumbersCov

open JuliaLean.Registry

/-- Registry entries covering every method definition in the five owned Base files. -/
def entries : List Entry := [] ++ JuliaLean.NumbersCov.Rows.Number.entries
  ++ JuliaLean.NumbersCov.Rows.Operators.entries
  ++ JuliaLean.NumbersCov.Rows.Promotion.entries
  ++ JuliaLean.NumbersCov.Rows.Rational.entries
  ++ JuliaLean.NumbersCov.Rows.Complex.entries

end JuliaLean.NumbersCov
