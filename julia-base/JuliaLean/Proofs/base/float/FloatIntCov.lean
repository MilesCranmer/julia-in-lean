import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.checked.FloatIntCov
import JuliaLean.Proofs.base.div.FloatIntCov
import JuliaLean.Proofs.base.float.FloatIntCovModels
import JuliaLean.Proofs.base.checked.Rows
import JuliaLean.Proofs.base.div.FloatIntCovRows
import JuliaLean.Proofs.base.float.FloatIntCovRows

namespace JuliaLean.FloatIntCov

open JuliaLean.Registry
open JuliaLean.FloatIntCov.Checked
open JuliaLean.FloatIntCov.Div
open JuliaLean.FloatIntCov.Float

/-- Registry entries of this area. -/
def umbrellaEntries : List Entry := []

def entries : List Entry := umbrellaEntries ++ CheckedRows.entries ++ DivRows.entries ++ FloatRows.entries

end JuliaLean.FloatIntCov
