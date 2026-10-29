import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.FloatIntCov.Checked
import JuliaLean.FloatIntCov.Div
import JuliaLean.FloatIntCov.Float
import JuliaLean.FloatIntCov.CheckedRows
import JuliaLean.FloatIntCov.DivRows
import JuliaLean.FloatIntCov.FloatRows

namespace JuliaLean.FloatIntCov

open JuliaLean.Registry
open JuliaLean.FloatIntCov.Checked
open JuliaLean.FloatIntCov.Div
open JuliaLean.FloatIntCov.Float

/-- Registry entries of this area. -/
def umbrellaEntries : List Entry := []

def entries : List Entry := umbrellaEntries ++ CheckedRows.entries ++ DivRows.entries ++ FloatRows.entries

end JuliaLean.FloatIntCov
