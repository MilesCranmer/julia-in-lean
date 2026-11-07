import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range.coverage.colon
import JuliaLean.Proofs.base.range.coverage.access
import JuliaLean.Proofs.base.range.coverage.compare
import JuliaLean.Proofs.base.range.coverage.convert
import JuliaLean.Proofs.base.range.coverage.ops
import JuliaLean.Proofs.base.twiceprecision.coverage.operations
import JuliaLean.Proofs.base.range.coverage.floats
import JuliaLean.Proofs.base.range.coverage.log
import JuliaLean.Proofs.base.range.coverage.methods
import JuliaLean.Proofs.base.range.coverage.methods2
import JuliaLean.Proofs.base.range.coverage.dispatch
import JuliaLean.Proofs.base.range.coverage.access_methods
import JuliaLean.Proofs.base.range.coverage.conversions_methods
import JuliaLean.Proofs.base.range.coverage.tail_methods
import JuliaLean.Proofs.base.twiceprecision.coverage.methods

namespace JuliaLean.RangesCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := Colon.entries ++ Access.entries ++ Compare.entries ++ Convert.entries ++ Ops.entries ++ Twice.entries ++ Floats.entries ++ Log.entries ++ Methods.entries ++ Methods2.entries ++ Dispatch.entries ++ AccessMethods.entries ++ ConversionsMethods.entries ++ TailMethods.entries ++ TwiceMethods.entries

end JuliaLean.RangesCov
