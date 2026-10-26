import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RangesCov.Colon
import JuliaLean.RangesCov.Access
import JuliaLean.RangesCov.Compare
import JuliaLean.RangesCov.Convert
import JuliaLean.RangesCov.Ops
import JuliaLean.RangesCov.Twice
import JuliaLean.RangesCov.Floats
import JuliaLean.RangesCov.Log
import JuliaLean.RangesCov.Methods
import JuliaLean.RangesCov.Methods2
import JuliaLean.RangesCov.Dispatch
import JuliaLean.RangesCov.AccessMethods
import JuliaLean.RangesCov.ConversionsMethods
import JuliaLean.RangesCov.TailMethods
import JuliaLean.RangesCov.TwiceMethods

namespace JuliaLean.RangesCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := Colon.entries ++ Access.entries ++ Compare.entries ++ Convert.entries ++ Ops.entries ++ Twice.entries ++ Floats.entries ++ Log.entries ++ Methods.entries ++ Methods2.entries ++ Dispatch.entries ++ AccessMethods.entries ++ ConversionsMethods.entries ++ TailMethods.entries ++ TwiceMethods.entries

end JuliaLean.RangesCov
