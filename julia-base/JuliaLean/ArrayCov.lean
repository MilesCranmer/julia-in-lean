import JuliaLean.Registry.Types
import JuliaLean.ArrayCov.Model
import JuliaLean.ArrayCov.Simple
import JuliaLean.ArrayCov.Construct
import JuliaLean.ArrayCov.ReshapedSimple
import JuliaLean.ArrayCov.ReinterpretSimple
import JuliaLean.ArrayCov.ReshapedShape
import JuliaLean.ArrayCov.ReinterpretCartesian
import JuliaLean.ArrayCov.ReshapeCore
import JuliaLean.ArrayCov.ReshapedIndex
import JuliaLean.ArrayCov.ReshapedPointers
import JuliaLean.ArrayCov.ReinterpretConstruct
import JuliaLean.ArrayCov.ReinterpretShape
import JuliaLean.ArrayCov.ReinterpretAccess
import JuliaLean.ArrayCov.ReinterpretPadding
import JuliaLean.ArrayCov.ArrayCore
import JuliaLean.ArrayCov.ArrayWrap
import JuliaLean.ArrayCov.ArrayFind
import JuliaLean.ArrayCov.ArrayMisc
import JuliaLean.ArrayCov.ArrayIndex
import JuliaLean.ArrayCov.ArrayPush
import JuliaLean.ArrayCov.ArrayDeleteRoutes
import JuliaLean.ArrayCov.ArrayFilterSet
import JuliaLean.ArrayCov.ArrayIndcopy
import JuliaLean.ArrayCov.ArrayCollect
import JuliaLean.ArrayCov.ArrayGrowth
import JuliaLean.MemSafety.G4.Proofs

namespace JuliaLean.ArrayCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := []

end JuliaLean.ArrayCov
