import JuliaLean.ReduceCov.TraitsEntries
import JuliaLean.ReduceCov.IndicesEntries
import JuliaLean.ReduceCov.SomeRows
import JuliaLean.ReduceCov.MissingRows
import JuliaLean.ReduceCov.ReduceRows
import JuliaLean.ReduceCov.ReducedimRows

namespace JuliaLean.ReduceCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry :=
  TraitsEntries.entries ++ IndicesEntries.entries ++ SomeRows.entries ++
  MissingCov.entries ++ ReduceRows.entries ++ ReducedimRows.entries

end JuliaLean.ReduceCov
