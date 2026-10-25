import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Ranges.Ordinal
import JuliaLean.Ranges.Keywords
import JuliaLean.Ranges.Operations
import JuliaLean.Ranges.Counted
import JuliaLean.Ranges.Hash
import JuliaLean.Ranges.FullWidth

namespace JuliaLean.Ranges

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry :=
  ordinalEntries ++ keywordEntries ++ operationsEntries ++ countedEntries ++ hashEntries
    ++ fullWidthEntries

end JuliaLean.Ranges
