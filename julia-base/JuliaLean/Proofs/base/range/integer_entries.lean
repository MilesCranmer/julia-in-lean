import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range.integer_ordinal
import JuliaLean.Proofs.base.range.integer_keywords
import JuliaLean.Proofs.base.range.integer_operations
import JuliaLean.Proofs.base.range.integer_counted
import JuliaLean.Proofs.base.multidimensional.range_hash
import JuliaLean.Proofs.base.range.integer_full_width

namespace JuliaLean.Ranges

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry :=
  ordinalEntries ++ keywordEntries ++ operationsEntries ++ countedEntries ++ hashEntries
    ++ fullWidthEntries

end JuliaLean.Ranges
