import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.abstractarray
import JuliaLean.Proofs.base.abstractarray.specifications
import JuliaLean.Proofs.base.abstractarray.contract_refutations
import JuliaLean.Proofs.base.abstractarray.ordinary_indexing
import JuliaLean.Proofs.base.abstractarray.zero_index
import JuliaLean.Proofs.base.abstractarray.copy_contents
import JuliaLean.Proofs.base.abstractarray.copy_methods
import JuliaLean.Proofs.base.abstractarray.circshift
import JuliaLean.Proofs.base.abstractarray.map_n
import JuliaLean.Proofs.base.abstractarray.concatenation_entries
import JuliaLean.Proofs.base.abstractarray.typed_concatenation

namespace JuliaLean.AbstractArraySpecs

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
] ++ catEntries

end JuliaLean.AbstractArraySpecs
