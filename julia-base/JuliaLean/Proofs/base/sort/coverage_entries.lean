import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.ordering.value_order
import JuliaLean.Proofs.base.pair.value_pair
import JuliaLean.Proofs.base.tuple.sort_tuple_correct
import JuliaLean.Proofs.base.namedtuple.sort_namedtuple_correct
import JuliaLean.Proofs.base.sort.compatibility_properties
import JuliaLean.Proofs.base.tuple.sort_tuple_coverage
import JuliaLean.Proofs.base.ntuple.sort_ntuple
import JuliaLean.Proofs.base.namedtuple.sort_namedtuple_coverage
import JuliaLean.Proofs.base.sort.compatibility_kernels
import JuliaLean.Proofs.base.sort.method_coverage
import JuliaLean.Proofs.base.ordering.generic_order
import JuliaLean.Proofs.base.pair.generic_pair

namespace JuliaLean.SortTuplesCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := []

end JuliaLean.SortTuplesCov
