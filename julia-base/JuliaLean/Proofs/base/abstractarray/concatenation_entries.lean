import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.abstractarray.concatenation_refutations
import JuliaLean.Proofs.base.abstractarray.concatenation_helpers
import JuliaLean.Proofs.base.abstractarray.scalar_concatenation
import JuliaLean.Proofs.base.abstractarray.concatenation_ordinary

namespace JuliaLean.AbstractArraySpecs

open JuliaLean.Registry

/-- Separate front-end contracts; all use the documented positional concatenation,
not equality with a delegated method. Each refutation evaluates its own row's model. -/
def catEntries : List Entry := []

end JuliaLean.AbstractArraySpecs
