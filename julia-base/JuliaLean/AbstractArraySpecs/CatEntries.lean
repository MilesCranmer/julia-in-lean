import JuliaLean.Registry.Types
import JuliaLean.AbstractArraySpecs.CatRowsRefute
import JuliaLean.AbstractArraySpecs.CatHelpers
import JuliaLean.AbstractArraySpecs.HvnScalar
import JuliaLean.AbstractArraySpecs.CatOrdinaryLemmas

namespace JuliaLean.AbstractArraySpecs

open JuliaLean.Registry

/-- Separate front-end contracts; all use the documented positional concatenation,
not equality with a delegated method. Each refutation evaluates its own row's model. -/
def catEntries : List Entry := []

end JuliaLean.AbstractArraySpecs
