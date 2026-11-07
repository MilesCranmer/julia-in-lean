import JuliaLean.Proofs.base.tuple.properties
import JuliaLean.Proofs.base.tuple.compare

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- Reuse the complete short/Any32 Tuple and NamedTuple hash proof. -/
def TupleHashConsistency : Prop := JuliaLean.Tuples.HashIsequal

theorem tupleHashConsistency_proven : TupleHashConsistency :=
  JuliaLean.Tuples.hashIsequal

end JuliaLean.HashOps
