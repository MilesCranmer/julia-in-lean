import JuliaLean.Proofs.base.iobuffer.OpProofsSeek
import JuliaLean.Proofs.base.iobuffer.OpProofsRead
import JuliaLean.Proofs.base.iobuffer.OpProofsTruncate

/-!
The operation specifications `SeekSpec`, `SkipSpec`, `OccursinSpec`, `ReadSpec`,
`ReadUntilSpec`, `TakeSpec` and `TruncateSpec`, each proved from the invariant
`∀ io, Reachable io → Inv io`.
-/
