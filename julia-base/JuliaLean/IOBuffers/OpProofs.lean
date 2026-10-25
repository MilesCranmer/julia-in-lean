import JuliaLean.IOBuffers.OpProofsSeek
import JuliaLean.IOBuffers.OpProofsRead
import JuliaLean.IOBuffers.OpProofsTruncate

/-!
The operation specifications `SeekSpec`, `SkipSpec`, `OccursinSpec`, `ReadSpec`,
`ReadUntilSpec`, `TakeSpec` and `TruncateSpec`, each proved from the invariant
`∀ io, Reachable io → Inv io`.
-/
