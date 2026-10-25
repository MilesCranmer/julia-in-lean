import JuliaLean.IOBuffers.WriteProofsApp
import JuliaLean.IOBuffers.WriteProofsSeq

/-! Write properties of `IOBuffer`, assuming every reachable buffer satisfies `Inv`. -/

namespace JuliaLean.IOBuffers

theorem writeAtPosition_of_inv (hinv : ∀ io, Reachable io → Inv io) : WriteAtPosition :=
  WriteP.writeAtPosition' hinv

theorem appendWritesAtEnd_of_inv (hinv : ∀ io, Reachable io → Inv io) : AppendWritesAtEnd :=
  WriteP.appendWritesAtEnd' hinv

theorem writeReadRoundtrip_of_inv (hinv : ∀ io, Reachable io → Inv io) : WriteReadRoundtrip :=
  WriteP.writeReadRoundtrip' hinv

theorem pipeFIFO_of_inv (_hinv : ∀ io, Reachable io → Inv io) : PipeFIFO :=
  WriteP.pipeFIFO'

theorem pipeMarkReset_of_inv (_hinv : ∀ io, Reachable io → Inv io) : PipeMarkReset :=
  WriteP.pipeMarkReset'

end JuliaLean.IOBuffers
