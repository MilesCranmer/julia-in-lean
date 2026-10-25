import JuliaLean.IOBuffers.InvProofs
import JuliaLean.IOBuffers.OpProofs
import JuliaLean.IOBuffers.WriteProofs

/-!
The proven `IOBuffer` properties, with the invariant of every reachable buffer
(`reachable_inv`) discharged.
-/

namespace JuliaLean.IOBuffers

theorem seekSpec : SeekSpec := seekSpec_of_inv reachable_inv
theorem skipSpec : SkipSpec := skipSpec_of_inv reachable_inv
theorem truncateSpec : TruncateSpec := truncateSpec_of_inv reachable_inv
theorem takeSpec : TakeSpec := takeSpec_of_inv reachable_inv
theorem readSpec : ReadSpec := readSpec_of_inv reachable_inv
theorem readUntilSpec : ReadUntilSpec := readUntilSpec_of_inv reachable_inv
theorem occursinSpec : OccursinSpec := occursinSpec_of_inv reachable_inv
theorem writeAtPosition : WriteAtPosition := writeAtPosition_of_inv reachable_inv
theorem appendWritesAtEnd : AppendWritesAtEnd := appendWritesAtEnd_of_inv reachable_inv
theorem writeReadRoundtrip : WriteReadRoundtrip := writeReadRoundtrip_of_inv reachable_inv
theorem pipeFIFO : PipeFIFO := pipeFIFO_of_inv reachable_inv
theorem pipeMarkReset : PipeMarkReset := pipeMarkReset_of_inv reachable_inv

end JuliaLean.IOBuffers
