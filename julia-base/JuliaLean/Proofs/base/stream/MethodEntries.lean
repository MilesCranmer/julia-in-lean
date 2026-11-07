import JuliaLean.Proofs.base.libuv.StreamMethods
import JuliaLean.Proofs.base.asyncevent.StreamMethods
import JuliaLean.Proofs.base.iostream.StreamMethods
import JuliaLean.Proofs.base.process.StreamMethods
import JuliaLean.Proofs.base.stream.Methods

namespace JuliaLean.Streams.Methods

def entries :=
  Libuv.entries ++ AsyncEvent.entries ++ IOStream.entries ++ Process.entries ++ Stream.entries

end JuliaLean.Streams.Methods
