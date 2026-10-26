import JuliaLean.Streams.Methods.Libuv
import JuliaLean.Streams.Methods.AsyncEvent
import JuliaLean.Streams.Methods.IOStream
import JuliaLean.Streams.Methods.Process
import JuliaLean.Streams.Methods.Stream

namespace JuliaLean.Streams.Methods

def entries :=
  Libuv.entries ++ AsyncEvent.entries ++ IOStream.entries ++ Process.entries ++ Stream.entries

end JuliaLean.Streams.Methods
