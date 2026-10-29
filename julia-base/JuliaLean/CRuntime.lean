import JuliaLean.CRuntime.Memory
import JuliaLean.CRuntime.Types
import JuliaLean.CRuntime.ParallelMark.Core
import JuliaLean.CRuntime.ParallelMark.Bounds
import JuliaLean.CRuntime.ParallelMark.PrimitiveRace
import JuliaLean.CRuntime.ParallelMark.Deque
import JuliaLean.CRuntime.ParallelMark.ActualCapacity.Source
import JuliaLean.CRuntime.Finalizers.Core
import JuliaLean.CRuntime.WorldStop
import JuliaLean.CRuntime.WriteBarrier
import JuliaLean.CRuntime.PagePool

namespace JuliaLean.CRuntime

def entries : List JuliaLean.Registry.Entry :=
  WorldStop.entries ++ WriteBarrier.entries ++ PagePool.entries

end JuliaLean.CRuntime
