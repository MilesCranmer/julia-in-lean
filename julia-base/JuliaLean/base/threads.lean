import JuliaLean.base.threadingconstructs
import JuliaLean.base.locks_mt

/-!
# Threads module loader

The two includes load their separate source models. The Julia `Condition`
binding is completed by lock.jl; separate Lean namespaces prevent accidental
lookup of the single-threaded Base.Condition binding. This source file defines
no Julia methods.

Julia source: base/threads.jl:1-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

"""
Multithreading support.
"""
module Threads

global Condition # we'll define this later, make sure we don't import Base.Condition

include("threadingconstructs.jl")
include("locks-mt.jl")

end
```
-/
namespace JuliaLean.base.threads
export JuliaLean.base.threadingconstructs (threadid maxthreadid nthreads threadpool threadpoolsize threadpooltids nthreadpools ngcthreads)
export JuliaLean.base.locks_mt (SpinLock PaddedSpinLock)
end JuliaLean.base.threads
