# Threads.threadpooldescription labels the first adopted foreign thread "foreign: gc".
# GC threads occupy the jl_n_gcthreads ids after the interactive and default pools, but
# the description uses ngcthreads() == jl_n_gcthreads + 1 as the width of that range.
const FOREIGN_TID = Ref(0)
function foreign_entry(::Ptr{Cvoid})::Ptr{Cvoid}
    FOREIGN_TID[] = Threads.threadid()
    return C_NULL
end
entry = @cfunction(foreign_entry, Ptr{Cvoid}, (Ptr{Cvoid},))
handle = Ref{UInt}(0)
@assert ccall(:pthread_create, Cint, (Ptr{UInt}, Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}),
              handle, C_NULL, entry, C_NULL) == 0
ccall(:pthread_join, Cint, (UInt, Ptr{Cvoid}), handle[], C_NULL)

tid = FOREIGN_TID[]
n_others = Threads.nthreads(:interactive) + Threads.nthreads(:default)
gc_threads = unsafe_load(cglobal(:jl_n_gcthreads, Cint))  # GC threads have ids n_others .+ (1:gc_threads)
desc = Threads.threadpooldescription(tid)
println("pools: interactive=", Threads.nthreads(:interactive), " default=", Threads.nthreads(:default),
        " gc threads=", gc_threads, " ngcthreads()=", Threads.ngcthreads())
println("adopted foreign thread id = ", tid, ", threadpool = ", Threads.threadpool(tid))
println("threadpooldescription(", tid, ") = ", repr(desc))
is_gc_thread = n_others < tid <= n_others + gc_threads
println("thread is a GC thread: ", is_gc_thread)
println(!is_gc_thread && desc == "foreign: gc" ?
    "REPRODUCED concurrencycov-threadpooldescription-gc-range" :
    "NOT REPRODUCED concurrencycov-threadpooldescription-gc-range")
