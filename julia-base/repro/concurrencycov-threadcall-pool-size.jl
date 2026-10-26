# The @threadcall docstring says its concurrency "can be increased by setting the
# UV_THREADPOOL_SIZE environment variable and restarting the julia process", but the
# semaphore that limits it is a constant computed when the system image was built.
if !haskey(ENV, "THREADCALL_CHILD")
    cmd = addenv(`$(Base.julia_cmd()) --startup-file=no $(@__FILE__)`,
                 "THREADCALL_CHILD" => "1", "UV_THREADPOOL_SIZE" => "8")
    print(read(cmd, String))
    exit()
end
println("UV_THREADPOOL_SIZE = ", ENV["UV_THREADPOOL_SIZE"])
println("Base.max_ccall_threads = ", Base.max_ccall_threads)
println("threadcall semaphore size = ", Base.threadcall_restrictor.sem_size)
# warm up, then run 8 one-second sleeps at once
@threadcall(:usleep, Cint, (Cuint,), 1)
t = @elapsed @sync for i in 1:8
    @async @threadcall(:sleep, Cuint, (Cuint,), 1)
end
println("8 concurrent 1 s threadcalls took ", round(t; digits=1), " s")
println(Base.threadcall_restrictor.sem_size != 8 && t > 1.5 ?
    "REPRODUCED concurrencycov-threadcall-pool-size" :
    "NOT REPRODUCED concurrencycov-threadcall-pool-size")
