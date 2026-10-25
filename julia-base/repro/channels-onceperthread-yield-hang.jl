# A OncePerThread initializer that yields, while another task on the same thread
# calls the object, hangs both tasks. Run in a child process with a timeout.
code = """
const o = Base.OncePerThread{Int}(() -> (yield(); 42))
t = @async o()
yield()              # t starts the initializer, which yields back here
println(o())         # spins forever without yielding
println(fetch(t))
"""
cmd = `$(Base.julia_cmd()) --startup-file=no -t 1 -e $code`
out = IOBuffer()
p = run(pipeline(ignorestatus(cmd), stdout=out, stderr=devnull), wait=false)
status = timedwait(() -> process_exited(p), 20)
if status === :timed_out
    kill(p, Base.SIGKILL)
    println("child still running after 20 s")
    println("REPRODUCED channels-onceperthread-yield-hang")
else
    print("child finished: ", String(take!(out)))
end
