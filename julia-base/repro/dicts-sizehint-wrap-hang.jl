# sizehint!(d, n) with 3n beyond typemax(Int): the requested table size wraps to
# 16 slots, and rehash! loops forever once d has more than 16 entries.
# The call runs in a child process that is killed after 30 seconds.
n = 2^62
println("3n = ", 3 * n, ", table size requested = ", Base._tablesz(cld(3 * n, 2)))
code = "d = Dict(i => i for i in 1:17); sizehint!(d, $n); println(\"returned \", length(d))"
p = run(pipeline(`$(Base.julia_cmd()) --startup-file=no -e $code`; stderr = devnull); wait = false)
t0 = time()
while process_running(p) && time() - t0 < 30
    sleep(0.2)
end
hung = process_running(p)
if hung
    kill(p, Base.SIGKILL)
    wait(p)
end
println("sizehint!(Dict with 17 entries, 2^62): ", hung ? "still running after 30 s" : "finished with exit code $(p.exitcode)")
hung && println("REPRODUCED dicts-sizehint-wrap-hang")
