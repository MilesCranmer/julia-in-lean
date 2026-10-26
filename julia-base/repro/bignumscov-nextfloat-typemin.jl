function outcome(fn)
    code = "Base.$fn(big(1.0), typemin(Int))"
    proc = run(pipeline(`$(Base.julia_cmd()) --startup-file=no -e $code`,
                        stdout=devnull, stderr=devnull); wait=false)
    status = timedwait(() -> process_exited(proc), 2.0)
    if status == :timed_out
        kill(proc)
        wait(proc)
        return "hangs"
    end
    return "returned"
end

next_result = outcome("nextfloat")
prev_result = outcome("prevfloat")

println("nextfloat(big(1.0), typemin(Int)) -> ", next_result)
println("prevfloat(big(1.0), typemin(Int)) -> ", prev_result)

if next_result == "hangs" && prev_result == "hangs"
    println("REPRODUCED bignumscov-nextfloat-typemin")
end
