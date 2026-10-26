task = @async asyncmap(identity, 1:1; ntasks=() -> -1)
status = timedwait(() -> istaskdone(task), 1.0; pollint=0.01)
println("asyncmap status after one second: ", status)

if status == :timed_out
    schedule(task, ErrorException("reproducer cleanup"); error=true)
    wait(task; throw=false)
    println("REPRODUCED tasks-asyncmap-negative-ntasks-function")
end
