# Base.RangeStepStyle(x) for a value or type that is not a range never returns.
# RangeStepStyle(instance) = RangeStepStyle(typeof(instance)) (base/traits.jl:72)
# and the only type methods are for AbstractRange and Union{}, so a non-range
# type T (an instance of DataType) goes back to the instance method, which calls
# RangeStepStyle(DataType), RangeStepStyle(DataType), ... forever.
# The call runs in a child process that is killed after 30 seconds.
code = "Base.RangeStepStyle(1)"
p = run(pipeline(`$(Base.julia_cmd()) --startup-file=no -e $code`; stdout=devnull, stderr=devnull); wait=false)
t0 = time()
while process_running(p) && time() - t0 < 30
    sleep(0.5)
end
hung = process_running(p)
hung && (kill(p); wait(p))
println("Base.RangeStepStyle(1): ", hung ? "still running after 30 s (killed)" : "exited with code $(p.exitcode)")
# The sibling traits return or throw at once for non-range types.
println("Base.ArithmeticStyle(1) = ", Base.ArithmeticStyle(1))
if hung
    println("REPRODUCED reducecov-rangestepstyle-hang")
end
