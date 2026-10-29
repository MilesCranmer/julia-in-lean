# range(; stop, step, length) (range_step_stop_length, range.jl:199) computes the start with
# wrapping arithmetic and builds StepRange(start, step, stop); when stop - (length-1)*step
# underflows, the wrapped start lies above stop and the result is empty instead of having
# `length` elements (or throwing).
r = range(stop = typemin(Int) + 1, step = 2, length = 3)
println("r = ", r, ", length(r) = ", length(r))
if length(r) != 3
    println("REPRODUCED range-step-stop-length-count")
else
    error("range-step-stop-length-count did not reproduce")
end
