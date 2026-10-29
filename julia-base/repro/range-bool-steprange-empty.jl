# StepRange(false, -1, true) counts down from false towards true, so it has no elements.
# steprange_last_empty(start::Bool, step, stop) (range.jl:399) returns `start` for a negative step,
# which makes the stored last element equal to the start: the range has one element, `false`.
r = StepRange(false, -1, true)
got = collect(r)
want = Bool[x for x in (0:-1:1)]
println("collect(StepRange(false, -1, true)) = ", got, ", length ", length(r), ", expected ", want)
if got != want
    println("REPRODUCED range-bool-steprange-empty")
else
    error("range-bool-steprange-empty did not reproduce")
end
