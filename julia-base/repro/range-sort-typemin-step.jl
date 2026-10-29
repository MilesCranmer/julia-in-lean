# sort(r::AbstractRange) (range.jl:1463) returns reverse(r) for a descending range; reversing a step
# range negates the step, which wraps for typemin, so the sorted range is empty.
r = Int8(0):Int8(-128):Int8(-128)
got = collect(sort(r))
want = sort(collect(r))
println("collect(r) = ", collect(r), ", collect(sort(r)) = ", got, ", expected ", want)
if got != want
    println("REPRODUCED range-sort-typemin-step")
else
    error("range-sort-typemin-step did not reproduce")
end
