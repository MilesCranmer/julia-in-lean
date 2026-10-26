r = LinRange(0.0, 1.0, 7)
x = 2.0
actual_add = collect(r .+ x)
expected_add = collect(r) .+ x
actual_sub = collect(r .- x)
expected_sub = collect(r) .- x

println("collect(r .+ x) = ", actual_add)
println("collect(r) .+ x = ", expected_add)
println("collect(r .- x) = ", actual_sub)
println("collect(r) .- x = ", expected_sub)

(actual_add != expected_add && actual_sub != expected_sub) &&
    println("REPRODUCED broadcastcov-linrange-shift-elementwise")
