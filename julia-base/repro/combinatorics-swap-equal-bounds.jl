A = zeros(2, 2)
results = Any[
    Base.swapcols!(A, 3, 3),
    Base.swaprows!(A, 3, 3),
]

println("swapcols!(A, 3, 3): ", repr(results[1]))
println("swaprows!(A, 3, 3): ", repr(results[2]))
println("axes(A):             ", repr(axes(A)))

if results == [nothing, nothing]
    println("REPRODUCED combinatorics-swap-equal-bounds")
end
