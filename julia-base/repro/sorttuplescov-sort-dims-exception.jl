A = [3 1; 2 4]
caught(f) = try f(); nothing catch e; typeof(e) end
e3 = caught(() -> sort!(copy(A); dims=3))
e0 = caught(() -> sort!(copy(A); dims=0))
e0s = caught(() -> sort!(copy(A); dims=0, scratch=nothing))
println(e3, " ", e0, " ", e0s)
if e3 === ArgumentError && e0s === ArgumentError && e0 !== ArgumentError
    println("REPRODUCED sorttuplescov-sort-dims-exception")
end
