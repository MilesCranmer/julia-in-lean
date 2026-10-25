r = (0:5) .* 0.1 .+ 0.3            # StepRangeLen{Float64, TwicePrecision{Float64}, ...}
s = repr(r)
println("repr(r) = ", s)
r2 = eval(Meta.parse(s))
println("collect(r)  = ", collect(r))
println("collect(r2) = ", collect(r2))
println("r == r2: ", r == r2, ", isequal(collect(r), collect(r2)): ", isequal(collect(r), collect(r2)))
r3 = StepRangeLen(0.3, 0.1, 6)      # plain Float64 reference and step
println("repr(StepRangeLen(0.3, 0.1, 6)) = ", repr(r3), "; collect = ", collect(r3), "; reparsed = ", collect(eval(Meta.parse(repr(r3)))))
!isequal(collect(r), collect(r2)) && println("REPRODUCED show-range-repr-elements")
