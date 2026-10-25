# x .\ r throws for a floating-point range built by the colon operator.
r = 0.0:0.5:2.0
v = try 2.0 .\ r catch e; e end
println("2.0 .\\ (0.0:0.5:2.0) = ", v isa Exception ? first(split(sprint(showerror, v), '\n')) : v)
println("2.0 .\\ collect(0.0:0.5:2.0) = ", 2.0 .\ collect(r))
println("(0.0:0.5:2.0) ./ 2.0 = ", r ./ 2.0)
if v isa MethodError
    println("REPRODUCED broadcastviews-range-ldiv")
end
