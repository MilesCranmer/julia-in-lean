t = count((true, false); init=0.0)
r = try
    count([true, false]; init=0.0)
catch err
    err
end
println(repr(t), " ", r isa Exception ? typeof(r) : repr(r))
if t === 1.0 && r isa MethodError
    println("REPRODUCED reduce-count-init-float")
end
