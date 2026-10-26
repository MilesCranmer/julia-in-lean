source = "Base.Cartesian.@nloops 2 i A body"
result = try
    macroexpand(Main, Meta.parse(source))
catch err
    err
end

println("source: ", source)
println("macroexpand result type: ", typeof(result))

if result isa MethodError && result.f === Base.Cartesian._nloops
    println("REPRODUCED exprreflect-nloops-atomic-body")
else
    println("NOT REPRODUCED exprreflect-nloops-atomic-body")
end
