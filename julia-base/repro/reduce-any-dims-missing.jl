whole = any([missing, false])
r = try
    any([missing false]; dims=2)
catch err
    err
end
println(repr(whole), " ", r isa Exception ? typeof(r) : repr(r))
if whole === missing && r isa TypeError
    println("REPRODUCED reduce-any-dims-missing")
end
