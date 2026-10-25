r = try
    evalpoly(2.0, ())
catch err
    err
end
println("evalpoly(2.0, ()) = ", r)
s = try
    evalpoly(2.0, Float64[])
catch err
    err
end
println("evalpoly(2.0, Float64[]) = ", s)
if !(r == 0.0 && s == 0.0)
    println("REPRODUCED mathfuncs-evalpoly-empty")
end
