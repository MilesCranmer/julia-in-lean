x = hypot(3.0, 4.0, 12.0)
y = try
    @fastmath hypot(3.0, 4.0, 12.0)
catch err
    err
end

println("hypot(3.0, 4.0, 12.0) = ", x)
println("@fastmath hypot(3.0, 4.0, 12.0) = ", repr(y))
if x == 13.0 && y isa MethodError
    println("REPRODUCED nummisc-fastmath-hypot-varargs")
end
