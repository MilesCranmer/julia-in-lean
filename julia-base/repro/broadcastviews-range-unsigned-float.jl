# Broadcasting an unsigned range with a floating-point scalar returns wrong elements or throws.
r = UInt(1):UInt(2):UInt(5)
a = r .- 2.0
b = collect(r) .- 2.0
println("(UInt(1):UInt(2):UInt(5)) .- 2.0 = ", collect(a))
println("collect(UInt(1):UInt(2):UInt(5)) .- 2.0 = ", b)
c = try -2.0 .* (UInt(1):UInt(3)) catch e; e end
println("-2.0 .* (UInt(1):UInt(3)) = ", c isa Exception ? sprint(showerror, c) : collect(c))
println("-2.0 .* collect(UInt(1):UInt(3)) = ", -2.0 .* collect(UInt(1):UInt(3)))
if collect(a) != b || c isa Exception
    println("REPRODUCED broadcastviews-range-unsigned-float")
end
