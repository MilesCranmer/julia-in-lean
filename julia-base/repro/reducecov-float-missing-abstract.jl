# float(A) for A::AbstractArray{Union{T, Missing}} with an abstract T converts every
# element to typeof(float(zero(T))), which is Float64 for T = Real or Integer, so BigFloat
# entries are rounded and large BigInt entries become Inf. float(A) without missing
# refuses abstract element types, and float on the concrete arrays keeps BigFloat.
a = float(Union{Missing, Real}[big"1.1", missing])
b = float(Union{Missing, Integer}[big(10)^400, missing])
println("float(Union{Missing, Real}[big\"1.1\", missing]) = ", repr(a))
println("float(Union{Missing, Integer}[big(10)^400, missing]) = ", repr(b))
println("float([big\"1.1\"])[1] == big\"1.1\": ", float([big"1.1"])[1] == big"1.1")
println("float([big(10)^400])[1] == big(10)^400: ", float([big(10)^400])[1] == big(10)^400)
c = try
    float(Real[big"1.1"])
catch e
    e
end
println("float(Real[big\"1.1\"]) -> ", c isa Exception ? typeof(c) : repr(c))
if a[1] != big"1.1" && isinf(b[1])
    println("REPRODUCED reducecov-float-missing-abstract")
end
