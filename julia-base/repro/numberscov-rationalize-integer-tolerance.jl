T = Int8
x = 128
tol = 1
q = rationalize(T, x; tol=tol)

println("Julia ", VERSION)
println("rationalize(Int8, 128; tol=1) = ", q)
println("isfinite(result) = ", isfinite(q))
println("127//1 is within tolerance = ", abs(x - 127//1) <= tol)

if q == 1//0 && abs(x - 127//1) <= tol
    println("REPRODUCED numberscov-rationalize-integer-tolerance")
else
    error("bug did not reproduce")
end
