T = Int8
x = 128
tol = 1
q = rationalize(T, x; tol=tol)

println("Julia ", VERSION)
println("rationalize(Int8, 128; tol=1) = ", q)
println("isfinite(result) = ", isfinite(q))
println("127//1 is within tolerance = ", abs(x - 127//1) <= tol)

@assert q == 1//0 && abs(x - 127//1) <= tol

float_x = 128.0
float_tol = 0.0
float_q = rationalize(T, float_x; tol=float_tol)
float_error = abs(float_x - float_q)
println("rationalize(Int8, 128.0; tol=0.0) = ", float_q)
println("floating approximation error = ", float_error)
@assert (float_q == 127//1 && float_error == 1.0) ||
        (float_q == 1//0 && isinf(float_error))
@assert float_error > float_tol
println("REPRODUCED numberscov-rationalize-integer-tolerance")
