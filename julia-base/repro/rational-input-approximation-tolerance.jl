x = 128 // 1
tol = eps(float(x)) / 2
q = rationalize(Int8, x; tol=tol)
err = abs(float(x) - float(q))
println("Julia ", VERSION)
println("rationalize(Int8, 128//1; tol=eps(128.0)/2) = ", q)
println("tolerance = ", tol, ", error = ", err)
@assert !isfinite(q) || err > tol
println("REPRODUCED rational-input-approximation-tolerance")
