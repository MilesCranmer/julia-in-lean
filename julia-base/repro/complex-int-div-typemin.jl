q = Complex(1, 0) / Complex(typemin(Int), 0)
println("Complex(1, 0) / Complex(typemin(Int), 0) = ", q)
println("1 / typemin(Int)                         = ", 1 / typemin(Int))
println("Complex(1, 0) / Complex(0, typemin(Int)) = ", Complex(1, 0) / Complex(0, typemin(Int)))
if isnan(real(q))
    println("REPRODUCED complex-int-div-typemin")
end
