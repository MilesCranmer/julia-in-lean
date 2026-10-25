x = nextfloat(0.0)                   # 5.0e-324
a = ceil(x; digits=-1)
b = floor(-x; digits=-1)
c = round(x, RoundFromZero; digits=-1)
println("ceil(5.0e-324; digits=-1) = ", a)
println("floor(-5.0e-324; digits=-1) = ", b)
println("round(5.0e-324, RoundFromZero; digits=-1) = ", c)
println("ceil(1.0e-310; digits=-1) = ", ceil(1.0e-310; digits=-1))
println("ceil(1.0e-30; digits=-300) = ", ceil(1.0e-30; digits=-300))
println("ceil(5.0e-324; digits=0) = ", ceil(x; digits=0))
if a == 0 && b == 0 && c == 0
    println("REPRODUCED floatfuncs-digits-step-underflow")
end
