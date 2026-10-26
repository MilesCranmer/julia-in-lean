r = range(0.0; step=0.25, length=6)
x = 3.0
actual = collect(r ./ x)
expected = collect(r) ./ x

println("collect(r ./ x) = ", actual)
println("collect(r) ./ x = ", expected)

actual != expected && println("REPRODUCED broadcastcov-steprangelen-div-elementwise")
