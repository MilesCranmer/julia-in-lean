z = complex(49.0, 0.0)
q = z / complex(49.0, 0.0)
r = z / 49.0
println("complex(49.0, 0.0) / complex(49.0, 0.0) = ", q)
println("complex(49.0, 0.0) / 49.0               = ", r)
if q != r && q != 1
    println("REPRODUCED complex-div-real-divisor")
end
