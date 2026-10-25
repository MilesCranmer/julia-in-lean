z = complex(1.0, 2.0^1000)
w = complex(2.0^-40, 0.0)
q = z / w
println("complex(1.0, 2.0^1000) / complex(2.0^-40, 0.0) = ", q)
println("componentwise z / 2.0^-40                       = ", z / real(w))
println("(Inf + 0im) / (1 + 0im) = ", complex(Inf, 0.0) / complex(1.0, 0.0))
if isnan(real(q))
    println("REPRODUCED complex-div-spurious-nan")
end
