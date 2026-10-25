n = typemin(Int)
println("2.0^n = ", 2.0^n)
r = try
    complex(2.0, 0.0)^n
catch e
    e
end
println("complex(2.0, 0.0)^n = ", r)
if r isa DomainError
    println("REPRODUCED complex-pow-typemin")
end
