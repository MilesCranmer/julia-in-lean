# isqrt of a negative BigInt must throw DomainError, like isqrt of a negative Int
function err(f)
    try
        f()
        return nothing
    catch e
        return e
    end
end
e_int = err(() -> isqrt(-4))
e_big = err(() -> isqrt(big(-4)))
println("isqrt(-4)      throws ", typeof(e_int))
println("isqrt(big(-4)) throws ", typeof(e_big))
if e_int isa DomainError && e_big isa DivideError
    println("REPRODUCED bignums-isqrt-negative")
end
