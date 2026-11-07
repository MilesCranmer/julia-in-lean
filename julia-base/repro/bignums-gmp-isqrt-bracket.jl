# The input is a small, immediately constructible BigInt value.
function reproduced()
    try
        isqrt(BigInt(-1))
        return false
    catch err
        return err isa DivideError
    end
end
println((reproduced() ? "REPRODUCED " : "NOT_REPRODUCED ") * "bignums-gmp-isqrt-bracket")
