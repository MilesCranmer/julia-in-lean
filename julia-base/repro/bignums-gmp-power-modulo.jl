# The input is a small, immediately constructible BigInt value.
function reproduced()
    try
        powermod(BigInt(2), BigInt(-1), BigInt(4))
        return false
    catch err
        return err isa DivideError
    end
end
println((reproduced() ? "REPRODUCED " : "NOT_REPRODUCED ") * "bignums-gmp-power-modulo")
