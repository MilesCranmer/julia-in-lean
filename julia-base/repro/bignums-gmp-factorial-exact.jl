# This scalar BigInt occupies two 64-bit GMP limbs. Julia rejects the public
# Culong argument conversion before attempting to compute or allocate a factorial.
function reproduced()
    try
        factorial(BigInt(2)^64)
        return false
    catch err
        return err isa InexactError
    end
end
println((reproduced() ? "REPRODUCED " : "NOT_REPRODUCED ") * "bignums-gmp-factorial-exact")
