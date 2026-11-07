# Equal unit inputs are constructible and gcdx completes immediately.
function reproduced()
    try
        a, b = BigInt(1), BigInt(1)
        g, u, v = gcdx(a, b)
        return g == 1 && u == 0 && v == 1 && !(abs(v) * g < abs(a))
    catch
        return false
    end
end
println((reproduced() ? "REPRODUCED " : "NOT_REPRODUCED ") * "bignums-gmp-extended-gcd")
