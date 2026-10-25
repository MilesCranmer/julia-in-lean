# powermod(x, p, m) with p < 0 and gcd(x, m) != 1 has no answer. For machine integers it
# throws DomainError from invmod; for BigInt it throws DivideError from GMP's mpz_powm.
function err(f)
    try
        return f()
    catch e
        return e
    end
end
a = err(() -> powermod(2, -1, 4))
b = err(() -> powermod(big(2), -1, big(4)))
c = err(() -> powermod(2, -1, big(4)))
d = err(() -> powermod(big(3), -2, big(0)))
e = err(() -> powermod(3, -2, 0))
println("powermod(2, -1, 4)           -> ", typeof(a))
println("powermod(big(2), -1, big(4)) -> ", typeof(b))
println("powermod(2, -1, big(4))      -> ", typeof(c))
println("powermod(big(3), -2, big(0)) -> ", typeof(d))
println("powermod(3, -2, 0)           -> ", typeof(e))
if a isa DomainError && b isa DivideError && c isa DivideError
    println("REPRODUCED bignums-powermod-noninvertible")
end
