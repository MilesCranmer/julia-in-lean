# digits!(a, n; base) must fill `a` with the least significant digits when `a` is too short
# (digits! docstring). For a BigInt and a power-of-two base above 62, the mpz_export fast
# path calls resize!(a, ...) instead, which fails for any non-resizable vector.
function res(f)
    try
        return f()
    catch e
        return typeof(e)
    end
end
v1 = view(zeros(Int, 10), 1:3)
v2 = view(zeros(Int, 10), 1:3)
a = res(() -> digits!(v1, 2^62 + 5; base=128))
b = res(() -> digits!(v2, big(2)^62 + 5; base=128))
c = res(() -> digits!(zeros(Int, 3), big(2)^62 + 5; base=128))
println("digits!(view, 2^62 + 5; base=128)      = ", a)
println("digits!(view, big(2)^62 + 5; base=128) = ", b)
println("digits!(Vector, big(2)^62 + 5; base=128) = ", c)
if a == [5, 0, 0] && b === MethodError && c == [5, 0, 0]
    println("REPRODUCED bignums-digits-view-pow2-base")
end
