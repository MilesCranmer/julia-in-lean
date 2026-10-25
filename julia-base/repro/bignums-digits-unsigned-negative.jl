# digits(T, n) with an unsigned element type T and a negative n has no valid answer
# (the digits of a negative number are negative). For machine integers it throws
# InexactError; for BigInt it silently returns wrapped "digits" that are not digits.
function res(f)
    try
        return f()
    catch e
        return typeof(e)
    end
end
a = res(() -> digits(UInt8, -7))
b = res(() -> digits(UInt8, big(-7)))
c = res(() -> digits(UInt8, big(-1000)))
println("digits(UInt8, -7)         = ", a)
println("digits(UInt8, big(-7))    = ", b)
println("digits(UInt8, big(-1000)) = ", c)
if a === InexactError && b == UInt8[0xf9]
    println("REPRODUCED bignums-digits-unsigned-negative")
end
