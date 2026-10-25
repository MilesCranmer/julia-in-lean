# Rational{BigInt}(NaN) is meant to fail like Rational{Int}(NaN) (InexactError: the value
# has no rational representation). Its first line returns zero(BigInt)//zero(BigInt),
# which itself throws ArgumentError "invalid rational: zero(BigInt)//zero(BigInt)".
function res(f)
    try
        return repr(f())
    catch e
        return "throws " * string(typeof(e))
    end
end
a = res(() -> Rational{Int}(NaN))
b = res(() -> Rational{BigInt}(NaN))
c = res(() -> Rational(big(NaN)))
d = res(() -> Rational{Int}(big(NaN)))
println("Rational{Int}(NaN)      -> ", a)
println("Rational{BigInt}(NaN)   -> ", b)
println("Rational(big(NaN))      -> ", c)
println("Rational{Int}(big(NaN)) -> ", d)
if a == "throws InexactError" && b == "throws ArgumentError"
    println("REPRODUCED bignums-rational-nan")
end
