# round(T, x, RoundNearestTiesAway) works for every float type except BigFloat, where the
# integer-target method converts the mode to an MPFR mode and has no conversion for it.
function res(f)
    try
        return repr(f())
    catch e
        return "throws " * string(typeof(e))
    end
end
a = res(() -> round(Int, 2.5, RoundNearestTiesAway))
b = res(() -> round(Int, big(2.5), RoundNearestTiesAway))
c = res(() -> round(BigInt, big(2.5), RoundNearestTiesUp))
d = res(() -> round(big(2.5), RoundNearestTiesAway))
println("round(Int, 2.5, RoundNearestTiesAway)      -> ", a)
println("round(Int, big(2.5), RoundNearestTiesAway) -> ", b)
println("round(BigInt, big(2.5), RoundNearestTiesUp) -> ", c)
println("round(big(2.5), RoundNearestTiesAway)      -> ", d)
if a == "3" && b == "throws MethodError" && c == "throws MethodError"
    println("REPRODUCED bignums-round-ties-away")
end
