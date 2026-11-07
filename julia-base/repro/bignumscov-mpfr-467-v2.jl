# The exactly represented positive zero has the same 64-bit precision as the
# formal witness. A documented tie mode is rejected before rounding starts.
let reproduced = false
    try
        setrounding(BigFloat, RoundNearest)
        x = BigFloat(0; precision=64)
        if rounding(BigFloat) == RoundNearest && precision(x) == 64 && iszero(x) && !signbit(x)
            try
                round(BigInt, x, RoundNearestTiesAway)
            catch err
                reproduced = err isa MethodError
            end
        end
    catch
        reproduced = false
    end
    println(reproduced ? "REPRODUCED bignumscov-mpfr-467-v2" :
                         "NOT_REPRODUCED bignumscov-mpfr-467-v2")
end
