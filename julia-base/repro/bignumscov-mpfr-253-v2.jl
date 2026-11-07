# A public mode tag is rejected by the global setter.
function check()
    old = rounding(BigFloat)
    try
        try
            setrounding(BigFloat, RoundNearestTiesAway)
            return false
        catch err
            return err isa MethodError
        end
    finally
        setrounding(BigFloat, old)
    end
end
ok = try check() catch; false end
println((ok ? "REPRODUCED " : "NOT_REPRODUCED ") * "bignumscov-mpfr-253-v2")
