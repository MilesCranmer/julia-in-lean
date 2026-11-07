# Public scoped setting retains a callback's global-mode mutation.
function check()
    old = rounding(BigFloat)
    try
        setrounding(BigFloat, RoundNearest)
        observed = setrounding(BigFloat, RoundUp) do
            setrounding(BigFloat, RoundDown)
            rounding(BigFloat)
        end
        after = rounding(BigFloat)
        # The documented save/set/callback/restore program returns RoundDown
        # and restores RoundNearest. The lexical implementation does neither.
        return observed == RoundUp && after == RoundDown
    finally
        setrounding(BigFloat, old)
    end
end
ok = try check() catch; false end
println((ok ? "REPRODUCED " : "NOT_REPRODUCED ") * "bignumscov-mpfr-setup-rounding-v2")
