x = -nextfloat(0.0f0)
@assert reinterpret(UInt32, x) == 0x80000001
result = mod2pi(x)
@assert result isa Float32
@assert isfinite(result)
@assert reinterpret(UInt32, result) == 0x40c90fdb
setprecision(BigFloat, 256) do
    two_pi_upper = setrounding(BigFloat, RoundUp) do
        2 * BigFloat(pi)
    end
    @assert BigFloat(result) > two_pi_upper
end
println("REPRODUCED mathfuncs-mod2pi-ieee-range")
