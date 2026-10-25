step(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f
function main()
    edges = UInt32[0, 1, 2, 0x7fffff, 0x800000, 0x3f800000, 0x40c90fdb, 0x40c90fda,
        0x7f7fffff, 0x7f800000, 0x7fc00000, 0x7f800001, 0x33d6bf95, 0x34000000]
    ws = vcat(edges, edges .+ 0x80000000)
    s = 0x243f6a8885a308d3
    for _ in 1:4000
        s = step(s)
        push!(ws, UInt32(s >> 32))
    end
    i = 0
    for w in ws
        i += 1
        x = reinterpret(Float32, w)
        d = Float64(x)
        println(i, " f64 ", isnan(d) ? "nan" : string(reinterpret(UInt64, d)))
        println(i, " mod2pi32 ", isfinite(x) ? string(reinterpret(UInt32, mod2pi(x))) : "skip")
        s = step(s)
        y = reinterpret(Float64, s)
        println(i, " f32 ", isnan(y) ? "nan" : string(reinterpret(UInt32, Float32(y))))
    end
end
main()
