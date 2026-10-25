step(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f
function main()
    bases = UInt32[0x40000000, 0x40200000, 0x40400000, 0x41200000, 0x3fc00000, 0x3f800001, 0x40490fdb, 0x3f800000]
    s = 0x243f6a8885a308d3
    i = 0
    for a in bases, _ in 1:120
        i += 1
        s = step(s)
        e = s % 140
        s = step(s)
        x = reinterpret(Float64, (e + 1023) << 52 + s % (UInt64(1) << 52))
        o = try
            string(reinterpret(UInt32, prevpow(reinterpret(Float32, a), x)))
        catch err
            err isa DomainError ? "domain" : err isa InexactError ? "inexact" : "error"
        end
        println(i, " ", o)
    end
end
main()
