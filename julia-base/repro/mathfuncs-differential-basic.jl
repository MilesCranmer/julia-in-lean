const EDGES = UInt64[
    0, 1, 2, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001, 0x1CC0000000000000,
    0x2000000000000000, 0x1fffffffffffffff, 0x3E46A09E667F3BCD, 0x3fe0000000000000,
    0x3ff0000000000000, 0x3ff0000000000001, 0x4000000000000000, 0x4008000000000000,
    0x4010000000000000, 0x5FE6A09E667F3BCC, 0x5FE6A09E667F3BCD, 0x7fefffffffffffff,
    0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001, 0x4066800000000000,
    0x400921FB54442D18]
const ALL = vcat(EDGES, EDGES .+ 0x8000000000000000)
step(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f
out(x::Float64) = isnan(x) ? "nan" : string(reinterpret(UInt64, x))
outj(f) = try out(f()) catch e; e isa DomainError ? "domain" : "error" end
withexp(w, e) = (w >> 63) << 63 + UInt64(e) << 52 + (w & (UInt64(2)^52 - 1))
F(b) = reinterpret(Float64, b)

function main()
    i = 0
    n = length(ALL)
    for a in ALL, b in ALL
        i += 1
        x = F(a); y = F(b)
        println(i, " min ", out(min(x, y)))
        println(i, " max ", out(max(x, y)))
        println(i, " hypot ", out(hypot(x, y)))
        println(i, " hypot3 ", out(hypot(x, y, F(ALL[i % n + 1]))))
        println(i, " clamp ", out(clamp(x, y, F(ALL[(7i) % n + 1]))))
    end
    s = 0x243f6a8885a308d3
    for k in 0:5999
        i += 1
        s = step(s); w1 = s
        s = step(s); w2 = s
        s = step(s); w3 = s
        e1 = (w3 >> 3) % 2047
        d = (w3 >> 20) % 40
        e2 = e1 > d ? e1 - d : 0
        e3 = e1 > 2d ? e1 - 2d : 0
        x = F(k % 5 == 0 ? w1 : withexp(w1, e1))
        y = F(k % 5 == 0 ? w2 : withexp(w2, e2))
        z = F(withexp(w3, e3))
        println(i, " hypot ", out(hypot(x, y)))
        println(i, " hypot3 ", out(hypot(x, y, z)))
        println(i, " deg2rad ", out(deg2rad(x)))
        println(i, " rad2deg ", out(rad2deg(x)))
        println(i, " fourthroot ", outj(() -> fourthroot(x)))
        println(i, " min ", out(min(x, y)))
        println(i, " max ", out(max(x, y)))
        sh = (w3 >> 40) % 64
        n0 = Int64(Int128(w1) - Int128(2)^63)
        d0 = Int64((w2 >> sh) % (UInt64(1) << 63)) + 1
        num = k % 7 == 0 ? Int64(2)^60 - Int64(w1 % 1000) : n0 >> (w3 % 64)
        den = k % 7 == 0 ? Int64(2)^60 : d0
        if num != 0
            println(i, " exponentrat ", exponent(num // den))
        end
    end
    for a in UInt64[0, 1, 2, 127, 128, 255, UInt64(2)^63 - 1, UInt64(2)^63, typemax(UInt64), typemax(UInt64) - 127]
        for b in UInt64[0, 1, UInt64(2)^63, typemax(UInt64), typemax(UInt64) - 127]
            i += 1
            x = a % Int64; y = b % Int64; x8 = a % Int8; y8 = b % Int8
            println(i, " copysign64 ", copysign(x, y))
            println(i, " flipsign64 ", flipsign(x, y))
            println(i, " copysign8 ", copysign(x8, y8))
            println(i, " flipsign8 ", flipsign(x8, y8))
        end
    end
    println("COUNT ", i)
end
main()
