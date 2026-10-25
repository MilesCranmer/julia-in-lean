# Oracle for JuliaLean/MathFuncs/CheckTrig.lean: prints `<index> <op> <result>` for
# sinpi/cospi/sincospi/tanpi/kernels/cbrt on Float64 words and the Int64 methods.

lcg(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f

ratbits(n::Integer, k::Integer) = reinterpret(UInt64, ldexp(Float64(n), -k))

const EDGES = UInt64[0, 1, 2, 0x000ffffffffffffe, 0x000fffffffffffff, 0x0010000000000000,
    0x0010000000000001, 0x3ff0000000000000, 0x3fefffffffffffff, 0x3ff0000000000001,
    0x7fefffffffffffff, 0x7feffffffffffffe, 0x7ff0000000000000, 0x7ff8000000000000,
    0x7ff0000000000001, 0x7fffffffffffffff, 0x3e10000000000000, 0x3cb0000000000000]

const SIGN = 0x8000000000000000

function words()
    ws = UInt64[]
    for w in EDGES
        push!(ws, w, w + SIGN)
    end
    for k in -200:200
        k == 0 && continue
        w = reinterpret(UInt64, k / 8)
        for j in 0:4
            push!(ws, w + j - 2)
        end
    end
    for i in 0:2097
        push!(ws, ratbits(1, 1074 - i))
    end
    for e in (51, 52, 53)
        w = ratbits(1, -e)
        for j in 0:40
            push!(ws, w + j - 20, w + j - 20 + SIGN)
        end
    end
    for m in 1:300
        push!(ws, ratbits(m^3, 0), ratbits(-m^3, 0))
    end
    for j in (-350, -100, -20, 20, 100, 300)
        for m in 1:20
            push!(ws, ratbits(m^3, -3j))
        end
    end
    s = 0x243f6a8885a308d3
    for _ in 1:3000
        s = lcg(s)
        e = (s >> 53) % 91
        sign = (s >> 52) % 2
        push!(ws, sign * SIGN + (e + 1023 - 30) << 52 + s % (UInt64(1) << 52))
    end
    for _ in 1:1000
        s = lcg(s)
        push!(ws, s)
    end
    for _ in 1:300
        s = lcg(s)
        push!(ws, (s >> 63) << 63 + s % (UInt64(1) << 52))
    end
    ws
end

function ints()
    xs = Int64[]
    append!(xs, -20:20)
    append!(xs, [typemin(Int64), typemax(Int64), typemin(Int64) + 1, typemax(Int64) - 1,
                 2^53, 2^53 + 1, -2^53 - 1])
    s = 0x9e3779b97f4a7c15
    for _ in 1:200
        s = lcg(s)
        push!(xs, reinterpret(Int64, s))
    end
    xs
end

out(x::Float64) = isnan(x) ? "nan" : string(reinterpret(UInt64, x))

function outcall(f, x)
    try
        out(f(x))
    catch e
        e isa DomainError ? "domain" : e isa BoundsError ? "bounds" : e isa MethodError ? "method" : "error"
    end
end

function main()
    for (j, w) in enumerate(words())
        x = reinterpret(Float64, w)
        println(j, " sinpi ", outcall(sinpi, x))
        println(j, " cospi ", outcall(cospi, x))
        println(j, " sincospi_s ", outcall(y -> sincospi(y)[1], x))
        println(j, " sincospi_c ", outcall(y -> sincospi(y)[2], x))
        println(j, " tanpi ", outcall(tanpi, x))
        println(j, " sinpi_kernel ", out(Base.Math.sinpi_kernel(x)))
        println(j, " cospi_kernel ", out(Base.Math.cospi_kernel(x)))
        println(j, " cbrt ", out(cbrt(x)))
    end
    for (j, n) in enumerate(ints())
        println(j, " isinpi ", out(sinpi(n)))
        println(j, " icospi ", out(cospi(n)))
        println(j, " itanpi ", out(tanpi(n)))
    end
end

main()
