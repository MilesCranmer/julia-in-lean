# Differential oracle for JuliaLean/MathFuncs/CheckPow.lean: prints the `ff` corpus lines
# (x::Float64 ^ y::Float64) followed by the `fi` corpus lines (x::Float64 ^ n::Integer).

lcg(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f

lit(u) = reinterpret(Float64, UInt64(u))
bits(x::Float64) = reinterpret(UInt64, x)

unif(r::UInt64, lo, hi) = lo + (hi - lo) * (Float64(r >> 11) / lit(0x4340000000000000))

randbits(s1::UInt64, s2::UInt64, e0, w, neg) =
    ((s1 >> 20) % neg == 0 ? 0x8000000000000000 : UInt64(0)) +
    (UInt64(e0) + (s1 >> 11) % w) << 52 + (s2 & (UInt64(1) << 52 - 1))

const XSPECIALS = UInt64[0, 0x8000000000000000, 0x3ff0000000000000, 0xbff0000000000000,
    0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 1, 0x8000000000000001,
    0x000fffffffffffff, 0x800fffffffffffff, 0x0010000000000000, 0x8010000000000000,
    0x7fefffffffffffff, 0xffefffffffffffff, 0x4000000000000000, 0xc000000000000000,
    0x3fe0000000000000, 0xbfe0000000000000, 0x4008000000000000, 0xc008000000000000,
    0x4024000000000000, 0x3ff0000000000001, 0x3fefffffffffffff, 0xbfefffffffffffff,
    0xbff0000000000001, 2, 0x3ff8000000000000, 0x7fe0000000000000, 0x0008000000000000,
    0x01a56e1fc2f8f359, 0x3fb999999999999a, 0xbfb999999999999a]

const YPOS = UInt64[0, 0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000,
    0x3fe0000000000000, 0x7ff0000000000000, 0x40d8000000000000, 0x40d8004000000000,
    0x40b0000000000000, 0x40b0010000000000, 0x433fffffffffffff, 0x43d8000000000000,
    0x43d7ffffffffffff, 0x43d8000000000001, 0x7e37e43c8800759c, 0x3ff8000000000000,
    0x4004000000000000, 0x01a56e1fc2f8f359, 1, 0x43e0000000000000, 0x408ff80000000000,
    0x4090000000000000, 0x4090c80000000000, 0x4090cc0000000000, 0x40d8002000000000,
    0x40b0008000000000, 0x40affe0000000000, 0x40afff0000000000, 0x7fefffffffffffff]

const YSPECIALS = vcat(YPOS, YPOS .+ 0x8000000000000000, UInt64[0x7ff8000000000000, 0xfff8000000000000])

const KLIST = [1, 2, 3, 5, 8, 13, -1, -2, -3, -5, -8, -13]

function ff_pairs()
    a = Tuple{UInt64,UInt64}[]
    for x in XSPECIALS, y in YSPECIALS
        push!(a, (x, y))
    end
    s = 0x853c49e6748fea9b
    for _ in 1:1800
        s = lcg(s); s1 = s
        s = lcg(s)
        x = randbits(s1, s, 1003, 41, 4)
        s = lcg(s)
        push!(a, (x, bits(unif(s, -60.0, 60.0))))
    end
    for _ in 1:300
        s = lcg(s); s1 = s
        s = lcg(s)
        x = randbits(s1, s, 1003, 41, 2)
        s = lcg(s)
        m = Int((s >> 11) % 35000) - 5000
        push!(a, (x, bits(Float64(m))))
    end
    for k in KLIST, _ in 1:125
        s = lcg(s)
        base = lit(UInt64(1023 + k) << 52) * (1.0 + unif(s, 0.0, lit(0x3f50000000000000)))
        s = lcg(s)
        t = s >> 63 == 0 ? unif(s, lit(0x408fb80000000000), lit(0x4090080000000000)) :
            unif(s, lit(0xc090e00000000000), lit(0xc08fb80000000000))
        push!(a, (bits(base), bits(t / Float64(k))))
    end
    for _ in 1:200
        s = lcg(s)
        x = s & (UInt64(1) << 52 - 1)
        s = lcg(s)
        push!(a, (x, bits(unif(s, lit(0xbff3333333333333), lit(0x3ff3333333333333)))))
    end
    for _ in 1:400
        s = lcg(s)
        x = unif(s, lit(0x3fefffffff800000), lit(0x3ff0000000400000))
        x = (s >> 20) % 2 == 0 ? -x : x
        s = lcg(s)
        m = Int((s >> 11) % (UInt64(1) << 40)) + 24577
        m = (s >> 5) % 3 == 0 ? -m : m
        push!(a, (bits(x), bits(Float64(m))))
    end
    for _ in 1:400
        s = lcg(s); x = s
        s = lcg(s)
        push!(a, (x, s))
    end
    return a
end

const NLIST = vcat(Any[Int64(n) for n in (0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -4096, -4097, -4095,
        24576, 24577, 24575, 30000, 100001, -100001, 1023, -1023, 1024, -1074, -1075, 1075, 1025,
        -1025, 2^53, 2^53 + 1, -(2^53 + 1), 2^62 + 1, 2^62, 1048575, -1048575, typemin(Int64),
        typemin(Int64) + 1, typemax(Int64), typemax(Int64) - 1)],
    Any[Int128(2)^63, -Int128(2)^63 - 1, Int128(2)^64 + 1, -Int128(2)^64 - 1, Int128(2)^64,
        UInt64(2)^63 + 1, typemax(UInt64), UInt64(2)^63,
        big(2)^100 + 1, -big(2)^100 - 1, big(2)^100, -big(2)^100])

function fi_bases()
    a = copy(XSPECIALS)
    for d in (1, 2, 3, 10, 1000)
        push!(a, 0x3ff0000000000000 + d, 0x3ff0000000000000 - d)
        push!(a, 0xbff0000000000000 + d)
    end
    for b in (0x3feffffe00000000, 0x3ff0000100000000, 0x3fefffffffffe000, 0x3ff0000000001000)
        push!(a, b, b + 0x8000000000000000)
    end
    s = 0xda3e39cb94b95bdb
    for _ in 1:30
        s = lcg(s); s1 = s
        s = lcg(s)
        push!(a, randbits(s1, s, 983, 81, 2))
    end
    return a
end

function fi_pairs()
    a = Tuple{UInt64,Any}[]
    for x in fi_bases(), n in NLIST
        push!(a, (x, n))
    end
    s = 0x6a09e667f3bcc909
    for _ in 1:1000
        s = lcg(s); s1 = s
        s = lcg(s)
        x = randbits(s1, s, 1013, 21, 2)
        s = lcg(s)
        push!(a, (x, Int((s >> 11) % 35000) - 5000))
    end
    for _ in 1:500
        s = lcg(s)
        x = unif(s, lit(0x3feffffffffffff8), lit(0x3ff0000000000004))
        x = (s >> 20) % 2 == 0 ? -x : x
        s = lcg(s)
        push!(a, (bits(x), reinterpret(Int64, s)))
    end
    return a
end

out(x::Float64) = isnan(x) ? "nan" : string(reinterpret(UInt64, x))

function powff(x::Float64, y::Float64)
    try
        return out(x^y)
    catch e
        e isa DomainError && return "domain"
        rethrow()
    end
end

function main()
    for (j0, (x, y)) in enumerate(ff_pairs())
        println(j0 - 1, " powff ", powff(lit(x), lit(y)))
    end
    for (j0, (x, n)) in enumerate(fi_pairs())
        println(j0 - 1, " powfi ", out(lit(x)^n))
    end
end

main()
