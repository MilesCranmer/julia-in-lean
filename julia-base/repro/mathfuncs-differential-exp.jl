# Differential oracle for JuliaLean/MathFuncs/CheckExp.lean: prints the `float` corpus lines
# followed by the `int` corpus lines, in the same format and order as the Lean checker.

lcg(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f

out(x::Float64) = isnan(x) ? "nan" : string(reinterpret(UInt64, x))
lit(u) = reinterpret(Float64, UInt64(u))

const SPECIALS = UInt64[0, 0x8000000000000000, 1, 0x8000000000000001, 0x000fffffffffffff, 0x800fffffffffffff,
    0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
    0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
    0x7ff0000000000001, 0x3ff0000000000000, 0xbff0000000000000, 0x3fe0000000000000,
    0xbfe0000000000000, 0x3c90000000000000, 0xbc90000000000000]

const THRESHOLDS = UInt64[0x4090000000000000, 0x40862e42fefa39f0, 0x40734413509f79ff,
    0xc090cc0000000000, 0xc0874910d52d3052, 0xc07439b746e36b52,
    0x408ff00000000000, 0x4086232bdd7abcd2, 0x40733a7146f72a41,
    0xc08ff00000000000, 0xc086232bdd7abcd2, 0xc0733a7146f72a41,
    0xbfd269621134db92, 0x3fcc8ff7c79a9a22, 0x40862e42fefa39f4, 0xc042b708872320e2,
    0x4042b708872320e2, 0, 0x0010000000000000, 0x7fefffffffffffff]

const KLIST = [-1080, -1077, -1076, -1075, -1074, -1073, -1060, -1023, -1022,
    -1021, -1000, -60, -55, -54, -53, -52, -51, -3, -2, -1, 1, 2, 52, 53, 54, 105, 106, 107,
    500, 1022, 1023, 1024, 1025]

const KSCALES = [lit(0x3fe62e42fefa39ef), lit(0x3fd34413509f79ff), 1.0]

unif(r::UInt64, lo, hi) = lo + (hi - lo) * (Float64(r >> 11) / lit(0x4340000000000000))

bits(x::Float64) = reinterpret(UInt64, x)

function inputs()
    a = copy(SPECIALS)
    for t in THRESHOLDS, j in 0:100
        push!(a, bits(nextfloat(lit(t), j - 50)))
    end
    for k in KLIST, c in KSCALES
        x = Float64(k) * c
        for j in 0:6
            push!(a, bits(nextfloat(x, j - 3)))
        end
    end
    s = 0x9e3779b97f4a7c15
    for _ in 1:200
        s = lcg(s)
        m = Int((s >> 11) % 537000) - 275000
        x = Float64(2m + 1) / lit(0x4080000000000000)
        push!(a, bits(x), bits(nextfloat(x, 1)), bits(prevfloat(x, 1)))
    end
    for c in (lit(0x40771547652b82fe), lit(0x408a934f0979a371)), _ in 1:100
        s = lcg(s)
        m = Int((s >> 11) % 537000) - 275000
        x = (Float64(m) + 0.5) / c
        for j in 0:4
            push!(a, bits(nextfloat(x, j - 2)))
        end
    end
    for b in (Val(2), Val(:ℯ), Val(10)), _ in 1:150
        s = lcg(s)
        push!(a, bits(unif(s, Base.Math.MIN_EXP(b, Float64), -Base.Math.SUBNORM_EXP(b, Float64))))
    end
    for (n, lo, hi) in ((600, -750.0, 750.0), (600, -1100.0, 1100.0), (600, -40.0, 40.0), (400, -1.0, 1.0))
        for _ in 1:n
            s = lcg(s)
            push!(a, bits(unif(s, lo, hi)))
        end
    end
    for _ in 1:300
        s = lcg(s)
        e = UInt64(953) + (s >> 11) % 82
        s = lcg(s)
        push!(a, ((s >> 63) << 63) + (e << 52) + (s & (UInt64(1) << 52 - 1)))
    end
    for _ in 1:200
        s = lcg(s)
        push!(a, s)
    end
    return a
end

const TYPES = (Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128)

function int_candidates(T)
    nb = 8 * sizeof(T)
    a = BigInt[typemin(T), big(typemin(T)) + 1, big(typemin(T)) + 2, typemax(T), big(typemax(T)) - 1, -1, 0, 1, 2]
    for v in 0:2300
        push!(a, big(v) - 1150)
    end
    for j in 0:79
        push!(a, -big(2)^64 - 1074 + j - 5)
        push!(a, -big(2)^65 - 1074 + j - 5)
        push!(a, -big(2)^127 + j)
        push!(a, big(2)^64 - 1074 + j - 5)
    end
    s = 0x2545f4914f6cdd1d + UInt64(nb)
    for _ in 1:100
        s = lcg(s)
        hi = s
        s = lcg(s)
        w = mod(big(hi) * big(2)^64 + big(s), big(2)^nb)
        push!(a, T <: Signed && w >= big(2)^(nb - 1) ? w - big(2)^nb : w)
    end
    return filter(v -> typemin(T) <= v <= typemax(T), a)
end

function main()
    xs = inputs()
    for (j0, b) in enumerate(xs)
        j = j0 - 1
        x = lit(b)
        println(j, " in ", b)
        println(j, " exp ", out(exp(x)))
        println(j, " exp2 ", out(exp2(x)))
        println(j, " exp10 ", out(exp10(x)))
        println(j, " expm1 ", out(expm1(x)))
        println(j, " explo ", out(Base.Math.exp_impl(x, x * lit(0x3c80000000000000), Val(:ℯ))))
    end
    i = 0
    for T in TYPES
        for v in int_candidates(T)
            println(i, " exp2i_", T, " ", out(exp2(T(v))))
            i += 1
        end
    end
end

main()
