# Differential oracle for JuliaLean/MathFuncs/CheckLog.lean: prints `<index> <op> <result>`
# for log, log2, log10, log1p and Base.Math._log_ext. Optional ARGS: start count.

lcg(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f

function gen!(out, n, f, s)
    for _ in 1:n
        s = lcg(s)
        push!(out, f(s))
    end
    return s
end

const edges = UInt64[0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x8000000000000001, 0x800fffffffffffff,
   0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
   0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
   0x7ff0000000000001, 0x3ff0000000000000, 0xbff0000000000000, 0x4000000000000000,
   0x3fe0000000000000, 0x4024000000000000, 0x3fb999999999999a, 0x4059000000000000,
   0x408f400000000000, 0x4005bf0a8b145769, 0x3ff0000000000001, 0x3fefffffffffffff,
   0x0008000000000000, 0x0000000000000002, 0x3ca0000000000000, 0xbca0000000000000,
   0x3cb0000000000000, 0xbc90000000000000, 0x0010000000000001, 0x7fe0000000000000,
   0x4330000000000000, 0x4340000000000000, 0x43e0000000000000, 0xc000000000000000]

const thresholds = UInt64[0x3fee0fabfbc702a3, 0x3ff1082b577d34ee, 0x3ca0000000000000, 0xbca0000000000000,
   0xbfaf0540438fd5c4, 0x3fb082b577d34ed8, 0xbff0000000000000, 0x3ff0000000000000]

const cells = [0x3ff0000000000000 + UInt64(2j + 1) << 44 for j in 0:127]

around(b::Integer) = UInt64[b - 1, b, b + 1]

function main_corpus()
    c = copy(edges)
    for t in thresholds, d in 0:6
        push!(c, t + d - 3)
    end
    for e in (0, -1, 7, -1000, 1000), cl in cells
        append!(c, around(Int128(cl) + Int128(e) << 52))
    end
    for j in 0:127
        append!(c, around(UInt64(2j + 1) << 34))
    end
    for e in (-2, -1, 0, 1, 2), cl in cells
        x = reinterpret(Float64, UInt64(Int128(cl) + Int128(e) << 52)) - 1.0
        append!(c, around(reinterpret(UInt64, x)))
    end
    for k in 0:29; push!(c, 0xbff0000000000000 - (k + 1)); end
    for k in 0:29; push!(c, 0xbfefffffffffffff - UInt64(k) << 40); end
    for k in 0:4; push!(c, 0xbff0000000000000 + (k + 1)); end
    s = 0x2545f4914f6cdd1d
    s = gen!(c, 1500, s -> s % 0x7ff0000000000000, s)
    s = gen!(c, 500, s -> s % (UInt64(1) << 52), s)
    s = gen!(c, 1000, s -> 0x3feccccccccccccd + s % (0x3ff199999999999a - 0x3feccccccccccccd), s)
    s = gen!(c, 1000, s -> (s >> 63) << 63 + (s & typemax(Int64) % UInt64) % 0x3ff0000000000001, s)
    s = gen!(c, 500, s -> (s >> 63) << 63 + 0x3fa999999999999a + s % (0x3fb1eb851eb851ec - 0x3fa999999999999a), s)
    gen!(c, 300, identity, s)
    return c
end

denorm_adjust(xb::UInt64) =
    (reinterpret(UInt64, reinterpret(Float64, xb) * 0x1p52) & ~Base.sign_mask(Float64)) - UInt64(52) << 52

function ext_corpus()
    c = UInt64[0x3ff0000000000000, 0x0010000000000000, 0x7fefffffffffffff, 0x4000000000000000,
        0x3fe0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff, 0x4008000000000000]
    append!(c, denorm_adjust.(UInt64[1, 0x000fffffffffffff, 0x0008000000000000, 2, 3]))
    for e in (-1021, -1000, -1, 0, 1, 500, 1023), j in 0:127
        append!(c, around(Int128(0x3fe6955500000000) + Int128(j) << 45 + Int128(e) << 52))
    end
    s = 0x9e3779b97f4a7c15
    s = gen!(c, 1500, s -> 0x0010000000000000 + s % (0x7ff0000000000000 - 0x0010000000000000), s)
    s = gen!(c, 1000, s -> denorm_adjust(1 + s % ((UInt64(1) << 52) - 1)), s)
    gen!(c, 500, s -> 0x3fe0000000000000 + s % (UInt64(1) << 53), s)
    return c
end

fmt(x::Float64) = isnan(x) ? "nan" : string(reinterpret(UInt64, x))

function fmtcall(f, x)
    try
        fmt(f(x))
    catch err
        err isa DomainError ? "domain" : err isa BoundsError ? "bounds" : "method"
    end
end

function runall(start, count)
    corpus = [[(false, b) for b in main_corpus()]; [(true, b) for b in ext_corpus()]]
    stop = min(length(corpus), start + count)
    for i in start:stop-1
        isext, b = corpus[i+1]
        println(i, " in ", b)
        if isext
            h, l = Base.Math._log_ext(b)
            println(i, " logext_hi ", fmt(h))
            println(i, " logext_lo ", fmt(l))
        else
            x = reinterpret(Float64, b)
            for (name, f) in (("log", log), ("log2", log2), ("log10", log10), ("log1p", log1p))
                println(i, " ", name, " ", fmtcall(f, x))
            end
        end
    end
end

if length(ARGS) == 2
    runall(parse(Int, ARGS[1]), parse(Int, ARGS[2]))
else
    runall(0, typemax(Int) ÷ 2)
end
