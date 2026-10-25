# Oracle for JuliaLean/MathFuncs/CheckRem2pi.lean: prints `<index> <op> <result>` for
# rem_pio2_kernel, paynehanek, rem2pi (all rounding modes) and mod2pi on the same corpus.

step(s::UInt64) = s * 0x5851f42d4c957f2d + 0x14057b7ef767814f

const EDGES = UInt64[0, 1, 2, 0x000ffffffffffffe, 0x000fffffffffffff,
    0x0010000000000000, 0x0010000000000001, 0x3fe0000000000000, 0x3ff0000000000000,
    0x4000000000000000, 0x3ff8000000000000, 0x4004000000000000, 0x4330000000000000,
    0x4340000000000000, 0x43e0000000000000, 0x7feffffffffffffe, 0x7fefffffffffffff,
    0x7ff0000000000000, 0x7ff0000000000001, 0x7ff8000000000000, 0x7fffffffffffffff]

const THRESHOLDS = UInt64[0x400f6a7a, 0x4002d97c, 0x401c463b, 0x4015fdbc, 0x4012d97c,
    0x401921fb, 0x413921fb, 0x3ff921fb, 0x400921fb, 0x3fe921fb]

const SIGN = 0x8000000000000000
bits(x::Float64) = reinterpret(UInt64, x)
f64(u::UInt64) = reinterpret(Float64, u)

function corpus()
    ws = UInt64[]
    st = 0x9e3779b97f4a7c15
    for w in EDGES
        push!(ws, w, w + SIGN)
    end
    for k in 0:40
        a = Float64(k)
        h = Float64(2k + 1) / 2.0
        push!(ws, bits(a), bits(-a), bits(h), bits(-h))
    end
    for b in (0x3ff921fb54442d18, 0x3fe921fb54442d18)
        for k in -100:100
            c = Float64(k) * f64(b)
            for d in -3:3
                push!(ws, bits(nextfloat(c, d)))
            end
        end
    end
    for t in THRESHOLDS
        for dh in 0:2
            h = t + dh - 1
            st = step(st)
            for lo in (UInt64(0), UInt64(1), UInt64(0x7fffffff), UInt64(0xffffffff), st >> 32)
                w = h << 32 + lo
                push!(ws, w, w + SIGN)
            end
        end
    end
    for e in UInt64(0):UInt64(1040)
        st = step(st)
        s = (st >> 63) << 63
        push!(ws, s + ((e << 20 + 0x921fb) << 32) + (st & 0xffffffff))
        push!(ws, s + ((e << 20 + 0x921fa) << 32) + 0xffffffff)
        push!(ws, s + ((e << 20 + 0x921fc) << 32))
    end
    c = ldexp(f64(0x3ff921fb54442d18), 20)
    for d in -3:3
        v = nextfloat(c, d)
        push!(ws, bits(v), bits(-v))
    end
    for b in (0x401921fb54442d18, 0x400921fb54442d18, 0x4012d97c7f3321d2, 0x3ff921fb54442d18)
        for d in -3:3
            v = nextfloat(f64(b), d)
            push!(ws, bits(v), bits(-v))
        end
    end
    for e in UInt64(0):UInt64(2046)
        for _ in 1:2
            st = step(st)
            push!(ws, (st % 2) << 63 + e << 52 + st >> 12)
        end
    end
    for _ in 1:1500
        st = step(st)
        r1 = st
        st = step(st)
        push!(ws, (r1 >> 63) << 63 + (1000 + r1 % 48) << 52 + st >> 12)
    end
    for _ in 1:500
        st = step(st)
        push!(ws, st)
    end
    return ws
end

out(x::Float64) = isnan(x) ? "nan" : string(bits(x))
function outr(x, r)
    try
        out(rem2pi(x, r))
    catch e
        e isa MethodError ? "method" : e isa DomainError ? "domain" :
            e isa BoundsError ? "bounds" : "unexpected:$(typeof(e))"
    end
end

function main()
    ws = corpus()
    io = IOBuffer()
    for (j1, w) in enumerate(ws)
        j = j1 - 1
        x = f64(w)
        n, y = Base.Math.rem_pio2_kernel(x)
        println(io, j, " kn ", n)
        println(io, j, " khi ", out(y.hi))
        println(io, j, " klo ", out(y.lo))
        if (w >> 32) & 0x7fffffff >= 0x413921fb
            q, p = Base.Math.paynehanek(x)
            println(io, j, " pn ", q)
            println(io, j, " phi ", out(p.hi))
            println(io, j, " plo ", out(p.lo))
        end
        println(io, j, " rn ", outr(x, RoundNearest))
        println(io, j, " rz ", outr(x, RoundToZero))
        println(io, j, " rd ", outr(x, RoundDown))
        println(io, j, " ru ", outr(x, RoundUp))
        println(io, j, " ra ", outr(x, RoundNearestTiesAway))
        println(io, j, " m2 ", out(mod2pi(x)))
    end
    print(String(take!(io)))
end

main()
