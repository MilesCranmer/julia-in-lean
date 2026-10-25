# Differential oracle for JuliaLean/FloatRanges/Validation.lean: draws the same cases
# with the same LCG and prints the same lines (`lake env lean --run
# JuliaLean/FloatRanges/Check.lean START COUNT` prints the model's).
const VB = UInt64[0x0000000000000000,0x8000000000000000,0x3ff0000000000000,0xbff0000000000000,0x3fb999999999999a,0xbfb999999999999a,0x3fc999999999999a,0x3fd3333333333333,0x3fe0000000000000,0x3ff8000000000000,0x4000000000000000,0x4008000000000000,0x4024000000000000,0x3fe6666666666666,0x3ff199999999999a,0x4061866666666666,0xbff028f5c28f5c29,0x3fd5555555555555,0x400921fb54442d18,0x3d06849b86a12b9b,0x01a56e1fc2f8f359,0x0000000000000001,0x8000000000000001,0x4340000000000000,0x4340000000000001,0x430c6bf526340000,0x4170000000000000,0x4170000010000000,0x42a2309ce5400000,0x7fefffffffffffff,0xffefffffffffffff,0x3ff0000000000001,0x3fefffffffffffff,0x7ff0000000000000,0xfff0000000000000,0x7ff8000000000000,0x3fb8c7e28240b780,0x3faf06f694467382,0x402fae147ae147ae,0xbf9bda5119ce075f,0x43e02207973f6440,0x43dfeb3dd0676600,0x7fe1ccf385ebc8a0,0xffe1ccf385ebc8a0,0x4089f4cccccccccd,0x4089f4ccccccccd7,0xc083580000000000,0x4065c00000000000,0x3fbcf41f212d7732,0x3ee4f8b588e368f1,0x401c000000000000,0xc00c000000000000,0x4059000000000000,0x416312d000000000,0x3e8ad7f29abcaf48,0x3fd0000000000000]
const SB = UInt64[0x3fb999999999999a,0xbfb999999999999a,0x3fd3333333333333,0x3ff0000000000000,0xbff0000000000000,0x3fe0000000000000,0x3fd5555555555555,0x400921fb54442d18,0x3f9bda5119ce075f,0xbf9bda5119ce075f,0x404a266666666666,0x01a56e1fc2f8f359,0x4000000000000000,0x46293e5939a08cea,0x7ff0000000000000,0xfff0000000000000,0x7ff8000000000000,0x0000000000000000,0x7fefffffffffffff,0x3f86872b020c49ba,0x3f99ce075f6fd220,0x401c000000000000,0xc0440ccccccccccd,0x42a2309ce5400000,0x3fa8e965e6eef808,0xbfd0000000000000,0x3f50624dd2f1a9fc,0x3e45798ee2308c3a,0x4008000000000000,0xbfe6666666666666,0x3efa36e2eb1c432d,0x7e37e43c8800759c]
const NS = Int[0, 1, 2, 3, 4, 5, 6, 10, 24, 100, 1476, 4096, 1000000, 10000000000000000,
               4611686018427387904, 9223372036854775807, -1, 7, 11, 1490]
outF(x::Float64) = isnan(x) ? "nan" : string(reinterpret(UInt64, x))
outB(b::Bool) = b ? "true" : "false"
function outErr(e)
    e isa ArgumentError ? "E:argument" : e isa InexactError ? "E:inexact" :
    e isa DivideError ? "E:divide" : e isa BoundsError ? "E:bounds" :
    e isa OverflowError ? "E:overflow" : e isa DomainError ? "E:domain" :
    e isa MethodError ? "E:method" : rethrow(e)
end
macro j(f, ex)
    :(try $(esc(f))($(esc(ex))) catch e; outErr(e) end)
end
fieldsS(r) = "$(r.len) $(r.offset) $(outF(r.ref.hi)) $(outF(r.ref.lo)) $(outF(r.step.hi)) $(outF(r.step.lo))"
function descS(r)
    mid = max(1, r.len ÷ 2)
    xm = Base.unsafe_getindex(r, mid)
    ins = [@j(outB, x in r) for x in (first(r), last(r), xm, nextfloat(xm))]
    "$(fieldsS(r)) | $(outF(first(r))) $(outF(last(r))) $(@j(outF, r[2])) $(@j(outF, r[mid])) $(outF(step(r))) | $(join(ins, " ")) | rev $(@j(q -> "$(fieldsS(q)) $(@j(outF, q[2]))", reverse(r))) | neg $(@j(fieldsS, -r))"
end
fieldsL(r) = "$(outF(r.start)) $(outF(r.stop)) $(r.len) $(r.lendiv)"
function descL(r)
    mid = max(1, r.len ÷ 2)
    xm = Base.unsafe_getindex(r, mid)
    ins = [@j(outB, x in r) for x in (Base.unsafe_getindex(r, 2), xm, nextfloat(xm))]
    g2 = q -> @j(outF, q[2])
    "$(fieldsL(r)) | $(@j(outF, r[1])) $(@j(outF, r[2])) $(@j(outF, r[mid])) $(@j(outF, r[r.len])) $(outF(step(r))) | $(join(ins, " ")) | rev $(@j(g2, reverse(r))) | neg $(@j(g2, -r)) | add $(@j(g2, r .+ 0.1)) | mul $(@j(g2, r .* 3.0))"
end
descSmall(r) = "$(fieldsS(r)) $(outF(first(r))) $(outF(last(r))) $(@j(outF, r[2]))"
function main(start, count)
    cases = Any[]
    st = 0x243f6a8885a308d3
    for (kind, cnt) in enumerate((1200, 800, 500, 300, 600, 300)), _ in 1:cnt
        p = UInt64[]
        for _ in 1:4
            st = st * 0x5851f42d4c957f2d + 0x14057b7ef767814f
            push!(p, st >> 33)
        end
        v(k) = reinterpret(Float64, VB[p[k] % length(VB) + 1])
        s(k) = reinterpret(Float64, SB[p[k] % length(SB) + 1])
        n(k) = NS[p[k] % length(NS) + 1]
        push!(cases, (kind, v(1), s(2), v(3), v(2), n(3), s(1), v(4)))
    end
    for w in vcat(VB, SB)
        push!(cases, (7, reinterpret(Float64, w)))
    end
    for i in start:min(length(cases) - 1, start + count - 1)
        c = cases[i+1]
        k = c[1]
        line = if k == 1
            "colon " * @j(descS, c[2]:c[3]:c[4])
        elseif k == 2
            "rangelen " * @j(descS, range(c[2], c[5]; length=c[6]))
        elseif k == 3
            "startstep " * @j(descS, range(c[2]; step=c[3], length=c[6]))
        elseif k == 4
            "stopstep " * @j(descS, range(; stop=c[5], step=c[7], length=c[6]))
        elseif k == 5
            "lin " * @j(descL, LinRange(c[2], c[5], c[6]))
        elseif k == 6
            "bcast " * @j(r -> "$(@j(descSmall, r .+ c[8])) / $(@j(descSmall, r .* c[8])) / $(@j(descSmall, c[8] * r))", c[2]:c[3]:c[4])
        else
            a, b = Base.rat(c[2])
            "rat $a $b"
        end
        println(i, " ", line)
    end
end
main(parse(Int, get(ARGS, 1, "0")), parse(Int, get(ARGS, 2, "100000")))
