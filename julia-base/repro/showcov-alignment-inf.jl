# Base.alignment(io, x::Real) splits the printed number at the first '.', 'e',
# 'E', 'f' or 'F' (base/show.jl:3194-3199); the 'f' of Inf is taken for a
# Float32 exponent marker, so Inf is aligned on its last letter.
for x in (1.5, Inf, -Inf, NaN, Inf32)
    println(rpad(repr(x), 6), " alignment = ", Base.alignment(stdout, x))
end
s = sprint(show, MIME"text/plain"(), [1.5, Inf, NaN])
println(s)
if Base.alignment(stdout, Inf) == (2, 1) && Base.alignment(stdout, NaN) == (3, 0)
    println("REPRODUCED showcov-alignment-inf")
end
