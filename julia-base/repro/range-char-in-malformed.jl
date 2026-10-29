# in(x::AbstractChar, r::AbstractRange{<:AbstractChar}) (range.jl:1495) tests membership by
# comparing x with minimum(r) and maximum(r) and the codepoint Int(x) with the step. The `in`
# docstring promises membership in the sense of `==` to an element of the collection. The malformed
# Char '\x41\x00\x00\x41' has codepoint 65 (that of 'A') and lies between 'A' and 'B' in Char order,
# but it is not == to 'A' or 'B'.
x = reinterpret(Char, 0x41000041)
r = 'A':'B'
println("x = ", repr(x), ", Int(x) = ", Int(x), ", collect(r) = ", collect(r))
println("x in r = ", x in r, ", any(==(x), r) = ", any(==(x), r))
if (x in r) && !any(==(x), r)
    println("REPRODUCED range-char-in-malformed")
else
    error("range-char-in-malformed did not reproduce")
end
