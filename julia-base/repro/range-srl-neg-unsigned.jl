# -(r::StepRangeLen) (range.jl:1323) builds StepRangeLen{T,R,S,L}(-r.ref, -r.step, r.len, r.offset);
# for unsigned T the negated step wraps (-0x01 == 0xff), so element 3 of -r is 0 + 2 * 0xff == 510,
# which is not a UInt8, while the elementwise negation -r[3] == 0xfe exists.
r = StepRangeLen(UInt8(0), UInt8(1), 3)
want = .-collect(r)
got = try
    collect(-r)
catch e
    e
end
println("collect(r) = ", collect(r), ", .-collect(r) = ", want, ", collect(-r) = ", got)
if got != want
    println("REPRODUCED range-srl-neg-unsigned")
else
    error("range-srl-neg-unsigned did not reproduce")
end
