# reverse of an unsigned StepRangeLen (range.jl:1446) rebuilds typeof(r) with negate(r.step), a
# signed integer, which no StepRangeLen{UInt8,UInt8,UInt8,Int} constructor accepts.
r = StepRangeLen(UInt8(1), UInt8(2), 3)
println("collect(r) = ", collect(r))
res = try
    collect(reverse(r))
catch e
    e
end
println("collect(reverse(r)) = ", res)
if res != reverse(collect(r))
    println("REPRODUCED range-srl-reverse-unsigned")
else
    error("range-srl-reverse-unsigned did not reproduce")
end
