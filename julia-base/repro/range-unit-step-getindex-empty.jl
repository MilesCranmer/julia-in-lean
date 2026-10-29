# getindex(r::AbstractUnitRange, s::StepRange{T}) (range.jl:1034) computes the stop of an empty
# index range as `_empty_stop(start, step(s))` (range.jl:1002), which throws OverflowError when the
# start index maps to typemin(T). Indexing with an empty in-bounds range should return an empty
# range: collect(r)[collect(s)] is empty.
r = Int8(-128):Int8(127)
s = Int8(1):Int8(1):Int8(0)
println("isempty(s) = ", isempty(s), ", collect(r)[collect(s)] = ", collect(r)[collect(s)])
got = try
    r[s]
catch e
    e
end
println("r[s] = ", got)
if got isa Exception
    println("REPRODUCED range-unit-step-getindex-empty")
else
    error("range-unit-step-getindex-empty did not reproduce")
end
