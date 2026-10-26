# IdentityUnitRange(r)[m] for the Bool StepRange mask m = StepRange(true, -1, false)
# (elements [true, false]) returns an empty range instead of the first element:
# getindex(S::IdentityUnitRange, i::StepRange{Bool}) (base/indices.jl:395-399) builds
# range(first(i) ? first(S) : last(S), length = last(i), step = Int(step(i))), and
# last(i) is false, so the length is 0.
m = StepRange(true, -1, false)
s = Base.IdentityUnitRange(1:2)
r = s[m]
expected = collect(s)[collect(m)]
println("collect(StepRange(true, -1, false)) = ", collect(m))
println("Base.IdentityUnitRange(1:2)[StepRange(true, -1, false)] = ", repr(r), " (", length(r), " elements)")
println("collect(Base.IdentityUnitRange(1:2))[collect(StepRange(true, -1, false))] = ", expected)
if collect(r) != expected
    println("REPRODUCED reducecov-identityrange-bool-step")
end
