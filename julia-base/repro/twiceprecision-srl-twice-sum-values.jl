# sum(r::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision}) multiplies r.ref
# by length(r) via *(x::TwicePrecision{<:IEEEFloat}, v::Integer), which truncates
# x.hi by top_set_bit(abs(v) - 1) bits so ((x.hi - u) + x.lo) * v overflows 53
# bits of precision when length(r) >= 2^27, losing exactness on symmetric integer
# Float64 ranges whose exact sum is 0.
r = -51540000771.0:3.0:51540000771.0
s = sum(r)
println("r = ", r, ", length(r) = ", length(r), ", first(r) + last(r) = ", first(r) + last(r))
println("sum(r) = ", s, " (expected 0.0)")
if s != 0.0
    println("REPRODUCED twiceprecision-srl-twice-sum-values")
end
