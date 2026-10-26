# A Base.Slice indexed with an integer that is not an Int returns the element at that
# position instead of the integer itself. Slice only defines getindex(S::Slice, i::Int)
# (base/indices.jl:350); other integers reach the generic AbstractRange method, which
# computes first(S) + (i - 1). For an offset Slice the two disagree.
s = Base.Slice(3:5)
a = s[3]
b = s[Int8(3)]
c = s[UInt(4)]
println("Base.Slice(3:5)[3] = ", a)
println("Base.Slice(3:5)[Int8(3)] = ", b)
println("Base.Slice(3:5)[UInt(4)] = ", c)
println("Base.IdentityUnitRange(3:5)[Int8(3)] = ", Base.IdentityUnitRange(3:5)[Int8(3)])
if a == 3 && b != 3
    println("REPRODUCED reducecov-slice-integer-index")
end
