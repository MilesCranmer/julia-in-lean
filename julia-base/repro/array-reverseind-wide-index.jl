struct HugeReverseVector <: AbstractVector{Int}
end
Base.size(::HugeReverseVector) = (typemax(Int),)
Base.getindex(::HugeReverseVector, i::Int) = i

v = HugeReverseVector()
i = Int128(1)
expected = Int128(typemax(Int))
actual = reverseind(v, i)
println("reverseind result=", actual, " expected=", expected)
@assert actual != expected
println("REPRODUCED array-reverseind-wide-index")
