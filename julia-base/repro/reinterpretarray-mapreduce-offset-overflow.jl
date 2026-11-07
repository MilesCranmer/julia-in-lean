struct LastIndexVector{T} <: AbstractVector{T}
    value::T
end
Base.size(::LastIndexVector) = (1,)
Base.axes(::LastIndexVector) = (typemax(Int):typemax(Int),)
Base.firstindex(::LastIndexVector) = typemax(Int)
Base.lastindex(::LastIndexVector) = typemax(Int)
Base.IndexStyle(::Type{<:LastIndexVector}) = IndexLinear()
Base.eachindex(::IndexLinear, a::LastIndexVector) = axes(a, 1)
Base.getindex(a::LastIndexVector, i::Int) = i == typemax(Int) ? a.value : throw(BoundsError(a, i))
a = reinterpret(reshape, UInt8, LastIndexVector(UInt16(0x0102)))
expected = sum(a[Base.SCartesianIndex2{2}(i, typemax(Int))] for i in 1:2)
try
    actual = sum(a)
    error("NOT REPRODUCED: sum returned $actual, expected $expected")
catch err
    if err isa BoundsError && Tuple(err.i) == (typemin(Int),)
        println("sum of valid two-byte view should be $expected; it read parent index ", err.i)
        println("REPRODUCED reinterpretarray-mapreduce-offset-overflow")
        println("REPRODUCED memsafety-reinterpretarray-mapreduce")
    else
        rethrow()
    end
end
println("REPRODUCED reinterpretarray-mapreduce-routing")
