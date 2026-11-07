struct MaxAxisIntVector <: AbstractVector{Int}
    value::Int
end

Base.size(::MaxAxisIntVector) = (1,)
Base.axes(::MaxAxisIntVector) = (typemax(Int):typemax(Int),)
Base.IndexStyle(::Type{MaxAxisIntVector}) = IndexLinear()
Base.getindex(v::MaxAxisIntVector, i::Int) =
    i == typemax(Int) ? v.value : throw(BoundsError(v, i))

v = MaxAxisIntVector(0)
first = searchsortedfirst(v, 1)
result = searchsorted(v, 1)
found = insorted(1, v)

if first <= lastindex(v)
    println("REPRODUCED sort-vector-search-correct")
end
if !isempty(result)
    println("REPRODUCED sort-searchsorted-equivalent-range")
end
if found
    println("REPRODUCED sort-insorted-vector-correct")
end
