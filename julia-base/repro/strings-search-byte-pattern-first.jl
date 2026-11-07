struct EmptyOffsetBytes <: AbstractVector{UInt8}
    first::Int
end

Base.size(::EmptyOffsetBytes) = (0,)
Base.axes(v::EmptyOffsetBytes) = (v.first:(v.first - 1),)
Base.IndexStyle(::Type{EmptyOffsetBytes}) = IndexLinear()
Base.getindex(v::EmptyOffsetBytes, i::Int) = throw(BoundsError(v, i))

haystack = EmptyOffsetBytes(0)
pattern = UInt8[]
match_range = findnext(pattern, haystack, 0)
println("findnext = ", match_range)
match_range != (0:-1) && println("REPRODUCED strings-search-byte-pattern-first")
