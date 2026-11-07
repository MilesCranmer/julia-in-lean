struct OffsetBytes <: AbstractVector{UInt8}
    data::Vector{UInt8}
    first::Int
end

Base.size(v::OffsetBytes) = (length(v.data),)
Base.axes(v::OffsetBytes) = (v.first:(v.first + length(v.data) - 1),)
Base.IndexStyle(::Type{OffsetBytes}) = IndexLinear()
Base.getindex(v::OffsetBytes, i::Int) = v.data[i - v.first + 1]

source = OffsetBytes(UInt8[], 0)
pattern = OffsetBytes(UInt8[], 1)
first_match = findfirst(pattern, source)
last_match = findlast(pattern, source)
println("findfirst(empty, source) = ", first_match)
println("findlast(empty, source) = ", last_match)
if first_match != 0:-1 || last_match != 0:-1
    println("REPRODUCED strings-search-first-last-byte-pattern")
end
