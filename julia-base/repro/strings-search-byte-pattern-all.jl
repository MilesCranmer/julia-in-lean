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
matches = findall(pattern, source; overlap=true)
println("findall(empty, source; overlap=true) = ", matches)
if matches != [0:-1]
    println("REPRODUCED strings-search-byte-pattern-all")
end
