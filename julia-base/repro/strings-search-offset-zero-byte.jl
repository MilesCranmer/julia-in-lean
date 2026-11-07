struct OffsetBytes <: AbstractVector{UInt8}
    data::Vector{UInt8}
    origin::Int
end
Base.size(a::OffsetBytes) = size(a.data)
Base.axes(a::OffsetBytes) = (a.origin:(a.origin + length(a.data) - 1),)
Base.firstindex(a::OffsetBytes) = a.origin
Base.lastindex(a::OffsetBytes) = a.origin + length(a.data) - 1
Base.IndexStyle(::Type{OffsetBytes}) = IndexLinear()
Base.keys(a::OffsetBytes) = axes(a, 1)
Base.eachindex(a::OffsetBytes) = axes(a, 1)
function Base.getindex(a::OffsetBytes, i::Int)
    checkbounds(a, i)
    return a.data[i - a.origin + 1]
end

source = OffsetBytes(UInt8[0x41], 0)
pattern = UInt8[0x41]
@assert source[0] == pattern[1]
forward = findnext(pattern, source, 0)
first_match = findfirst(pattern, source)
all_matches = findall(pattern, source; overlap=true)
backward = try
    findprev(pattern, source, 0)
catch err
    err
end
@assert forward === nothing && first_match === nothing && isempty(all_matches)
@assert backward isa BoundsError
println("axes(source) = ", axes(source), "; source[0] = ", source[0])
println("findnext = ", forward, "; findfirst = ", first_match, "; findall(overlap=true) = ", all_matches)
println("findprev = ", nameof(typeof(backward)))
for id in ("strings-search-offset-zero-byte", "strings-search-byte-pattern-first",
           "strings-search-byte-pattern-last", "strings-search-first-last-byte-pattern",
           "strings-search-byte-pattern-all")
    println("REPRODUCED ", id)
end
