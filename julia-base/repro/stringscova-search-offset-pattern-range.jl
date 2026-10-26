struct OffsetBytes <: AbstractVector{UInt8}
    data::Vector{UInt8}
    first::Int
end

Base.size(v::OffsetBytes) = (length(v.data),)
Base.axes(v::OffsetBytes) = (v.first:(v.first + length(v.data) - 1),)
Base.IndexStyle(::Type{OffsetBytes}) = IndexLinear()
Base.getindex(v::OffsetBytes, i::Int) = v.data[i - v.first + 1]

haystack = OffsetBytes(UInt8[0x40, 0x52, 0x62, 0x63], 10)
pattern = OffsetBytes(UInt8[0x52, 0x62], 5)

forward = findnext(pattern, haystack, firstindex(haystack))
reverse = findprev(pattern, haystack, lastindex(haystack))
first_match = findfirst(pattern, haystack)
last_match = findlast(pattern, haystack)

println("findnext(pattern, haystack, 10) = ", forward)
println("findprev(pattern, haystack, 13) = ", reverse)
println("findfirst(pattern, haystack) = ", first_match)
println("findlast(pattern, haystack) = ", last_match)
println("expected = 11:12")

if forward == 11:16 && reverse == 11:16 && first_match == 11:16 && last_match == 11:16
    println("REPRODUCED stringscova-search-offset-pattern-range")
else
    println("NOT REPRODUCED stringscova-search-offset-pattern-range")
end
