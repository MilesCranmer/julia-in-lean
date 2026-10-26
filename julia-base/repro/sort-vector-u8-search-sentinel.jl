# A vector that keeps its bounds check under the caller's @inbounds, so the
# invalid read is reported instead of reading arbitrary memory.
struct Checked <: AbstractVector{Int}
    data::Vector{Int}
end
Base.size(v::Checked) = size(v.data)
Base.getindex(v::Checked, i::Integer) = (1 <= i <= length(v.data) || throw(BoundsError(v, i)); v.data[i])

v = Checked(collect(1:255))
println(searchsortedlast(v, 128, 1, 255, Base.Order.Forward))
err = try
    searchsortedlast(v, 128, 0x01, 0xff, Base.Order.Forward)
catch e
    e
end
println(typeof(err), " at index ", repr(err.i))
if err isa BoundsError && err.i == 0
    println("REPRODUCED sort-vector-u8-search-sentinel")
end
