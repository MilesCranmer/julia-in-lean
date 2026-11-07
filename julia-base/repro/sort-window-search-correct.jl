# This custom AbstractVector exposes UInt8 axes through the documented API.
struct Checked <: AbstractVector{Int}
    data::Vector{Int}
end
Base.size(v::Checked) = size(v.data)
Base.axes(::Checked) = (UInt8(1):UInt8(255),)
Base.IndexStyle(::Type{Checked}) = IndexLinear()
Base.getindex(v::Checked, i::Integer) =
    (1 <= i <= length(v.data) || throw(BoundsError(v, i)); v.data[Int(i)])

v = Checked(collect(1:255))
@assert firstindex(v) == UInt8(1)
@assert lastindex(v) == UInt8(255)
err = try
    searchsortedlast(v, 128)
catch e
    e
end
println(typeof(err), " at index ", err isa BoundsError ? repr(err.i) : "none")
if err isa BoundsError && err.i == 0
    println("REPRODUCED sort-window-search-correct")
end
