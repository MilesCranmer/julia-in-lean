struct VirtualAscii <: AbstractString end
Base.ncodeunits(::VirtualAscii) = typemax(Int)
Base.codeunit(::Type{VirtualAscii}) = UInt8
Base.codeunit(s::VirtualAscii, i::Integer) = 1 <= i <= typemax(Int) ? UInt8('a') : throw(BoundsError(s, i))
Base.isvalid(::VirtualAscii, i::Integer) = 1 <= i <= typemax(Int)
Base.firstindex(::VirtualAscii) = 1
Base.lastindex(::VirtualAscii) = typemax(Int)
Base.length(::VirtualAscii) = typemax(Int)
Base.getindex(s::VirtualAscii, i::Integer) = isvalid(s, i) ? 'a' : throw(BoundsError(s, i))
Base.thisind(s::VirtualAscii, i::Int) = 0 <= i <= typemax(Int) ? i : throw(BoundsError(s, i))
Base.nextind(::VirtualAscii, i::Int) = i + 1
Base.prevind(::VirtualAscii, i::Int) = i - 1
struct NoDelimiter end
Base.findnext(::NoDelimiter, ::VirtualAscii, ::Integer) = nothing

iterator = eachsplit(VirtualAscii(), NoDelimiter(); limit=1, keepempty=true)
first = iterate(iterator)
@assert first !== nothing
second = iterate(iterator, first[2])
@assert second !== nothing
third = iterate(iterator, second[2])
@assert third !== nothing
@assert first[2][1] == second[2][1] == third[2][1] == typemin(Int) + 1
@assert first[2][2] == second[2][2] == third[2][2] == 1
@assert ncodeunits(first[1]) == typemax(Int)
@assert ncodeunits(second[1]) == ncodeunits(third[1]) == -1
println("limit=1 emitted byte counts: ", (ncodeunits(first[1]), ncodeunits(second[1]), ncodeunits(third[1])))
println("states: ", (first[2], second[2], third[2]))
println("REPRODUCED stringutil-split-sentinel-overflow")
