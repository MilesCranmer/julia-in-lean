mutable struct EndAtMaxVector{T} <: AbstractVector{T}
    values::Vector{T}
    first::Int
    deletions::Vector{Tuple{Int,Int}}
end

Base.size(v::EndAtMaxVector) = size(v.values)
Base.axes(v::EndAtMaxVector) = (firstindex(v):lastindex(v),)
Base.firstindex(v::EndAtMaxVector) = v.first
Base.lastindex(v::EndAtMaxVector) = v.first + length(v.values) - 1
Base.IndexStyle(::Type{<:EndAtMaxVector}) = IndexLinear()
Base.iterate(v::EndAtMaxVector, state::Int=1) =
    state > length(v.values) ? nothing : (v.values[state], state + 1)

function Base.getindex(v::EndAtMaxVector, i::Int)
    firstindex(v) <= i <= lastindex(v) || throw(BoundsError(v, i))
    v.values[i - firstindex(v) + 1]
end

function Base.setindex!(v::EndAtMaxVector, value, i::Int)
    firstindex(v) <= i <= lastindex(v) || throw(BoundsError(v, i))
    v.values[i - firstindex(v) + 1] = value
    v
end

function Base.deleteat!(v::EndAtMaxVector, indices::AbstractUnitRange{<:Integer})
    push!(v.deletions, (first(indices), last(indices)))
    isempty(indices) && return v
    firstindex(v) <= first(indices) <= lastindex(v) || throw(BoundsError(v, indices))
    firstindex(v) <= last(indices) <= lastindex(v) || throw(BoundsError(v, indices))
    deleteat!(v.values, (first(indices) - firstindex(v) + 1):(last(indices) - firstindex(v) + 1))
    v
end

function main()
    v = EndAtMaxVector([11, 22], typemax(Int) - 1, Tuple{Int,Int}[])
    @assert length(v) == 2
    @assert lastindex(v) == typemax(Int)
    @assert iterate(v) == (11, 2)
    @assert iterate(v, 2) == (22, 3)
    @assert iterate(v, 3) === nothing
    failure = try
        filter!(_ -> true, v)
        nothing
    catch error
        error
    end
    println("VERSION ", VERSION)
    println("AXES ", axes(v))
    println("DELETE_CALLS ", v.deletions)
    println("RESULT ", typeof(failure))
    println("VALUES ", v.values)
    @assert failure isa BoundsError
    @assert v.deletions == [(typemin(Int), typemax(Int))]
    @assert v.values == [11, 22]
    println("REPRODUCED array-filter-bang-native-axes")
end

main()
