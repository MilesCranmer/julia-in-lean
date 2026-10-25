struct OffsetPermutation <: AbstractVector{Int}
    data::Vector{Int}
end

Base.size(p::OffsetPermutation) = size(p.data)
Base.axes(p::OffsetPermutation) = (0:length(p.data)-1,)
Base.IndexStyle(::Type{OffsetPermutation}) = IndexCartesian()
Base.getindex(p::OffsetPermutation, i::Int) = p.data[i + 1]
Base.iterate(p::OffsetPermutation, state=1) = state > length(p.data) ? nothing : (p.data[state], state + 1)

p = OffsetPermutation([2, 3, 1])
valid = isperm(p)
err = try
    invperm(p)
    nothing
catch caught
    caught
end

println("axes(p):    ", axes(p))
println("isperm(p):  ", valid)
println("invperm(p): ", nameof(typeof(err)), ": ", sprint(showerror, err))

if valid && err isa ArgumentError
    println("REPRODUCED combinatorics-invperm-offset")
end
