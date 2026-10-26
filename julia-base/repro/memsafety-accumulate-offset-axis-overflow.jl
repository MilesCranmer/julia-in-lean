if isempty(ARGS)
    cmd = `$(Base.julia_cmd()) --startup-file=no --check-bounds=yes $(@__FILE__) child`
    io = IOBuffer()
    proc = run(pipeline(ignorestatus(cmd); stdout=io, stderr=io))
    output = String(take!(io))
    print(output)
    println("child exit code = ", proc.exitcode, ", signal = ", proc.termsignal)
    if occursin("BoundsError", output) && occursin("accumulate.jl:392", output)
        println("REPRODUCED memsafety-accumulate-offset-axis-overflow")
    end
    exit()
end

struct ExtremeVector{T} <: AbstractVector{T}
    data::Vector{T}
end

Base.size(::ExtremeVector) = (1,)
Base.axes(::ExtremeVector) = (Base.IdentityUnitRange(typemax(Int):typemax(Int)),)
Base.IndexStyle(::Type{<:ExtremeVector}) = IndexLinear()
Base.getindex(a::ExtremeVector, i::Int) =
    i == typemax(Int) ? a.data[1] : throw(BoundsError(a, i))
Base.setindex!(a::ExtremeVector, x, i::Int) =
    i == typemax(Int) ? (a.data[1] = x) : throw(BoundsError(a, i))

input = ExtremeVector([1])
output = ExtremeVector([0])
accumulate!(+, output, input; dims=1)
