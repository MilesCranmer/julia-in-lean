struct HighAxisMatrix <: AbstractMatrix{Int}
    value::Base.RefValue{Int}
end
Base.size(::HighAxisMatrix) = (1, 1)
Base.axes(::HighAxisMatrix) = ntuple(_ -> Base.IdentityUnitRange(typemax(Int):typemax(Int)), 2)
Base.getindex(a::HighAxisMatrix, i::Int, j::Int) = a.value[]
Base.setindex!(a::HighAxisMatrix, value, i::Int, j::Int) = (a.value[] = value)

src = HighAxisMatrix(Ref(42))
dest = HighAxisMatrix(Ref(-1))
permutedims!(dest, src, (2, 1))
@assert dest.value[] == -1
@assert src.value[] == 42
println("destination = ", dest.value[], "; source = ", src.value[])
println("REPRODUCED permuteddims-tile-ranges")
