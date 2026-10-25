struct GenericArray{T,N,A<:Array{T,N}} <: AbstractArray{T,N}
    data::A
end

Base.size(A::GenericArray) = size(A.data)
Base.getindex(A::GenericArray{T,N}, I::Vararg{Int,N}) where {T,N} = getindex(A.data, I...)
Base.setindex!(A::GenericArray{T,N}, x, I::Vararg{Int,N}) where {T,N} = setindex!(A.data, x, I...)
Base.similar(::GenericArray, ::Type{T}, dims::Dims{N}) where {T,N} = GenericArray(Array{T,N}(undef, dims))

struct OffsetVector{T,A<:Vector{T}} <: AbstractVector{T}
    data::A
    offset::Int
end

Base.size(A::OffsetVector) = size(A.data)
Base.axes(A::OffsetVector) = (Base.IdentityUnitRange((A.offset + 1):(A.offset + length(A.data))),)
Base.IndexStyle(::Type{<:OffsetVector}) = IndexLinear()
Base.getindex(A::OffsetVector, i::Int) = A.data[i - A.offset]
Base.setindex!(A::OffsetVector, x, i::Int) = (A.data[i - A.offset] = x)
Base.similar(A::OffsetVector, ::Type{T}, inds::Tuple{Base.IdentityUnitRange}) where {T} =
    OffsetVector(Vector{T}(undef, length(inds[1])), first(inds[1]) - 1)
Base.similar(::OffsetVector, ::Type{T}, dims::Dims{1}) where {T} = OffsetVector(Vector{T}(undef, dims[1]), 0)
Base.dataids(A::OffsetVector) = Base.dataids(A.data)

function out(f)
    try
        return "ok:" * string(f())
    catch err
        return "error:" * string(nameof(typeof(err)))
    end
end

M = GenericArray(reshape(collect(1:6), 2, 3))
for d in (-1, 0, 1, 2, 3, 4)
    println("size ", d, " ", out(() -> size(M, d)))
    println("axes ", d, " ", try a = axes(M, d); "ok:$(first(a)):$(length(a))" catch err; "error:$(nameof(typeof(err)))" end)
end
println("scalar-int ", Base.checkindex(Bool, axes(M, 2), 1))
println("scalar-bool ", Base.checkindex(Bool, axes(M, 2), true))
println("to-bool ", out(() -> Base.to_index(true)))
println("range ", Base.checkindex(Bool, 1:6, 2:5))
println("empty-range ", Base.checkindex(Bool, 1:6, 7:6))
println("coords-full ", Base.checkbounds_indices(Bool, axes(M), (2, 3)))
println("coords-short ", Base.checkbounds_indices(Bool, axes(M), (2,)))
println("coords-trail1 ", Base.checkbounds_indices(Bool, axes(M), (2, 3, 1)))
println("coords-trail2 ", Base.checkbounds_indices(Bool, axes(M), (2, 3, 2)))
println("linear-short ", checkbounds(Bool, M, 2))
println("mask-good ", checkbounds(Bool, M, trues(2, 3)))
println("mask-bad ", checkbounds(Bool, M, trues(3, 2)))
dest = OffsetVector([0, 0, 0, 0], 4)
src = OffsetVector([7, 8, 9], -1)
copyto!(dest, src)
println("copy ", join(dest.data, ","))
short = OffsetVector([9, 9], 0)
println("copy-short ", try copyto!(short, src); join(short.data, ",") catch err; "error:$(nameof(typeof(err)))" end)
overlap = GenericArray([1, 2, 3, 4])
copyto!(view(overlap, 2:4), view(overlap, 1:3))
println("copy-overlap ", join(overlap.data, ","))
raw = Vector{Any}(undef, 3)
raw[1] = 10
raw[3] = 30
off = OffsetVector(raw, -2)
println("each ", join(eachindex(off), ","))
assigned = String[]
for i in (-1, 0, 1, true)
    push!(assigned, try string(isassigned(off, i)) catch err; "error:$(nameof(typeof(err)))" end)
end
println("assigned ", join(assigned, ","))
println("require-normal ", try Base.require_one_based_indexing(M); "ok" catch; "error" end)
println("require-offset ", try Base.require_one_based_indexing(off); "ok" catch err; "error:$(nameof(typeof(err)))" end)
S = similar(GenericArray([1, 2]), Int, 4)
println("similar ", firstindex(S), ":", length(S))
println("vcat ", join(vcat(GenericArray([1, 2]), GenericArray([3, 4])), ","))
println("hcat ", size(hcat(GenericArray([1, 2]), GenericArray([3, 4])), 1))
r = OffsetVector([1, 2, 3, 4], -2)
println("reverse ", join(reverse(r).data, ","))
fill!(r, 6)
println("fill ", join(r.data, ","))
println("empty ", isempty(GenericArray(Int[])), ",", isempty(r))
println("COUNT 37")
