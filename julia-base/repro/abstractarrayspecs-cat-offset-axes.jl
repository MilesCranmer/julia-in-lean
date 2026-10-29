# One root cause, exercised through each front end listed in the bug's covers field.
# No packages. Large positive offsets force BoundsError before any uninitialized
# output cell can be read. The block-diagonal example uses initialized zeros.
struct OV <: AbstractVector{Int}
    data::Vector{Int}
end
Base.size(v::OV) = size(v.data)
Base.axes(v::OV) = (Base.IdentityUnitRange(3:2+length(v.data)),)
Base.getindex(v::OV, i::Int) = (@boundscheck checkbounds(v, i); v.data[i-2])

struct OA{N} <: AbstractArray{Int,N}
    data::Array{Int,N}
    offsets::NTuple{N,Int}
end
Base.size(a::OA) = size(a.data)
Base.axes(a::OA) = map((o, n) -> Base.IdentityUnitRange(o+1:o+n), a.offsets, size(a.data))
Base.getindex(a::OA{N}, I::Vararg{Int,N}) where N =
    (@boundscheck checkbounds(a, I...); a.data[(I .- a.offsets)...])

x = OV([1, 2])
r = cat(x, [3, 4]; dims=(1, 2))
println("block diagonal: ", repr(r))
original = r == [0 0; 0 0; 1 3; 2 4] && r != [1 0; 2 0; 0 3; 0 4]

v = OV([20])
m = OA(reshape([40], 1, 1), (1, 3))
av = OA(reshape([1], 1, 1, 1), (9, 0, 0))
ah = OA(reshape([1], 1, 1, 1), (0, 9, 0))
b = reshape([2], 1, 1, 1)

# id, front end, arguments. Method locations are printed to verify the dispatch.
cases = [
    ("vcat-any", vcat, ("s", v)),
    ("hcat-any", hcat, ("s", m)),
    ("typed-vcat-any", Base.typed_vcat, (Int, v, 1)),
    ("typed-hcat-any", Base.typed_hcat, (Int, m, 1)),
    ("vcat-one", vcat, (av,)),
    ("vcat-two", vcat, (av, b)),
    ("vcat-arrays", vcat, (av, b, b)),
    ("vcat-mixed", vcat, (av, 1)),
    ("hcat-one", hcat, (ah,)),
    ("hcat-two", hcat, (ah, b)),
    ("hcat-arrays", hcat, (ah, b, b)),
    ("hcat-mixed", hcat, (ah, 1)),
    ("typed-vcat-one", Base.typed_vcat, (Int, av)),
    ("typed-vcat-two", Base.typed_vcat, (Int, av, b)),
    ("typed-vcat-arrays", Base.typed_vcat, (Int, av, b, b)),
    ("typed-hcat-one", Base.typed_hcat, (Int, ah)),
    ("typed-hcat-two", Base.typed_hcat, (Int, ah, b)),
    ("typed-hcat-arrays", Base.typed_hcat, (Int, ah, b, b)),
    ("cat-promote", Base._cat, (1, v, 1)),
    ("cat-inner", Base.__cat, (zeros(Int, 1), (1,), (true,), v)),
]
results = Bool[original]
for (id, f, args) in cases
    method = which(f, Tuple{map(typeof, args)...})
    wrong = try
        f(args...)
        false
    catch e
        println(id, " ", method.file, ":", method.line, " => ", typeof(e))
        e isa BoundsError
    end
    push!(results, wrong)
    wrong || println("NOT REPRODUCED ", id)
end
wrong_cat_t = try
    Base.cat_t(Int, v; dims=1)
    false
catch e
    println("cat-t => ", typeof(e))
    e isa BoundsError
end
push!(results, wrong_cat_t)
if all(results)
    println("REPRODUCED abstractarrayspecs-cat-offset-axes")
else
    error("At least one covered front end did not reproduce")
end
