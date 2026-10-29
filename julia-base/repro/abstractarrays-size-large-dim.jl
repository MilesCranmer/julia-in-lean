struct GenericMatrix <: AbstractMatrix{Int} end

Base.size(::GenericMatrix) = (2, 3)
Base.getindex(::GenericMatrix, i::Int, j::Int) = i + 2 * (j - 1)

function result(f)
    try
        return f()
    catch err
        return err
    end
end

A = GenericMatrix()
u = UInt(typemax(Int)) + 1
w = Int128(typemax(Int)) + 1
size_u = result(() -> size(A, u))
size_w = result(() -> size(A, w))
axes_u = result(() -> axes(A, u))
axes_w = result(() -> axes(A, w))

println("UInt64 size=", nameof(typeof(size_u)), " axes=", repr(axes_u))
println("Int128 size=", nameof(typeof(size_w)), " axes=", repr(axes_w))
cat_u = result(() -> Base.cat_size(A, u))
cat_w = result(() -> Base.cat_size(A, w))
println("UInt64 cat_size=", nameof(typeof(cat_u)))
println("Int128 cat_size=", nameof(typeof(cat_w)))
if size_u isa InexactError && size_w isa InexactError && axes_u == Base.OneTo(1) && axes_w == Base.OneTo(1) &&
        cat_u isa InexactError && cat_w isa InexactError
    println("REPRODUCED abstractarrays-size-large-dim")
end
