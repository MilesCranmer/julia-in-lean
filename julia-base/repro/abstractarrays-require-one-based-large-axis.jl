struct HugeAxisVector <: AbstractVector{Int} end

Base.size(::HugeAxisVector) = (1,)
Base.axes(::HugeAxisVector) = (Base.IdentityUnitRange(typemax(UInt):typemax(UInt)),)
Base.getindex(::HugeAxisVector, ::Int) = 1

function result(f)
    try
        return f()
    catch err
        return err
    end
end

A = HugeAxisVector()
offset_result = result(() -> Base.has_offset_axes(A))
require_result = result(() -> Base.require_one_based_indexing(A))
println("has_offset_axes=", nameof(typeof(offset_result)))
println("require_one_based_indexing=", nameof(typeof(require_result)))
if offset_result isa InexactError && require_result isa InexactError
    println("REPRODUCED abstractarrays-require-one-based-large-axis")
end
