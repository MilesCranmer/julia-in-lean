struct StridedWrapper{T,N} <: AbstractArray{T,N}
    data::Array{T,N}
end
Base.size(A::StridedWrapper) = size(A.data)
Base.strides(A::StridedWrapper) = strides(A.data)
Base.getindex(A::StridedWrapper, I...) = getindex(A.data, I...)
A = StridedWrapper(reshape(collect(1:6), 2, 3))
actual = stride(A, 3)
expected = length(A)
println("size = ", size(A), "; strides = ", strides(A), "; stride(A, 3) = ", actual, "; length = ", expected)
if actual != expected
    println("REPRODUCED abstractarrays-stride-trailing-dimension")
else
    error("The trailing-dimension stride agrees with the contiguous element count")
end
