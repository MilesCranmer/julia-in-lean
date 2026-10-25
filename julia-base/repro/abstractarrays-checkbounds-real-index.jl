struct GenericVector{T,A<:AbstractVector{T}} <: AbstractVector{T}
    data::A
end

Base.size(A::GenericVector) = size(A.data)
Base.getindex(A::GenericVector, i::Int) = getindex(A.data, i)

function getindex_error(A, i)
    try
        A[i]
        return nothing
    catch err
        return err
    end
end

A = GenericVector([10, 20, 30])
bool_check = checkbounds(Bool, A, true)
float_check = checkbounds(Bool, A, 2.5)
bool_error = getindex_error(A, true)
float_error = getindex_error(A, 2.5)

println("Bool: checkbounds=", bool_check, " getindex=", repr(bool_error))
println("Float64: checkbounds=", float_check, " getindex=", repr(float_error))
if bool_check && float_check && bool_error isa ArgumentError && float_error isa ArgumentError
    println("REPRODUCED abstractarrays-checkbounds-real-index")
end
