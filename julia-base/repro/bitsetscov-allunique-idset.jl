# allunique(::Union{AbstractSet,AbstractDict}) = true and
# allequal(::Union{AbstractSet,AbstractDict}) = length(c) <= 1
# (base/set.jl:544, 658) assume the elements are pairwise non-isequal. An IdSet
# or IdDict keeps isequal elements that are not ===, e.g. 1 and 1.0.
s = Base.IdSet{Any}(Any[1, 1.0])
d = IdDict{Any,Int}(1 => 2, 1.0 => 2)
println("allunique(s) = ", allunique(s), ", allunique(collect(s)) = ", allunique(collect(s)))
println("allequal(s) = ", allequal(s), ", allequal(collect(s)) = ", allequal(collect(s)))
println("allunique(d) = ", allunique(d), ", allunique(collect(d)) = ", allunique(collect(d)))
println("allequal(d) = ", allequal(d), ", allequal(collect(d)) = ", allequal(collect(d)))
if allunique(s) != allunique(collect(s)) && allequal(s) != allequal(collect(s)) &&
        allunique(d) != allunique(collect(d)) && allequal(d) != allequal(collect(d))
    println("REPRODUCED bitsetscov-allunique-idset")
end
