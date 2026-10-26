# replace(new, A) on an AbstractSet that is not a Set copies A to res and then
# walks A, doing pop!(res, x); push!(res, new(x)) one element at a time
# (base/set.jl:931-940). A new value that equals a later old value is popped
# again, so the result loses elements. replace! (res === A) collects the pairs
# first and gives the right answer.
a = replace(x -> x + 1, BitSet([1, 2]))
b = replace!(x -> x + 1, BitSet([1, 2]))
println("replace(x -> x + 1, BitSet([1, 2]))  = ", a)
println("replace!(x -> x + 1, BitSet([1, 2])) = ", b)
c = replace(BitSet([1, 2]), 1 => 2, 2 => 1)
println("replace(BitSet([1, 2]), 1 => 2, 2 => 1) = ", c)
d = sort!(collect(replace(x -> x + 1, Base.IdSet{Int}([1, 2]))))
println("collect(replace(x -> x + 1, IdSet{Int}([1, 2]))) = ", d)
if a != BitSet([2, 3]) && b == BitSet([2, 3]) && c != BitSet([1, 2]) && d != [2, 3]
    println("REPRODUCED bitsetscov-replace-generic-set")
end
