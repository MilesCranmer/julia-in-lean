# The generic replacement branch for BitSet, IdSet, and IdDict removes and
# inserts each replacement before processing the next original element
# (base/set.jl:931-940). A later removal can erase an earlier replacement.
# The mutating branch collects replacements before removing and inserting.
println("JULIA ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)
a = replace(x -> x + 1, BitSet([1, 2]))
b = replace!(x -> x + 1, BitSet([1, 2]))
println("replace(x -> x + 1, BitSet([1, 2]))  = ", a)
println("replace!(x -> x + 1, BitSet([1, 2])) = ", b)
c = replace(BitSet([1, 2]), 1 => 2, 2 => 1)
println("replace(BitSet([1, 2]), 1 => 2, 2 => 1) = ", c)
d = sort!(collect(replace(x -> x + 1, Base.IdSet{Int}([1, 2]))))
println("collect(replace(x -> x + 1, IdSet{Int}([1, 2]))) = ", d)
source = IdDict(1 => :one, 2 => :two)
swapkey(pair) = (3 - first(pair)) => last(pair)
swapped = replace(swapkey, source)
inplace = replace!(swapkey, copy(source))
expected = IdDict(2 => :one, 1 => :two)
println("IdDict source = ", repr(sort!(collect(source); by=first)))
println("replace IdDict key swap = ", repr(sort!(collect(swapped); by=first)))
println("replace! IdDict key swap = ", repr(sort!(collect(inplace); by=first)))
println("expected IdDict key swap = ", repr(sort!(collect(expected); by=first)))
idbug = length(swapped) == 1 && !isequal(swapped, expected) &&
    isequal(inplace, expected) && length(source) == 2 &&
    source[1] === :one && source[2] === :two
if a != BitSet([2, 3]) && b == BitSet([2, 3]) && c != BitSet([1, 2]) &&
        d != [2, 3] && idbug
    println("REPRODUCED bitsetscov-replace-generic-set")
end
