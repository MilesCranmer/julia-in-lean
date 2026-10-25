b = symdiff!(BitSet([1]), [2, 2])
s = symdiff!(Set([1]), [2, 2])
c = symdiff(BitSet([1]), [2, 2])
println(collect(b), " ", sort!(collect(s)), " ", collect(c))
if collect(b) == [1] && sort!(collect(s)) == [1, 2]
    println("REPRODUCED bitarrays-bitset-symdiff-duplicates")
end
