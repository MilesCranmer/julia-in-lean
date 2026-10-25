s = "é€"
println("partition(s, 2) = ", repr(collect(Iterators.partition(s, 2))))
r = try
    collect(Iterators.partition(s, typemax(Int)))
catch e
    e
end
println("partition(s, typemax(Int)) = ", r isa Exception ? sprint(showerror, r) : repr(r))
r isa BoundsError && println("REPRODUCED strings-partition-overflow")
