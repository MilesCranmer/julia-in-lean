# partition(itr, n) of a non-array iterator allocates a Vector of n slots for every chunk
r = try collect(Iterators.partition((1, 2, 3), typemax(Int))) catch e; e end
println("collect(partition((1,2,3), typemax(Int))) = ", r isa Exception ? sprint(showerror, r) : repr(r))
println("collect(partition([1,2,3], typemax(Int))) = ", repr(collect(Iterators.partition([1, 2, 3], typemax(Int)))))
f() = first(Iterators.partition((i for i in 1:3), 10^8))
f()
b = @allocated f()
println("first chunk of partition((i for i in 1:3), 10^8) allocates ", b, " bytes")
r isa ArgumentError && b > 10^8 && println("REPRODUCED iterators-partition-generic-alloc")
