# drop(drop(itr, a), b) adds a + b with wraparound
r = try
    collect(Iterators.drop(Iterators.drop([1, 2, 3], typemax(Int)), 1))
catch e
    e
end
println("collect(drop(drop([1,2,3], typemax(Int)), 1)) = ", r isa Exception ? sprint(showerror, r) : repr(r))
println("collect(drop([1,2,3], typemax(Int))) = ", repr(collect(Iterators.drop([1, 2, 3], typemax(Int)))))
r isa ArgumentError && println("REPRODUCED iterators-drop-drop-overflow")
