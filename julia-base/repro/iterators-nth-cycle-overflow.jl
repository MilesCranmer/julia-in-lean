# nth(cycle(v, m), k) checks k > length(v) * m with a wrapping multiplication
c = Iterators.cycle([1, 2, 3], 2^62)
r = try
    Iterators.nth(c, 1)
catch e
    e
end
println("nth(cycle([1,2,3], 2^62), 1) = ", r isa Exception ? sprint(showerror, r) : repr(r))
println("first(cycle([1,2,3], 2^62)) = ", first(c))
r isa BoundsError && println("REPRODUCED iterators-nth-cycle-overflow")
