# product of iterators that report isdone == true throws once all of them are exhausted
show_r(x) = x isa Exception ? sprint(showerror, x) : repr(x)
a = try collect(Iterators.product(Iterators.Stateful([1, 2]))) catch e; e end
b = try collect(Iterators.product(eachline(IOBuffer("a\nb")))) catch e; e end
c = try collect(Iterators.product(Iterators.Stateful([1]), Iterators.Stateful([2]))) catch e; e end
println("collect(product(Stateful([1,2]))) = ", show_r(a))
println("collect(product(eachline(io))) = ", show_r(b))
println("collect(product(Stateful([1]), Stateful([2]))) = ", show_r(c))
println("collect(product([1,2])) = ", repr(collect(Iterators.product([1, 2]))))
a isa ArgumentError && b isa ArgumentError && println("REPRODUCED iterators-product-stateful-done")
