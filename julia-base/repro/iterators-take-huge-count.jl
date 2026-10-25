# take/first/last convert the count with Int(n), so counts above typemax(Int) throw
show_r(x) = x isa Exception ? sprint(showerror, x) : repr(x)
a = try first((1, 2, 3), typemax(UInt)) catch e; e end
b = try last((1, 2, 3), typemax(UInt)) catch e; e end
c = try collect(Iterators.take(1:3, typemax(UInt))) catch e; e end
d = first([1, 2, 3], typemax(UInt))
println("first((1,2,3), typemax(UInt)) = ", show_r(a))
println("last((1,2,3), typemax(UInt)) = ", show_r(b))
println("collect(take(1:3, typemax(UInt))) = ", show_r(c))
println("first([1,2,3], typemax(UInt)) = ", show_r(d))
a isa InexactError && b isa InexactError && d == [1, 2, 3] && println("REPRODUCED iterators-take-huge-count")
