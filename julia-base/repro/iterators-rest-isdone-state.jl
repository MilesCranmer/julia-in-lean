# isempty(rest) after Iterators.peel ignores the state stored in the Rest
itr = Iterators.take(Iterators.Stateful([1, 2, 3]), 1)
x, r = Iterators.peel(itr)
e = isempty(r)
c = collect(r)
println("peel(take(Stateful([1,2,3]), 1)) = (", x, ", r); isempty(r) = ", e, ", collect(r) = ", c)
io = IOBuffer("a\nb\nc\n")
y, r2 = Iterators.peel(Iterators.take(eachline(io), 1))
e2 = isempty(r2)
println("peel(take(eachline(io), 1)): isempty(rest) = ", e2, ", collect(rest) = ", collect(r2))
if !e && isempty(c) && !e2
    println("REPRODUCED iterators-rest-isdone-state")
end
