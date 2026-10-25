# isempty(Iterators.take(itr, 0)) is false when itr is a nonempty stateful iterator
s = Iterators.Stateful([1, 2, 3])
t = Iterators.take(s, 0)
e1 = isempty(t)
println("isempty(take(Stateful([1,2,3]), 0)) = ", e1, ", collect = ", collect(t))
e2 = isempty(Iterators.take(eachline(IOBuffer("a\nb\n")), 0))
println("isempty(take(eachline(io), 0)) = ", e2)
# zip promises not to advance a stateful iterator when another one is finished
a = Iterators.Stateful([10, 20, 30])
z = collect(zip(a, Iterators.take(Iterators.Stateful([1]), 0)))
rest_a = collect(a)
println("collect(zip(a, take(Stateful([1]), 0))) = ", z, ", then collect(a) = ", rest_a)
if !e1 && !e2 && isempty(z) && rest_a == [20, 30]
    println("REPRODUCED iterators-take-isdone-zero")
end
