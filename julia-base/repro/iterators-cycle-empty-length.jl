# cycle(v) claims IsInfinite even for empty v, so take/zip report lengths that are never produced
v = Int[]
t = Iterators.take(Iterators.cycle(v), 3)
n = 0
for _ in t
    global n += 1
end
println("length(take(cycle(Int[]), 3)) = ", length(t), ", elements yielded = ", n)
f = first(Iterators.cycle(v), 3)
println("first(cycle(Int[]), 3) has length ", length(f))
s = first(Iterators.cycle(String[]), 2)
println("first(cycle(String[]), 2) = ", repr(s))
z = collect(zip(Iterators.cycle(v), 1:3))
println("length(collect(zip(cycle(Int[]), 1:3))) = ", length(z))
if length(t) == 3 && n == 0 && length(f) == 3 && length(s) == 2 && !isassigned(s, 1) && length(z) == 3
    println("REPRODUCED iterators-cycle-empty-length")
end
