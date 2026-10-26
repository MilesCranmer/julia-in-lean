# eltype(countfrom(true)) is Bool, but the iterator yields true, 2, 3, ...
# because state + step on two Bools is an Int. collect then throws InexactError.
c = Iterators.countfrom(true)
println("eltype = ", eltype(c))
y = iterate(c)
y = iterate(c, y[2])
println("second element = ", repr(y[1]), " :: ", typeof(y[1]))
r = try
    collect(Iterators.take(c, 3))
catch e
    e
end
println("collect(take(countfrom(true), 3)) = ", repr(r))
if eltype(c) === Bool && !(y[1] isa eltype(c))
    println("REPRODUCED iteratorscov-countfrom-eltype")
end
