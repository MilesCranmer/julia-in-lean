err(f) = try
    f()
catch e
    e
end
a = prod(())
b = err(() -> prod(identity, ()))
c = err(() -> sum(()))
println(a, " ", typeof(b), " ", typeof(c))
if a == 1 && b isa ArgumentError
    println("REPRODUCED tuples-prod-empty")
end
