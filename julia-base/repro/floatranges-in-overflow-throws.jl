# x in r throws InexactError when x - first(r) overflows.
r = range(-1.0e308, 1.0e308; length=3)
println("collect(r) = ", collect(r))
for x in (0.0, 1.0e308)
    try
        println("$x in r = ", x in r)
    catch e
        println("$x in r throws ", sprint(showerror, e))
        e isa InexactError && x == 1.0e308 && println("REPRODUCED floatranges-in-overflow-throws")
    end
end
