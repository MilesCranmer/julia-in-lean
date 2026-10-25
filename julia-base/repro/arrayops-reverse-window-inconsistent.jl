println(reverse!([1, 2, 3], 5, 5))
err = try
    reverse([1, 2, 3], 5, 5)
    nothing
catch e
    e
end
println(repr(err))
println(repr(try reverse(Int[], 5, 5); nothing catch e; e end), " vs ", reverse!(Int[], 5, 5))
if err isa BoundsError
    println("REPRODUCED arrayops-reverse-window-inconsistent")
end
