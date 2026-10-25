a = [10, 20, 30, 40]
err = try
    deleteat!(a, [1, 3, 5])
    nothing
catch e
    e
end
println(repr(err))
println(a)
b = [10, 20, 30, 40]
try keepat!(b, [2, 4, 3]) catch end
println(b)
if err isa BoundsError && a == [20, 20, 30, 40]
    println("REPRODUCED arrayops-deleteat-error-partial")
end
