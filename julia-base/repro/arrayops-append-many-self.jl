a = [1, 2, 3]
append!(a, a, a)
println(a)
b = [1, 2, 3]
prepend!(b, b, b)
println(b)
println(push!([1, 2, 3], [1, 2, 3]..., [1, 2, 3]...))
if length(a) == 12 && length(b) == 12
    println("REPRODUCED arrayops-append-many-self")
end
