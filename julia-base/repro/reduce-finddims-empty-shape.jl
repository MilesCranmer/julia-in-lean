A = zeros(0, 0)
s = size(sum(A; dims=1))
v, i = findmax(A; dims=1)
println(s, " ", size(v), " ", size(i))
if s == (1, 0) && size(v) == (0, 0)
    println("REPRODUCED reduce-finddims-empty-shape")
end
