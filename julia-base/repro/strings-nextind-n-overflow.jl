j = nextind("a", 1, typemax(Int))
println("nextind(\"a\", 1, typemax(Int)) = ", j)
j < 1 && println("REPRODUCED strings-nextind-n-overflow")
