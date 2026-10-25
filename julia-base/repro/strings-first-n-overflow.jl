s = "é"
r = first(s, typemax(Int))
println("first(\"é\", typemax(Int)) = ", repr(r))
println("first(\"é\", 1) = ", repr(first(s, 1)))
r == "" && first(s, 1) == "é" && println("REPRODUCED strings-first-n-overflow")
