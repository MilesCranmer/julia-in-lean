w = [4, 5, 2, 1, 1, 4, 4, 4, 2, 4, 5, 5, 3, 3, 2, 2, 4, 5, 2, 2, 5, 5]
got = partialsort(w, 5:-1:3)
want = sort(w)[5:-1:3]
println(got, "  expected: ", want)
if got != want
    println("REPRODUCED sort-partialsort-reversed-range")
end
