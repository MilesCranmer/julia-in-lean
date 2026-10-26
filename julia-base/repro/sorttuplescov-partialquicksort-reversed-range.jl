x = [1, 3, 4, 5, 3, 5, 5, 2, 1, 4, 5, 1, 4, 3, 5, 5, 5, 4, 3, 5, 5, 2]
k = 5:-1:3
got = sort(x; alg=PartialQuickSort(k))[k]
want = sort(x)[k]
println(got, "  expected: ", want)
if got != want
    println("REPRODUCED sorttuplescov-partialquicksort-reversed-range")
end
