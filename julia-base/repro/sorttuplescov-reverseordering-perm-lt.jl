using Base.Order: Perm, Forward, ReverseOrdering, lt
p = Perm(Forward, [0, 0])
a = lt(ReverseOrdering(p), 1, 2)
b = lt(p, 2, 1)
println(a, " ", b)
if a != b
    println("REPRODUCED sorttuplescov-reverseordering-perm-lt")
end
