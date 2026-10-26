# insorted(x, r::AbstractRange) uses `in` (==) instead of the sort-order equivalence
# that the vector method and the docstring use.
a = insorted(-0.0, [0.0, 1.0])   # false: -0.0 is ordered before 0.0 by isless
b = insorted(-0.0, 0.0:1.0)      # true
c = insorted(missing, [1, 2, 3]) # false
d = insorted(missing, 1:3)       # missing, not a Bool
println(a, " ", b, " ", c, " ", d)
if a != b || !(d isa Bool)
    println("REPRODUCED sorttuplescov-insorted-range-equivalence")
end
