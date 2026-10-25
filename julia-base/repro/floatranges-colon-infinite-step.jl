# a:s:b with an infinite step has one element, and that element is NaN instead of a.
r = 0.0:Inf:1.0
println("length(0.0:Inf:1.0) = ", length(r))
println("first(0.0:Inf:1.0) = ", first(r))
println("collect(0.0:Inf:1.0) = ", collect(r))
length(r) == 1 && isnan(first(r)) && println("REPRODUCED floatranges-colon-infinite-step")
