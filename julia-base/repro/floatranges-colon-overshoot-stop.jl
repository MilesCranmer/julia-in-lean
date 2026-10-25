# a:s:b with s > 0 can contain an element larger than b when the length exceeds 2^53.
r = 0.1131:0.0252:1.0e15
println("length = ", length(r))
println("last(r) = ", repr(last(r)), "  stop = ", repr(1.0e15))
println("r[end] > 1.0e15: ", r[end] > 1.0e15)
last(r) > 1.0e15 && println("REPRODUCED floatranges-colon-overshoot-stop")
