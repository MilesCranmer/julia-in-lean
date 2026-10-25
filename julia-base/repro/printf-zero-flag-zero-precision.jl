using Printf
literal = @sprintf("%05.0d", Int32(3))
dynamic = @sprintf("%05.*d", 0, Int32(3))
println("%05.0d three = ", repr(literal), "; C99 expected ", repr("    3"))
println("%05.*d precision 0 = ", repr(dynamic), "; C99 expected ", repr("    3"))
literal == "00003" && dynamic == "00003" && println("REPRODUCED printf-zero-flag-zero-precision")
