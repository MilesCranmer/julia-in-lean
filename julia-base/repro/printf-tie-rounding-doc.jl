using Printf
zero = @sprintf("%.0f", 0.5)
two = @sprintf("%.0f", 2.5)
neg = @sprintf("%f", -0.0078125)
println("%.0f 0.5 = ", repr(zero), "; documented away-from-zero would be ", repr("1"))
println("%.0f 2.5 = ", repr(two), "; documented away-from-zero would be ", repr("3"))
println("%f -0.0078125 = ", repr(neg), "; documented away-from-zero would be ", repr("-0.007813"))
zero == "0" && two == "2" && neg == "-0.007812" && println("REPRODUCED printf-tie-rounding-doc")
