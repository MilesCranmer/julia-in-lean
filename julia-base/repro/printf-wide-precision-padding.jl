using Printf
right = @sprintf("%5.1s", "你")
left = @sprintf("%-5.1s", "你")
println("%5.1s wide character = ", repr(right), "; textwidth = ", textwidth(right), "; width = 5")
println("%-5.1s wide character = ", repr(left), "; textwidth = ", textwidth(left), "; width = 5")
textwidth(right) == 4 && textwidth(left) == 4 && println("REPRODUCED printf-wide-precision-padding")
