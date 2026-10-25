# Compact display rounds an exact tie to the even six-digit neighbour for small
# integers, but not above 2^54.
x = 1.234565e17
@assert BigInt(x) == 123456500000000000
small = sprint(show, 1234565.0; context=:compact => true)
s = sprint(show, x; context=:compact => true)
println("compact(1234565.0) = ", small, "    (tie rounded to even)")
println("compact(1.234565e17) = ", s, "    (expected 1.23456e17)")
small == "1.23456e6" && s == "1.23457e17" && println("REPRODUCED parseprint-ryu-compact-tie-even")
