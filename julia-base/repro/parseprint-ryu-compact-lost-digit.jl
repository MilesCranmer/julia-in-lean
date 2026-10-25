# Compact display (as in arrays and the REPL's :compact context) should round a
# Float64 to six significant digits.
x = 1.7562091489257724e16
s = sprint(show, x; context=:compact => true)
println("compact = ", s, "    (expected 1.75621e16)")
println("matrix display: ", repr("text/plain", [x 1.0]))
err = abs(big(parse(Float64, s)) - big(x))
println("error = ", err, "    half a unit in the sixth digit = 5.0e10")
err > big(5) * big(10)^10 && println("REPRODUCED parseprint-ryu-compact-lost-digit")
