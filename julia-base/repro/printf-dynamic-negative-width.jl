using Printf
for (fmt, value) in [("%*d", 42), ("%*s", "hi"), ("%*.1f", 1.5)]
    actual = Printf.format(Printf.Format(fmt), -5, value)
    local literal = Printf.format(Printf.Format(replace(fmt, "*" => "-5")), value)
    println(fmt, " width -5 = ", repr(actual), "; literal = ", repr(literal))
end
@sprintf("%*d", -5, 42) == "42" && println("REPRODUCED printf-dynamic-negative-width")
