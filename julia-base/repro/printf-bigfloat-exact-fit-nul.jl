using Printf
for (fmt, x) in [("%320f", big"2.0"), ("%f", big"1e313"), ("%400e", big"1.0")]
    s = Printf.format(Printf.Format(fmt), x)
    println(rpad(fmt, 6), " ", repr(x), ": length = ", ncodeunits(s), ", last byte = ", repr(s[end]))
end
s = @sprintf("%320f", big"2.0")
endswith(s, '\0') && println("REPRODUCED printf-bigfloat-exact-fit-nul")
