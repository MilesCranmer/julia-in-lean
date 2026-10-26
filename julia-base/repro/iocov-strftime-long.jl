fmt = "%Y-" * "x"^130
s = Libc.strftime(fmt, 0.0)
println("length(strftime(fmt, 0.0)) = ", length(s), "  (", repr(first(s, 10)), ")")
println("short format: ", repr(Libc.strftime("%Y-xx", 0.0)))
if isempty(s)
    println("REPRODUCED iocov-strftime-long")
end
