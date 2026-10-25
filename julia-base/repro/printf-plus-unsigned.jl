using Printf
for fmt in ["%+u", "%+o", "%+x", "%+X", "% x"]
    println(rpad(fmt, 4), " 42 = ", repr(Printf.format(Printf.Format(fmt), 42)),
            "; C99 expected ", repr(Printf.format(Printf.Format(replace(fmt, "+" => "", " " => "")), 42)))
end
@sprintf("%+x", 42) == "+2a" && @sprintf("% x", 42) == " 2a" && println("REPRODUCED printf-plus-unsigned")
