using Printf
function reproduce_negative_precision()
    for (fmt, args) in [("%.*s", (-2, "hello")), ("%.*f", (-1, 0.5)), ("%.*e", (-1, 0.5)), ("%.*g", (-1, 0.5))]
        r = try repr(Printf.format(Printf.Format(fmt), args...)) catch e typeof(e) end
        literal = Printf.format(Printf.Format(replace(fmt, ".*" => "")), args[2])
        println(fmt, " with precision ", args[1], " => ", r, "; C99 expected ", repr(literal))
    end
    e = try @sprintf("%.*s", -2, "hello"); nothing catch e; e end
    e isa BoundsError && println("REPRODUCED printf-dynamic-negative-precision")
end
reproduce_negative_precision()
