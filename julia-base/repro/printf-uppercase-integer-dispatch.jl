using Printf
failures = 0
for s in ["%D", "%O", "%U"]
    f = Printf.Format(s)
    println("Format(", repr(s), ") accepted; arguments = ", f.numarguments)
    e = try Printf.format(f, 1); nothing catch e; e end
    println("format => ", typeof(e))
    global failures += e isa MethodError
end
failures == 3 && println("REPRODUCED printf-uppercase-integer-dispatch")
