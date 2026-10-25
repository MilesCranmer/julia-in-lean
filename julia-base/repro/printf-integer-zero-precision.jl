using Printf
failures = 0
for c in ["d", "i", "u", "o", "x", "X"]
    s = "%.0" * c
    actual = Printf.format(Printf.Format(s), UInt32(0))
    println(s, " zero = ", repr(actual), "; C99 expected ", repr(""))
    global failures += actual == "0"
end
failures == 6 && println("REPRODUCED printf-integer-zero-precision")
