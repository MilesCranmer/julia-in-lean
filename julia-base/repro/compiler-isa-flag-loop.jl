struct C end
# `w` records whether the previous element was a C; the result should be true when a C is
# followed by a String.
function f(a, b)
    w = false
    r = false
    for el in (a, b)
        r = w && el isa String
        w = el isa C
    end
    r
end
println("f(C(), \"y\") = ", f(C(), "y"), "   (expected true)")
println("Base.return_types(f, (C, String)) = ", Base.return_types(f, (C, String)))
f(C(), "y") || println("REPRODUCED compiler-isa-flag-loop")
