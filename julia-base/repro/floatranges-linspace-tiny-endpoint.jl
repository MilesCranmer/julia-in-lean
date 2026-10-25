# range(a, b; length=n) does not end at b when b is tiny but nonzero.
for b in (1.0e-14, 1.0e-20, 1.0e-300)
    r = range(1.0, b; length=24)
    println("last(range(1.0, $b; length=24)) = ", repr(last(r)), "   (stop = ", repr(b), ")")
end
r = range(1.0, 1.0e-300; length=24)
println("collect(r)[end] = ", repr(collect(r)[end]))
last(range(1.0, 1.0e-14; length=24)) != 1.0e-14 && last(r) != 1.0e-300 &&
    println("REPRODUCED floatranges-linspace-tiny-endpoint")
