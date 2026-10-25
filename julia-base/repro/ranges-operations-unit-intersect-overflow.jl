r = Int8(-100):Int8(100)
s = Int8(-120):Int8(7):Int8(125)
t = intersect(r, s)
if Int8(97) in r && Int8(97) in s && !(Int8(97) in t) && last(t) == 90
    println("REPRODUCED ranges-operations-unit-intersect-overflow")
else
    error("unit/step intersection overflow did not reproduce: $t")
end
