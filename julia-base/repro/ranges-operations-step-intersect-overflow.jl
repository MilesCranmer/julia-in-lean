r = Int8(-100):Int8(2):Int8(120)
s = Int8(-100):Int8(3):Int8(120)
t = intersect(r, s)
u = Int8(-128):Int8(127):Int8(126)
@assert last(u) == 126 && last(intersect(u,u)) == -1
descending = Int8(120):Int8(-3):Int8(-128)
other = Int8(-100):Int8(7):Int8(120)
@assert first(intersect(descending,other)) == 104 && !(Int8(104) in descending)
if Int8(116) in r && Int8(116) in s && !(Int8(116) in t) && last(t) == 110
    println("REPRODUCED ranges-operations-step-intersect-overflow")
else
    error("step/step intersection overflow did not reproduce: $t")
end
