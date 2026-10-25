b = count(trues(128); init=Int8(0))
v = count(fill(true, 128); init=Int8(0))
g = count(identity, trues(128); init=Int8(0))
println(repr(b), " ", repr(v), " ", repr(g), " ", repr(count(trues(300); init=0x00)))
if b == -128 && v == 128
    println("REPRODUCED bitarrays-count-init-wrap")
end
