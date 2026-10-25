# The decimal correction of a:s:b silently switches off once an endpoint exceeds 2^24.
for b in (1.6777216e7, 1.6777217e7, 2.0e7)
    r = 0.0:0.1:b
    println("(0.0:0.1:$b)[4] = ", repr(r[4]), "   length = ", length(r))
end
(0.0:0.1:1.6777216e7)[4] === 0.3 && (0.0:0.1:1.6777217e7)[4] !== 0.3 &&
    println("REPRODUCED floatranges-colon-decimal-threshold")
