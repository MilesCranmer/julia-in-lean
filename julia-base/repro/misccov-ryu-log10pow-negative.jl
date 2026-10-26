# Docstrings of Base.Ryu.log10pow2/log10pow5 (base/ryu/utils.jl:22-35): "Compute
# floor(log10(2^e)). This is valid for all e < 1651." and "... floor(log10(5^e)) ...
# valid for all e < 2621". Both are wrong for some negative e.
e2 = -1651; r2 = Base.Ryu.log10pow2(e2)
e5 = -2621; r5 = Base.Ryu.log10pow5(e5)
# floor(log10(b^e)) == r  iff  10^r <= b^e < 10^(r+1); for negative e and r compare
# b^(-e) against 10^(-r) exactly with BigInt.
ok2 = big(2)^(-e2) <= big(10)^(-r2) && big(10)^(-(r2 + 1)) < big(2)^(-e2)
ok5 = big(5)^(-e5) <= big(10)^(-r5) && big(10)^(-(r5 + 1)) < big(5)^(-e5)
println("log10pow2($e2) = $r2, floor(log10(2^$e2)) == $r2: ", ok2)
println("log10pow5($e5) = $r5, floor(log10(5^$e5)) == $r5: ", ok5)
println("floor(log10(big(2)^$e2)) = ", floor(BigInt, log10(big(2.0)^e2)))
if !ok2 && !ok5
    println("REPRODUCED misccov-ryu-log10pow-negative")
end
