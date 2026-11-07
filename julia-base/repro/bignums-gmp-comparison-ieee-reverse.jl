id = "bignums-gmp-comparison-ieee-reverse"
ok = try
    x = BigInt(0)
    y = -0.0
    cmp(y, x) == 0 && isless(y, x) && !isless(x, y)
catch
    false
end
println((ok ? "REPRODUCED " : "NOT_REPRODUCED ") * id)
