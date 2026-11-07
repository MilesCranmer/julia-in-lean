id = "bignums-gmp-comparison-ieee"
ok = try
    x = BigInt(0)
    y = -0.0
    cmp(x, y) == 0 && isless(y, x) && !isless(x, y)
catch
    false
end
println((ok ? "REPRODUCED " : "NOT_REPRODUCED ") * id)
