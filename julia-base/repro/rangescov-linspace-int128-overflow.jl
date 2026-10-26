a = Int128(2)^126
b = a + Int128(2)^80
r = range(a, b; length=4)
println("range(2^126, 2^126 + 2^80; length=4) = ", collect(r))
println("expected first ≈ ", Float64(a), " and last ≈ ", Float64(b))
(first(r) < 0 && Float64(a) > 0) && println("REPRODUCED rangescov-linspace-int128-overflow")
