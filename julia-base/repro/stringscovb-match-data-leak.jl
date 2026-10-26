# match/occursin allocate PCRE match data and do not free it when pcre2_match
# (or the offset conversion) throws; the C memory is never reclaimed.
r = r"(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)"
function growth(f, n)
    for _ in 1:1000; try f() catch end; end
    GC.gc()
    before = Sys.maxrss()
    for _ in 1:n; try f() catch end; end
    GC.gc()
    return (Sys.maxrss() - before) / 2^20
end
ok = growth(() -> match(r, "abcdefghij", 2), 1_000_000)
bad = growth(() -> match(r, "abcdefghij", 0), 1_000_000)
println("max RSS growth over 10^6 calls: match(r, s, 2) = ", round(ok; digits=1),
        " MiB, match(r, s, 0) (throws InexactError) = ", round(bad; digits=1), " MiB")
bad > 150 && ok < 50 && println("REPRODUCED stringscovb-match-data-leak")
