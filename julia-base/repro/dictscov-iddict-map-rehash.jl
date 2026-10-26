# map!(f, values(d::IdDict)) uses the generic fallback (base/abstractdict.jl:673-681),
# `for (key, val) in pairs(dict); dict[key] = f(val); end`. setindex!(::IdDict)
# rehashes when d.ndel >= 3*length(d.ht)>>2 (base/iddict.jl:84-87), even when the
# key is already present. Rehashing in the middle of the iteration moves the
# remaining pairs, so some values are skipped (or visited twice).
# mergewith!(combine, d, d) (base/abstractdict.jl:288-293) fails the same way.

# three Int keys whose objectid falls in slot 0 of the initial 16-slot table
ks = Int[]
for k in 1:100_000
    objectid(k) & 15 == 0 && push!(ks, k)
    length(ks) == 3 && break
end
f, x, y = ks

function build()
    d = IdDict{Int,Int}()
    d[f] = 0; d[x] = 1; d[y] = 2   # f in slot 0, x in slot 1, y in slot 2
    delete!(d, f)                  # tombstone in slot 0; ndel = 1
    for j in 1:23                  # 23 more deletions without a rehash: ndel = 24
        junk = -j
        d[junk] = 0
        delete!(d, junk)
    end
    return d
end

d = build()
println("keys f, x, y = ", (f, x, y), "; ndel = ", d.ndel, ", length(d.ht) = ", length(d.ht))
println("before map!: ", collect(d))
map!(v -> v + 10, values(d))
println("after  map!(v -> v + 10, values(d)): ", collect(d), "  (expected x => 11, y => 12)")
ok_map = d[x] == 11 && d[y] == 12

d2 = build()
mergewith!(+, d2, d2)
println("after  mergewith!(+, d2, d2): ", collect(d2), "  (expected x => 2, y => 4)")
ok_merge = d2[x] == 2 && d2[y] == 4

if !ok_map && !ok_merge
    println("REPRODUCED dictscov-iddict-map-rehash")
end
