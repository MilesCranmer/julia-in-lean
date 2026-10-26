nt = (a = 1,)
caught(f) = try f() catch e; typeof(e) end
z1 = caught(() -> merge(nt, zip([:b, :b], [2, 3])))
c1 = merge(nt, collect(zip([:b, :b], [2, 3])))
z2 = caught(() -> merge(nt, zip([:b, :c], [2])))
c2 = merge(nt, collect(zip([:b, :c], [2])))
println(z1, " ", c1)
println(z2, " ", c2)
if z1 != c1 && z2 != c2
    println("REPRODUCED sorttuplescov-merge-zip")
end
