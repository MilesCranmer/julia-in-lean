using Base.BinaryPlatforms
p = parse(Platform, "x86_64-unknown-openbsd7.4")
println("parse(Platform, \"x86_64-unknown-openbsd7.4\") = ", repr(p))
println("os_version(p) = ", repr(os_version(p)))
t = triplet(p)
println("triplet(p) = ", repr(t))
q = parse(Platform, t)
println("parse(Platform, triplet(p)) = ", repr(q), "; == p: ", q == p)
f = parse(Platform, "x86_64-unknown-freebsd13.2")
println("FreeBSD for comparison: triplet = ", repr(triplet(f)))
if q != p && os_version(q) === nothing
    println("REPRODUCED platforms-openbsd-os-version")
end
