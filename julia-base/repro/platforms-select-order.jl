using Base.BinaryPlatforms
# Artifacts whose platforms differ only in the libgfortran minor version, which `triplet`
# does not print; every one of them matches the host equally well.
host = Platform("x86_64", "linux")
key(m) = Platform("x86_64", "linux"; libgfortran_version = "5.$m.0", validate_strict = true)
function build(pairs)
    d = Dict{Platform,String}()
    for (k, v) in pairs
        d[k] = v
    end
    return d
end
found = false
for a in 0:40, b in a+1:40
    ka, kb = key(a), key(b)
    d1 = build([ka => "5.$a", kb => "5.$b"])
    d2 = build([kb => "5.$b", ka => "5.$a"])
    s1, s2 = select_platform(d1, host), select_platform(d2, host)
    if d1 == d2 && s1 != s2
        println("triplet(ka) = ", triplet(ka), ", triplet(kb) = ", triplet(kb))
        println("d1 = ", d1, "\nd2 = ", d2, "\nd1 == d2: ", d1 == d2)
        println("select_platform(d1, host) = ", repr(s1), ", select_platform(d2, host) = ", repr(s2))
        println("REPRODUCED platforms-select-order")
        global found = true
        break
    end
end
found || println("no order dependence found")
