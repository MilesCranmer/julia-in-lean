# print(::Base.VersionRange) with a "*" lower bound pads the upper bound to three
# components, so reparsing the printed range gives a smaller range
# (Base.VersionRange on master; on 1.13 the same code lives in the Pkg stdlib as Pkg.Versions)
const VR = isdefined(Base, :VersionRange) ? Base.VersionRange : (import Pkg; Pkg.Versions.VersionRange)
println("using ", parentmodule(VR), ".VersionRange")
r = VR("*-2")
s = string(r)
r2 = VR(s)
println("VersionRange(\"*-2\") prints as ", repr(s), "; shown as ", repr(r))
println("v\"2.5.0\" in VersionRange(\"*-2\") = ", v"2.5.0" in r)
println("v\"2.5.0\" in VersionRange(string(VersionRange(\"*-2\"))) = ", v"2.5.0" in r2)
if s == "0 -2.0.0" && (v"2.5.0" in r) && !(v"2.5.0" in r2)
    println("REPRODUCED versionnumbers-range-print-upper")
end
