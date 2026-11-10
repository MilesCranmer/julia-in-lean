# `x ⊑ₑ y` (Compiler/src/ssair/EscapeAnalysis.jl:246-300) compares an IndexableFields AliasInfo
# with an Unindexable one by `for i = length(xinfos)` (line 278), which visits only the last
# field. So `⊑ₑ` is not transitive, it disagrees with `⊔ₑ` (x ⊑ₑ y but x ⊔ₑ y != y), and for an
# object with no fields it throws a BoundsError, so `x ⊑ₑ x ⊔ₑ y` fails.
const EA = Base.Compiler.EscapeAnalysis
id = "compiler-escape-sqsub-transitive"
use(i) = (s = EA.AInfo(); push!(s, EA.LocalUse(i)); s)
info(a) = EA.EscapeInfo(EA.NoEscape(), a)
x = info(EA.IndexableFields([use(2)]))
y = info(EA.IndexableFields([use(2), EA.AInfo()]))
z = info(EA.Unindexable(EA.AInfo()))
xy, yz, xz = EA.:⊑ₑ(x, y), EA.:⊑ₑ(y, z), EA.:⊑ₑ(x, z)
println("transitivity: x ⊑ₑ y = ", xy, ", y ⊑ₑ z = ", yz, ", x ⊑ₑ z = ", xz)
w = info(EA.IndexableFields([use(2), EA.AInfo()]))
wz = EA.:⊑ₑ(w, z); j = EA.:⊔ₑ(w, z)
println("join agreement: w ⊑ₑ z = ", wz, ", (w ⊔ₑ z) == z = ", j == z, ", (w ⊔ₑ z) ⊑ₑ z = ", EA.:⊑ₑ(j, z))
e = info(EA.IndexableFields(EA.AInfo[]))
ub = try
    EA.:⊑ₑ(e, EA.:⊔ₑ(e, z))
catch err
    sprint(showerror, err)
end
println("upper bound: e ⊑ₑ (e ⊔ₑ z) = ", ub)
ok = xy && yz && !xz && wz && !(j == z) && ub isa String && occursin("BoundsError", ub)
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
