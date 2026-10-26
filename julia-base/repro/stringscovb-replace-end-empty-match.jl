using Base: AnnotatedString, annotations
X = AnnotatedString("X", [(1:1, :z, 1)])
r1 = replace(AnnotatedString("ab"), r"$" => X)
r2 = replace(AnnotatedString("ab"), r"^" => X)
println("replace(\"ab\", r\"\$\" => X) = ", repr(r1.string), " ", [(a.region, a.label) for a in annotations(r1)])
println("replace(\"ab\", r\"^\" => X) = ", repr(r2.string), " ", [(a.region, a.label) for a in annotations(r2)])
isempty(annotations(r1)) && r1.string == "abX" && !isempty(annotations(r2)) &&
    println("REPRODUCED stringscovb-replace-end-empty-match")
