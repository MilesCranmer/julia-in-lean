using Base: AnnotatedString, annotations
X = AnnotatedString("X", [(1:1, :z, 1)])
r = replace(AnnotatedString("abc"), r"b*" => X)
println("replace(\"abc\", r\"b*\" => X) = ", repr(r.string), " ", [(a.region, a.label) for a in annotations(r)])
println("plain replace = ", repr(replace("abc", r"b*" => "X")))
# the 'c' at code unit 4 is not part of any replacement
any(a -> 4 in a.region, annotations(r)) && println("REPRODUCED stringscovb-replace-skipped-empty-annotation")
