using Base: AnnotatedString, eachregion
e = AnnotatedString("")
sub = SubString(AnnotatedString("x"), 1, 0)
a = collect(eachregion(e))
b = collect(eachregion(sub))
println("length(eachregion(AnnotatedString(\"\"))) = ", length(a), ", first piece = ", repr(String(first(a)[1])))
println("length(eachregion(empty SubString of an AnnotatedString)) = ", length(b))
length(a) == 1 && isempty(b) && println("REPRODUCED stringutil-eachregion-empty")
