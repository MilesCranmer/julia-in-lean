using Base: AnnotatedString, annotations
# :A applies to the character 'a' only
s = AnnotatedString("aé", [(1:1, :A, 1)])
r = reverse(s)
println("String(reverse(s)) = ", repr(String(r)))
println("regions = ", [a.region for a in annotations(r)])
println("labels of 'é' at index 1 = ", [a.label for a in annotations(r, 1)])
println("labels of 'a' at index 3 = ", [a.label for a in annotations(r, 3)])
# :B covers the whole string "b🍕" (code units 1:5)
t = AnnotatedString("b🍕", [(1:5, :B, 2)])
u = reverse(t)
println("String(reverse(t)) = ", repr(String(u)), ", ncodeunits = ", ncodeunits(u))
println("regions = ", [a.region for a in annotations(u)])
if isempty(annotations(r, 3)) && first(annotations(u)[1].region) < 1
    println("REPRODUCED stringutil-annotated-reverse")
end
