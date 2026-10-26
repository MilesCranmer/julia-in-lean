using Base: AnnotatedString, annotate!, annotations
s = AnnotatedString("abc", [(1:2, :face, :red)])
annotate!(s, 1:3, :face, nothing)          # documented to remove existing :face annotations
println("after annotate!(s, 1:3, :face, nothing): ", [(a.region, a.label, a.value) for a in annotations(s)])
t = AnnotatedString("abc", [(1:2, :face, :red)])
annotate!(t, :face, nothing)
println("after annotate!(t, :face, nothing): ", [(a.region, a.label, a.value) for a in annotations(t)])
!isempty(annotations(s)) && !isempty(annotations(t)) && println("REPRODUCED stringscovb-annotate-nothing-partial")
