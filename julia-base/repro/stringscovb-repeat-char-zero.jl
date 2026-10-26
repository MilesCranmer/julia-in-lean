using Base: AnnotatedString, AnnotatedChar, annotations
c = AnnotatedChar('a', [(:l, 1)])
s = AnnotatedString("a", [(1:1, :l, 1)])
rc, rs = repeat(c, 0), repeat(s, 0)
println("repeat(AnnotatedChar, 0) == \"\": ", rc == "", ", annotations ", [(a.region, a.label) for a in annotations(rc)])
println("repeat(AnnotatedString, 0) == \"\": ", rs == "", ", annotations ", annotations(rs))
println("rc == rs: ", rc == rs)
!(rc == "") && rs == "" && println("REPRODUCED stringscovb-repeat-char-zero")
