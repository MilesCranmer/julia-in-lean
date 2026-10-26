using Base: AnnotatedString, annotated_chartransform, annotations
s = AnnotatedString("ab", [(2:2, :l, 1)])          # :l covers 'b'
r = annotated_chartransform(c -> c == 'b' ? 'é' : c, s)
println(repr(r.string), " ", [(a.region, a.label) for a in annotations(r)])
println("bytes of 'é' in the result: 2:3")
first(annotations(r)).region == 3:3 && println("REPRODUCED stringscovb-chartransform-ascii-grow")
