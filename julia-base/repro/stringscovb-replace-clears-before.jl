using Base: AnnotatedString, AnnotatedIOBuffer, annotations
mk() = (io = AnnotatedIOBuffer(); write(io, AnnotatedString("XYZW", [(1:1, :p, 1), (2:4, :d, 2)])); seek(io, 1); io)
a = mk(); replace(a, AnnotatedString("ab", [(1:2, :s, 3)]), "a" => "c")
b = mk(); write(b, AnnotatedString("cb", [(1:2, :s, 3)]))
println("replace into position 1: ", [(x.region, x.label) for x in annotations(a)])
println("write into position 1:   ", [(x.region, x.label) for x in annotations(b)])
!any(x -> x.label == :p, annotations(a)) && any(x -> x.label == :p, annotations(b)) &&
    println("REPRODUCED stringscovb-replace-clears-before")
