using Base: AnnotatedString, AnnotatedIOBuffer, annotations
io = AnnotatedIOBuffer(); write(io, AnnotatedString("abcde", [(1:5, :s, 1)])); seek(io, 2)
nb = write(io, AnnotatedString(""))
seekstart(io)
r = read(io, AnnotatedString)
println("bytes written = ", nb, ", annotations = ", [(a.region, a.label) for a in annotations(r)])
println("r == AnnotatedString(\"abcde\", [(1:5, :s, 1)]): ", r == AnnotatedString("abcde", [(1:5, :s, 1)]))
r != AnnotatedString("abcde", [(1:5, :s, 1)]) && length(annotations(r)) == 2 &&
    println("REPRODUCED stringscovb-aio-empty-write-splits")
