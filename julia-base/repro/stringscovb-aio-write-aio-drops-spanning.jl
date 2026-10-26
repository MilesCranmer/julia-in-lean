using Base: AnnotatedString, AnnotatedIOBuffer, annotations
src = AnnotatedIOBuffer(); write(src, AnnotatedString("abcde", [(1:5, :s, 1)])); seek(src, 2)
dst = AnnotatedIOBuffer(); write(dst, AnnotatedString("XY", [(1:2, :d, 2)]))
nb = write(dst, src)                      # copies "cde", which carries :s
println("bytes written = ", nb, ", dst = ", repr(String(take!(copy(dst.io)))))
println("annotations(dst) = ", [(a.region, a.label) for a in annotations(dst)])
[(a.region, a.label) for a in annotations(dst)] == [(1:2, :d)] &&
    println("REPRODUCED stringscovb-aio-write-aio-drops-spanning")
