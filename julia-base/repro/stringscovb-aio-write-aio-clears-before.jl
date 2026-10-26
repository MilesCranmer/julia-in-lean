using Base: AnnotatedString, AnnotatedIOBuffer, annotations
src = AnnotatedIOBuffer(); write(src, AnnotatedString("abcde", [(1:5, :s, 1)])); seekstart(src)
dst = AnnotatedIOBuffer(); write(dst, AnnotatedString("XYZW", [(1:1, :p, 1), (2:4, :d, 2)])); seek(dst, 1)
write(dst, src)                           # overwrite bytes 2:6 of dst
viabuffer = [(a.region, a.label) for a in annotations(dst)]
ref = AnnotatedIOBuffer(); write(ref, AnnotatedString("XYZW", [(1:1, :p, 1), (2:4, :d, 2)])); seek(ref, 1)
write(ref, AnnotatedString("abcde", [(1:5, :s, 1)]))
viastring = [(a.region, a.label) for a in annotations(ref)]
println("write(dst, src::AnnotatedIOBuffer) -> ", viabuffer)
println("write(dst, AnnotatedString)        -> ", viastring)
viabuffer == [(2:6, :s)] && viastring == [(1:1, :p), (2:6, :s)] &&
    println("REPRODUCED stringscovb-aio-write-aio-clears-before")
