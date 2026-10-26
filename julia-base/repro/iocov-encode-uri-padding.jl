enc = Base.Filesystem.encode_uri_component("a\tb")
println("encode_uri_component(\"a\\tb\") = ", repr(enc))
u = Base.Filesystem.uripath("/tmp/a\tb")
println("uripath(\"/tmp/a\\tb\") ends with ", repr(last(u, 6)))
if enc == "a%9b"
    println("REPRODUCED iocov-encode-uri-padding")
end
