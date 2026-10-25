using Unicode
# isequal_normalized with stripmark=true when a combining mark decomposes to nothing.
nf(s) = Unicode.normalize(s; decompose = true, stripmark = true)
pairs = [("no\u00EBl", "noel"),        # docstring example (precomposed ë)
         ("noe\u0308l", "noel"),       # the docstring's canonically equivalent s2
         ("cafe\u0301", "cafe"), ("cafe\u0301", "cafee"), ("a\u0301", "aa"), ("\u0301", "")]
bad = 0
for (a, b) in pairs
    got = isequal_normalized(a, b; stripmark = true)
    want = nf(a) == nf(b)
    println("isequal_normalized(", repr(a), ", ", repr(b), "; stripmark=true) = ", got,
            "   normalize: ", repr(nf(a)), " vs ", repr(nf(b)), " => ", want)
    global bad += got != want
end
# The same call with bounds checking forced on exposes the out-of-bounds read d[0].
code = """using Unicode; try isequal_normalized("a\\u0301", "a"; stripmark=true); println("no error") catch e; println(sprint(showerror, e)) end"""
out = readchomp(`$(Base.julia_cmd()) --startup-file=no --check-bounds=yes -e $code`)
println("with --check-bounds=yes: ", first(out, 90))
bad > 0 && println("REPRODUCED regexunicode-isequal-normalized-stripmark")
