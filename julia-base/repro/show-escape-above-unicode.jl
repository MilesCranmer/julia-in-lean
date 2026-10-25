s = "\xf4\x90\x80\x80"   # one Char whose decoded code point is 0x110000
e = escape_string(s)
println("escape_string(s) = ", repr(e))
r = try unescape_string(e) catch err; err end
println("unescape_string(escape_string(s)) = ", repr(r))
p = try Meta.parse(repr(s)) catch err; err end
println("Meta.parse(repr(s)) = ", p isa Exception ? typeof(p) : repr(p))
!(r isa String && r == s) && println("REPRODUCED show-escape-above-unicode")
