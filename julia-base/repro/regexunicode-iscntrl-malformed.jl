# iscntrl returns true for some malformed Chars (bare continuation bytes, truncated lead bytes).
cs = ['\x80', '\xbf', '\xc2', '\xc0', '\xe0', '\xff']
for c in cs
    println(repr(c), ": ismalformed=", Base.ismalformed(c), " iscntrl=", iscntrl(c), " isprint=", isprint(c),
            " category=", Base.Unicode.category_abbrev(c))
end
iscntrl('\x80') && Base.ismalformed('\x80') && !iscntrl('\xff') && println("REPRODUCED regexunicode-iscntrl-malformed")
