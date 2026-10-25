import TOML
# TOML 1.1: \xHH is the code point U+00HH.
r = TOML.tryparse("a = \"\\xE9\"")
v = r["a"]
println(repr(v), " isvalid=", isvalid(v), " codeunits=", collect(codeunits(v)))
if v != "\u00e9" && !isvalid(v)
    println("REPRODUCED toml-hex-escape-byte")
end
