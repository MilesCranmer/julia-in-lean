import TOML
# Whitespace between a line-ending backslash and the newline must be allowed.
s = "a = \"\"\"x \\  \n  y\"\"\""
println(repr(s))
r = TOML.tryparse(s)
println(r isa TOML.ParserError ? "ParserError: " * string(r.type) : r)
println(TOML.tryparse("a = \"\"\"x \\\n  y\"\"\""))
if r isa TOML.ParserError
    println("REPRODUCED toml-continuation-trailing-space")
end
