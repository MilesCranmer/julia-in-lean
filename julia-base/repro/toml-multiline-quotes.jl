import TOML
# One or two quotes may sit right before the closing delimiter of a multi-line string.
for s in ("a = \"\"\"\"q\"\"\"\"", "a = \"\"\"q\"\"\"\"\"", "a = '''x''''")
    r = TOML.tryparse(s)
    println(repr(s), " => ", r isa TOML.ParserError ? "ParserError: " * string(r.type) : r)
end
r = TOML.tryparse("a = \"\"\"\"q\"\"\"\"")
if r isa TOML.ParserError
    println("REPRODUCED toml-multiline-quotes")
end
