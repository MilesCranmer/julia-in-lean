import TOML
# Underscores before the exponent are dropped from the check once an exponent is read.
for s in ("a = 6.022_140_76e23", "a = 1_000e3", "a = 1_000.5", "a = 1e1_0", "a = 1_0.5e1_0")
    r = TOML.tryparse(s)
    println(repr(s), " => ", r isa TOML.ParserError ? "ParserError: " * string(r.type) : r)
end
r = TOML.tryparse("a = 6.022_140_76e23")
if r isa TOML.ParserError
    println("REPRODUCED toml-float-underscore-exponent")
end
