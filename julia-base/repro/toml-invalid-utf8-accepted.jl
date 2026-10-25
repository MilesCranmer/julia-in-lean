import TOML
# A TOML document must be valid UTF-8.
for s in ("a = \"\xff\"", "# \xc3\na = 1")
    println(repr(s), " => ", TOML.tryparse(s))
end
r = TOML.tryparse("a = \"\xff\"")
if r isa Dict && !isvalid(r["a"])
    println("REPRODUCED toml-invalid-utf8-accepted")
end
