import TOML
# Parser startup has code to skip a leading byte order mark, but it never runs.
r = TOML.tryparse("\ufeffa = 1")
println(r isa TOML.ParserError ? "ParserError: " * string(r.type) : r)
println(TOML.tryparse("a = 1"))
if r isa TOML.ParserError
    println("REPRODUCED toml-bom-not-skipped")
end
