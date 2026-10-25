import TOML
# TOML v1.1 offset date-times; the TOML stdlib documents itself as a TOML v1.1 parser.
for s in ("odt = 1979-05-27T00:32:00-07:00", "odt = 1979-05-27T07:32:00+00:00", "odt = 1979-05-27T07:32:00Z")
    r = TOML.tryparse(s)
    println(repr(s), " => ", r isa TOML.ParserError ? "ParserError: " * string(r.type) : r)
end
r = TOML.tryparse("odt = 1979-05-27T00:32:00-07:00")
if r isa TOML.ParserError
    println("REPRODUCED toml-offset-datetime-rejected")
end
