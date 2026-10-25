import TOML
# Inline tables are immutable, but an array-of-tables header can add keys to them.
r1 = TOML.tryparse("a = {}\n[[a.b]]")
r2 = TOML.tryparse("a = [{}]\n[[a.b]]")
r3 = TOML.tryparse("a = {}\n[a.b]")   # the plain table header is rejected
println(r1)
println(r2)
println(typeof(r3))
if r1 isa Dict && r2 isa Dict && r3 isa TOML.ParserError
    println("REPRODUCED toml-array-table-in-inline-table")
end
