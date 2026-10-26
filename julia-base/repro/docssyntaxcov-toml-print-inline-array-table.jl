# TOML.print writes invalid TOML when a table inside an array of tables is in
# `inline_tables`: it prints the `[[a]]` header followed by a bare inline table.
using TOML
inner = Dict("c" => 1)
d = Dict("a" => [inner])
s = sprint(io -> TOML.print(io, d; inline_tables = Base.IdSet{Dict{String}}([inner])))
println(repr(s))
r = TOML.tryparse(s)
println(r isa TOML.ParserError ? "reparse fails: " * sprint(showerror, r) : "reparse ok: $(repr(r))")
if r isa TOML.ParserError
    println("REPRODUCED docssyntaxcov-toml-print-inline-array-table")
end
