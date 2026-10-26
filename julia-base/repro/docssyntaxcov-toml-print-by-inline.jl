# TOML.print(...; sorted=true, by=f) orders the keys of ordinary tables by `f`, but
# the keys of inline tables (printed by print_inline_table) with plain `sort!`.
using TOML
by = k -> -Int(k[1])               # reverse alphabetical
t = Dict("a" => 1, "b" => 2)
plain = sprint(io -> TOML.print(io, t; sorted = true, by))
inline = sprint(io -> TOML.print(io, Dict("x" => t); sorted = true, by,
                                 inline_tables = Base.IdSet{Dict{String}}([t])))
println(repr(plain))
println(repr(inline))
if startswith(plain, "b") && occursin("{a = 1, b = 2}", inline)
    println("REPRODUCED docssyntaxcov-toml-print-by-inline")
end
