# Base's own parser (Dates === nothing), used by code loading for Project.toml files.
P = Base.TOML.Parser{nothing}
r = try
    Base.TOML.tryparse(P("a = [1979-05-27, 1979-05-28]"))
catch e
    e
end
println(r isa Exception ? (typeof(r), sprint(showerror, r)) : r)
println(Base.TOML.tryparse(P("a = 1979-05-27")))
dir = mktempdir()
f = joinpath(dir, "Project.toml")
write(f, "name = \"Foo\"\nreleases = [2020-01-01, 2021-01-01]\n")
r2 = try
    Base.parsed_toml(f)
catch e
    e
end
println(r2 isa Exception ? (typeof(r2), sprint(showerror, r2)) : r2)
if r isa Exception && !(r isa Base.TOML.ParserError) && r2 isa Exception
    println("REPRODUCED toml-base-parser-date-array")
end
