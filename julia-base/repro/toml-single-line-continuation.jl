import TOML
# A line-ending backslash is only allowed in multi-line basic strings.
s = "a = \"x\\\ny\""
println(repr(s))
r = TOML.tryparse(s)
println(r)
if r isa Dict && r["a"] == "xy"
    println("REPRODUCED toml-single-line-continuation")
end
