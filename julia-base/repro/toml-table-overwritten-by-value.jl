import TOML
# [a.b.c] creates a.b; a later `b = 1` under [a] replaces that table silently.
s = """
[a.b.c]
x = 1

[a]
b = 2
"""
r = TOML.tryparse(s)
println(r)
t = TOML.tryparse("[a.b]\nx = 1\n[a]\nb = 2")   # same conflict one level up is rejected
println(typeof(t))
if r isa Dict && r["a"]["b"] == 2
    println("REPRODUCED toml-table-overwritten-by-value")
end
