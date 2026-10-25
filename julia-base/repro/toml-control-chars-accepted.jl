import TOML
# Control characters (other than tab) are forbidden in strings and comments; bare CR is not a newline.
cases = ("a = \"x\x01y\"", "a = 'x\x7fy'", "# \x00\na = 1", "a = 1\rb = 2", "a = \"\"\"x\ry\"\"\"")
results = [TOML.tryparse(s) for s in cases]
for (s, r) in zip(cases, results)
    println(repr(s), " => ", r)
end
if all(r -> r isa Dict, results)
    println("REPRODUCED toml-control-chars-accepted")
end
