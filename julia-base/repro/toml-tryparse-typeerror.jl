import TOML
# A key that holds a value, used as a parent of an array-of-tables header.
for s in ("a = 1\n[[a.b]]", "a = \"x\"\n[[a.b.c]]", "a = [[1]]\n[[a.b]]")
    r = try
        TOML.tryparse(s)
    catch e
        e
    end
    println(repr(s), " => ", typeof(r))
end
r = try TOML.tryparse("a = 1\n[[a.b]]") catch e e end
if r isa TypeError
    println("REPRODUCED toml-tryparse-typeerror")
end
