import TOML
# Malformed prefixed integers: a digit outside the base, or a prefix with no digits.
for s in ("a = 0o8", "a = 0b2", "a = 0x-1", "a = 0b:00")
    r = try
        TOML.tryparse(s)
    catch e
        e
    end
    println(repr(s), " => ", r isa Exception ? sprint(showerror, r) : typeof(r))
end
r = try TOML.tryparse("a = 0o8") catch e e end
if r isa ArgumentError
    println("REPRODUCED toml-tryparse-argumenterror")
end
