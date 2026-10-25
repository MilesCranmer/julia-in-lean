import TOML
# A sign before a date or time counts toward the 4-digit year / 2-digit hour width.
for s in ("a = -200-01-01", "a = +999-01-01", "a = +1:30:00", "a = -0:30:00", "a = +2000-01-01")
    println(repr(s), " => ", TOML.tryparse(s))
end
r1 = TOML.tryparse("a = -200-01-01")
r2 = TOML.tryparse("a = +1:30:00")
if r1 isa Dict && r2 isa Dict
    println("REPRODUCED toml-signed-date-time")
end
