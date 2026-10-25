import TOML
# Integers that fit in Int64 are returned as Int128 once their text is longer than 17 characters.
for s in ("a = 12345678901234567", "a = 123456789012345678", "a = 1700000000000000000",
          "a = 9223372036854775807", "a = -10000000000000000", "a = 0x00000000000000001")
    v = TOML.parse(s)["a"]
    println(rpad(s, 28), " => ", typeof(v), " ", v)
end
println(typeof(TOML.parse("a = [1, 1700000000000000000]")["a"]))
v = TOML.parse("a = 1700000000000000000")["a"]
if v isa Int128 && typemin(Int64) <= v <= typemax(Int64)
    println("REPRODUCED toml-int64-parsed-as-int128")
end
