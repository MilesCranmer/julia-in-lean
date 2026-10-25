import TOML
# 22 octal digits can exceed UInt64, but the length rule picks UInt64 for them.
small = "a = 0o2000000000000000000000"    # 2^64
big   = "a = 0o20000000000000000000000"   # 2^67
r1 = TOML.tryparse(small)
r2 = TOML.tryparse(big)
println(r1 isa TOML.ParserError ? "ParserError: " * string(r1.type) : r1)
println(r2)
println(TOML.tryparse("a = 0x10000000000000000"))
# The UInt128 limit has the same problem at 43 octal digits (0o4 followed by 42 zeros is 2^128).
println(TOML.tryparse("a = 0o4" * "0"^42) isa TOML.ParserError, " ", typeof(TOML.tryparse("a = 0o4" * "0"^43)["a"]))
if r1 isa TOML.ParserError && r2 isa Dict
    println("REPRODUCED toml-octal-overflow-length")
end
