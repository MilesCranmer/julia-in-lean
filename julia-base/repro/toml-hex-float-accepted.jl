import TOML
# TOML has no hexadecimal floats; "0x" with no hex digit falls through to Float64 parsing.
r = TOML.tryparse("a = 0x.5")
println(r)
println(TOML.tryparse("a = 0x5.5") isa TOML.ParserError)
if r isa Dict && r["a"] == 0.3125
    println("REPRODUCED toml-hex-float-accepted")
end
