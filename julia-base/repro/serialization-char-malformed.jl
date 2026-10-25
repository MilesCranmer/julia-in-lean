using Serialization

# A malformed Char, as produced by iterating a String holding invalid UTF-8.
c = "\xc0"[1]

# 1. A tuple followed by a second value in the same stream.
io = IOBuffer()
serialize(io, (c, Int32(1)))
serialize(io, 42)
seekstart(io)
y = deserialize(io)
println("first deserialize: ", repr(y), "  (expected ", repr((c, Int32(1))), ")")
after = try
    repr(deserialize(io))
catch e
    "throws " * sprint(showerror, e)
end
println("second deserialize: ", after, "  (expected 42)")

# 2. A Dict{Char,Int32} on its own.
d = Dict{Char,Int32}(c => 0)
io2 = IOBuffer()
serialize(io2, d)
seekstart(io2)
r2 = try
    repr(deserialize(io2))
catch e
    "throws " * sprint(showerror, e)
end
println("Dict round trip: ", r2, "  (expected ", repr(d), ")")

if y != (c, Int32(1)) && !occursin("Dict(", r2)
    println("REPRODUCED serialization-char-malformed")
end
