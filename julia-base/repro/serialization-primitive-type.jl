using Serialization

# A user-defined primitive type with no write/read methods of its own.
primitive type Bits32 32 end
x = reinterpret(Bits32, 0x01020304)

function roundtrip(v)
    io = IOBuffer()
    try
        serialize(io, v)
        seekstart(io)
        y = deserialize(io)
        return isequal(y, v) && typeof(y) === typeof(v) ? "ok" : "wrong result $(repr(y))"
    catch e
        return "throws " * first(split(sprint(showerror, e), '\n'))
    end
end

r_scalar = roundtrip(x)
r_vector = roundtrip([x, x])
println("serialize(io, x):          ", r_scalar)
println("serialize(io, [x, x]):     ", r_vector)

if startswith(r_scalar, "throws MethodError") && r_vector == "ok"
    println("REPRODUCED serialization-primitive-type")
end
