using Sockets

# A dotted-quad field that overflows Int64 escapes parse(IPv4, ..) as an
# OverflowError from Base.parse(Int, ..) instead of an ArgumentError.
r = nothing
try
    parse(IPv4, "1.2.3.999999999999999999999999")
catch e
    global r = e
end
println("parse(IPv4, \"1.2.3.999999999999999999999999\") threw ",
        r === nothing ? "nothing" : nameof(typeof(r)))
ok = r isa OverflowError
println(ok ? "REPRODUCED sockets-ipv4-overflow-error" : "not reproduced")
