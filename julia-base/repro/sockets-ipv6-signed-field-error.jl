using Sockets

# A signed field in IPv6 text should be rejected with ArgumentError like every
# other malformed field, but UInt128(parse(Int, f, base=16)) throws InexactError.
r = nothing
try
    parse(IPv6, "::-1")
catch e
    global r = e
end
println("parse(IPv6, \"::-1\") threw ", r === nothing ? "nothing" : nameof(typeof(r)))
ok = r isa InexactError
println(ok ? "REPRODUCED sockets-ipv6-signed-field-error" : "not reproduced")
