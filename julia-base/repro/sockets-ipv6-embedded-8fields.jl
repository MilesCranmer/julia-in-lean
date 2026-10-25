using Sockets

# "::1:2:3:4:5:1.2.3.4" is valid IPv6 text (five groups + embedded IPv4 around
# one elided group); inet_pton accepts it. parse(IPv6, ..) rejects it because
# the split has 8 tokens, so the length == 8 branch parses "1.2.3.4" as a hex
# group instead of taking the embedded-IPv4 branch.
buf = zeros(UInt8, 16)
libc_ok = ccall((:inet_pton, "libc.so.6"), Cint, (Cint, Cstring, Ptr{Cvoid}),
                Cint(10), "::1:2:3:4:5:1.2.3.4", buf) == 1
r = nothing
try
    parse(IPv6, "::1:2:3:4:5:1.2.3.4")
catch e
    global r = e
end
println("inet_pton(\"::1:2:3:4:5:1.2.3.4\") accepted = ", libc_ok)
println("parse(IPv6, \"::1:2:3:4:5:1.2.3.4\") threw ",
        r === nothing ? "nothing" : string(nameof(typeof(r)), ": ", r.msg))
ok = libc_ok && r isa ArgumentError
println(ok ? "REPRODUCED sockets-ipv6-embedded-8fields" : "not reproduced")
