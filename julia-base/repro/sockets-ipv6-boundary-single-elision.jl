using Sockets

texts = ("::1:2:3:4:5:6:7", "1:2:3:4:5:6:7::")
errors = Bool[]
for text in texts
    buf = zeros(UInt8, 16)
    accepted = ccall((:inet_pton, "libc.so.6"), Cint,
        (Cint, Cstring, Ptr{Cvoid}), Cint(10), text, buf) == 1
    result = try
        parse(IPv6, text)
    catch e
        e
    end
    println("inet_pton(", repr(text), ") accepted = ", accepted)
    println("parse(IPv6, ", repr(text), ") = ",
        result isa Exception ? string(nameof(typeof(result)), ": ", result.msg) : string(result))
    push!(errors, accepted && result isa ArgumentError)
end
println(all(errors) ? "REPRODUCED sockets-ipv6-boundary-single-elision" : "not reproduced")
