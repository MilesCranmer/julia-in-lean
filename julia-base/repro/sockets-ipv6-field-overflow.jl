using Sockets

# IPv6 groups may hold at most four hex digits (RFC 4291 section 2.2); the
# documented IPv6(::Integer...) constructor checks 0 <= x <= 0xFFFF. parse does
# not: an oversized field bleeds into the neighbouring groups or wraps away.
a = try string(parse(IPv6, "::10000")) catch; "error" end
b = try string(parse(IPv6, "::12345")) catch; "error" end
println("parse(IPv6, \"::10000\") = ", a)
println("parse(IPv6, \"::12345\") = ", b)
ok = a == "::1:0" && b == "::1:2345"
println(ok ? "REPRODUCED sockets-ipv6-field-overflow" : "not reproduced")
