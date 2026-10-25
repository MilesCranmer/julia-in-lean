using Sockets

# Two '::' elisions are invalid IPv6 text. parse(IPv6, ..) neither rejects them
# nor errors: it silently drops or shifts groups when the field counter goes
# negative and the negative shift discards the remaining groups.
a = try string(parse(IPv6, "1::2::3")) catch; "error" end
b = try string(parse(IPv6, "::1:2::")) catch; "error" end
println("parse(IPv6, \"1::2::3\") = ", a)
println("parse(IPv6, \"::1:2::\") = ", b)
ok = a == "1::2:0:0" && b == "::1:2:0:0"
println(ok ? "REPRODUCED sockets-ipv6-double-elision" : "not reproduced")
