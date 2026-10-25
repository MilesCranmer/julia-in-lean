using Sockets

# Same delegation bug on the IPv6 side: parse(Int, f, base=16) accepts signs
# and whitespace, so parse(IPv6, ..) accepts fields like "+1" or " 1".
a = try string(parse(IPv6, "::+1")) catch; "error" end
b = try string(parse(IPv6, ":: 1")) catch; "error" end
println("parse(IPv6, \"::+1\") = ", a)
println("parse(IPv6, \":: 1\") = ", b)
ok = a == "::1" && b == "::1"
println(ok ? "REPRODUCED sockets-ipv6-field-grammar" : "not reproduced")
