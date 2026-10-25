using Sockets

# A single leading or trailing ':' (not part of a '::' pair) is invalid IPv6
# text, but parse(IPv6, ..) accepts it and silently shifts the address.
a = try string(parse(IPv6, ":1")) catch; "error" end
b = try string(parse(IPv6, "1:")) catch; "error" end
println("parse(IPv6, \":1\") = ", a)
println("parse(IPv6, \"1:\") = ", b)
ok = a == "0:1::" && b == "1::"
println(ok ? "REPRODUCED sockets-ipv6-lone-colon" : "not reproduced")
