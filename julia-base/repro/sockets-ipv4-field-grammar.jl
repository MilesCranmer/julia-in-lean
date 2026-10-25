using Sockets

# parse(IPv4, ..) rejects leading zeros "due to ambiguity" but accepts fields
# with a sign or surrounding whitespace, because it delegates each field to
# parse(Int, f, base=10), which allows [whitespace] sign [whitespace] digits
# [whitespace].
a = try string(parse(IPv4, "+1.2.3.4")) catch; "error" end
b = try string(parse(IPv4, "1.2.3.+4")) catch; "error" end
c = try string(parse(IPv4, " 98.7.6.6 ")) catch; "error" end
d = try string(parse(IPv4, "1.2.3.-0")) catch; "error" end
e = try string(parse(IPv4, "1.2.3.4\n")) catch; "error" end
println("parse(IPv4, \"+1.2.3.4\")    = ", a)
println("parse(IPv4, \"1.2.3.+4\")    = ", b)
println("parse(IPv4, \" 98.7.6.6 \")  = ", c)
println("parse(IPv4, \"1.2.3.-0\")    = ", d)
println("parse(IPv4, \"1.2.3.4\\n\")  = ", e)
ok = a == "1.2.3.4" && b == "1.2.3.4" && c == "98.7.6.6" && d == "1.2.3.0" && e == "1.2.3.4"
println(ok ? "REPRODUCED sockets-ipv4-field-grammar" : "not reproduced")
