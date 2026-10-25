using Sockets

# parse(IPv6, "") silently returns the unspecified address "::";
# inet_pton and every other IPv6 parser reject the empty string.
ok = false
try
    global ok = parse(IPv6, "") == ip"::"
catch
end
println("parse(IPv6, \"\") = ", try string(parse(IPv6, "")) catch e; string(nameof(typeof(e))) end)
println(ok ? "REPRODUCED sockets-ipv6-empty-string" : "not reproduced")
