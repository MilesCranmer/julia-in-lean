# uuid5(ns, name) is documented as "specified by RFC 4122", whose section 4.3 hashes
# the namespace bytes followed by the bytes of the name.  Julia hashes
# codeunits(unescape_string(name)) (stdlib/UUIDs/src/UUIDs.jl:152), so a name that is
# an escape spelling of another collides with it, and names such as Windows paths
# throw.
using UUIDs

ns = UUIDs.namespace_dns
u1 = uuid5(ns, "a\\nb")    # 4 characters: a, backslash, n, b
u2 = uuid5(ns, "a\nb")     # 3 characters: a, newline, b
println("uuid5(ns, \"a\\\\nb\") = ", u1)
println("uuid5(ns, \"a\\nb\")  = ", u2)

# RFC 4122 section 4.3 over the raw name bytes, with the SHA module UUIDs itself uses.
function rfc_uuid5(ns::UUID, name::String)
    nsb = UInt8[(ns.value >> (8 * (16 - i))) & 0xff for i in 1:16]
    h = UUIDs.SHA.sha1(vcat(nsb, codeunits(name)))
    h[7] = (h[7] & 0x0f) | 0x50
    h[9] = (h[9] & 0x3f) | 0x80
    return UUID(foldl((v, b) -> v << 8 | b, h[1:16]; init = UInt128(0)))
end
println("RFC 4122 uuid5 of \"a\\\\nb\" = ", rfc_uuid5(ns, "a\\nb"))

r = try
    uuid5(ns, "C:\\Users\\julia")
catch e
    e
end
println("uuid5(ns, \"C:\\\\Users\\\\julia\") = ", repr(r))

if u1 == u2 && u1 != rfc_uuid5(ns, "a\\nb")
    println("REPRODUCED base64uuid-uuid5-unescape")
end
