# The Base64 manual (stdlib/Base64/docs/src/index.md, master) says: "When decoding,
# if the data has padding outside of its specified location in the last 0-2
# characters of the last group of four alphabet characters (e.g. "A===", "AAAA=",
# "A=AA"), the data is rejected with ArgumentError: malformed base64 sequence."
# decode_slow (stdlib/Base64/src/decode.jl:158-181) treats a padded group as an
# ordinary group and keeps decoding after it.
using Base64

function try_decode(s)
    try
        base64decode(s)
    catch e
        e
    end
end

r1 = try_decode("QQ==QQ==")        # padding in the first of two groups
println("base64decode(\"QQ==QQ==\") = ", repr(r1))

# For long inputs the same strings are also silently truncated.
a = fill(0x61, 1023)
b = fill(0x62, 30)
s = "QQ==" * base64encode(a) * base64encode(b)
r2 = try_decode(s)
println("length(s) = ", length(s), ", result = ",
        r2 isa Exception ? repr(r2) : "$(length(r2)) bytes (input carries 1 + 1023 + 30 = 1054)")

if !(r1 isa ArgumentError)
    println("REPRODUCED base64uuid-decode-padding-midstream")
end
