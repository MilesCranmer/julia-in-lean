# Base.cwstring (base/strings/cstring.jl:119-123) is defined only on Windows. Its body:
#     bytes = codeunits(String(s))
#     0 in bytes && throw(ArgumentError("embedded NULs are not allowed in C strings: $(repr(s))"))
#     return push!(transcode(UInt16, bytes), 0)
# The lines below run the same calls on any platform.
s = "PATH\xc0\x80X"
bytes = codeunits(String(s))
w = transcode(UInt16, bytes)
println("'\\0' in s = ", '\0' in s, ", 0 in bytes = ", 0 in bytes)
println("transcode(UInt16, bytes) = ", repr(w))
!(0 in bytes) && (0 in w) && println("REPRODUCED transcode-cwstring-overlong-nul")
