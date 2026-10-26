# The extended-capability names of a terminfo file are read at the wrong
# offset when the extended section has no string capabilities, or when its
# last string capability is absent (base/terminfo.jl:131-136).
le16(x) = reinterpret(UInt8, [htol(Int16(x))])

# Legacy header: magic, name_bytes=2, no flags/numbers/strings, empty table; name "x".
header() = vcat(le16(0o432), le16(2), le16(0), le16(0), le16(0), le16(0), Vector{UInt8}("x\0"))

# Extended section 1: one boolean "AX" = true, no strings.
ext1 = vcat(le16(1), le16(0), le16(0), le16(1), le16(3),  # flags, numbers, strings, table entries, table bytes
            [0x01, 0x00],                                  # flag value, pad to even
            le16(0),                                       # name offset of "AX"
            Vector{UInt8}("AX\0"))
r1 = read(IOBuffer(vcat(header(), ext1)), Base.TermInfoRaw).extended
println("flag only: ", r1)

# Extended section 2: strings Sa = "ab" and Sb absent (-1).
tbl = Vector{UInt8}("ab\0Sa\0Sb\0")
ext2 = vcat(le16(0), le16(0), le16(2), le16(4), le16(length(tbl)),
            le16(0), le16(-1),     # string value offsets
            le16(0), le16(3),      # name offsets, relative to the start of the names
            tbl)
r2 = read(IOBuffer(vcat(header(), ext2)), Base.TermInfoRaw).extended
println("last string absent: ", r2)

if !haskey(r1, :AX) && haskey(r1, :X) && !haskey(r2, :Sb) && get(r2, :ab, nothing) == "ab"
    println("REPRODUCED showcov-terminfo-extended-labels")
end
