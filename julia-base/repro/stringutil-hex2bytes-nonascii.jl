bytes = UInt8[0xc0, 0xb0, 0x30]
s = String(copy(bytes))
sub = SubString(s)

println("VERSION ", VERSION)
println("INPUT_CODEUNITS ", collect(codeunits(s)))
println("ISOVERLONG ", isoverlong(first(s)), " ISMALFORMED ", ismalformed(first(s)))

try
    println("UInt8(Char) RESULT ", UInt8(first(s)))
catch err
    println("UInt8(Char) ERROR ", typeof(err), " ", sprint(showerror, err))
end

try
    result = hex2bytes(sub)
    println("hex2bytes(SubString) RESULT ", result)
    result == UInt8[0x00] && println("REPRODUCED stringutil-hex2bytes-nonascii")
catch err
    println("hex2bytes(SubString) ERROR ", typeof(err), " ", sprint(showerror, err))
end
