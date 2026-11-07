threw = false
for v in (Int32[0x61, -1], UInt32[0x61, 0x00200000])
    try
        println("transcode(UInt8, ", repr(v), ") = ", repr(transcode(UInt8, v)))
    catch e
        println("transcode(UInt8, ", repr(v), ") threw ", typeof(e), ": ", sprint(showerror, e))
        v isa Vector{UInt32} && e isa Base.CodePointError{UInt32} && (global threw = true)
    end
end
threw && println("REPRODUCED transcode-utf32-out-of-range")
