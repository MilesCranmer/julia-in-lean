threw = false
for v in (Int32[0x61, -1], UInt32[0x61, 0x00200000])
    try
        println("transcode(String, ", repr(v), ") = ", repr(transcode(String, v)))
    catch e
        println("transcode(String, ", repr(v), ") threw ", typeof(e), ": ", sprint(showerror, e))
        v isa Vector{UInt32} && (global threw = true)
    end
end
threw && println("REPRODUCED transcode-utf32-out-of-range")
