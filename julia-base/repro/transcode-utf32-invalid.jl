s = "a\xffb"
println("transcode(UInt16, s) = ", repr(transcode(UInt16, s)))
try
    println("transcode(UInt32, s) = ", repr(transcode(UInt32, s)))
catch e
    println("transcode(UInt32, s) threw ", typeof(e), ": ", sprint(showerror, e))
    e isa Base.InvalidCharError && println("REPRODUCED transcode-utf32-invalid")
end
