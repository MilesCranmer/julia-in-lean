r = 0:-1
println("isempty(0:-1) = ", isempty(r), "; convert(Vector{UInt8}, collect(r)) = ", convert(Vector{UInt8}, collect(r)))
bug = false
try
    println("convert(UnitRange{UInt8}, 0:-1) = ", repr(convert(UnitRange{UInt8}, r)))
catch e
    println("convert(UnitRange{UInt8}, 0:-1) throws ", sprint(showerror, e))
    global bug = e isa InexactError
end
bug && println("REPRODUCED rangescov-unitrange-convert-empty")
