r = LinRange(-90:60:90)
println("LinRange(-90:60:90) = LinRange{", eltype(r), "}(", first(r), ", ", last(r), ", ", length(r), ")")
bug = false
try
    println("r[2] = ", r[2])
catch e
    println("r[2] throws ", sprint(showerror, e))
    global bug = e isa InexactError
end
try
    LinRange{Int8}(Int8(-90), Int8(90), 4)
    println("LinRange{Int8}(-90, 90, 4) constructed")
catch e
    println("LinRange{Int8}(-90, 90, 4) throws ", sprint(showerror, e))
end
bug && println("REPRODUCED rangescov-linrange-integer-elements")
