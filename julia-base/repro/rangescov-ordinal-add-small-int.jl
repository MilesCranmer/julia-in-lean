r, s = Int8(126):Int8(127), Int8(1):Int8(2)
println("collect(r) + collect(s) = ", collect(r) + collect(s))
bug = false
try
    t = r + s
    println(typeof(t))
    println("collect(r + s) = ", collect(t))
catch e
    println("collect(r + s) throws ", sprint(showerror, e))
    global bug = e isa InexactError
end
bug && println("REPRODUCED rangescov-ordinal-add-small-int")
