a, b = typemax(Int) - 10, typemax(Int)
bug = false
try
    r = range(a, b; length=3)
    println("range(typemax(Int)-10, typemax(Int); length=3) = ", collect(r))
catch e
    println("range(typemax(Int)-10, typemax(Int); length=3) throws ", sprint(showerror, e))
    global bug = e isa InexactError
end
println("Float64 endpoints: ", Float64(a), " ", Float64(b))
bug && println("REPRODUCED rangescov-linspace-int-imin-inexact")
