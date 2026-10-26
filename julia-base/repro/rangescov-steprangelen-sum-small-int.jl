r = (Int8(1):Int8(100)) .* Int8(1)
println(typeof(r), " ", r == 1:100)
println("sum(collect(r)) = ", sum(collect(r)))
bug = false
try
    println("sum(r) = ", sum(r))
catch e
    println("sum(r) throws ", sprint(showerror, e))
    global bug = e isa InexactError
end
bug && println("REPRODUCED rangescov-steprangelen-sum-small-int")
