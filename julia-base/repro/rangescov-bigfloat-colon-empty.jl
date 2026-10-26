# a:b with b < a should be an empty range (docstring of (:), base/range.jl:54-55)
println("Float64: 3.0:1.0 = ", repr(3.0:1.0), ", isempty = ", isempty(3.0:1.0))
bug = false
try
    r = big(3.0):big(1.0)
    println("BigFloat: big(3.0):big(1.0) = ", repr(r), ", isempty = ", isempty(r))
catch e
    println("BigFloat: big(3.0):big(1.0) throws ", sprint(showerror, e))
    global bug = e isa ArgumentError
end
bug && println("REPRODUCED rangescov-bigfloat-colon-empty")
