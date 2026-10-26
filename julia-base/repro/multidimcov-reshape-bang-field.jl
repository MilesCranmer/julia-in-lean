a = [1, 2, 3, 4]

reproduced = try
    Base.reshape!(a, (4,))
    false
catch err
    println("error = ", repr(err))
    err isa FieldError && err.field === :dims
end

println("array = ", a)
println(reproduced ? "REPRODUCED multidimcov-reshape-bang-field" : "NOT REPRODUCED")
