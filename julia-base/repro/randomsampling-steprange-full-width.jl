using Random

r = typemin(Int):1:typemax(Int)
println("typeof = ", typeof(r), "; isempty = ", isempty(r), "; length = ", length(r))
println("UnitRange: rand(Xoshiro(1), typemin(Int):typemax(Int)) = ", rand(Xoshiro(1), typemin(Int):typemax(Int)))
try
    println("rand = ", rand(Xoshiro(1), r))
    println("NOT REPRODUCED randomsampling-steprange-full-width")
catch e
    println(typeof(e), ": ", sprint(showerror, e))
    if e isa ArgumentError && !isempty(r)
        println("REPRODUCED randomsampling-steprange-full-width")
    else
        rethrow()
    end
end
