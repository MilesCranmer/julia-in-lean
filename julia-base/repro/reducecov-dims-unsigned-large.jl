# A reduction over a dimension given as a large unsigned integer throws InexactError
# from Int(d) in _check_valid_region (base/reducedim.jl:33), while the same trailing
# dimension as an Int (or axes(A, d)) is accepted.
function outcome(f)
    try
        repr(f())
    catch e
        string(typeof(e))
    end
end
a = outcome(() -> sum([1, 2]; dims=UInt(2)^63))
b = outcome(() -> sum([1, 2]; dims=typemax(Int)))
c = outcome(() -> maximum([1, 2]; dims=UInt(2)^63))
d = outcome(() -> axes([1, 2], UInt(2)^63))
println("sum([1, 2]; dims=UInt(2)^63) -> ", a)
println("sum([1, 2]; dims=typemax(Int)) -> ", b)
println("maximum([1, 2]; dims=UInt(2)^63) -> ", c)
println("axes([1, 2], UInt(2)^63) -> ", d)
if a == "InexactError" && b == "[1, 2]"
    println("REPRODUCED reducecov-dims-unsigned-large")
end
