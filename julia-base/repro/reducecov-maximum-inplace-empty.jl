# maximum!(r, A) (and minimum!, extrema!) with init=true throws a BoundsError from an
# internal view when A is empty along a reduced dimension, while maximum(A; dims)
# throws the documented ArgumentError for the same reduction.
function outcome(f)
    try
        repr(f())
    catch e
        string(typeof(e))
    end
end
a = outcome(() -> maximum!(zeros(1), zeros(0)))
b = outcome(() -> maximum(zeros(0); dims=1))
c = outcome(() -> minimum!(zeros(2), zeros(2, 0)))
d = outcome(() -> minimum(zeros(2, 0); dims=2))
e = outcome(() -> extrema!([(0.0, 0.0)], zeros(0)))
println("maximum!(zeros(1), zeros(0)) -> ", a)
println("maximum(zeros(0); dims=1) -> ", b)
println("minimum!(zeros(2), zeros(2, 0)) -> ", c)
println("minimum(zeros(2, 0); dims=2) -> ", d)
println("extrema!([(0.0, 0.0)], zeros(0)) -> ", e)
if a == "BoundsError" && b == "ArgumentError" && c == "BoundsError" && d == "ArgumentError"
    println("REPRODUCED reducecov-maximum-inplace-empty")
end
