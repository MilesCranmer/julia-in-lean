println("JULIA ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)
parent = typemin(Int):(Int(1) << 62):(Int(1) << 62)
selector = 1:2:3
expected = [parent[index] for index in selector]
actual = view(parent, selector)
println("parent = ", collect(parent))
println("selector = ", collect(selector))
println("expected = ", expected)
println("actual = ", collect(actual))
if expected == [typemin(Int), 0] && isempty(actual)
    println("REPRODUCED subarray-step-view-step-overflow")
else
    error("Composed step overflow was not reproduced")
end
