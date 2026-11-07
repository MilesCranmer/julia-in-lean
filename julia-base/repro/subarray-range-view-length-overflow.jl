println("JULIA ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)
parent = typemin(Int):typemax(Int)
println("parent scalar at 1 = ", parent[1])
failed = true
for selector in (1:1, 1:1:1)
    outcome = try
        value = view(parent, selector)
        println("view with ", typeof(selector), " = ", value)
        false
    catch error
        println("view with ", typeof(selector), " throws ", typeof(error))
        error isa BoundsError
    end
    global failed &= outcome
end
if parent[1] == typemin(Int) && failed
    println("REPRODUCED subarray-range-view-length-overflow")
else
    error("Range view overflow was not reproduced")
end
