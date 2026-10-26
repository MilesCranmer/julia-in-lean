failed = false
for T in (Union{}, Type{Int})
    try
        println("hasfield(", T, ", :name) = ", hasfield(T, :name))
    catch e
        println("hasfield(", T, ", :name) throws ", typeof(e))
        global failed = true
    end
end
if failed
    println("REPRODUCED runtimecov-hasfield-kind-types")
end
