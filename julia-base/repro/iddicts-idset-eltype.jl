# IdSet push! (base/idset.jl:48-70) neither converts nor checks its argument
# against the element type. An IdSet{Int} accepts a String; iterate's
# s.list[state]::S cast (base/idset.jl:125) then throws TypeError, and
# union! (base/abstractset.jl:105-111) stops early because it trusts
# length(s) == max_values(T).
s = IdSet{Int}()
push!(s, "a string")
accepted = ("a string" in s) && length(s) == 1
c = try
    collect(s); "no error"
catch e
    typeof(e)
end
setcmp = try
    push!(Set{Int}(), "a string"); "accepted"
catch e
    typeof(e)
end
b = IdSet{Bool}(Any[1, 2, true, false])
println("IdSet{Int} push!(s, \"a string\"): in = ", "a string" in s, ", length = ", length(s))
println("collect(s) threw: ", c)
println("push!(Set{Int}(), \"a string\") threw: ", setcmp)
println("IdSet{Bool}(Any[1, 2, true, false]): length = ", length(b),
        ", true in = ", true in b, ", false in = ", false in b)
if accepted && c === TypeError && !(true in b)
    println("REPRODUCED iddicts-idset-eltype")
end
