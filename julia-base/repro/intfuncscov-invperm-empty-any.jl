v = Any[]
tuple_result = invperm(())
vector_result = try
    invperm(v)
catch e
    e
end
println("isperm(Any[]) = ", isperm(v))
println("invperm(()) = ", tuple_result)
println("invperm(Any[]) = ", vector_result isa Exception ? sprint(showerror, vector_result) : vector_result)
if isperm(v) && tuple_result == () && vector_result isa MethodError
    println("REPRODUCED intfuncscov-invperm-empty-any")
else
    println("not reproduced")
end
