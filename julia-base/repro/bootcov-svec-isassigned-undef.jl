# isassigned(v::SimpleVector, i) (base/essentials.jl:1141-1144) only checks bounds,
# so it returns true for a slot holding an undefined reference.
v = ccall(:jl_alloc_svec, Any, (Int,), 2)::Core.SimpleVector
println("length(v)        = ", length(v))
r = run(ignorestatus(`$(Base.julia_cmd()) --startup-file=no -e "v = ccall(:jl_alloc_svec, Any, (Int,), 2); try v[1]; println(\"v[1] returned\") catch e; println(\"v[1] throws \", typeof(e)) end"`))
println("child exit code for v[1]: ", r.exitcode)
println("isassigned(v, 1) = ", isassigned(v, 1))
if isassigned(v, 1)
    println("REPRODUCED bootcov-svec-isassigned-undef")
end
