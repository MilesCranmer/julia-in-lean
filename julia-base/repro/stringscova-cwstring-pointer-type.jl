cw = Cwstring(Ptr{Cwchar_t}(C_NULL))
p = Ptr{Cvoid}(cw)
println("typeof(Ptr{Cvoid}(cw)) = ", typeof(p))
println("requested type = ", Ptr{Cvoid})
if typeof(p) !== Ptr{Cvoid}
    println("REPRODUCED stringscova-cwstring-pointer-type")
end
