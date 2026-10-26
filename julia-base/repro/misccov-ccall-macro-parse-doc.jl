# The docstring of Base.ccall_macro_parse (base/c.jl:255-264) says
#   "returns: a tuple of `(function_name, return_type, arg_types, args)`
#    The above input outputs this: (:printf, :Cvoid, [:Cstring, :Cuint], ["%d", :value])"
r = Base.ccall_macro_parse(:(printf("%d"::Cstring, value::Cuint)::Cvoid))
println("ccall_macro_parse(:(printf(\"%d\"::Cstring, value::Cuint)::Cvoid)) = ", repr(r))
println("length = ", length(r), ", first element = ", repr(r[1]))
if length(r) != 4 || r[1] !== :printf
    println("REPRODUCED misccov-ccall-macro-parse-doc")
end
