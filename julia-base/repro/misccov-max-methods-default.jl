# Base.Experimental.@max_methods docstring (base/experimental.jl:162-178):
# "Supported values are `1`, `2`, `3`, `4`, and `default` (currently equivalent to `3`)."
# The macro is defined only as `@max_methods(n::Int)` (and the two-argument form), so the
# documented value `default` is rejected with a MethodError.
r = try
    macroexpand(Main, :(Base.Experimental.@max_methods default))
catch e
    e
end
println("@max_methods default => ", r isa Exception ? sprint(showerror, r)[1:min(end, 140)] : repr(r))
println("@max_methods 3       => ", repr(macroexpand(Main, :(Base.Experimental.@max_methods 3))))
if r isa Exception
    println("REPRODUCED misccov-max-methods-default")
end
