T = typeof((; var"+" = 1))          # NamedTuple{(:+,), Tuple{Int64}}
s = repr(T)
println("repr(T) = ", repr(s))
r = try eval(Meta.parse(s)) catch err; err end
println("eval(Meta.parse(repr(T))) = ", r isa Exception ? typeof(r) : repr(r))
r !== T && println("REPRODUCED show-namedtuple-type-operator")
