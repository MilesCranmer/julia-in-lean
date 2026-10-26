# replace(A, old_new...) without count removes replaced singleton types from
# the element type (docstring, base/set.jl:817-820), and for a Set it builds
# that narrower set with union!(empty(A, T), A) before replacing
# (base/set.jl:721, 731, 846), so the old elements no longer fit.
v = replace([1, missing], missing => 0)
t = replace((1, missing), missing => 0)
println("replace([1, missing], missing => 0) = ", v)
println("replace((1, missing), missing => 0) = ", t)
r = try
    replace(Set([1, missing]), missing => 0)
catch e
    e
end
println("replace(Set([1, missing]), missing => 0) = ", r isa Exception ? typeof(r) : r)
r2 = try
    replace(Set([1, nothing]), nothing => 0)
catch e
    e
end
println("replace(Set([1, nothing]), nothing => 0) = ", r2 isa Exception ? typeof(r2) : r2)
if r isa MethodError && r2 isa MethodError && v == [1, 0]
    println("REPRODUCED bitsetscov-replace-set-singleton")
end
