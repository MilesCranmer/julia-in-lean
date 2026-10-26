# expand_ccallable (base/c.jl:201-234) throws "expected method definition in @ccallable"
# for anything that is not a method definition, but a function forward declaration
# `function f end` reaches `sig.head` on the Symbol `f` and throws a FieldError.
r1 = try macroexpand(Main, :(Base.@ccallable Int 1)) catch e; e end
r2 = try macroexpand(Main, :(Base.@ccallable function f end)) catch e; e end
println("@ccallable Int 1          => ", typeof(r1), ": ", sprint(showerror, r1))
println("@ccallable function f end => ", typeof(r2), ": ", sprint(showerror, r2))
if r1 isa ErrorException && r2 isa FieldError
    println("REPRODUCED misccov-ccallable-forward-decl")
end
