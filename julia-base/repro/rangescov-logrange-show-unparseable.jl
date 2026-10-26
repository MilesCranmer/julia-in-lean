r = logrange(1.0, 4.0, 5)
s = repr(r)
println("repr(logrange(1.0, 4.0, 5)) = ", s)
println("repr(Base.OneTo(3)) = ", repr(Base.OneTo(3)))
bug = false
try
    println("eval(Meta.parse(s)) == r: ", eval(Meta.parse(s)) == r)
catch e
    println("eval(Meta.parse(s)) throws ", sprint(showerror, e))
    global bug = e isa UndefVarError
end
bug && println("REPRODUCED rangescov-logrange-show-unparseable")
