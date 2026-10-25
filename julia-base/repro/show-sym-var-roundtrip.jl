sym = Symbol("a\rb")                       # name containing a carriage return
ex = Expr(:call, :f, sym)
s = string(ex)                             # show_sym prints var"..." with the raw \r byte
println("string(ex) = ", repr(s))
back = Meta.parse(s)
println("Meta.parse(string(ex)) = ", repr(back), "  args[2] = ", repr(String(back.args[2])))
nt = NamedTuple{(sym,)}((1,))
r = repr(nt)
println("repr(nt) = ", repr(r))
nt2 = eval(Meta.parse(r))
println("fieldnames(eval(Meta.parse(repr(nt)))) = ", repr(map(String, fieldnames(typeof(nt2)))))
bad = Symbol("a b\xff")                    # invalid UTF-8 name (isidentifier stops at the space)
s2 = string(Expr(:call, :f, bad))
println("string(Expr(:call, :f, Symbol(\"a b\\xff\"))) = ", repr(s2))
b2 = try Meta.parse(s2) catch err; err end
println("Meta.parse of that = ", b2 isa Exception ? typeof(b2) : repr(b2))
(back != ex || keys(nt2) != keys(nt)) && println("REPRODUCED show-sym-var-roundtrip")
