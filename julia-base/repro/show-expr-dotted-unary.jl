ex = Meta.parse(".-x")              # Expr(:call, :.-, :x): broadcast unary minus
s = string(ex)
println("string(ex) = ", repr(s))
back = Meta.parse(s)
println("Meta.parse(string(ex)) = ", sprint(Meta.show_sexpr, back), "   original = ", sprint(Meta.show_sexpr, ex))
back != ex && println("REPRODUCED show-expr-dotted-unary")
