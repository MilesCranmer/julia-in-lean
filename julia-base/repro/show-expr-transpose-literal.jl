ex = Meta.parse("(-1)'")            # Expr(Symbol("'"), -1)
s = string(ex)
println("string(ex) = ", repr(s))
back = try Meta.parse(s) catch err; err end
println("Meta.parse(string(ex)) = ", back isa Exception ? typeof(back) : repr(back))
back != ex && println("REPRODUCED show-expr-transpose-literal")
