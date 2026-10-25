ex = Meta.parse("x::(-T)")          # Expr(:(::), :x, Expr(:call, :-, :T))
s = string(ex)
println("string(ex) = ", repr(s))
back = try Meta.parse(s) catch err; err end
println("Meta.parse(string(ex)) = ", back isa Exception ? typeof(back) : repr(back))
back != ex && println("REPRODUCED show-expr-decl-unary-rhs")
