sym = Symbol("\x80")
r = try repr(sym) catch err; err end
println("repr(Symbol(\"\\x80\")) = ", r isa Exception ? r : repr(r))
r isa Exception && println("REPRODUCED show-symbol-invalid-utf8")
