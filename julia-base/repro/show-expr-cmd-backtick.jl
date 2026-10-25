ex = Meta.parse("`echo \\`x\\``")   # command literal whose text contains a backtick
println("ex.args[3] = ", repr(ex.args[3]))
s = string(ex)
println("string(ex) = ", repr(s))
back = Meta.parse(s)
println("Meta.parse(string(ex)) = ", repr(back))
Base.remove_linenums!(back) != Base.remove_linenums!(copy(ex)) && println("REPRODUCED show-expr-cmd-backtick")
