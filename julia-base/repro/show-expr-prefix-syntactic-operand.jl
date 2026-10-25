function check(src)
    ex = Meta.parse(src)
    s = string(ex)
    back = try Meta.parse(s) catch err; err end
    println(rpad(src, 8), " string(ex) = ", rpad(repr(s), 8), " Meta.parse(string(ex)) = ", back isa Exception ? typeof(back) : repr(back))
    return back != ex
end
bad = map(check, ["::(-1)", "::(!a)", "\$(-1)", "&(-1)"])
any(bad) && println("REPRODUCED show-expr-prefix-syntactic-operand")
