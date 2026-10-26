using Base: PCRE
# NO_START_OPTIMIZE is listed in PCRE.EXECUTE_MASK, so the Regex constructor accepts it as a match option
r = Regex("a", Base.DEFAULT_COMPILER_OPTS, Base.DEFAULT_MATCH_OPTS | PCRE.NO_START_OPTIMIZE)
println("constructed: ", r)
res = try match(r, "a") catch e e end
println("match(r, \"a\") -> ", repr(res))
res isa ErrorException && occursin("bad option value", res.msg) &&
    println("REPRODUCED stringscovb-regex-execute-mask")
