# in(pair, ::ImmutableDict) does `valcmp(value, dict.value) && return true`,
# which throws on a missing comparison; the AbstractDict method returns missing.
const ID = Base.ImmutableDict
r1 = try; (:a => missing) in ID(:a => 1); catch e; sprint(showerror, e); end
r2 = (:a => missing) in Dict(:a => 1)
r3 = try; ID(:a => missing) == ID(:a => missing); catch e; sprint(showerror, e); end
r4 = Dict(:a => missing) == Dict(:a => missing)
println("(:a => missing) in ImmutableDict(:a => 1): ", repr(r1))
println("(:a => missing) in Dict(:a => 1): ", repr(r2))
println("ImmutableDict(:a => missing) == ImmutableDict(:a => missing): ", repr(r3))
println("Dict(:a => missing) == Dict(:a => missing): ", repr(r4))
if r1 isa String && startswith(r1, "TypeError") && r2 === missing && r3 isa String && r4 === missing
    println("REPRODUCED dicts-immutabledict-in-missing")
end
