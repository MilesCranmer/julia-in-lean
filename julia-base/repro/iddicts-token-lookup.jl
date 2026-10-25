# IdDict stores a value that is `Base.secret_table_token`
# (base/abstractdict.jl:17): `in`/`haskey` report the key absent and `d[k]`
# throws KeyError although the entry is present; `in(::Pair, d)` and
# `mergewith!` inherit the wrong answer.
const T = Symbol("__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__")

d = IdDict{Any,Any}()
d["k"] = T
present_in = in("k", keys(d))
present_haskey = haskey(d, "k")
present_get = get(d, "k", "MISSING") === T
got = try
    d["k"]
    "no error"
catch e
    typeof(e)
end
pair_in = ("k" => T) in d
m = mergewith!((x, y) -> (x, y), IdDict{Any,Any}("k" => T), IdDict{Any,Any}("k" => 1))
println("in(k, keys(d)): ", present_in, ", haskey(d, k): ", present_haskey)
println("get returns stored token: ", present_get)
println("d[k] threw: ", got)
println("length(d) = ", length(d), " (entry still present)")
println("(k => T) in d: ", pair_in)
println("mergewith!(tuple-combine) result for k: ", repr(m["k"]))
if !present_in && !present_haskey && present_get && got === KeyError && !pair_in && m["k"] === 1
    println("REPRODUCED iddicts-token-lookup")
end
