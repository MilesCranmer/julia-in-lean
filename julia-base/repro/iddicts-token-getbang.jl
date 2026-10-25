# IdDict `get!(d, key, default)` and `get!(f, d, key)` (base/iddict.jl:151-183)
# look the key up through the `secret_table_token` sentinel. When the stored
# value *is* the token symbol, `get!` treats the existing entry as absent,
# overwrites it with the default and returns the default.
const T = Symbol("__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__")

d = IdDict{Any,Any}()
d["k"] = T
r = get!(d, "k", "DEFAULT")
e = IdDict{Any,Any}()
e["k"] = T
rf = get!(() -> "FROM-F", e, "k")
println("get!(d, \"k\", \"DEFAULT\") -> ", repr(r), "; stored value is now: ", repr(d["k"]))
println("get!(() -> \"FROM-F\", e, \"k\") -> ", repr(rf), "; stored value is now: ", repr(e["k"]))
if r === "DEFAULT" && d["k"] === "DEFAULT" && rf === "FROM-F" && e["k"] === "FROM-F"
    println("REPRODUCED iddicts-token-getbang")
end
