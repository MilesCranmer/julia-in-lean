# IdDict `pop!(d, k)` (base/iddict.jl:117-121) detects a hit through the
# `secret_table_token` sentinel: when the stored value *is* the token symbol,
# the entry is removed (count/ndel updated by the two-argument `pop!`) and the
# one-argument `pop!` then throws KeyError for a key that was present.
const T = Symbol("__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__")

d = IdDict{Any,Any}()
d["k"] = T
threw = try
    pop!(d, "k")
    nothing
catch e
    typeof(e)
end
if threw === KeyError && length(d) == 0
    println("pop!(d, \"k\") threw KeyError while the key was present")
    println("length(d) after the throw: ", length(d), " (entry was removed)")
    println("REPRODUCED iddicts-token-pop")
else
    println("not reproduced: threw=", threw, " length=", length(d))
end
