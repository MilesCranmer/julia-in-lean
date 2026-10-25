# PersistentDict looks keys up with === ("behaves like an IdDict"), Dict with
# isequal. The generic AbstractDict == special-cases IdDict but not
# PersistentDict, so == between the two is asymmetric (or throws).
const PD = Base.PersistentDict
p = PD{Any,Int}(1 => 1)
d = Dict{Any,Int}(1.0 => 1)
println("PersistentDict{Any,Int}(1 => 1) == Dict{Any,Int}(1.0 => 1): ", p == d)
println("Dict{Any,Int}(1.0 => 1) == PersistentDict{Any,Int}(1 => 1): ", d == p)
println("isequal both ways: ", isequal(p, d), " ", isequal(d, p))
r = try; Dict(1.0 => 1) == PD(1 => 1); catch e; typeof(e); end
println("Dict(1.0 => 1) == PersistentDict(1 => 1): ", r, "; reverse: ", PD(1 => 1) == Dict(1.0 => 1))
println("IdDict(1 => 1) == Dict(1.0 => 1): ", IdDict(1 => 1) == Dict(1.0 => 1), "; reverse: ", Dict(1.0 => 1) == IdDict(1 => 1))
if p == d && !(d == p)
    println("REPRODUCED dicts-persistentdict-eq-asymmetric")
end
