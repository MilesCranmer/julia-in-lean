function reproduce()
    a = [1]
    b = [1]
    p = Base.PersistentDict(a => 1)
    d = Dict(b => 1)
    a !== b && isequal(a, b) && length(p) == length(d) == 1 &&
        (p == d) === true && (d == p) === false
end
ok = try reproduce() catch; false end
println(ok ? "REPRODUCED dicts-persistentdict-eq-asymmetric" : "NOT_REPRODUCED dicts-persistentdict-eq-asymmetric")
