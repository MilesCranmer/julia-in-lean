function reproduce()
    a = Base.ImmutableDict(:a => 1, :a => 1)
    b = Dict(:a => 1, :b => 1)
    length(a) == length(b) == 2 &&
        (a == b) === true && (b == a) === false &&
        isequal(a, b) && !isequal(b, a)
end
ok = try reproduce() catch; false end
println(ok ? "REPRODUCED dicts-immutabledict-isequal" : "NOT_REPRODUCED dicts-immutabledict-isequal")
