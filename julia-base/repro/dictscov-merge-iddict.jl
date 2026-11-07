function reproduce()
    d = IdDict{Any,Int}(true => 1, 1 => 1)
    m = merge(d)
    length(d) == 2 && true !== 1 && isequal(true, 1) && length(m) == 1
end
ok = try reproduce() catch; false end
println(ok ? "REPRODUCED dictscov-merge-iddict" : "NOT_REPRODUCED dictscov-merge-iddict")
