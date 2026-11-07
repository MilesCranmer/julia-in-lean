function reproduce()
    d = Base.ImmutableDict(:a => 1)
    filter_failed = try
        filter(_ -> true, d)
        false
    catch e
        e isa MethodError
    end
    copy_failed = try
        copy(d)
        false
    catch e
        e isa MethodError
    end
    filter_failed && copy_failed
end
ok = try reproduce() catch; false end
println(ok ? "REPRODUCED dictscov-immutable-filter-copy" : "NOT_REPRODUCED dictscov-immutable-filter-copy")
