if !isdefined(Base, :StringView)
    println("StringView is unavailable on Julia ", VERSION)
else
    data = @view UInt8[0x61][1:1]
    s = Base.StringView(data)
    results = map((typemin, one, oneunit)) do f
        try
            f(typeof(s))
        catch e
            e
        end
    end
    println("backing type = ", typeof(data))
    println("typemin(typeof(s)) = ", results[1])
    println("one(typeof(s)) = ", results[2])
    println("oneunit(typeof(s)) = ", results[3])
    if all(e -> e isa MethodError, results)
        println("REPRODUCED stringscova-stringview-empty-constructor")
    end
end
