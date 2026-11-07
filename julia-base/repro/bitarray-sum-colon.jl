let id = "bitarray-sum-colon"
    ok = try
        original = falses(1)
        alias = reshape(original, 1, 1)
        push!(original, true)
        size(alias) == (1, 1) && !alias[1] && sum(collect(alias)) == 0 && sum(alias) == 1
    catch
        false
    end
    let confirmed = ok
    println(confirmed ? "REPRODUCED $id" : "NOT_REPRODUCED $id")
    confirmed
end
end
