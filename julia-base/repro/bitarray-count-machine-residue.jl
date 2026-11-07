let id = "bitarray-count-machine-residue"
    ok = try
        original = falses(1)
        alias = reshape(original, 1, 1)
        push!(original, true)
        expected = count(identity, collect(alias); init=UInt8(0))
        actual = count(identity, alias; init=UInt8(0))
        size(alias) == (1, 1) && !alias[1] && expected == UInt8(0) && actual == UInt8(1)
    catch
        false
    end
    let confirmed = ok
    println(confirmed ? "REPRODUCED $id" : "NOT_REPRODUCED $id")
    confirmed
end
end
