function check_counterexample()
    backing = falses(1)
    source = reshape(backing, 1, 1)
    resize!(backing, 65)
    fill!(backing, false)
    size(source) == (1, 1) || return false
    source[1] == false || return false
    try
        map(|, source, source)
        return false
    catch error
        return error isa BoundsError
    end
end

reproduced = try
    check_counterexample()
catch
    false
end
let confirmed = reproduced
    println(confirmed ? "REPRODUCED bitarray-map-binary" : "NOT_REPRODUCED bitarray-map-binary")
    confirmed
end
