function check_counterexample()
    backing = falses(1)
    source = reshape(backing, 1, 1)
    resize!(backing, 65)
    fill!(backing, false)
    size(source) == (1, 1) || return false
    source[1] == false || return false
    destination = falses(65)
    returned = map!(!, destination, source)
    return returned === destination && all(destination[i] for i in 1:65)
end

reproduced = try
    check_counterexample()
catch
    false
end
let confirmed = reproduced
    println(confirmed ? "REPRODUCED bitarray-map-not-bang" : "NOT_REPRODUCED bitarray-map-not-bang")
    confirmed
end
