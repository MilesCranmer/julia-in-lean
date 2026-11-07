function reproduced()
    a = falses(1)
    shared = vec(reshape(a, 1, 1))
    resize!(shared, 65)
    fill!(shared, false)
    length(a) == 1 && a[1] == false || return false
    try
        map(!, a)
        return false
    catch err
        return err isa BoundsError
    end
end
let confirmed = reproduced()
    println(confirmed ? "REPRODUCED bitarray-map-not" : "NOT_REPRODUCED bitarray-map-not")
    confirmed
end
