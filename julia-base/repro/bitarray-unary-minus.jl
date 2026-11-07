function reproduced()
    a = falses(1)
    shared = vec(reshape(a, 1, 1))
    resize!(shared, 65)
    fill!(shared, false)
    shared[65] = true
    length(a) == 1 && a[1] == false || return false
    try
        -a
        return false
    catch err
        return err isa BoundsError
    end
end
let confirmed = reproduced()
    println(confirmed ? "REPRODUCED bitarray-unary-minus" : "NOT_REPRODUCED bitarray-unary-minus")
    confirmed
end
