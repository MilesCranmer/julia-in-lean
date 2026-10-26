function main()
    growing_mask = Bool[true, false]
    growing = Base.LogicalIndex(growing_mask)
    growing_mask[2] = true
    growing_actual = collect(growing)

    shrinking_mask = Bool[true, true]
    shrinking = Base.LogicalIndex(shrinking_mask)
    shrinking_mask[2] = false

    println("growing mask = ", growing_mask)
    println("growing expected = [1, 2]")
    println("growing actual = ", growing_actual)
    println("shrinking mask = ", shrinking_mask)
    println("shrinking expected = [1]")

    threw = false
    try
        println("shrinking actual = ", collect(shrinking))
    catch e
        println("shrinking threw = ", typeof(e), ": ", sprint(showerror, e))
        threw = e isa TypeError
    end

    reproduced = growing_actual == [1] && threw
    println(reproduced ? "REPRODUCED multidimcov-logicalindex-mutable-mask" :
                         "NOT REPRODUCED multidimcov-logicalindex-mutable-mask")
end

main()
