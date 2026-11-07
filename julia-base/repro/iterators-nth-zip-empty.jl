function reproduce_iterators_nth_zip_empty()
    result = try
        Iterators.nth(zip(), 0)
    catch err
        err isa BoundsError && return
        rethrow()
    end
    result === () || error("unexpected result: $(repr(result))")
    println("REPRODUCED iterators-nth-zip-empty")
end

reproduce_iterators_nth_zip_empty()
