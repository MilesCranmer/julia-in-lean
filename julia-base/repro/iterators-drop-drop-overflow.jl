function reproduce_iterators_drop_drop_overflow()
    try
        result = Iterators.drop(Iterators.drop([1, 2, 3], typemax(Int)), 1)
        values = collect(result)
        isempty(values) || error("unexpected values: $(repr(values))")
    catch err
        err isa ArgumentError || rethrow()
        println("REPRODUCED iterators-drop-drop-overflow")
    end
end

reproduce_iterators_drop_drop_overflow()
