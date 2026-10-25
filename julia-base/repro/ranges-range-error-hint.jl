try
    range(step=1, length=3)
catch e
    msg = sprint(showerror, e)
    println(msg)
    occursin("At least one of `length` or `stop` must be specified.", msg) &&
        println("REPRODUCED ranges-range-error-hint")
end
