# `throw_promote_shape_mismatch` normalizes offset axes with
# `firstindex(x):lastindex(x)`, which describes their storage indices rather
# than their axis values. Two different axes can therefore print identically.
try
    promote_shape((Base.OneTo(3),), (2:4,))
    println("promote_shape unexpectedly returned")
catch err
    msg = sprint(showerror, err)
    println(msg)
    if msg == "DimensionMismatch: a has axes (1:3,), b has axes (1:3,), mismatch at dim 1"
        println("REPRODUCED reducecov-promote-shape-message")
    end
end
