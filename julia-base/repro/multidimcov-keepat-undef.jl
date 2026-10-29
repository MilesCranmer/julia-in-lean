# keepat!(a, inds) reads every kept element, so a kept #undef element throws
# UndefRefError, while deleteat! of the complement keeps the #undef slot.
function mk()
    a = Vector{String}(undef, 3)
    a[1] = "x"
    a[3] = "z"
    a
end

function run(label, f)
    a = mk()
    try
        f(a)
        println(label, ": ok, assigned = ", [isassigned(a, i) for i in eachindex(a)],
                ", values = ", [isassigned(a, i) ? a[i] : "#undef" for i in eachindex(a)])
        return :ok
    catch err
        println(label, ": ", typeof(err))
        return err
    end
end

r_del = run("deleteat!(a, [3])", a -> deleteat!(a, [3]))
r_keep = run("keepat!(a, [1, 2])", a -> keepat!(a, [1, 2]))
r_keep_range = run("keepat!(a, 1:2)", a -> keepat!(a, 1:2))
r_mask = run("keepat!(a, [true, true, false])", a -> keepat!(a, [true, true, false]))
r_mask_shift = run("keepat!(a, [false, true, true])", a -> keepat!(a, [false, true, true]))
r_del_shift = run("deleteat!(a, [1])", a -> deleteat!(a, [1]))

reproduced = r_del === :ok && r_keep isa UndefRefError && r_mask === :ok
println(reproduced ? "REPRODUCED multidimcov-keepat-undef" : "NOT REPRODUCED")
