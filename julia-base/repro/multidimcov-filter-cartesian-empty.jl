# filter(f, a) on an empty IndexCartesian array throws TypeError when the inferred return
# type of f is not Bool, because map(f, a) of an empty array has the inferred element type.
outcome(f) = try (:ok, f()) catch e; (:err, e) end
A = Any[1 2 3; 4 5 6; 7 8 9]
e = view(A, 1:0, 1:2)                 # empty, IndexCartesian
println("IndexStyle = ", IndexStyle(e), ", isempty = ", isempty(e))
r_cart = outcome(() -> filter(x -> x == 1, e))
println("filter on empty cartesian view: ", r_cart[1] == :ok ? repr(r_cart[2]) : typeof(r_cart[2]))
r_lin = outcome(() -> filter(x -> x == 1, view(Any[1, 2], 1:0)))
println("filter on empty linear view: ", r_lin[1] == :ok ? repr(r_lin[2]) : typeof(r_lin[2]))
r_full = outcome(() -> filter(x -> x == 1, view(A, 1:2, 1:2)))
println("filter on nonempty cartesian view: ", r_full[1] == :ok ? repr(r_full[2]) : typeof(r_full[2]))
reproduced = r_cart[1] == :err && r_cart[2] isa TypeError && r_lin[1] == :ok && r_full[1] == :ok
println(reproduced ? "REPRODUCED multidimcov-filter-cartesian-empty" : "NOT REPRODUCED")
