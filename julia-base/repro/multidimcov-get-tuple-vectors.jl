# get(A, I, default) accepts a tuple of AbstractVector{Int} (RangeVecIntList), but
# get! calls indcopy(size(A), I), which has methods only for a Vector of index vectors
# and a tuple of ranges or Ints. A tuple of index vectors throws MethodError.
outcome(f) = try (:ok, f()) catch e; (:err, e) end
A = reshape(collect(1.0:9.0), 3, 3)
r_ranges = outcome(() -> get(A, (1:2, 2:4), 0.0))
r_vecvec = outcome(() -> get(A, [[1, 2], [2, 3, 4]], 0.0))
r_tuple = outcome(() -> get(A, ([1, 2], [2, 3, 4]), 0.0))
r_mixed = outcome(() -> get(A, (1:2, [2, 3, 4]), 0.0))
println("get(A, (1:2, 2:4), 0.0) = ", r_ranges)
println("get(A, [[1, 2], [2, 3, 4]], 0.0) = ", r_vecvec)
println("get(A, ([1, 2], [2, 3, 4]), 0.0) = ", r_tuple[1] == :err ? typeof(r_tuple[2]) : r_tuple)
println("get(A, (1:2, [2, 3, 4]), 0.0) = ", r_mixed[1] == :err ? typeof(r_mixed[2]) : r_mixed)
reproduced = r_ranges[1] == :ok && r_vecvec[1] == :ok && r_tuple[1] == :err && r_tuple[2] isa MethodError &&
    r_mixed[1] == :err && r_mixed[2] isa MethodError
println(reproduced ? "REPRODUCED multidimcov-get-tuple-vectors" : "NOT REPRODUCED")
