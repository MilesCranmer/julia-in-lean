# Nothing has zero-size elements; only two partition steps are inspected.
@assert Sys.WORD_SIZE == 64
L = (Int(1) << 62) + 5
n = (Int(1) << 62) + 3
xs = Vector{Nothing}(undef, L)
@assert sizeof(Nothing) == 0 && sizeof(xs) == 0 && length(xs) == L
@assert isassigned(xs, 1) && isassigned(xs, L)
@assert xs[1] === nothing && xs[L] === nothing
p = Iterators.partition(xs, n)
@assert length(p) == 2
first_step = iterate(p)
@assert first_step !== nothing
first_chunk, state = first_step
@assert length(first_chunk) == n && state == n + 1
@assert L - n == 2
second_step = iterate(p, state)
@assert second_step !== nothing
second_chunk, next_state = second_step
@assert length(second_chunk) == 0
@assert next_state == typemin(Int) + 7
println("REPRODUCED iterators-partition-vector")
