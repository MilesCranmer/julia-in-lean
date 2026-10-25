r = StepRange(Int64(-2), UInt64(1), Int64(-1))
@assert length(r) == 2
@assert first(r) == -2 && last(r) == -1
@assert iterate(r) == (-2, -2)
function throws_inexact(f)
    try
        f()
        false
    catch e
        e isa InexactError || rethrow()
        true
    end
end
if throws_inexact(() -> r[length(r)]) &&
   throws_inexact(() -> iterate(r, first(r))) &&
   throws_inexact(() -> collect(r))
    println("REPRODUCED ranges-ordinal-unsigned-step-last")
end
