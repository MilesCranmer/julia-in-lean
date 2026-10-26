# findmax!(rval, rind, A; init=false) ignores the values already in rval: rind is
# always refilled with zero indices, and a zero index makes findminmax! overwrite
# the stored value. maximum!(r, A; init=false) keeps and combines the values in r.
rv = fill(100.0, 1)
fm = findmax!(rv, zeros(Int, 1), [1.0, 2.0]; init=false)
mx = maximum!(fill(100.0, 1), [1.0, 2.0]; init=false)
fn = findmin!(fill(-100.0, 1), zeros(Int, 1), [1.0, 2.0]; init=false)
mn = minimum!(fill(-100.0, 1), [1.0, 2.0]; init=false)
println("findmax!(fill(100.0, 1), zeros(Int, 1), [1.0, 2.0]; init=false) = ", fm)
println("maximum!(fill(100.0, 1), [1.0, 2.0]; init=false) = ", mx)
println("findmin!(fill(-100.0, 1), zeros(Int, 1), [1.0, 2.0]; init=false) = ", fn)
println("minimum!(fill(-100.0, 1), [1.0, 2.0]; init=false) = ", mn)
if fm[1] == [2.0] && mx == [100.0] && fn[1] == [1.0] && mn == [-100.0]
    println("REPRODUCED reducecov-findmax-inplace-init")
end
