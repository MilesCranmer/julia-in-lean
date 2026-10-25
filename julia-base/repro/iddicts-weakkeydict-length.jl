# WeakKeyDict setindex! (base/weakdict.jl:90-107) reuses the existing WeakRef
# when an isequal key is already present: it points the WeakRef at the new key
# object (k.value = key) but registers no finalizer on it. When that new key
# is collected, nothing marks the dictionary dirty, so the dead entry is never
# swept: length counts it, iteration skips it, and re-inserting adds a second
# entry.
wk = WeakKeyDict{Any,Any}()
k1 = [1]
wk[k1] = :first
function replace_key!(wk)
    k2 = [1]                 # isequal(k1, k2), k1 !== k2
    wk[k2] = :second
    nothing
end
replace_key!(wk)
GC.gc(); GC.gc(); GC.gc()
n1 = length(wk); p1 = collect(wk)
println("after the second key was collected: length = ", n1, ", collect = ", p1,
        ", haskey(wk, k1) = ", haskey(wk, k1))
wk[k1] = :third
n2 = length(wk); p2 = collect(wk)
println("after wk[k1] = :third: length = ", n2, ", collect = ", p2)
if n1 == 1 && isempty(p1) && n2 == 2 && length(p2) == 1
    println("REPRODUCED iddicts-weakkeydict-length")
end
