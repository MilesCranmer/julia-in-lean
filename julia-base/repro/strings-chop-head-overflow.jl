println("chop(\"ab\", head=3, tail=0) = ", repr(chop("ab", head=3, tail=0)))
r = try
    repr(chop("ab", head=typemax(Int), tail=0))
catch e
    e
end
println("chop(\"ab\", head=typemax(Int), tail=0) = ", r isa Exception ? sprint(showerror, r) : r)
r isa BoundsError && println("REPRODUCED strings-chop-head-overflow")
