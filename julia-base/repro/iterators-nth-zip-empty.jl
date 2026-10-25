# nth(zip(), n) returns () for n <= 0 instead of throwing BoundsError
r0 = try Iterators.nth(zip(), 0) catch e; e end
rm = try Iterators.nth(zip(), -3) catch e; e end
println("nth(zip(), 0) = ", repr(r0), ", nth(zip(), -3) = ", repr(rm))
println("nth(zip([1]), 0) throws: ", try Iterators.nth(zip([1]), 0); false catch e; e isa BoundsError end)
r0 === () && rm === () && println("REPRODUCED iterators-nth-zip-empty")
