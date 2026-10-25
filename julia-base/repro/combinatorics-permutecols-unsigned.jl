A = [1 3 5; 2 4 6]
p = UInt[3, 1, 2]

q = copy(p)
cols = copy(A)
Base.permutecols!(cols, q)
println("permutecols! result:    ", repr(cols))
println("permutecols! indices:   ", repr(q))
println("expected columns:       ", repr(A[:, p]))

q = copy(p)
invcols = copy(A)
Base.invpermutecols!(invcols, q)
println("invpermutecols! result: ", repr(invcols))
println("invpermutecols! indices:", repr(q))
println("expected inverse:       ", repr(A[:, invperm(p)]))

if cols != A[:, p] && invcols != A[:, invperm(p)] && q != p
    println("REPRODUCED combinatorics-permutecols-unsigned")
end
