# view(V, :) of a view with an IdentityUnitRange index reads and writes the wrong parent elements
IUR = Base.IdentityUnitRange
M = reshape(collect(1:20), 4, 5)
V = view(M, IUR(2:3), 2)                 # V[2] == M[2,2] == 6, V[3] == M[3,2] == 7
W = view(V, :)                           # same axes as V
println("V[2], V[3] = ", V[2], ", ", V[3], ";  view(V, :)[2], [3] = ", W[2], ", ", W[3])
M2 = copy(M); fill!(view(view(M2, IUR(2:3), 2), :), 0)
println("fill!(view(view(M, IUR(2:3), 2), :), 0) zeroed ", Tuple.(findall(M2 .!= M)))
M3 = copy(M); copyto!(view(M3, IUR(2:3), 2), view(M3, IUR(2:3), 2))
println("copyto!(V, V) changed column 2 from ", M[:, 2], " to ", M3[:, 2])
X = view(M, IUR(3:4), 5)                 # last column
Y = view(X, :)
println("view(view(M, IUR(3:4), 5), :) reads parent linear index ", Y.offset1 + Y.stride1 * 4, " for index 4; length(M) = ", length(M))
if W[2] == M[3, 2] && Tuple.(findall(M2 .!= M)) == [(3, 2), (4, 2)] && M3[:, 2] != M[:, 2] && Y.offset1 + Y.stride1 * 4 > length(M)
    println("REPRODUCED reinterpretarrays-nested-slice-offset")
end
