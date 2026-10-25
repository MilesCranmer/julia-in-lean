# The generic AbstractDict ==, isequal and hash assume that iteration yields each
# key once. An ImmutableDict yields shadowed pairs too, so == and isequal become
# asymmetric and isequal dictionaries can hash differently.
const ID = Base.ImmutableDict
X = ID(:a => 1, :a => 1)          # setting :a twice to the same value
Y = ID(:a => 1, :b => 2)
println("X == Y: ", X == Y, "; Y == X: ", Y == X)
println("isequal(X, Y): ", isequal(X, Y), "; isequal(Y, X): ", isequal(Y, X))
println("haskey(X, :b) = ", haskey(X, :b), ", haskey(Y, :b) = ", haskey(Y, :b))
A = ID(:b => 2, :a => 1, :a => 1)
B = ID(:a => 1, :b => 2, :b => 2)
println("isequal(A, B): ", isequal(A, B), "; hash(A) == hash(B): ", hash(A) == hash(B))
println("length(Set{Any}([A, B])) = ", length(Set{Any}([A, B])))
println("allunique(X) = ", allunique(X), ", allunique(collect(X)) = ", allunique(collect(X)),
        "; allequal(X) = ", allequal(X), ", allequal(collect(X)) = ", allequal(collect(X)))
if X == Y && !(Y == X) && isequal(X, Y) && !isequal(Y, X) && isequal(A, B) && hash(A) != hash(B)
    println("REPRODUCED dicts-immutabledict-isequal")
end
