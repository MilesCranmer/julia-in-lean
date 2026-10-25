A = [typemin(Int);;]
whole = maximum(abs, vec(A))
d = maximum(abs, A; dims=1)
println(repr(whole), " ", repr(d))
if whole == typemin(Int) && d == [0;;]
    println("REPRODUCED reduce-maxabs-dims-typemin")
end
