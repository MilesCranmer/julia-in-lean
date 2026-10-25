a = searchsortedfirst(1:0, 0; rev=true)
b = searchsorted(5:4, 5; rev=true)
c = searchsorted(1:-1:2, 2)
println(a, " ", b, " ", c)
println(searchsortedfirst(Int[], 0; rev=true), " ", searchsorted(Int[], 5; rev=true), " ", searchsorted(Int[], 2))
if a != 1 && !isempty(b) && first(c) != 1
    println("REPRODUCED sort-range-search-empty")
end
