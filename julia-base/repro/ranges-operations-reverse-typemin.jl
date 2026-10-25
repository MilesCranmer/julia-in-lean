r = Int8(0):typemin(Int8):typemin(Int8)
s = reverse(r)
sortable = Int8(127):typemin(Int8):Int8(-1)
@assert length(sortable) == 2 && isempty(sort(sortable))
if length(r) == 2 && isempty(s) && reverse(collect(r)) == Int8[-128, 0]
    println("REPRODUCED ranges-operations-reverse-typemin")
else
    error("reverse typemin did not reproduce: $s")
end
