r = Int8(-128):Int8(127):Int8(126)
s = Int8(5):Int8(4)
if isempty(s) && collect(intersect(r,s)) == Int8[-128,-1]
    println("REPRODUCED ranges-operations-intersect-empty")
else
    error("intersection with an empty range did not reproduce")
end
