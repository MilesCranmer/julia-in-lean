r = Int8(0):typemin(Int8):typemin(Int8)
s = reverse(r)
sortable = Int8(127):typemin(Int8):Int8(-1)
@assert length(sortable) == 2 && isempty(sort(sortable))
if length(r) == 2 && isempty(s) && reverse(collect(r)) == Int8[-128, 0]
    println("REPRODUCED ranges-operations-reverse-typemin")
else
    error("reverse typemin did not reproduce: $s")
end

let region = CartesianIndices((0:typemin(Int):typemin(Int),))
    @assert length(region) == 2
    expected = [CartesianIndex(typemin(Int)), CartesianIndex(0)]
    @assert reverse(collect(region)) == expected
    for (id, result) in (("multidimensional-reverse-region-all", reverse(region)),
                         ("multidimensional-reverse-region-dimension", reverse(region; dims=1)),
                         ("multidimensional-reverse-region-single-tuple", reverse(region; dims=(1,))))
        @assert isempty(result) && length(result) == 0
        println(id, ": source length = 2; reverse length = ", length(result))
        println("REPRODUCED ", id)
    end
end
let region = CartesianIndices((0:typemin(Int):typemin(Int), 1:1))
    result = reverse(region; dims=(1, 2))
    @assert length(region) == 2 && isempty(result) && length(result) == 0
    println("multidimensional-reverse-region-dimensions: source length = 2; reverse length = ", length(result))
    println("REPRODUCED multidimensional-reverse-region-dimensions")
end
