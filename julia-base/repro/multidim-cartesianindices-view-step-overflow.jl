source = CartesianIndices((typemin(Int):(Int(1) << 62):0,))
selector = 1:2:3
region_selector = CartesianIndices((selector,))
expected = [source[1], source[3]]
@assert length(source) == 3 && length(selector) == 2
@assert expected == [CartesianIndex(typemin(Int)), CartesianIndex(0)]
viewed = view(source, selector)
selected = source[region_selector]
region_view = view(source, region_selector)
@assert isempty(viewed) && length(viewed) == 0
@assert isempty(selected) && length(selected) == 0
@assert isempty(region_view) && length(region_view) == 0
println("source length = ", length(source), "; selector = ", selector, "; expected = ", expected)
println("view length = ", length(viewed), "; region indexing length = ", length(selected), "; region view length = ", length(region_view))
for id in ("multidim-cartesianindices-view-step-overflow", "multidimensional-region-view", "multidimensional-region-selector-slicing")
    println("REPRODUCED ", id)
end
