# iterate(r, state) for a StepRangeLen whose length is typemax(Int): the state of the last
# element is typemax(Int), and iterate(r, typemax(Int)) should return nothing.
r = StepRangeLen(0, 1, typemax(Int))
x = iterate(r, typemax(Int))
println("length(r) = ", length(r), ", iterate(r, typemax(Int)) = ", repr(x))
x === nothing && error("iterate returned nothing; not reproduced")
println("REPRODUCED range-srl-iterate-typemax")
