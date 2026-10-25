b = try
    circshift!(falses(0), 1)
catch e
    e
end
v = circshift!(Bool[], 1)
println(repr(b), " ", repr(v))
if b isa DivideError && v == Bool[]
    println("REPRODUCED bitarrays-circshift-empty")
end
