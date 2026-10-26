# sizehint!(B::BitVector, sz::Integer) calls num_bit_chunks(sz), which only has
# an Int method (base/bitarray.jl:120, 798-801), so any other Integer type
# throws MethodError; sizehint!(::Vector{Bool}, ::UInt) works.
v = fill(false, 3)
sizehint!(v, UInt(10))
println("sizehint!(fill(false, 3), UInt(10)) = ", v)
r = try
    sizehint!(falses(3), UInt(10))
catch e
    e
end
println("sizehint!(falses(3), UInt(10)) = ", typeof(r))
r2 = try
    sizehint!(falses(3), Int32(10))
catch e
    e
end
println("sizehint!(falses(3), Int32(10)) = ", typeof(r2))
if r isa MethodError && r2 isa MethodError
    println("REPRODUCED bitsetscov-sizehint-bitvector-integer")
end
