# reshape of a lazy range of length typemax(Int) throws although the dimensions multiply to its length
r = 1:typemax(Int)
x = try size(reshape(r, typemax(Int), 1)) catch e e end
y = try size(reshape(r, :, 1)) catch e e end
z = try size(reshape(Base.OneTo(typemax(Int)), 1, :)) catch e e end
println("reshape(1:typemax(Int), typemax(Int), 1) -> ", x)
println("reshape(1:typemax(Int), :, 1) -> ", y)
println("reshape(Base.OneTo(typemax(Int)), 1, :) -> ", z)
if x isa ArgumentError && y isa ArgumentError && z isa ArgumentError
    println("REPRODUCED reinterpretarrays-reshape-typemax-dim")
end
