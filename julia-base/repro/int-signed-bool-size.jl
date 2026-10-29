# signed(T) is documented as "the signed type of the same size", but signed(Bool) is Int.
S = signed(Bool)
println("signed(Bool) = ", S, ", sizeof(signed(Bool)) = ", sizeof(S), ", sizeof(Bool) = ", sizeof(Bool))
println("unsigned(Bool) = ", unsigned(Bool), ", sizeof(unsigned(Bool)) = ", sizeof(unsigned(Bool)))
println("signed(UInt8) = ", signed(UInt8), ", sizeof = ", sizeof(signed(UInt8)))
if S <: Signed && sizeof(S) != sizeof(Bool)
    println("REPRODUCED int-signed-bool-size")
else
    println("NOT REPRODUCED int-signed-bool-size")
end
