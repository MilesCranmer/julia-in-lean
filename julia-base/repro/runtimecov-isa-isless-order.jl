const ISA = Base.BinaryPlatforms.CPUID.ISA
x = ISA(Set{UInt32}([1]))
y = ISA(Set{UInt32}([3]))
z = ISA(Set{UInt32}([1, 2]))
println("isless(x, y) = ", isless(x, y), ", isless(y, x) = ", isless(y, x), ", isequal(x, y) = ", isequal(x, y))
println("isless(y, z) = ", isless(y, z), ", isless(z, y) = ", isless(z, y), ", isequal(y, z) = ", isequal(y, z))
println("isless(x, z) = ", isless(x, z))
x2 = ISA(Set{UInt32}([1]))
println("x <= x2 = ", x <= x2, ", x2 <= x = ", x2 <= x, ", isequal(x, x2) = ", isequal(x, x2))
# isless must be a total order together with isequal: exactly one of isless(a, b),
# isless(b, a), isequal(a, b) holds, and incomparability is transitive.
if !isless(x, y) && !isless(y, x) && !isequal(x, y) && !isless(y, z) && !isless(z, y) && isless(x, z)
    println("REPRODUCED runtimecov-isa-isless-order")
end
