m = Memory{Int}(undef, 3)
n = UInt(2)

ref_result = Base.wrap(Array, memoryref(m), n)
memory_result = try
    Base.wrap(Array, m, n)
catch err
    err
end

println("MemoryRef result: ", size(ref_result))
println("Memory result: ", typeof(memory_result), ": ", sprint(showerror, memory_result))
println("Expected: both overloads return an Array with size (2,)")

if size(ref_result) == (2,) && memory_result isa MethodError
    println("REPRODUCED arraycov-wrap-memory-unsigned")
else
    println("NOT REPRODUCED arraycov-wrap-memory-unsigned")
end
