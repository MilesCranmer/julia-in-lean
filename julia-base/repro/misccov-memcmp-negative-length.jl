# Base.memcpy, memmove and memset pass `n` to ccall as Csize_t, so a negative n throws
# InexactError; Base.memcmp (base/cmem.jl:54-57) passes `n % Csize_t`, so a negative n
# becomes a length near 2^64 and memcmp reads past both buffers until they differ.
a = UInt8[1, 2, 3]; b = UInt8[9, 2, 3]
r1 = try GC.@preserve a b Base.memcpy(pointer(a), pointer(b), -1) catch e; e end
r2 = try GC.@preserve a b Base.memmove(pointer(a), pointer(b), -1) catch e; e end
r3 = try GC.@preserve a b Base.memset(pointer(a), 0, -1) catch e; e end
r4 = try GC.@preserve a b Base.memcmp(pointer(a), pointer(b), -1) catch e; e end
for (name, r) in (("memcpy", r1), ("memmove", r2), ("memset", r3), ("memcmp", r4))
    println(name, "(..., -1) => ", r isa Exception ? sprint(showerror, r) : repr(r))
end
if r1 isa InexactError && r2 isa InexactError && r3 isa InexactError && !(r4 isa Exception)
    println("REPRODUCED misccov-memcmp-negative-length")
end
