# A writable IOBuffer over a view throws MethodError when it has to grow
io = IOBuffer(view(zeros(UInt8, 4), 1:4); write=true)
r = try write(io, "hello") catch e; e end
println("write(io, \"hello\") = ", typeof(r) <: Exception ? sprint(showerror, r)[1:60] : r)
io2 = IOBuffer(view(zeros(UInt8, 8), 1:8); write=true)
write(io2, "hi"); take!(io2)
r2 = try write(io2, "x") catch e; e end
println("write after take! = ", typeof(r2))
r isa MethodError && println("REPRODUCED iobuffers-view-grow")
