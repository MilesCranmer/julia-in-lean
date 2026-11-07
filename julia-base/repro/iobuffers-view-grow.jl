# A writable IOBuffer over a view throws MethodError when it has to grow
io = IOBuffer(view(zeros(UInt8, 4), 1:4); write=true)
r = try write(io, "hello") catch e; e end
println("write(io, \"hello\") = ", typeof(r) <: Exception ? sprint(showerror, r)[1:60] : r)
io2 = IOBuffer(view(zeros(UInt8, 8), 1:8); write=true)
write(io2, "hi"); take!(io2)
r2 = try write(io2, "x") catch e; e end
println("write after take! = ", typeof(r2))
seekable = IOBuffer(view(zeros(UInt8, 4), 1:4); write=true, maxsize=8)
seekable_result = try write(seekable, "hello") catch e; e end
pipe = PipeBuffer(view(zeros(UInt8, 4), 1:4); maxsize=8)
pipe_result = try write(pipe, "hello") catch e; e end
roundtrip = IOBuffer(view(zeros(UInt8, 4), 1:4);
    read=true, write=true, truncate=true, maxsize=8)
roundtrip_result = try
    write(roundtrip, "hello")
    seekstart(roundtrip)
    read(roundtrip)
catch e
    e
end
truncated = IOBuffer(view(zeros(UInt8, 4), 1:4); write=true, maxsize=8)
truncate_result = try truncate(truncated, 5) catch e; e end
println("bounded seekable, pipe, roundtrip, truncate = ",
    map(typeof, (seekable_result, pipe_result, roundtrip_result, truncate_result)))
all(x -> x isa MethodError, (r, r2, seekable_result, pipe_result,
    roundtrip_result, truncate_result)) && println("REPRODUCED iobuffers-view-grow")
