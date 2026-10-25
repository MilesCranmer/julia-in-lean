# PipeBuffer documents maxsize::Integer but only accepts Int
r = try PipeBuffer(UInt8[]; maxsize=UInt(10)) catch e; e end
r2 = try PipeBuffer(UInt(10)) catch e; e end
println("PipeBuffer(UInt8[]; maxsize=UInt(10)) = ", typeof(r), "; PipeBuffer(UInt(10)) = ", typeof(r2))
r isa TypeError && println("REPRODUCED iobuffers-pipebuffer-maxsize-type")
