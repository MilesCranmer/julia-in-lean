io = IOBuffer()
write(io, "abc")
v = take!(io)              # take! result: String(v) may reuse its memory
b = reshape(v, 1, 3)       # a second array sharing v's data
s = String(v)
h = hash(s)
b[1] = UInt8('A')          # write through the other array
println("s = ", repr(s), ", hash unchanged: ", hash(s) == h)

io = IOBuffer()
write(io, "abc")
v = take!(io)
w = vec(reshape(v, 1, 3))  # a second Vector sharing v's data
s1 = String(v)
resize!(w, 1)
s2 = String(w)             # creating another String truncates s1
println("s1 = ", repr(s1), ", s1 === s2: ", s1 === s2)
(s != "abc" || s1 != "abc") && println("REPRODUCED transcode-string-vector-alias")
