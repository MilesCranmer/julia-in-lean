s = "X\n" * "a"^8191                       # 8193 bytes, two lines
rev = collect(Iterators.reverse(eachline(IOBuffer(s))))
fwd = readlines(IOBuffer(s))
println("readlines:            ", [(sizeof(l), first(l, 3)) for l in fwd])
println("reverse(eachline(io)): ", [(sizeof(l), first(l, 3)) for l in rev])
t = "X" * "a"^4094 * "\n" * "a"^4096 * "\n" * "z"
rt = collect(Iterators.reverse(eachline(IOBuffer(t))))
println("second input, lengths: readlines ", sizeof.(readlines(IOBuffer(t))), ", reversed eachline ", sizeof.(rt))
if rev != reverse(fwd)
    println("REPRODUCED iocov-eachline-reverse-first-line")
end
