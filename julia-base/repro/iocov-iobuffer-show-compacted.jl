pb = PipeBuffer()
write(pb, "x"^100); read(pb, 90); write(pb, "y"^2000)
println(sprint(show, pb))
println("position(pb) = ", position(pb), ", bytesavailable(pb) = ", bytesavailable(pb))
m = match(r"ptr=(\d+)", sprint(show, pb))
if parse(Int, m.captures[1]) != position(pb) + 1
    println("REPRODUCED iocov-iobuffer-show-compacted")
end
