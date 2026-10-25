res(f) = try
    f()
catch e
    sprint(showerror, e)
end
b1 = res(() -> reverse(falses(0, 7); dims=1))
b2 = res(() -> reverse(falses(0, 7); dims=2))
a1 = res(() -> reverse(zeros(Bool, 0, 7); dims=1))
a2 = res(() -> reverse(zeros(Bool, 0, 7); dims=2))
println(repr(b1), " | ", repr(b2))
println(summary(a1), " | ", summary(a2))
if b1 isa String && b2 isa String && occursin("step cannot be zero", b2) && size(a2) == (0, 7)
    println("REPRODUCED bitarrays-reverse-dims-empty")
end
