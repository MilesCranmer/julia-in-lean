r = Int8(1):Int8(3)
x = Int8(64)
println("collect(r) .* x = ", repr(collect(r) .* x))
s = r .* x
println("typeof(r .* x) = ", typeof(s))
try
    println("(r .* x)[2] = ", repr(s[2]))
catch e
    println("(r .* x)[2] throws ", sprint(showerror, e))
    e isa InexactError && collect(r) .* x == Int8[64, -128, -64] &&
        println("REPRODUCED ranges-broadcast-mul-elementwise")
end
