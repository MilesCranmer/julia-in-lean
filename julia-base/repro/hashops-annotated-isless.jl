using Base: AnnotatedString

a = AnnotatedString("x", [(1:1, :style, :red)])
b = AnnotatedString("x", [(1:1, :style, :blue)])

println("isequal(a, b) = ", isequal(a, b))
println("isless(a, b) = ", isless(a, b))
println("isless(b, a) = ", isless(b, a))
println("cmp(a, b) = ", cmp(a, b))

if !isequal(a, b) && !isless(a, b) && !isless(b, a) && cmp(a, b) == 0
    println("REPRODUCED hashops-annotated-isless")
else
    println("NOT REPRODUCED")
end
