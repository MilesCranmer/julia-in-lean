# cmp(-0.0, 0//1) must follow the isless total order, which puts -0.0 before 0//1
x = -0.0
y = 0//1
println("isless(-0.0, 0//1) = ", isless(x, y), ", isless(0//1, -0.0) = ", isless(y, x))
println("cmp(-0.0, 0//1) = ", cmp(x, y), ", cmp(0//1, -0.0) = ", cmp(y, x))
println("cmp(-0.0, 0) = ", cmp(x, 0), ", cmp(-0.0, 0.0) = ", cmp(x, 0.0))
if isless(x, y) && cmp(x, y) == 0 && cmp(y, x) == 0
    println("REPRODUCED promotion-cmp-rational-signed-zero")
end
