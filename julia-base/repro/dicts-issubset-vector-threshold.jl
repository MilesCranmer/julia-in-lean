# issubset(a, b) is documented to use `in`, which compares with `==` for vectors,
# but for length(b) > 70 it converts b to a Set and compares with isequal.
b_short = [-0.0; ones(69)]
b_long = [-0.0; ones(70)]
r_short = issubset([0.0], b_short)
r_long = issubset([0.0], b_long)
in_long = all(x -> x in b_long, [0.0])
println("length(b) = 70: issubset([0.0], b) = ", r_short)
println("length(b) = 71: issubset([0.0], b) = ", r_long, "; all(x -> x in b, [0.0]) = ", in_long)
r_nan = issubset([NaN], [NaN; ones(70)])
println("issubset([NaN], [NaN; ones(70)]) = ", r_nan, "; NaN in [NaN; ones(70)] = ", NaN in [NaN; ones(70)])
if r_short && !r_long && in_long
    println("REPRODUCED dicts-issubset-vector-threshold")
end
