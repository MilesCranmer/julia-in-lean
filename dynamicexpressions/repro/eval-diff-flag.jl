# differentiable_eval_tree_array never checks leaves: a NaN constant (or a NaN
# feature) returns flag true with NaN output.
using DynamicExpressions
ops = OperatorEnum(1 => (inv, -), 2 => (+, /))
y, ok = differentiable_eval_tree_array(Node{Float64}(; val=NaN), reshape([0.0], 1, 1), ops)
println("y=", y, " flag=", ok)
(ok && any(isnan, y)) && println("REPRODUCED eval-diff-flag")
