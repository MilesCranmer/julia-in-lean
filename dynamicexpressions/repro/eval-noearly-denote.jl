# early_exit=false is documented to disable early termination. For the
# non-constant tree `x1 + inv(inv(0.0))` (value x1), the constant subtree is
# still evaluated by the constant-tree shortcut, which stops at the invalid
# intermediate inv(0.0) = Inf: the flag is false and tree(X) returns NaN.
using DynamicExpressions
ops = OperatorEnum(1 => (inv, -), 2 => (+, /))
c = Node(; op=1, children=(Node(; op=1, children=(Node{Float64}(; val=0.0),)),))
t = Node(; op=1, children=(Node{Float64}(; feature=1), c))
X = reshape([1.0, 2.0], 1, 2)
ctx = EvalContext(; early_exit=false, use_fused=false)
_, ok = eval_tree_array(t, X, ops; eval_context=ctx)
y = t(X, ops; eval_context=ctx)
println("flag=", ok, " call=", y, " expected=", X[1, :] .+ inv(inv(0.0)))
(!ok && all(isnan, y)) && println("REPRODUCED eval-noearly-denote")
