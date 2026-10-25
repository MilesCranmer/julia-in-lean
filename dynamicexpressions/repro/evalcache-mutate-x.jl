# PR #219 (unary feature cache). The cache keys its entries by the identity
# (===) of X, so new contents behind the same identity return stale values:
# X mutated in place, or a view whose index vector was mutated (the new view is
# === to the old one). The EvalContext docstring forbids in-place mutation of
# the input matrix; the view case is not mentioned there.
using DynamicExpressions
if !isdefined(DynamicExpressions.EvaluateModule, :UnaryFeatureCache)
    println("NOT APPLICABLE: this DynamicExpressions has no UnaryFeatureCache (PR #219)")
    exit()
end
using DynamicExpressions.EvaluateModule: UnaryFeatureCache
ops = OperatorEnum(1 => (cos,), 2 => (+,))
tree = Node(; op=1, children=(Node(Float64; feature=1),))

X = [0.0 1.0]
ctx = EvalContext(; unary_cache=UnaryFeatureCache(Float64))
eval_tree_array(tree, X, ops; eval_context=ctx)
X[1, 1] = 2.0
y, ok = eval_tree_array(tree, X, ops; eval_context=ctx)
yref, okref = eval_tree_array(tree, X, ops)
println("in-place mutation: cached=", (y, ok), " uncached=", (yref, okref))

P = [0.0 1.0 2.0 3.0]
idx = [1, 2]
ctxv = EvalContext(; unary_cache=UnaryFeatureCache(Float64))
eval_tree_array(tree, view(P, :, idx), ops; eval_context=ctxv)
idx .= [3, 4]
yv, okv = eval_tree_array(tree, view(P, :, idx), ops; eval_context=ctxv)
yvref, okvref = eval_tree_array(tree, view(P, :, idx), ops)
println("view with mutated indices: cached=", (yv, okv), " uncached=", (yvref, okvref),
    " (fresh view === old view: ", view(P, :, idx) === view(P, :, idx), ")")

(y != yref && yv != yvref) && println("REPRODUCED evalcache-mutate-x")
