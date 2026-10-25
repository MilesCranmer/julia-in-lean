# PR #219 (unary feature cache). The cache keys its entries by the identity
# (===) of the operators. An operator whose behaviour depends on mutable state
# (here a closure over a Ref) keeps its identity when that state changes, so
# the cache returns values computed with the old state.
using DynamicExpressions
if !isdefined(DynamicExpressions.EvaluateModule, :UnaryFeatureCache)
    println("NOT APPLICABLE: this DynamicExpressions has no UnaryFeatureCache (PR #219)")
    exit()
end
using DynamicExpressions.EvaluateModule: UnaryFeatureCache
scale = Ref(2.0)
scaled = x -> scale[] * x
ops = OperatorEnum(1 => (scaled,), 2 => (+,))
tree = Node(; op=1, children=(Node(Float64; feature=1),))
X = [1.0 2.0]
ctx = EvalContext(; unary_cache=UnaryFeatureCache(Float64))
eval_tree_array(tree, X, ops; eval_context=ctx)
scale[] = 3.0
y, ok = eval_tree_array(tree, X, ops; eval_context=ctx)
yref, okref = eval_tree_array(tree, X, ops)
println("cached=", (y, ok), " uncached=", (yref, okref))
y != yref && println("REPRODUCED evalcache-mutate-op")
