# PR #219 (unary feature cache). An entry stored by a context with
# early_exit=false may come from a non-finite feature row. A context with
# early_exit=true that shares the same UnaryFeatureCache then hits that entry and
# reports success, where uncached evaluation stops at the non-finite feature.
# Here inv(x1) with x1 = [Inf, 1.0]: cached ([0.0, 1.0], true), uncached flag false.
using DynamicExpressions
if !isdefined(DynamicExpressions.EvaluateModule, :UnaryFeatureCache)
    println("NOT APPLICABLE: this DynamicExpressions has no UnaryFeatureCache (PR #219)")
    exit()
end
using DynamicExpressions.EvaluateModule: UnaryFeatureCache
ops = OperatorEnum(1 => (inv,), 2 => (+,))
tree = Node(; op=1, children=(Node(Float64; feature=1),))
X = [Inf 1.0]
cache = UnaryFeatureCache(Float64)
loose = EvalContext(; early_exit=false, unary_cache=cache)
strict = EvalContext(; early_exit=true, unary_cache=cache)
eval_tree_array(tree, X, ops; eval_context=loose)
y, ok = eval_tree_array(tree, X, ops; eval_context=strict)
yref, okref = eval_tree_array(tree, X, ops; eval_context=EvalContext(; early_exit=true))
println("cached strict=", (y, ok), " uncached strict=", (yref, okref))
ok != okref && println("REPRODUCED evalcache-shared-early-exit")
