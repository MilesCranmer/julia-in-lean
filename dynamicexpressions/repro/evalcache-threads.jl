# PR #219 (unary feature cache). The cache has no lock. Threads that share one
# EvalContext but evaluate on different matrices race on cache.X/cache.entries:
# one thread passes the identity check for its X, another resets the entries for
# its own X and stores a value, and the first thread then reads that value.
# Started with one thread, the script reruns itself with 8.
if Threads.nthreads() == 1
    run(`$(Base.julia_cmd()) --threads=8 --project=$(Base.active_project()) $(PROGRAM_FILE)`)
    exit()
end
using DynamicExpressions
if !isdefined(DynamicExpressions.EvaluateModule, :UnaryFeatureCache)
    println("NOT APPLICABLE: this DynamicExpressions has no UnaryFeatureCache (PR #219)")
    exit()
end
using DynamicExpressions.EvaluateModule: UnaryFeatureCache
println("threads=", Threads.nthreads())
ops = OperatorEnum(1 => (cos,), 2 => (+,))
tree = Node(; op=1, children=(Node(Float64; feature=1),))
X1 = fill(0.0, 1, 64)
X2 = fill(1.0, 1, 64)
refs = (eval_tree_array(tree, X1, ops)[1], eval_tree_array(tree, X2, ops)[1])

function count_wrong(inputs, refs, n)
    ctx = EvalContext(; unary_cache=UnaryFeatureCache(Float64))
    wrong = Threads.Atomic{Int}(0)
    errors = Threads.Atomic{Int}(0)
    Threads.@threads for i in 1:n
        k = mod1(i, length(inputs))
        try
            y, ok = eval_tree_array(tree, inputs[k], ops; eval_context=ctx)
            (ok && y == refs[k]) || Threads.atomic_add!(wrong, 1)
        catch
            Threads.atomic_add!(errors, 1)
        end
    end
    return wrong[], errors[]
end

wrong, errs = count_wrong((X1, X2), refs, 400_000)
println("two matrices, one shared context: wrong=", wrong, " errors=", errs, " of 400000")
wrong_same, errs_same = count_wrong((X1,), refs[1:1], 400_000)
println("one matrix, one shared context: wrong=", wrong_same, " errors=", errs_same, " of 400000")
(wrong > 0) && println("REPRODUCED evalcache-threads")
