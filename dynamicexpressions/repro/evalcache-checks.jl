# PR #219 (unary feature cache): observations behind the proven evalcache-*
# properties (no bug claimed). Each line prints `CHECK <name> true` when the
# observed behaviour matches the Lean model. Pass `turbo` as the first argument
# when LoopVectorization is available to also check the turbo path.
using DynamicExpressions
using DynamicExpressions: ArrayBuffer
using DynamicExpressions.EvaluateModule: UnaryFeatureCache, reset_index!
turbo = !isempty(ARGS) && ARGS[1] == "turbo"
turbo && @eval using LoopVectorization
check(name, ok) = println("CHECK ", name, " ", ok)

ops = OperatorEnum(1 => (cos, exp, inv), 2 => (+, *))
x1 = Node(Float64; feature=1)
x2 = Node(Float64; feature=2)
u(op, c) = Node(; op, children=(c,))
b(op, l, r) = Node(; op, children=(l, r))
X = [0.3 1.0 -2.0; 800.0 0.5 NaN]
same(a, b) = isequal(a, b)

# Returned arrays never alias the stored entry; mutating them does not change it.
cache = UnaryFeatureCache(Float64)
ctx = EvalContext(; unary_cache=cache)
y1, _ = eval_tree_array(u(1, x1), X, ops; eval_context=ctx)
y2, _ = eval_tree_array(u(1, x1), X, ops; eval_context=ctx)
entry = cache.entries[1, 1]
check("hit-fresh", !Base.mightalias(y1, entry) && !Base.mightalias(y2, entry) && y1 !== y2)
y2 .= 99.0
y3, _ = eval_tree_array(u(1, x1), X, ops; eval_context=ctx)
check("hit-after-caller-mutation", same(y3, cos.(X[1, :])))

# Buffers: a hit fills a slot; slot reuse after reset_index! leaves entries intact.
for buf in (ArrayBuffer(Vector{Float64}[], Ref(0)), ArrayBuffer(zeros(16, 3), Ref(0)))
    c = EvalContext(; buffer=buf, unary_cache=UnaryFeatureCache(Float64))
    ref = EvalContext(; buffer=copy(buf))
    ok = true
    for t in (u(1, x1), b(1, u(1, x1), x2), b(2, u(3, x1), u(1, x1)), u(1, x1))
        reset_index!(buf); reset_index!(ref.buffer)
        r = eval_tree_array(t, X, ops; eval_context=ref)
        reset_index!(buf)
        y, f = eval_tree_array(t, X, ops; eval_context=c)
        ok &= same(y, r[1]) && f == r[2] && buf.index[] == ref.buffer.index[]
        e = c.unary_cache.entries[1, 1]
        ok &= e !== nothing && !Base.mightalias(y, e)
    end
    check("buffer-$(buf.array isa Matrix ? "matrix" : "vector")", ok)
end

# copy gives a fresh, empty cache.
cc = copy(ctx)
check("copy-fresh", cc.unary_cache !== cache && cc.unary_cache.X === nothing &&
    size(cc.unary_cache.entries) == (0, 0))

# Above 16 MiB of entries nothing is stored.
big = randn(2, 600_000)
cb = EvalContext(; unary_cache=UnaryFeatureCache(Float64))
yb, _ = eval_tree_array(u(1, x1), big, ops; eval_context=cb)
check("limit-empty", isempty(cb.unary_cache.entries) && same(yb, cos.(big[1, :])))

# Stored entries: early_exit=true keeps only finite outputs of finite rows;
# early_exit=false stores the operator output as is.
for ee in (true, false)
    c = EvalContext(; early_exit=ee, unary_cache=UnaryFeatureCache(Float64))
    for t in (u(2, x2), u(1, x2), u(1, x1), u(2, x1))
        eval_tree_array(t, X, ops; eval_context=c)
    end
    E = c.unary_cache.entries
    stored = sort([(i, f) for i in 1:3, f in 1:2 if E[i, f] !== nothing])
    exact = all(same(E[i, f], ops.unaops[i].(X[f, :])) for (i, f) in stored)
    finite = all(all(isfinite, E[i, f]) && all(isfinite, X[f, :]) for (i, f) in stored)
    check("stored-early-exit-$ee", exact && (ee ? finite && stored == [(1, 1), (2, 1)] :
        stored == [(1, 1), (1, 2), (2, 1), (2, 2)]))
end

# bumper=true and fused unary chains never touch the cache.
cbump = EvalContext(; bumper=true, unary_cache=UnaryFeatureCache(Float64))
eval_tree_array(u(1, x1), X, ops; eval_context=cbump)
check("bumper-skips", cbump.unary_cache.X === nothing)
cf = EvalContext(; unary_cache=UnaryFeatureCache(Float64))
yf, ff = eval_tree_array(u(1, u(3, x1)), X, ops; eval_context=cf)
rf = eval_tree_array(u(1, u(3, x1)), X, ops)
check("fused-chain-no-entry", cf.unary_cache.X === nothing && same(yf, rf[1]) && ff == rf[2])

# Sharing one cache across use_fused and buffer settings (same early_exit) is safe.
let shared = UnaryFeatureCache(Float64), ok = true
    for t in (u(1, x1), b(1, u(1, x1), x1), u(2, u(1, x1)), b(2, u(1, x1), u(2, x1)))
        for fused in (true, false), rep in 1:2
            c = EvalContext(; use_fused=fused, unary_cache=shared)
            r = eval_tree_array(t, X, ops; eval_context=EvalContext(; use_fused=fused))
            y, f = eval_tree_array(t, X, ops; eval_context=c)
            ok &= same(y, r[1]) && f == r[2]
        end
    end
    check("shared-fused", ok)
end

# More than 15 unary operators (dispatch without @nif) uses the cache too.
many = OperatorEnum(1 => [[cos, exp, inv]; [(x -> x * i) for i in 1:14]], 2 => [+])
let cm = EvalContext(; unary_cache=UnaryFeatureCache(Float64)), okm = true
    for k in (1, 17, 1, 17)
        r = eval_tree_array(u(k, x1), X, many)
        y, f = eval_tree_array(u(k, x1), X, many; eval_context=cm)
        okm &= same(y, r[1]) && f == r[2]
    end
    check("many-unary", okm && cm.unary_cache.entries[17, 1] !== nothing)
end

if turbo
    Xf = [0.3 1.0 -2.0; 0.1 0.5 2.0]
    let ct = EvalContext(; turbo=true, unary_cache=UnaryFeatureCache(Float64)), okt = true
        for t in (u(1, x1), b(1, u(1, x1), x2), u(1, x1))
            r = eval_tree_array(t, Xf, ops; eval_context=EvalContext(; turbo=true))
            y, f = eval_tree_array(t, Xf, ops; eval_context=ct)
            okt &= same(y, r[1]) && f == r[2]
        end
        check("turbo-skips", okt && ct.unary_cache.X === nothing)
    end
end
