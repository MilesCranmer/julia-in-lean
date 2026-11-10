# Lead compiler-cacheresult-va-tail-miss: a const-prop result whose argument types end in a
# `Vararg` is never found again by `constprop_cache_lookup`, so every call site with the same
# constant arguments runs constant propagation again within one inference session.
#
# `const_prop_call` (Compiler/src/abstractinterpretation.jl:1517-1522) marks position i as
# overridden when `argtypes[i] !== argtype_by_index(cache_argtypes, i)`. For a trailing
# `Vararg{T}` that comparison is against `unwrapva(cache_va)`, so the tail is always marked
# overridden. The lookup (Compiler/src/inferenceresult.jl:245-248) then compares the query's
# tail with `is_argtype_match(..., overridden_by_const = true)`; a `Vararg` is not forwardable,
# so the match is always false.
#
# Prints `REPRODUCED compiler-cacheresult-va-tail-miss` when the local cache holds more than one
# const-prop entry with the same argument types for the varargs callee, while the fixed-arity
# control holds one.
const CC = Base.Compiler
const R = Ref(0)
g(a, b...) = (R[] = 1; a == 1 ? length(b) : "s")
h(a, b, c) = (R[] = 1; a == 1 ? b + c : "s")
callg(v::Vector{Int}) = (g(1, v...), g(1, v...), g(1, v...))
callh(v::Int) = (h(1, v, v), h(1, v, v), h(1, v, v))

function constprop_entries(caller, A, f)
    interp = CC.NativeInterpreter()
    CC.typeinf_frame(interp, Base.method_instance(caller, A), false)
    cache = interp.inf_cache
    rs = hasproperty(cache, :results) ? cache.results : cache
    rs = Any[x isa CC.InferenceResult ? x : x.result for x in rs]
    m = only(methods(f))
    return [r.argtypes for r in rs if r.linfo.def === m && r.overridden_by_const !== nothing]
end

println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
eg = constprop_entries(callg, (Vector{Int},), g)
eh = constprop_entries(callh, (Int,), h)
println("varargs callee: ", length(eg), " const-prop entries: ", eg)
println("fixed-arity callee: ", length(eh), " const-prop entries: ", eh)
if length(eg) > 1 && allequal(eg) && length(eh) == 1
    println("REPRODUCED compiler-cacheresult-va-tail-miss")
else
    println("NOT REPRODUCED compiler-cacheresult-va-tail-miss")
end
