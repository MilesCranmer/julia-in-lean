import DynExpr.Registry.Types
import DynExpr.EvalCache.Race
import DynExpr.EvalCache.Refute

/-! Slice root: the unary feature cache of PR #219 (branch
`perf/unary-feature-cache`, head 5e2f3b8c), not on master. -/

namespace DynExpr.EvalCache
open DynExpr.Registry

private def pr : String := "Models PR #219 (perf/unary-feature-cache, head 5e2f3b8c), not master."

private def entry (id : String) (fns : List String) (statement pre : String)
    (prop thm : Lean.Name) (status : Status := .proven) (notes : String := "") : Entry :=
  ⟨id, "src/Evaluate.jl", fns, statement, pre, status, prop, some thm,
    if notes.isEmpty then pr else pr ++ " " ++ notes⟩

def entries : List Entry := [
  entry "evalcache-single"
    ["eval_tree_array", "EvalContext", "UnaryFeatureCache", "cached_deg1_eval", "dispatch_deg1_eval"]
    "With a UnaryFeatureCache that is fresh or consistent with the current X and operators, eval_tree_array returns exactly the uncached result (value array, flag, or the same exception) for every early_exit, use_fused, bumper, turbo and buffer setting."
    "Well-formed tree (operator indices in range, features in 1..size(X,1)); sizeof(T) > 0; operators that do not throw (modelled as total functions); cache fresh, or its recorded identities are other than this call's, or its entries match X and operators (CacheOK)."
    ``evalCacheSingle ``evalCacheSingle_proof .proven
    "Covers 16 MiB skip, NaN/Inf and both dispatch branches (<=15 and >15 unary operators); proof is a simulation of evalT by the cached evaluator (Sim.lean).",
  entry "evalcache-node"
    ["_eval_tree_array", "cached_deg1_eval", "ArrayBuffer", "get_array"]
    "Inside the evaluator every cached step returns the uncached ResultOk, including the array identity (fresh, or the same ArrayBuffer slot), and leaves the buffer index in the same state: a hit takes exactly one slot and copies the stored vector into it, like the uncached feature copy."
    "As evalcache-single."
    ``evalCacheNode ``evalCacheNode_proof .proven
    "Aliasing: stored entries are copy(output.x) and hits copyto! into a fresh array or slot, so the returned array never shares storage with an entry (the model's arrays are values; Julia check repro/evalcache-checks.jl: hit-fresh, hit-after-caller-mutation, buffer-vector, buffer-matrix). The slot discipline then follows from eval-alias-slots.",
  entry "evalcache-stored"
    ["cached_deg1_eval", "UnaryFeatureCache"]
    "After a call the cache is still consistent with the input: every stored entry (i, f) is unary operator i applied to X[f, :]; under early_exit the row and the entry are finite; without early_exit the entry is the operator output as is (NaN/Inf included). The cache is either unchanged or carries this call's identities."
    "As evalcache-single."
    ``evalCacheStored ``evalCacheStored_proof,
  entry "evalcache-store-rule"
    ["cached_deg1_eval", "UnaryFeatureCache"]
    "For a node op(x_f) on a fresh cache within the size limit (turbo and bumper off), a successful call stores op.(X[f, :]) exactly when early_exit is off, or the row and the output are both finite."
    "Well-formed node; sizeof(T) > 0; nunary * nfeatures <= max_entries."
    ``evalCacheStoreRule ``evalCacheStoreRule_proof,
  entry "evalcache-sequence"
    ["eval_tree_array", "EvalContext", "UnaryFeatureCache", "cached_deg1_eval"]
    "One cache shared by any sequence of calls (different trees; any identities of X and operators, whose changes reset the entries; any use_fused, bumper, turbo and buffer per call) gives every call its uncached result, provided contents never change behind an identity and all calls use the same early_exit."
    "Well-formed trees; sizeof(T) > 0; XStable and OpsStable (same identity, same contents); one early_exit value."
    ``evalCacheSequence ``evalCacheSequence_proof .proven
    "Companions: evalcache-mutate-x, evalcache-mutate-op, evalcache-shared-early-exit drop one hypothesis each.",
  entry "evalcache-mutate-x"
    ["eval_tree_array", "UnaryFeatureCache", "cached_deg1_eval"]
    "As evalcache-sequence, but X may change contents while keeping its identity."
    "As evalcache-sequence without XStable."
    ``evalCacheMutateX ``Ex.evalCacheMutateX_refuted .refuted
    "Entries are keyed by X === cache.X. cos(x1) on X = [0.0 1.0], then X[1,1] = 2.0 in place: cached ([1.0, 0.54], true), uncached ([-0.42, 0.54], true). Also a view(P, :, idx) whose idx vector is mutated: the new view is === to the old one, so the stale entry is returned. The EvalContext docstring forbids in-place mutation of the input matrix; the view case is not mentioned (Q56).",
  entry "evalcache-mutate-op"
    ["eval_tree_array", "UnaryFeatureCache", "cached_deg1_eval", "OperatorEnum"]
    "As evalcache-sequence, but an operator may change behaviour while the operators keep their identity."
    "As evalcache-sequence without OpsStable."
    ``evalCacheMutateOp ``Ex.evalCacheMutateOp_refuted .refuted
    "Entries are keyed by operators === cache.operators. With x -> scale[] * x and scale[] = 2.0 then 3.0 on X = [1.0 2.0]: cached ([2.0, 4.0], true), uncached ([3.0, 6.0], true). Not covered by the docstring (Q56).",
  entry "evalcache-shared-early-exit"
    ["eval_tree_array", "EvalContext", "UnaryFeatureCache", "cached_deg1_eval"]
    "As evalcache-sequence, but the contexts sharing the cache may differ in early_exit."
    "As evalcache-sequence without the single early_exit value."
    ``evalCacheSharedEarly ``Ex.evalCacheSharedEarly_refuted .refuted
    "Under early_exit=false the cache stores entries of non-finite feature rows. inv(x1) on X = [Inf 1.0] through an early_exit=false context, then an early_exit=true context sharing the same UnaryFeatureCache: cached ([0.0, 1.0], true), uncached ([Inf, 1.0], false). Sharing one cache between such contexts is not ruled out by the API (Q57). Sharing with the same early_exit is proven safe (evalcache-sequence).",
  entry "evalcache-limit"
    ["eval_tree_array", "UnaryFeatureCache", "cached_deg1_eval"]
    "When a full entry matrix would exceed 16 MiB, the result is the uncached one and the cache, once reset for this input, has a 0x0 entry matrix and stores nothing."
    "As evalcache-single, plus max_entries < nunary * nfeatures."
    ``evalCacheLimit ``evalCacheLimit_proof,
  entry "evalcache-turbo"
    ["eval_tree_array", "EvalContext", "cached_deg1_eval", "_is_loopvectorization_loaded"]
    "With turbo=true the cache is never read or written: the result is the uncached turbo result and the cache state is unchanged."
    "None."
    ``evalCacheTurbo ``evalCacheTurbo_proof .proven
    "cached_deg1_eval returns nothing before touching the cache when turbo or bumper is on (src/Evaluate.jl:606-607). Fused kernels (op(op2(x)), binary leaf kernels) never consult the cache and compute the same values (evalcache-single for both use_fused values). Julia check: evalcache-checks.jl turbo-skips, bumper-skips, fused-chain-no-entry, shared-fused, many-unary.",
  entry "evalcache-copy"
    ["EvalContext", "UnaryFeatureCache"]
    "copy(eval_context) starts from a fresh UnaryFeatureCache, so it gives uncached results whatever state, even stale, the original cache is in."
    "Well-formed tree; sizeof(T) > 0."
    ``evalCacheCopy ``evalCacheCopy_proof,
  entry "evalcache-threads"
    ["eval_tree_array", "UnaryFeatureCache", "cached_deg1_eval"]
    "Two threads that share one cache, each evaluating a unary feature node on its own input, finish with their uncached results under every interleaving of the cache accesses."
    "Well-formed nodes; sizeof(T) > 0; contents stable per identity; cache consistent for both inputs."
    ``evalCacheRace ``Ex.evalCacheRace_refuted .refuted
    "The cache has no lock. Lean schedule: A checks X1, B resets for X2, misses and stores, A reads B's entry. Julia: Threads.@threads over 400000 evaluations of cos(x1) alternating two 1x64 matrices with one shared EvalContext gave tens of thousands of wrong outputs (flag true); with one matrix, none (Q58). Companion: evalcache-threads-same.",
  entry "evalcache-threads-same"
    ["cached_deg1_eval", "UnaryFeatureCache"]
    "Two threads that share one cache and one input (identities, contents, early_exit), evaluating any unary feature nodes, finish with their uncached results under every interleaving of the modelled cache steps."
    "As evalcache-threads, plus the same input for both threads; each modelled step (identity check and reset, entry read, store) is atomic."
    ``evalCacheRaceSame ``evalCacheRaceSame_proof .proven
    "Assumes the modelled steps are atomic and their writes visible to the other thread; Julia gives no such guarantee for unsynchronized fields (a data race), so this is about the algorithm, not the memory model. Julia run with one shared matrix showed no wrong outputs."
]

end DynExpr.EvalCache
