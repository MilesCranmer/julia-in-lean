# `inline_cost_clamp` (Compiler/src/optimize.jl:131-137) rounds a cost through the 8-bit encoding
# of src/ircode.c, whose largest finite value is 3968; every cost from 3969 to 65534 comes back as
# MAX_INLINE_COST, the "never inline" marker. With a raised `inline_cost_threshold` (here 10^9, as
# suggested in JuliaLang/julia#60121 instead of typemax(Int)) a callee of cost about 5000 is far
# below the threshold but is reported non-inlineable, while one of cost about 3000 is inlined.
# The same happens with inline_cost_threshold = Int(MAX_INLINE_COST) = 65535, which is what
# GPUCompiler sets for `always_inline = true` since JuliaGPU/GPUCompiler.jl#741 (Nov 2025).
const CC = Base.Compiler
id = "compiler-inlining-clamp-finite-to-max"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
println("inline_cost_clamp(3968) = ", Int(CC.inline_cost_clamp(3968)),
    ", inline_cost_clamp(3969) = ", Int(CC.inline_cost_clamp(3969)))

struct BigThresholdInterp <: CC.AbstractInterpreter
    world::UInt
    inf_cache::Any
    threshold::Int
end
BigThresholdInterp(t = 10^9) = BigThresholdInterp(Base.get_world_counter(),
    isdefined(CC, :InferenceCache) ? CC.InferenceCache() : CC.InferenceResult[], t)
CC.InferenceParams(::BigThresholdInterp) = CC.InferenceParams()
CC.OptimizationParams(i::BigThresholdInterp) = CC.OptimizationParams(; inline_cost_threshold = i.threshold)
CC.get_inference_world(i::BigThresholdInterp) = i.world
CC.get_inference_cache(i::BigThresholdInterp) = i.inf_cache
CC.cache_owner(::BigThresholdInterp) = BigThresholdInterp

# each `r[](1)` calls an unknown function and costs inline_nonleaf_penalty (1000)
three(r) = (r[](1); r[](1); r[](1); nothing)
five(r) = (r[](1); r[](1); r[](1); r[](1); r[](1); nothing)
callthree(r) = three(r)
callfive(r) = five(r)

params = CC.OptimizationParams(; inline_cost_threshold = 10^9)
for f in (three, five)
    ir, = only(Base.code_ircode(f, (Base.RefValue{Any},)))
    cost = zeros(Int, length(ir.stmts))
    CC.statement_costs!(cost, ir.stmts.stmt, ir, ir.sptypes, params)
    println(f, ": body cost ", sum(cost), ", inline_cost_model(ir, params, 10^9) = ",
        Int(CC.inline_cost_model(ir, params, 10^9)))
end
invokes(ci, name) = count(st -> Meta.isexpr(st, :invoke) &&
    (m = st.args[1]; m = m isa Core.CodeInstance ? m.def : m; m.def.name === name), ci.code)
interp = BigThresholdInterp()
c3 = first(only(code_typed(callthree, (Base.RefValue{Any},); interp)))
c5 = first(only(code_typed(callfive, (Base.RefValue{Any},); interp)))
println("threshold 10^9: three calls left = ", invokes(c3, :three), ", five calls left = ", invokes(c5, :five))
gi = BigThresholdInterp(Int(CC.MAX_INLINE_COST))
g3 = first(only(code_typed(callthree, (Base.RefValue{Any},); interp = gi)))
g5 = first(only(code_typed(callfive, (Base.RefValue{Any},); interp = gi)))
println("threshold MAX_INLINE_COST (GPUCompiler always_inline): three calls left = ", invokes(g3, :three),
    ", five calls left = ", invokes(g5, :five))
ok = CC.inline_cost_clamp(3969) == CC.MAX_INLINE_COST && invokes(c3, :three) == 0 && invokes(c5, :five) == 1
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
