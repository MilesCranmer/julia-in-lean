# `inline_cost_model(interp, result, inline_flag, ir)` (Compiler/src/typeinfer.jl:498-546) raises
# `cost_threshold` with plain `Int` additions. With `inline_cost_threshold = typemax(Int)`, the
# value GPUCompiler sets to force inlining (JuliaLang/julia#60121), the tuple-return bonus and the
# `@inline` adjustment wrap to a negative threshold, so a small method returning a non-concrete
# `Tuple` (or an `@inline` method without a dispatch-tuple signature) becomes uninlineable, while
# the default parameters inline it.
const CC = Base.Compiler
id = "compiler-inlining-threshold-overflow"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)

struct MaxThresholdInterp <: CC.AbstractInterpreter
    world::UInt
    inf_cache::Any
end
MaxThresholdInterp() = MaxThresholdInterp(Base.get_world_counter(),
    isdefined(CC, :InferenceCache) ? CC.InferenceCache() : CC.InferenceResult[])
CC.InferenceParams(::MaxThresholdInterp) = CC.InferenceParams()
CC.OptimizationParams(::MaxThresholdInterp) = CC.OptimizationParams(; inline_cost_threshold = typemax(Int))
CC.get_inference_world(i::MaxThresholdInterp) = i.world
CC.get_inference_cache(i::MaxThresholdInterp) = i.inf_cache
CC.cache_owner(::MaxThresholdInterp) = MaxThresholdInterp

params = CC.OptimizationParams(; inline_cost_threshold = typemax(Int))
d = params.inline_cost_threshold
println("threshold with tuple bonus: ", d + params.inline_tupleret_bonus)
println("threshold with @inline: ", d + 19 * d)

tuplefn(x::Int) = x > 0 ? (x,) : (x, x)
calltuple(x) = tuplefn(x)
@noinline opaque(x) = x
plainfn(x::Int) = x > 0 ? opaque(x) : -x
callplain(x) = plainfn(x)

invokes(ci, name) = count(st -> Meta.isexpr(st, :invoke) &&
    (m = st.args[1]; m = m isa Core.CodeInstance ? m.def : m; m.def.name === name), ci.code)
for (label, interp) in (("default", nothing), ("typemax", MaxThresholdInterp()))
    kw = interp === nothing ? (;) : (; interp)
    ci1 = first(only(code_typed(calltuple, (Int,); kw...)))
    ci2 = first(only(code_typed(callplain, (Int,); kw...)))
    println(label, " threshold: tuplefn calls left = ", invokes(ci1, :tuplefn),
        ", plainfn calls left = ", invokes(ci2, :plainfn))
end
default_ci = first(only(code_typed(calltuple, (Int,))))
max_ci = first(only(code_typed(calltuple, (Int,); interp = MaxThresholdInterp())))
max_plain = first(only(code_typed(callplain, (Int,); interp = MaxThresholdInterp())))
ok = d + params.inline_tupleret_bonus < 0 && invokes(default_ci, :tuplefn) == 0 &&
     invokes(max_ci, :tuplefn) == 1 && invokes(max_plain, :plainfn) == 0
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
