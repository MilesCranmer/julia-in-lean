# adjust_effects(ipo_effects, def::Method) (Compiler/src/typeinfer.jl:659-661) sets nonoverlayed
# to CONSISTENT_OVERLAY whenever the method's purity has the consistent_overlay bit, even when
# inference found ALWAYS_TRUE, so the override weakens the effects it is meant to strengthen.
# The bit is set here with a hand-written `Expr(:purity, ...)` on a method that is not an overlay.
const CC = Base.Compiler
id = "compiler-effects-adjust-consistent-overlay"
@eval plain(x::Int) = x + 1
@eval annotated(x::Int) = ($(Expr(:meta, Expr(:purity,
    false, false, false, false, false, false, false, false, false, true, false))); x + 1)
m = only(methods(annotated))
o = CC.decode_effects_override(m.purity)
e1 = Base.infer_effects(plain, (Int,)); e2 = Base.infer_effects(annotated, (Int,))
println("purity = ", repr(m.purity), ", consistent_overlay = ", o.consistent_overlay)
println("infer_effects(plain) = ", e1, ", nonoverlayed = ", repr(e1.nonoverlayed))
println("infer_effects(annotated) = ", e2, ", nonoverlayed = ", repr(e2.nonoverlayed))
a = CC.adjust_effects(CC.EFFECTS_TOTAL, m)
println("adjust_effects(EFFECTS_TOTAL, m).nonoverlayed = ", repr(a.nonoverlayed))
ok = o.consistent_overlay && e1.nonoverlayed == CC.ALWAYS_TRUE &&
     e2.nonoverlayed == CC.CONSISTENT_OVERLAY && a.nonoverlayed == CC.CONSISTENT_OVERLAY
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
