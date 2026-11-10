# EFFECT_FREE_GLOBALLY is 0x03, the bit union of ALWAYS_FALSE and
# EFFECT_FREE_IF_INACCESSIBLEMEMONLY (Compiler/src/effects.jl:176-183). So
# is_effect_free_if_inaccessiblememonly reads it as the conditional state, and inference flags
# every `GC.@preserve` begin/end statement IR_FLAG_EFIIMO (Compiler/src/optimize.jl:86-90).
# merge_effectbits(EFFECT_FREE_GLOBALLY, EFFECT_FREE_IF_INACCESSIBLEMEMONLY) is
# EFFECT_FREE_GLOBALLY, which drops the condition, and merge_effects! then turns it into ALWAYS_TRUE.
const CC = Base.Compiler
id = "compiler-effects-effect-free-globally-collision"
G = CC.EFFECT_FREE_GLOBALLY; IAMO = CC.EFFECT_FREE_IF_INACCESSIBLEMEMONLY
q = CC.is_effect_free_if_inaccessiblememonly(CC.Effects(CC.EFFECTS_TOTAL; effect_free = G))
m = CC.merge_effectbits(G, IAMO)
println("EFFECT_FREE_GLOBALLY == ALWAYS_FALSE | EFFECT_FREE_IF_INACCESSIBLEMEMONLY: ", G == (CC.ALWAYS_FALSE | IAMO))
println("is_effect_free_if_inaccessiblememonly(effect_free = EFFECT_FREE_GLOBALLY) = ", q)
println("merge_effectbits(EFFECT_FREE_GLOBALLY, EFFECT_FREE_IF_INACCESSIBLEMEMONLY) = ", repr(m))
g(x) = GC.@preserve x 1
src = only(code_typed(g, (Vector{Int},); optimize = false))[1]
flagged = false
for (i, stmt) in enumerate(src.code)
    if stmt isa Expr && stmt.head in (:gc_preserve_begin, :gc_preserve_end)
        f = src.ssaflags[i]
        has = (f & CC.IR_FLAG_EFIIMO) != 0
        global flagged |= has
        println("statement ", i, " ", stmt.head, ": IR_FLAG_EFIIMO set = ", has)
    end
end
ok = q && m == G && flagged
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
