# `is_better_effects` (Compiler/src/effects.jl:226-302) does not follow the order of the
# `consistent` states: it calls CONSISTENT_IF_NOTRETURNED better than
# CONSISTENT_IF_INACCESSIBLEMEMONLY and also the reverse, it calls the union of both conditions
# better than CONSISTENT_IF_INACCESSIBLEMEMONLY (the union is weaker), and it does not call
# CONSISTENT_IF_NOTRETURNED better than the union (it is stronger).
const CC = Base.Compiler
id = "compiler-effects-is-better-order"
c(v) = CC.Effects(CC.EFFECTS_TOTAL; consistent = v)
NR = CC.CONSISTENT_IF_NOTRETURNED; IM = CC.CONSISTENT_IF_INACCESSIBLEMEMONLY; BOTH = NR | IM
stronger(a, b) = a != b && CC.merge_effects(a, b) == b   # every field of a at least as strong
r1 = CC.is_better_effects(c(NR), c(IM)); r2 = CC.is_better_effects(c(IM), c(NR))
r3 = CC.is_better_effects(c(BOTH), c(IM)); r4 = CC.is_better_effects(c(NR), c(BOTH))
println("is_better_effects(?c NOTRETURNED, ?c INACCESSIBLEMEMONLY) = ", r1, "; stronger = ", stronger(c(NR), c(IM)))
println("is_better_effects(?c INACCESSIBLEMEMONLY, ?c NOTRETURNED) = ", r2, "; stronger = ", stronger(c(IM), c(NR)))
println("is_better_effects(?c both, ?c INACCESSIBLEMEMONLY) = ", r3, "; stronger = ", stronger(c(BOTH), c(IM)))
println("is_better_effects(?c NOTRETURNED, ?c both) = ", r4, "; stronger = ", stronger(c(NR), c(BOTH)))
# The two incomparable states each called better than the other is the reproduced claim.
ok = r1 && r2 && !stronger(c(NR), c(IM)) && !stronger(c(IM), c(NR))
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
