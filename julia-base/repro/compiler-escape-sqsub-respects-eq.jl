# `x ⊑ₑ y` (Compiler/src/ssair/EscapeAnalysis.jl:246-256) returns false as soon as `y === ⊥`,
# before comparing fields. `ignore_argescape(⊥)` copies the Liveness set, so it is `== ⊥` but
# not `=== ⊥`, and it is not `⊑ₑ ⊥` although `⊥ ⊑ₑ` it.
const EA = Base.Compiler.EscapeAnalysis
id = "compiler-escape-sqsub-respects-eq"
bot = EA.NotAnalyzed()
x = EA.ignore_argescape(bot)
println("x == ⊥: ", x == bot, "; x === ⊥: ", x === bot, "; x ⊑ₑ ⊥: ", EA.:⊑ₑ(x, bot), "; ⊥ ⊑ₑ x: ", EA.:⊑ₑ(bot, x))
ok = x == bot && !EA.:⊑ₑ(x, bot) && EA.:⊑ₑ(bot, x)
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
