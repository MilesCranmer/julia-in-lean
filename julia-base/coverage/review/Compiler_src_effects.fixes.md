# Fixes for the Compiler_src_effects review

## Line 324, `merge_effectbits(old::Bool, new::Bool)` (HOLLOW)

Fixed by strengthening the property. `MergeEffectbitsLaws` in
`JuliaLean/Proofs/Compiler/src/effects.lean` has a new conjunct, proven by case analysis
over both arguments:

```lean
(∀ a b : Bool, mergeEffectbitsBool a b = true ↔ (a = true ∧ b = true))
```

The merge keeps a Bool property (such as nothrow) exactly when both sides have it. This
fixes the truth table, so `old | new` (which keeps nothrow when one side throws) no longer
satisfies it, and nor does any function other than `&`. The commutativity, associativity
and idempotence conjuncts are kept. The entry `compiler-effects-merge-effectbits` states
the new law in its statement text.

Model unchanged. Build: `lake build JuliaLean.Proofs.Compiler.src.effects` OK. Difftest
`difftest/compiler/effects.jl` re-run, seeds 1, 2 and 3 at 50000 cases each: AGREE
50000/50000 for each. All four `repro/compiler-effects-*.jl` print REPRODUCED on the pinned
Julia. `scripts/audit.sh`: AUDIT OK, ENTRIES 8895.

## Other rows

No change. The 29 FAITHFUL rows keep their entries.
