# DynExpr: a Lean 4 formalization of DynamicExpressions.jl

This Lean package models [DynamicExpressions.jl](https://github.com/SymbolicML/DynamicExpressions.jl)
at the master commit recorded in [ARCHITECTURE.md](ARCHITECTURE.md) (version 2.13.0;
the `EvalCache` slice models PR #219). Each registered property of the package is
either proven in Lean or refuted by a Lean counterexample together with a Julia
reproducer in `repro/`. `registry.tsv` lists every property and its status, and
[QUESTIONS.md](QUESTIONS.md) records the rulings on unclear intended behaviour.

Build and audit (Lean toolchain from `lean-toolchain`, no Mathlib):

```sh
lake build
bash scripts/audit.sh    # ends with AUDIT OK; writes .lake/audit.out
```

The reproducers need DynamicExpressions.jl itself: `repro/Project.toml` pins it at
the master commit, so `julia --project=repro -e 'using Pkg; Pkg.instantiate()'`
installs it, and `scripts/run-repros.sh` then runs every reproducer of a refuted
entry. The `evalcache-*` reproducers need the PR #219 branch instead.
