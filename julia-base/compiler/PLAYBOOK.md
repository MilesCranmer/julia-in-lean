# Playbook: formalizing Julia's inference lattice

This extends julia-in-lean from Base to the compiler. The pilot covers the inference
lattice and its widening: `Compiler/src/abstractlattice.jl`, `Compiler/src/typelattice.jl`
and `Compiler/src/typelimits.jl`. Read `../ARCHITECTURE.md` first; its modelling rules,
registry, audit, `repro/` and `bugs/` schema all apply. This file adds what is specific to
the compiler and overrides it where they differ.

Two goals, in order:

1. Bugs: lattice operations that break their own laws on inputs inference produces. A
   broken law here means wrong inferred types (unsound code), inference that does not
   terminate, or results that depend on the order inference visits code. The last one
   matters for package caches: order-dependent inference produces different code
   instances for the same input, so precompiled code is redone or invalidated.
2. Optimization leads: places where the code loses precision it did not need to lose,
   does work whose result is provably fixed, or has a fast path that can never fire (or
   always fires). Record each in `compiler/PERF_LEADS.md` with the source lines, the
   Lean statement that shows it, and how often real inference would hit it (a guess,
   labelled as one). A lead is a hypothesis for a human to measure, never a claim of
   speedup.

## Pinned sources

- Model source: Julia master `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, the same commit
  `../ARCHITECTURE.md` pins, so the existing `src/subtype.c` model matches. Read it from a
  checkout of that commit. Cite `Compiler/src/<file>.jl:<line>` from there, and check every
  citation against the file.
- Julia built from that commit (`$JULIA` below). Difftests use this binary. Reproducers run
  on it and on current master (`julia +nightly`, record `VERSION` and
  `Base.GIT_VERSION_INFO.commit`). A bug that no longer reproduces on nightly is recorded
  as fixed-upstream, not reported.
- Release for comparison: `julia +1.13`.

## Compute

```
lake build JuliaLean.Proofs.Compiler.src.typelattice compilerdiff
$JULIA difftest/compiler/typelattice.jl --cases 50000 --seed 1
```

Build only the modules you changed and their dependents. A full cold `lake build` needs
a memory cap: at the default thread count it can use over 40 GB, so limit it with
`LEAN_NUM_THREADS` (5 threads stayed under 32 GB) or run it under a cgroup cap. Several
agents can work at once if each has its own checkout; they must not share one `.lake`.

## Layout

```
JuliaLean/Compiler/src/<file>.lean          source-mirrored model of Compiler/src/<file>.jl
JuliaLean/Proofs/Compiler/src/<file>.lean   properties, proofs, `entries : List Entry`
JuliaLean/Proofs/Compiler/src/<file>/       topic files when one file gets large
difftest/compiler/<file>.jl                 Julia driver: generate cases, run the pinned
                                            Compiler, compare with the Lean executable
CompilerDiff.lean (lean_exe `compilerdiff`) reads JSON-line cases, prints model results
coverage/methods/Compiler_src_<file>.tsv    inventory rows, same columns as Base's
compiler/PERF_LEADS.md                      optimization leads
```

`JuliaLean/Registry.lean` imports each `Proofs/Compiler/src/<file>` and appends its
`entries`. The setup agent wires these once; later agents only fill their own file.

## Reusing the type model

Types are `JuliaLean.C.Val` (`JuliaLean/src/julia_h.lean`), with the type-name universe
`Types`. Subtyping is `jlSubtype n T a b`, equality `jlTypesEqual`, intersection
`jlIntersectTypes`, all in `JuliaLean/src/subtype_c.lean` and running in `CM` with an
explicit fuel `n`. `typejoin` is in `JuliaLean/base/promotion.lean`. Reuse these; do
not write a second type representation. Lattice elements (`Const`, `PartialStruct`,
`Conditional`, `InterConditional`, `MustAlias`, `PartialTypeVar`, `LimitedAccuracy`,
`PartialOpaque`, `MaybeUndef`) become one Lean inductive over `Val`, mirroring
`Compiler/src/typelattice.jl` and `Core`'s definitions.

The lattice is layered (`abstractlattice.jl`): each layer's `⊑`, `tmerge` and `tmeet`
handle their own wrappers and defer to the next layer. Mirror that structure, with the
layer passed explicitly, rather than flattening it into one function. Model the default
`typeinf_lattice` stack first.

Proofs over the 13k-line subtype model are expensive. Separate the two concerns:

- State each lattice property twice when needed. A generic version takes subtyping as
  a parameter `sub : Val → Val → Bool` with explicit, named assumptions (reflexive,
  transitive, `Union{}` least, `Any` greatest, and whatever else the proof needs). Prove
  it from those. Every assumption must be one Julia's subtyping is meant to satisfy;
  list each in the docstring.
- Refute with the concrete model: instantiate `sub` with `jlSubtype` on a concrete
  universe and check the counterexample with `decide`. Then confirm it on the pinned
  Julia with a reproducer. A counterexample that holds only in the generic version (an
  abstract `sub` no real subtyping matches) is not a finding.

## What to state

Sources, in order of preference:

1. The implementation disagreeing with itself: `tmerge(a, b)` vs `tmerge(b, a)`; the
   fast path (`tmerge_fast_path`, `issimpleenoughtype`) vs the slow path on the same
   inputs; `⊑` vs `is_lattice_equal` vs `⊏`; one layer vs the layer below on inputs the
   upper layer does not wrap; `widenconst` before vs after an operation.
2. Lattice laws inference relies on: `⊑` is a preorder; `tmerge` is an upper bound of
   both arguments (soundness: losing this means wrong code); `tmerge(a, a) ⊑ a`;
   `tmeet` is a lower bound and below both arguments; widening terminates (repeated
   `tmerge` along an ascending chain reaches a fixed point in a bounded number of steps;
   `limit_type_size` and `type_more_complex` bound the result's depth and length);
   `widenconst(a) ⊒ a`; monotonicity of `tmerge` and `widenconst` in each argument.
   Commutativity and associativity of `tmerge` are not promised. Refuting them is a
   finding only with a concrete consequence (order-dependent inference results), so
   record it as a perf or caching lead unless it also breaks soundness.
3. Comments and docstrings in the source, read in context.

Quantify over all lattice elements the default lattice can produce, including those
built from `Union`s, `UnionAll`s, `Vararg`s, `Type{T}`, nested `PartialStruct`s and
`Conditional`s on the same or different slots. Do not assume the interesting case away
("no Vararg", "concrete types only", "small depth"). If a property needs a precondition,
it must be one inference maintains (state where), and the reviewer will check it.

## Differential testing (before stating any property)

The Julia driver builds lattice elements (edge-heavy: `Union{}`, `Any`, `Type`,
`Type{Union{}}`, `Vararg` tails, `NTuple`, deep nesting near the limits in
`typelimits.jl`, `Const` of types, `PartialStruct` with undefined fields), serializes
each with its type-name universe to JSON, calls the pinned `Compiler` function on the
default lattice (`Compiler.typeinf_lattice(Compiler.NativeInterpreter())`, or the
`fallback_lattice` where the source does), and compares with `compilerdiff` output.
Reach 100% agreement on at least 50k cases over several seeds. A mismatch is a model bug
until proven otherwise. Record each run's seed, case count and agreement in the
difftest's header comment.

## Rules carried over from the Python project's review

A row counts only if it survives independent review (`../coverage/REVIEW_PROMPT.md`).
Check these before claiming one:

- The theorem must unfold the function's body. If `fun _ _ => Any` or "always return
  the first argument" also satisfies it, it pins nothing.
- Fuel exhaustion (`outOfBudget`) is never a Julia outcome. A property that holds
  because the model ran out of fuel is hollow.
- Do not use Lean `=` on `Val` where Julia uses `==` on types (`jlTypesEqual`) or `===`.
- Never weaken a statement to get a proof. If it is false, refute it. A hard property
  stays `todo` with a note on what is missing.
- Forbidden: `sorry`, `admit`, `native_decide`, `bv_decide`, `ofReduceBool`, new axioms,
  `implemented_by`, `@[extern]`.

## Bugs and leads

A refutation needs `repro/<id>.jl` printing `REPRODUCED <id>` on the pinned Julia, and
`bugs/<id>.yaml`. Reproducers call `Base.Compiler` functions directly; that is fine for
this project. Where possible also show a user-visible effect (a `Base.return_types` or
`code_typed` result that is wrong, or that changes with definition order). Priority:
P0 is unsound inference (inferred type excludes a value the code returns) or a hang;
P1 is order-dependent or non-terminating widening on code real packages could write;
P2 is precision lost or a law broken with no visible effect yet; P3 is cosmetic.

Triage is read-only. Search with `gh search issues --repo JuliaLang/julia` and
`gh search prs`, with unquoted words and several spellings, and record every query.
Never create, comment on or react to anything on GitHub.
