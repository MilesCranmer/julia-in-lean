# Triage of the wave-3 findings (2026-11-10)

Skeptical pass over the bug yamls and perf leads of five areas: loading, escape, slot2ssa,
cacheresult and inlining. Each reproducer was run on four builds:

- pinned 1.15.0-DEV.184 `f755f49a9e`
- `julia +nightly` 1.15.0-DEV.304 `290d5bb5f5` (2026-10-31)
- `julia +1.13` 1.13.3 `67ac47b9cd`
- master 1.15.0-DEV.627 `4c0e39dde6`, an upstream master build from 2026-11-09 on the build machine
  (clean tree). It is 6 commits behind upstream master
  `eb844b8ebd` (2026-11-10), and none of those 6 touch the files involved. Master source was
  also read at `eb844b8ebd` for every cause line.

All results are in each yaml (`output.master`, `reproduced.master`). The verdict for each one is a
`Triage 2026-11-10` paragraph appended to `likelihood`, since `check_bugs.py` allows no `triage`
key. All duplicate searches were read-only; every query is listed in `duplicates.queries`.
`check_bugs.py` reports 0 problems in all five worktrees.

## Surviving findings, ranked

| # | area | id | priority | summary | pinned / nightly / 1.13 / master | duplicate |
|---|------|----|----------|---------|----------------------------------|-----------|
| 1 | slot2ssa | `compiler-slot2ssa-catch-loop-header` | **P0** | A `while` loop at the start of a `catch` block reads the value the local had when the exception was thrown: `loopcatch()` returns 1, not 4, and the `Ref` variant segfaults. Plain source code. | yes / yes / yes / yes (run; segfault also on master) | none. Related: [#63994](https://github.com/JuliaLang/julia/issues/63994) (a different stale local in `finally`), [#57393](https://github.com/JuliaLang/julia/issues/57393) |
| 2 | inlining | `compiler-inlining-clamp-finite-to-max` | P2 | Every cost from 3969 to 65534 encodes to "never inline". GPUCompiler's `always_inline = true` sets the threshold to 65535, so callees costing over 3968 stay calls there. | yes / yes / yes / yes | none |
| 3 | loading | `compiler-loading-clone-targets-oob` | P2 (was P1) | A damaged clone-target length in a `.ji` header segfaults `using` in `jl_check_pkgimage_clones` instead of rejecting the cache. | yes / yes / yes / yes | none |
| 4 | loading | `compiler-loading-dir-include-size` | P2 | A directory `include_dependency` is stale when the directory's `st_size` changes but its listing (its documented content) does not. | yes / yes / yes / yes | none |
| 5 | loading | `compiler-loading-depot-shadow-recompile` | P2 | A dev'd package in a later depot is recompiled every session when an earlier depot has a copy at the same relative path. | yes / yes / yes / yes | none. Related: [#52161](https://github.com/JuliaLang/julia/issues/52161) |
| 6 | slot2ssa | `compiler-slot2ssa-arg-entry-loop` | P3 (was P2) | No phi for an assigned argument when block 1 is a loop header; a hand-built CodeInfo returns 1 instead of 4. | yes / yes / yes / yes | none |
| 7 | inlining | `compiler-inlining-typeassert-one-arg` | P3 (was P2) | `statement_cost` throws a BoundsError on `Core.typeassert(x)`, giving "Internal error: during type inference". | yes / yes / yes / yes | none |
| 8 | cacheresult | `compiler-cacheresult-va-tail-miss` | P3 (was P2) | A const-prop key that ends in `Vararg` is never found again, so each such call site repeats constant propagation. | yes / yes / yes / yes | none |
| 9 | inlining | `compiler-inlining-threshold-overflow` | P3 (was P2) | `inline_cost_threshold = typemax(Int)` wraps the threshold negative, so the methods it should inline are never inlined. | yes / yes / yes / yes | **duplicate** of [#60121](https://github.com/JuliaLang/julia/pull/60121) (PR, closed unmerged) |
| 10 | escape | `compiler-escape-sqsub-transitive` | P3 | `⊑ₑ` loops `for i = length(xinfos)`, so it checks only the last field and is not transitive (BoundsError for zero fields). | yes / yes / yes / yes | none |
| 11 | inlining | `compiler-inlining-llvmcall-cost` | P3 | `maxarg + 1` wraps for `llvmcall`, so it costs 20, not 10, and its own branch is dead. | yes / yes / yes / yes | none |
| 12 | escape | `compiler-escape-sqsub-respects-eq` | P3 | `x ⊑ₑ ⊥` is false for `x == ⊥` when `x !== ⊥`. | yes / yes / yes / yes | none |
| 13 | inlining | `compiler-inlining-rsiimo-reserved-comment` | P3 (doc) | The comment says RSIIMO uses bit 15; it uses bit 20. | yes / yes / n/a (no flag in 1.13) / yes | none |

Notes on each finding:

1. **catch-loop-header.** The strongest finding of the wave. It is a real miscompile of ordinary
   code: a retry or polling loop at the top of a `catch`. Julia 1.10.12 gets it right (4); since
   1.11 every release returns 1, and the `Ref` variant segfaults on master too. `slot2ssa.jl` has
   not changed since the pinned commit. [#62519](https://github.com/JuliaLang/julia/pull/62519)
   (merged) changed codegen for PhiC slots of unreachable catch blocks, not this. This should
   be reported first.
2. **clamp.** This used to need an unusual threshold. Since
   [JuliaGPU/GPUCompiler.jl#741](https://github.com/JuliaGPU/GPUCompiler.jl/pull/741) (merged
   2025-11-15), GPUCompiler sets `inline_cost_threshold = Int(CC.MAX_INLINE_COST)` = 65535 for
   `always_inline = true`. The reproducer now runs with that threshold too, and a cost-5000
   callee stays a call. GPUCompiler adds no LLVM `alwaysinline` attribute for this setting, so
   only LLVM's own heuristics can still inline such a callee. Not measured: how many real
   kernels have callees above 3968.
3. **clone-targets-oob.** Downgraded because the input is narrow. `compilecache` writes a
   temporary file and renames it, so a killed writer cannot leave a partial cache under the
   cache name. The damage must fall inside the few dozen bytes of clone-target fields. Not
   tested: whether a truncated file reaches this path.
4. **dir-include-size.** The `include_dependency` docstring defines a directory's content as
   `join(readdir(path))`, and no commit says the size is meant to be part of it. On APFS the size
   follows the entry count, so there only a move to another file system triggers it; ext4 and XFS
   never shrink a directory.
5. **depot-shadow.** Registered packages are not affected: lookup and restore both go through
   `DEPOT_PATH` in order. Only a manifest `path =` entry that points into a later depot triggers
   it.
6. **arg-entry-loop.** Downgraded because the input breaks a lowering invariant. Commit
   [bc7e002d13](https://github.com/JuliaLang/julia/commit/bc7e002d13) (2016) says: "It simplifies
   later analysis to assume that arguments are not overwritten". Both flisp lowering and
   JuliaLowering keep it; on master, JuliaLowering emits `x@_3 = x@_2` and the function returns 4.
   But the invariant is not documented and `verify_ir` does not check it, so a hand-built CodeInfo
   is miscompiled without any error.
7. **typeassert-one-arg.** Only erroneous code hits it: a one-argument `Core.typeassert` always
   throws, and the function still runs. On master, [#64765](https://github.com/JuliaLang/julia/pull/64765)
   ([c95c86857c](https://github.com/JuliaLang/julia/commit/c95c86857c)) added an
   `_apply_iterate` branch with a length check next to this line, but did not change the line.
8. **va-tail-miss.** Downgraded after measuring it. `typeinf_frame` with a fresh
   `NativeInterpreter` on 40000 Base method instances (pinned) made 39775 const-prop entries.
   66 of them had a `Vararg` tail, and 16 repeated an earlier key, which is 0.04% extra work.
9. **threshold-overflow.** Known: [#60121](https://github.com/JuliaLang/julia/pull/60121)
   (closed unmerged, 2026-06-26). JeffBezanson agreed there that the additions should saturate.
   GPUCompiler no longer passes `typemax(Int)` ([GPUCompiler.jl#741](https://github.com/JuliaGPU/GPUCompiler.jl/pull/741)). Fix it together with
   finding 2.
10. and 12. **⊑ₑ.** No caller in `Compiler/src` reaches the slow path (`has_all_escape` returns at
   the fast path). Fix both in one change.
11. **llvmcall.** It changes a decision only within 10 of the threshold.
13. **RSIIMO comment.** The comment and the flag were added in the same commit,
   [5566b23a42](https://github.com/JuliaLang/julia/commit/5566b23a42) ([#62604](https://github.com/JuliaLang/julia/pull/62604)).

## Withdrawn

| area | id | reason |
|------|----|--------|
| slot2ssa | `compiler-slot2ssa-fixup-uses-isdefined` | Dead code. The only caller of `fixup_uses!` is the `if false` branch at `slot2ssa.jl:579` on master, so no compiled code can reach it. Kept as a cleanup note: delete the function and the branch, as [5fdc91d4e3](https://github.com/JuliaLang/julia/commit/5fdc91d4e3) did for other unused functions. The yaml stays, at P3, with this verdict. |
| escape | `compiler-escape-sqsub-join-agree`, `compiler-escape-join-upper-bound` | Not separate bugs: the same loop as `compiler-escape-sqsub-transitive` (its `covers`). |
| inlining | `compiler-inlining-statement-cost-nothrow` | Not separate: covered by `compiler-inlining-typeassert-one-arg`. |

No finding turned out to be a model artifact or fixed on master. Each reproducer calls the real
Julia functions, and each cause line is unchanged at `eb844b8ebd`.

## Perf and caching leads, ranked

Each lead is a hypothesis to measure, not a claimed speedup. Every lead's measurement plan is
also in its area's `compiler/PERF_LEADS.md` section ("Triage 2026-11-10").

| # | area | lead | verdict | measurement plan |
|---|------|------|---------|------------------|
| 1 | inlining | Clamp to never-inline above 3968 (finding 2) | survives, downstream trigger | Run GPUCompiler test kernels and some KernelAbstractions kernels through a `GPUInterpreter` with `always_inline = true` (code_typed only). Count the `:invoke`s left, with and without a clamp that saturates at 3968. |
| 2 | loading | Directory include `st_size` (finding 4) | survives | Use julia-code-search to count packages that pass a directory to `include_dependency`. Copy one precompiled depot from ext4 to tmpfs and count `:fsize_changed` reasons, before and after a patch that skips the size for directories. |
| 3 | loading | Depot shadowing (finding 5) | survives, niche | Time `using` in sessions 2 and 3 of the reproducer, with and without a patch that prefers the depot holding `modspec.path`. |
| 4 | escape | `getaliases` scans every index; missed grandchildren cost extra passes | plausible | Profile `Compiler/test/EscapeAnalysis.jl` and a generated 500-`Ref` loop function. Report the share of samples in `getaliases` and the number of passes, with and without a member list per root. |
| 5 | slot2ssa | Linear `in` in `compute_live_ins` and the IDF | plausible for huge functions only | Time `construct_ssa!` on generated functions with N blocks and M slots (100 to 1000 each), with and without `BitSet`. Profile one large generated JuMP or MTK method; drop the lead if `construct_ssa!` is under 1% of optimizer time. |
| 6 | loading | `cachepath_cache` read but not filled | real, small | Make 100 `Base.isprecompiled` calls over a 300-package manifest with an empty dict and with a reused one; count `stat` calls with strace. |
| 7 | cacheresult | Vararg-tail key not reused (finding 8) | measured: 0.04% on Base | Repeat the count on a package image's method instances; drop the lead if under 1%. |
| 8 | cacheresult | Local cache keeps optimized source that the global cache drops | memory only | `Base.summarysize` of the inference cache after a large `typeinf_frame`, with and without `discard_optimized_result` on the local path. First check that local inlining never reads that source. |
| 9 | loading | Candidates with equal mtimes tried in listing order | small | On a depot unpacked from a tarball, count "Rejecting" lines with `JULIA_DEBUG=loading`, with ties sorted by name and without. Drop if under 1 ms per `using`. |
| 10 | loading | `compilecache_freshest_path` and `require` differ across depots | no wrong load | With stacked depots, strace a no-op `Pkg.precompile()` to count files the driver opens or touches that `using` never reads. |
| 11 | escape | Shared `Liveness` sets mutated in place | effect unproven | Copy shared sets before writing and diff the finalizer-inlining IR in `Compiler/test/inline.jl`; drop if nothing changes. |
| 12 | inlining | `llvmcall` costs 20 (finding 11) | tiny | Count methods in SIMD.jl or VectorizationBase within 10 per llvmcall of the threshold. |
| 13 | cacheresult | `is_result_constabi_eligible` runs twice | tiny | Count the calls during a sysimage build; drop if under 10 ms in total. |
| 14 | inlining | `ifelse(c, x, x)` on a global not folded; `Const` result skips rewrites | hypotheses | Count both shapes in optimized sysimage IR; drop if only a handful. |
| 15 | slot2ssa | `first_insert_for_bb` rescans; phis for `@isdefined`-only slots | not measurable or rare | None planned unless lead 5's profile shows them. |
| 16 | cacheresult, escape | `maybe_compress_codeinfo` drop branch is dead for optimized sources; `⊑ₑ` slow path is dead in the analysis | simplifications | None; these are clarity changes. |

## Commits

Each worktree has one local commit, "Compiler: Triage <area> findings", that changes only the
area's bug yamls, reproducers and `PERF_LEADS.md` section. This file is part of the loading
commit. Nothing was pushed, and nothing was written to GitHub.
