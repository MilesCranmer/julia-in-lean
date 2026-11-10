# Response to the review of the loading cache-file rows

The six HOLLOW rows are fixed by mirror fixes in `JuliaLean/base/loading.lean` and by new or
strengthened statements. The new statements are in `JuliaLean/Proofs/base/loading/accept.lean`
(registered as `Cachefile.acceptEntries`); the strengthened ones are in `cachefile.lean`. No
statement was weakened. The entries for other methods were removed from the 2682 and 4802 rows;
each of them is still listed on its own method's row.

Most of the new statements use `OkRun o m Q`: every run of `m`, from any state, returns normally
with a value satisfying `Q`. Unlike `AllOk`, a function that always throws, never returns or
always rejects does not satisfy it. The `walk_ok` tactic proves these by following the body: it
must show that each callee returns, from a hypothesis in the context.

Model changes (reviewed against pinned f755f49), all difftested again (results below):

- `_cacheflag_to_uint8`: `f` is an `Int` after the first `|=` and the one `UInt8` conversion is the
  `::UInt8` return (base/loading.jl:2012-2020). The model used to convert after every `|=`.
- `stale_cachefile`: `Dict{PkgId, UInt64}(modules)` keeps the last entry of a repeated key
  (base/loading.jl:5019); the model took the first. The `@assert` on a preloaded dependency
  (base/loading.jl:5029) is modelled. `PkgId("")` (base/loading.jl:4917, 5004) is the literal
  `⟨none, ""⟩`, no longer the abstract `ops.emptyPkgId`.
- `_include_dependency!`: the recorded `-1.0` (base/loading.jl:2702) is the literal, no longer the
  abstract `ops.minusOneMtime`.

| line | function | change | what is now pinned |
|---|---|---|---|
| 2012 | `_cacheflag_to_uint8` | mirror fix; new `compiler-loading-cacheflags-byte-layout` | The exact byte `p + 2d + 8c + 32i + 64o` for fields in `0:3` (the `OOICCDDP` comment at line 1955), as an equation on the function. The row note no longer claims the opposite of the model. `loading-cacheflags-byte-encoding` stays todo: it is about a separate model (`Models1Group9.Flags.toUInt8`) from another area. Out-of-range fields are not stated (see the row note). |
| 2682 | `_include_dependency!` | new `compiler-loading-include-dependency-record` | Equations for both branches: the resolved path (`abspath`, or `normpath(joinpath(dirname(prev), _path))`); while tracking, the exact `recordDependency` call under `require_lock` with `(mod, path, UInt64(filesize), CRC of the file or of join(readdir), -1.0)`, or `(mod, path, 0, 0, mtime)` without `track_content`; otherwise no record and the two `SystemError` branches; the return value `(path, prev)`. Also `include_mtime_recorded(-1.0) = false`, so the checker compares size and hash for these records, which links the refuted `compiler-loading-dir-include-size` to the recorded `filesize` of a directory. |
| 3041 | `maybe_loaded_precompile` | statement restated as an equation | The run from every state returns `some (.ok (find? ...), s)`: the first module with the requested build id, `nothing` otherwise, and the state (`require_lock` count included) unchanged. A version that throws or diverges fails it. |
| 4802 | `any_includes_stale` | precision restated with `OkRun`; soundness strengthened | `compiler-loading-any-includes-stale-precise` now says the call returns, with false, on unchanged includes; throwing or looping on them fails it. `compiler-loading-any-includes-stale-sound` now also carries the `startswith(_f, Sys.STDLIB)` condition and the `in_package_store` condition (as whatever those calls guarantee when they answer true), so it is no longer weaker than the code at lines 4815 and 4845. Unrelated entries removed from the row. |
| 4916 | `stale_cachefile(modspec, cachefile)` | new `compiler-loading-stale-cachefile-modspec-accepts` | The method accepts every cache that passes the checks, with no hypothesis on the cache's package or build id, with `stalecheck = true`, and with the given flags or the result of `CacheFlags()` when none are given. The always-stale function fails it, and so would forwarding any other package id or build id. |
| 4919 | `stale_cachefile` | new `compiler-loading-stale-cachefile-accepts`; `-rejects` extended | Acceptance: when every check passes, the call returns a fresh verdict (`OkRun`), so the always-stale function fails it. The hypotheses cover the header, flags, coverage, package id, build id, syntax version, pkgimage checks, each required module (loaded with its recorded identity and build id, or locatable), the source path, package identities, includes, checksums and preferences. `-rejects` gains the syntax-version check. Walks for the pkgimages-disabled, CPU-target and package-id rejections did not finish within 3M heartbeats and were dropped. |

Still not stated, on purpose and noted in the rows:

- Rejection by the checks inside loops (`julia_version`, `dep_loaded_incompatible`, `dep_missing`,
  `dep_buildid_mismatch`, `dep_identity_changed`, the two coverage loops), and `pkgid_mismatch`,
  `pkgimages_disabled`, `cpu_target` and `ocachefile_missing`.
  The `AllOk` loop lemma does not record that one element forced an early return; this needs a
  second loop lemma.
- Acceptance with a pinned concrete dependency, with the source path accepted only after
  `fixup_stdlib_path`, with a dependency already in `loaded_precompiles` and `stalecheck=false`,
  and with a coverage mismatch accepted as a plain cache.

The callees of `stale_cachefile` that are model functions with their own rows
(`parse_cache_header`, `match_cache_coverage`, `check_clone_targets`, `any_includes_stale`,
`checksums_invalid_io`, `stale_prefs`, `maybe_root_module`, `maybe_loaded_precompile`) appear in
the acceptance statement as hypotheses that each returns a passing value.

On the refuted entry: agreed that the docstring promises a recompile if the content changes, not
only if it changes, so `compiler-loading-dir-include-size` stays a P2 needless-recompile lead.

Checks:

- `difftest/base/loading.jl` after the model fixes, pinned Julia 1.15.0-DEV.184 (f755f49a9e41):
  seeds 1, 2 and 3, 17000 / 17000 agree each.
- `repro/compiler-loading-dir-include-size.jl` on the pinned Julia still prints
  `REPRODUCED compiler-loading-dir-include-size`.
- `bash scripts/audit.sh`: `AUDIT OK`, 8986 entries (7189 proven, 761 refuted, 1036 todo).
  `scripts/check_bugs.py`: BUGS 709, PROBLEMS 0.
- The new `accept.lean` builds in about 2.5 minutes with a 2.6 GB peak. An earlier version that
  closed the dependency-loop branches with `grind` peaked over the 12 GB cap; the loop hypothesis
  is now turned into implications in the proof, and `simp_all` closes those branches.
- Axioms: propext, Classical.choice and Quot.sound only.
