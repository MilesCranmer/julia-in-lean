# Response to the review of Compiler/src/typeinfer.jl

Both HOLLOW rows now have a new entry that pins the function on every input. The statements and
proofs are in `JuliaLean/Proofs/Compiler/src/inferenceresult/Exact.lean` (registered as
`exactTypeinferEntries`). The earlier entry `compiler-cacheresult-discard-compress-agree` is kept
unchanged. The model was not changed. All new entries are proven, and `scripts/audit.sh` ends with
`AUDIT OK`.

| line | function | new entry | what is now pinned |
|---|---|---|---|
| 592 | keep_source_for_output | `compiler-cacheresult-keep-source-exact` | `keep_source_for_output(mi)` is true exactly when `jl_generating_output()` is nonzero and `isa_compileable_sig(mi)` holds. When not generating output it is false, whatever `isa_compileable_sig` would answer. An always-false version fails the first clause. |
| 595 | maybe_compress_codeinfo | `compiler-cacheresult-maybe-compress-exact` | All three results. Toplevel code (`mi.def` not a `Method`) is returned as the `CodeInfo`, so compressing toplevel code fails the third clause. For a method, the result is `nothing` exactly when trees may be discarded, the source is not inlineable, `precompile_keep_ir` is off and `keep_source_for_output` is false. It is the compressed `String` exactly when `may_compress` holds and the source is neither dropped nor kept by `precompile_keep_ir`. A version that never compresses fails the second clause. |

The FAITHFUL rows (483, 582, 1537) were not changed. `keep_source_for_output`'s true branch is
still not difftested, because `jl_generating_output()` is 0 in the difftest process; the new entry
is about the model, which takes both answers as inputs.
