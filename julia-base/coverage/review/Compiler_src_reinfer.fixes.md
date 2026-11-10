# Fixes for the review of `Compiler/src/reinfer.jl`

Responses to the HOLLOW rows of `Compiler_src_reinfer.tsv` (review commit 1416952).

## reinfer.jl:103, `binding_changed_since_require_world`

Added `BindingFastPathAgrees` (proven), so the entry now states `BindingQueriesBoth`. The oracle
is constrained by `LeafRangePromise`, which is read from `binding_access_range`
(`Compiler/src/abstractinterpretation.jl:4241-4284`) and `walk_binding_partition` (`:4127-4140`).
For a binding whose newest partition is a leaf containing the world, the access range starts no
later than that partition. Under that promise, for a world at or after the require world in which
the newest partition is current, the function gives exactly the walk's answer
(`bindingChangedSlow`: `min_world(binding_access_range_at(b, world)) > require_world`). That is
the comment's claim that the fast path agrees with the walk. The difftest checks both the promise
(`leafpromise:holds`, none broken) and the agreement on the pinned Julia
(`fastpath:agree`, none disagreeing) on every `r.bindingChanged` case.

## reinfer.jl:119, `insert_backedges`; :128, `scan_new_code!`; :149, `verify_method_graph`

The soundness refutation now goes through `insert_backedges` itself. `compiler-reinfer-stale-min-world`
states `InsertBackedgesSound`: after `insert_backedges` runs over the loaded code instances,
every one that is valid in the current world has call edges whose lookup in that world gives the
recorded methods. `insertBackedgesSound_refuted` runs the whole `insertBackedges`
(`scanNewMethods`, `scanNewCode`, `verifyMethodGraph` with its assertions, `verifyMethod`,
`jlPromoteCiToCurrent`) on the `RuntimeConsistent` counterexample heap with `decide +kernel`. The
code instance ends valid from world 1 to `typemax`, but its call dispatches elsewhere in world 3.
On that run the assertions of `verify_method_graph` pass. We did not prove that they never fail
in general (the same open invariant as cycle handling below), and the row note says so.
`verifyMethodSound_refuted` (at `verify_method` level) remains as a lemma, and the bug yaml names
both.

## reinfer.jl:180, `needs_instrumentation`

Marked todo. The function only decides anything under code coverage or allocation logging, and
that branch is not modelled (`should_instrument`, debuginfo, `jl_codeinst_coverage_compatible`,
`gen_staged_sig`). Difftesting it would also need the pinned Julia run with coverage on. The
proven `compiler-reinfer-needs-instrumentation-off` stays, for the two early returns only, and
no row cites it now.

## reinfer.jl:221, `verify_method`

Marked todo. Soundness is refuted through it (the `insert_backedges` run above unfolds it), but
properties 3 (`compiler-reinfer-cycle-group`) and 4 (`compiler-reinfer-range-bounded`) are still
unproven. They need an invariant on the Tarjan stack over the whole state machine. As evidence,
not proof, the difftest now checks both on every `r.verifyMethod` case of the pinned verifier.
`range:bounded` counts root ranges inside `[require_world, validation_world]`, and
`cycle:consistent` counts pairs of members of one cycle of instances awaiting verification that
are not left one valid in the validation world and the other not. No violation was seen in the
runs recorded in the difftest header. A first version of the check also followed edges through
code instances that were already validated, and on seed 2 it reported 6 splits. Each of those
cycles went through an instance with `max_world = typemax` that calls one still awaiting
verification. The verifier stops at such an instance and the runtime does not build that shape,
so it is an artifact of the fake graphs. `CycleGroupConsistent` (its `CIEdge`) and the check now
follow only instances awaiting verification, and the statement compares validity in the
validation world rather than `max_world == 0`.

## reinfer.jl:540, `method_morespecific_recorded`

Added `MorespecificRecordedExact` (proven; the entry now states `InterferenceSetsExact`). When the
interference sets name heap methods, the function returns exactly
`m1 ≠ m2 ∧ m1 ∈ m2.interferences ∧ m2 ∉ m1.interferences`. An always-false function fails this.

## reinfer.jl:566, `promote_mi_to_current`

Added `PromoteMiExact` (proven; the entry states `PromoteMiBoth`). Both outcomes are stated. It
sets `dispatch_status := METHOD_SIG_LATEST_ONLY` if and only if the world counter is still
`world`, the method's interference set is nonempty, `minworld` is its `primary_world` and the bit
is absent. Otherwise the heap is unchanged. A no-op fails this.

## reinfer.jl:597, `newmethod_removed_silently`

Added `NewmethodRemovedSilentlyExact` (proven; the entry states `NewmethodRemovedSilentlyBoth`). The
answer is exactly `(!(meth ∈ m's set) || expected_is_minmax) && has_empty_set_cover &&
morespecific_cannot_cycle`. With the exact statements of those three below, the whole decision
is pinned. Still open, with no entry (noted on the entry): the comment's promise that acceptance
implies the full `ml_matches` result is unchanged. The oracle's `_methods_by_ftype` is
uninterpreted, so stating it needs a model of the `ml_matches` sort over the interference graph.

## reinfer.jl:638, `expected_is_minmax`

Added `ExpectedIsMinmaxExact` (proven). When `<:` and `method_morespecific_recorded` answer, it
returns, and returns true iff the three conditions of its comment hold. Both directions are
stated, so an always-false function fails it.

## reinfer.jl:664, `has_empty_set_cover`

Added `HasEmptySetCoverExact` (proven). It returns true iff some expected method has an empty
set, recorded-beats `m` and covers `ti`. Both directions are stated.

## reinfer.jl:688, `morespecific_cannot_cycle`

Added `MorespecificCannotCycleExact` (proven). It returns true iff every visible member of `m`'s
set has an empty set or has `m` in its own. Both directions are stated.

## reinfer.jl:894, `verify_invokesig`

Added `VerifyInvokesigExact` (proven; the entry states `VerifyInvokesigBoth`). When its lookups
answer and `expected` is present in the verification world, it changes no state, and it accepts
iff (egal ∧ latest-which), or (method table ∧ latest-which ∧ contributors ≠ 0), or
(method table ∧ `_findsup` returns `expected` ∧ nonempty range). So an invoke edge whose target is
unchanged is accepted, which is the precision direction. A verifier that always rejects fails it.
