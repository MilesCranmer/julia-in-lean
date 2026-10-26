# Method-coverage review (fixed criteria)

This procedure checks whether Lean registry entries model the Julia Base
methods they claim to cover. Work from the package root and read the pinned
master source with `git -C <julia-source-root> show bbfa0ce4150:<path>`.
Review the source and proofs without executing Lean or Julia.

Your input is the coverage file `coverage/methods/{FILE}.tsv`. For every row
with status `modelled`, read the Julia method at the row's `line` to `endline`,
and for each registry id in the row's `entry`, read the entry in
`JuliaLean/*.lean`, its `prop` definition, and every definition it uses
(including ones imported from other areas). Then answer three questions:

1. MIRROR: Does the proposition use a Lean function that mirrors THIS method's
   body (its branches, checks, loops, arithmetic and calls, in the same order),
   rather than a different method of the same name, a hand-written
   specification, or a bare variable standing for the method's result?
2. PROPERTY: Does the proposition state something about this method's
   behaviour that its docstring, the manual, or an obvious invariant promises,
   quantified over all allowed inputs (not only worked examples), with
   hypotheses that are only type invariants or documented preconditions?
3. SETTLED: Is the entry proven or refuted, and for a refuted entry, does a
   reproducer `repro/<id>.jl` exist?

For every row with status `excluded`, answer one question instead: does the
note's reason truly apply to this method (for example, a `no-behaviour:` row
must have no observable behaviour to state)?

The verdict is FAITHFUL only if every answer is yes; otherwise HOLLOW. Be
strict: when unsure, answer no and say what is missing.

Write `coverage/review/{FILE}.tsv` with header
`line	name	verdict	mirror	property	settled	reason`, one row per
modelled or excluded row, `yes`/`no`/`-` in the answer columns, and a
one-sentence reason naming what is missing for every `no`. Report the totals as
`REVIEW {FILE} FAITHFUL <n> HOLLOW <m>`.
