# Memory-safety entry review (fixed criteria)

This procedure checks Lean proofs that claim unchecked array and pointer accesses
in Julia Base are in bounds. Work from the package root and read the pinned
master source with
`git -C <julia-source-root> show f755f49a9e41380d7da126b3c1db9fe7f83dd027:<path>`.
Review the source and proofs without executing Lean or Julia.

For every registry entry with id `memsafety-*` and status `proven` in
`JuliaLean/MemSafety/G{GROUP}.lean`, read its `prop` definition (follow every
definition it uses, including ones imported from other areas) and the Julia
source lines the entry and its sites in `memsafety/sites-{GROUP}.tsv` cite.
Then answer three questions:

1. MODEL: Does the proposition contain a Lean function that computes the index
   (or pointer offset) the Julia code uses at the unchecked access, from the
   same inputs the Julia function receives, by mirroring the Julia statements
   between the function's entry and the access (every branch, check, loop
   bound and arithmetic step that affects the index)? Answer no if the index
   is a bare universally quantified variable, or if only a formula from one
   line is modelled while earlier statements that constrain it are not.
2. HYPOTHESES: Is every hypothesis of the proposition one of: a type or
   representation invariant of an argument (for example `length(a.ref.mem)`
   bounds, a Dict's power-of-two slot count) that is itself proven elsewhere
   in this repository or stated in Julia's documentation (quote it); or a
   precondition stated in the docstring of the public function (quote it)?
   Answer no if any hypothesis restates the conclusion, or assumes that an
   index, offset or span lies inside the array (for example `start + count ≤
   len`) without that fact being derived from the modelled Julia code.
3. COVERAGE: Does the entry cover every site that its rows in
   `memsafety/sites-{GROUP}.tsv` attribute to it, including every public
   caller path that reaches the function with unchecked arguments? Answer no
   and name the uncovered site or caller otherwise.

The verdict is FAITHFUL only if all three answers are yes; otherwise HOLLOW.
Be strict: when unsure, answer no and say what is missing.

Write `memsafety/review-{GROUP}.tsv` with header
`entry	verdict	model	hypotheses	coverage	reason`, one row per entry,
`yes`/`no` in the three answer columns, and a one-sentence reason that names
the missing statement, hypothesis or site for every `no`. Report the totals as
`REVIEW {GROUP} FAITHFUL <n> HOLLOW <m>`.
