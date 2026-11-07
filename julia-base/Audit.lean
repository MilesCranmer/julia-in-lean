import JuliaLean
import JuliaLean.Registry.Audit

/-!
Audit of the property registry. Run with `lake env lean Audit.lean`; any failure
raises an error, so the command exits nonzero. Open `todo` entries are listed as
`TODO <id>` lines and counted, but do not fail the audit.

Checks, for every registry entry:
* ids are unique;
* `prop` is a closed, universe-monomorphic `Prop` constant;
* `thm` is a theorem whose type is `prop` (proven) or `¬ prop` (refuted);
* `thm` depends only on `propext`, `Classical.choice`, and `Quot.sound`;
* refuted entries record a duplicate-issue search result in `issue`.

It prints `REFUTED <id>` lines used by the reproducer runner for Base runtime
refutations (`scripts/run-repros.sh`).
-/

#eval auditEntries JuliaLean.Registry.all
