import JuliaLean

/-!
Audit of the property registry. Run with `lake env lean Audit.lean`; any failure
raises an error, so the command exits nonzero.

Checks, for every registry entry:
* ids are unique;
* status is `proven` or `refuted` (`todo` fails);
* `prop` is a closed, universe-monomorphic `Prop` constant that quantifies over
  at least one data variable (no single worked examples);
* `thm` is a theorem whose type is `prop` (proven) or `¬ prop` (refuted);
* `thm` depends only on `propext`, `Classical.choice`, `Quot.sound`, and
  axioms declared in `JuliaLean.Runtime.Axioms`;
* refuted entries record a duplicate-issue search result in `issue`.

It prints `REFUTED <id>` lines consumed by `scripts/run-repros.sh`.
-/

open Lean Meta

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def runtimeAxiomModule : Name := `JuliaLean.Runtime.Axioms

def axiomAllowed (env : Environment) (ax : Name) : Bool :=
  standardAxioms.contains ax ||
    match env.getModuleIdxFor? ax with
    | some idx => env.header.moduleNames[idx.toNat]? == some runtimeAxiomModule
    | none => false

#eval show MetaM Unit from do
  let env ← getEnv
  let entries := JuliaLean.Registry.all
  let mut failures : Array String := #[]
  let mut seen : Std.HashSet String := {}
  let mut counts : Std.HashMap String Nat := {}
  for e in entries do
    let statusName := toString (repr e.status)
    counts := counts.insert statusName (counts.getD statusName 0 + 1)
    if seen.contains e.id then
      failures := failures.push s!"{e.id}: duplicate id"
    seen := seen.insert e.id
    if e.status == .todo then
      failures := failures.push s!"{e.id}: status todo"
      continue
    let some propInfo := env.find? e.prop
      | failures := failures.push s!"{e.id}: prop {e.prop} not found"; continue
    unless propInfo.levelParams.isEmpty do
      failures := failures.push s!"{e.id}: prop {e.prop} has universe parameters"
      continue
    let propExpr := mkConst e.prop
    unless ← isProp propExpr do
      failures := failures.push s!"{e.id}: {e.prop} is not a Prop"
      continue
    if (← JuliaLean.Registry.countForallData 6 propExpr) == 0 then
      failures := failures.push s!"{e.id}: property quantifies over no input"
    let some thm := e.thm
      | failures := failures.push s!"{e.id}: settled entry has no theorem"; continue
    let some (.thmInfo thmInfo) := env.find? thm
      | failures := failures.push s!"{e.id}: theorem {thm} not found"; continue
    unless thmInfo.levelParams.isEmpty do
      failures := failures.push s!"{e.id}: theorem {thm} has universe parameters"
      continue
    let expected := if e.status == .proven then propExpr else mkNot propExpr
    unless ← isDefEq thmInfo.type expected do
      failures := failures.push s!"{e.id}: type of {thm} is not {expected}"
      continue
    let axioms ← collectAxioms thm
    for ax in axioms do
      unless axiomAllowed env ax do
        failures := failures.push s!"{e.id}: {thm} uses disallowed axiom {ax}"
    if e.status == .refuted then
      if e.issue.isEmpty then
        failures := failures.push s!"{e.id}: refuted entry has no duplicate-issue search result"
      IO.println s!"REFUTED {e.id}"
  for (k, v) in counts.toList do
    IO.println s!"STATUS {k} {v}"
  IO.println s!"ENTRIES {entries.length}"
  unless failures.isEmpty do
    for f in failures do
      IO.println s!"FAIL {f}"
    throwError m!"audit failed with {failures.size} problem(s)"
  IO.println "AUDIT OK"
