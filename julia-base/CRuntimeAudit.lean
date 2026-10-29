import Lean
import JuliaLean.Registry.Generality
import JuliaLean.CRuntime

open Lean Meta

def cruntimeStandardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def cruntimeRuntimeAxiomModule : Name := `JuliaLean.Runtime.Axioms

def cruntimeAxiomAllowed (env : Environment) (ax : Name) : Bool :=
  cruntimeStandardAxioms.contains ax ||
    match env.getModuleIdxFor? ax with
    | some idx => env.header.moduleNames[idx.toNat]? == some cruntimeRuntimeAxiomModule
    | none => false

#eval show MetaM Unit from do
  let env ← getEnv
  let entries := JuliaLean.CRuntime.entries
  let mut failures : Array String := #[]
  let mut seen : Std.HashSet String := {}
  for e in entries do
    if seen.contains e.id then
      failures := failures.push s!"{e.id}: duplicate id"
    seen := seen.insert e.id
    if e.juliaFile.isEmpty then
      failures := failures.push s!"{e.id}: Julia source file is empty"
    if e.juliaFns.isEmpty then
      failures := failures.push s!"{e.id}: Julia function list is empty"
    if e.source.isEmpty then
      failures := failures.push s!"{e.id}: source path is empty"
    if e.statement.isEmpty then
      failures := failures.push s!"{e.id}: statement is empty"
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
      unless cruntimeAxiomAllowed env ax do
        failures := failures.push s!"{e.id}: {thm} uses disallowed axiom {ax}"
    if e.status == .refuted then
      if e.issue.isEmpty then
        failures := failures.push s!"{e.id}: refuted entry has no duplicate-issue search result"
      match e.refutationEvidence with
      | .runtime => IO.println s!"CRUNTIME-REFUTED-RUNTIME {e.id}"
      | .modelCounterexample => IO.println s!"CRUNTIME-REFUTED-MODEL {e.id}"
    else
      IO.println s!"CRUNTIME {e.id} {repr e.status}"
  unless failures.isEmpty do
    for f in failures do
      IO.println s!"FAIL {f}"
    throwError m!"CRuntime audit failed with {failures.size} problem(s)"
  IO.println "CRUNTIME AUDIT OK"
