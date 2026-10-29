import Lean
import JuliaLean.Registry.Generality
import JuliaLean.CRuntime.WorldStop

open Lean Meta

def worldStopAllowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show MetaM Unit from do
  let env ← getEnv
  for entry in JuliaLean.CRuntime.WorldStop.entries do
    if entry.status == .todo then
      throwError m!"{entry.id}: unsettled"
    if (← JuliaLean.Registry.countForallData 6 (mkConst entry.prop)) == 0 then
      throwError m!"{entry.id}: property quantifies over no input"
    let some theoremName := entry.thm
      | throwError m!"{entry.id}: missing theorem"
    let some (.thmInfo theoremInfo) := env.find? theoremName
      | throwError m!"{entry.id}: theorem not found"
    let expected := if entry.status == .proven then mkConst entry.prop else mkNot (mkConst entry.prop)
    unless ← isDefEq theoremInfo.type expected do
      throwError m!"{entry.id}: theorem type mismatch"
    for ax in ← collectAxioms theoremName do
      unless worldStopAllowedAxioms.contains ax do
        throwError m!"{entry.id}: disallowed axiom {ax}"
    if entry.status == .refuted && entry.issue.isEmpty then
      throwError m!"{entry.id}: missing duplicate search"
    IO.println s!"WORLDSTOP {entry.id} {repr entry.status}"
  IO.println "WORLDSTOP AUDIT OK"
