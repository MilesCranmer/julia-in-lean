import JuliaLean.Registry.Types

namespace JuliaLean.Registry

open Lean Meta

private def declarationModule (name : Name) : MetaM Name := do
  let env ← getEnv
  unless (env.find? name).isSome do
    throwError "registry metadata: declaration {name} does not exist"
  let some idx := env.getModuleIdxFor? name |
    throwError "registry metadata: declaration {name} has no imported module"
  let some moduleName := env.header.moduleNames[idx.toNat]? |
    throwError "registry metadata: invalid module index for declaration {name}"
  pure moduleName

private def metadataRow (e : Entry) : MetaM Json := do
  let propertyModule ← declarationModule e.prop
  let (status, theoremName, theoremModule) ← match e.status, e.thm with
    | .todo, none => pure ("todo", none, none)
    | .proven, some name => pure ("proven", some name, some (← declarationModule name))
    | .refuted, some name => pure ("refuted", some name, some (← declarationModule name))
    | .todo, some _ => throwError "registry metadata: todo entry {e.id} has a theorem"
    | _, none => throwError "registry metadata: settled entry {e.id} has no theorem"
  pure <| Json.mkObj [
    ("id", toJson e.id),
    ("status", toJson status),
    ("julia_file", toJson e.juliaFile),
    ("julia_functions", toJson e.juliaFns),
    ("statement", toJson e.statement),
    ("source", toJson e.source),
    ("property", toJson e.prop),
    ("theorem", toJson theoremName),
    ("property_module", toJson propertyModule),
    ("theorem_module", toJson theoremModule)]

/-- Export registry entries as JSON lines using declaration modules from the environment. -/
def printMetadataRows (es : List Entry) : MetaM Unit := do
  let rows ← es.mapM metadataRow
  for row in rows do
    IO.println row.compress

end JuliaLean.Registry
