import JuliaLean.Registry.Types
import JuliaLean.StringsCovA.BasicPromises

namespace JuliaLean.StringsCovA.BasicRebuiltRegistry

open JuliaLean.Registry

private def rawEntries : List Entry := []

private def rebuiltPrefix : Lean.Name :=
  match ``BasicRebuilt.SizeofProperty with
  | .str pre _ => pre
  | name => name

private def promisesPrefix : Lean.Name :=
  match ``BasicPromises.SizeofProperty with
  | .str pre _ => pre
  | name => name

private def rewriteName (name : Lean.Name) : Lean.Name :=
  match name with
  | .str pre suffix =>
      if pre == rebuiltPrefix then .str promisesPrefix suffix else name
  | _ => name

private def rewriteEntry (entry : Entry) : Entry :=
  { entry with
    prop := rewriteName entry.prop
    thm := entry.thm.map rewriteName }

def entries : List Entry := rawEntries.map rewriteEntry

end JuliaLean.StringsCovA.BasicRebuiltRegistry
