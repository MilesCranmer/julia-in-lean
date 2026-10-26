import JuliaLean.Streams.Coverage
import JuliaLean.Registry.Types

namespace JuliaLean.Streams.Methods

open JuliaLean.Registry

def methodEntry (file slug : String) (line endline : Nat) (signature statement : String)
    (prop theoremName : Lean.Name) : Entry :=
  { id := "streams-method-" ++ slug ++ "-l" ++ toString line
    juliaFile := file
    juliaFns := [signature]
    statement := statement
    source := file ++ ":" ++ toString line ++
      (if line = endline then "" else "-" ++ toString endline)
    status := .proven
    prop := prop
    thm := some theoremName }

end JuliaLean.Streams.Methods
