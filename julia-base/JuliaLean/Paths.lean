import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Paths.Model
import JuliaLean.Paths.Props
import JuliaLean.Paths.Refute
import JuliaLean.Paths.Split
import JuliaLean.Paths.Relpath

namespace JuliaLean.Paths

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "paths-isdirpath-trailing", juliaFile := "base/path.jl"
    juliaFns := ["isdirpath"]
    statement := "isdirpath(p * \"/\") is true for every p."
    source := "base/path.jl:244 (isdirpath docstring)", status := .proven
    prop := ``IsdirpathTrailing, thm := some ``isdirpathTrailing_proven }
]

end JuliaLean.Paths
