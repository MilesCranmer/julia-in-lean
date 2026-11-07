import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.path
import JuliaLean.Proofs.base.path.Props
import JuliaLean.Proofs.base.path.Refute
import JuliaLean.Proofs.base.path.Split
import JuliaLean.Proofs.base.path.Relpath

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
