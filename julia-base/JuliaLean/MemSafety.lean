import JuliaLean.MemSafety.G1
import JuliaLean.MemSafety.G2
import JuliaLean.MemSafety.G3
import JuliaLean.MemSafety.G4
import JuliaLean.MemSafety.G5
import JuliaLean.MemSafety.G6

namespace JuliaLean.MemSafety

open JuliaLean.Registry

/-- Registry entries of this area; group `G<n>` covers `memsafety/sites-<n>.tsv`. -/
def entries : List Entry :=
  G1.entries ++ G2.entries ++ G3.entries ++ G4.entries ++ G5.entries ++ G6.entries

end JuliaLean.MemSafety
