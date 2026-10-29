import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Dicts.RangeUnique
import JuliaLean.Dicts.Validation
import JuliaLean.Dicts.Lossy
import JuliaLean.Dicts.Persistent
import JuliaLean.Dicts.ProofReach
import JuliaLean.Dicts.ProofSetAlgebra

namespace JuliaLean.Dicts

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "dicts-persistentdict-objectid-collision", juliaFile := "base/hamt.jl",
    juliaFns := ["PersistentDict(::PersistentDict, key, val)", "HAMT.insert!"],
    statement := "Setting a key on any PersistentDict succeeds and the key then maps to the value (it behaves like an IdDict).",
    source := "PersistentDict docstring base/dict.jl:945-946", status := .refuted,
    prop := ``Persistent.PersistentSetGet, thm := some ``Persistent.persistentSetGet_refuted,
    issue := "#54740 (open, duplicate)",
    notes := "Both versions: PersistentDict{Any,Int}(8722453200027809036 => 1, 0x0000000000000001 => 2) throws ErrorException(\"Perfect hash collision\"); the keys are !== with equal objectid (objectid of Int64/UInt64 is int64hash xor a type constant). IdDict stores both." }
]

end JuliaLean.Dicts
