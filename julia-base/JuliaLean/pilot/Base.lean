import Std
import JuliaLean.src.dispatch
import JuliaLean.pilot.corpus
import JuliaLean.pilot.base.boot
import JuliaLean.pilot.base.essentials
import JuliaLean.pilot.base.abstractarray
import JuliaLean.pilot.base.array
import JuliaLean.pilot.base.indices
import JuliaLean.pilot.base.multidimensional
import JuliaLean.pilot.base.tuple
import JuliaLean.pilot.base.range
import JuliaLean.pilot.base.anyall
import JuliaLean.pilot.base.ntuple
import JuliaLean.pilot.base.int
import JuliaLean.pilot.base.bool
import JuliaLean.pilot.base.float
import JuliaLean.pilot.base.number
import JuliaLean.pilot.base.promotion
import JuliaLean.pilot.base.operators
import JuliaLean.pilot.base.div
import JuliaLean.pilot.base.runtime_internals

/-!
Assembles all ported `Base` and corpus method bodies for the dispatch pilot.
-/

namespace JuliaLean.Pilot

open JuliaLean

def allBodies : Std.HashMap String Body :=
  Std.HashMap.ofList <|
    Corpus.bodies ++
    Base.Boot.bodies ++
    Base.Essentials.bodies ++
    Base.AbstractArray.bodies ++
    Base.Array.bodies ++
    Base.Indices.bodies ++
    Base.Multidimensional.bodies ++
    Base.Tuple.bodies ++
    Base.Range.bodies ++
    Base.AnyAll.bodies ++
    Base.NTuple.bodies ++
    Base.Int.bodies ++
    Base.Bool.bodies ++
    Base.Float.bodies ++
    Base.Number.bodies ++
    Base.Promotion.bodies ++
    Base.Operators.bodies ++
    Base.Div.bodies ++
    Base.RuntimeInternals.bodies

end JuliaLean.Pilot
