import JuliaLean.base.ryu.shortest
import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
def ryuExponentAccesses (x : JuliaLean.Float.F64) (compact : Bool) : List Access :=
  if JuliaLean.Float.F64.iszero x || JuliaLean.Float.F64.isnan x ||
      !JuliaLean.Float.F64.isfinite x then [] else
    let (output, nexp) := ryuReduceModel x
      (if compact then some (999999 : Int) else none)
    let olength := (ryuDecimalLength output).val
    let exp2 : Int := nexp + olength - 1
    let exp2 := if exp2 < 0 then -exp2 else exp2
    if 100 ≤ exp2 then [⟨100, exp2 / 10 + 1⟩]
    else if 10 ≤ exp2 then [⟨100, exp2 + 1⟩]
    else []

def ryuSmallExponentAccesses (x : RyuSmall) (compact : Bool) : List Access :=
  if x.zero || !x.finite then [] else
    let (output, nexp) := ryuSmallReduce x
      (if compact then some (999999 : Int) else none)
    let olength := (ryuDecimalLength output).val
    let exp2 : Int := nexp + olength - 1
    let exp2 := if exp2 < 0 then -exp2 else exp2
    if 100 ≤ exp2 then [⟨100, exp2 / 10 + 1⟩]
    else if 10 ≤ exp2 then [⟨100, exp2 + 1⟩]
    else []

def RyuExponentTableInBounds : Prop :=
  (∀ x compact, AllInBounds (ryuExponentAccesses x compact)) ∧
  (∀ x compact, AllInBounds (ryuSmallExponentAccesses x compact))





end JuliaLean.MemSafety.G2
