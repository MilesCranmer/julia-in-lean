import JuliaLean.AbstractArrays.Model

/-! Deterministic differential corpus shared with `repro/abstractarrays-differential.jl`. -/

namespace JuliaLean.AbstractArrays.Validation

open JuliaLean JuliaLean.AbstractArrays

private def outI : Jl I64 → String
  | .ok x => s!"ok:{x.val}"
  | .error .boundsError => "error:BoundsError"
  | .error (.argumentError _) => "error:ArgumentError"
  | .error e => s!"error:{repr e}"

private def outA : Jl Axis → String
  | .ok a => s!"ok:{a.first.val}:{a.len}"
  | .error .boundsError => "error:BoundsError"
  | .error e => s!"error:{repr e}"

private def outB : Jl Bool → String
  | .ok b => toString b
  | .error (.argumentError _) => "error:ArgumentError"
  | .error .boundsError => "error:BoundsError"
  | .error e => s!"error:{repr e}"

private def outSlots : Jl (GVec Int) → String
  | .ok v => String.intercalate "," (v.slots.map fun x => match x with | some n => toString n | none => "undef")
  | .error .boundsError => "error:BoundsError"
  | .error e => s!"error:{repr e}"

private def outInts (xs : List I64) : String := String.intercalate "," (xs.map fun x => toString x.val)

def differential : IO Unit := do
  let sizes := [i64 2, i64 3]
  for d in [-1, 0, 1, 2, 3, 4] do
    IO.println s!"size {d} {outI (sizeDim sizes (i64 d))}"
    IO.println s!"axes {d} {outA (axesDim sizes (i64 d))}"
  let a3 := Axis.oneTo 3
  IO.println s!"scalar-int {checkScalar a3 (.integer (i64 1))}"
  IO.println s!"scalar-bool {checkScalar a3 (.unsupportedReal (i64 1))}"
  IO.println s!"to-bool {outI (ScalarIndex.toIndex (.unsupportedReal (i64 1)))}"
  IO.println s!"range {checkRange (Axis.oneTo 6) ⟨i64 2, i64 5, false⟩}"
  IO.println s!"empty-range {checkRange (Axis.oneTo 6) ⟨i64 7, i64 6, true⟩}"
  let axes := [Axis.oneTo 2, Axis.oneTo 3]
  IO.println s!"coords-full {checkCoords axes [.integer (i64 2), .integer (i64 3)]}"
  IO.println s!"coords-short {checkCoords axes [.integer (i64 2)]}"
  IO.println s!"coords-trail1 {checkCoords axes [.integer (i64 2), .integer (i64 3), .integer (i64 1)]}"
  IO.println s!"coords-trail2 {checkCoords axes [.integer (i64 2), .integer (i64 3), .integer (i64 2)]}"
  IO.println s!"linear-short {checkLinear axes (.integer (i64 2))}"
  IO.println s!"mask-good {checkMask axes axes}"
  IO.println s!"mask-bad {checkMask axes [Axis.oneTo 3, Axis.oneTo 2]}"
  let dest : GVec Int := ⟨i64 5, [some 0, some 0, some 0, some 0]⟩
  let src : GVec Int := ⟨i64 0, [some 7, some 8, some 9]⟩
  IO.println s!"copy {outSlots (dest.copyAll src)}"
  IO.println s!"copy-short {outSlots ((⟨i64 1, [some 9, some 9]⟩ : GVec Int).copyAll src)}"
  let ov := JuliaLean.ArrayOps.copyto [1, 2, 3, 4] (JInt.lit .i64 2) none
    (JInt.lit .i64 1) (JInt.lit .i64 3)
  IO.println s!"copy-overlap {match ov with | .ok xs => String.intercalate "," (xs.map toString) | .error _ => "error"}"
  let off : GVec Int := ⟨i64 (-1), [some 10, none, some 30]⟩
  IO.println s!"each {outInts off.eachIndex}"
  IO.println s!"assigned {outB (off.isAssigned (.integer (i64 (-1))))},{outB (off.isAssigned (.integer (i64 0)))},{outB (off.isAssigned (.integer (i64 1)))},{outB (off.isAssigned (.unsupportedReal (i64 1)))}"
  IO.println s!"require-normal {match requireOneBased axes with | .ok _ => "ok" | .error _ => "error"}"
  IO.println s!"require-offset {match requireOneBased [⟨i64 (-1), 3⟩] with | .ok _ => "ok" | .error _ => "error:ArgumentError"}"
  IO.println s!"similar {(GVec.similar (α := Int) 4).first.val}:{(GVec.similar (α := Int) 4).slots.length}"
  IO.println s!"vcat {String.intercalate "," ((vcatPromote id id [1, 2] [3, 4]).map toString)}"
  IO.println s!"hcat {match hcatPromote id id [1, 2] [3, 4] with | .ok rows => rows.length | .error _ => 0}"
  let r : GVec Int := ⟨i64 (-1), [some 1, some 2, some 3, some 4]⟩
  IO.println s!"reverse {outSlots (.ok r.reverse)}"
  IO.println s!"fill {outSlots (.ok (r.fill 6))}"
  IO.println s!"empty {(⟨i64 1, []⟩ : GVec Int).isEmpty},{r.isEmpty}"
  IO.println "COUNT 37"

#eval differential

end JuliaLean.AbstractArrays.Validation
