import JuliaLean.base.accumulate
import JuliaLean.base.range

namespace JuliaLean.Proofs.base.accumulate
set_option maxRecDepth 4096

open JuliaLean JuliaLean.base.accumulate

private def scalarIndex (axes : List (List JInt64)) (indices : List JInt64) : Bool :=
  axes.length == indices.length && (axes.zip indices).all (fun (axis, index) => axis.contains index)

private def readCell (axes : List (List JInt64)) (indices : List JInt64) : AccResult Unit :=
  if scalarIndex axes indices then .ok () else .error (.julia .boundsError)

private def linearIndices (axes : List (List JInt64)) : List JInt64 :=
  JuliaLean.base.range.unitRangeList (JInt.wrap .i64 1)
    (JInt.wrap .i64 ((axes.map List.length).prod : Nat))

/-- A constant-Unit array supplies the complete installed operations interface.
Its scalars and arithmetic cannot fail; checked indexing alone detects unsafe accesses. -/
private def unitArrayOps : AccumulateOps Unit (List (List JInt64)) (List (List JInt64)) JInt64
    Unit Unit Unit Unit Nat where
  arrays := {
    axes := id
    outputAxes := id
    axesEqual := fun a b => a == b
    linearIndices := linearIndices
    outputLinearIndices := linearIndices
    linearIndicesEqual := fun a b => a == b
    isEmpty := fun axes => axes.any List.isEmpty
    isVector := fun axes => axes.length == 1
    get := readCell
    getOutput := readCell
    set := fun axes indices _ => do let _ ← readCell axes indices; pure axes
    getLinear := fun axes index => readCell [linearIndices axes] [index]
    setLinear := fun axes index _ => do let _ ← readCell [linearIndices axes] [index]; pure axes
    copyTo := fun out input => if out == input then .ok out else .error (.dimensionMismatch "axes") }
  apply := fun _ _ _ => .ok ()
  reduceFirst := fun _ _ => .ok ()
  applyInit := fun _ _ _ => .ok ()
  similarPromoted := fun _ input _ => .ok input
  iteratorAccumulate := fun _ input _ => .ok input
  dimPositive := fun dim => decide (0 < dim)
  dimGreaterThan := fun dim rank => decide (rank < dim)
  dimEquals := fun dim rank => dim == rank
  dimToNat := fun dim => .ok dim
  oneDim := 1
  oneIndex := JInt.wrap .i64 1
  indexSucc := fun index => index + JInt.wrap .i64 1
  indexPred := fun index => index - JInt.wrap .i64 1
  indexRange := JuliaLean.base.range.unitRangeList
  prefixFirst := fun _ => ()
  prefixStep := fun _ _ _ => .ok ()
  prefixApply := fun _ _ _ => .ok ()
  prefixCombine := fun _ _ _ => .ok ()
  sumOp := ()
  productOp := ()
  arithmeticStyle := fun _ => .other
  emptyKeywords := ⟨[], none, fun _ => ""⟩

def AccumulateDimsAccessesInBounds : Prop :=
  ∀ (axes : List (List JInt64)) (dim : Nat) (init : Option Unit),
    (∀ axis ∈ axes, ∃ first last, axis = JuliaLean.base.range.unitRangeList first last) →
    accumulateAlongDimension unitArrayOps () axes axes dim init ≠ .error (.julia .boundsError)

private theorem unitRange_nonempty (first last : JInt64) (h : first.val ≤ last.val) :
    ∃ tail, JuliaLean.base.range.unitRangeList first last = first :: tail := by
  unfold JuliaLean.base.range.unitRangeList
  rw [ite_eq_right (by omega)]
  rw [show (last.val - first.val + 1).toNat = (last.val - first.val).toNat + 1 by omega,
    List.range_succ_eq_map, List.map_cons]
  have hz : first + JuliaLean.base.range.jint (0 : Int) = first := by
    apply Subtype.ext
    change wrapInt .i64 (first.val + 0) = first.val
    simpa using wrapInt_of_inRange .i64 first.val first.property
  simp only [Int.natCast_zero] at *
  rw [hz]
  exact ⟨_, rfl⟩

private theorem rest_reads_outside (index bad : JInt64) (tail : List JInt64)
    (hneq : bad ≠ index) :
    accumulateFirstAxisRest unitArrayOps () [[index]] [[index]] () [] (bad :: tail) =
      .error (.julia .boundsError) := by
  have hr : readCell [[index]] [bad] = .error (.julia .boundsError) := by
    simp [readCell, scalarIndex, hneq]
  unfold accumulateFirstAxisRest
  change (do
    let value ← readCell [[index]] [bad]
    let next ← unitArrayOps.apply () () value
    let out ← unitArrayOps.arrays.set [[index]] [bad] next
    accumulateFirstAxisRest unitArrayOps () out [[index]] next [] tail) = _
  rw [hr]
  rfl

private theorem slice_reads_outside (index bad : JInt64) (tail : List JInt64)
    (hneq : bad ≠ index)
    (ht : JuliaLean.base.range.unitRangeList (index + JInt.wrap .i64 1) index = bad :: tail) :
    accumulateFirstAxisSlice unitArrayOps () [[index]] [[index]] [index] [] none =
      .error (.julia .boundsError) := by
  have hr : readCell [[index]] [index] = .ok () := by simp [readCell, scalarIndex]
  have hs : unitArrayOps.arrays.set [[index]] [index] () = .ok [[index]] := by
    change (do let _ ← readCell [[index]] [index]; pure [[index]]) = _
    rw [hr]
    rfl
  change (do
    let value ← readCell [[index]] [index]
    let first ← unitArrayOps.reduceFirst () value
    let out ← unitArrayOps.arrays.set [[index]] [index] first
    accumulateFirstAxisRest unitArrayOps () out [[index]] first []
      (JuliaLean.base.range.unitRangeList (index + JInt.wrap .i64 1) index)) = _
  simp only [hr, hs, show unitArrayOps.reduceFirst () () = .ok () from rfl,
    bind, Except.bind]
  rw [ht]
  exact rest_reads_outside index bad tail hneq

private theorem singleton_reads_outside (index bad : JInt64) (tail : List JInt64)
    (hneq : bad ≠ index)
    (ht : JuliaLean.base.range.unitRangeList (index + JInt.wrap .i64 1) index = bad :: tail) :
    accumulateAlongDimension unitArrayOps () [[index]] [[index]] 1 none =
      .error (.julia .boundsError) := by
  have hs := slice_reads_outside index bad tail hneq ht
  have hp : unitArrayOps.dimPositive 1 = true := rfl
  have ha : unitArrayOps.arrays.axes [[index]] = [[index]] := rfl
  have hb : unitArrayOps.arrays.outputAxes [[index]] = [[index]] := rfl
  have he : unitArrayOps.arrays.axesEqual [[index]] [[index]] = true := by
    simp [unitArrayOps]
  have hg : unitArrayOps.dimGreaterThan 1 1 = false := rfl
  have hn : unitArrayOps.dimToNat 1 = .ok 1 := rfl
  have hd : unitArrayOps.dimEquals 1 1 = true := rfl
  simp [accumulateAlongDimension, hp, ha, hb, he, hg, hn, hd,
    accumulateFirstAxisSlices, cartesianIndices, hs, bind, Except.bind]

set_option maxRecDepth 1000 in
private theorem extreme_axis_reads_outside : accumulateAlongDimension unitArrayOps () [[JInt.typemax .i64]]
    [[JInt.typemax .i64]] 1 none = .error (.julia .boundsError) := by
  have hwrap : JInt.typemax .i64 + JInt.wrap .i64 1 = JInt.typemin .i64 := by decide
  have hneq : JInt.typemin .i64 ≠ JInt.typemax .i64 := by decide
  have rangeHead : ∃ tail, JuliaLean.base.range.unitRangeList
      (JInt.typemax .i64 + JInt.wrap .i64 1) (JInt.typemax .i64) =
        JInt.typemin .i64 :: tail := by
    rw [hwrap]
    exact unitRange_nonempty _ _ (by decide)
  obtain ⟨tail, ht⟩ := rangeHead
  exact singleton_reads_outside _ _ tail hneq ht

theorem accumulateDimsAccessesInBounds_refuted : ¬ AccumulateDimsAccessesInBounds := by
  intro h
  have ha : ∀ axis ∈ ([[JInt.typemax .i64]] : List (List JInt64)),
      ∃ first last, axis = JuliaLean.base.range.unitRangeList first last := by
    intro axis haxis
    have heq : axis = [JInt.typemax .i64] := by simpa using haxis
    subst axis
    exact ⟨JInt.typemax .i64, JInt.typemax .i64, by decide⟩
  exact h [[JInt.typemax .i64]] 1 none ha extreme_axis_reads_outside

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-accumulate-offset-axis-overflow", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate!", "_accumulate!", "_accumulaten!"]
    statement := "Every unchecked access computed after the dimensional axis checks remains on the common input and output axis."
    source := "AbstractArray axis invariant; base/accumulate.jl:337-355,374-434"
    status := .refuted, prop := ``AccumulateDimsAccessesInBounds
    thm := some ``accumulateDimsAccessesInBounds_refuted
    issue := "none found (queries: accumulate offset axis overflow; accumulate typemax firstindex; accumulate custom axes bounds; PRs same)"
    notes := "The installed dimensional accumulate method evaluates first(axis)+1 using native wrapping arithmetic. A singleton typemax(Int) axis therefore reaches an out-of-axis read at typemin(Int). Both Julia versions reproduce with forced bounds checks." }
]

end JuliaLean.Proofs.base.accumulate
