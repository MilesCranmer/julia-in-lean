import JuliaLean.MultidimCov.Model

namespace JuliaLean.MultidimCov.LogicalFaithfulCore

open JuliaLean

structure Mask where
  id : Nat
  axes : List JuliaLean.MultidimCov.Axis
  values : List Bool
  deriving Repr, DecidableEq

inductive IndexKind where | linear | cartesian (rank : Nat) deriving Repr, DecidableEq

structure LogicalIndex where
  mask : Mask
  cachedCount : Nat
  kind : IndexKind
  deriving Repr, DecidableEq

def construct (kind : IndexKind) (mask : Mask) : LogicalIndex :=
  { mask, cachedCount := mask.values.count true, kind }

inductive Output where
  | linear (index : Nat)
  | cartesian (coordinates : List I64)
  deriving Repr, DecidableEq

def linearToCartesian (axes : List JuliaLean.MultidimCov.Axis) (position : Nat) : List I64 :=
  let rec go : List JuliaLean.MultidimCov.Axis → Nat → List I64
    | [], _ => []
    | axis :: rest, n =>
        let len := max axis.len 1
        axisElem axis (n % len) :: go rest (n / len)
  go axes position

def outputAt (index : LogicalIndex) (position : Nat) : Output :=
  match index.kind with
  | .linear => .linear (position + 1)
  | .cartesian _ => .cartesian (linearToCartesian index.mask.axes position)

def collect (index : LogicalIndex) : List Output :=
  ((index.mask.values.zipIdx).filterMap fun pair =>
    if pair.1 then some (outputAt index pair.2) else none).take index.cachedCount

def promisedOutputs (index : LogicalIndex) : List Output :=
  (index.mask.values.zipIdx).filterMap fun pair =>
    if pair.1 then some (outputAt index pair.2) else none

def TracksCurrentMask : Prop := ∀ index : LogicalIndex, collect index = promisedOutputs index

theorem tracksCurrentMask_refuted : ¬ TracksCurrentMask := by
  intro h
  let axis : JuliaLean.MultidimCov.Axis :=
    { first := JInt.lit .i64 1, step := JInt.lit .i64 1, len := 2 }
  let mask : Mask := { id := 1, axes := [axis], values := [true, true] }
  let index : LogicalIndex := { mask, cachedCount := 1, kind := .linear }
  have bad := h index
  simp [collect, promisedOutputs, outputAt, index, mask] at bad

end JuliaLean.MultidimCov.LogicalFaithfulCore
