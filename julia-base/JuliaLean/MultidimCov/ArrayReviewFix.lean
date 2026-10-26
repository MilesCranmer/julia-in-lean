import JuliaLean.Registry.Types
import JuliaLean.Core

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

inductive ArrayLoopResult where
  | value (x : Int)
  | thrown
  deriving Repr, DecidableEq

def iteratorUpperBoundFull : List (Int × Bool) → ArrayLoopResult
  | [] => .thrown
  | (value, barrier) :: rest => if barrier then .value value else iteratorUpperBoundFull rest

def collectToFull (fits : Int → Bool) (set widen : List Int → Int → List Int)
    : List Int → List Int → List Int
  | destination, [] => destination
  | destination, value :: rest =>
      if fits value then collectToFull fits set widen (set destination value) rest
      else collectToFull fits set widen (widen destination value) rest

def growToFull (fits : Int → Bool) (push widen : List Int → Int → List Int)
    : List Int → List Int → List Int
  | destination, [] => destination
  | destination, value :: rest =>
      if fits value then growToFull fits push widen (push destination value) rest
      else growToFull fits push widen (widen destination value) rest

def reverseWindowFull (values : List Int) (start stop : Nat) : List Int :=
  values.take (start - 1) ++ (values.drop (start - 1) |>.take (stop - start + 1)).reverse ++
    values.drop stop

def IteratorUpperBehavior : Prop :=
  (∀ values : List Int, iteratorUpperBoundFull (values.map fun value => (value, false)) = .thrown) ∧
  (∀ (before : List Int) value (after : List (Int × Bool)),
    iteratorUpperBoundFull
      (before.map (fun x => (x, false)) ++ (value, true) :: after) = .value value)

theorem iteratorUpperBehavior : IteratorUpperBehavior := by
  unfold IteratorUpperBehavior
  constructor
  · intro values
    induction values <;> simp [iteratorUpperBoundFull, *]
  · intro before value after
    induction before <;> simp [iteratorUpperBoundFull, *]

def CollectToBehavior : Prop := ∀ fits set widen destination values,
  collectToFull fits set widen destination values =
    values.foldl (fun output value =>
      if fits value then set output value else widen output value) destination

theorem collectToBehavior : CollectToBehavior := by
  intro fits set widen destination values
  induction values generalizing destination with
  | nil => rfl
  | cons value rest ih =>
      by_cases h : fits value
      · simp [collectToFull, h, ih]
      · simp [collectToFull, h, ih]

def GrowToBehavior : Prop := ∀ fits push widen destination values,
  growToFull fits push widen destination values =
    values.foldl (fun output value =>
      if fits value then push output value else widen output value) destination

theorem growToBehavior : GrowToBehavior := by
  intro fits push widen destination values
  induction values generalizing destination with
  | nil => rfl
  | cons value rest ih =>
      by_cases h : fits value
      · simp [growToFull, h, ih]
      · simp [growToFull, h, ih]

def ReverseWindowBehavior : Prop := ∀ values start stop,
  1 ≤ start → start ≤ stop → stop ≤ values.length →
  reverseWindowFull values start stop =
    values.take (start - 1) ++ (values.drop (start - 1) |>.take (stop - start + 1)).reverse ++
      values.drop stop

theorem reverseWindowBehavior : ReverseWindowBehavior := by
  unfold ReverseWindowBehavior
  intros
  rfl

private def arrayFixEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def arrayReviewFixEntries : List Entry := [
  arrayFixEntry "multidimcov-array-iterator-upper-full" "_iterator_upper_bound(itr)" "The inference-only loop continues until its barrier becomes true or the iterator exhausts; it has no artificial fuel bound." "base/array.jl:805-815" ``IteratorUpperBehavior ``iteratorUpperBehavior,
  arrayFixEntry "multidimcov-array-collect-to-full" "collect_to!(dest,itr,offs,st)" "Collection consumes every remaining iterator value, writing fitting values and widening exactly at type changes." "base/array.jl:895-912" ``CollectToBehavior ``collectToBehavior,
  arrayFixEntry "multidimcov-array-grow-to-full" "grow_to!(dest,itr,st)" "Growth consumes every remaining value, pushing fitting values and widening exactly at type changes." "base/array.jl:935-949" ``GrowToBehavior ``growToBehavior,
  arrayFixEntry "multidimcov-array-reverse-window-valid" "reverse(::AbstractVector,start,stop)" "For every documented in-bounds window, reverse preserves the prefix and suffix and reverses exactly that window." "base/array.jl:2253-2266" ``ReverseWindowBehavior ``reverseWindowBehavior
]

end JuliaLean.MultidimCov
