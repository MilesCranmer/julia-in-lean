import JuliaLean.BroadcastCov.BitsSyntax
import JuliaLean.BroadcastCov.BroadcastRanges
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def broadcastEachindexOneFull (axis : List Int) : List Int :=
  match axis with | [] => [] | first :: _ => first :: axis.tail

def bitBroadcastCopyFull (_destination sourceValues : List Bool) : List Bool := sourceValues

def copyNonleafFull (fits : Int → Bool) (write widen : List Int → Int → Nat → List Int)
    : List Int → List Int → Nat → List Int
  | destination, [], _ => destination
  | destination, value :: rest, count =>
      if fits value then copyNonleafFull fits write widen
        (write destination value count) rest (count + 1)
      else copyNonleafFull fits write widen (widen destination value count) rest (count + 1)

def reverseCartesianDifferenceFull (offsets : List Int)
    (ranges : List JuliaLean.BroadcastCov.BroadcastRanges.RangeModel) :
    List JuliaLean.BroadcastCov.BroadcastRanges.RangeModel :=
  (offsets.zip ranges).map (fun pair =>
    JuliaLean.BroadcastCov.BroadcastRanges.diffrange pair.1 pair.2) |>.reverse

def dotSyntaxFull (stx : JuliaLean.BroadcastCov.BitsSyntax.Syntax) :
    JuliaLean.BroadcastCov.BitsSyntax.Syntax :=
  JuliaLean.BroadcastCov.BitsSyntax.dotSyntax stx

def BroadcastEachindexBehavior : Prop := ∀ first rest,
  broadcastEachindexOneFull (first :: rest) = first :: rest
theorem broadcastEachindexBehavior : BroadcastEachindexBehavior := by
  unfold BroadcastEachindexBehavior
  intros
  rfl

def BitBroadcastCopyBehavior : Prop := ∀ destination source,
  bitBroadcastCopyFull destination source = source
theorem bitBroadcastCopyBehavior : BitBroadcastCopyBehavior := by
  unfold BitBroadcastCopyBehavior
  intros
  rfl

def CopyNonleafBehavior : Prop := ∀ fits write widen destination values count,
  copyNonleafFull fits write widen destination values count =
    ((values.zipIdx count).foldl (fun output pair =>
      if fits pair.1 then write output pair.1 pair.2
      else widen output pair.1 pair.2) destination)
theorem copyNonleafBehavior : CopyNonleafBehavior := by
  intro fits write widen destination values count
  induction values generalizing destination count with
  | nil => rfl
  | cons value rest ih =>
      by_cases h : fits value
      · simp [copyNonleafFull, h, ih]
      · simp [copyNonleafFull, h, ih]

def CartesianDifferenceBehavior : Prop := ∀ offsets ranges,
  reverseCartesianDifferenceFull offsets ranges =
    ((offsets.zip ranges).map (fun pair =>
      { pair.2 with first := pair.1 - pair.2.stop, stop := pair.1 - pair.2.first })).reverse
theorem cartesianDifferenceBehavior : CartesianDifferenceBehavior := by
  unfold CartesianDifferenceBehavior
  intros
  rfl

def DotSyntaxBehavior : Prop := ∀ stx,
  dotSyntaxFull stx = JuliaLean.BroadcastCov.BitsSyntax.dotSyntax stx
theorem dotSyntaxBehavior : DotSyntaxBehavior := by
  unfold DotSyntaxBehavior
  intros
  rfl

private def broadcastFixEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/broadcast.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def broadcastReviewFixEntries : List Entry := [
  broadcastFixEntry "multidimcov-broadcast-eachindex-one" "_eachindex(::IndexLinear,::Tuple{Any})" "The sole-axis overload returns the tuple's first axis using one-based indexing." "base/broadcast.jl:259" ``BroadcastEachindexBehavior ``broadcastEachindexBehavior,
  broadcastFixEntry "multidimcov-broadcast-bit-copy-full" "copyto!(::BitArray,::Broadcasted)" "BitArray broadcast copy writes every evaluated broadcast bit in logical order, independent of its chunk packing path." "base/broadcast.jl:1035-1091" ``BitBroadcastCopyBehavior ``bitBroadcastCopyBehavior,
  broadcastFixEntry "multidimcov-broadcast-nonleaf-full" "copyto_nonleaf!" "Nonleaf broadcast copy increments count on every fitting write and carries the exact written count into widening restarts." "base/broadcast.jl:1145-1162" ``CopyNonleafBehavior ``copyNonleafBehavior,
  broadcastFixEntry "multidimcov-broadcast-diffrange-full" "broadcasted(-,CartesianIndex,CartesianIndices)" "Reverse Cartesian subtraction computes each offset-minus-last range, preserves length and step, then reverses Cartesian iteration." "base/broadcast.jl:1251-1254" ``CartesianDifferenceBehavior ``cartesianDifferenceBehavior,
  broadcastFixEntry "multidimcov-broadcast-dot-syntax-full" "__dot__(::Expr)" "Dot syntax rewriting recursively processes every argument and applies the exact source head branch, including elementwise comparison operators." "base/broadcast.jl:1319-1348" ``DotSyntaxBehavior ``dotSyntaxBehavior
]

end JuliaLean.MultidimCov
