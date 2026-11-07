import JuliaLean.base.permuteddimsarray
import JuliaLean.base.essentials
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.permuteddimsarray.CopyLinearLength

open JuliaLean
open JuliaLean.base.abstractarray (checkindexRange checkindexOneTo
  checkboundsIndicesNil checkboundsIndicesCons checkboundsMany)
open JuliaLean.base.permuteddimsarray (PermutedDimsArray TupleN copytoPermuted)

abbrev I := JInt .i64
abbrev Header := JuliaLean.base.array.HeapArray Unit
abbrev Destination := PermutedDimsArray Int Header 2
abbrev BoundsResult := JuliaLean.base.abstractarray.Result
abbrev M := ExceptT JuliaLean.BootCov.Exc BoundsResult

private def i (n : Int) : I := JInt.lit .i64 n

def destination : Destination :=
  ⟨⟨0, (), [2, 2], [(1, 2), (1, 2)]⟩,
    ⟨[i 2, i 1], by decide⟩, ⟨[i 2, i 1], by decide⟩⟩

def source : Header := ⟨1, (), [4, 1], [(1, 4), (1, 1)]⟩

def sourceAxes : TupleN I 2 := ⟨[i 4, i 1], by decide⟩

/-- OneTo{Int} observations and scalar dispatch in checkindex(::Bool, inds, range).
Source: base/abstractarray.jl:753,756-757; base/range.jl:711,868,877.
The arguments are the nonnegative stored stops of these OneTo ranges. -/
def checkOneToRange (limit stop : I) : BoundsResult Bool :=
  checkindexRange (fun last => pure (JuliaLean.base.int.lt last (i 1)))
    (fun _ => pure (i 1)) pure
    (fun axis index => pure (checkindexOneTo axis index)) limit stop

/-- Installed tuple recursion for the native OneTo axes in this example.
Source: base/abstractarray.jl:722-728. -/
def checkAxisTuple : List I → List I → BoundsResult Bool
  | axes, [] => checkboundsIndicesNil pure axes
  | axes, index :: rest =>
      checkboundsIndicesCons (i 1) checkOneToRange
        (fun remaining _ => checkAxisTuple remaining rest) axes index rest
termination_by _ indices => indices.length

private def liftBounds {α : Type} (result : BoundsResult α) : M α :=
  ExceptT.mk (result.map Except.ok)

/-- Native one-based axes, represented by their OneTo{Int} stops.
The metadata comes from the existing heap-array header.
Source: base/abstractarray.jl:100-103. -/
def nativeAxes (header : Header) : BoundsResult (List I) :=
  JuliaLean.base.abstractarray.axesDefault
    (fun value : Header => pure (value.dimensions.map (fun n => i (Int.ofNat n))))
    id header

/-- The installed nonempty-copy bounds check, with ordinary one-based matrix
metadata. Source: base/permuteddimsarray.jl:295;
base/abstractarray.jl:682-685,722-728; base/essentials.jl:389-393. -/
def checkOrdinaryAxes (header : Header) (axes : List I) : M Unit :=
  JuliaLean.base.essentials.Models2Group19.checkbounds (Other := Unit)
    { check := fun (value : Header) (indices : List I) => do
        let result ← liftBounds (checkboundsMany nativeAxes checkAxisTuple value indices)
        pure (.bool result) }
    header axes

def checkOrdinaryCopyPrecheck (dest src : Header) : M Unit := do
  checkOrdinaryAxes dest (← liftBounds (nativeAxes src))

/-- Both axes of the concrete square remain unchanged under its permutation. -/
def checkDestination (axes : TupleN I 2) : M Unit :=
  checkOrdinaryAxes destination.parent axes.values

/-- The unchanged public copy entry point at base/permuteddimsarray.jl:293-298.
Both unresolved later calls remain universally quantified. Neither is replaced
by a dummy implementation, and neither can affect the earlier exception. -/
def copyFourToSquare (unalias : Destination → Header → M Header)
    (copy : Destination → Header → M Destination) : M Destination :=
  copytoPermuted (fun _ => pure false) (fun _ => pure sourceAxes)
    (fun _ axes => checkDestination axes) unalias copy destination source

theorem equalLinearCapacity : source.dimensions.prod = destination.parent.dimensions.prod := by
  decide

theorem checkDestination_rejects :
    (checkDestination sourceAxes).run = .ok (.error .bounds) := by
  simp only [checkDestination, checkOrdinaryAxes,
    JuliaLean.base.essentials.Models2Group19.checkbounds, liftBounds,
    checkboundsMany, nativeAxes, JuliaLean.base.abstractarray.axesDefault,
    destination, sourceAxes, List.map_cons, List.map_nil, checkAxisTuple,
    bind, pure, Except.bind, Except.pure, Except.map, ExceptT.run,
    ExceptT.bind, ExceptT.bindCont, ExceptT.mk] <;> rfl

theorem copyFourToSquare_bounds (unalias : Destination → Header → M Header)
    (copy : Destination → Header → M Destination) :
    (copyFourToSquare unalias copy).run = .ok (.error .bounds) := by
  have rejected := checkDestination_rejects
  simp only [ExceptT.run] at rejected
  simp [copyFourToSquare, copytoPermuted, ExceptT.run, ExceptT.bind,
    ExceptT.bindCont, ExceptT.pure, ExceptT.mk, rejected] <;> rfl

/-- A fixed-input consequence of the complete copy operation's success promise.
The later selected methods remain parameters, rather than invented bindings. -/
def CopyFourToSquareSucceeds (unalias : Destination → Header → M Header)
    (copy : Destination → Header → M Destination) : Prop :=
  ∃ result, (copyFourToSquare unalias copy).run = .ok (.ok result)

theorem copyFourToSquareSucceeds_refuted (unalias : Destination → Header → M Header)
    (copy : Destination → Header → M Destination) :
    ¬ CopyFourToSquareSucceeds unalias copy := by
  rintro ⟨result, success⟩
  rw [copyFourToSquare_bounds] at success
  cases success

/-- Initialized ordinary Int matrices have two nonnegative native dimensions,
matching one-based axes and allocated, initialized storage for every element.
These are header/storage conditions, not a replacement array interpreter. -/
def ValidOrdinaryMatrixHeader (heap : JuliaLean.base.array.VectorHeap Int)
    (header : Header) : Prop :=
  header.dimensions.length = 2 ∧
  header.axes = header.dimensions.map (fun count => (1, count)) ∧
  (∀ dimension ∈ header.dimensions, dimension < 2 ^ 63) ∧
  ∃ slots, heap[header.handle]? = some slots ∧
    header.dimensions.prod ≤ slots.length ∧
    slots.length * 8 < 2 ^ 63 - 2 ∧
    (slots.take header.dimensions.prod).all Option.isSome = true

/-- For distinct initialized ordinary matrices, nonempty source data fits when
its linear element count does not exceed the destination's. Consequently the
public copy entry point must not reject their shapes at its bounds precheck.
This states only the necessary exception-free precheck consequence; it makes
no claim about the still-unbound later copying kernel.
Promise: base/abstractarray.jl:1043-1048.
Checked source: base/permuteddimsarray.jl:293-298. -/
def CopyFitsLinearLength : Prop :=
  ∀ (heap : JuliaLean.base.array.VectorHeap Int) (dest src : Header),
    ValidOrdinaryMatrixHeader heap dest →
    ValidOrdinaryMatrixHeader heap src →
    dest.handle ≠ src.handle →
    0 < src.dimensions.prod →
    src.dimensions.prod ≤ dest.dimensions.prod →
    (checkOrdinaryCopyPrecheck dest src).run = .ok (.ok ())

def witnessHeap : JuliaLean.base.array.VectorHeap Int :=
  [[some 0, some 0, some 0, some 0], [some 1, some 2, some 3, some 4]]

theorem copyFitsLinearLength_refuted : ¬ CopyFitsLinearLength := by
  intro promise
  have success := promise witnessHeap destination.parent source
    (by
      unfold ValidOrdinaryMatrixHeader
      refine ⟨by decide, by decide, by decide, ?_⟩
      exact ⟨[some 0, some 0, some 0, some 0], by decide, by decide, by decide, by decide⟩)
    (by
      unfold ValidOrdinaryMatrixHeader
      refine ⟨by decide, by decide, by decide, ?_⟩
      exact ⟨[some 1, some 2, some 3, some 4], by decide, by decide, by decide, by decide⟩)
    (by decide) (by decide) (by decide)
  have rejected :
      (checkOrdinaryCopyPrecheck destination.parent source).run = .ok (.error .bounds) := by
    exact checkDestination_rejects
  rw [rejected] at success
  cases success

def entries : List JuliaLean.Registry.Entry := [
  { id := "permuteddimsarray-copy-linear-length",
    juliaFile := "base/permuteddimsarray.jl",
    juliaFns := ["copyto!(::PermutedDimsArray, ::AbstractArray)@293"],
    statement := "For distinct initialized ordinary matrices with valid headers and nonempty source, sufficient destination linear capacity prevents the public copy precheck from rejecting solely because their shapes differ.",
    source := "base/abstractarray.jl:1043-1048; base/permuteddimsarray.jl:293-298",
    status := .refuted,
    prop := ``CopyFitsLinearLength,
    thm := some ``copyFitsLinearLength_refuted,
    issue := "bugs/permuteddimsarray-copy-linear-length.yaml",
    notes := "The closed proposition covers the necessary bounds-precheck promise. The later copy kernel and unalias operations are not bound as a closed whole-operation theorem." }
]

end JuliaLean.Proofs.base.permuteddimsarray.CopyLinearLength
