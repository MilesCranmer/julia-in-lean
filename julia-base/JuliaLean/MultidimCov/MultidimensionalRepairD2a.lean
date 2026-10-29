import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairD2a

open JuliaLean.Registry

inductive Error where | argument | dimensionMismatch | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure Axis where
  first : Int
  last : Int
  deriving Repr, DecidableEq
def Axis.length (axis : Axis) : Int := max 0 (axis.last - axis.first + 1)

structure Block where
  destination : List Axis
  source : List Axis
  deriving Repr, DecidableEq

def circshiftBlocks : List Axis → List Int → List Axis → List Axis → Result (List Block)
  | [], [], destination, source => .ok [⟨destination, source⟩]
  | axis :: axes, shift :: shifts, destination, source =>
      if axis.length = 0 then .error .argument else
      let amount := shift.emod axis.length
      let sourceFirst := axis.first + amount
      let sourceLast := axis.last - amount
      let destination1 := ⟨axis.first, sourceFirst - 1⟩
      let destination2 := ⟨sourceFirst, axis.last⟩
      let source1 := ⟨axis.first, sourceLast⟩
      let source2 := ⟨sourceLast + 1, axis.last⟩
      match circshiftBlocks axes shifts (destination ++ [destination1]) (source ++ [source2]) with
      | .error error => .error error
      | .ok firstBlocks => match circshiftBlocks axes shifts
          (destination ++ [destination2]) (source ++ [source1]) with
        | .error error => .error error
        | .ok secondBlocks => .ok (firstBlocks ++ secondBlocks)
  | _axes, _shifts, destination, source => .ok [⟨destination, source⟩]

def circshiftTop (sameObject : Bool) (destinationAxes sourceAxes : List Axis)
    (sourceEmpty : Bool) (shifts : List Int) : Result (List Block) :=
  if sameObject then .error .argument
  else if destinationAxes ≠ sourceAxes then .error .argument
  else if sourceEmpty then .ok []
  else circshiftBlocks sourceAxes (shifts.take sourceAxes.length ++
    List.replicate (sourceAxes.length - shifts.length) 0) [] []

def circcopyBlocks : List Axis → List Axis → List Axis → List Axis → Result (List Block)
  | [], [], destination, source => .ok [⟨destination, source⟩]
  | destinationAxis :: destinationAxes, sourceAxis :: sourceAxes, destination, source =>
      if destinationAxis.length = 0 then .error .argument else
      let amount := (sourceAxis.first - destinationAxis.first).emod destinationAxis.length
      let destinationSplit := destinationAxis.first + amount
      let destination1 := ⟨destinationAxis.first, destinationSplit - 1⟩
      let destination2 := ⟨destinationSplit, destinationAxis.last⟩
      let sourceSplit := sourceAxis.last - amount
      let source1 := ⟨sourceAxis.first, sourceSplit⟩
      let source2 := ⟨sourceSplit + 1, sourceAxis.last⟩
      match circcopyBlocks destinationAxes sourceAxes (destination ++ [destination1]) (source ++ [source2]) with
      | .error error => .error error
      | .ok firstBlocks => match circcopyBlocks destinationAxes sourceAxes
          (destination ++ [destination2]) (source ++ [source1]) with
        | .error error => .error error
        | .ok secondBlocks => .ok (firstBlocks ++ secondBlocks)
  | _destinationAxes, _sourceAxes, destination, source => .ok [⟨destination, source⟩]

def circcopyTop (sameObject : Bool) (destinationAxes sourceAxes : List Axis) : Result (List Block) :=
  if sameObject then .error .argument
  else if destinationAxes.map Axis.length ≠ sourceAxes.map Axis.length then .error .dimensionMismatch
  else if List.zipWith (fun source destination => source.first - destination.first)
      sourceAxes destinationAxes |>.all (· = 0) then .ok []
  else circcopyBlocks destinationAxes sourceAxes [] []

def blockCopy (construct : List Axis → Result R)
    (copyto : R → R → Result O) (block : Block) : Result O :=
  match construct block.destination with
  | .error error => .error error
  | .ok destination => match construct block.source with
    | .error error => .error error
    | .ok source => copyto destination source

def Contract : Prop :=
  (∀ same destination source empty shifts blocks,
    circshiftTop same destination source empty shifts = .ok blocks →
      same = false ∧ destination = source) ∧
  (∀ destination source, circshiftBlocks [] [] destination source =
    .ok [⟨destination, source⟩]) ∧
  (∀ same destination source blocks,
    circcopyTop same destination source = .ok blocks →
      same = false ∧ destination.map Axis.length = source.map Axis.length) ∧
  (∀ destination source, circcopyBlocks [] [] destination source =
    .ok [⟨destination, source⟩]) ∧
  (∀ {R O : Type} construct copyto block output,
    blockCopy (R := R) (O := O) construct copyto block = .ok output →
      ∃ destination source, construct block.destination = .ok destination ∧
        construct block.source = .ok source ∧ copyto destination source = .ok output)

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro same destination source empty shifts blocks h
    by_cases hs : same
    · simp [circshiftTop, hs] at h
    · by_cases ha : destination = source
      · have hs0 : same = false := by cases same <;> simp_all
        exact ⟨hs0, ha⟩
      · simp [circshiftTop, hs, ha] at h
  · intros
    rfl
  · intro same destination source blocks h
    by_cases hs : same
    · simp [circcopyTop, hs] at h
    · by_cases ha : destination.map Axis.length = source.map Axis.length
      · have hs0 : same = false := by cases same <;> simp_all
        exact ⟨hs0, ha⟩
      · simp [circcopyTop, hs, ha] at h
  · intros
    rfl
  · intro R O construct copyto block output h
    cases hd : construct block.destination with
    | error error => simp [blockCopy, hd] at h
    | ok destination =>
        cases hs : construct block.source with
        | error error => simp [blockCopy, hd, hs] at h
        | ok source => exact ⟨destination, source, rfl, rfl, by simpa [blockCopy, hd, hs] using h⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairD2a
