import JuliaLean.Proofs.base.experimental.memory_safety_group2

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
def cartesianCoords : List Nat → List (List Int)
  | [] => [[]]
  | n :: ns =>
      (oneBased n).flatMap fun i => (cartesianCoords ns).map fun is => i :: is


/-! ## `base/multidimensional.jl` -/

def cartesianCollectAccesses (axes : List Axis) : List Access :=
  let n := product (axes.map (·.len))
  (oneBased n).map fun i => ⟨n, i⟩

def CartesianCollectInBounds : Prop := ∀ axes,
  AllInBounds (cartesianCollectAccesses axes)

def bitChunkCount (bits : List Bool) : Nat := (bits.length + 63) / 64

def chunkHasTrue (bits : List Bool) (chunk : Nat) : Bool :=
  ((bits.drop (chunk * 64)).take 64).any id

def logicalChunkScan (bits : List Bool) : Nat → Nat → List Access
  | 0, _ => []
  | fuel + 1, chunk =>
      if h : chunk < bitChunkCount bits then
        let here := ⟨bitChunkCount bits, (chunk : Int) + 1⟩
        if chunkHasTrue bits chunk then [here]
        else here :: logicalChunkScan bits fuel (chunk + 1)
      else []

def logicalIndexAccesses (bits : List Bool) : List Access :=
  if bits.any id then logicalChunkScan bits (bitChunkCount bits) 0 else []

def LogicalIndexInBounds : Prop := ∀ bits, AllInBounds (logicalIndexAccesses bits)

def cartesianValues : List (List Int) → List (List Int)
  | [] => [[]]
  | values :: rest =>
      values.flatMap fun i => (cartesianValues rest).map fun is => i :: is

def genericGetindexAccesses (axes : List Axis) (indices : List (List Int)) : List Access :=
  let coords := cartesianValues indices
  if coords.all (fun is => !(constCartesianAccessAxes axes is).isEmpty) then
    coords.flatMap (constCartesianAccessAxes axes) ++
      (oneBased coords.length).map fun i => ⟨coords.length, i⟩
  else []

def genericSetindexAccesses (axes : List Axis) (indices : List (List Int))
    (sourceLength : Nat) : List Access :=
  let coords := cartesianValues indices
  if coords.all (fun is => !(constCartesianAccessAxes axes is).isEmpty) &&
      sourceLength = coords.length then
    coords.flatMap (constCartesianAccessAxes axes) ++
      (oneBased sourceLength).map fun i => ⟨sourceLength, i⟩
  else []

def GenericIndexingInBounds : Prop :=
  (∀ axes indices, AllInBounds (genericGetindexAccesses axes indices)) ∧
  (∀ axes indices sourceLength, AllInBounds (genericSetindexAccesses axes indices sourceLength))

structure Region where
  parentAxes : List Axis
  starts : List Int
  lengths : List Nat
  deriving DecidableEq, Repr

def Region.count (r : Region) : Nat := product r.lengths

def regionCoords (r : Region) : List (List Int) :=
  (cartesianCoords r.lengths).map fun offsets =>
    (r.starts.zip offsets).map fun (start, offset) => start + offset - 1

def regionValid (r : Region) : Bool :=
  r.parentAxes.length == r.starts.length && r.starts.length == r.lengths.length &&
    ((r.parentAxes.zip (r.starts.zip r.lengths)).all fun (axis, start, len) =>
      decide (axis.first.val ≤ start ∧
        (len = 0 ∨ start + len - 1 < axis.first.val + axis.len)))

def cartesianCopyAccesses (dest src : Region) : List Access :=
  if dest.lengths = src.lengths && regionValid dest && regionValid src then
    ((regionCoords src).flatMap (constCartesianAccessAxes src.parentAxes)) ++
      ((regionCoords dest).flatMap (constCartesianAccessAxes dest.parentAxes))
  else []

def CartesianCopyInBounds : Prop := ∀ dest src,
  AllInBounds (cartesianCopyAccesses dest src)

def bitSourceScanAccesses (sourceLength sourceStart count : Nat) : List Access :=
  if 1 ≤ sourceStart && sourceStart + count ≤ sourceLength + 1 then
    (List.range count).map fun k => ⟨sourceLength, (sourceStart + k : Nat)⟩
  else []

def BitSourceScanInBounds : Prop := ∀ sourceLength sourceStart count,
  AllInBounds (bitSourceScanAccesses sourceLength sourceStart count)

def isassignedAccess (axes : List Axis) (coords : List Int) (indexLinear : Bool) : List Access :=
  if !(constCartesianAccessAxes axes coords).isEmpty &&
      ((indexLinear && coords.length != 1) || (!indexLinear && coords.length != axes.length)) then
    constCartesianAccessAxes axes coords
  else []

def IsassignedInBounds : Prop := ∀ axes coords indexLinear,
  AllInBounds (isassignedAccess axes coords indexLinear)




theorem cartesianCollectInBounds : CartesianCollectInBounds := by
  intro axes
  simpa [cartesianCollectAccesses] using mappedOneBased (product (axes.map (·.len)))

private theorem logicalChunkScan_safe (bits : List Bool) : ∀ fuel chunk access,
    access ∈ logicalChunkScan bits fuel chunk → access.inBounds
  | 0, chunk, access, h => by simp [logicalChunkScan] at h
  | fuel + 1, chunk, access, h => by
      simp only [logicalChunkScan] at h
      split at h
      · split at h
        · simp only [List.mem_singleton] at h
          subst access
          simp only [Access.inBounds]
          omega
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · simp only [Access.inBounds]
            omega
          · exact logicalChunkScan_safe bits fuel (chunk + 1) access h
      · simp at h

theorem logicalIndexInBounds : LogicalIndexInBounds := by
  intro bits access ha
  simp only [logicalIndexAccesses] at ha
  split at ha
  · exact logicalChunkScan_safe bits _ 0 access ha
  · simp at ha

theorem genericIndexingInBounds : GenericIndexingInBounds := by
  constructor
  · intro axes indices access ha
    simp only [genericGetindexAccesses] at ha
    split at ha
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · simp only [List.mem_flatMap] at ha
        obtain ⟨coords, hcoords, ha⟩ := ha
        exact constCartesianAccessAxes_safe axes coords access ha
      · exact mappedOneBased (cartesianValues indices).length access ha
    · simp at ha
  · intro axes indices sourceLength access ha
    simp only [genericSetindexAccesses] at ha
    split at ha
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · simp only [List.mem_flatMap] at ha
        obtain ⟨coords, hcoords, ha⟩ := ha
        exact constCartesianAccessAxes_safe axes coords access ha
      · exact mappedOneBased sourceLength access ha
    · simp at ha

theorem cartesianCopyInBounds : CartesianCopyInBounds := by
  intro dest src access ha
  simp only [cartesianCopyAccesses] at ha
  split at ha
  · rw [List.mem_append] at ha
    rcases ha with ha | ha
    · simp only [List.mem_flatMap] at ha
      obtain ⟨coords, hcoords, ha⟩ := ha
      exact constCartesianAccessAxes_safe src.parentAxes coords access ha
    · simp only [List.mem_flatMap] at ha
      obtain ⟨coords, hcoords, ha⟩ := ha
      exact constCartesianAccessAxes_safe dest.parentAxes coords access ha
  · simp at ha

theorem bitSourceScanInBounds : BitSourceScanInBounds := by
  intro sourceLength sourceStart count access ha
  simp only [bitSourceScanAccesses] at ha
  split at ha
  · simp only [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [List.mem_range] at hk
    simp only [Access.inBounds]
    simp_all
    omega
  · simp at ha

theorem isassignedInBounds : IsassignedInBounds := by
  intro axes coords indexLinear access ha
  simp only [isassignedAccess] at ha
  split at ha
  · exact constCartesianAccessAxes_safe axes coords access ha
  · simp at ha

end JuliaLean.MemSafety.G2
