import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- The zero-based column-major offset used by `hvncat_calcindex`,
`base/abstractarray.jl:2865-2873`. -/
def linearOffset : List Nat → List Nat → Nat
  | [], [] => 0
  | d :: ds, c :: cs => c + d * linearOffset ds cs
  | _, _ => 0

/-- Every coordinate is below the corresponding dimension. -/
def coordsValid : List Nat → List Nat → Prop
  | [], [] => True
  | d :: ds, c :: cs => c < d ∧ coordsValid ds cs
  | _, _ => False

def coordsValidB : List Nat → List Nat → Bool
  | [], [] => true
  | d :: ds, c :: cs => decide (c < d) && coordsValidB ds cs
  | _, _ => false

/-- The indices reached after the public copy methods convert starts to `Int`,
reject negative counts, and check the complete span. -/
def checkedSpanAccesses (a : LinearArray α) (start : Int) (count : Nat) : List Int :=
  if a.first ≤ start ∧ start + count ≤ a.first + a.values.length then
    (List.range count).map fun (k : Nat) => start + (k : Int)
  else []

/-- A source or destination access in a paired copy loop. -/
inductive CopyAccess where
  | dest (index : Int)
  | src (index : Int)

/-- Paired iteration indices used by `copyto_unaliased!` after its destination
length check. -/
def unaliasedCopyAccesses (dest : LinearArray α) (src : LinearArray β) : List CopyAccess :=
  if src.values.length ≤ dest.values.length then
    ((linearArrayIndices dest).take src.values.length).map CopyAccess.dest ++
      (linearArrayIndices src).map CopyAccess.src
  else []

/-- Canonical one-based linear index computed from checked Cartesian
coordinates by `_to_linear_index`; the Cartesian path reuses the same checked
coordinates. -/
def canonicalIndexAccess (dims coords : List Nat) : Option Nat :=
  if coordsValidB dims coords then some (linearOffset dims coords + 1) else none

/-- Copy loops in `base/abstractarray.jl:953-1176,1392-1503`: checked spans,
paired `eachindex`/`LinearIndices`, and canonical index conversion. -/
def AbstractArrayCopySafe : Prop :=
  (∀ (α : Type) (a : LinearArray α) start count i,
    i ∈ checkedSpanAccesses a start count → inAxis a.first a.values.length i) ∧
  (∀ (α β : Type) (dest : LinearArray α) (src : LinearArray β) access,
    access ∈ unaliasedCopyAccesses dest src →
      match access with
      | .dest i => inAxis dest.first dest.values.length i
      | .src i => inAxis src.first src.values.length i) ∧
  (∀ dims coords index, canonicalIndexAccess dims coords = some index →
    inOneBased dims.prod index)

/-- All zero-based coordinates of an array shape. -/
def shapeCoordinates : List Nat → List (List Nat)
  | [] => [[]]
  | dim :: dims => (List.range dim).flatMap fun coordinate =>
      (shapeCoordinates dims).map (coordinate :: ·)

/-- Linear destination indices and scratch-vector positions reached by the
hvcat/hvncat fills after their element-count and shape construction. -/
def concatAccesses (dims : List Nat) : List Nat :=
  (shapeCoordinates dims).map fun coords => linearOffset dims coords + 1

def AbstractArrayConcatSafe : Prop :=
  (∀ dims index, index ∈ concatAccesses dims → inOneBased dims.prod index) ∧
  (∀ (dims : List Nat) i, i ∈ oneBasedLoop dims.length → inOneBased dims.length i)

/-- Slice positions allocated by `_dim_stack!`. -/
def stackAccesses (slices : List α) : List Nat := oneBasedLoop slices.length

/-- The write positions of `_keepat!` are a prefix of the vector's iteration
indices; a checked source read stops the loop before a longer invalid prefix. -/
def keepatWriteAccesses (a : LinearArray α) (requested : List Int) : List Int :=
  (linearArrayIndices a).take requested.length

/-- `stack`, `map!`, `map_n!`, and both `_keepat!` methods in
`base/abstractarray.jl:3075-3086,3482-3559,3699-3728`. -/
def AbstractArrayIterationSafe : Prop :=
  (∀ (α : Type) (slices : List α) i,
    i ∈ stackAccesses slices → inOneBased slices.length i) ∧
  (∀ (α : Type) (a : LinearArray α) i,
    i ∈ linearArrayIndices a → inAxis a.first a.values.length i) ∧
  (∀ (α : Type) (a : LinearArray α) requested i,
    i ∈ keepatWriteAccesses a requested → inAxis a.first a.values.length i)

private theorem linearOffset_lt_product :
    ∀ dims coords, coordsValid dims coords → linearOffset dims coords < dims.prod
  | [], [], _ => by simp [linearOffset]
  | d :: ds, c :: cs, h => by
      have hc : c < d := h.1
      have ih := linearOffset_lt_product ds cs h.2
      have hs : linearOffset ds cs + 1 ≤ ds.prod := Nat.succ_le_iff.mpr ih
      calc
        linearOffset (d :: ds) (c :: cs) = c + d * linearOffset ds cs := rfl
        _ < d + d * linearOffset ds cs := Nat.add_lt_add_right hc _
        _ = d * (linearOffset ds cs + 1) := by simp [Nat.mul_add, Nat.add_comm]
        _ ≤ d * ds.prod := Nat.mul_le_mul_left d hs
        _ = (d :: ds).prod := by simp
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

private theorem linearArrayIndices_safe_early (a : LinearArray α) :
    ∀ i ∈ linearArrayIndices a, inAxis a.first a.values.length i := by
  intro i hi
  simp only [linearArrayIndices, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  unfold inAxis
  omega

private theorem coordsValidB_true : ∀ dims coords,
    coordsValidB dims coords = true → coordsValid dims coords
  | [], [], _ => trivial
  | d :: ds, c :: cs, h => by
      simp only [coordsValidB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, coordsValidB_true ds cs h.2⟩
  | [], _ :: _, h => by simp [coordsValidB] at h
  | _ :: _, [], h => by simp [coordsValidB] at h

theorem abstractArrayCopySafe_proven : AbstractArrayCopySafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro α a start count i hi
    unfold checkedSpanAccesses at hi
    split at hi
    · rename_i hspan
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      unfold inAxis
      omega
    · simp at hi
  · intro α β dest src access hi
    unfold unaliasedCopyAccesses at hi
    split at hi
    · simp only [List.mem_append, List.mem_map] at hi
      rcases hi with ⟨index, hindex, rfl⟩ | ⟨index, hindex, rfl⟩
      · exact linearArrayIndices_safe_early dest index (List.mem_of_mem_take hindex)
      · exact linearArrayIndices_safe_early src index hindex
    · simp at hi
  · intro dims coords index hi
    unfold canonicalIndexAccess at hi
    split at hi
    · rename_i hcoords
      cases hi
      have hb := linearOffset_lt_product dims coords (coordsValidB_true dims coords hcoords)
      unfold inOneBased
      omega
    · contradiction

theorem abstractArrayConcatSafe_proven : AbstractArrayConcatSafe := by
  constructor
  · intro dims index hi
    simp only [concatAccesses, List.mem_map] at hi
    obtain ⟨coords, hcoords, rfl⟩ := hi
    have valid : coordsValid dims coords := by
      induction dims generalizing coords with
      | nil =>
          simp [shapeCoordinates] at hcoords
          subst coords
          trivial
      | cons dim dims ih =>
          simp only [shapeCoordinates, List.mem_flatMap, List.mem_map, List.mem_range] at hcoords
          obtain ⟨coordinate, hc, rest, hr, rfl⟩ := hcoords
          exact ⟨hc, ih rest hr⟩
    have hb := linearOffset_lt_product dims coords valid
    unfold inOneBased
    omega
  · intro dims i hi
    simp only [oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

theorem abstractArrayIterationSafe_proven : AbstractArrayIterationSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro α slices i hi
    simp only [stackAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega
  · intro α a i hi
    exact linearArrayIndices_safe_early a i hi
  · intro α a requested i hi
    exact linearArrayIndices_safe_early a i (List.mem_of_mem_take hi)

end JuliaLean.MemSafety.G3
