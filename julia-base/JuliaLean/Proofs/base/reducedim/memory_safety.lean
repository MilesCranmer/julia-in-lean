import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- Two-axis presentation of `check_reducedims`, `base/reducedim.jl:205-233`.
`columns` denotes the column-major flattening of all tail Cartesian axes; the
same computation applies recursively to any number of tail axes. -/
def reductionChoices (rows cols resultRows resultCols : Nat) : Option (Bool × Bool) :=
  let reduceRows := if resultRows = 1 then some true else if resultRows = rows then some false else none
  let reduceCols := if resultCols = 1 then some true else if resultCols = cols then some false else none
  match reduceRows, reduceCols with
  | some r, some c => some (r, c)
  | _, _ => none

def reduceLeadingBlock (rows cols : Nat) (reduceRows reduceCols : Bool) : Nat :=
  if reduceRows then
    if reduceCols then rows * cols else rows
  else if reduceCols ∧ rows = 1 then cols
  else if reduceCols then 0
  else 1

def reduceSlowAccesses (rows cols resultRows resultCols : Nat) : List Access :=
  match reductionChoices rows cols resultRows resultCols with
  | none => []
  | some (reduceRows, reduceCols) =>
    (List.range cols).flatMap fun j =>
      (List.range rows).flatMap fun i =>
        let ri := if reduceRows then 0 else i
        let rj := if reduceCols then 0 else j
        [at0 (rows * cols) (i + rows * j),
         at0 (resultRows * resultCols) (ri + resultRows * rj)]

/-- Fast `_mapreducedim!`, lines 256-268.  `check_reducedims` computes the
leading block, then `ibase` advances by exactly that block for every output
slot. -/
def reduceFastAccesses (rows cols resultRows resultCols : Nat) : List Access :=
  match reductionChoices rows cols resultRows resultCols with
  | none => []
  | some (reduceRows, reduceCols) =>
    let block := reduceLeadingBlock rows cols reduceRows reduceCols
    if block > 16 then
      (List.range (resultRows * resultCols)).flatMap fun i =>
        [at0 (resultRows * resultCols) i,
         span0 (rows * cols) (i * block) block]
    else []

def ReductionAccessesInBounds : Prop :=
  ∀ rows cols rr rc,
    accessesSafe (reduceSlowAccesses rows cols rr rc) ∧
    accessesSafe (reduceFastAccesses rows cols rr rc)

private theorem reductionChoices_shape (rows cols rr rc : Nat) (br bc : Bool)
    (h : reductionChoices rows cols rr rc = some (br, bc)) :
    rr = (if br then 1 else rows) ∧ rc = (if bc then 1 else cols) := by
  unfold reductionChoices at h
  repeat' split at h
  all_goals simp_all

private theorem reduceLeading_product (rows cols rr rc : Nat) (br bc : Bool)
    (hc : reductionChoices rows cols rr rc = some (br, bc))
    (hp : 0 < reduceLeadingBlock rows cols br bc) :
    (rr * rc) * reduceLeadingBlock rows cols br bc = rows * cols := by
  obtain ⟨rfl, rfl⟩ := reductionChoices_shape rows cols rr rc br bc hc
  cases br <;> cases bc
  · simp [reduceLeadingBlock]
  · by_cases hr : rows = 1 <;> simp_all [reduceLeadingBlock]
  · simp [reduceLeadingBlock, Nat.mul_comm]
  · simp [reduceLeadingBlock]

theorem reductionAccessesInBounds_proven : ReductionAccessesInBounds := by
  intro rows cols rr rc
  constructor
  · intro a ha
    simp only [reduceSlowAccesses] at ha
    split at ha
    · simp at ha
    · rename_i br bc hc
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at ha
      obtain ⟨j, hj, i, hi, rfl | rfl⟩ := ha
      · simp only [Access.safe, at0]
        have hm := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hj)
        rw [Nat.mul_succ] at hm
        omega
      · simp only [Access.safe, at0]
        obtain ⟨rfl, rfl⟩ := reductionChoices_shape rows cols rr rc br bc hc
        cases br <;> cases bc <;> simp_all [Access.safe, at0]
        all_goals
          have hm := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hj)
          rw [Nat.mul_succ] at hm
          omega
  · intro a ha
    simp only [reduceFastAccesses] at ha
    split at ha
    · simp at ha
    · rename_i br bc hc
      split at ha
      · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at ha
        obtain ⟨i, hi, rfl | rfl⟩ := ha
        · simp [Access.safe, at0]
          omega
        · simp only [Access.safe, span0]
          have heq := reduceLeading_product rows cols rr rc br bc hc (by omega)
          have hm := Nat.mul_le_mul_right (reduceLeadingBlock rows cols br bc)
            (Nat.succ_le_iff.mpr hi)
          rw [Nat.succ_mul] at hm
          omega
      · simp at ha

/-! Arbitrary-dimensional reduction model used by the registry entry. -/

def reductionFlags : List Nat → List Nat → Option (List Bool)
  | [], [] => some []
  | a :: as, r :: rs =>
      if r = 1 then (reductionFlags as rs).map (true :: ·)
      else if r = a then (reductionFlags as rs).map (false :: ·)
      else none
  | _, _ => none

def reducedShape : List Bool → List Nat → List Nat
  | b :: bs, a :: as => (if b then 1 else a) :: reducedShape bs as
  | _, _ => []

def reducedCoords : List Bool → List Int → List Int
  | b :: bs, i :: is => (if b then 1 else i) :: reducedCoords bs is
  | _, _ => []

def selectedProduct : List Bool → List Nat → Nat
  | b :: bs, a :: as => (if b then a else 1) * selectedProduct bs as
  | _, _ => 1

def leadingReductions : Bool → List Bool → List Nat → Bool
  | _, [], [] => true
  | had, b :: bs, a :: as =>
      let ok := !(had && b && a > 1)
      ok && leadingReductions (had || !b) bs as
  | _, _, _ => false

def reductionBlockND (dims : List Nat) (flags : List Bool) : Nat :=
  if leadingReductions false flags dims then selectedProduct flags dims else 0

def reduceSlowNDAccesses (dims resultDims : List Nat) (coord : List Int) : List Access :=
  if resultDims.length ≤ dims.length then
    let result := normalizeDims resultDims dims.length
    match reductionFlags dims result with
    | some flags =>
      if coordsWithinB dims coord then
        uncheckedCartesianAccess dims coord ++
          uncheckedCartesianAccess (reducedShape flags dims) (reducedCoords flags coord)
      else []
    | none => []
  else []

def reduceFastNDAccesses (dims resultDims : List Nat) : List Access :=
  if resultDims.length ≤ dims.length ∧ 0 < shapeProduct dims then
    let result := normalizeDims resultDims dims.length
    match reductionFlags dims result with
    | some flags =>
      let block := reductionBlockND dims flags
      if block > 16 then
        (List.range (shapeProduct (reducedShape flags dims))).flatMap fun i =>
          [at0 (shapeProduct (reducedShape flags dims)) i,
           span0 (shapeProduct dims) (i * block) block]
      else []
    | none => []
  else []

private theorem reductionFlags_lengths : ∀ dims result flags,
    reductionFlags dims result = some flags →
    flags.length = dims.length ∧ result = reducedShape flags dims
  | [], [], [], _ => by simp [reductionFlags, reducedShape]
  | a :: as, r :: rs, flags, h => by
      simp only [reductionFlags] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨fs, hfs, rfl⟩ := h
        have ih := reductionFlags_lengths as rs fs hfs
        simp [reducedShape, ih.1, ih.2, *]
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨fs, hfs, rfl⟩ := h
          have ih := reductionFlags_lengths as rs fs hfs
          simp [reducedShape, ih.1, ih.2, *]
        · simp at h
  | [], _ :: _, _, h => by simp [reductionFlags] at h
  | _ :: _, [], _, h => by simp [reductionFlags] at h

private theorem reducedCoords_within : ∀ flags dims coord,
    flags.length = dims.length → coordsWithin dims coord →
    coordsWithin (reducedShape flags dims) (reducedCoords flags coord)
  | [], [], [], _, _ => by simp [coordsWithin, reducedShape, reducedCoords]
  | b :: bs, a :: as, i :: is, hlen, hc => by
      have htail : coordsWithin as is :=
        ⟨by simpa [coordsWithin] using hc.1,
         fun p hp => hc.2 p (List.mem_cons_of_mem _ hp)⟩
      have ih := reducedCoords_within bs as is (by simpa using hlen) htail
      constructor
      · simp [reducedShape, reducedCoords, ih.1]
      · intro p hp
        simp only [reducedShape, reducedCoords, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · cases b <;> simp_all
          exact hc.2 (a, i) (by simp)
        · exact ih.2 p hp
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp [coordsWithin] at h

private theorem selectedProduct_identity : ∀ flags dims,
    flags.length = dims.length →
    shapeProduct (reducedShape flags dims) * selectedProduct flags dims = shapeProduct dims
  | [], [], _ => by simp [shapeProduct, reducedShape, selectedProduct]
  | b :: bs, a :: as, h => by
      have ih := selectedProduct_identity bs as (by simpa using h)
      cases b with
      | false =>
          simp only [reducedShape, selectedProduct, Bool.false_eq_true, ↓reduceIte,
            Nat.one_mul, shapeProduct, List.foldr_cons]
          change (a * shapeProduct (reducedShape bs as)) * selectedProduct bs as =
            a * shapeProduct as
          calc
            (a * shapeProduct (reducedShape bs as)) * selectedProduct bs as =
                a * (shapeProduct (reducedShape bs as) * selectedProduct bs as) := by
                  rw [Nat.mul_assoc]
            _ = a * shapeProduct as := by rw [ih]
      | true =>
          simp only [reducedShape, selectedProduct, ↓reduceIte, Nat.one_mul,
            shapeProduct, List.foldr_cons]
          change shapeProduct (reducedShape bs as) *
              (a * selectedProduct bs as) = a * shapeProduct as
          calc
            shapeProduct (reducedShape bs as) * (a * selectedProduct bs as) =
                a * (shapeProduct (reducedShape bs as) * selectedProduct bs as) := by ac_rfl
            _ = a * shapeProduct as := by rw [ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

def ReductionNDAccessesInBounds : Prop := ∀ dims resultDims,
  (∀ coord, accessesSafe (reduceSlowNDAccesses dims resultDims coord)) ∧
  accessesSafe (reduceFastNDAccesses dims resultDims)

theorem reductionNDAccessesInBounds_proven : ReductionNDAccessesInBounds := by
  intro dims resultDims
  constructor
  · intro coord a ha
    simp only [reduceSlowNDAccesses] at ha
    split at ha
    · split at ha
      · rename_i flags hf
        split at ha
        · have hs := reductionFlags_lengths dims (normalizeDims resultDims dims.length) flags hf
          have hc := coordsWithinB_true dims coord (by assumption)
          simp only [List.mem_append] at ha
          rcases ha with ha | ha
          · exact uncheckedCartesian_safe dims coord hc a ha
          · exact uncheckedCartesian_safe _ _
              (reducedCoords_within flags dims coord hs.1 hc) a ha
        · simp at ha
      · simp at ha
    · simp at ha
  · intro a ha
    simp only [reduceFastNDAccesses] at ha
    split at ha
    · split at ha
      · rename_i flags hf
        split at ha
        · simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] at ha
          obtain ⟨i, hi, rfl | rfl⟩ := ha
          · simp [Access.safe, at0]; omega
          · simp only [Access.safe, span0]
            have hs := reductionFlags_lengths dims (normalizeDims resultDims dims.length) flags hf
            have hid := selectedProduct_identity flags dims hs.1
            have hlead : leadingReductions false flags dims = true := by
              unfold reductionBlockND at *
              split at * <;> simp_all
            have hb : reductionBlockND dims flags = selectedProduct flags dims := by
              simp [reductionBlockND, hlead]
            rw [hb]
            have hm := Nat.mul_le_mul_right (selectedProduct flags dims)
              (Nat.succ_le_iff.mpr hi)
            rw [Nat.succ_mul, hid] at hm
            omega
        · simp at ha
      · simp at ha
    · simp at ha

end JuliaLean.MemSafety.G1
