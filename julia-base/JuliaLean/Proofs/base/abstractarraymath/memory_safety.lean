import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- `conj!`, `base/abstractarraymath.jl:194`, calls `broadcast!` with the same
array as source and destination; broadcast's axis check and iterator therefore
compute the identical ordinal for both accesses. -/
def broadcastConjAccesses (length : Nat) : List Access :=
  axisAccesses length ++ axisAccesses length

def BroadcastConjInBounds : Prop := ∀ length,
  accessesSafe (broadcastConjAccesses length)

theorem broadcastConjInBounds_proven : BroadcastConjInBounds := by
  intro length a ha
  simp only [broadcastConjAccesses, List.mem_append] at ha
  rcases ha with ha | ha <;> exact axisLoopInBounds_proven length a ha

def zipMul : List Nat → List Nat → List Nat
  | d :: ds, c :: cs => d * c :: zipMul ds cs
  | _, _ => []

def repeatCoords (inner : Bool) : List Nat → List Nat → List Int → List Int → List Int
  | d :: ds, c :: cs, i :: is, j :: js =>
      (if inner then (i - 1) * c + j else i + d * (j - 1)) ::
        repeatCoords inner ds cs is js
  | _, _, _, _ => []

private theorem repeatHead_bounds (d c : Nat) (i j : Int) (inner : Bool)
    (hi : 1 ≤ i ∧ i ≤ d) (hj : 1 ≤ j ∧ j ≤ c) :
    let out := if inner then (i - 1) * c + j else i + d * (j - 1)
    1 ≤ out ∧ out ≤ d * c := by
  dsimp
  cases inner with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hm0 : 0 ≤ (d : Int) * (j - 1) := Int.mul_nonneg (by omega) (by omega)
      have hm1 : (d : Int) * (j - 1) ≤ (d : Int) * ((c : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have heq : (d : Int) * ((c : Int) - 1) = d * c - d := by
        rw [Int.mul_sub, Int.mul_one]
      rw [heq] at hm1
      omega
  | true =>
      simp only [↓reduceIte]
      have hm0 : 0 ≤ (i - 1) * (c : Int) := Int.mul_nonneg (by omega) (by omega)
      have hm1 : (i - 1) * (c : Int) ≤ ((d : Int) - 1) * c :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have heq : ((d : Int) - 1) * c = d * c - c := by
        rw [Int.sub_mul, Int.one_mul]
      rw [heq] at hm1
      omega

private theorem repeatCoords_within : ∀ dims counts I J inner,
    dims.length = counts.length → coordsWithin dims I → coordsWithin counts J →
    coordsWithin (zipMul dims counts) (repeatCoords inner dims counts I J)
  | [], [], [], [], _, _, _, _ => by simp [coordsWithin, zipMul, repeatCoords]
  | d :: ds, c :: cs, i :: is, j :: js, inner, hlen, hI, hJ => by
      have hItail : coordsWithin ds is :=
        ⟨by simpa [coordsWithin] using hI.1,
         fun p hp => hI.2 p (List.mem_cons_of_mem _ hp)⟩
      have hJtail : coordsWithin cs js :=
        ⟨by simpa [coordsWithin] using hJ.1,
         fun p hp => hJ.2 p (List.mem_cons_of_mem _ hp)⟩
      have htail := repeatCoords_within ds cs is js inner (by simpa using hlen) hItail hJtail
      constructor
      · simpa [zipMul, repeatCoords] using congrArg Nat.succ htail.1
      · intro p hp
        simp only [zipMul, repeatCoords, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · apply repeatHead_bounds
          · exact hI.2 (d, i) (by simp)
          · exact hJ.2 (c, j) (by simp)
        · exact htail.2 p hp
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h, _ => by simp [coordsWithin] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h => by simp [coordsWithin] at h

/-- Generic `repeat_outer`/`repeat_inner`, `base/abstractarraymath.jl:583-611`.
The function computes `TIJ` componentwise from the two Cartesian loop indices,
then computes the unchecked column-major linear ordinal of `out[IJ]`. -/
def genericRepeatAccesses (dims counts : List Nat) (I J : List Int) (inner : Bool) : List Access :=
  if dims.length = counts.length && coordsWithinB dims I && coordsWithinB counts J then
    let outDims := zipMul dims counts
    let IJ := repeatCoords inner dims counts I J
    uncheckedCartesianAccess outDims IJ ++ uncheckedCartesianAccess dims I
  else []

def GenericRepeatInBounds : Prop := ∀ dims counts I J inner,
  accessesSafe (genericRepeatAccesses dims counts I J inner)

theorem genericRepeatInBounds_proven : GenericRepeatInBounds := by
  intro dims counts I J inner a ha
  simp only [genericRepeatAccesses] at ha
  split at ha
  · simp only [List.mem_append] at ha
    have hI : coordsWithin dims I := coordsWithinB_true dims I (by simp_all)
    have hJ : coordsWithin counts J := coordsWithinB_true counts J (by simp_all)
    rcases ha with ha | ha
    · apply uncheckedCartesian_safe _ _ (repeatCoords_within dims counts I J inner
        (by simp_all) hI hJ) a ha
    · exact uncheckedCartesian_safe dims I hI a ha
  · simp at ha

/-- Vector `repeat_outer`, `base/abstractarraymath.jl:573-581`.  The source
length and repetition count determine both allocation and every copied block. -/
def repeatVectorAccesses (size count : Nat) : List Access :=
  (List.range count).map fun j => span0 (size * count) (j * size) size

def RepeatVectorInBounds : Prop :=
  ∀ size count, accessesSafe (repeatVectorAccesses size count)

theorem repeatVectorInBounds_proven : RepeatVectorInBounds := by
  intro size count a h
  simp only [repeatVectorAccesses, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  simp only [List.mem_range] at hj
  simp only [Access.safe, span0]
  have hm := Nat.mul_le_mul_right size (Nat.succ_le_iff.mpr hj)
  simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using hm

/-- Matrix `repeat_outer`, `base/abstractarraymath.jl:559-571`.  One span is
copied for each input column in each `(i,j)` output tile. -/
def repeatMatrixAccesses (rows cols rowCopies colCopies : Nat) : List Access :=
  (List.range colCopies).flatMap fun j =>
    (List.range rowCopies).flatMap fun i =>
      (List.range cols).map fun q =>
        span0 ((rows * rowCopies) * (cols * colCopies))
          (i * rows + (rows * rowCopies) * (j * cols + q)) rows

def RepeatMatrixInBounds : Prop :=
  ∀ rows cols m n, accessesSafe (repeatMatrixAccesses rows cols m n)

theorem repeatMatrixInBounds_proven : RepeatMatrixInBounds := by
  intro rows cols m n a ha
  simp only [repeatMatrixAccesses, List.mem_flatMap, List.mem_range, List.mem_map] at ha
  obtain ⟨j, hj, i, hi, q, hq, rfl⟩ := ha
  simp only [Access.safe, span0]
  let outRows := rows * m
  let col := j * cols + q
  have hiBlock : i * rows + rows ≤ outRows := by
    have h := Nat.mul_le_mul_right rows (Nat.succ_le_iff.mpr hi)
    simpa [outRows, Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using h
  have hcol : col + 1 ≤ cols * n := by
    have hjmul := Nat.mul_le_mul_right cols (Nat.succ_le_iff.mpr hj)
    have hq1 : q + 1 ≤ cols := Nat.succ_le_iff.mpr hq
    dsimp [col]
    calc
      j * cols + q + 1 = j * cols + (q + 1) := by omega
      _ ≤ j * cols + cols := Nat.add_le_add_left hq1 _
      _ = (j + 1) * cols := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n * cols := hjmul
      _ = cols * n := Nat.mul_comm _ _
  calc
    i * rows + outRows * col + rows = (i * rows + rows) + outRows * col := by omega
    _ ≤ outRows + outRows * col := Nat.add_le_add_right hiBlock _
    _ = outRows * (col + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ outRows * (cols * n) := Nat.mul_le_mul_left outRows hcol

def RepeatVectorMatrixInBounds : Prop := RepeatVectorInBounds ∧ RepeatMatrixInBounds

theorem repeatVectorMatrixInBounds_proven : RepeatVectorMatrixInBounds :=
  ⟨repeatVectorInBounds_proven, repeatMatrixInBounds_proven⟩

end JuliaLean.MemSafety.G1
