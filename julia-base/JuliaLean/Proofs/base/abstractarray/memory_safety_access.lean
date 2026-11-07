import JuliaLean.Core

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

structure Access where
  capacity : Nat
  start : Nat
  count : Nat
  deriving Repr, DecidableEq

def Access.safe (a : Access) : Prop := a.start + a.count ≤ a.capacity

def accessesSafe (xs : List Access) : Prop := ∀ a ∈ xs, a.safe

def at0 (capacity index : Nat) : Access := ⟨capacity, index, 1⟩
def span0 (capacity start count : Nat) : Access := ⟨capacity, start, count⟩

/-- The access trace of a loop over `eachindex`, `axes`, `keys`, or `pairs` of
the same linear storage. -/
def axisAccesses (length : Nat) : List Access :=
  (List.range length).map (at0 length)

def AxisLoopInBounds : Prop := ∀ length, accessesSafe (axisAccesses length)

theorem axisLoopInBounds_proven : AxisLoopInBounds := by
  intro length a h
  simp only [axisAccesses, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [List.mem_range] at hi
  simp [Access.safe, at0]
  omega

def shapeProduct (dims : List Nat) : Nat := dims.foldr (· * ·) 1

def normalizeDims (dims : List Nat) (n : Nat) : List Nat :=
  dims ++ List.replicate (n - dims.length) 1

def normalizeCoords (coords : List Int) (n : Nat) : List Int :=
  coords ++ List.replicate (n - coords.length) 1

/-- `_sub2ind_recurse`, `base/abstractarray.jl:3165-3208`, for one-based Array
axes. -/
def sub2ind : List Nat → List Int → Int
  | [], _ => 1
  | _, [] => 1
  | [_], [i] => i
  | d :: ds, i :: is => i + d * (sub2ind ds is - 1)

theorem sub2ind_bounds : ∀ dims coords,
    dims.length = coords.length →
    (∀ p ∈ dims.zip coords, 1 ≤ p.2 ∧ p.2 ≤ p.1) →
    1 ≤ sub2ind dims coords ∧ sub2ind dims coords ≤ shapeProduct dims
  | [], [], _, _ => by simp [sub2ind, shapeProduct]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | [d], [i], _, h => by
      have hi := h (d, i) (by simp)
      simpa [sub2ind, shapeProduct] using hi
  | d :: d2 :: ds, i :: i2 :: is, hlen, h => by
      have hd := h (d, i) (by simp)
      have htail : ∀ p ∈ (d2 :: ds).zip (i2 :: is), 1 ≤ p.2 ∧ p.2 ≤ p.1 := by
        intro p hp
        exact h p (List.mem_cons_of_mem _ hp)
      have hlen' : (d2 :: ds).length = (i2 :: is).length := by simpa using hlen
      have ih := sub2ind_bounds (d2 :: ds) (i2 :: is) hlen' htail
      change 1 ≤ i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ∧
        i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * shapeProduct (d2 :: ds)
      have hm0 : 0 ≤ (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) :=
        Int.mul_nonneg (by omega) (by omega)
      have hm1 : (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * ((shapeProduct (d2 :: ds) : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hid : (d : Int) * ((shapeProduct (d2 :: ds) : Int) - 1) =
          (d : Int) * shapeProduct (d2 :: ds) - d := by
        rw [Int.mul_sub, Int.mul_one]
      rw [hid] at hm1
      omega

def coordsWithin (dims : List Nat) (coords : List Int) : Prop :=
  dims.length = coords.length ∧
    ∀ p ∈ dims.zip coords, 1 ≤ p.2 ∧ p.2 ≤ p.1

def coordsWithinB (dims : List Nat) (coords : List Int) : Bool :=
  decide (dims.length = coords.length) &&
    (dims.zip coords).all fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1

theorem coordsWithinB_true (dims : List Nat) (coords : List Int)
    (h : coordsWithinB dims coords = true) : coordsWithin dims coords := by
  unfold coordsWithinB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun p hp => of_decide_eq_true (List.all_eq_true.mp h.2 p hp)⟩

def uncheckedCartesianAccess (dims : List Nat) (coords : List Int) : List Access :=
  [at0 (shapeProduct dims) (sub2ind dims coords - 1).toNat]

theorem uncheckedCartesian_safe (dims : List Nat) (coords : List Int)
    (h : coordsWithin dims coords) : accessesSafe (uncheckedCartesianAccess dims coords) := by
  intro a ha
  simp only [uncheckedCartesianAccess, List.mem_singleton] at ha
  subst a
  simp only [Access.safe, at0]
  have hb := sub2ind_bounds dims coords h.1 h.2
  have hc : ((sub2ind dims coords - 1).toNat : Int) = sub2ind dims coords - 1 :=
    Int.toNat_of_nonneg (by omega)
  omega

end JuliaLean.MemSafety.G1
