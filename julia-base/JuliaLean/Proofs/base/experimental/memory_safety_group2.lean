import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/experimental.jl:32-40`: `Experimental.Const.getindex` -/

def arrayAxes (dims : List Nat) : List Axis := dims.map Axis.oneTo

def normalizeDims (dims : List Nat) (n : Nat) : List Nat :=
  dims ++ List.replicate (n - dims.length) 1

def normalizeCoords (coords : List Int) (n : Nat) : List Int :=
  coords ++ List.replicate (n - coords.length) 1

def coordsCheck (dims : List Nat) (coords : List Int) : Bool :=
  let n := max dims.length coords.length
  let ds := normalizeDims dims n
  let is := normalizeCoords coords n
  (ds.zip is).all fun (d, i) => decide (1 ≤ i ∧ i ≤ d)

def sub2ind : List Nat → List Int → Int
  | [], _ => 1
  | _, [] => 1
  | [_], [i] => i
  | n :: ns, i :: is => i + n * (sub2ind ns is - 1)

def constLinearAccess (dims : List Nat) (i : Int) : List Access :=
  let n := product dims
  if 1 ≤ i && i ≤ n then [⟨n, i⟩] else []

def constCartesianAccess (dims : List Nat) (coords : List Int) : List Access :=
  let n := max dims.length coords.length
  let ds := normalizeDims dims n
  let is := normalizeCoords coords n
  if coordsCheck dims coords then
    [⟨product ds, sub2ind ds is⟩]
  else []

def ConstGetindexInBounds : Prop :=
  (∀ dims i, AllInBounds (constLinearAccess dims i)) ∧
  (∀ dims coords, AllInBounds (constCartesianAccess dims coords))


def relativeCoords : List Axis → List Int → List Int
  | [], [] => []
  | axes, [] => List.replicate axes.length 1
  | [], i :: is => i :: relativeCoords [] is
  | a :: axes, i :: is => (i - a.first.val + 1) :: relativeCoords axes is

def constCartesianAccessAxes (axes : List Axis) (coords : List Int) : List Access :=
  constCartesianAccess (axes.map (·.len)) (relativeCoords axes coords)




private theorem sub2ind_bounds : ∀ dims coords,
    dims.length = coords.length →
    (∀ p ∈ dims.zip coords, 1 ≤ p.2 ∧ p.2 ≤ p.1) →
    1 ≤ sub2ind dims coords ∧ sub2ind dims coords ≤ product dims
  | [], [], _, _ => by simp [sub2ind, product]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | [d], [i], _, h => by
      have hi := h (d, i) (by simp)
      simpa [sub2ind, product] using hi
  | d :: d2 :: ds, i :: i2 :: is, hlen, h => by
      have hd := h (d, i) (by simp)
      have htail : ∀ p ∈ (d2 :: ds).zip (i2 :: is), 1 ≤ p.2 ∧ p.2 ≤ p.1 := by
        intro p hp
        exact h p (by exact List.mem_cons_of_mem _ hp)
      have hlen' : (d2 :: ds).length = (i2 :: is).length := by simpa using hlen
      have ih := sub2ind_bounds (d2 :: ds) (i2 :: is) hlen' htail
      change 1 ≤ i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ∧
        i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * product (d2 :: ds)
      have hm0 : 0 ≤ (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) :=
        Int.mul_nonneg (by omega) (by omega)
      have hm1 : (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * ((product (d2 :: ds) : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hid : (d : Int) * ((product (d2 :: ds) : Int) - 1) =
          (d : Int) * product (d2 :: ds) - d := by
        rw [Int.mul_sub, Int.mul_one]
      rw [hid] at hm1
      omega

private theorem normalized_lengths (dims : List Nat) (coords : List Int) :
    (normalizeDims dims (max dims.length coords.length)).length =
      (normalizeCoords coords (max dims.length coords.length)).length := by
  simp [normalizeDims, normalizeCoords]
  omega

theorem constGetindexInBounds : ConstGetindexInBounds := by
  constructor
  · intro dims i access ha
    simp only [constLinearAccess] at ha
    split at ha
    · simp only [List.mem_singleton] at ha
      subst access
      simp only [Access.inBounds]
      simp_all
    · simp at ha
  · intro dims coords access ha
    simp only [constCartesianAccess] at ha
    split at ha
    · simp only [List.mem_singleton] at ha
      subst access
      simp only [Access.inBounds]
      apply sub2ind_bounds
      · exact normalized_lengths dims coords
      · intro p hp
        simp only [coordsCheck] at *
        have hall := of_decide_eq_true (List.all_eq_true.mp ‹_› p hp)
        exact hall
    · simp at ha

theorem constCartesianAccessAxes_safe (axes : List JuliaLean.AbstractArrays.Axis)
    (coords : List Int) : AllInBounds (constCartesianAccessAxes axes coords) := by
  simpa only [constCartesianAccessAxes] using
    constGetindexInBounds.2 (axes.map (fun axis => axis.len)) (relativeCoords axes coords)

end JuliaLean.MemSafety.G2
