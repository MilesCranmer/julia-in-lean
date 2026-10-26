import JuliaLean.SortTuplesCov.SortUInt

/-! Legacy QuickSort, MergeSort, and PartialQuickSort kernels from
`base/sort.jl:2401-2595` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

section

variable {V : Type} [Inhabited V]

def midpointInt (lo hi : Int) : Int := lo + (hi - lo) / 2

/-- `selectpivot!`, `base/sort.jl:2409-2429`. -/
def selectPivot (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V × V :=
  let mi := midpointInt lo hi
  let v := if lt (JuliaLean.Sort.rd v lo) (JuliaLean.Sort.rd v mi) then
    let a := JuliaLean.Sort.rd v lo
    let b := JuliaLean.Sort.rd v mi
    JuliaLean.Sort.wr (JuliaLean.Sort.wr v mi a) lo b else v
  let v := if lt (JuliaLean.Sort.rd v hi) (JuliaLean.Sort.rd v lo) then
    if lt (JuliaLean.Sort.rd v hi) (JuliaLean.Sort.rd v mi) then
      let a := JuliaLean.Sort.rd v hi
      let b := JuliaLean.Sort.rd v lo
      let c := JuliaLean.Sort.rd v mi
      JuliaLean.Sort.wr (JuliaLean.Sort.wr (JuliaLean.Sort.wr v hi b) lo c) mi a
    else
      let a := JuliaLean.Sort.rd v hi
      let b := JuliaLean.Sort.rd v lo
      JuliaLean.Sort.wr (JuliaLean.Sort.wr v hi b) lo a
    else v
  (v, JuliaLean.Sort.rd v lo)

def scanLess (lt : V → V → Bool) (pivot : V) : Nat → Array V → Int → Int
  | 0, _, i => i
  | fuel + 1, v, i => if lt (JuliaLean.Sort.rd v i) pivot then scanLess lt pivot fuel v (i + 1) else i

def scanGreater (lt : V → V → Bool) (pivot : V) : Nat → Array V → Int → Int
  | 0, _, j => j
  | fuel + 1, v, j => if lt pivot (JuliaLean.Sort.rd v j) then scanGreater lt pivot fuel v (j - 1) else j

def partitionLoop (lt : V → V → Bool) (pivot : V) (lo : Int) :
    Nat → Array V → Int → Int → Array V × Int
  | 0, v, _, j => (JuliaLean.Sort.wr (JuliaLean.Sort.wr v j pivot) lo (JuliaLean.Sort.rd v j), j)
  | fuel + 1, v, i, j =>
    let i := scanLess lt pivot fuel v (i + 1)
    let j := scanGreater lt pivot fuel v (j - 1)
    if i ≥ j then (JuliaLean.Sort.wr (JuliaLean.Sort.wr v j pivot) lo (JuliaLean.Sort.rd v j), j)
    else
      let a := JuliaLean.Sort.rd v i
      let b := JuliaLean.Sort.rd v j
      partitionLoop lt pivot lo fuel (JuliaLean.Sort.wr (JuliaLean.Sort.wr v i b) j a) i j

/-- Old `partition!`, `base/sort.jl:2435-2452`. -/
def legacyPartition (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V × Int :=
  let p := selectPivot lt v lo hi
  partitionLoop lt p.2 lo (hi - lo + 2).toNat p.1 lo hi

/-- `_quicksort!`, `base/sort.jl:2459-2478`. -/
def quickSortLoop (lt : V → V → Bool) : Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, lo, hi =>
    if lo < hi then
      if hi - lo ≤ 20 then JuliaLean.Sort.insertionSort lt v lo hi
      else
        let p := legacyPartition lt v lo hi
        let j := p.2
        if j - lo < hi - j then
          let w := if lo < j - 1 then quickSortLoop lt fuel p.1 lo (j - 1) else p.1
          quickSortLoop lt fuel w (j + 1) hi
        else
          let w := if j + 1 < hi then quickSortLoop lt fuel p.1 (j + 1) hi else p.1
          quickSortLoop lt fuel w lo (j - 1)
    else v

def quickSort (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V :=
  quickSortLoop lt (hi - lo + 2).toNat v lo hi

def copyLeftLoop (v : Array V) (lo : Int) : Nat → Array V → Array V
  | 0, t => t
  | fuel + 1, t => copyLeftLoop v lo fuel (JuliaLean.Sort.wr t (fuel + 1) (JuliaLean.Sort.rd v (lo + fuel)))

def mergeMainLoop (lt : V → V → Bool) (hi : Int) :
    Nat → Array V → Array V → Int → Int → Int → Array V × Int × Int × Int
  | 0, v, _, i, j, k => (v, i, j, k)
  | fuel + 1, v, t, i, j, k =>
    if k < j && j ≤ hi then
      if lt (JuliaLean.Sort.rd v j) (JuliaLean.Sort.rd t i) then
        mergeMainLoop lt hi fuel (JuliaLean.Sort.wr v k (JuliaLean.Sort.rd v j)) t i (j + 1) (k + 1)
      else
        mergeMainLoop lt hi fuel (JuliaLean.Sort.wr v k (JuliaLean.Sort.rd t i)) t (i + 1) j (k + 1)
    else (v, i, j, k)

def mergeRemainder (t : Array V) : Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, i, k => mergeRemainder t fuel (JuliaLean.Sort.wr v k (JuliaLean.Sort.rd t i)) (i + 1) (k + 1)

/-- `_mergesort!`, `base/sort.jl:2488-2531`. -/
def mergeSortLoop (lt : V → V → Bool) : Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, lo, hi =>
    if lo < hi then
      if hi - lo ≤ 20 then JuliaLean.Sort.insertionSort lt v lo hi
      else
        let m := midpointInt lo hi
        let v := mergeSortLoop lt fuel v lo m
        let v := mergeSortLoop lt fuel v (m + 1) hi
        let leftLength := (m - lo + 1).toNat
        let t := copyLeftLoop v lo leftLength (Array.replicate leftLength default)
        let r := mergeMainLoop lt hi (hi - lo + 1).toNat v t 1 (m + 1) lo
        mergeRemainder t (r.2.2.2 - r.2.1).toNat r.1 r.2.1 r.2.2.2
    else v

def mergeSort (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V :=
  mergeSortLoop lt (hi - lo + 2).toNat v lo hi

/-- `_partialquicksort!`, `base/sort.jl:2539-2566`. -/
def partialQuickSortLoop (lt : V → V → Bool) (firstTarget lastTarget : Int) :
    Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, lo, hi =>
    if lo < hi then
      if hi - lo ≤ 20 then JuliaLean.Sort.insertionSort lt v lo hi
      else
        let p := legacyPartition lt v lo hi
        let j := p.2
        if j ≤ firstTarget then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 (j + 1) hi
        else if j ≥ lastTarget then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 lo (j - 1)
        else if j - lo < hi - j then
          let w := if lo < j - 1 then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 lo (j - 1) else p.1
          partialQuickSortLoop lt firstTarget lastTarget fuel w (j + 1) hi
        else
          let w := if j + 1 < hi then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 (j + 1) hi else p.1
          partialQuickSortLoop lt firstTarget lastTarget fuel w lo (j - 1)
    else v

def partialQuickSort (lt : V → V → Bool) (firstTarget lastTarget : Int)
    (v : Array V) (lo hi : Int) : Array V :=
  partialQuickSortLoop lt firstTarget lastTarget (hi - lo + 2).toNat v lo hi

def LegacySortKernelsCorrect : Prop :=
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    (selectPivot lt v lo hi).2 = JuliaLean.Sort.rd (selectPivot lt v lo hi).1 lo) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi, hi ≤ lo →
    quickSort lt v lo hi = v) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    lo < hi → hi - lo ≤ 20 → quickSort lt v lo hi =
      JuliaLean.Sort.insertionSort lt v lo hi) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    lo < hi → hi - lo ≤ 20 → mergeSort lt v lo hi =
      JuliaLean.Sort.insertionSort lt v lo hi) ∧
  (∀ (V : Type) [Inhabited V] lt f l (v : Array V) lo hi,
    lo < hi → hi - lo ≤ 20 → partialQuickSort lt f l v lo hi =
      JuliaLean.Sort.insertionSort lt v lo hi)

/- The size proofs for the recursive kernels follow because every mutation is
an Array modification.  They are kept together so the registry property uses
all three method bodies. -/
theorem legacySortKernelsCorrect : LegacySortKernelsCorrect := by
  refine ⟨by intros; simp [selectPivot], ?_, ?_, ?_, ?_⟩
  · intro V inst lt v lo hi
    intro h
    unfold quickSort
    generalize (hi - lo + 2).toNat = fuel
    cases fuel <;> simp [quickSortLoop, show ¬ lo < hi by omega]
  · intro V inst lt v lo hi hlo hsmall
    have hfuel : 0 < (hi - lo + 2).toNat := by omega
    cases hfuelEq : (hi - lo + 2).toNat with
    | zero => simp_all
    | succ fuel => simp [quickSort, hfuelEq, quickSortLoop, hlo, hsmall]
  · intro V inst lt v lo hi hlo hsmall
    have hfuel : 0 < (hi - lo + 2).toNat := by omega
    cases hfuelEq : (hi - lo + 2).toNat with
    | zero => simp_all
    | succ fuel => simp [mergeSort, hfuelEq, mergeSortLoop, hlo, hsmall]
  · intro V inst lt f l v lo hi hlo hsmall
    have hfuel : 0 < (hi - lo + 2).toNat := by omega
    cases hfuelEq : (hi - lo + 2).toNat with
    | zero => simp_all
    | succ fuel => simp [partialQuickSort, hfuelEq, partialQuickSortLoop, hlo, hsmall]

end

end JuliaLean.SortTuplesCov
