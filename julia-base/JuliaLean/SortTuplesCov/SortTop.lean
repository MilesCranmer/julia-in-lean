import JuliaLean.SortTuplesCov.SortCountingRadix

/-! Public sorting wrappers, tuple merge sort, permutation wrappers, and
multidimensional routing from `base/sort.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

/-! ### Vector and tuple sort wrappers -/

/-- `sort!(v; ...)`, `base/sort.jl:1732-1741`, after `ord` and
`maybe_apply_initial_optimizations` have been evaluated. -/
def sortVectorBang {V : Type} (core : List V → List V) (v : List V) : List V := core v

/-- `sort(v::AbstractVector; kws...)`, `base/sort.jl:1780`.  The pair records
that the source is unchanged and the copied result is sorted. -/
def sortVectorCopy {V : Type} (core : List V → List V) (v : List V) : List V × List V :=
  (v, core v)

/-- `sort` on KeySet and ValueIterator, `base/sort.jl:1782-1783`. -/
def sortCollected {V : Type} (collect : List V) (core : List V → List V) : List V := core collect

/-- Tuple `merge`, `base/sort.jl:1814-1818`. -/
def mergeSorted {V : Type} (lt : V → V → Bool) : List V → List V → List V
  | xs, [] => xs
  | [], ys => ys
  | x :: xs, y :: ys =>
    if lt y x then y :: mergeSorted lt (x :: xs) ys
    else x :: mergeSorted lt xs (y :: ys)
termination_by xs ys => xs.length + ys.length

/-- `_mergesort(x::NTuple, o)`, `base/sort.jl:1809-1813`, with fuel equal to
the tuple length. -/
def tupleMergeSort {V : Type} (lt : V → V → Bool) : Nat → List V → List V
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, xs =>
    let n := xs.length / 2
    mergeSorted lt (tupleMergeSort lt fuel (xs.take n)) (tupleMergeSort lt fuel (xs.drop n))

/-- Default tuple `_sort`, `base/sort.jl:1798-1808`. -/
def sortTupleDefault {V : Type} (vectorCore : List V → List V)
    (lt : V → V → Bool) (xs : List V) : List V :=
  if xs.length > 9 then vectorCore xs else tupleMergeSort lt (xs.length + 1) xs

def TopLevelSortCorrect : Prop :=
  (∀ (V : Type) core (v : List V), sortVectorBang core v = core v) ∧
  (∀ (V : Type) core (v : List V), (sortVectorCopy core v).1 = v ∧
    (sortVectorCopy core v).2 = core v) ∧
  (∀ (V : Type) lt (xs : List V), mergeSorted lt xs [] = xs) ∧
  (∀ (V : Type) lt (ys : List V), mergeSorted lt [] ys = ys) ∧
  (∀ (V : Type) core lt (xs : List V), xs.length > 9 →
    sortTupleDefault core lt xs = core xs)

theorem topLevelSortCorrect : TopLevelSortCorrect := by
  refine ⟨by simp [sortVectorBang], by simp [sortVectorCopy], by simp [mergeSorted],
    by intro V lt ys; cases ys <;> simp [mergeSorted], ?_⟩
  intro V core lt xs h
  simp [sortTupleDefault, h]

/-! ### Permutation wrappers -/

inductive SortpermRoute where
  | integerRangeFastPath | generic
  deriving DecidableEq

/-- `sortperm`, `base/sort.jl:1966-1979`: explicit branching on `rev`. -/
def sortpermOrderingChoice (rev : RevChoice) : Bool := reverseRequested rev

/-- `_sortperm`, `base/sort.jl:1980-1994`, after extrema and overflow checks. -/
def sortpermRoute (forward vector integerElements moreThanOne noOverflow shortRange : Bool) :
    SortpermRoute :=
  if forward && vector && integerElements && moreThanOne && noOverflow && shortRange then
    .integerRangeFastPath
  else .generic

/-- `sortperm!`, `base/sort.jl:2037-2055`, recording validation and the
initialized linear indices. -/
def sortpermBang (axesMatch vectorDimsConflict : Bool) (length : Nat) : Except String (List Nat) :=
  if vectorDimsConflict then .error "Dims argument incorrect for type"
  else if !axesMatch then .error "index array must have the same axes"
  else .ok ((List.range length).map (.+1))

/-- `partialsortperm!`, `base/sort.jl:1896-1915`, including the axes check and
unconditional index initialization (`initialized` is accepted but unused). -/
def partialsortpermBang (axesMatch initialized : Bool) (length : Nat) : Except String (List Nat) :=
  if !axesMatch then .error "index vector must have the same axes"
  else
    let _ := initialized
    .ok ((List.range length).map (.+1))

def SortpermWrappersCorrect : Prop :=
  sortpermOrderingChoice .true_ = true ∧ sortpermOrderingChoice .false_ = false ∧
  (∀ f v i n o r, f && v && i && n && o && r = true →
    sortpermRoute f v i n o r = .integerRangeFastPath) ∧
  (∀ n, sortpermBang true false n = .ok ((List.range n).map (.+1))) ∧
  (∀ n initialized, partialsortpermBang true initialized n =
    .ok ((List.range n).map (.+1)))

theorem sortpermWrappersCorrect : SortpermWrappersCorrect := by
  refine ⟨by decide, by decide, ?_, by simp [sortpermBang], by simp [partialsortpermBang]⟩
  intro f v i n o r h
  cases f <;> cases v <;> cases i <;> cases n <;> cases o <;> cases r <;>
    simp_all [sortpermRoute]

/-! ### Multidimensional sorting -/

inductive ArraySortRoute where
  | firstDimension | permutedDimension
  deriving DecidableEq

/-- `sort(A; dims)`, `base/sort.jl:2112-2134`. -/
def arraySortRoute (dimension : Int) : ArraySortRoute :=
  if dimension = 1 then .firstDimension else .permutedDimension

inductive ChunkScratchRoute where
  | noScratch | acquiredScratch | reusedScratch
  deriving DecidableEq

/-- The three `sort_chunks!` methods, `base/sort.jl:2136-2154`. -/
def sortChunksRoute (scratchPresent nestedProducedScratch : Bool) : ChunkScratchRoute :=
  if scratchPresent then .reusedScratch
  else if nestedProducedScratch then .acquiredScratch else .noScratch

/-- Local `get_view` and `get_value`, `base/sort.jl:2205-2206,2224`. -/
def getViewIndices (selectedDimension : Nat) (idx : List Nat) (ndims : Nat) : List (Option Nat) :=
  (List.range ndims).map fun i => if i + 1 = selectedDimension then none else idx[i]?
def getValue (x : Nat) : Nat := x

def MultidimensionalSortCorrect : Prop :=
  arraySortRoute 1 = .firstDimension ∧
  (∀ d, d ≠ 1 → arraySortRoute d = .permutedDimension) ∧
  sortChunksRoute true false = .reusedScratch ∧
  sortChunksRoute false true = .acquiredScratch ∧
  sortChunksRoute false false = .noScratch ∧
  (∀ x, getValue x = x) ∧
  (∀ d idx n, (getViewIndices d idx n).length = n)

theorem multidimensionalSortCorrect : MultidimensionalSortCorrect := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by simp [getValue], ?_⟩
  · intro d h
    simp [arraySortRoute, h]
  · intro d idx n
    simp [getViewIndices]

end JuliaLean.SortTuplesCov
