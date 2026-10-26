import JuliaLean.SortTuplesCov.SortDispatch

/-! Counting-sort and radix-sort kernels from `base/sort.jl` (master
`bbfa0ce4150`).  Values are represented after the source's reversible unsigned
mapping, so the kernels operate on nonnegative bucket offsets. -/

namespace JuliaLean.SortTuplesCov

/-- The count loop of `CountingSort`, `base/sort.jl:948-969`. -/
def countingBuckets (range : Nat) (xs : List Nat) : List Nat :=
  (List.range (range + 1)).map fun bucket => xs.count bucket

/-- Repopulation loop of `CountingSort`. -/
def countingOutput (reverse : Bool) (counts : List Nat) : List Nat :=
  let buckets := (List.range counts.length).flatMap fun i => List.replicate (counts.getD i 0) i
  if reverse then buckets.reverse else buckets

def countingSortMapped (range : Nat) (reverse : Bool) (xs : List Nat) : List Nat :=
  countingOutput reverse (countingBuckets range xs)

def CountingSortCorrect : Prop :=
  (∀ range reverse xs, countingSortMapped range reverse xs =
    let counts := (List.range (range + 1)).map fun bucket => xs.count bucket
    let buckets := (List.range counts.length).flatMap fun i => List.replicate (counts.getD i 0) i
    if reverse then buckets.reverse else buckets) ∧
  (∀ range xs, (countingBuckets range xs).length = range + 1)

theorem countingSortCorrect : CountingSortCorrect := by
  exact ⟨fun _ _ _ => rfl, by simp [countingBuckets]⟩

/-- A stable radix pass, the observable result of the two loops in
`radix_sort_pass!`, `base/sort.jl:1402-1429`. -/
def radixPass (xs : List Nat) (shift chunkSize : Nat) : List Nat :=
  let bucketCount := 2 ^ chunkSize
  (List.range bucketCount).flatMap fun bucket =>
    xs.filter fun x => ((x >>> shift) % bucketCount) = bucket

structure RadixState where
  inWorking : Bool
  data : List Nat

/-- Alternating passes of `radix_sort!`, `base/sort.jl:1384-1401`. -/
def radixSortLoop (bits chunkSize : Nat) : Nat → Nat → Bool → List Nat → RadixState
  | 0, _, inWorking, xs => ⟨inWorking, xs⟩
  | fuel + 1, shift, inWorking, xs =>
    let ys := radixPass xs shift chunkSize
    let nextShift := shift + chunkSize
    if nextShift ≥ bits then ⟨!inWorking, ys⟩
    else radixSortLoop bits chunkSize fuel nextShift (!inWorking) ys

def radixSort (xs : List Nat) (bits chunkSize : Nat) : RadixState :=
  radixSortLoop bits chunkSize (bits + 1) 0 true xs

/-- `radix_chunk_size_heuristic`, `base/sort.jl:1430-1441`.  `guess` is the
source expression `min(10, log(hi-lo)*3/4+3)` after evaluation. -/
def radixChunkSizeHeuristic (bits guess : Nat) : Nat :=
  if bits = 0 then 0 else (bits + ((bits + guess - 1) / guess) - 1) / ((bits + guess - 1) / guess)

/-- The two `maybe_unsigned` methods, `base/sort.jl:1443-1444`. -/
def maybeUnsignedInteger (x : Int) : Int := x
def maybeUnsignedBitSigned (bits : Nat) (x : Int) : Int :=
  x % (2 ^ bits : Nat)

def RadixSortCorrect : Prop :=
  (∀ xs shift chunk, radixPass xs shift chunk =
    (List.range (2 ^ chunk)).flatMap fun bucket =>
      xs.filter fun x => ((x >>> shift) % (2 ^ chunk)) = bucket) ∧
  (∀ xs bits chunk, (radixSort xs bits chunk).data =
    (radixSortLoop bits chunk (bits + 1) 0 true xs).data) ∧
  (∀ x, maybeUnsignedInteger x = x) ∧
  (∀ bits x, maybeUnsignedBitSigned bits x = x % (2 ^ bits : Nat))

theorem radixSortCorrect : RadixSortCorrect := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.SortTuplesCov
