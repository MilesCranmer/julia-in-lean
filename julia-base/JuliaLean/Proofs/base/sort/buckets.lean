import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.dispatch
import JuliaLean.base.range
/-! Counting-sort and radix-sort kernels from `base/sort.jl` (master
`bbfa0ce4150`).  Values are represented after the source's reversible unsigned
mapping, so the kernels operate on nonnegative bucket offsets. -/

namespace JuliaLean.SortTuplesCov

def CountingSortCorrect : Prop :=
  (∀ range reverse xs, countingSortMapped range reverse xs =
    let counts := (List.range (range + 1)).map fun bucket => xs.count bucket
    let buckets := (List.range counts.length).flatMap fun i => List.replicate (counts.getD i 0) i
    if reverse then buckets.reverse else buckets) ∧
  (∀ range xs, (countingBuckets range xs).length = range + 1)

theorem countingSortCorrect : CountingSortCorrect := by
  exact ⟨fun _ _ _ => rfl, by simp [countingBuckets]⟩

def RadixSortCorrect : Prop :=
  (∀ xs shift chunk, radixPass xs shift chunk =
    (List.range (2 ^ chunk)).flatMap fun bucket =>
      xs.filter fun x => ((x >>> shift) % (2 ^ chunk)) = bucket) ∧
  (∀ xs bits chunk, (radixSort xs bits chunk).map (fun state => state.data) =
    (radixSortLoop bits chunk (bits + 1) 0 true xs).map (fun state => state.data)) ∧
  (∀ x, maybeUnsignedInteger x = x) ∧
  (∀ bits x, maybeUnsignedBitSigned bits x = x % (2 ^ bits : Nat))

theorem radixSortCorrect : RadixSortCorrect := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- With a zero chunk and positive bits, no number of passes can finish. -/
theorem radixSortLoop_zeroChunk (bits fuel : Nat) (hbits : 0 < bits) :
    ∀ inWorking xs, radixSortLoop bits 0 fuel 0 inWorking xs =
      .error (.errorException "fuel") := by
  induction fuel with
  | zero => intro inWorking xs; rfl
  | succ fuel ih =>
    intro inWorking xs
    simpa only [radixSortLoop, Nat.zero_add,
      if_neg (Nat.not_le.mpr hbits)] using ih (!inWorking) (radixPass xs 0 0)

theorem radixSort_zeroChunk (xs : List Nat) (bits : Nat) (hbits : 0 < bits) :
    radixSort xs bits 0 = .error (.errorException "fuel") :=
  radixSortLoop_zeroChunk bits (bits + 1) hbits true xs

/-- The source tests `bits` only after its first pass, even for zero bits. -/
theorem radixSort_zeroBits (xs : List Nat) (chunk : Nat) :
    radixSort xs 0 chunk = .ok ⟨false, radixPass xs 0 chunk⟩ := by
  simp [radixSort, radixSortLoop]

end JuliaLean.SortTuplesCov
