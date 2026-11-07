import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.bitarray.common.count
import JuliaLean.Proofs.base.bitarray.common.reshape

section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch5.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

/-- The range check used by the frozen split-rest proposition. -/
def b5SplitCheck (len count : I64) : BitMutationM Unit :=
  if int 0 ≤ count ∧ count ≤ len then pure ()
  else throw (.argument "requested count out of range")

/-- The list suffix callback used by the frozen split-rest proposition. -/
def b5SplitSuffix {α : Type} (xs : List α) (count : I64) : BitMutationM (List α) :=
  pure (xs.drop (xs.length - count.val.toNat))

/-- The list resize callback used by the frozen split-rest proposition. -/
def b5SplitResize {α : Type} (xs : List α) (len : I64) : BitMutationM (List α) :=
  pure (xs.take len.val.toNat)

/-- Exposing execution with an arbitrary state avoids reducing its storage representation. -/
theorem b5SplitRun {α : Type} (xs : List α) (n : I64) (s : State) :
    (bitArraySplitRest b5SplitCheck b5SplitSuffix b5SplitResize
      (fun values => int values.length) xs n).run s =
      if int 0 ≤ n ∧ n ≤ int xs.length then
        (.ok (xs.take (int xs.length - n).val.toNat,
          xs.drop (xs.length - n.val.toNat)), s)
      else (.error (.argument "requested count out of range"), s) := by
  unfold bitArraySplitRest b5SplitCheck b5SplitSuffix b5SplitResize
  by_cases h : int 0 ≤ n ∧ n ≤ int xs.length
  · simp only [h, and_self, ite_true]
    rfl
  · simp only [h, ite_false]
    rfl

/-- Subtracting an admissible count from a representable list length does not wrap. -/
theorem b5SplitSubtraction (length : Nat) (n : I64)
    (hnative : length ≤ 9223372036854775807)
    (hcheck : int 0 ≤ n ∧ n ≤ int length) :
    (int length - n).val.toNat = length - n.val.toNat := by
  have hlen := packedInt_val length hnative
  have hzero : 0 ≤ n.val := hcheck.1
  have hcount : n.val ≤ (length : Int) := by
    have hc := hcheck.2
    change n.val ≤ (int length).val at hc
    rw [hlen] at hc
    exact hc
  have hvalue : (int length - n).val = (length : Int) - n.val := by
    change wrapInt .i64 ((int length).val - n.val) = _
    rw [hlen]
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ (length : Int) - n.val ∧
      (length : Int) - n.val ≤ 9223372036854775807
    omega
  rw [hvalue]
  omega

/-- The complete bounded split-rest run, including all rejected counts and state preservation. -/
theorem b5SplitRunNative {α : Type} (xs : List α) (n : I64) (s : State)
    (hnative : xs.length ≤ 9223372036854775807) :
    (bitArraySplitRest b5SplitCheck b5SplitSuffix b5SplitResize
      (fun values => int values.length) xs n).run s =
      if int 0 ≤ n ∧ n ≤ int xs.length then
        (.ok (xs.take (xs.length - n.val.toNat),
          xs.drop (xs.length - n.val.toNat)), s)
      else (.error (.argument "requested count out of range"), s) := by
  rw [b5SplitRun]
  split
  · rename_i hcheck
    rw [b5SplitSubtraction xs.length n hnative hcheck]
  · rfl

/-- Every successful bounded split returns lists whose concatenation is the input. -/
theorem b5SplitPartitionNative {α : Type} (xs : List α) (n : I64) (s : State)
    (hnative : xs.length ≤ 9223372036854775807) (left right : List α) (s' : State)
    (hrun : (bitArraySplitRest b5SplitCheck b5SplitSuffix b5SplitResize
      (fun values => int values.length) xs n).run s = (.ok (left, right), s')) :
    left ++ right = xs ∧ s' = s := by
  rw [b5SplitRunNative xs n s hnative] at hrun
  split at hrun
  · cases hrun
    exact ⟨List.take_append_drop _ _, rfl⟩
  · cases hrun
end JuliaLean.ChatGPT.Batch5.Group1
end



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray


/-- Representation invariant for the supplied Vector{UInt64} heap. Unknown raw
isbits cells are allowed: slice/copy never performs an initialized-value read.
The byte-size bound is the native eight-byte allocation limit. There is no
nonnegative-n restriction and no disjointness assumption on old aliases. -/
def UInt64VectorDomain (s : Heap) (a : Nat) : Prop :=
  s.validVector a ∧ ∀ slots ∈ s.memories, slots.length < 2 ^ 60

/-- Every old header other than the resized vector retains its exact reference
and length, so aliases through another header remain the same views. -/
def SplitRestHeaderFrame (s after : Heap) (a : Nat) : Prop :=
  ∀ index header, s.arrays[index]? = some header → index ≠ a →
    after.arrays[index]? = some header

/-- A successful grow may copy the old prefix to the resulting vector's new
physical window. This is precisely the region where old backing bytes may change
when the storage implementation reuses and shifts within the original memory. -/
def SplitRestCopiedWindow (s after : Heap) (a memory cell : Nat) : Prop :=
  ∃ header, after.arrays[a]? = some header ∧ header.reference.1 = memory ∧
    header.reference.2.val - 1 ≤ (cell : Int) ∧
    (cell : Int) < header.reference.2.val - 1 + ((s.contents a).length : Int)

/-- UInt64 deletion does not clear raw cells. Growth preserves every old memory
length and every old cell outside the copied prefix window. Combined with prefix
preservation below, this fixes the observable effect on every shared-memory alias. -/
def SplitRestMemoryFrame (s after : Heap) (a : Nat) : Prop :=
  ∀ memory before, s.memories[memory]? = some before →
    ∃ current, after.memories[memory]? = some current ∧ current.length = before.length ∧
      ∀ cell, cell < before.length → ¬ SplitRestCopiedWindow s after a memory cell →
        current[cell]? = before[cell]?

/-- Fresh suffix allocation and exact object identity/mutation frame for a
successful call. The caller keeps the same prefix handle; existing other headers
are retained, including arbitrary aliases of its backing memory. -/
def SplitRestUInt64SuccessFrame (s after : Heap) (a prefixHandle suffix : Nat) : Prop :=
  prefixHandle = a ∧ suffix = s.arrays.length ∧
  after.arrays.length = s.arrays.length + 1 ∧
  s.memories.length + 1 ≤ after.memories.length ∧
  after.memories.length ≤ s.memories.length + 2 ∧
  after.validVector prefixHandle ∧ after.validVector suffix ∧
  SplitRestHeaderFrame s after a ∧ SplitRestMemoryFrame s after a

/-- Full native-n source-effects contract for the Vector{UInt64} specialization.
For 0 ≤ n ≤ length, the source is shortened to the prefix and a fresh suffix is
returned; all old bytes are unchanged. Requests larger than length throw the
source ArgumentError before mutation. Negative n retains the actual source
behavior: wrapping endpoint overflow can give BoundsError before allocation;
otherwise resize can grow, preserving the old prefix while new cells remain
unspecified, or fail with the actual allocation/checked-arithmetic error classes.
No successful result, error branch, or alias class is excluded by a precondition.
Sources: base/bitarray.jl:1941-1946; base/tuple.jl:255-259;
base/array.jl:1523-1530,1559-1574. -/
def SplitRestUInt64Effects : Prop :=
  ∀ (s : Heap) (a : Nat) (n : I64), UInt64VectorDomain s a →
    let before := s.contents a
    let len : Int := before.length
    let result := (JuliaLean.base.bitarray.Models1Group16.splitRestUInt64 a n).run s
    if len < n.val then
      result.1 = .error (.argument
        s!"The iterator only contains {before.length} elements, but at least {n.val} were requested.") ∧
      result.2 = s
    else if 0 ≤ n.val then
      ∃ prefixHandle suffix oldHeader newHeader,
        result.1 = .ok (prefixHandle, suffix) ∧
        SplitRestUInt64SuccessFrame s result.2 a prefixHandle suffix ∧
        result.2.contents prefixHandle = before.take (len - n.val).toNat ∧
        result.2.contents suffix = before.drop (len - n.val).toNat ∧
        s.arrays[a]? = some oldHeader ∧ result.2.arrays[a]? = some newHeader ∧
        newHeader.reference = oldHeader.reference ∧
        newHeader.size.val = len - n.val ∧
        result.2.memories.take s.memories.length = s.memories
    else if (2 : Int)^63 - 1 ≤ len - n.val then
      result.1 = .error .bounds ∧ result.2 = s
    else
      match result.1 with
      | .ok (prefixHandle, suffix) =>
          SplitRestUInt64SuccessFrame s result.2 a prefixHandle suffix ∧
          (result.2.contents prefixHandle).length = (len - n.val).toNat ∧
          (result.2.contents prefixHandle).take before.length = before ∧
          result.2.contents suffix = []
      | .error error =>
          PreservesExisting s result.2 ∧
          result.2.arrays.length = s.arrays.length + 1 ∧
          result.2.memories.length = s.memories.length + 1 ∧
          result.2.contents s.arrays.length = [] ∧
          match error with
          | .argument _ => True
          | .overflow => True
          | _ => False

/-- The independent split_rest partition promise, on the complete represented
UInt64 Vector/native-Int domain. Errors are permitted, but every success must
partition the old sequence in order. This deliberately includes negative n and
can therefore be refuted by the known negative-count behavior; it is not weakened
to a nonnegative precondition. The separate Effects property constrains which
errors are possible and records all source mutation/alias effects.
Documentation: base/tuple.jl:215-226. Implementation: base/bitarray.jl:1941-1946. -/
def SplitRestUInt64Partition : Prop :=
  ∀ (s : Heap) (a : Nat) (n : I64), UInt64VectorDomain s a →
    let result := (JuliaLean.base.bitarray.Models1Group16.splitRestUInt64 a n).run s
    match result.1 with
    | .ok (prefixHandle, suffix) =>
        s.contents a = result.2.contents prefixHandle ++ result.2.contents suffix
    | .error _ => True
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group16


def splitEmptyHeap : Heap := ⟨[[]], [⟨(0, int 1), int 0⟩]⟩

theorem splitEmptyDomain : UInt64VectorDomain splitEmptyHeap 0 := by
  unfold UInt64VectorDomain splitEmptyHeap
  decide

theorem Models1G16SplitRestU64Partition_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.SplitRestUInt64Partition := by
  intro h
  have hv := h splitEmptyHeap 0 (int (-1)) splitEmptyDomain
  change ([] : List (Option U64)) = [none] at hv
  cases hv
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesSplitRest1 : List JuliaLean.Registry.Entry := [
  { id := "tuples-split-rest-negative", juliaFile := "base/bitarray.jl", juliaFns := ["split_rest(v::Vector, n)", "_split_rest(a::Union{Vector,BitVector}, n)"],
    statement := "Base.split_rest(v, n) for a Vector either throws or returns (rest_but_n, last_n) whose concatenation is v.", source := "base/tuple.jl:215-226 (split_rest docstring: the first collection contains all elements but the n last ones, which make up the second)",
    status := .todo, prop := ``SplitRestPartition, thm := none, notes := "Statement defect: xs = replicate (2^64) false and n = Int64(0) passes the injected check at wrapped length zero but returns an empty prefix instead of xs; Julia cannot construct this input; require xs.length \u2264 typemax(Int)." }
]
def entriesSplitRest2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-split-rest-u64-effects", juliaFile := "base/bitarray.jl",
    juliaFns := ["_split_rest(::Vector{UInt64}, ::Int)"],
    statement := "Splitting a UInt64 vector checks excessive counts first, returns an exact prefix/suffix for nonnegative counts, and retains native negative-count wrap, growth, allocation errors and shared-memory mutation frames.",
    source := "base/bitarray.jl:1941-1946; base/tuple.jl:215-226,255-259; base/array.jl:981-990,1559-1574", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.SplitRestUInt64Effects, thm := none,
    notes := "No complete exact proof returned. splitRestNativeLengthBound and splitRestExcessiveCount prove the native length bound and exact excessive-count ArgumentError with an unchanged heap; remaining goal: nonnegative splitting, negative-count growth and wrap, allocation errors, and mutation frames." },
  { id := "bitarray-split-rest-u64-partition", juliaFile := "base/bitarray.jl",
    juliaFns := ["_split_rest(::Vector{UInt64}, ::Int)"],
    statement := "Every successful UInt64-vector split preserves the original sequence as returned prefix followed by suffix, over the full represented native count domain, including negative counts.",
    source := "base/bitarray.jl:1941-1946; base/tuple.jl:215-226,255-259; base/array.jl:981-990,1559-1574", issue := "Searched JuliaLang/julia issues and PRs; no duplicate found; see bugs/tuples-split-rest-negative.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.SplitRestUInt64Partition, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16SplitRestU64Partition_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/tuples-split-rest-negative.yaml." }
]
end JuliaLean.Proofs.base.bitarray

