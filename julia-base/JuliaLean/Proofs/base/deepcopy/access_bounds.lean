import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- A valid `Memory` has `length` elements backed by at least `length *
aligned_sizeof(T)` bytes. The allocator rejects sizes exceeding `Int`'s
positive range (`src/genericmemory.c:55-71`); externally wrapped storage must
also cover the declared extent. -/
structure DeepcopyMemory (α : Type) where
  elements : List (Option α)
  elementSize : Nat
  storageBytes : Nat
  extent : elements.length * elementSize ≤ storageBytes
  sizeFits : (elements.length * elementSize : Int) ≤ IntTy.max .i64

/-- The ordinary allocator returns the zero-length singleton first; otherwise
it rejects element counts or byte counts at least `MAXINTVAL - 1`. -/
def deepcopyAllocationSucceeds (x : DeepcopyMemory α) : Prop :=
  x.elements.length = 0 ∨
    (x.elements.length < 9223372036854775806 ∧
     x.elements.length * x.elementSize < 9223372036854775806)

instance (x : DeepcopyMemory α) : Decidable (deepcopyAllocationSucceeds x) := by
  unfold deepcopyAllocationSucceeds
  infer_instance

/-- The bits branch calls `copy`, which allocates the same number of elements
and calls the same-type `unsafe_copyto!` at offsets 1. The zero-length return
precedes pointer conversion; otherwise `memmove` receives the wrapping `Int`
product from `base/genericmemory.jl:197-207,223-225,257-263`. -/
def deepcopyBitsBytes (x : DeepcopyMemory α) : Option Int :=
  if deepcopyAllocationSucceeds x ∧ x.elements.length ≠ 0 then
    some (wrapInt .i64 ((x.elementSize : Int) * x.elements.length))
  else none

/-- `copy` allocates storage for the same element count and element layout. -/
def deepcopyDestinationBytes (x : DeepcopyMemory α) : Nat :=
  x.elements.length * x.elementSize

/-- Source references reached by `_deepcopy_memory_t`, after the isbits early
return, from `base/deepcopy.jl:108-127`. -/
def deepcopyMemoryAccesses (isbits : Bool) (x : List (Option α)) : List Nat :=
  if isbits then [] else oneBasedLoop x.length

/-- Destination references are created only for assigned source elements. -/
def deepcopyMemoryWrites (isbits : Bool) (x : List (Option α)) : List Nat :=
  (deepcopyMemoryAccesses isbits x).filter fun i => (x[i - 1]?).join.isSome

/-- The non-bits loop stays in bounds, and the bits path copies exactly the
allocated byte extent without integer overflow or an out-of-bounds span. -/
def DeepcopyMemorySafe : Prop :=
  (∀ (α : Type) (isbits : Bool) (x : List (Option α)) (i : Nat),
    i ∈ deepcopyMemoryAccesses isbits x → inOneBased x.length i) ∧
  (∀ (α : Type) (isbits : Bool) (x : List (Option α)) (i : Nat),
    i ∈ deepcopyMemoryWrites isbits x →
      inOneBased (List.replicate x.length (none : Option α)).length i) ∧
  (∀ (α : Type) (x : DeepcopyMemory α),
    (x.elements.length = 0 → deepcopyBitsBytes x = none) ∧
    (deepcopyAllocationSucceeds x → x.elements.length ≠ 0 →
      deepcopyBitsBytes x = some ((x.elements.length * x.elementSize : Nat) : Int) ∧
      x.elements.length * x.elementSize ≤ x.storageBytes ∧
      x.elements.length * x.elementSize ≤ deepcopyDestinationBytes x))

theorem deepcopyMemorySafe_proven : DeepcopyMemorySafe := by
  have sourceSafe : ∀ (α : Type) (isbits : Bool) (x : List (Option α)) i,
      i ∈ deepcopyMemoryAccesses isbits x → inOneBased x.length i := by
    intro α isbits x i hi
    cases isbits with
    | true => simp [deepcopyMemoryAccesses] at hi
    | false =>
      simp only [deepcopyMemoryAccesses, Bool.false_eq_true, ↓reduceIte,
        oneBasedLoop, List.mem_map, List.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      unfold inOneBased
      omega
  refine ⟨sourceSafe, ?_, ?_⟩
  · intro α isbits x i hi
    unfold deepcopyMemoryWrites at hi
    have hsource : i ∈ deepcopyMemoryAccesses isbits x := by
      exact (List.mem_filter.mp hi).1
    simpa only [List.length_replicate] using sourceSafe α isbits x i hsource
  · intro α x
    constructor
    · intro hz
      simp [deepcopyBitsBytes, hz]
    · intro ha hn
      have hmul : (x.elementSize : Int) * x.elements.length =
          (x.elements.length * x.elementSize : Nat) := by
        simp [Int.mul_comm]
      have hrange : IntTy.min .i64 ≤ (x.elements.length * x.elementSize : Nat) ∧
          (x.elements.length * x.elementSize : Int) ≤ IntTy.max .i64 := by
        constructor
        · simp only [IntTy.min, IntTy.signed, IntTy.bits]; omega
        · exact x.sizeFits
      refine ⟨?_, x.extent, ?_⟩
      · simp only [deepcopyBitsBytes, if_pos (And.intro ha hn), hmul]
        exact congrArg some (wrapInt_of_inRange .i64 _ hrange)
      · exact Nat.le_refl _

end JuliaLean.MemSafety.G3
