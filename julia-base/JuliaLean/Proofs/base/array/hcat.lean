import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy
import JuliaLean.Proofs.base.array.common.grow

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem empty_memory_get_bounds (α : Type) (i : I) :
    (mutableGet (α := α) 0 i).run
      ⟨[[]], [⟨(0, one), zero⟩]⟩ =
        (.error .bounds, ⟨[[]], [⟨(0, one), zero⟩]⟩) := by
  have invalid : ¬ (1 ≤ i.val ∧ i ≤ zero) := by
    change ¬ (1 ≤ i.val ∧ i.val ≤ 0)
    omega
  change ((if !(decide (1 ≤ i.val ∧ i ≤ zero)) then
      (fun s : MutableMemory α => ((Except.error .bounds : Except Error α), s))
    else _) ⟨[[]], [⟨(0, one), zero⟩]⟩) = _
  simp only [invalid, decide_false, Bool.not_false, ↓reduceIte]

/-- Empty concatenation produces a zero-length Vector{Any}; no integer index
can read an element. The default DimensionMismatch has the empty message. -/
def EmptyConcatSpec : Prop :=
  dimensionMismatch.message = "" ∧
  ∀ (α : Type) (i : I),
    let allocate := fun n => do
      let handle ← mutableAllocate (α := α) (some ⟨8, true, false⟩) 0 n
      pure (StoredType.any, handle)
    (∃ handle memory,
      (vcatEmpty allocate).run ⟨[], []⟩ = (.ok (.any, handle), memory) ∧
      (mutableLength (α := α) handle).run memory = (.ok zero, memory) ∧
      memory.contents handle = [] ∧
      (mutableGet (α := α) handle i).run memory = (.error .bounds, memory)) ∧
    (∃ handle memory,
      (hcatEmpty allocate).run ⟨[], []⟩ = (.ok (.any, handle), memory) ∧
      (mutableLength (α := α) handle).run memory = (.ok zero, memory) ∧
      memory.contents handle = [] ∧
      (mutableGet (α := α) handle i).run memory = (.error .bounds, memory))

theorem emptyConcatSpec : EmptyConcatSpec := by
  refine ⟨rfl, ?_⟩
  intro α i
  constructor
  · exact ⟨0, ⟨[[]], [⟨(0, one), zero⟩]⟩, rfl, rfl, rfl, empty_memory_get_bounds α i⟩
  · exact ⟨0, ⟨[[]], [⟨(0, one), zero⟩]⟩, rfl, rfl, rfl, empty_memory_get_bounds α i⟩
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section HeapRanges

attribute [local irreducible] JInt.wrap wrapInt

/-! ### Same-type vertical concatenation -/

/-- One step of `for a in arrays; n += length(a); end` (array.jl:2348-2350). -/
def vcatLengthStep {Tag α : Type} (a : HeapArray Tag) (r : I) : VectorM α (ForInStep I) := do
  let l ← heapLength a.handle
  pure (ForInStep.yield (r + l))

/-- `vcat(arrays::Vector{T}...)` (array.jl:2346) with the native allocator for element type
`target` and the source `unsafe_copyto!`. -/
abbrev heapVcat {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag) (arrays : List (HeapArray Tag)) :
    VectorM α (HeapArray Tag) :=
  vcat (fun a => heapLength a.handle) (fun n => heapAllocateIntDims layout target [n])
    heapColonMemoryCopy arrays

theorem vcat_total_loop {Tag α : Type} (heap : VectorHeap α) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (n : I) (hn : 0 ≤ n.val)
    (hsum : n.val + ((contents.map List.length).sum : Int) < 4611686018427387904) :
    (forIn arrays n vcatLengthStep).run heap =
      .ok (JInt.wrap .i64 (n.val + (contents.map List.length).sum), heap) := by
  induction arrays generalizing contents n with
  | nil =>
    cases contents with
    | nil =>
      simp only [List.forIn_nil, vector_pure_run, List.map_nil, List.sum_nil, Int.natCast_zero,
        Int.add_zero]
      congr
      exact (Subtype.ext (ival_wrap _ (ival_bounds n))).symm
    | cons c cs => simp at hc
  | cons a as ih =>
    cases contents with
    | nil => simp at hc
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hc
      obtain ⟨ha, hcs⟩ := hc
      simp only [List.map_cons, List.sum_cons, Int.natCast_add] at hsum
      have hcn : c.length < 2 ^ 62 := by
        show c.length < 4611686018427387904
        omega
      obtain ⟨hl, hv⟩ := heapLength_of_slots heap a.handle c ha hcn
      have hnv : (n + JInt.wrap .i64 (c.length : Int)).val = n.val + c.length := by
        rw [ival_add n (JInt.wrap .i64 (c.length : Int)) (by rw [hv]; omega), hv]
      simp only [List.forIn_cons, vcatLengthStep, vector_bind_run, hl, vector_pure_run]
      rw [ih cs hcs (n + JInt.wrap .i64 (c.length : Int)) (by rw [hnv]; clear hv hnv hl; omega)
        (by rw [hnv]; clear hv hnv hl; omega)]
      simp only [hnv, List.map_cons, List.sum_cons, Int.natCast_add, Int.add_assoc]

/-- `vcat(arrays::Vector{T}...)` (array.jl:2346): a fresh `Vector{T}` holding the slots of the
arguments one after another (unassigned slots included), with every argument untouched. -/
def VcatSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (l : MemoryLayout) (target : Tag)
    (heap : VectorHeap α) (arrays : List (HeapArray Tag)) (contents : List (List (Option α))),
    layout target = some l →
    arrays.map (fun a => heap[a.handle]?) = contents.map some →
    (∀ c ∈ contents, c.length < 2 ^ 63) →
    let total := (contents.map List.length).sum
    let n := (JInt.wrap .i64 (total : Int)).val
    let run := (heapVcat layout target arrays).run heap
    (∀ e, arrayAllocError l [n] = some e → run = .error e) ∧
    (arrayAllocError l [n] = none → (total : Int) = n →
      run = .ok (⟨heap.length, target, [total], [(1, total)]⟩, heap ++ [contents.flatten])) ∧
    (arrayAllocError l [n] = none →
      ∀ (pre : List (List (Option α))) (c : List (Option α)) post, contents = pre ++ c :: post →
      (pre.map List.length).sum ≤ n.toNat → n.toNat < (pre.map List.length).sum + c.length →
      run = .error (if (pre.map List.length).sum + c.length < typemaxNat
        then .assertion "Concurrent modification of arrays?" else .bounds))
end HeapRanges
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `hcat(V::Vector{T}...)` (array.jl:2335) on typed heap arrays: `V[j]` is the `j`-th argument,
element reads are the checked `getindex`, the `::T` assertion holds for elements of a
`Vector{T}`, and the comprehension `[V[j][i]::T for i=1:h, j=1:n]` is `collect` of a generator of
shape `(h, n)` iterated in column-major order, whose inferred element type is `T`. -/
def typedHcatCollectOps {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) :
    GeneratorCollectOps (VectorM α) (MatrixGenerator (VectorM α) (List I) α)
      α Tag Unit (List Nat) (List α) (HeapArray Tag) where
  size _ := ()
  defaultEltype _ := et
  unknown _ := false
  emptyVector _ := pure ⟨0, et, [], []⟩
  grow a _ := pure a
  shape g _ := pure (g.iter.iterators.map List.length)
  iterate g := do
    let xs ← ((g.iter.iterators[1]?.getD []).flatMap fun j =>
      (g.iter.iterators[0]?.getD []).map fun i => [i, j]).mapM g.f
    pure (match xs with | [] => none | x :: t => some (x, t))
  typeof := L.typeof
  arrayForInner t _ shp := heapAllocateArray layout t shp
  isTypeSubtype _ := false
  typeType := et
  anyType := et
  isAbstractArray _ := true
  isConcrete _ := true
  ndims _ := one
  abstractArrayType t _ _ := t
  collectWithFirst b v _ st := typedCollectWithFirst layout L b v (v :: st) st
  typeassert a _ := pure a

def typedHcat {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (T : Tag) (vs : List (HeapArray Tag)) :
    VectorM α (HeapArray Tag) :=
  hcat (fun vs j => match vs[(j.val - 1).toNat]? with
      | some v => pure v
      | none => throw .bounds)
    (fun a => heapLength a.handle) (fun a i => heapGet a.handle i) pure
    (fun a b => pure (intRange a b))
    (fun cs k => match cs[(k.val - 1).toNat]? with
      | some c => pure c
      | none => throw .bounds)
    (typedHcatCollectOps layout L T)
    vs

/-- The `hcat` docstring promise for vectors of one element type, as the old entry stated it:
`hcat(V::Vector{T}...)` is a `Matrix{T}` (the same element type as `cat(V...; dims=2)` and
`vcat(V...)`). -/
def HcatEltypeSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (T : Tag) (heap : VectorHeap α)
    (vs : List (HeapArray Tag)) (h : Nat),
    vs ≠ [] → 0 < h →
    (∀ v ∈ vs, v.elementType = T ∧ ∃ xs : List α, xs.length = h ∧ heap[v.handle]? = some (xs.map some) ∧
      ∀ x ∈ xs, L.isa x T = true) →
    ∃ r next, (typedHcat layout L T vs).run heap = .ok (r, next) ∧ r.elementType = T

/-- A two-type universe for the counterexample: every value is an `Int`, which is also an `Any`. -/
inductive HcatDemoType where
  | int
  | any
  deriving DecidableEq

def hcatDemoLattice : TypeLattice HcatDemoType Int where
  typeof _ := .int
  isa _ _ := true
  join s t := if s = t then s else .any
  isa_typeof _ := rfl
  isa_join_left _ _ _ _ := rfl
  isa_join_right _ _ _ _ := rfl

/-- The heap holding `Any[1]` and `Any[2]`. -/
def hcatDemoHeap : VectorHeap Int := [[some 1], [some 2]]

def hcatDemoVectors : List (HeapArray HcatDemoType) :=
  [⟨0, .any, [1], [(1, 1)]⟩, ⟨1, .any, [1], [(1, 1)]⟩]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `hcat(V::Vector{T}...)` (array.jl:2335) on typed heap arrays: `V[j]` is the `j`-th argument,
element reads are the checked `getindex`, the `::T` assertion holds for elements of a
`Vector{T}`, and the comprehension `[V[j][i]::T for i=1:h, j=1:n]` is `collect` of a generator of
shape `(h, n)` iterated in column-major order, whose inferred element type is `T`. -/
def typedHcatCollectOps {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) :
    GeneratorCollectOps (VectorM α) (MatrixGenerator (VectorM α) (List I) α)
      α Tag Unit (List Nat) (List α) (HeapArray Tag) where
  size _ := ()
  defaultEltype _ := et
  unknown _ := false
  emptyVector _ := pure ⟨0, et, [], []⟩
  grow a _ := pure a
  shape g _ := pure (g.iter.iterators.map List.length)
  iterate g := do
    let xs ← ((g.iter.iterators[1]?.getD []).flatMap fun j =>
      (g.iter.iterators[0]?.getD []).map fun i => [i, j]).mapM g.f
    pure (match xs with | [] => none | x :: t => some (x, t))
  typeof := L.typeof
  arrayForInner t _ shp := heapAllocateArray layout t shp
  isTypeSubtype _ := false
  typeType := et
  anyType := et
  isAbstractArray _ := true
  isConcrete _ := true
  ndims _ := one
  abstractArrayType t _ _ := t
  collectWithFirst b v _ st := typedCollectWithFirst layout L b v (v :: st) st
  typeassert a _ := pure a

def typedHcat {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (T : Tag) (vs : List (HeapArray Tag)) :
    VectorM α (HeapArray Tag) :=
  hcat (fun vs j => match vs[(j.val - 1).toNat]? with
      | some v => pure v
      | none => throw .bounds)
    (fun a => heapLength a.handle) (fun a i => heapGet a.handle i) pure
    (fun a b => pure (intRange a b))
    (fun cs k => match cs[(k.val - 1).toNat]? with
      | some c => pure c
      | none => throw .bounds)
    (typedHcatCollectOps layout L T)
    vs

def HcatEltypeSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (T : Tag) (heap : VectorHeap α)
    (vs : List (HeapArray Tag)) (columns : List (List α)),
    vs ≠ [] → vs.length = columns.length → vs.length < 2 ^ 31 →
    (∀ p ∈ vs.zip columns, p.1.elementType = T ∧ p.2.length < 2 ^ 31 ∧
      heap[p.1.handle]? = some (p.2.map some) ∧ p.1.dimensions = [p.2.length] ∧
      ∀ x ∈ p.2, L.isa x T = true) →
    let h := (columns.headD []).length
    ((∀ c ∈ columns, c.length = h) →
      ∃ r next, (typedHcat layout L T vs).run heap = .ok (r, next) ∧ r.elementType = T ∧
        r.dimensions = [h, vs.length] ∧
        next[r.handle]? = some ((List.range vs.length).flatMap (fun j =>
          ((columns[j]?).getD []).map some))) ∧
    ((∃ c ∈ columns, c.length ≠ h) →
      (typedHcat layout L T vs).run heap = .error (.dimensionMismatch "vectors must have same lengths"))
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.ArrayExtra
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.int

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem batchWrapValue (t : IntTy) (n : Int) :
    (JInt.wrap t n).val = wrapInt t n := rfl

theorem batchAddValue (a b : I) :
    (a + b).val = wrapInt .i64 (a.val + b.val) := rfl
end ChatGPTBatch1.ArrayExtra
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.ArrayExtra
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.int

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

attribute [local irreducible] JInt.wrap wrapInt

/-- Reading an existing heap length is exact throughout the nonnegative Int range. -/
theorem batchHeapLengthOfSlots (heap : VectorHeap α) (handle : Nat) (xs : List (Option α))
    (hs : heap[handle]? = some xs) (hn : xs.length < 9223372036854775808) :
    (heapLength handle).run heap = .ok (JInt.wrap .i64 xs.length, heap) ∧
      (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
  refine ⟨by simp only [heapLength_run, hs], ival_wrap _ ?_⟩
  omega

/-- The length sum follows wrapping Int addition even when the mathematical sum overflows. -/
theorem batchVcatTotalLoop {Tag α : Type} (heap : VectorHeap α)
    (arrays : List (HeapArray Tag)) (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some) (n : I) :
    (forIn arrays n vcatLengthStep).run heap =
      .ok (JInt.wrap .i64 (n.val + (contents.map List.length).sum), heap) := by
  induction arrays generalizing contents n with
  | nil =>
    cases contents with
    | nil =>
      simp only [List.forIn_nil, vector_pure_run, List.map_nil, List.sum_nil,
        Int.natCast_zero, Int.add_zero]
      congr 2
      exact (Subtype.ext (ival_wrap _ (ival_bounds n))).symm
    | cons c cs => simp only [List.map_nil, List.map_cons] at hc; cases hc
  | cons a as ih =>
    cases contents with
    | nil => simp only [List.map_cons, List.map_nil] at hc; cases hc
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hc
      obtain ⟨ha, hcs⟩ := hc
      simp only [List.forIn_cons, vcatLengthStep, vector_bind_run,
        heapLength_run, ha, vector_pure_run]
      rw [ih cs hcs]
      congr 2
      apply Subtype.ext
      simp only [batchWrapValue, batchAddValue]
      rw [wrapInt_add_left]
      rw [Int.add_right_comm n.val (wrapInt .i64 c.length)]
      rw [wrapInt_add_right]
      simp only [List.map_cons, List.sum_cons, Int.natCast_add]
      congr 1
      omega


theorem batchVcatCopyLoop {Tag α : Type} (heap : VectorHeap α) (arr : HeapArray Tag)
    (harr : arr.handle = heap.length) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (pre : List (Option α)) (total : Nat)
    (htotal : pre.length + (contents.map List.length).sum = total)
    (htb : total < 9223372036854775807) :
    (forIn arrays (JInt.wrap .i64 ((pre.length : Int) + 1)) (vcatCopyStep arr)).run
        (heap ++ [pre ++ List.replicate (total - pre.length) none]) =
      .ok (JInt.wrap .i64 ((total : Int) + 1), heap ++ [pre ++ contents.flatten]) := by
  induction arrays generalizing contents pre with
  | nil =>
    cases contents with
    | nil =>
      simp only [List.map_nil, List.sum_nil, Nat.add_zero] at htotal
      subst htotal
      simp only [List.forIn_nil, vector_pure_run, Nat.sub_self, List.replicate_zero,
        List.flatten_nil]
    | cons c cs => simp at hc
  | cons a as ih =>
    cases contents with
    | nil => simp at hc
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hc
      obtain ⟨ha, hcs⟩ := hc
      simp only [List.map_cons, List.sum_cons] at htotal
      have halt : a.handle < heap.length := (List.getElem?_eq_some_iff.mp ha).choose
      have hsrc : (heap ++ [pre ++ List.replicate (total - pre.length) none])[a.handle]? =
          some c := by rw [List.getElem?_append_left halt]; exact ha
      have hdst : (heap ++ [pre ++ List.replicate (total - pre.length) none])[arr.handle]? =
          some (pre ++ List.replicate (total - pre.length) none) := by rw [harr]; simp
      have hdlen : (pre ++ List.replicate (total - pre.length) (none : Option α)).length =
          total := by simp; omega
      have hct : c.length < 9223372036854775808 := by omega
      have hpt : pre.length + c.length ≤ total := by omega
      obtain ⟨hal, hav⟩ := batchHeapLengthOfSlots _ a.handle c hsrc hct
      obtain ⟨harl, harv⟩ := batchHeapLengthOfSlots _ arr.handle _ hdst (by
        rw [hdlen]; omega)
      rw [hdlen] at harl harv
      have hnd : (JInt.wrap .i64 ((pre.length : Int) + 1)).val = pre.length + 1 :=
        ival_wrap _ (by clear hav harv hal harl; omega)
      have hsum : (JInt.wrap .i64 ((pre.length : Int) + 1) + JInt.wrap .i64 (c.length : Int)).val =
          pre.length + 1 + c.length := by
        rw [ival_add (JInt.wrap .i64 ((pre.length : Int) + 1)) (JInt.wrap .i64 (c.length : Int))
          (by rw [hnd, hav]; clear hnd hav harv hal harl; omega), hnd, hav]
      have hlimit : (one + JInt.wrap .i64 (total : Int)).val = 1 + total := by
        rw [ival_add one (JInt.wrap .i64 (total : Int))
          (by rw [ival_one, harv]; clear hnd hav harv hsum hal harl; omega), ival_one, harv]
      have hcond : decide (JInt.wrap .i64 ((pre.length : Int) + 1) +
          JInt.wrap .i64 (c.length : Int) ≤ one + JInt.wrap .i64 (total : Int)) = true := by
        rw [decide_eq_true_eq, jle_iff, hsum, hlimit]
        clear hnd hav harv hsum hlimit hal harl
        omega
      have hnext : JInt.wrap .i64 ((pre.length : Int) + 1) + JInt.wrap .i64 (c.length : Int) =
          JInt.wrap .i64 (((pre ++ c).length : Int) + 1) := by
        apply Subtype.ext
        rw [hsum, ival_wrap (((pre ++ c).length : Int) + 1)
          (by simp; clear hnd hav harv hsum hlimit hcond hal harl; omega)]
        simp
        clear hnd hav harv hsum hlimit hcond hal harl
        omega
      have htotal' : (pre ++ c).length + (cs.map List.length).sum = total := by
        simp; clear hnd hav harv hsum hlimit hcond hal harl hnext; omega
      have hrest := ih cs hcs (pre ++ c) htotal'
      have hflat : pre ++ (c :: cs).flatten = (pre ++ c) ++ cs.flatten := by
        simp [List.append_assoc]
      by_cases hcz : c = []
      · subst hcz
        simp only [List.append_nil] at hnext hrest
        have hstep := vcatCopyStep_run arr a _ _ _ _ _ hal harl hcond
          (heapUnsafeCopy_zero_run _ _ _ _ _ _ (by rw [hav]; rfl))
        simp only [List.forIn_cons, vector_bind_run, hstep]
        rw [hnext, hrest, hflat, List.append_nil]
      · have hcp : 0 < c.length := List.length_pos_iff.mpr hcz
        have hcopy := heapUnsafeCopy_run _ arr a c _ hsrc hdst
          (JInt.wrap .i64 ((pre.length : Int) + 1)) one (JInt.wrap .i64 (c.length : Int))
          (by rw [hav]; exact_mod_cast hcp) (by rw [hnd]; clear hnd hav harv hsum hlimit; omega)
          (by rw [hnd, hav, hdlen]; clear hnd hav harv hsum hlimit; omega)
          (by rw [ival_one]; exact Int.le_refl 1)
          (by rw [ival_one, hav]; clear hnd hav harv hsum hlimit; omega)
        have hwin : (pre ++ List.replicate (total - pre.length) none).take
              ((JInt.wrap .i64 ((pre.length : Int) + 1)).val - 1).toNat ++
            (c.drop (one.val - 1).toNat).take (JInt.wrap .i64 (c.length : Int)).val.toNat ++
            (pre ++ List.replicate (total - pre.length) none).drop
              ((JInt.wrap .i64 ((pre.length : Int) + 1)).val - 1 +
                (JInt.wrap .i64 (c.length : Int)).val).toNat =
            (pre ++ c) ++ List.replicate (total - (pre ++ c).length) none := by
          rw [hnd, hav, ival_one]
          have h1 : ((pre.length : Int) + 1 - 1).toNat = pre.length := by
            clear hnd hav harv hsum hlimit hcopy; omega
          have h2 : ((pre.length : Int) + 1 - 1 + c.length).toNat = pre.length + c.length := by
            clear hnd hav harv hsum hlimit hcopy; omega
          rw [h1, h2, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero,
            Int.toNat_natCast, List.take_length, List.take_left' rfl, List.drop_append,
            List.drop_replicate]
          simp only [List.length_append, List.append_assoc, Nat.sub_sub]
          rw [List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append]
          congr 3
          clear hnd hav harv hsum hlimit hcopy hcond hnext
          omega
        rw [hwin] at hcopy
        have hset : (heap ++ [pre ++ List.replicate (total - pre.length) none]).set arr.handle
            ((pre ++ c) ++ List.replicate (total - (pre ++ c).length) none) =
            heap ++ [(pre ++ c) ++ List.replicate (total - (pre ++ c).length) none] := by
          rw [harr]; simp [List.set_append_right]
        rw [hset] at hcopy
        have hstep := vcatCopyStep_run arr a _ _ _ _ _ hal harl hcond hcopy
        simp only [List.forIn_cons, vector_bind_run, hstep]
        rw [hnext, hrest, hflat]


theorem batchVcatCopyPrefix {Tag α : Type} (heap : VectorHeap α) (arr : HeapArray Tag)
    (harr : arr.handle = heap.length) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α))) (tail : List (HeapArray Tag))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (pre : List (Option α)) (total : Nat)
    (htotal : pre.length + (contents.map List.length).sum ≤ total)
    (htb : total < 9223372036854775807) :
    (forIn (arrays ++ tail) (JInt.wrap .i64 ((pre.length : Int) + 1)) (vcatCopyStep arr)).run
        (heap ++ [pre ++ List.replicate (total - pre.length) none]) =
      (forIn tail (JInt.wrap .i64 (((pre ++ contents.flatten).length : Int) + 1))
        (vcatCopyStep arr)).run
          (heap ++ [(pre ++ contents.flatten) ++
            List.replicate (total - (pre ++ contents.flatten).length) none]) := by
  induction arrays generalizing contents pre with
  | nil =>
    cases contents with
    | nil =>
      simp only [List.nil_append, List.flatten_nil, List.append_nil]
    | cons c cs => simp at hc
  | cons a as ih =>
    cases contents with
    | nil => simp at hc
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hc
      obtain ⟨ha, hcs⟩ := hc
      simp only [List.map_cons, List.sum_cons] at htotal
      have halt : a.handle < heap.length := (List.getElem?_eq_some_iff.mp ha).choose
      have hsrc : (heap ++ [pre ++ List.replicate (total - pre.length) none])[a.handle]? =
          some c := by rw [List.getElem?_append_left halt]; exact ha
      have hdst : (heap ++ [pre ++ List.replicate (total - pre.length) none])[arr.handle]? =
          some (pre ++ List.replicate (total - pre.length) none) := by rw [harr]; simp
      have hdlen : (pre ++ List.replicate (total - pre.length) (none : Option α)).length =
          total := by simp; omega
      have hct : c.length < 9223372036854775808 := by omega
      have hpt : pre.length + c.length ≤ total := by omega
      obtain ⟨hal, hav⟩ := batchHeapLengthOfSlots _ a.handle c hsrc hct
      obtain ⟨harl, harv⟩ := batchHeapLengthOfSlots _ arr.handle _ hdst (by
        rw [hdlen]; omega)
      rw [hdlen] at harl harv
      have hnd : (JInt.wrap .i64 ((pre.length : Int) + 1)).val = pre.length + 1 :=
        ival_wrap _ (by clear hav harv hal harl; omega)
      have hsum : (JInt.wrap .i64 ((pre.length : Int) + 1) + JInt.wrap .i64 (c.length : Int)).val =
          pre.length + 1 + c.length := by
        rw [ival_add (JInt.wrap .i64 ((pre.length : Int) + 1)) (JInt.wrap .i64 (c.length : Int))
          (by rw [hnd, hav]; clear hnd hav harv hal harl; omega), hnd, hav]
      have hlimit : (one + JInt.wrap .i64 (total : Int)).val = 1 + total := by
        rw [ival_add one (JInt.wrap .i64 (total : Int))
          (by rw [ival_one, harv]; clear hnd hav harv hsum hal harl; omega), ival_one, harv]
      have hcond : decide (JInt.wrap .i64 ((pre.length : Int) + 1) +
          JInt.wrap .i64 (c.length : Int) ≤ one + JInt.wrap .i64 (total : Int)) = true := by
        rw [decide_eq_true_eq, jle_iff, hsum, hlimit]
        clear hnd hav harv hsum hlimit hal harl
        omega
      have hnext : JInt.wrap .i64 ((pre.length : Int) + 1) + JInt.wrap .i64 (c.length : Int) =
          JInt.wrap .i64 (((pre ++ c).length : Int) + 1) := by
        apply Subtype.ext
        rw [hsum, ival_wrap (((pre ++ c).length : Int) + 1)
          (by simp; clear hnd hav harv hsum hlimit hcond hal harl; omega)]
        simp
        clear hnd hav harv hsum hlimit hcond hal harl
        omega
      have htotal' : (pre ++ c).length + (cs.map List.length).sum ≤ total := by
        simp; clear hnd hav harv hsum hlimit hcond hal harl hnext; omega
      have hrest := ih cs hcs (pre ++ c) htotal'
      have hflat : pre ++ (c :: cs).flatten = (pre ++ c) ++ cs.flatten := by
        simp [List.append_assoc]
      by_cases hcz : c = []
      · subst hcz
        simp only [List.append_nil] at hnext hrest
        have hstep := vcatCopyStep_run arr a _ _ _ _ _ hal harl hcond
          (heapUnsafeCopy_zero_run _ _ _ _ _ _ (by rw [hav]; rfl))
        simp only [List.cons_append, List.forIn_cons, vector_bind_run, hstep]
        rw [hnext, hrest, hflat, List.append_nil]
      · have hcp : 0 < c.length := List.length_pos_iff.mpr hcz
        have hcopy := heapUnsafeCopy_run _ arr a c _ hsrc hdst
          (JInt.wrap .i64 ((pre.length : Int) + 1)) one (JInt.wrap .i64 (c.length : Int))
          (by rw [hav]; exact_mod_cast hcp) (by rw [hnd]; clear hnd hav harv hsum hlimit; omega)
          (by rw [hnd, hav, hdlen]; clear hnd hav harv hsum hlimit; omega)
          (by rw [ival_one]; exact Int.le_refl 1)
          (by rw [ival_one, hav]; clear hnd hav harv hsum hlimit; omega)
        have hwin : (pre ++ List.replicate (total - pre.length) none).take
              ((JInt.wrap .i64 ((pre.length : Int) + 1)).val - 1).toNat ++
            (c.drop (one.val - 1).toNat).take (JInt.wrap .i64 (c.length : Int)).val.toNat ++
            (pre ++ List.replicate (total - pre.length) none).drop
              ((JInt.wrap .i64 ((pre.length : Int) + 1)).val - 1 +
                (JInt.wrap .i64 (c.length : Int)).val).toNat =
            (pre ++ c) ++ List.replicate (total - (pre ++ c).length) none := by
          rw [hnd, hav, ival_one]
          have h1 : ((pre.length : Int) + 1 - 1).toNat = pre.length := by
            clear hnd hav harv hsum hlimit hcopy; omega
          have h2 : ((pre.length : Int) + 1 - 1 + c.length).toNat = pre.length + c.length := by
            clear hnd hav harv hsum hlimit hcopy; omega
          rw [h1, h2, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero,
            Int.toNat_natCast, List.take_length, List.take_left' rfl, List.drop_append,
            List.drop_replicate]
          simp only [List.length_append, List.append_assoc, Nat.sub_sub]
          rw [List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append]
          congr 3
          clear hnd hav harv hsum hlimit hcopy hcond hnext
          omega
        rw [hwin] at hcopy
        have hset : (heap ++ [pre ++ List.replicate (total - pre.length) none]).set arr.handle
            ((pre ++ c) ++ List.replicate (total - (pre ++ c).length) none) =
            heap ++ [(pre ++ c) ++ List.replicate (total - (pre ++ c).length) none] := by
          rw [harr]; simp [List.set_append_right]
        rw [hset] at hcopy
        have hstep := vcatCopyStep_run arr a _ _ _ _ _ hal harl hcond hcopy
        simp only [List.cons_append, List.forIn_cons, vector_bind_run, hstep]
        rw [hnext, hrest, hflat]



def batchVcatOutcome {Tag α : Type} (arrays : List (HeapArray Tag))
    (outcome : Except Error (HeapArray Tag × VectorHeap α)) :
    Except Error (HeapArray Tag × VectorHeap α) :=
  match outcome with
  | .error err => .error err
  | .ok (arr, heap') =>
    match (forIn arrays one (vcatCopyStep arr)).run heap' with
    | .error err => .error err
    | .ok (_, heap'') => .ok (arr, heap'')

theorem batchVcatBodyRun {Tag α : Type} (allocate : I → VectorM α (HeapArray Tag))
    (arrays : List (HeapArray Tag)) (heap : VectorHeap α) (n : I)
    (outcome : Except Error (HeapArray Tag × VectorHeap α))
    (hcount : (forIn arrays zero vcatLengthStep).run heap = .ok (n, heap))
    (halloc : (allocate n).run heap = outcome) :
    ((do let total ← forIn arrays zero vcatLengthStep
         let arr ← allocate total
         let _ ← forIn arrays one (vcatCopyStep arr)
         pure arr : VectorM α (HeapArray Tag)).run heap) =
      batchVcatOutcome arrays outcome := by
  simp only [vector_bind_run, hcount, halloc, batchVcatOutcome, vector_pure_run]
  cases outcome with
  | error e => rfl
  | ok p =>
    rcases p with ⟨arr, heap'⟩
    dsimp only
    cases hr : (forIn arrays one (vcatCopyStep arr)).run heap' with
    | error e => simp only [hr]
    | ok p => cases p; simp only [hr]

theorem batchHeapAllocateIntDimsRun {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (l : MemoryLayout) (target : Tag) (hl : layout target = some l)
    (n : I) (heap : VectorHeap α) :
    (heapAllocateIntDims layout target [n]).run heap = allocOutcome l target [n.val] heap := by
  simp only [heapAllocateIntDims, opusGrowth.heapArrayUndef_run layout target l hl,
    List.map_cons, List.map_nil]

/-- The source vcat separates into its length loop, native allocation, and copy loop. -/
theorem batchVcatRun {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (l : MemoryLayout) (target : Tag) (hl : layout target = some l)
    (heap : VectorHeap α) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some) :
    (heapVcat layout target arrays).run heap =
      batchVcatOutcome arrays
        (allocOutcome l target [(JInt.wrap .i64 ((contents.map List.length).sum : Int)).val] heap) := by
  have hsum := batchVcatTotalLoop heap arrays contents hc zero
  simp only [ival_zero, Int.zero_add] at hsum
  exact batchVcatBodyRun (fun n => heapAllocateIntDims layout target [n]) arrays heap _ _
    hsum (batchHeapAllocateIntDimsRun layout l target hl _ heap)

theorem batchAllocOutcomeError {Tag α : Type} (l : MemoryLayout) (target : Tag)
    (dims : List Int) (heap : VectorHeap α) (e : Error)
    (h : arrayAllocError l dims = some e) : allocOutcome l target dims heap = .error e := by
  simp only [allocOutcome, h]

theorem batchVcatOutcomeError {Tag α : Type} (arrays : List (HeapArray Tag))
    (outcome : Except Error (HeapArray Tag × VectorHeap α)) (e : Error)
    (h : outcome = .error e) : batchVcatOutcome arrays outcome = .error e := by
  rw [h]
  rfl

theorem batchAllocOutcomeSuccess {Tag α : Type} (l : MemoryLayout) (target : Tag)
    (dims : List Int) (heap : VectorHeap α) (h : arrayAllocError l dims = none) :
    allocOutcome l target dims heap =
      .ok (⟨heap.length, target, dims.map Int.toNat,
        (dims.map Int.toNat).map (fun n => (1, n))⟩,
        heap ++ [List.replicate (dims.map Int.toNat).prod none]) := by
  simp only [allocOutcome, h]

theorem batchVcatOutcomeSuccess {Tag α : Type} (arrays : List (HeapArray Tag))
    (arr : HeapArray Tag) (heap heap' : VectorHeap α) (k : I)
    (h : (forIn arrays one (vcatCopyStep arr)).run heap = .ok (k, heap')) :
    batchVcatOutcome arrays (.ok (arr, heap)) = .ok (arr, heap') := by
  simp only [batchVcatOutcome, h]

theorem batchVcatOutcomeCopyError {Tag α : Type} (arrays : List (HeapArray Tag))
    (arr : HeapArray Tag) (heap : VectorHeap α) (e : Error)
    (h : (forIn arrays one (vcatCopyStep arr)).run heap = .error e) :
    batchVcatOutcome arrays (.ok (arr, heap)) = .error e := by
  simp only [batchVcatOutcome, h]

/-- Allocator rejections occur after the wrapped length sum and before any copying. -/
theorem batchVcatAllocationFailure {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (l : MemoryLayout) (target : Tag) (hl : layout target = some l)
    (heap : VectorHeap α) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (e : Error)
    (he : arrayAllocError l [(JInt.wrap .i64 ((contents.map List.length).sum : Int)).val] = some e) :
    (heapVcat layout target arrays).run heap = .error e := by
  exact (batchVcatRun layout l target hl heap arrays contents hc).trans
    (batchVcatOutcomeError arrays _ e (batchAllocOutcomeError l target _ heap e he))

/-- A successful allocation bounds the mathematical size away from Int overflow. -/
theorem batchArraySizeBound (l : MemoryLayout) (n : Int)
    (h : arrayAllocError l [n] = none) :
    0 ≤ n ∧ n < 9223372036854775806 := by
  change (if n < 0 ∨ ¬ memoryFits l n.toNat then
    some (Error.argument genericMemorySizeMessage) else none) = none at h
  have hgood : ¬ (n < 0 ∨ ¬ memoryFits l n.toNat) := by
    intro hbad
    rw [if_pos hbad] at h
    cases h
  have hn : 0 ≤ n := by omega
  have hm : memoryFits l n.toNat := by
    by_cases hm : memoryFits l n.toNat
    · exact hm
    · exact False.elim (hgood (Or.inr hm))
  have hb := hm.1
  unfold maxIntVal at hb
  constructor
  · exact hn
  · omega

/-- vcat has exactly the documented fresh output whenever its mathematical size fits. -/
theorem batchVcatSuccess {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (l : MemoryLayout) (target : Tag) (hl : layout target = some l)
    (heap : VectorHeap α) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (halloc : arrayAllocError l [(JInt.wrap .i64 ((contents.map List.length).sum : Int)).val] = none)
    (hn : ((contents.map List.length).sum : Int) =
      (JInt.wrap .i64 ((contents.map List.length).sum : Int)).val) :
    (heapVcat layout target arrays).run heap =
      .ok (⟨heap.length, target, [(contents.map List.length).sum],
        [(1, (contents.map List.length).sum)]⟩, heap ++ [contents.flatten]) := by
  have hb := batchArraySizeBound l _ halloc
  rw [← hn] at hb
  have hnat : (JInt.wrap .i64 ((contents.map List.length).sum : Int)).val.toNat =
      (contents.map List.length).sum := by rw [← hn]; rfl
  have ha := batchAllocOutcomeSuccess l target
    [(JInt.wrap .i64 ((contents.map List.length).sum : Int)).val] heap halloc
  simp only [List.map_cons, List.map_nil, hnat,
    List.prod_cons, List.prod_nil, Nat.mul_one] at ha
  have hcopy := batchVcatCopyLoop heap
    (⟨heap.length, target, [(contents.map List.length).sum],
      [(1, (contents.map List.length).sum)]⟩ : HeapArray Tag) rfl arrays contents hc []
      (contents.map List.length).sum (by simp only [List.length_nil, Nat.zero_add]) (by omega)
  simp only [List.length_nil, Int.natCast_zero, Int.zero_add, List.nil_append, Nat.sub_zero] at hcopy
  change (forIn arrays one (vcatCopyStep
    (⟨heap.length, target, [(contents.map List.length).sum],
      [(1, (contents.map List.length).sum)]⟩ : HeapArray Tag))).run
      (heap ++ [List.replicate (contents.map List.length).sum none]) = _ at hcopy
  exact (batchVcatRun layout l target hl heap arrays contents hc).trans
    ((congrArg (batchVcatOutcome arrays) ha).trans (batchVcatOutcomeSuccess arrays _ _ _ _ hcopy))



theorem batchVcatAssertNo (p c n : Nat) (hp : p ≤ n)
    (hn : n < 9223372036854775806) (hc : c < 9223372036854775808)
    (hbad : n < p + c) (hsmall : p + c < typemaxNat) :
    ¬ (JInt.wrap .i64 ((p : Int) + 1) + JInt.wrap .i64 (c : Int) ≤
      one + JInt.wrap .i64 (n : Int)) := by
  have hvp : (JInt.wrap .i64 ((p : Int) + 1)).val = p + 1 := ival_wrap _ (by omega)
  have hvc : (JInt.wrap .i64 (c : Int)).val = c := ival_wrap _ (by omega)
  have hvn : (JInt.wrap .i64 (n : Int)).val = n := ival_wrap _ (by omega)
  unfold typemaxNat at hsmall
  rw [jle_iff, ival_add _ _ (by rw [hvp, hvc]; omega), hvp, hvc,
    ival_add _ _ (by rw [ival_one, hvn]; omega), ival_one, hvn]
  omega

theorem batchVcatAssertYes (p c n : Nat) (hp : p ≤ n)
    (hn : n < 9223372036854775806) (hc : c < 9223372036854775808)
    (hlarge : ¬ p + c < typemaxNat) :
    JInt.wrap .i64 ((p : Int) + 1) + JInt.wrap .i64 (c : Int) ≤
      one + JInt.wrap .i64 (n : Int) := by
  have hvp : (JInt.wrap .i64 ((p : Int) + 1)).val = p + 1 := ival_wrap _ (by omega)
  have hvc : (JInt.wrap .i64 (c : Int)).val = c := ival_wrap _ (by omega)
  have hvn : (JInt.wrap .i64 (n : Int)).val = n := ival_wrap _ (by omega)
  have hw : wrapInt .i64 ((p : Int) + 1 + c) =
      (p : Int) + 1 + c - 18446744073709551616 := by
    unfold typemaxNat at hlarge
    simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true]
    omega
  rw [jle_iff, batchAddValue, hvp, hvc, hw,
    ival_add _ _ (by rw [ival_one, hvn]; omega), ival_one, hvn]
  omega

theorem batchVcatBadWindow (p c n : Nat) (hp : p ≤ n)
    (hn : n < 9223372036854775806) (hc : c < 9223372036854775808)
    (hbad : n < p + c) :
    ¬ (0 ≤ (JInt.wrap .i64 (c : Int)).val ∧
      1 ≤ (JInt.wrap .i64 ((p : Int) + 1)).val ∧
      (JInt.wrap .i64 ((p : Int) + 1)).val - 1 +
        (JInt.wrap .i64 (c : Int)).val ≤ (n : Int) ∧
      1 ≤ one.val ∧ one.val - 1 + (JInt.wrap .i64 (c : Int)).val ≤ c) := by
  rw [ival_wrap _ (by omega), ival_wrap _ (by omega), ival_one]
  omega

/-- The first copy crossing the allocated destination end either fails its assertion,
or (when that assertion's sum wraps) fails the memory window check. -/
theorem batchVcatCopyOverflow {Tag α : Type} (heap : VectorHeap α)
    (arr a : HeapArray Tag) (pre c : List (Option α)) (total : Nat)
    (harr : arr.handle = heap.length) (ha : heap[a.handle]? = some c)
    (hp : pre.length ≤ total) (ht : total < 9223372036854775806)
    (hc : c.length < 9223372036854775808) (hbad : total < pre.length + c.length) :
    (vcatCopyStep arr a (JInt.wrap .i64 ((pre.length : Int) + 1))).run
      (heap ++ [pre ++ List.replicate (total - pre.length) none]) =
        .error (if pre.length + c.length < typemaxNat
          then .assertion "Concurrent modification of arrays?" else .bounds) := by
  let h0 := heap ++ [pre ++ List.replicate (total - pre.length) none]
  change (vcatCopyStep arr a (JInt.wrap .i64 ((pre.length : Int) + 1))).run h0 = _
  have halt : a.handle < heap.length := (List.getElem?_eq_some_iff.mp ha).choose
  have hsrc : h0[a.handle]? = some c := by
    dsimp only [h0]
    rw [List.getElem?_append_left halt]
    exact ha
  have hdst : h0[arr.handle]? = some (pre ++ List.replicate (total - pre.length) none) := by
    dsimp only [h0]
    rw [harr]
    simp
  have hdlen : (pre ++ List.replicate (total - pre.length) (none : Option α)).length = total := by
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨hal, hav⟩ := batchHeapLengthOfSlots h0 a.handle c hsrc hc
  obtain ⟨harl, harv⟩ := batchHeapLengthOfSlots h0 arr.handle _ hdst (by rw [hdlen]; omega)
  rw [hdlen] at harl harv
  obtain ⟨start, hstart⟩ : ∃ start : I, start = JInt.wrap .i64 ((pre.length : Int) + 1) := ⟨_, rfl⟩
  obtain ⟨count, hcount⟩ : ∃ count : I, count = JInt.wrap .i64 (c.length : Int) := ⟨_, rfl⟩
  obtain ⟨limit, hlimit⟩ : ∃ limit : I, limit = JInt.wrap .i64 (total : Int) := ⟨_, rfl⟩
  rw [← hstart]
  rw [← hcount] at hal hav
  rw [← hlimit] at harl harv
  by_cases hover : pre.length + c.length < typemaxNat
  · have hno := batchVcatAssertNo pre.length c.length total hp ht hc hbad hover
    rw [← hstart, ← hcount, ← hlimit] at hno
    simp only [vcatCopyStep, vector_bind_run, hal, harl, hno, decide_false,
      Bool.not_false, ite_true, vector_throw_run, if_pos hover]
  · have hyes := batchVcatAssertYes pre.length c.length total hp ht hc hover
    rw [← hstart, ← hcount, ← hlimit] at hyes
    have hpos : count.val ≠ 0 := by rw [hav]; omega
    have hwindow := batchVcatBadWindow pre.length c.length total hp ht hc hbad
    rw [← hdlen, ← hstart, ← hcount] at hwindow
    have hcopy : (heapColonMemoryCopy arr start a one count).run h0 = .error .bounds := by
      simp only [heapColonMemoryCopy, unsafeCopyArray, hpos, decide_false,
        Bool.false_eq_true, ite_false, vector_bind_run, vector_pure_run,
        heapCopyReferences, heapSlots_run, hsrc, hdst, hwindow, Bool.not_false,
        ite_true, vector_throw_run]
    simp only [vcatCopyStep, vector_bind_run, hal, harl, hyes, decide_true,
      Bool.not_true, Bool.false_eq_true, ite_false, hcopy, if_neg hover]


theorem batchMappedSplit {α β γ : Type} (f : α → β) (g : γ → β)
    (xs : List α) (pre : List γ) (c : γ) (post : List γ)
    (h : xs.map f = (pre ++ c :: post).map g) :
    ∃ ys x zs, xs = ys ++ x :: zs ∧ ys.map f = pre.map g ∧
      f x = g c ∧ zs.map f = post.map g := by
  induction pre generalizing xs with
  | nil =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.nil_append, List.map_cons, List.cons.injEq] at h
      exact ⟨[], x, xs, rfl, rfl, h.1, h.2⟩
  | cons b bs ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      obtain ⟨ys, y, zs, heq, hys, hy, hzs⟩ := ih xs h.2
      refine ⟨x :: ys, y, zs, ?_, ?_, hy, hzs⟩
      · simp only [List.cons_append, heq]
      · simp only [List.map_cons, h.1, hys]

/-- A first capacity-crossing argument determines vcat's documented overflow error. -/
theorem batchVcatOverflow {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (l : MemoryLayout) (target : Tag) (hl : layout target = some l)
    (heap : VectorHeap α) (arrays : List (HeapArray Tag))
    (contents : List (List (Option α)))
    (hc : arrays.map (fun a => heap[a.handle]?) = contents.map some)
    (hb : ∀ c ∈ contents, c.length < 2 ^ 63)
    (halloc : arrayAllocError l [(JInt.wrap .i64 ((contents.map List.length).sum : Int)).val] = none)
    (pre : List (List (Option α))) (c : List (Option α)) (post : List (List (Option α)))
    (hcontents : contents = pre ++ c :: post)
    (hp : (pre.map List.length).sum ≤
      (JInt.wrap .i64 ((contents.map List.length).sum : Int)).val.toNat)
    (hbad : (JInt.wrap .i64 ((contents.map List.length).sum : Int)).val.toNat <
      (pre.map List.length).sum + c.length) :
    (heapVcat layout target arrays).run heap =
      .error (if (pre.map List.length).sum + c.length < typemaxNat
        then .assertion "Concurrent modification of arrays?" else .bounds) := by
  have hcb := hb c (by rw [hcontents]; simp)
  obtain ⟨apre, a, apost, has, hpre, ha, _⟩ :=
    batchMappedSplit (fun a : HeapArray Tag => heap[a.handle]?) some arrays pre c post
      (by rw [← hcontents]; exact hc)
  obtain ⟨n, hndef⟩ : ∃ n : Nat, n =
      (JInt.wrap .i64 ((contents.map List.length).sum : Int)).val.toNat := ⟨_, rfl⟩
  rw [← hndef] at hp hbad
  have hn : n < 9223372036854775806 := by
    have hbound := batchArraySizeBound l _ halloc
    rw [hndef]
    omega
  have hlen : pre.flatten.length = (pre.map List.length).sum := by
    simp only [List.length_flatten]
  have hallocation := batchAllocOutcomeSuccess l target
    [(JInt.wrap .i64 ((contents.map List.length).sum : Int)).val] heap halloc
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Nat.mul_one, ← hndef] at hallocation
  let arr : HeapArray Tag := ⟨heap.length, target, [n], [(1, n)]⟩
  have hprefix := batchVcatCopyPrefix heap arr rfl apre pre (a :: apost) hpre [] n
    (by simpa only [List.length_nil, Nat.zero_add] using hp) (by omega)
  simp only [List.length_nil, Int.natCast_zero, Int.zero_add, List.nil_append,
    Nat.sub_zero] at hprefix
  change (forIn (apre ++ a :: apost) one (vcatCopyStep arr)).run
    (heap ++ [List.replicate n none]) = _ at hprefix
  have hstep := batchVcatCopyOverflow heap arr a pre.flatten c n rfl ha
    (by rw [hlen]; exact hp) hn hcb (by rw [hlen]; exact hbad)
  rw [hlen] at hstep
  have hcopy : (forIn arrays one (vcatCopyStep arr)).run
      (heap ++ [List.replicate n none]) =
      .error (if (pre.map List.length).sum + c.length < typemaxNat
        then .assertion "Concurrent modification of arrays?" else .bounds) := by
    rw [has, hprefix]
    simp only [List.forIn_cons, vector_bind_run, hlen, hstep]
  exact (batchVcatRun layout l target hl heap arrays contents hc).trans
    ((congrArg (batchVcatOutcome arrays) hallocation).trans
      (batchVcatOutcomeCopyError arrays arr _ _ hcopy))

/-- Verified specification for same-element-type vector concatenation. -/
theorem MultidimcovArrayV2VcatSame_proven : VcatSpec := by
  intro Tag α layout l target heap arrays contents hl hc hb
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact batchVcatAllocationFailure layout l target hl heap arrays contents hc e he
  · intro halloc hn
    exact batchVcatSuccess layout l target hl heap arrays contents hc halloc hn
  · intro halloc pre c post hcontents hp hbad
    exact batchVcatOverflow layout l target hl heap arrays contents hc hb
      halloc pre c post hcontents hp hbad
end ChatGPTBatch1.ArrayExtra
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

/-- Runtime allocation summaries for Int and Any in the concrete hcat example. -/
def hcatAllocation : HcatDemoType → Option MemoryLayout
  | .int => some ⟨8, false, false⟩
  | .any => some ⟨8, true, false⟩

/-- Two Any vectors become an Int matrix through the value-directed comprehension. -/
theorem MultidimcovHcatVectorEltype_refuted :
    ¬ JuliaLean.Proofs.base.array.HcatEltypeSpec := by
  intro h
  obtain ⟨r, next, hr, ht⟩ := h HcatDemoType Int hcatAllocation hcatDemoLattice
    .any hcatDemoHeap hcatDemoVectors 1 (by decide) (by decide) (by
      intro v hv
      simp only [hcatDemoVectors, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨rfl, [1], rfl, rfl, by intro x hx; rfl⟩
      · exact ⟨rfl, [2], rfl, rfl, by intro x hx; rfl⟩)
  have bad := congrArg (fun result => result.toOption.map (fun p => p.1.elementType)) hr
  have computed : ((typedHcat hcatAllocation hcatDemoLattice HcatDemoType.any
      hcatDemoVectors).run hcatDemoHeap).toOption.map (fun p => p.1.elementType) =
      (some HcatDemoType.int : Option HcatDemoType) := by
    change (((typedCollectTo hcatAllocation hcatDemoLattice
        (⟨2, .int, [1, 2], [(1, 1), (1, 2)]⟩ : HeapArray HcatDemoType)
        (JInt.wrap .i64 2) [2]) >>= (fun result => pure result)).run
        [[some 1], [some 2], [some 1, none]]).toOption.map
      (fun p => p.1.elementType) = some HcatDemoType.int
    simp only [bind_pure]
    unfold typedCollectTo
    rw [collectTo]
    change ((typedCollectTo hcatAllocation hcatDemoLattice
        (⟨2, .int, [1, 2], [(1, 1), (1, 2)]⟩ : HeapArray HcatDemoType)
        (JInt.wrap .i64 3) []).run
        [[some 1], [some 2], [some 1, some 2]]).toOption.map
      (fun p => p.1.elementType) = some HcatDemoType.int
    unfold typedCollectTo
    rw [collectTo]
    rfl
  rw [computed] at bad
  change (some HcatDemoType.int : Option HcatDemoType) = some r.elementType at bad
  rw [ht] at bad
  cases bad
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesHcat1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-hcat-vector-eltype", juliaFile := "base/array.jl",
    juliaFns := ["hcat(V::Vector{T}...) where T"],
    statement := "`hcat(V::Vector{T}...)` (array.jl:2335; `hcat` docstring in abstractarray.jl: \"Concatenate arrays or numbers horizontally\") for one or more vectors of one element type (the call with no argument is `hcat()`, `multidimcov-array-v2-empty-concat`): when every vector has the length `h` of the first (including `h = 0`), the result is a fresh `h × n` `Matrix{T}` holding the vectors as its columns; when some vector's length differs from the first's, `DimensionMismatch(\"vectors must have same lengths\")` is raised.",
    source := "base/array.jl:2335", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #26004, #33919, #64568, #19387; see bugs/multidimcov-hcat-vector-eltype.yaml",
    prop := ``HcatEltypeSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovHcatVectorEltype_refuted,
    notes := "" }
]
def entriesHcat2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-vcat-same", juliaFile := "base/array.jl",
    juliaFns := ["vcat(arrays::Vector{T}...) where T"],
    statement := "vcat of Vector{T}s is a fresh Vector{T} of the total length holding their slots one after another, with every argument unchanged.",
    source := "base/array.jl:2346-2360",
    status := .proven, prop := ``VcatSpec, thm := some ``ChatGPTBatch1.ArrayExtra.MultidimcovArrayV2VcatSame_proven}
]
def entriesHcat3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-empty-concat", juliaFile := "base/array.jl",
    juliaFns := ["DimensionMismatch()", "vcat()", "hcat()"],
    statement := "DimensionMismatch() has an empty message; empty vcat and hcat allocate a zero-length Vector{Any} with no readable index.",
    source := "base/array.jl:14,2332-2333", status := .proven,
    prop := ``EmptyConcatSpec, thm := some ``emptyConcatSpec}
]
end JuliaLean.Proofs.base.array

