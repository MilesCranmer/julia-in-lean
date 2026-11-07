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

def FillContentsSpec : Prop :=
  ∀ (α β : Type) (n : Nat) (keys : List I),
    (∀ j, j ∈ keys ↔ 1 ≤ j.val ∧ j.val ≤ (n : Int)) →
    ∀ (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
      (v : β) (x : α) (old : I → Option α),
    let set := setindexScalar (fun _ : α => true) id
      (fun x => (pure x : SlotM α α))
      (setindexTyped (slotBounds n) slotRefNew slotStore)
    let typed := fillTyped (fun _ : Unit => (pure keys : SlotM α (List I))) set
    (typed () x).run old =
      (.ok (), fun j => if 1 ≤ j.val ∧ j.val ≤ (n : Int) then some x else old j) ∧
    (fillBang already asTyped (fun v => slotLift (convert v)) typed () v).run old =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, old)
      | .ok y =>
        (.ok (), fun j => if 1 ≤ j.val ∧ j.val ≤ (n : Int) then some y else old j)

theorem fillContentsSpec : FillContentsSpec := by
  intro α β n keys hkeys already asTyped convert v x old set typed
  have htyped : ∀ (y : α) (state : I → Option α), (typed () y).run state =
      (.ok (), fun j => if 1 ≤ j.val ∧ j.val ≤ (n : Int) then some y else state j) := by
    intro y state
    have hstep : ∀ old i, i ∈ keys →
        (set () y i).run old = (.ok (), updateSlot old i (some y)) := by
      intro old i hi
      have hb := (hkeys i).mp hi
      simp [set, setindexScalar, setindexTyped, slotBounds, slotRefNew, slotStore, hb,
        ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    have hloop := fill_loop keys (set () y) y hstep state
    simp only [hkeys] at hloop
    simp only [typed, fillTyped, stateExcept_bind, stateExcept_pure]
    rw [hloop]
  refine ⟨htyped x old, ?_⟩
  cases ha : already v with
  | true =>
    simpa only [fillBang, ha, ite_true, Bool.true_eq, stateExcept_bind, stateExcept_pure]
      using htyped (asTyped v) old
  | false =>
    cases hc : convert v with
    | error e =>
      simp [fillBang, ha, hc, slotLift, ExceptT.run, ExceptT.bind,
        ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure,
        Bind.bind, Pure.pure]
    | ok y =>
      have hlift : (slotLift (.ok y) : SlotM α α).run old = (.ok y, old) := rfl
      simpa only [fillBang, ha, Bool.false_eq_true, ite_false, hc,
        stateExcept_bind, hlift] using htyped y old

/-- The AbstractArray setter is an extensible interface from abstractarray.jl.
The concrete Array instance is additionally checked in FillContentsSpec. -/
def AbstractFillSpec : Prop :=
  ∀ (α β A K : Type) [DecidableEq K] (indices : A → List K)
    (set : A → α → K → ExceptT Error (StateM (K → Option α)) Unit),
    (∀ old a x i, i ∈ indices a →
      (set a x i).run old = (.ok (), fun j => if j = i then some x else old j)) →
    ∀ (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
      (a : A) (v : β) (x : α) (old : K → Option α),
    let typed := fillTyped (fun a => (pure (indices a) : ExceptT Error (StateM (K → Option α)) (List K))) set
    (typed a x).run old =
      (.ok a, fun j => if j ∈ indices a then some x else old j) ∧
    (fillBang already asTyped (fun v => stateExceptLift (convert v)) typed a v).run old =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, old)
      | .ok y => (.ok a, fun j => if j ∈ indices a then some y else old j)

theorem abstractFillSpec : AbstractFillSpec := by
  intro α β A K _ indices set hset already asTyped convert a v x old typed
  have htyped : ∀ (y : α) (state : K → Option α), (typed a y).run state =
      (.ok a, fun j => if j ∈ indices a then some y else state j) := by
    intro y state
    have hloop := fill_loop (indices a) (set a y) y (fun old i hi => hset old a y i hi) state
    simp only [typed, fillTyped, stateExcept_bind, stateExcept_pure]
    rw [hloop]
  refine ⟨htyped x old, ?_⟩
  cases ha : already v with
  | true =>
    simpa only [fillBang, ha, ite_true, Bool.true_eq, stateExcept_bind, stateExcept_pure]
      using htyped (asTyped v) old
  | false =>
    cases hc : convert v with
    | error e =>
      simp only [fillBang, ha, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc]
    | ok y =>
      simpa only [fillBang, ha, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc] using htyped y old

def CompleteFillSpec : Prop := FillContentsSpec ∧ AbstractFillSpec

def ByteFillSpec : Prop :=
  ∀ (Byte Z : Type) (memset : Nat → Byte → JInt .u64 → CopyM Byte Unit),
    (∀ old ptr x count, (memset ptr x count).run old =
      (.ok (), fun address => if ptr ≤ address ∧ address < ptr + count.val.toNat
        then some x else old address)) →
    ∀ (already : Z → Bool) (asTyped : Z → Byte) (convert : Z → Except Error Byte)
      (a : Nat × Nat) (v : Z) (old : Nat → Option Byte), a.2 < 2 ^ 63 →
    (fillBytes (fun a => pure a) (fun _ => pure ()) (fun ref => pure ref.1)
      already asTyped (fun v => stateExceptLift (convert v))
      (fun a => pure (JInt.wrap .i64 a.2)) memset (fun _ => pure ()) a v).run old =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, old)
      | .ok x =>
        (.ok a, fun address => if a.1 ≤ address ∧ address < a.1 + a.2
          then some x else old address)

abbrev constructorFiller {α : Type} (indices : List Nat → List I) :=
  arrayShapeFiller (α := α) id indices

theorem constructorFiller_run (indices : List Nat → List I)
    (hindices : ∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int))
    (dims : List Nat) (hdims : dims.prod < 2 ^ 63) (x : α) (old : I → Option α) :
    (constructorFiller indices dims x).run old = (.ok dims, filledShape old dims x) :=
  arrayShapeFiller_run id indices hindices dims hdims x old

/-- Successful runtime allocation preserves dimension values and valid storage size. -/
def AllocationShapeLaw (value : Z → Int)
    (allocate : List Z → SlotM α (List Nat)) : Prop :=
  ∀ old dims shape fresh, (allocate dims).run old = (.ok shape, fresh) →
    shape = dims.map (fun d => (value d).toNat) ∧ shape.prod < 2 ^ 63

def FillConstructorSpec : Prop :=
  ∀ (α Z : Type) (value : Z → Int) (allocate : List Z → SlotM α (List Nat)),
    AllocationShapeLaw value allocate →
    ∀ (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (v : α) (dims : List Z) (old : I → Option α),
    ∀ operation ∈ [fill585 allocate (constructorFiller indices),
      fill587 allocate (constructorFiller indices),
      fillVarargs (fill585 allocate (constructorFiller indices)),
      fill586 (similar421 (similar420 allocate ())) (constructorFiller indices)],
    (operation v dims).run old =
      match (allocate dims).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok _, fresh) =>
        let shape := dims.map (fun d => (value d).toNat)
        (.ok shape, filledShape fresh shape v)

theorem fillConstructorSpec : FillConstructorSpec := by
  intro α Z value allocate halloc indices hindices v dims old operation hop
  have hcore : (fill585 allocate (constructorFiller indices) v dims).run old =
      match (allocate dims).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok _, fresh) =>
        let shape := dims.map (fun d => (value d).toNat)
        (.ok shape, filledShape fresh shape v) := by
    cases ha : (allocate dims).run old with
    | mk result fresh =>
      cases result with
      | error e => simp only [fill585, stateExcept_bind, ha]
      | ok shape =>
        obtain ⟨hshape, hn⟩ := halloc old dims shape fresh ha
        simp only [fill585, stateExcept_bind, stateExcept_pure, ha]
        rw [constructorFiller_run indices hindices shape hn v fresh]
        simp only [hshape]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;> exact hcore

def MixedFillConstructorSpec : Prop :=
  ∀ (α Z : Type) (value : Z → Int) (allocate : List Z → SlotM α (List Nat)),
    AllocationShapeLaw value allocate →
    ∀ (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (v : α) (dims : List (Sum Z Z)) (old : I → Option α),
    ∀ operation ∈ [fillMixedDims dimensionArgument
      (fill585 allocate (constructorFiller indices)),
      fillVarargs (fillMixedDims dimensionArgument
        (fill585 allocate (constructorFiller indices)))],
    (operation v dims).run old =
      match (allocate (dims.map (fun d => d.elim id id))).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok _, fresh) =>
        let shape := dims.map (fun d => (value (d.elim id id)).toNat)
        (.ok shape, filledShape fresh shape v)

theorem mixedFillConstructorSpec : MixedFillConstructorSpec := by
  intro α Z value allocate halloc indices hindices v dims old operation hop
  have hmap : dims.map dimensionArgument = dims.map (fun d => d.elim id id) := by
    apply List.map_congr_left
    intro d _
    cases d <;> rfl
  have hc := fillConstructorSpec α Z value allocate halloc indices hindices v
    (dims.map (fun d => d.elim id id)) old
    (fill585 allocate (constructorFiller indices)) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl <;>
    simpa only [fillMixedDims, fillVarargs, hmap, List.map_map, Function.comp_def] using hc

def CheckedAllocationLaw (value : Z → Int)
    (allocate : List Z → SlotM α (List Nat)) : Prop :=
  AllocationShapeLaw value allocate ∧
  (∀ old dims, validAllocationDimensions value dims →
    ∃ fresh, (allocate dims).run old = (.ok (dims.map (fun d => (value d).toNat)), fresh)) ∧
  (∀ old dims, (∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, value d < 0) →
    ∃ message, (allocate dims).run old = (.error (.argument message), old)) ∧
  (∀ old dims, (∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
    (allocate dims).run old = (.error .inexact, old))

def DocumentedFillDimensionsSpec : Prop :=
  ∀ (α Z : Type) (value : Z → Int) (allocate : List Z → SlotM α (List Nat)),
    CheckedAllocationLaw value allocate →
    ∀ (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (v : α) (dims : List Z) (old : I → Option α),
    let operations := [fill585 allocate (constructorFiller indices),
      fill587 allocate (constructorFiller indices),
      fillVarargs (fill585 allocate (constructorFiller indices)),
      fill586 (similar421 (similar420 allocate ())) (constructorFiller indices)]
    (validAllocationDimensions value dims →
      ∃ fresh, ∀ operation ∈ operations,
        (operation v dims).run old =
          (.ok (dims.map (fun d => (value d).toNat)),
            filledShape fresh (dims.map (fun d => (value d).toNat)) v)) ∧
    ((∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
      (∃ d ∈ dims, value d < 0) →
      ∃ message, ∀ operation ∈ operations,
        (operation v dims).run old = (.error (.argument message), old)) ∧
    ((∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
      ∀ operation ∈ operations, (operation v dims).run old = (.error .inexact, old))

theorem documentedFillDimensionsSpec : DocumentedFillDimensionsSpec := by
  intro α Z value allocate halloc indices hindices v dims old operations
  have hc := fillConstructorSpec α Z value allocate halloc.1 indices hindices v dims old
  refine ⟨?_, ?_, ?_⟩
  · intro hvalid
    obtain ⟨fresh, ha⟩ := halloc.2.1 old dims hvalid
    refine ⟨fresh, ?_⟩
    intro operation hop
    have h := hc operation hop
    simpa only [ha] using h
  · intro hrepresentable hnegative
    obtain ⟨message, ha⟩ := halloc.2.2.1 old dims hrepresentable hnegative
    refine ⟨message, ?_⟩
    intro operation hop
    have h := hc operation hop
    simpa only [ha] using h
  · intro hout operation hop
    have ha := halloc.2.2.2 old dims hout
    have h := hc operation hop
    simpa only [ha] using h

def UnsupportedFillAxesSpec : Prop :=
  ∀ (α Z : Type)
    (similarAxes : List (ConstructorAxis Z) → SlotM α (List Nat)),
    (∀ old dims, (∃ d ∈ dims, unsupportedAxis d) →
      (similarAxes dims).run old = (.error (.method "similar"), old)) →
    ∀ (indices : List Nat → List I) (v : α) (dims : List (ConstructorAxis Z))
      (old : I → Option α), (∃ d ∈ dims, unsupportedAxis d) →
    (fill586 similarAxes (constructorFiller indices) v dims).run old =
      (.error (.method "similar"), old) ∧
    (fillVarargs (fill586 similarAxes (constructorFiller indices)) v dims).run old =
      (.error (.method "similar"), old)

theorem unsupportedFillAxesSpec : UnsupportedFillAxesSpec := by
  intro α Z similarAxes hsimilar indices v dims old haxis
  have hs := hsimilar old dims haxis
  simp only [fill586, fillVarargs, stateExcept_bind, hs, and_self]

def CompleteFillDimensionsSpec : Prop :=
  DocumentedFillDimensionsSpec ∧ MixedFillConstructorSpec ∧ UnsupportedFillAxesSpec

theorem intDimensionsFit (dims : List I) :
    heapDimensionsFit (dims.map (fun dim => dim.val.toNat)) = true := by
  apply List.all_eq_true.mpr
  intro n hn
  obtain ⟨dim, hd, rfl⟩ := List.mem_map.mp hn
  simp only [decide_eq_true_eq]
  have hu := dim.property.2
  change dim.val ≤ 9223372036854775807 at hu
  change dim.val.toNat < 9223372036854775808
  omega

theorem heapNatDimension_toNat (dims : List Nat) (hfit : heapDimensionsFit dims = true)
    (n : Nat) (hn : n ∈ dims) : (JInt.wrap .i64 (n : Int)).val.toNat = n :=
  (congrArg Int.toNat (heapNatDimension_value dims hfit n hn)).trans (Int.toNat_natCast n)

theorem heapNatDimensions_values (dims : List Nat) (hfit : heapDimensionsFit dims = true) :
    (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))).map
      (fun n => n.val.toNat) = dims := by
  revert hfit
  induction dims with
  | nil => intro _; rfl
  | cons n ns ih =>
    intro hfit
    have htail : heapDimensionsFit ns = true := by
      apply List.all_eq_true.mpr
      intro value hvalue
      exact List.all_eq_true.mp hfit value (List.mem_cons_of_mem n hvalue)
    exact List.cons_eq_cons.mpr
      ⟨heapNatDimension_toNat (n :: ns) hfit n (by simp), ih htail⟩

theorem heapNatDimensions_nonnegative (dims : List Nat)
    (hfit : heapDimensionsFit dims = true) :
    (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))).any
      (fun n => decide (n.val < 0)) = false := by
  apply List.any_eq_false.mpr
  intro n hn
  obtain ⟨value, hv, rfl⟩ := List.mem_map.mp hn
  have hnonnegative : 0 ≤ (JInt.wrap .i64 (value : Int)).val :=
    Int.le_trans (Int.natCast_nonneg value)
      (Int.le_of_eq (heapNatDimension_value dims hfit value hv).symm)
  simpa only [decide_eq_true_eq] using Int.not_lt.mpr hnonnegative
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

def dimensionArgument (d : Sum Z Z) : Z :=
  match d with
  | .inl integer => toDimInteger integer
  | .inr endpoint => toDimOneTo id endpoint

def validAllocationDimensions (value : Z → Int) (dims : List Z) : Prop :=
  (∀ d ∈ dims, 0 ≤ value d ∧ value d ≤ IntTy.i64.max) ∧
    (dims.map value).prod ≤ IntTy.i64.max

private def bytePrefixCompare : List (JInt .u8) → List (JInt .u8) → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x.val < y.val then -1 else if y.val < x.val then 1 else bytePrefixCompare xs ys

def ByteFillSpec : Prop :=
  ∀ (ops : BigIntegerOps), ops.Lawful →
  ∀ (e : IntTy) (address len : Nat) (x : IntegerValue) (heap : JuliaLean.base.pointer.ByteHeap),
    e = .u8 ∨ e = .i8 → len < 2 ^ 63 →
    JuliaLean.base.cmem.validRange heap (bytePtr address) (JInt.wrap .u64 len) →
    let run := (fillBytes (fun a : Nat × Nat => pure a) (fun _ => pure ())
      (fun ref => pure (bytePtr ref.1)) (IntegerValue.isBit e)
      (fun x : IntegerValue => JInt.wrap e x.val)
      (fun x : IntegerValue => StateT.lift (x.convertTo ops e))
      (fun a => pure (JInt.wrap .i64 a.2))
      (fun p v count => do
        let _ ← byteCall (fun heap => JuliaLean.base.cmem.memset cLibrary
          (fun v : JInt e => JuliaLean.base.cmem.cintFromInt v.val) (fun c : JInt .u64 => .ok c)
          heap p v count)
        pure ())
      (fun _ => pure ()) (address, len) x).run heap
    (¬ (e.min ≤ x.val ∧ x.val ≤ e.max) → run = .error .inexact) ∧
    (e.min ≤ x.val → x.val ≤ e.max →
      ∃ after, run = .ok ((address, len), after) ∧
        JuliaLean.base.cmem.fillEffect heap after (bytePtr address) (JInt.wrap .u64 len)
          (JInt.wrap .u8 x.val))

def heapStoreRef {α : Type} (ref : Nat × I) (x : α) : VectorM α Unit :=
  modify fun heap => heap.set ref.1 ((heap[ref.1]?.getD []).set (ref.2.val - 1).toNat (some x))

/-- `_setindex!(A::Array{T}, x::T, i::Int)` (array.jl:1036, `setindexTyped`) for an Array of any
shape on the shared heap: `checkbounds`, `memoryrefnew(A.ref, i, false)` and `memoryrefset!`. -/
def heapSetTyped {Tag α : Type} (a : HeapArray Tag) (x : α) (i : I) : VectorM α Unit := do
  let _ ← setindexTyped (m := VectorM α) (fun a i => heapBounds (α := α) a.handle i)
    (fun (a : HeapArray Tag) i _ => heapReference (α := α) a.handle i)
    (fun ref value _ => heapStoreRef ref value) a x i
  pure ()

/-- `fill!(A::AbstractArray{T}, x)` and `_fill!(A, x)` (array.jl:368, 373; docstring at
array.jl:335-366: "Fill array `A` with the value `x`. If `x` is an object reference, all elements
will refer to the same object.") for every `AbstractArray`: for Arrays of every shape on the shared
heap with `eachindex(A) = 1:length(A)` and array.jl's `_setindex!`, and for any mutable array type
with lawful `eachindex`/`setindex!` (`MutableArrayInterface`). A value already of type `T` is
stored, otherwise `convert(T, x)` (user-extensible, a parameter with no law) decides: its error
propagates with the array unchanged; otherwise every element of `A` becomes the value and `A` is
returned (the heap: every slot of its memory, every other heap object unchanged). -/
def FillSpec : Prop :=
  (∀ (Tag α β : Type) (alreadyTyped : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (heap : VectorHeap α) (a : HeapArray Tag)
    (xs : List (Option α)) (v : β),
    heap[a.handle]? = some xs → xs.length < 2 ^ 63 →
    let run := (fillBang alreadyTyped asTyped (fun v => StateT.lift (convert v))
      (fillTyped (fun a => do return intRange one (← heapArrayLength a))
        (fun a x i => heapSetTyped a x i)) a v).run heap
    let value := if alreadyTyped v then .ok (asTyped v) else convert v
    (∀ e, value = .error e → run = .error e) ∧
    (∀ y, value = .ok y → run = .ok (a, heap.set a.handle (List.replicate xs.length (some y))))) ∧
  (∀ (σ K α β : Type) (A : MutableArrayInterface σ K α), A.Lawful →
    ∀ (alreadyTyped : β → Bool) (asTyped : β → α) (convert : β → Except Error α) (s : σ) (v : β),
    let run := (fillBang (m := StateT σ (Except Error)) alreadyTyped asTyped
      (fun v => StateT.lift (convert v))
      (fillTyped (fun _ => do return A.eachindex (← get))
        (fun _ x i => do set (← StateT.lift (A.set (← get) x i)))) () v).run s
    let value := if alreadyTyped v then .ok (asTyped v) else convert v
    (∀ e, value = .error e → run = .error e) ∧
    (∀ y, value = .ok y → ∃ s', run = .ok ((), s') ∧ A.eachindex s' = A.eachindex s ∧
      ∀ i ∈ A.eachindex s, A.get s' i = some y))

def heapFillAll {Tag α β : Type} (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (a : HeapArray Tag) (v : β) : VectorM α (HeapArray Tag) :=
  fillBang already asTyped (fun v => liftM (convert v))
    (fillTyped (fun a : HeapArray Tag => pure (intRange one (JInt.wrap .i64 (a.dimensions.prod : Int))))
      (fun a x i => heapSet a.handle x i)) a v

/-- `Array{T,N}(undef, dims)` for dimensions of every `Integer` type (int.jl's or the integer
type's `Int(d)`, `InexactError`; `Int(true) = 1`), then the Core allocator checks them. -/
def heapAllocateValues {Tag α : Type} (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (target : Tag)
    (dims : List IntegerValue) : VectorM α (HeapArray Tag) := do
  let ints ← dims.mapM (fun d => match d.toInt ops with
    | .ok k => pure k
    | .error e => throw e)
  heapAllocateIntDims layout target ints

/-- The documented outcome of allocating an array of dimensions `dims` (any `Integer` types) and
filling it with `value`: `InexactError` for a dimension with no equal `Int`, then the allocation
error of `arrayAllocError`, otherwise the fresh filled array (or the value's error). -/
def filledOutcome {Tag α : Type} (l : MemoryLayout) (target : Tag) (dims : List IntegerValue)
    (value : Except Error α) (heap : VectorHeap α) : Except Error (HeapArray Tag × VectorHeap α) :=
  if dims.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max)) then .error .inexact
  else match arrayAllocError l (dims.map (fun d => d.val)) with
    | some e => .error e
    | none => value.map (fun x =>
      let shape := dims.map (fun d => d.val.toNat)
      freshHeapArray target shape (List.replicate shape.prod (some x)) heap)

/-- `zeros`/`ones` (array.jl:611-651, the `$fname` methods; docstrings at array.jl:590-628:
"Create an `Array`, with element type `T`, of all zeros with size specified by `dims`") on the
heap, with `$felt(T)` (`zero(T)`/`one(T)`, number.jl, user-extensible: any value or error) and
`fill!`'s conversion: `zeros(T, dims::Integer...)` for dimensions of every `Integer` type (mixed
types, `Bool` and `BigInt` included), `zeros(dims...)` with the default `Float64`, `zeros(T, ())`
(zero dimensions, one element) and `zeros(T, dims)` with `Integer`/`OneTo` dimensions (`to_dim`)
each give `filledOutcome`. -/
def ConstantArraySpec : Prop :=
  ∀ (Tag α β : Type) (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (target float64 : Tag)
    (lt lf : MemoryLayout) (element : Tag → Except Error β)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
    (heap : VectorHeap α) (dims : List IntegerValue) (mixed : List (Sum IntegerValue IntegerValue)),
    ops.Lawful → layout target = some lt → layout float64 = some lf →
    let value := fun T => (element T).bind (fun v => if already v then .ok (asTyped v) else convert v)
    let constant := fun (T : Tag) (dims : List IntegerValue) =>
      constant637 (heapAllocateValues layout ops T) (liftM (element T))
        (heapFillAll already asTyped convert) dims
    (constantTypedVarargs constant target dims).run heap =
      filledOutcome lt target dims (value target) heap ∧
    (constantVarargs (constantDefaultType float64 constant) dims).run heap =
      filledOutcome lf float64 dims (value float64) heap ∧
    (constant642 (heapAllocateValues layout ops target) (liftM (element target))
      (heapFillAll already asTyped convert) []).run heap =
      filledOutcome lt target ([] : List IntegerValue) (value target) heap ∧
    (constantMixedDims dimensionArgument constant target mixed).run heap =
      filledOutcome lt target (mixed.map dimensionArgument) (value target) heap

def FillDimensionsSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (typeOf : α → Tag)
    (v : α) (l : MemoryLayout) (heap : VectorHeap α)
    (dims : List IntegerValue) (mixed : List (Sum IntegerValue IntegerValue)),
    ops.Lawful → layout (typeOf v) = some l →
    let fill := fun (allocate : List IntegerValue → VectorM α (HeapArray Tag))
        (dims : List IntegerValue) =>
      fill585 allocate (heapFillAll (fun _ => true) id (fun x => .ok x)) v dims
    (fillVarargs (fun v dims => fill585 (heapAllocateValues layout ops (typeOf v))
      (heapFillAll (fun _ => true) id (fun x => .ok x)) v dims) v dims).run heap =
      filledOutcome l (typeOf v) dims (.ok v) heap ∧
    (fill (heapAllocateValues layout ops (typeOf v)) dims).run heap =
      filledOutcome l (typeOf v) dims (.ok v) heap ∧
    (fillMixedDims dimensionArgument (fun v dims => fill586 (heapAllocateValues layout ops (typeOf v))
      (heapFillAll (fun _ => true) id (fun x => .ok x)) v dims) v mixed).run heap =
      filledOutcome l (typeOf v) (mixed.map dimensionArgument) (.ok v) heap ∧
    (fill587 (heapAllocateValues layout ops (typeOf v)) (heapFillAll (fun _ => true) id (fun x => .ok x))
      v []).run heap = filledOutcome l (typeOf v) ([] : List IntegerValue) (.ok v) heap
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6b
open JuliaLean JuliaLean.base.array

def ByteFillSpec : Prop :=
  ∀ (ops : OpaqueIntegerOps), ops.ConversionLaw →
  ∀ (t : IntTy) (address len : Nat) (x : IntegerArgument)
    (heap : JuliaLean.base.pointer.ByteHeap),
    t = .u8 ∨ t = .i8 → len < 2 ^ 63 →
    JuliaLean.base.cmem.validRange heap (bytePointer address) (JInt.wrap .u64 len) →
    let run := (fillBytes (fun a : Nat × Nat => pure a) (fun _ => pure ())
      (fun ref => pure (bytePointer ref.1))
      (fun x => match x with | .bit s _ => decide (s = t) | _ => false)
      (fun x => JInt.wrap t x.value)
      (fun x => StateT.lift (convertInteger ops t x))
      (fun a => pure (JInt.wrap .i64 a.2))
      (fun p value count => do
        let _ ← byteCall (fun heap => JuliaLean.base.cmem.memset
          JuliaLean.base.cmem.StandardC.standardCMemoryOps
          (fun value : JInt t => JuliaLean.base.cmem.cintFromInt value.val)
          (fun count : JInt .u64 => .ok (JuliaLean.base.int.remT .u64 count))
          heap p value count)
        pure ())
      (fun _ => pure ()) (address, len) x).run heap
    (¬ (t.min ≤ x.value ∧ x.value ≤ t.max) → run = .error .inexact) ∧
    (t.min ≤ x.value → x.value ≤ t.max →
      ∃ after, run = .ok ((address, len), after) ∧
        JuliaLean.base.cmem.fillEffect heap after (bytePointer address)
          (JInt.wrap .u64 len) (JInt.wrap .u8 x.value))

private theorem convertInteger_range (ops : OpaqueIntegerOps) (law : ops.ConversionLaw)
    (t : IntTy) (x : IntegerArgument) :
    convertInteger ops t x =
      if t.min ≤ x.value ∧ x.value ≤ t.max then .ok (JInt.wrap t x.value) else .error .inexact := by
  cases x with
  | bit s v =>
      by_cases h : t.min ≤ v.val ∧ v.val ≤ t.max
      · have hwrap : JInt.wrap t v.val = (⟨v.val, h⟩ : JInt t) := by
          apply Subtype.ext
          exact wrapInt_of_inRange t v.val h
        simp [convertInteger, IntegerArgument.value, JuliaLean.base.int.convert,
          JInt.convert, Except.mapError, h, hwrap]
      · simp [convertInteger, IntegerArgument.value, JuliaLean.base.int.convert,
          JInt.convert, Except.mapError, h]
  | boolean b =>
      have h : t.min ≤ (if b then 1 else 0) ∧ (if b then 1 else 0) ≤ t.max := by
        cases t <;> cases b <;> decide
      simp [convertInteger, IntegerArgument.value, JuliaLean.base.int.ofBool,
        JuliaLean.base.int.lit, h]
  | «opaque» value =>
      by_cases h : t.min ≤ value ∧ value ≤ t.max
      · simp [convertInteger, IntegerArgument.value, law t value, h]
      · simp [convertInteger, IntegerArgument.value, law t value, h]
private theorem byteCountLen (len : Nat) (hlen : len < 2 ^ 63) :
    JInt.rem .u64 (JInt.wrap .i64 (len : Int)) = JInt.wrap .u64 (len : Int) := by
  have hfits : IntTy.i64.min ≤ (len : Int) ∧ (len : Int) ≤ IntTy.i64.max := by
    constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  have hval := wrapInt_of_inRange .i64 (len : Int) hfits
  apply Subtype.ext
  change wrapInt .u64 (wrapInt .i64 (len : Int)) = wrapInt .u64 (len : Int)
  rw [hval]

private theorem byteMemsetRun (t : IntTy) (address len : Nat) (value : Int)
    (heap : JuliaLean.base.pointer.ByteHeap) (htypes : t = .u8 ∨ t = .i8)
    (hlen : len < 2 ^ 63) (hvalue : t.min ≤ value ∧ value ≤ t.max)
    (hvalid : JuliaLean.base.cmem.validRange heap (bytePointer address)
      (JInt.wrap .u64 len)) :
    ∃ after result,
      JuliaLean.base.cmem.memset
        JuliaLean.base.cmem.StandardC.standardCMemoryOps
        (fun value : JInt t => JuliaLean.base.cmem.cintFromInt value.val)
        (fun count : JInt .u64 => .ok (JuliaLean.base.int.remT .u64 count))
        heap (bytePointer address) (JInt.wrap t value) (JInt.wrap .u64 len) =
          .ok (after, result) ∧
      JuliaLean.base.cmem.fillEffect heap after (bytePointer address)
        (JInt.wrap .u64 len) (JInt.wrap .u8 value) := by
  have hcin : -(2 ^ 31 : Int) ≤ value ∧ value < 2 ^ 31 := by
    rcases htypes with ht | ht
    · subst t
      have hv : 0 ≤ value ∧ value ≤ 255 := by
        simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using hvalue
      omega
    · subst t
      have hv : -128 ≤ value ∧ value ≤ 127 := by
        simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using hvalue
      omega
  have h32 : IntTy.i32.min ≤ value ∧ value ≤ IntTy.i32.max := by
    constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  have hvalueVal : (JInt.wrap t value).val = value :=
    wrapInt_of_inRange t value hvalue
  have hconvert : (fun value : JInt t => JuliaLean.base.cmem.cintFromInt value.val)
      (JInt.wrap t value) = .ok (JInt.wrap .i32 value) := by
    change JuliaLean.base.cmem.cintFromInt (JInt.wrap t value).val =
      .ok (JInt.wrap .i32 value)
    rw [hvalueVal]
    unfold JuliaLean.base.cmem.cintFromInt
    rw [if_pos hcin]
  have hcount :
      (fun count : JInt .u64 =>
        (Except.ok (JuliaLean.base.int.remT .u64 count) :
          JuliaLean.Jl JuliaLean.base.cmem.CSizeT))
        (JInt.wrap .u64 len) = Except.ok (JInt.wrap .u64 len) := by
    simp [JuliaLean.base.int.remT, JuliaLean.base.int.rem_same]
  obtain ⟨after, result, hmemset, _, hfill⟩ :=
    JuliaLean.Proofs.base.cmem.memsetByteValue_proven
      (fun value : JInt t => JuliaLean.base.cmem.cintFromInt value.val)
      (fun count : JInt .u64 => .ok (JuliaLean.base.int.remT .u64 count))
      heap (bytePointer address) (JInt.wrap t value) (JInt.wrap .u64 len)
      (JInt.wrap .i32 value) (JInt.wrap .u64 len) hconvert hcount
      (by
        simpa [JuliaLean.Proofs.base.cmem.cvoidPointer,
          JuliaLean.base.pointer.convertPtrType] using hvalid)
  have hfill' : JuliaLean.base.cmem.fillEffect heap after (bytePointer address)
      (JInt.wrap .u64 len) (JInt.wrap .u8 value) := by
    have h32val : (JInt.wrap .i32 value).val = value :=
      wrapInt_of_inRange .i32 value h32
    rw [h32val] at hfill
    simpa [JuliaLean.Proofs.base.cmem.cvoidPointer,
      JuliaLean.base.pointer.convertPtrType] using hfill
  exact ⟨after, result, hmemset, hfill'⟩

theorem byteFillSpec : ByteFillSpec := by
  intro ops law t address len x heap htypes hlen hvalid
  have hcountLen := byteCountLen len hlen
  refine ⟨?_, ?_⟩
  · intro hbad
    cases x with
    | bit s v =>
        by_cases hs : s = t
        · have hvalue : t.min ≤ v.val ∧ v.val ≤ t.max := by
            simpa [hs] using v.property
          exact (hbad (by simpa [IntegerArgument.value] using hvalue)).elim
        · have hbad' : ¬ (t.min ≤ v.val ∧ v.val ≤ t.max) := by
            simpa [IntegerArgument.value] using hbad
          have hconvert : convertInteger ops t (.bit s v) = .error .inexact := by
            have h := convertInteger_range ops law t (.bit s v)
            simpa [IntegerArgument.value, hbad'] using h
          simp [fillBytes, hs, hconvert, byteCall, hcountLen,
            StateT.run, StateT.bind, StateT.lift, StateT.pure, Bind.bind, Pure.pure,
            Except.bind, Except.pure]
    | boolean b =>
        have hvalue : t.min ≤ (if b then 1 else 0) ∧
            (if b then 1 else 0) ≤ t.max := by
          rcases htypes with ht | ht
          · subst t
            cases b <;> decide
          · subst t
            cases b <;> decide
        exact (hbad (by simpa [IntegerArgument.value] using hvalue)).elim
    | «opaque» value =>
        have hbad' : ¬ (t.min ≤ value ∧ value ≤ t.max) := by
          simpa [IntegerArgument.value] using hbad
        have hconvert : convertInteger ops t (.opaque value) = .error .inexact := by
          have h := convertInteger_range ops law t (.opaque value)
          simpa [IntegerArgument.value, hbad'] using h
        simp [fillBytes, hconvert, byteCall, hcountLen,
          StateT.run, StateT.bind, StateT.lift, StateT.pure, Bind.bind, Pure.pure,
          Except.bind, Except.pure]
  · intro hlo hhi
    have hvalue : t.min ≤ x.value ∧ x.value ≤ t.max := ⟨hlo, hhi⟩
    cases x with
    | bit s v =>
        by_cases hs : s = t
        · subst t
          obtain ⟨after, result, hmemset, hfill⟩ :=
            byteMemsetRun s address len v.val heap htypes hlen v.property hvalid
          refine ⟨after, ?_, hfill⟩
          simp [fillBytes, IntegerArgument.value, byteCall, hcountLen, hmemset,
          StateT.run, StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.set,
          MonadState.get, MonadStateOf.get, MonadState.set, MonadStateOf.set, getThe,
          Bind.bind, Pure.pure, Except.bind, Except.pure]
        · have hv : t.min ≤ v.val ∧ v.val ≤ t.max := by
            simpa [IntegerArgument.value] using hvalue
          have hc : convertInteger ops t (.bit s v) = .ok (JInt.wrap t v.val) := by
            have h := convertInteger_range ops law t (.bit s v)
            simpa [IntegerArgument.value, hv] using h
          obtain ⟨after, result, hmemset, hfill⟩ :=
            byteMemsetRun t address len v.val heap htypes hlen hv hvalid
          refine ⟨after, ?_, hfill⟩
          simp [fillBytes, IntegerArgument.value, hs, hc, byteCall, hcountLen, hmemset,
            StateT.run, StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.set,
            MonadState.get, MonadStateOf.get, MonadState.set, MonadStateOf.set, getThe,
            Bind.bind, Pure.pure, Except.bind, Except.pure]
    | boolean b =>
        have hv : t.min ≤ (if b then 1 else 0) ∧
            (if b then 1 else 0) ≤ t.max := by
          rcases htypes with ht | ht
          · subst t
            cases b <;> decide
          · subst t
            cases b <;> decide
        have hc : convertInteger ops t (.boolean b) =
            .ok (JInt.wrap t (if b then 1 else 0)) := by
          have h := convertInteger_range ops law t (.boolean b)
          simpa [IntegerArgument.value, hv] using h
        obtain ⟨after, result, hmemset, hfill⟩ :=
          byteMemsetRun t address len (if b then 1 else 0) heap htypes hlen hv hvalid
        refine ⟨after, ?_, hfill⟩
        simp [fillBytes, IntegerArgument.value, hc, byteCall, hcountLen, hmemset,
          StateT.run, StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.set,
          MonadState.get, MonadStateOf.get, MonadState.set, MonadStateOf.set, getThe,
          Bind.bind, Pure.pure, Except.bind, Except.pure]
    | «opaque» value =>
        have hv : t.min ≤ value ∧ value ≤ t.max := by
          simpa [IntegerArgument.value] using hvalue
        have hc : convertInteger ops t (.opaque value) =
            .ok (JInt.wrap t value) := by
          have h := convertInteger_range ops law t (.opaque value)
          simpa [IntegerArgument.value, hv] using h
        obtain ⟨after, result, hmemset, hfill⟩ :=
          byteMemsetRun t address len value heap htypes hlen hv hvalid
        refine ⟨after, ?_, hfill⟩
        simp [fillBytes, IntegerArgument.value, hc, byteCall, hcountLen, hmemset,
          StateT.run, StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.set,
          MonadState.get, MonadStateOf.get, MonadState.set, MonadStateOf.set, getThe,
          Bind.bind, Pure.pure, Except.bind, Except.pure]
end round6b
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
section
variable {α : Type}

/-- The stores of a `for j in js; A[j] = x; end` loop on one heap array. -/
theorem heapSetLoop_run (h : Nat) (x : α) : ∀ (js : List I) (heap : VectorHeap α)
    (slots : List (Option α)), heap[h]? = some slots →
    (∀ j ∈ js, 1 ≤ j.val ∧ j.val ≤ (slots.length : Int)) →
    (forIn js PUnit.unit (fun j _ => do
        heapSet h x j
        pure (ForInStep.yield PUnit.unit)) : VectorM α PUnit).run heap =
      .ok ((), heap.set h (js.foldl (fun sl j => sl.set (j.val - 1).toNat (some x)) slots)) := by
  intro js
  induction js with
  | nil =>
    intro heap slots hs _
    have hlt := (List.getElem?_eq_some_iff.mp hs).choose
    have hself : heap.set h slots = heap := by
      rw [← (List.getElem?_eq_some_iff.mp hs).choose_spec]
      exact List.set_getElem_self hlt
    simp only [List.forIn_nil, List.foldl_nil, hself]
    rfl
  | cons j rest ih =>
    intro heap slots hs hjs
    have hj := hjs j (List.mem_cons_self ..)
    have hlt := (List.getElem?_eq_some_iff.mp hs).choose
    have hset := heapSet_run heap h slots hs j hj.1 hj.2 x
    simp only [List.forIn_cons, vector_bind_run, hset, vector_pure_run]
    have hs' : (heap.set h (slots.set (j.val - 1).toNat (some x)))[h]? =
        some (slots.set (j.val - 1).toNat (some x)) := List.getElem?_set_self hlt
    have hrest : ∀ j ∈ rest, 1 ≤ j.val ∧ j.val ≤ ((slots.set (j.val - 1).toNat (some x)).length : Int) := by
      intro j' hj'
      rw [List.length_set]
      exact hjs j' (List.mem_cons_of_mem _ hj')
    rw [ih _ _ hs' (by intro j' hj'; rw [List.length_set]; exact hjs j' (List.mem_cons_of_mem _ hj'))]
    simp only [List.set_set, List.foldl_cons]

theorem foldl_set_range (x : β) (slots : List β) : ∀ n, n ≤ slots.length →
    ((List.range n).foldl (fun sl (k : Nat) => sl.set k x) slots) =
      List.replicate n x ++ slots.drop n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.set_append_right _ _ (by simp)]
    simp only [List.length_replicate, Nat.sub_self]
    obtain ⟨y, rest, hdr⟩ : ∃ y rest, slots.drop n = y :: rest := by
      cases h : slots.drop n with
      | nil => have := List.length_drop (l := slots) (i := n); rw [h] at this; simp at this; omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    rw [hdr, List.set_cons_zero, List.replicate_succ', List.append_assoc, List.singleton_append]
    congr 2
    rw [← List.drop_drop, hdr]
    rfl

theorem foldl_congr_mem {β γ : Type} {f g : β → γ → β} : ∀ (l : List γ) (b : β),
    (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f b = l.foldl g b := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons y l ih =>
    intro b h
    simp only [List.foldl_cons]
    rw [h y (List.mem_cons_self ..) b]
    exact ih _ (fun x hx b => h x (List.mem_cons_of_mem _ hx) b)

/-- The stores of `fill!` over indices `1:W` on a heap array of `W` slots. -/
theorem setRange_run (h : Nat) (x : α) (W : I) (heap : VectorHeap α) (slots : List (Option α))
    (hs : heap[h]? = some slots) (hW : W.val = (slots.length : Int)) :
    (forIn (intRange one W) PUnit.unit (fun j _ => do
        heapSet h x j
        pure (ForInStep.yield PUnit.unit)) : VectorM α PUnit).run heap =
      .ok ((), heap.set h (List.replicate slots.length (some x))) := by
  have hone : (one : I).val = 1 := rfl
  have hmem : ∀ j ∈ intRange one W, 1 ≤ j.val ∧ j.val ≤ (slots.length : Int) := by
    intro j hj
    have := intRange_mem _ _ j hj
    rw [hone, hW] at this
    exact this
  rw [heapSetLoop_run h x _ heap slots hs hmem]
  have hb := ival_bounds W
  have hfold : (intRange one W).foldl (fun sl j => sl.set (j.val - 1).toNat (some x)) slots =
      (List.range slots.length).foldl (fun sl (k : Nat) => sl.set k (some x)) slots := by
    simp only [intRange, List.foldl_map, hone, hW]
    rw [show ((slots.length : Int) - 1 + 1).toNat = slots.length by omega]
    apply foldl_congr_mem
    intro k hk sl
    simp only [List.mem_range] at hk
    have : (JInt.wrap .i64 (1 + (k : Int))).val = 1 + k := ival_wrap _ (by omega)
    rw [this, show (1 + (k : Int) - 1).toNat = k by omega]
  rw [hfold, foldl_set_range _ _ _ (Nat.le_refl _), List.drop_length, List.append_nil]

/-- A successful `Array{T,N}(undef, dims)` has nonnegative dimensions and fewer than `2^63` slots. -/
theorem allocError_none (l : MemoryLayout) (ds : List Int) (h : arrayAllocError l ds = none) :
    (∀ d ∈ ds, 0 ≤ d) ∧ (ds.map Int.toNat).prod < 2 ^ 63 := by
  match ds, h with
  | [], _ => simp
  | [d], h =>
    unfold arrayAllocError at h
    by_cases hc : d < 0 ∨ ¬ memoryFits l d.toNat
    · simp [hc] at h
    · have h1 : 0 ≤ d := by omega
      have h2 : memoryFits l d.toNat := by
        by_cases hf : memoryFits l d.toNat
        · exact hf
        · exact absurd (Or.inr hf) hc
      have := h2.1
      unfold maxIntVal at this
      simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, Nat.mul_one]
      exact ⟨h1, by omega⟩
  | a :: b :: rest, h =>
    unfold arrayAllocError at h
    by_cases hc : 2 ≤ (a :: b :: rest).length ∧ ((∃ d ∈ a :: b :: rest, d < 0 ∨ d = 9223372036854775807) ∨
        9223372036854775807 < (a :: b :: rest).prod)
    · simp only [hc, ite_true] at h; cases h
    · simp only [hc, ite_false] at h
      have hlen : 2 ≤ (a :: b :: rest).length := by simp
      have hnn : ∀ d ∈ a :: b :: rest, 0 ≤ d := by
        intro d hd
        by_cases h0 : 0 ≤ d
        · exact h0
        · exact absurd ⟨hlen, Or.inl ⟨d, hd, Or.inl (by omega)⟩⟩ hc
      by_cases hf : memoryFits l (a :: b :: rest).prod.toNat
      · obtain ⟨hcast, hp0⟩ := prod_toNat_cast _ hnn
        have := hf.1
        unfold maxIntVal at this
        refine ⟨hnn, ?_⟩
        have : ((a :: b :: rest).map Int.toNat).prod = (a :: b :: rest).prod.toNat := by omega
        omega
      · simp only [hf, not_false_eq_true, ite_true] at h; cases h

/-- `Array{T,N}(undef, dims)` for dimensions of every `Integer` type. -/
theorem heapAllocateValues_run {Tag : Type} (layout : Tag → Option MemoryLayout)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (T : Tag) (l : MemoryLayout)
    (hl : layout T = some l) (dims : List round4.IntegerValue) (heap : VectorHeap α) :
    (round4.heapAllocateValues layout ops T dims).run heap =
      if dims.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max)) then
        .error .inexact
      else allocOutcome l T (dims.map (·.val)) heap := by
  have hmap : ∀ (f : round4.IntegerValue → VectorM α I),
      (∀ d (h : VectorHeap α), (f d).run h =
        if IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max then .ok (JInt.wrap .i64 d.val, h)
        else .error .inexact) →
      ∀ ds : List round4.IntegerValue, (ds.mapM f).run heap =
      if ds.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max)) then
        .error .inexact
      else .ok (ds.map (fun d => JInt.wrap .i64 d.val), heap) := by
    intro f hf ds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.mapM_cons, vector_bind_run, hf, List.any_cons]
      by_cases hd : IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max
      · simp only [hd, and_self, ite_true]
        rw [ih]
        cases hany : ds.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max)) <;>
          simp [hd, hany] <;> rfl
      · simp [hd]
  simp only [round4.heapAllocateValues, vector_bind_run]
  erw [hmap _ ?hfgoal]
  cases hany : dims.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max))
  · simp only [Bool.false_eq_true, ite_false]
    unfold heapAllocateIntDims
    rw [heapArrayUndef_run layout T l hl]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro d hd
    by_cases hfit : IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max
    · exact ival_wrap _ hfit
    · exfalso
      have h2 : dims.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max)) = true :=
        List.any_eq_true.mpr ⟨d, hd, by simp [hfit]⟩
      rw [hany] at h2; cases h2
  · rfl
  case hfgoal =>
    intro d h
    by_cases hd : IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max
    · have hc : d.toInt ops = .ok (JInt.wrap .i64 d.val) := by rw [integerValue_toInt hops, if_pos hd]
      simp only [hc, if_pos hd]
      rfl
    · have hc : d.toInt ops = .error .inexact := by rw [integerValue_toInt hops, if_neg hd]
      simp only [hc, if_neg hd]
      rfl

theorem fresh_wrap_val {Tag : Type} (a : HeapArray Tag) (hP : a.dimensions.prod < 2 ^ 63) :
    (JInt.wrap .i64 (a.dimensions.prod : Int)).val =
      ((List.replicate a.dimensions.prod (none : Option α)).length : Int) := by
  rw [List.length_replicate]; exact ival_wrap _ (by omega)

theorem fillTyped_fresh {Tag : Type} (ei : HeapArray Tag → VectorM α (List I)) (a : HeapArray Tag)
    (heap : VectorHeap α) (hs : heap[a.handle]? = some (List.replicate a.dimensions.prod none)) (W : I)
    (hei : (ei a).run heap = .ok (intRange one W, heap))
    (hWv : W.val = ((List.replicate a.dimensions.prod (none : Option α)).length : Int)) (x : α) :
    (fillTyped ei (fun a x i => heapSet a.handle x i) a x).run heap =
      .ok (a, heap.set a.handle (List.replicate a.dimensions.prod (some x))) := by
  simp only [fillTyped, vector_bind_run, hei]
  simp only [setRange_run a.handle x W heap _ hs hWv, List.length_replicate, vector_pure_run]

/-- `fill!(a, v)` on a Base array whose `P < 2^63` slots are all unassigned. -/
theorem fillFresh_run {Tag β : Type} (a : HeapArray Tag) (heap : VectorHeap α)
    (hs : heap[a.handle]? = some (List.replicate a.dimensions.prod none))
    (hP : a.dimensions.prod < 2 ^ 63)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α) (v : β) :
    (round4.heapFillAll already asTyped convert a v).run heap =
      (if already v then .ok (asTyped v) else convert v).map (fun x =>
        (a, heap.set a.handle (List.replicate a.dimensions.prod (some x)))) := by
  have hfill := fillTyped_fresh (fun a : HeapArray Tag =>
    (pure (intRange one (JInt.wrap .i64 (a.dimensions.prod : Int))) : VectorM α (List I)))
    a heap hs _ (vector_pure_run _ _) (fresh_wrap_val a hP)
  simp only [round4.heapFillAll, fillBang]
  cases ha : already v
  · simp only [Bool.false_eq_true, ite_false, vector_bind_run, vector_lift_run]
    cases convert v with
    | error e => rfl
    | ok x => simp only [Except.map]; exact hfill x
  · simp only [ite_true, vector_bind_run, vector_pure_run]
    exact hfill _

/-- Allocation of `Integer` dimensions followed by `fill!` with an element computed in between. -/
theorem allocFill_run {Tag β : Type} (layout : Tag → Option MemoryLayout)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (T : Tag) (l : MemoryLayout)
    (hl : layout T = some l) (dims : List round4.IntegerValue) (heap : VectorHeap α)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α) (ev : Except Error β) :
    (do
      let a ← round4.heapAllocateValues layout ops T dims
      let e ← (liftM ev : VectorM α β)
      let _ ← round4.heapFillAll already asTyped convert a e
      pure a).run heap =
      round4.filledOutcome l T dims (ev.bind fun v => if already v then .ok (asTyped v) else convert v)
        heap := by
  simp only [vector_bind_run]
  rw [heapAllocateValues_run layout ops hops T l hl]
  unfold round4.filledOutcome
  cases hany : dims.any (fun d => !decide (IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max))
  · simp only [Bool.false_eq_true, ite_false]
    unfold allocOutcome
    cases hn : arrayAllocError l (dims.map (·.val)) with
    | some e => rfl
    | none =>
      obtain ⟨_, hP⟩ := allocError_none l _ hn
      simp only [vector_lift_run]
      cases ev with
      | error e => rfl
      | ok v =>
        simp only [Except.map, Except.bind]
        have hs : (heap ++ [List.replicate ((dims.map (·.val)).map Int.toNat).prod (none : Option α)])[heap.length]? =
            some (List.replicate ((dims.map (·.val)).map Int.toNat).prod none) := by simp
        rw [fillFresh_run (⟨heap.length, T, (dims.map (·.val)).map Int.toNat,
          ((dims.map (·.val)).map Int.toNat).map (fun n => (1, n))⟩ : HeapArray Tag) _ hs hP
          already asTyped convert v]
        cases (if already v = true then Except.ok (asTyped v) else convert v) with
        | error e => rfl
        | ok x =>
          simp only [Except.map, vector_pure_run, round4.freshHeapArray, List.map_map]
          rw [List.set_append_right _ _ (Nat.le_refl _)]
          simp
          rfl
  · rfl


/-- Allocation of `Integer` dimensions followed by `fill!` with a given value. -/
theorem allocFillValue_run {Tag β : Type} (layout : Tag → Option MemoryLayout)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (T : Tag) (l : MemoryLayout)
    (hl : layout T = some l) (dims : List round4.IntegerValue) (heap : VectorHeap α)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α) (v : β) :
    (do
      let a ← round4.heapAllocateValues layout ops T dims
      let _ ← round4.heapFillAll already asTyped convert a v
      pure a).run heap =
      round4.filledOutcome l T dims (if already v then .ok (asTyped v) else convert v) heap := by
  have h := allocFill_run layout ops hops T l hl dims heap already asTyped convert (.ok v)
  simp only [vector_bind_run, vector_lift_run, Except.map, Except.bind] at h ⊢
  exact h

theorem fillDimensionsSpec : round4.FillDimensionsSpec := by
  intro Tag α layout ops typeOf v l heap dims mixed hops hl
  dsimp only
  have key := fun ds => allocFillValue_run layout ops hops (typeOf v) l hl ds heap
    (fun _ => true) id (fun x => .ok x) v
  simp only [ite_true, id] at key
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [fillVarargs, fill585]; exact key dims
  · simp only [fill585]; exact key dims
  · simp only [fillMixedDims, fill586]; exact key _
  · simp only [fill587]; exact key []

theorem constantArraySpec : round4.ConstantArraySpec := by
  intro Tag α β layout ops target float64 lt lf element already asTyped convert heap dims mixed
    hops hlt hlf
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [constantTypedVarargs, constant637]
    exact allocFill_run layout ops hops target lt hlt dims heap already asTyped convert (element target)
  · simp only [constantVarargs, constantDefaultType, constant637]
    exact allocFill_run layout ops hops float64 lf hlf dims heap already asTyped convert (element float64)
  · simp only [constant642]
    exact allocFill_run layout ops hops target lt hlt [] heap already asTyped convert (element target)
  · simp only [constantMixedDims, constant637]
    exact allocFill_run layout ops hops target lt hlt _ heap already asTyped convert (element target)
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c
open JuliaLean.Proofs.base.array

 theorem MultidimcovArrayV2Fill_proven : JuliaLean.Proofs.base.array.CompleteFillSpec :=
  ⟨fillContentsSpec, abstractFillSpec⟩
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

/-- Filling converts before obtaining iteration keys. A failed conversion retains
its state; a successful conversion to the wrong type raises TypeError without
calling the user-selected _fill! method. -/
def FillCheckedErrors : Prop :=
  ∀ (W V E A : Type) (cast : V → Option E)
    (convert : V → ExceptT Error (StateM W) V)
    (fill : A → E → ExceptT Error (StateM W) A)
    (a : A) (x : V) (before after : W) (error : Error),
    cast x = none →
    ((convert x).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.fillChecked cast convert fill a x).run before =
        (.error error, after)) ∧
    (∀ value, (convert x).run before = (.ok value, after) → cast value = none →
      (JuliaLean.base.array.Completion.fillChecked cast convert fill a x).run before =
        (.error (.typeError "fill!"), after))

/-- For every live iterator implementation, fill returns its original array
handle on success and retains an eachindex failure before any write. -/
def FillTypedIdentityAndErrors : Prop :=
  ∀ (W A E K Keys : Type) [ForIn (ExceptT Error (StateM W)) Keys K]
    (keys : A → ExceptT Error (StateM W) Keys)
    (set : A → E → K → ExceptT Error (StateM W) Unit)
    (a : A) (value : E) (before after : W),
    (∀ result, (fillTyped keys set a value).run before = (.ok result, after) → result = a) ∧
    (∀ error, (keys a).run before = (.error error, after) →
      (fillTyped keys set a value).run before = (.error error, after))
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default. -/
def FillVarargsArguments : Prop :=
  ∀ (E D : Type) (value : E) (dims : List D) (initial : List Nat),
    (JuliaLean.base.array.Completion3.fillVarargs (fun x ds => call 0 (.ok (x, ds))) value dims).run initial =
      (.ok (value, dims), initial ++ [0])

/-- The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default. -/
def ConstantVarargsArguments : Prop :=
  ∀ (D : Type) (dims : List D) (initial : List Nat),
    (JuliaLean.base.array.Completion3.constantVarargs (fun ds => call 0 (.ok ds)) dims).run initial =
      (.ok dims, initial ++ [0])

/-- The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default. -/
def ConstantTypedVarargsArguments : Prop :=
  ∀ (T D : Type) (ty : T) (dims : List D) (initial : List Nat),
    (JuliaLean.base.array.Completion3.constantTypedVarargs (fun t ds => call 0 (.ok (t, ds))) ty dims).run initial =
      (.ok (ty, dims), initial ++ [0])

/-- The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default. -/
def ConstantDefaultFloat64 : Prop :=
  ∀ (Other D : Type) (dims : D) (initial : List Nat),
    (JuliaLean.base.array.Completion3.constantDefaultType (fun (t : TypeArgument Other) ds => call 0 (.ok (t, ds))) dims).run initial =
      (.ok (TypeArgument.float64, dims), initial ++ [0])

/-- Mixed integer/OneTo dimension tuples preserve integer values, convert each OneTo endpoint once in tuple order, then forward the normalized dimensions. -/
def FillMixedDimensions : Prop :=
  ∀ (T E : Type) (value : E) (dims : List (Sum T T)) (initial : List Nat),
    let encoded := dims.map (fun d => match d with
      | .inl value => Dim.integer value
      | .inr stop => Dim.oneTo ⟨stop⟩)
    let normalized := dims.map (fun d => match d with | .inl n => n | .inr n => n)
    let conversions := dims.filterMap (fun d => match d with | .inl _ => none | .inr _ => some 0)
    (JuliaLean.base.array.Completion3.fillMixedDims (fun n => call 0 (.ok n))
      (fun value dims => call 1 (.ok (value, dims))) value encoded).run initial =
        (.ok (value, normalized), initial ++ conversions ++ [1])

/-- Mixed integer/OneTo dimension tuples preserve integer values, convert each OneTo endpoint once in tuple order, then forward the normalized dimensions. -/
def ConstantMixedDimensions : Prop :=
  ∀ (T E : Type) (value : E) (dims : List (Sum T T)) (initial : List Nat),
    let encoded := dims.map (fun d => match d with
      | .inl value => Dim.integer value
      | .inr stop => Dim.oneTo ⟨stop⟩)
    let normalized := dims.map (fun d => match d with | .inl n => n | .inr n => n)
    let conversions := dims.filterMap (fun d => match d with | .inl _ => none | .inr _ => some 0)
    (JuliaLean.base.array.Completion3.constantMixedDims (fun n => call 0 (.ok n))
      (fun value dims => call 1 (.ok (value, dims))) value encoded).run initial =
        (.ok (value, normalized), initial ++ conversions ++ [1])
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion4
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion4
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- Allocation through the dimension-index similar method precedes filling; its error and effects propagate before the first write. -/
def FillAxesAllocationErrors : Prop :=
  ∀ (W Dims A E R : Type) (similar : Dims → ExceptT Error (StateM W) A)
    (fill : A → E → ExceptT Error (StateM W) R) (value : E) (dims : Dims)
    (before after : W) (error : Error),
    (similar dims).run before = (.error error, after) →
    (fillAxes similar fill value dims).run before = (.error error, after)

/-- Dimension-index constant allocation happens before zero/one computation. A zero/one error keeps the allocation effects and suppresses filling. -/
def ConstantAxesElementErrors : Prop :=
  ∀ (W Dims A E R : Type) (similar : Dims → ExceptT Error (StateM W) A)
    (element : ExceptT Error (StateM W) E) (fill : A → E → ExceptT Error (StateM W) R)
    (dims : Dims) (allocated : A) (before middle after : W) (error : Error),
    (similar dims).run before = (.ok allocated, middle) →
    element.run middle = (.error error, after) →
    (constantAxes similar element fill dims).run before = (.error error, after)
end JuliaLean.Proofs.base.array.Completion4


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

abbrev NativeFillFailure := Sum JuliaLean.base.range.Exc NativeCopyFailure
abbrev NativeFillResult (World A : Type) :=
  Option (Except (NativeFillFailure × World) (A × World))

/-- Preserve every original native/Array error family when injecting an
independently observed boundary result into the scalar-fill result family. -/
def NativeFillPromote (observed : NativeCopyResult World A) : NativeFillResult World A :=
  match observed with
  | none => none
  | some (.error (error, after)) => some (.error (.inr error, after))
  | some (.ok value) => some (.ok value)

/-- Observe the complete model result without erasing range errors, native
errors, the post-error world or divergence. This is a representation observer. -/
def NativeFillObserve (action : NativeFillM World A) (before : World) :
    NativeFillResult World A :=
  match NativeCopyObserve action.run before with
  | none => none
  | some (.error (error, after)) => some (.error (.inr error, after))
  | some (.ok (.error error, after)) => some (.error (.inl error, after))
  | some (.ok (.ok value, after)) => some (.ok (value, after))

/-- Independent singleton Core reference/store protocol. The rank-zero shape
has exactly one valid linear index. Observe the existing raw memoryrefNew
boundary at that mathematical index and the source's false Bool; only its
successful returned reference is passed to the original-value not_atomic/false
store. Native errors, post-error worlds and divergence short-circuit that store.
No modeled bounds, index, loop or setter method computes the expected result,
and no capacity/false-Bool behavior is assumed for the Core boundary. Sources:
base/array.jl:373-378,1031-1041; base/essentials.jl:385-393. -/
def NativeFillOtherRequest (native : NativeFillBoundary State T)
    (array : NativeCopyArray T) (value : T) (before : NativeCopyWorld State) :
    NativeFillResult (NativeCopyWorld State) (NativeCopyArray T) :=
  match NativeCopyObserve
      (native.memoryrefNew array.ref (JInt.wrap .i64 1) false) before with
  | none => none
  | some (.error (error, afterReference)) => some (.error (.inr error, afterReference))
  | some (.ok (reference, afterReference)) =>
      NativeFillPromote (NativeCopyReturn array
        (NativeCopyObserve
          (native.memoryrefSet reference value .notAtomic false) afterReference))

/-- Independent byte-fill ABI request. signedValue is supplied by an actual
UInt8 or Int8 payload in the exhaustive public type dispatch below, so it always
fits Cint. The mathematical singleton count is one Csize_t, and the pointer is
observed from native header fields independently of the pointer model. Only
raw memset and the one ordered GC-end action are observed; their errors, state
and divergence are never assumed away. In particular a negative Int8 remains
negative in Cint. This source byte overload does not call the indexed Core
reference boundary. Sources: array.jl:473-480;
cmem.jl:40-43; pointer.jl:75-87. -/
def NativeFillByteRequest (native : NativeFillBoundary State T)
    (array : NativeCopyArray T) (signedValue : Int) (before : NativeCopyWorld State) :
    NativeFillResult (NativeCopyWorld State) (NativeCopyArray T) :=
  let changed := native.memset before.bytes (NativeCopyCvoidAddress array.ref)
    (JInt.wrap .i32 signedValue) (JInt.wrap .u64 1)
  NativeFillPromote (NativeCopyReturn array
    (NativeCopyObserve (native.gcPreserveEnd (native.gcPreserveBegin array.ref))
      { before with bytes := changed.1 }))

/-- Independent full scalar-fill protocol. The supplied raw allocation type
metadata is checked for a one-element, rank-zero request by the independent
native-allocation observer. Every failure/divergence short-circuits all writes.
On success the two byte type tags select exactly one C-byte request; all other
type tags select a Core reference request followed by one same-value store
only on success. This describes
cardinality, original object/value identity, raw native arguments and effects;
it does not evaluate any fill!, setindex!, eachindex or iterator model. -/
def NativeFillRequest {OtherType : Type} (Values : OtherType → Type)
    (kind : NativeFillKind OtherType) :
    NativeFillBoundary State (NativeFillValue Values kind) →
    NativeFillValue Values kind → NativeCopyWorld State →
    NativeFillResult (NativeCopyWorld State) (NativeCopyArray (NativeFillValue Values kind)) :=
  match kind with
  | .uint8 => fun native value before =>
      match NativeUndefRequest native.allocation [] before with
      | none => none
      | some (.error (error, after)) => some (.error (.inr error, after))
      | some (.ok (array, after)) => NativeFillByteRequest native array value.val after
  | .int8 => fun native value before =>
      match NativeUndefRequest native.allocation [] before with
      | none => none
      | some (.error (error, after)) => some (.error (.inr error, after))
      | some (.ok (array, after)) => NativeFillByteRequest native array value.val after
  | .other _ => fun native value before =>
      match NativeUndefRequest native.allocation [] before with
      | none => none
      | some (.error (error, after)) => some (.error (.inr error, after))
      | some (.ok (array, after)) => NativeFillOtherRequest native array value after

/-- Source array.jl:587 and fill documentation at array.jl:534-583. All scalar
values and every Julia typeof tag are included. The empty dimension tuple is
the entire selected input domain and is machine-constructible; no extra header,
allocation-success or content premise is needed. The exact raw-native protocol
constrains all errors, partial state and divergence. It is falsified by omitted
or repeated stores, wrong element/pointer/count/type dispatch, omitted Core
reference requests, incorrect reference arguments, storing after reference
failure, wrong GC ordering, or replacing an error with a default. Native
reference/store/memset semantics and allocator freshness remain at their
existing explicit interfaces.
-/
def FillScalarNativeContract : Prop :=
  ∀ (State OtherType : Type) (Values : OtherType → Type)
    (kind : NativeFillKind OtherType)
    (native : NativeFillBoundary State (NativeFillValue Values kind))
    (value : NativeFillValue Values kind) (before : NativeCopyWorld State),
    NativeFillObserve (nativeFillScalar Values kind native value) before =
      NativeFillRequest Values kind native value before
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion.FillCheckedErrors_proven : JuliaLean.Proofs.base.array.Completion.FillCheckedErrors := by
  unfold JuliaLean.Proofs.base.array.Completion.FillCheckedErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.fillChecked, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.FillVarargsArguments_proven : JuliaLean.Proofs.base.array.Completion3.FillVarargsArguments := by
  unfold JuliaLean.Proofs.base.array.Completion3.FillVarargsArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.fillVarargs, JuliaLean.base.array.fillVarargs, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.ConstantVarargsArguments_proven : JuliaLean.Proofs.base.array.Completion3.ConstantVarargsArguments := by
  unfold JuliaLean.Proofs.base.array.Completion3.ConstantVarargsArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.constantVarargs, JuliaLean.base.array.constantVarargs, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.ConstantTypedVarargsArguments_proven : JuliaLean.Proofs.base.array.Completion3.ConstantTypedVarargsArguments := by
  unfold JuliaLean.Proofs.base.array.Completion3.ConstantTypedVarargsArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.constantTypedVarargs, JuliaLean.base.array.constantTypedVarargs, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.ConstantDefaultFloat64_proven : JuliaLean.Proofs.base.array.Completion3.ConstantDefaultFloat64 := by
  unfold JuliaLean.Proofs.base.array.Completion3.ConstantDefaultFloat64
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.constantDefaultType, JuliaLean.base.array.constantDefaultType, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.FillAxesAllocationErrors_proven : JuliaLean.Proofs.base.array.Completion4.FillAxesAllocationErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.FillAxesAllocationErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.fillAxes, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.ConstantAxesElementErrors_proven : JuliaLean.Proofs.base.array.Completion4.ConstantAxesElementErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.ConstantAxesElementErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.constantAxes, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesFill1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-zeros-ones", juliaFile := "base/array.jl",
    juliaFns := ["zeros(dims...)", "ones(dims...)", "zeros(::Type, dims...)", "ones(::Type, dims...)",
      "$fname@633", "$fname@634", "$fname@635", "$fname@636", "$fname@637", "$fname@642", "$fname@647"],
    statement := "`zeros`/`ones` (array.jl:611-651, the `$fname` methods; docstrings at array.jl:590-628: \"Create an `Array`, with element type `T`, of all zeros with size specified by `dims`\") on the heap, with `$felt(T)` (`zero(T)`/`one(T)`, number.jl, user-extensible: any value or error) and `fill!`'s conversion: `zeros(T, dims::Integer...)` for dimensions of every `Integer` type (mixed types, `Bool` and `BigInt` included), `zeros(dims...)` with the default `Float64`, `zeros(T, ())` (zero dimensions, one element) and `zeros(T, dims)` with `Integer`/`OneTo` dimensions (`to_dim`) each give `filledResult`.",
    source := "base/array.jl:590-628, array.jl:611-651", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.ConstantArraySpec, thm := some ``opusGrowth.constantArraySpec,
    notes := "" },
  { id := "multidimcov-array-v2-fill-dims", juliaFile := "base/array.jl",
    juliaFns := ["fill(v, dims::DimOrInd...)", "fill(v, ::NTuple{N,Union{Integer,OneTo}})",
      "fill(v, ::NTuple{N,Integer})", "fill(v, ::NTuple{N,DimOrInd})", "fill(v, ::Tuple{})"],
    statement := "`fill(v, dims)` (array.jl:583-587; docstring at array.jl:535-582: \"Create an array of size `dims` with every location set to `value`\") on the heap, for dimensions of every `Integer` type (and `OneTo`s, `to_dim`): `Array{typeof(v),N}(undef, dims)` (or `similar(Array{typeof(v),N}, dims)` for `OneTo`s) then `fill!(a, v)`: `filledResult` with element type `typeof(v)` and every slot `v`.",
    source := "base/array.jl:535-582, array.jl:583-587", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.FillDimensionsSpec, thm := some ``opusGrowth.fillDimensionsSpec,
    notes := "" },
  { id := "multidimcov-array-v2-fill-bytes", juliaFile := "base/array.jl",
    juliaFns := ["fill!(::Union{Array{UInt8},Array{Int8}}, ::Integer)"],
    statement := "Byte-array fill converts every Integer argument, using int.ofBool for Bool and installed remT for UInt ABI conversion. Successful calls fill every byte in the array window and preserve bytes outside it; failed element conversion propagates InexactError.",
    source := "base/array.jl:473-480", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round6b.ByteFillSpec,
    thm := some ``JuliaLean.Proofs.base.array.round6b.byteFillSpec,
    notes := "" }
]
def entriesFill2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-fill", juliaFile := "base/array.jl",
    juliaFns := ["fill!(::AbstractArray{T}, x)", "_fill!(::AbstractArray{T}, ::T)"],
    statement := "`fill!(A::AbstractArray{T}, x)` and `_fill!(A, x)` (array.jl:368, 373; docstring at array.jl:335-366: \"Fill array `A` with the value `x`. If `x` is an object reference, all elements will refer to the same object.\") for every `AbstractArray`: for Arrays of every shape on the shared heap with `eachindex(A) = 1:length(A)` and array.jl's `_setindex!`, and for any mutable array type with lawful `eachindex`/`setindex!` (`MutableArrayInterface`). A value already of type `T` is stored, otherwise `convert(T, x)` (user-extensible, a parameter with no law) decides: its error propagates with the array unchanged; otherwise every element of `A` becomes the value and `A` is returned (the heap: every slot of its memory, every other heap object unchanged).",
    source := "base/array.jl:335-366, array.jl:368", status := .proven,
    prop := ``CompleteFillSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2Fill_proven,
    notes := "" }
]
def entriesFill3 : List JuliaLean.Registry.Entry := [
{ id := "array-fill-checked-errors", juliaFile := "base/array.jl",
  juliaFns := ["fill!(A::AbstractArray{T}, x) where T"],
  statement := "Filling converts before obtaining iteration keys. A failed conversion retains its state; a successful conversion to the wrong type raises TypeError without calling the user-selected _fill! method.",
  source := "base/array.jl:368-372", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FillCheckedErrors, thm := some ``JuliaLean.Proofs.base.array.Completion.FillCheckedErrors_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-fill-typed-identity-and-errors", juliaFile := "base/array.jl",
  juliaFns := ["_fill!(A::AbstractArray{T}, x::T) where T"],
  statement := "For every live iterator implementation, fill returns its original array handle on success and retains an eachindex failure before any write.",
  source := "base/array.jl:373-378", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion.FillTypedIdentityAndErrors, thm := none,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
def entriesFill4 : List JuliaLean.Registry.Entry := [
{ id := "array-fill-varargs-arguments", juliaFile := "base/array.jl",
  juliaFns := ["fill(v, dims::DimOrInd...)"],
  statement := "The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default.",
  source := "base/array.jl:583-583", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.FillVarargsArguments, thm := some ``JuliaLean.Proofs.base.array.Completion3.FillVarargsArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-fill-mixed-dimensions", juliaFile := "base/array.jl",
  juliaFns := ["fill(v, dims::NTuple{N, Union{Integer, OneTo}}) where {N}"],
  statement := "Mixed integer/OneTo dimension tuples preserve integer values, convert each OneTo endpoint once in tuple order, then forward the normalized dimensions.",
  source := "base/array.jl:584-584", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion3.FillMixedDimensions, thm := none,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-constant-varargs-arguments", juliaFile := "base/array.jl",
  juliaFns := ["$fname(dims::DimOrInd...)"],
  statement := "The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default.",
  source := "base/array.jl:633-633", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.ConstantVarargsArguments, thm := some ``JuliaLean.Proofs.base.array.Completion3.ConstantVarargsArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-constant-typed-varargs-arguments", juliaFile := "base/array.jl",
  juliaFns := ["$fname(::Type{T}, dims::DimOrInd...) where {T}"],
  statement := "The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default.",
  source := "base/array.jl:634-634", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.ConstantTypedVarargsArguments, thm := some ``JuliaLean.Proofs.base.array.Completion3.ConstantTypedVarargsArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-constant-default-float64", juliaFile := "base/array.jl",
  juliaFns := ["$fname(dims::Tuple{Vararg{DimOrInd}})"],
  statement := "The variadic/default overload forwards all dimensions once, retaining the explicit type or selecting the documented Float64 default.",
  source := "base/array.jl:635-635", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.ConstantDefaultFloat64, thm := some ``JuliaLean.Proofs.base.array.Completion3.ConstantDefaultFloat64_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-constant-mixed-dimensions", juliaFile := "base/array.jl",
  juliaFns := ["$fname(::Type{T}, dims::NTuple{N, Union{Integer, OneTo}}) where {T,N}"],
  statement := "Mixed integer/OneTo dimension tuples preserve integer values, convert each OneTo endpoint once in tuple order, then forward the normalized dimensions.",
  source := "base/array.jl:636-636", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion3.ConstantMixedDimensions, thm := none,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesFill5 : List JuliaLean.Registry.Entry := [
{ id := "array-fill-axes-allocation-errors", juliaFile := "base/array.jl",
  juliaFns := ["fill(v, dims::NTuple{N, DimOrInd}) where {N}"],
  statement := "Allocation through the dimension-index similar method precedes filling; its error and effects propagate before the first write.",
  source := "base/array.jl:586-586", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.FillAxesAllocationErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.FillAxesAllocationErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-constant-axes-element-errors", juliaFile := "base/array.jl",
  juliaFns := ["$fname(::Type{T}, dims::NTuple{N, DimOrInd}) where {T,N}"],
  statement := "Dimension-index constant allocation happens before zero/one computation. A zero/one error keeps the allocation effects and suppresses filling.",
  source := "base/array.jl:647-651", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.ConstantAxesElementErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.ConstantAxesElementErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesFill6 : List JuliaLean.Registry.Entry := [
{ id := "array-fill-scalar-native",
     juliaFile := "base/array.jl",
     juliaFns := ["fill"],
     statement := "For fill(v, ()), every scalar type and value requests a one-element rank-zero Array, propagates all allocation/native errors and divergence, and returns the constructed Array identity after the exact native fill request. UInt8/Int8 select one memset byte with signed Cint preservation and ordered GC end; every other type requests Core memoryrefnew at index one with false bounds flag, then sends its successful returned reference and the original value to one not_atomic/false Core store. Native partial effects are retained without content or freshness laws.",
     source := "base/array.jl:534-587; invariant; base/array.jl:368-378,473-480,1031-1041; base/cmem.jl:40-43",
     status := .todo,
     prop := ``JuliaLean.Proofs.base.array.Models1Group13.FillScalarNativeContract,
     thm := none }
]
end JuliaLean.Proofs.base.array

