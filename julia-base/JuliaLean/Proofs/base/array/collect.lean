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
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c

def bitIntegerRuntimeLayout (T : IntTy) : DictLayout where
  metadata :=
    { int64RuntimeMetadata with
      runtimeType :=
        { int64RuntimeMetadata.runtimeType with
          layout := genericMemoryHeader (T.bits / 8) (T.bits / 8) 0 (-1)
          elementType := .datatype ⟨nativeLayout (T.bits / 8) 0 0 (-1) (T.bits / 8) 128,
            nativeLayout (T.bits / 8) 0 0 (-1) (T.bits / 8) 128, fun _ => 0⟩
          elementTag := .bitInteger T } }
  nonAtomicKind := rfl
  nonAtomicFlag := by cases T <;> decide
  unlocked := by cases T <;> decide
  inlineDatatype := by
    intro _ _ _
    exact ⟨_, rfl⟩
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Source and destination allocations retain separate, typed element views. -/
theorem typed_slot_mapM (convert : β → Except Error α)
    (slotConvert : Option (Sum α β) → Except Error (Option (Sum α β)))
    (hlaw : ∀ x, slotConvert (some (.inr x)) = (convert x).map (fun y => some (.inl y)))
    (xs : List β) :
    (xs.map (fun x => some (Sum.inr x))).mapM slotConvert =
      (xs.mapM convert).map (fun values => values.map (fun y => some (Sum.inl y))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, hlaw, Bind.bind, Except.bind]
    cases hx : convert x with
    | error e => simp only [Except.map]
    | ok y =>
      simp only [Except.map]
      rw [ih]
      cases xs.mapM convert <;> rfl

theorem bitinteger_array_mapM_success (T : IntTy) (xs : List (JInt S))
    (hfit : ∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max) :
    (xs.mapM (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))) =
      .ok (xs.map (fun x => JInt.wrap T x.val)) := by
  apply mapM_ok_of_mem
  intro x hx
  rw [bitinteger_array_conversion, ite_eq_left (hfit x hx)]

theorem bitinteger_array_mapM_failure (T : IntTy) (xs : List (JInt S))
    (hbad : ∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max)) :
    (xs.mapM (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))) =
      .error .inexact := by
  induction xs with
  | nil => simp at hbad
  | cons x xs ih =>
    simp only [List.mapM_cons]
    rw [bitinteger_array_conversion]
    by_cases hx : T.min ≤ x.val ∧ x.val ≤ T.max
    · simp only [hx, and_self, ite_true, Bind.bind, Except.bind]
      have htail : ∃ y ∈ xs, ¬(T.min ≤ y.val ∧ y.val ≤ T.max) := by
        obtain ⟨y, hy, hb⟩ := hbad
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hb hx)
        · exact ⟨y, hy, hb⟩
      rw [ih htail]
    · simp only [hx, ite_false, Bind.bind, Except.bind]

/-- `push!(a, x)` for each `x` of `xs` in turn, each converting `x` (`conv`) before growing. -/
def convertPushPlan {β α : Type} (l : MemoryLayout) (conv : β → Except Error α) :
    VectorGeometry → List β → Except Error VectorGeometry
  | g, [] => .ok g
  | g, x :: xs => (conv x).bind fun _ =>
      (growendPlan l g 1).bind fun g' => convertPushPlan l conv g' xs

/-- The first `Array{T,N}(undef, dims)` error (`arrayAllocError`) among the element types `ts`. -/
def firstAllocError {Tag : Type} (layout : Tag → MemoryLayout) (dims : List Int) :
    List Tag → Option Error
  | [] => none
  | t :: ts =>
    match arrayAllocError (layout t) dims with
    | some e => some e
    | none => firstAllocError layout dims ts

def UnknownTypedCollectionSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (xs : List α) (s : MutableMemory α),
    let result := (collectUnknown (mutableAllocate (MemoryLayoutMetadata.ofRuntime l) 0 zero) (mutablePush (MemoryLayoutMetadata.ofRuntime l)) xs).run s
    FollowsSteps (pushesPlan l emptyGeometry xs.length) result (fun r next =>
      r = s.arrays.length ∧ next.contents s.arrays.length = xs.map some ∧
      next.validVector s.arrays.length)

def elementConversion (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (x : β) : Except Error α :=
  if already x then .ok (asTyped x) else convert x

def collectingPush (layout : MemoryLayoutMetadata) (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (handle : Nat) (x : β) : MutationM α Unit := do
  let _ ← JuliaLean.base.array.push already asTyped
    (fun x => stateExceptLift (convert x))
    (push1361 (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
      mutableLength mutableSet) handle x
  pure ()

def UnknownCollectionSpec : Prop :=
  ∀ (α β : Type) (l : DictLayout) (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (xs : List β) (s : MutableMemory α),
    let conv := elementConversion already asTyped convert
    let result := (collectTyped (fun _ => ())
      (fun (_ : Type) itr (_ : Unit) => collectUnknown (mutableAllocate (MemoryLayoutMetadata.ofRuntime l) 0 zero)
        (collectingPush (MemoryLayoutMetadata.ofRuntime l) already asTyped convert) itr) α xs).run s
    FollowsSteps (convertPushPlan l conv emptyGeometry xs) result (fun r next =>
      ∃ ys, xs.mapM conv = .ok ys ∧ r = s.arrays.length ∧
        next.contents s.arrays.length = ys.map some ∧ next.validVector s.arrays.length)

def UnknownIntegerCollectionSpec : Prop :=
  ∀ (T S : IntTy) (xs : List (JInt S)) (s : MutableMemory (JInt T)),
    let l := bitIntegerRuntimeLayout T
    let convert := fun x : JInt S =>
      (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)
    let result := (collectUnknown (mutableAllocate (MemoryLayoutMetadata.ofRuntime l) 0 zero)
      (collectingPush (MemoryLayoutMetadata.ofRuntime l) (fun _ => false) (fun x : JInt S => JInt.wrap T x.val) convert) xs).run s
    FollowsSteps (convertPushPlan l convert emptyGeometry xs) result (fun r next =>
      (∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max) ∧ r = s.arrays.length ∧
      next.contents s.arrays.length = xs.map (fun x => some (JInt.wrap T x.val)) ∧
      next.validVector s.arrays.length)

def CompleteUnknownCollectionSpec : Prop :=
  UnknownTypedCollectionSpec ∧ UnknownCollectionSpec ∧ UnknownIntegerCollectionSpec

abbrev sizedLengthCollect {Tag α X Z : Type} (layout : Tag → Option MemoryLayout) (length : X → Z)
    (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeLength length itr))
        (fun t _ len => arrayForLength (fun len => liftM (toInt len))
          (heapVectorAllocate (α := α) layout) t len) copy t itr ()) target itr

def SizedLengthCollectSpec : Prop :=
  ∀ (Tag α β X Z : Type) (layout : Tag → Option MemoryLayout) (values : X → List β) (length : X → Z)
    (value : Z → Int) (toInt : Z → Except Error I)
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    CollectorIntLaw value toInt → SizedCopyLaw values convert copy →
    ∀ target itr heap, value (length itr) = (values itr).length →
    (sizedLengthCollect layout length toInt copy target itr).run heap =
      if (values itr).length < 2 ^ 63 then
        ((values itr).mapM convert).map
          (fun converted => collectedShape target [(values itr).length] converted heap)
      else .error .inexact

abbrev sizedShapeCollect {Tag α X Axes : Type} (layout : Tag → Option MemoryLayout) (axes : X → Axes)
    (toShape : Axes → VectorM α (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
        (fun t _ axs => arrayForShape (shapedCollectorAllocate layout toShape) t axs)
        copy t itr ()) target itr

def SizedShapeCollectSpec : Prop :=
  ∀ (Tag α β X Axes : Type) (layout : Tag → Option MemoryLayout) (values : X → List β) (axes : X → Axes)
    (toShape : Axes → VectorM α (List I)) (shapePolicy : Axes → Except Error (List I))
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    (∀ axs heap, (toShape axs).run heap =
      (shapePolicy axs).map (fun dims => (dims, heap))) →
    SizedCopyLaw values convert copy →
    ∀ target itr heap,
    (∀ dims shape, shapePolicy (axes itr) = .ok dims →
      intDimensionShape dims = .ok shape → shape.prod = (values itr).length) →
    (sizedShapeCollect layout axes toShape copy target itr).run heap =
      ((shapePolicy (axes itr)).bind intDimensionShape).bind
        (fun shape => ((values itr).mapM convert).map
          (fun converted => collectedShape target shape converted heap))

def SizedIntegerLengthSpec : Prop :=
  ∀ (Tag X : Type) (layout : Tag → Option MemoryLayout) (T S L : IntTy) (values : X → List (JInt S))
    (length : X → JInt L)
    (copy : HeapArray Tag → X → VectorM (JInt T) (HeapArray Tag)),
    SizedCopyLaw values
      (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) copy →
    ∀ target itr heap, (length itr).val = (values itr).length →
    (sizedLengthCollect layout length
      (fun x => (JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact))
      copy target itr).run heap =
      if (values itr).length < 2 ^ 63 then
        if ∀ x ∈ values itr, T.min ≤ x.val ∧ x.val ≤ T.max then
          .ok (collectedShape target [(values itr).length]
            ((values itr).map (fun x => JInt.wrap T x.val)) heap)
        else .error .inexact
      else .error .inexact

def SizedIntegerShapeSpec : Prop :=
  ∀ (Tag X Axes : Type) (layout : Tag → Option MemoryLayout) (T S : IntTy) (values : X → List (JInt S))
    (axes : X → Axes) (toShape : Axes → VectorM (JInt T) (List I))
    (shapePolicy : Axes → Except Error (List I))
    (copy : HeapArray Tag → X → VectorM (JInt T) (HeapArray Tag)),
    (∀ axs heap, (toShape axs).run heap =
      (shapePolicy axs).map (fun dims => (dims, heap))) →
    SizedCopyLaw values
      (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) copy →
    ∀ target itr heap,
    (∀ dims shape, shapePolicy (axes itr) = .ok dims →
      intDimensionShape dims = .ok shape → shape.prod = (values itr).length) →
    (sizedShapeCollect layout axes toShape copy target itr).run heap =
      ((shapePolicy (axes itr)).bind intDimensionShape).bind
        (fun shape =>
          if ∀ x ∈ values itr, T.min ≤ x.val ∧ x.val ≤ T.max then
            .ok (collectedShape target shape
              ((values itr).map (fun x => JInt.wrap T x.val)) heap)
          else .error .inexact)

def NativeHeapShapeCollectSpec : Prop :=
  ∀ (Tag α Axes : Type) (layout : Tag → Option MemoryLayout) (axes : HeapArray Tag → Axes)
    (toShape : Axes → VectorM α (List I))
    (convert : Option α → Except Error (Option α)),
    (∀ src heap, heapDimensionsFit src.dimensions = true →
      (toShape (axes src)).run heap =
        .ok (src.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)), heap)) →
    ∀ target heap src xs, heap[src.handle]? = some xs →
    src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (sizedShapeCollect layout axes toShape (heapArrayCopy convert) target src).run heap =
      (xs.mapM convert).map (fun values =>
        (HeapArray.mk heap.length target src.dimensions
          (src.dimensions.map (fun n => (1, n))), heap ++ [values]))

def NativeIntegerHeapShapeSpec : Prop :=
  ∀ (Axes : Type) (T S : IntTy) (axes : HeapArray IntTy → Axes)
    (toShape : Axes → VectorM (Sum (JInt T) (JInt S)) (List I))
    (slotConvert : Option (Sum (JInt T) (JInt S)) →
      Except Error (Option (Sum (JInt T) (JInt S)))),
    (∀ src heap, heapDimensionsFit src.dimensions = true →
      (toShape (axes src)).run heap =
        .ok (src.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)), heap)) →
    (∀ x, slotConvert (some (.inr x)) =
      ((JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)).map
        (fun y => some (.inl y))) →
    ∀ (heap : VectorHeap (Sum (JInt T) (JInt S))) (src : HeapArray IntTy)
      (xs : List (JInt S)), heap[src.handle]? = some (xs.map (fun x => some (.inr x))) →
    src.elementType = S → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let intLayout := fun t : IntTy => some (MemoryLayout.mk (t.bits / 8) false false)
    (sizedShapeCollect intLayout axes toShape (heapArrayCopy slotConvert) T src).run heap =
      if ∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max then
        .ok (HeapArray.mk heap.length T src.dimensions
          (src.dimensions.map (fun n => (1, n))),
          heap ++ [xs.map (fun x => some (.inl (JInt.wrap T x.val)))])
      else .error .inexact

def CompleteTypedCollectSpec : Prop :=
  CompleteUnknownCollectionSpec ∧ SizedLengthCollectSpec ∧ SizedShapeCollectSpec ∧
    SizedIntegerLengthSpec ∧ SizedIntegerShapeSpec ∧
    NativeHeapShapeCollectSpec ∧ NativeIntegerHeapShapeSpec ∧ GeneralSizedShapeSpec

/-- Array collection preserves type, shape and linear order, normalizes axes,
allocates distinct storage without changing old arrays, and rejects unassigned
source elements. The two copy operations are the external AbstractArray interfaces. -/
def ArrayCollectionSpec : Prop :=
  ∀ (Tag α Style Indices : Type) (layout : Tag → Option MemoryLayout)
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag)),
    CollectUnaliasedLaw destStyle srcStyle unaliased →
    CollectCartesianLaw cartesian indexed →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions = src.axes.map Prod.snd →
    src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let operation := collectArray HeapArray.axes
      (collectHeapIndices layout destStyle srcStyle unaliased cartesian indexed) src
    (operation.run heap =
      (xs.mapM collectReadSlot).map (fun values =>
        (HeapArray.mk heap.length src.elementType src.dimensions
          (src.dimensions.map (fun n => (1, n))), heap ++ [values]))) ∧
    (∀ values : List α, xs = values.map some → operation.run heap =
      .ok (HeapArray.mk heap.length src.elementType src.dimensions
        (src.dimensions.map (fun n => (1, n))), heap ++ [xs])) ∧
    (none ∈ xs → operation.run heap = .error .undefinedReference)
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorWindows

/- Wrapped `Int` values are compared through the `ival_*` lemmas; unfolding `JInt.wrap` inside
arithmetic decision procedures is exponential. -/
attribute [local irreducible] JInt.wrap

/-! ### Front deletion -/

theorem vwDeletebeg_error {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (d : I)
    (hd : d.val < 0 ∨ n.val < d.val) :
    (deletebeg (mutableStorage layout) pure handle d).run s =
      (.error (.argument "_deletebeg! requires delta in 0:length(a)"), s) := by
  have hbig : JInt.rem .u64 d > JInt.rem .u64 n := by
    change (JInt.rem .u64 n).val < (JInt.rem .u64 d).val
    have hb := ival_bounds d
    rw [urem_val n h.2.2.2.1]
    rcases hd with hd | hd
    · rw [urem_neg_val d hd]; have := ival_bounds n; omega
    · rw [urem_val d (by have := h.2.2.2.1; omega)]; exact hd
  simp only [deletebeg, ms_length, stateExcept_bind, stateExcept_pure,
    mutableLength_run s handle _ h.1, hbig, ite_true, stateExcept_throw]
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section TypedCollect

attribute [local irreducible] JInt.wrap wrapInt

theorem heapRangeCopy_zero_run {Tag α : Type} (heap : VectorHeap α) (x a : HeapArray Tag)
    (xi si n : I) (hn : n.val = 0) :
    (heapRangeCopy x xi a si n).run heap = .ok ((), heap) := by
  simp only [heapRangeCopy, heapCheckedCopy_zero_eq _ _ _ _ _ _ hn, vector_bind_run,
    vector_pure_run]

/-- The window copy of `setindex_widen_up_to`: the first `p` slots of a vector of `p + k` slots
whose first `p` are assigned land in a fresh vector of the same size. -/
theorem widen_copy_window {β : Type} (pre : List β) (k : Nat) :
    (List.replicate (pre.length + k) (none : Option β)).take ((1 : Int) - 1).toNat ++
        ((pre.map some ++ List.replicate k none).drop ((1 : Int) - 1).toNat).take
          (pre.length : Int).toNat ++
      (List.replicate (pre.length + k) none).drop ((1 : Int) - 1 + pre.length).toNat =
    pre.map some ++ List.replicate k none := by
  have h0 : ((1 : Int) - 1).toNat = 0 := rfl
  have h1 : ((1 : Int) - 1 + pre.length).toNat = pre.length := by omega
  rw [h0, h1, List.take_zero, List.drop_zero, List.nil_append, Int.toNat_natCast,
    List.take_left' (by simp), List.drop_replicate]
  congr 2
  omega

/-- The element types `setindex_widen_up_to` (array.jl:886) allocates while `collect_to!`
(array.jl:895-912) stores `xs` into an array of element type `t`: each value that is not an
instance of the current type moves the result to the `promote_typejoin` of the two. -/
def wideningTypes {Tag α : Type} (L : TypeLattice Tag α) : Tag → List α → List Tag
  | _, [] => []
  | t, x :: xs =>
    if L.isa x t then wideningTypes L t xs
    else L.join t (L.typeof x) :: wideningTypes L (L.join t (L.typeof x)) xs

/-- `collect_to!(dest, itr, offs, st)` (array.jl:895-912, comment: "if a result does not match,
widen the result type and re-dispatch") on a fresh typed vector whose first `p` slots already
hold `pre`: every remaining value `xs` is stored at `p+1, p+2, ...` in order; when a value is not
an instance of the current element type, `setindex_widen_up_to` moves the prefix to a fresh array
whose element type is the `promote_typejoin` of the old type and the value's type. The result has
the shape of `dest`, an element type that admits every stored value, and is `dest` itself when
every value already fits; arrays that existed before the call, other than `dest`, are untouched. -/

def CollectToSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) (heap : VectorHeap α)
    (dest : HeapArray Tag) (pre xs : List α) (k : Nat),
    let ints := dest.dimensions.map (fun n : Nat => (n : Int))
    heap[dest.handle]? = some (pre.map some ++ List.replicate k none) →
    heapDimensionsFit dest.dimensions = true → dest.dimensions.prod = pre.length + k →
    arrayAllocError (layout dest.elementType) ints = none → xs.length ≤ k →
    (∀ v ∈ pre, L.isa v dest.elementType = true) →
    let types := wideningTypes L dest.elementType xs
    let run := (typedCollectTo (fun t => some (layout t)) L dest
      (JInt.wrap .i64 ((pre.length : Int) + 1)) xs).run heap
    (∀ e, firstAllocError layout ints types = some e → run = .error e) ∧
    (firstAllocError layout ints types = none →
      ∃ r next, run = .ok (r, next) ∧
        next[r.handle]? = some ((pre ++ xs).map some ++ List.replicate (k - xs.length) none) ∧
        r.dimensions = dest.dimensions ∧
        (∀ v ∈ pre ++ xs, L.isa v r.elementType = true) ∧
        ((∀ v ∈ xs, L.isa v dest.elementType = true) → r = dest) ∧
        heap.length ≤ next.length ∧
        (∀ h, h < heap.length → h ≠ dest.handle → next[h]? = heap[h]?))

/-- `collect_to_with_first!(dest, v1, itr, st)` (array.jl:875-879): on a fresh typed vector with
room for every value, `v1` goes to the first linear index and the remaining values follow through
`collect_to!`, widening the element type as needed; the result keeps the shape of `dest`, holds
`v1` and then the remaining values, admits all of them, and is `dest` when every value fits. -/
def CollectWithFirstSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) (heap : VectorHeap α)
    (dest : HeapArray Tag) (v1 : α) (itr xs : List α) (k : Nat),
    let ints := dest.dimensions.map (fun n : Nat => (n : Int))
    heap[dest.handle]? = some (List.replicate k none) →
    heapDimensionsFit dest.dimensions = true → dest.dimensions.prod = k →
    arrayAllocError (layout dest.elementType) ints = none →
    xs.length + 1 ≤ k → L.isa v1 dest.elementType = true →
    let types := wideningTypes L dest.elementType xs
    let run := (typedCollectWithFirst (fun t => some (layout t)) L dest v1 itr xs).run heap
    (∀ e, firstAllocError layout ints types = some e → run = .error e) ∧
    (firstAllocError layout ints types = none →
      ∃ r next, run = .ok (r, next) ∧
        next[r.handle]? = some ((v1 :: xs).map some ++ List.replicate (k - 1 - xs.length) none) ∧
        r.dimensions = dest.dimensions ∧
        (∀ v ∈ v1 :: xs, L.isa v r.elementType = true) ∧
        ((∀ v ∈ xs, L.isa v dest.elementType = true) → r = dest))

/-- The widening collectors of array.jl:875-912: `collect_to!` (with `setindex_widen_up_to`) and
`collect_to_with_first!`. -/
def CollectToWideningSpec : Prop := CollectToSpec ∧ CollectWithFirstSpec

def typedCollectSized {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) (shape : List Nat)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  collectUnknownSized (fun _ => et) (fun _ _ => pure shape)
    (fun xs => pure (match xs with | [] => none | x :: t => some (x, t)))
    L.typeof (fun (_ : Unit) t _ (_ : Unit) shp => heapAllocateArray layout t shp)
    (fun _ => false) et et (fun _ => true) (fun _ => true) (fun _ => one) (fun t _ _ => t)
    (typedCollectWithFirst layout L) (fun a _ => pure a) () xs ()

/-- `collect(itr::Generator)` (array.jl:833) for a generator of known shape `shape` yielding `xs`
(`IteratorSize` is `HasLength` or `HasShape`, so the `grow_to!` branch is not taken). -/
def typedCollectGenerator {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) (shape : List Nat)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  collectGenerator (fun _ => ()) (fun _ => et) (fun _ => false) (fun _ => pure ⟨0, et, [], []⟩)
    (fun a _ => pure a) (fun _ _ => pure shape)
    (fun xs => pure (match xs with | [] => none | x :: t => some (x, t)))
    L.typeof (fun t (_ : Unit) shp => heapAllocateArray layout t shp)
    (fun _ => false) et et (fun _ => true) (fun _ => true) (fun _ => one) (fun t _ _ => t)
    (typedCollectWithFirst layout L) (fun a _ => pure a) xs

/-- `collect(itr)` (array.jl:771) for an iterator yielding `xs` whose `IteratorEltype` is
`EltypeUnknown` and whose `IteratorSize` is `HasShape`, which dispatches to the `_collect` method of
array.jl:858. -/
def typedCollect {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) (shape : List Nat)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  JuliaLean.base.array.collect () (fun _ => ()) (fun _ => ())
    (fun (_ : Unit) ys (_ : Unit) (_ : Unit) => typedCollectSized layout L et shape ys) xs

/-- The documented result of collecting a sized iterator whose element type is not known ahead
(`collect` docstring, array.jl:660-697, and the `collect_to!` widening comment at 895-898): an
empty iterator gives an empty array of the inferred element type; otherwise the array has the
iterator's shape, holds its values in iteration order, has an element type admitting every
value, and that element type is the type of the first value whenever every value is an instance
of it. `m` ranges over `collect(itr)`, `collect(::Generator)` and
`_collect(c, itr, ::EltypeUnknown, isz)`. -/
def CollectSizedSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) (et : Tag)
    (shape : List Nat) (xs : List α) (heap : VectorHeap α),
    heapDimensionsFit shape = true → shape.prod = xs.length →
    let ints := shape.map (fun n : Nat => (n : Int))
    let lay := fun t => some (layout t)
    ∀ m ∈ [typedCollectSized lay L et shape, typedCollectGenerator lay L et shape,
      typedCollect lay L et shape],
    (xs = [] → (m xs).run heap = allocOutcome (layout et) et ints heap) ∧
    (∀ x t, xs = x :: t →
      let types := L.typeof x :: wideningTypes L (L.typeof x) t
      (∀ e, firstAllocError layout ints types = some e → (m xs).run heap = .error e) ∧
      (firstAllocError layout ints types = none →
        ∃ r next, (m xs).run heap = .ok (r, next) ∧
          next[r.handle]? = some (xs.map some) ∧ r.dimensions = shape ∧
          (∀ v ∈ xs, L.isa v r.elementType = true) ∧
          ((∀ v ∈ t, L.isa v (L.typeof x) = true) → r.elementType = L.typeof x)))
end TypedCollect
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem mutationForIn_inv {α β σ : Type} (f : β → σ → MutationM α (ForInStep σ))
    (Inv : Nat → σ → MutableMemory α → Prop) :
    ∀ (xs : List β) (k : Nat),
    (∀ (j : Nat) (x : β) (st : σ) (s : MutableMemory α), xs[j]? = some x → Inv (k + j) st s →
      ∃ st' s', (f x st).run s = (.ok (.yield st'), s') ∧ Inv (k + j + 1) st' s') →
    ∀ st s, Inv k st s →
      ∃ st' s', (forIn xs st f).run s = (.ok st', s') ∧ Inv (k + xs.length) st' s'
  | [], k, _, st, s, h => ⟨st, s, rfl, by simpa using h⟩
  | x :: xs, k, step, st, s, h => by
    obtain ⟨st1, s1, h1, hi1⟩ := step 0 x st s rfl (by simpa using h)
    obtain ⟨st2, s2, h2, hi2⟩ := mutationForIn_inv f Inv xs (k + 1)
      (fun j y st s hy hI => by
        obtain ⟨a, b, c, d⟩ := step (j + 1) y st s (by simpa using hy)
          (by rw [show k + (j + 1) = k + 1 + j by omega]; exact hI)
        exact ⟨a, b, c, by rw [show k + 1 + j + 1 = k + (j + 1) + 1 by omega]; exact d⟩)
      st1 s1 (by simpa using hi1)
    refine ⟨st2, s2, ?_, by
      rw [List.length_cons, show k + (xs.length + 1) = k + 1 + xs.length from by omega]
      exact hi2⟩
    simp only [List.forIn_cons, stateExcept_bind, h1]
    exact h2

/-- `filter!(f, a)` (array.jl:3061; docstring at array.jl:3046-3060: "Update collection `a`,
removing elements for which `f` is `false`") on a fully assigned `Vector`: when `f` returns a
`Bool` for every element, `a` becomes, in order, the elements for which `f` is `true`, in a valid
vector, and `a` is returned; the first element on which `f` throws or returns a non-`Bool` decides
the error. -/

abbrev TypedVector (Tag : Type) := Tag × Nat

/-- `push!(dest, x)` (array.jl:1353) on a typed vector. -/

def typedPush {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (dest : TypedVector Tag) (x : α) : MutationM α Unit :=
  mutablePush (layout dest.1) dest.2 x

/-- `empty(dest, T)` (`Vector{T}()`): a fresh empty vector of element type `T`. -/

def typedEmpty {Tag α : Type} (layout : Tag → Option MemoryLayout) (dest : TypedVector Tag) (t : Tag) : MutationM α (TypedVector Tag) := do
  let h ← mutableAllocate (layout t) dest.2 zero
  pure (t, h)

/-- `push_widen(dest, el)` (array.jl:922) on typed vectors: `sizehint!` (array.jl:1612),
`append!(new, dest)` for a vector (array.jl:1422) and `push!` (array.jl:1353). -/

def typedPushWiden {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) :
    TypedVector Tag → α → MutationM α (TypedVector Tag) :=
  pushWiden Prod.fst L.typeof (fun t u => pure (L.join t u)) (typedEmpty layout) (fun d => mutableLength d.2)
    (fun d n => do
      let ms := mutableStorage (layout d.1)
      let _ ← sizehint ms pure
        (growbeg ms pure (growbegInternal ms))
        (growend ms pure (growendInternal ms)) d.2 n false true
      pure d)
    (fun _ => false) (fun _ _ => pure ())
    (fun new dest => do
      let ms := mutableStorage (layout new.1)
      let _ ← appendVector (m := MutationM α) (fun _ => false) pure mutableLength pure
        (growend ms pure (growendInternal ms)) mutableLength
        (fun _ => pure one) mutableCopyto new.2 dest.2
      pure ())
    (typedPush layout)

/-- `grow_to!(dest, itr, st)` (array.jl:935) where the remaining iteration from `st` yields `xs`. -/

def typedGrowTo {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) (dest : TypedVector Tag) (xs : List α) :
    MutationM α (TypedVector Tag) :=
  growTo (listIterator []) (fun d el => L.isa el d.1) (typedPush layout) (typedPushWiden layout L) dest xs

/-- `grow_to!(dest, itr)` (array.jl:914) for an iterator yielding `xs`. -/

def typedGrowFirst {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) (dest : TypedVector Tag)
    (xs : List α) : MutationM α (TypedVector Tag) :=
  growFirst (fun xs => pure (match xs with | [] => none | x :: t => some (x, t)))
    (fun d v => typedEmpty layout d (L.typeof v)) (typedPush layout) (fun d _ st => typedGrowTo layout L d st) dest xs

/-- `collect_to_with_first!(dest, v1, itr, st)` (array.jl:881) for a destination that is not an
`AbstractArray`, here a typed vector reached through `push!`. -/

def typedCollectWithFirstPush {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) :
    TypedVector Tag → α → List α → List α → MutationM α (TypedVector Tag) :=
  collectWithFirst (typedPush layout) (fun d _ st => typedGrowTo layout L d st)

/-- `_collect(c, itr, ::EltypeUnknown, ::SizeUnknown)` (array.jl:855) for an iterator yielding
`xs` with inferred element type `et`, `_similar_for` allocating a fresh empty vector of that
type. -/

def typedCollectUnknown {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) (et : Tag) (xs : List α) :
    MutationM α (TypedVector Tag) :=
  collectEltypeUnknown (fun _ => et)
    (fun (c : Nat) t _ (_ : Unit) => typedEmpty layout (t, c) t)
    (typedGrowFirst layout L) 0 xs ()
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

def collectingPush {layout : MemoryLayoutMetadata} (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (handle : Nat) (x : β) : MutationM α Unit := do
  let _ ← JuliaLean.base.array.push already asTyped
    (fun x => stateExceptLift (convert x))
    (push1361 (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
      mutableLength mutableSet) handle x
  pure ()

abbrev sizedLengthCollect {Tag α X Z : Type} (layout : Tag → Option MemoryLayout) (length : X → Z)
    (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeLength length itr))
        (fun t _ len => arrayForLength (fun len => liftM (toInt len))
          (heapVectorAllocate (α := α) layout) t len) copy t itr ()) target itr

abbrev sizedShapeCollect {Tag α X Axes : Type} (layout : Tag → Option MemoryLayout) (axes : X → Axes)
    (toShape : Axes → VectorM α (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
        (fun t _ axs => arrayForShape (shapedCollectorAllocate layout toShape) t axs)
        copy t itr ()) target itr

abbrev genericSizedShapeCollect {Tag α X Axes : Type} (axes : X → Axes)
    (similar : Tag → Axes → VectorM α (HeapArray Tag))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
        (fun t _ axs => arrayForShape similar t axs) copy t itr ()) target itr

/-- Reading an AbstractArray element is undefined exactly at an unassigned slot. -/
def collectReadSlot : Option α → Except Error (Option α)
  | none => .error .undefinedReference
  | some x => .ok (some x)

/-- Trusted Julia dispatch selects the empty-tuple, OneTo-tuple, or general
axes method; all three implementations below are the source-mirrored methods. -/
abbrev collectHeapIndices {Tag α Style Indices : Type} (layout : Tag → Option MemoryLayout)
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag))
    (axes : List (Int × Nat)) (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  if axes = [] then
    collectIndicesZero (fun a => heapAllocateArray layout a.elementType []) collectHeapEmpty
      destStyle srcStyle unaliased src
  else if axes.all (fun ax => decide (ax.1 = 1)) then
    collectIndicesOneTo (fun ax => JInt.wrap .i64 (ax.2 : Int))
      (fun a dims => heapAllocateIntDims layout a.elementType dims)
      collectHeapEmpty destStyle srcStyle unaliased axes src
  else
    collectIndicesGeneric (fun ax => JInt.wrap .i64 (ax.2 : Int))
      (fun a dims => heapAllocateIntDims layout a.elementType dims)
      HeapArray.axes cartesian indexed axes axes src
end round4
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
section TypedCollect

/-- `_collect(c, itr, ::EltypeUnknown, isz::Union{HasLength,HasShape})` (array.jl:858) for an
iterator of known shape `shape` yielding `xs`, with `et` the inferred element type, `similar` a
fresh typed array and the inference typeassert passing. -/
def typedCollectSized {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) (shape : List Nat)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  collectUnknownSized (fun _ => et) (fun _ _ => pure shape)
    (fun xs => pure (match xs with | [] => none | x :: t => some (x, t)))
    L.typeof (fun (_ : Unit) t _ (_ : Unit) shp => heapAllocateArray layout t shp)
    (fun _ => false) et et (fun _ => true) (fun _ => true) (fun _ => one) (fun t _ _ => t)
    (typedCollectWithFirst layout L) (fun a _ => pure a) () xs ()

/-- `collect(itr::Generator)` (array.jl:833) for a generator of known shape `shape` yielding `xs`
(`IteratorSize` is `HasLength` or `HasShape`, so the `grow_to!` branch is not taken). -/
def typedCollectGenerator {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) (shape : List Nat)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  collectGenerator (fun _ => ()) (fun _ => et) (fun _ => false) (fun _ => pure ⟨0, et, [], []⟩)
    (fun a _ => pure a) (fun _ _ => pure shape)
    (fun xs => pure (match xs with | [] => none | x :: t => some (x, t)))
    L.typeof (fun t (_ : Unit) shp => heapAllocateArray layout t shp)
    (fun _ => false) et et (fun _ => true) (fun _ => true) (fun _ => one) (fun t _ _ => t)
    (typedCollectWithFirst layout L) (fun a _ => pure a) xs

/-- `collect(itr)` (array.jl:771) for an iterator yielding `xs` whose `IteratorEltype` is
`EltypeUnknown` and whose `IteratorSize` is `HasShape`, which dispatches to the `_collect` method of
array.jl:858. -/
def typedCollect {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (et : Tag) (shape : List Nat)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  JuliaLean.base.array.collect () (fun _ => ()) (fun _ => ())
    (fun (_ : Unit) ys (_ : Unit) (_ : Unit) => typedCollectSized layout L et shape ys) xs
end TypedCollect
end round4
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

/-- `filter!(f, a::AbstractVector)` (array.jl:3061) on a store vector inside `SetVecM`: the
stores `a[j] = ai`, `nextind(a, j) = j + 1`, and for a `Vector` `resize!(a, j-1)` (array.jl:1559)
and `sizehint!(a, j-1)` (array.jl:1612). -/
def setVecFilterBang {K : Type} {layout : MemoryLayoutMetadata} (pred : K → SetVecM K Bool) (a : VectorRef) :
    SetVecM K VectorRef :=
  filterBang (fun _ => pure one) (fun a => StateT.lift (mutableLength (α := K) a.handle))
    (fun a x i => StateT.lift (mutableSet a.handle x i))
    pred (fun _ j => pure (j + one)) (fun _ => true)
    (fun a n => StateT.lift (do
      let _ ← resize (m := MutationM K) lengthToInt mutableLength JuliaLean.base.int.band
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
        (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure) a.handle n false
      pure ()))
    (fun a n => StateT.lift (vectorSizehint (layout := layout) a.handle n false true))
    (fun _ _ _ => pure ()) a

/-- `push!(v, x)` (array.jl:1361) on a store vector inside `SetVecM`. -/
def setVecPush {K : Type} {layout : MemoryLayoutMetadata} (a : VectorRef) (x : K) : SetVecM K Unit :=
  StateT.lift (vectorPushTyped (layout := layout) a.handle x)

/-- abstractset.jl's `mapfilter(pred, f, itr, res)` (abstractset.jl:636-641: `for x in itr;
pred(x) && f(res, x); end; res`) for the stateful `pred` and `f` that `_grow!` passes (the
abstractset.jl model takes pure callbacks, so its loop is run here in `SetVecM`). -/
def setVecMapfilter {K : Type} (pred : K → SetVecM K Bool) (f : VectorRef → K → SetVecM K Unit)
    (itr : List K) (res : VectorRef) : SetVecM K Unit := do
  for x in itr do
    if ← pred x then f res x

/-- `_grow!(pred!, v, itrs)` (array.jl:3172) on a store vector. -/
abbrev setVecGrow {K : Type} {layout : MemoryLayoutMetadata} : (K → SetVecM K Bool) → VectorRef → List (List K) →
    SetVecM K VectorRef :=
  grow (fun pred v => do let _ ← setVecFilterBang (layout := layout) pred v; pure ()) (setVecPush (layout := layout)) setVecMapfilter

def wideningTypes {Tag α : Type} (L : TypeLattice Tag α) : Tag → List α → List Tag
  | _, [] => []
  | t, x :: xs =>
    if L.isa x t then wideningTypes L t xs
    else L.join t (L.typeof x) :: wideningTypes L (L.join t (L.typeof x)) xs

def CollectToSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) (heap : VectorHeap α)
    (dest : HeapArray Tag) (pre xs : List α) (k : Nat),
    let ints := dest.dimensions.map (fun n : Nat => (n : Int))
    heap[dest.handle]? = some (pre.map some ++ List.replicate k none) →
    heapDimensionsFit dest.dimensions = true → dest.dimensions.prod = pre.length + k →
    arrayAllocError (layout dest.elementType) ints = none → xs.length ≤ k →
    (∀ v ∈ pre, L.isa v dest.elementType = true) →
    let types := wideningTypes L dest.elementType xs
    let run := (typedCollectTo (fun t => some (layout t)) L dest
      (JInt.wrap .i64 ((pre.length : Int) + 1)) xs).run heap
    (∀ e, firstAllocError layout ints types = some e → run = .error e) ∧
    (firstAllocError layout ints types = none →
      ∃ r next, run = .ok (r, next) ∧
        next[r.handle]? = some ((pre ++ xs).map some ++ List.replicate (k - xs.length) none) ∧
        r.dimensions = dest.dimensions ∧
        (∀ v ∈ pre ++ xs, L.isa v r.elementType = true) ∧
        ((∀ v ∈ xs, L.isa v dest.elementType = true) → r = dest) ∧
        heap.length ≤ next.length ∧
        (∀ h, h < heap.length → h ≠ dest.handle → next[h]? = heap[h]?))

def CollectWithFirstSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) (heap : VectorHeap α)
    (dest : HeapArray Tag) (v1 : α) (itr xs : List α) (k : Nat),
    let ints := dest.dimensions.map (fun n : Nat => (n : Int))
    heap[dest.handle]? = some (List.replicate k none) →
    heapDimensionsFit dest.dimensions = true → dest.dimensions.prod = k →
    arrayAllocError (layout dest.elementType) ints = none →
    xs.length + 1 ≤ k → L.isa v1 dest.elementType = true →
    let types := wideningTypes L dest.elementType xs
    let run := (typedCollectWithFirst (fun t => some (layout t)) L dest v1 itr xs).run heap
    (∀ e, firstAllocError layout ints types = some e → run = .error e) ∧
    (firstAllocError layout ints types = none →
      ∃ r next, run = .ok (r, next) ∧
        next[r.handle]? = some ((v1 :: xs).map some ++ List.replicate (k - 1 - xs.length) none) ∧
        r.dimensions = dest.dimensions ∧
        (∀ v ∈ v1 :: xs, L.isa v r.elementType = true) ∧
        ((∀ v ∈ xs, L.isa v dest.elementType = true) → r = dest))

def CollectToWideningSpec : Prop := CollectToSpec ∧ CollectWithFirstSpec

/-- `collect(element_type, collection)` (array.jl:684; docstring at array.jl:672-683: "Return an
`Array` with the given element type of all items in a collection or iterable. The result has the
same shape and number of dimensions as `collection`.") through `_collect(T, itr, isz)` (array.jl:686,
688), for an iterator yielding `xs`: with a length of any BitInteger type that is the true count
(`HasLength`), `Vector{T}(undef, Int(len))` and `copyto!` give a fresh vector of element type `T`
holding the converted values (`InexactError` when the length is not an `Int`); with an unknown size,
`Vector{T}()` and `push!` give a fresh valid vector of the converted values; a conversion error
propagates in both. -/
def CompleteTypedCollectSpec : Prop :=
  ∀ (Tag α β : Type) (layout : Tag → MemoryLayoutMetadata) (t : IntTy) (target : Tag) (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (length : List β → JInt t) (xs : List β)
    (heap : VectorHeap α) (s : MutableMemory α),
    xs.length < 2 ^ 62 →
    let value := fun x => if already x then .ok (asTyped x) else convert x
    let sized := (sizedLengthCollect layout length indexConvert (heapIterCopy already asTyped convert)
      target xs).run heap
    let unknown := (collectTyped (fun _ => ()) (fun _ itr (_ : Unit) =>
      collectUnknown (mutableAllocate (layout target) 0 zero) (collectingPush (layout := layout target) already asTyped convert) itr)
      target xs).run s
    (¬ intFits (length xs) → sized = .error .inexact) ∧
    ((length xs).val = xs.length → sized = (xs.mapM value).map (fun values =>
      freshHeapArray target [xs.length] (values.map some) heap)) ∧
    (∀ e, xs.mapM value = .error e → ∃ next, unknown = (.error e, next)) ∧
    (∀ values, xs.mapM value = .ok values → ∃ next, unknown = (.ok s.arrays.length, next) ∧
      next.validVector s.arrays.length ∧ next.contents s.arrays.length = values.map some)
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect2

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section lifts
variable {E U α β : Type}

/-- The installed `Array` runtime primitives (array.lean `VectorM`). -/
def liftHeap (x : VectorM α β) : M E U α β := do
  let w ← get
  match x.run w.heap with
  | .ok (b, h) =>
    set { w with heap := h }
    pure b
  | .error e => fail (.base e)

def liftBase (x : Except Error β) : M E U α β :=
  match x with
  | .ok b => pure b
  | .error e => fail (.base e)

def liftRange (x : JuliaLean.base.range.JlX β) : M E U α β :=
  match x with
  | .ok b => pure b
  | .error e => fail (.range e)
end lifts
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect2

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)

/-! ## Shapes and axes -/

/-- One axis returned by `axes(itr)`: a `Base.OneTo` of any `Integer` element type, or any other
`AbstractUnitRange` (a `UnitRange`, an offset axis, a user range type `R`). -/
inductive Axis (R : Type) where
  | oneTo (r : OneTo IntegerValue)
  | other (r : R)

/-- The `OneTo`s of an axes tuple, when every axis is one. -/
def oneTos {R : Type} : List (Axis R) → Option (List (OneTo IntegerValue))
  | [] => some []
  | .oneTo r :: rest => (oneTos rest).map (r :: ·)
  | .other _ :: _ => none

/-- `_similar_shape(itr, isz)` (array.jl:699-701): `nothing`, `length(itr)` or `axes(itr)`. -/
inductive Shape (R : Type) where
  | nothing (value : Option I)
  | length (n : IntegerValue)
  | axes (axs : List (Axis R))

/-- A container passed to `_similar_for` whose type uses Base's `similar(c, T, dims::Dims)`: an
`Array` (array.jl:419), a `UnitRange` such as the `1:1` of `collect(itr)`, or any other
AbstractArray (abstractarray.jl:834 for both, which ignores `c`'s contents). -/
inductive BaseContainer (Tag A : Type) where
  | array (a : HeapArray Tag)
  | range (r : UnitRange I)
  | other (a : A)

/-- `_similar_for`'s container: one with Base's `similar`, or an AbstractArray whose type defines
its own `similar(c, T, dims)` (a user array or package type `C`). -/
inductive Container (Tag A C : Type) where
  | base (c : BaseContainer Tag A)
  | own (c : C)

/-- The raw `dims` argument a container's own `similar(c, T, dims)` method receives. -/
inductive SimilarArg (R : Type) where
  | length (n : IntegerValue)
  | axes (axs : List (Axis R))
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect2

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section models
variable {E U α Tag R V A C X : Type}

/-- `to_shape` of an Integer (abstractarray.jl:840-841): `to_shape(i::Int) = i`, otherwise
`to_shape(i::Integer) = Int(i)` with int.jl's or the Integer type's conversion. -/
def toShapeIntegerValue (ops : BigIntegerOps) (x : IntegerValue) : M E U α I :=
  match x with
  | .bit .i64 i => pure (JuliaLean.base.abstractarray.toShapeInt i)
  | x => JuliaLean.base.abstractarray.toShapeInteger (fun x : IntegerValue => liftBase (x.toInt ops)) x

/-- `to_shape(r::AbstractOneTo) = _to_shape(last(r))` and `_to_shape(x::Integer) = to_shape(x)`
(abstractarray.jl:842-843), with range.jl's `last`. -/
def toShapeAxis (ops : BigIntegerOps) (r : OneTo IntegerValue) : M E U α I :=
  JuliaLean.base.abstractarray.toShapeOneTo
    (fun r => liftRange (JuliaLean.base.range.last_OrdinalRange (R := OneTo IntegerValue)
      (T := IntegerValue) (A := IntegerValue) r))
    (JuliaLean.base.abstractarray.toShapeIntegerHelper (toShapeIntegerValue ops)) r

/-- `Array{T,N}(undef, dims)` with `Int` dimensions: the installed allocator. -/
def allocUndef (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (t : Type) (dims : List I) : M E U α (HeapArray Tag) :=
  liftHeap (heapAllocateIntDims layout (tag t) dims)

/-- `similar(Array{T,N}, axs)` (array.jl:713's callee): a tuple of `OneTo`s goes through
abstractarray.jl:872 and `to_shape`, then array.jl:421 and abstractarray.jl:873 (`T(undef, dims)`);
the empty tuple is already `Dims` (array.jl:421); a tuple with another axis type has no Base
method, so the axis type's own `similar(::Type, axes)` method (`axisStorage`) runs. The storage
type `Array{T,N}` is passed to the abstractarray.jl models as its element type `t`, `N` being the
length of the dimension list. -/
def arraySimilar (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → UM E U V) (t : Type) (axs : List (Axis R)) :
    M E U α (Sum (HeapArray Tag) V) :=
  match oneTos axs with
  | some [] => Sum.inl <$> similar421
      (fun dims => JuliaLean.base.abstractarray.similarStorageDims (allocUndef layout tag) t dims)
      ([] : List I)
  | some rs => Sum.inl <$> JuliaLean.base.abstractarray.similarStorageLegacyOneTo
      (JuliaLean.base.abstractarray.toShapeMixed (toShapeAxis ops))
      (fun t dims => similar421
        (fun dims => JuliaLean.base.abstractarray.similarStorageDims (allocUndef layout tag) t dims) dims)
      t rs
  | none => Sum.inr <$> liftUser (axisStorage t axs)

/-- Dispatch of `_array_for_inner(T, isz, shp)` (array.jl:711-713). -/
def arrayForInner (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → UM E U V) (t : Type) :
    IteratorSize → Shape R → M E U α (Sum (HeapArray Tag) V)
  | .sizeUnknown, .nothing _ => Sum.inl <$>
      arrayForUnknown (fun t n => liftHeap (heapVectorAllocate layout (tag t) n)) t
  | .hasLength, .length len => Sum.inl <$>
      arrayForLength (fun len : IntegerValue => liftBase (len.toInt ops))
        (fun t n => liftHeap (heapVectorAllocate layout (tag t) n)) t len
  | .hasShape _, .axes axs => arrayForShape (arraySimilar layout ops tag axisStorage) t axs
  | _, _ => fail (.base (.method "_array_for_inner"))

/-- Dispatch of `_similar_shape(itr, isz)` (array.jl:699-701): `length(itr)` and `axes(itr)` are
calls into the iterator's methods; an `IsInfinite` iterator has no method. -/
def shapeOf (lengthQ : X → UM E U IntegerValue) (axesQ : X → UM E U (List (Axis R))) (itr : X) :
    IteratorSize → M E U α (Shape R)
  | .sizeUnknown => pure (.nothing (similarShapeUnknown itr))
  | .hasLength => Shape.length <$> similarShapeLength (fun itr => liftUser (lengthQ itr)) itr
  | .hasShape _ => Shape.axes <$> similarShapeAxes (fun itr => liftUser (axesQ itr)) itr
  | .isInfinite => fail (.base (.method "_similar_shape"))

/-- `similar(c, T, dims::Dims)`: array.jl:419 for an `Array`, abstractarray.jl:834 otherwise. -/
def baseSimilarDims (alloc : Type → List I → M E U α B) :
    BaseContainer Tag A → Type → List I → M E U α B
  | .array a, t, dims => similar419 (fun dims => alloc t dims) a dims
  | .range r, t, dims => JuliaLean.base.abstractarray.similarFallback alloc r t dims
  | .other a, t, dims => JuliaLean.base.abstractarray.similarFallback alloc a t dims

/-- `similar(c, T, n::Int)` (abstractarray.jl:823 then 834, or array.jl:419), or the container's
own method. -/
def similarInt (alloc : Type → List I → M E U α B)
    (own : C → Type → SimilarArg R → UM E U V) :
    Container Tag A C → Type → I → M E U α (Sum B V)
  | .own c, t, n => Sum.inr <$> liftUser (own c t (.length (.bit .i64 n)))
  | .base c, t, n => Sum.inl <$> JuliaLean.base.abstractarray.similarTypeVarargs
      (fun c t dims => baseSimilarDims alloc c t dims) c t [n]

/-- `similar(c, T, len)` for a length of any Integer type (abstractarray.jl:823; `(len,)` is
`Dims` for an `Int`, otherwise abstractarray.jl:832 converts it with `to_shape`), or the
container's own method. -/
def similarLength (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → UM E U V) :
    Container Tag A C → Type → IntegerValue → M E U α (Sum (HeapArray Tag) V)
  | .own c, t, len => Sum.inr <$> liftUser (own c t (.length len))
  | .base c, t, len => Sum.inl <$> JuliaLean.base.abstractarray.similarTypeVarargs
      (fun c t (dims : List IntegerValue) => match dims with
        | [.bit .i64 n] => baseSimilarDims (allocUndef layout tag) c t [n]
        | dims => JuliaLean.base.abstractarray.similarLegacyOneTo
            (JuliaLean.base.abstractarray.toShapeMixed (toShapeIntegerValue ops))
            (baseSimilarDims (allocUndef layout tag)) c t dims) c t [len]

/-- `similar(c, T, axs)`: the empty tuple is `Dims` (834/419); a tuple of `OneTo`s goes through
abstractarray.jl:832 and `to_shape`; a tuple with another axis type has no Base method, so the
axis type's own `similar(c, T, axes)` method (`axisSimilar`) runs; a container with its own
`similar` runs that. -/
def similarAxes (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V) :
    Container Tag A C → Type → List (Axis R) → M E U α (Sum (HeapArray Tag) V)
  | .own c, t, axs => Sum.inr <$> liftUser (own c t (.axes axs))
  | .base c, t, axs => match oneTos axs with
    | some [] => Sum.inl <$> baseSimilarDims (allocUndef layout tag) c t []
    | some rs => Sum.inl <$> JuliaLean.base.abstractarray.similarLegacyOneTo
        (JuliaLean.base.abstractarray.toShapeMixed (toShapeAxis ops))
        (baseSimilarDims (allocUndef layout tag)) c t rs
    | none => Sum.inr <$> liftUser (axisSimilar c t axs)

/-- Dispatch of `_similar_for(c::AbstractArray, T, itr, isz, shp)` (array.jl:703-708). -/
def similarFor (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (c : Container Tag A C) (t : Type) (itr : X) :
    IteratorSize → Shape R → M E U α (Sum (HeapArray Tag) V)
  | .sizeUnknown, .nothing _ => similarForUnknown (similarInt (allocUndef layout tag) own) c t itr
  | .hasLength, .length len => similarForLength (similarLength layout ops tag own) c t itr len
  | .hasShape _, .axes axs => similarForAxes (similarAxes layout ops tag own axisSimilar) c t itr axs
  | _, _ => fail (.base (.method "_similar_for"))
end models
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect2

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section expected
variable {E U α Tag R V : Type}

/-- A fresh array of element type `target` and dimensions `dims`, every slot unassigned, at the
next heap handle; every existing heap object is unchanged. Used only for zero elements, which
`Array{T,N}(undef, dims)` allocates for every element type. -/
def fresh (target : Tag) (dims : List Nat) : M E U α (HeapArray Tag) := do
  let w ← get
  set { w with heap := w.heap ++ [List.replicate dims.prod none] }
  pure ⟨w.heap.length, target, dims, dims.map (fun n => (1, n))⟩

/-- `Array{T,N}(undef, dims)` for `Int` dimensions: the installed array runtime allocator
(array.lean `heapAllocateIntDims`), whose size checks and errors are its own. -/
def allocInts (layout : Tag → Option MemoryLayout) (target : Tag) (dims : List Int) : M E U α (HeapArray Tag) :=
  liftHeap (heapAllocateIntDims layout target (dims.map (JInt.wrap .i64)))

/-- `Int(x)`: the equal `Int`, or `InexactError`. -/
def intValue (x : IntegerValue) : M E U α Int :=
  if IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max then pure x.val else fail (.base .inexact)

/-- An array with the given axes: `OneTo` axes give a fresh array whose dimensions are their
lengths; any other axis type gives what that type's own `similar` method returns. -/
def axesAllocation (layout : Tag → Option MemoryLayout) (target : Tag) (other : List (Axis R) → UM E U V) (axs : List (Axis R)) :
    M E U α (Sum (HeapArray Tag) V) :=
  match oneTos axs with
  | some rs => do Sum.inl <$> allocInts layout target (← rs.mapM (fun r => intValue r.stop))
  | none => Sum.inr <$> liftUser (other axs)
end expected
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect2

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)

/-! ## `multidimcov-array-v2-collect-alloc` -/

/-- `_array_for(T, itr, isz)` (array.jl:716, "used by syntax lowering for simple typed
comprehensions") with the installed `_similar_shape` and `_array_for_inner` methods, and
`_similar_for(c, T, itr, isz, shp)` (array.jl:703-708, "make a collection similar to `c` and
appropriate for collecting `itr`") for a container whose type uses Base's `similar` (an `Array`,
a `UnitRange`, any other AbstractArray), for every iterator (its `length` and `axes` are any
user calls), every element type, every Integer length and every axes tuple. The allocation
itself is the installed array runtime's `Array{T,N}(undef, dims)`; the statement fixes which
dimensions reach it and what happens before:

* `SizeUnknown`: a fresh empty `Vector{T}`, with no call into the iterator.
* `HasLength`: `length(itr)` runs once (its effects and exceptions kept); a length of any
  Integer type without an equal `Int` throws `InexactError` before any allocation; otherwise
  `Vector{T}(undef, Int(len))`.
* `HasShape`: `axes(itr)` runs once; `OneTo` axes of any Integer type allocate
  `Array{T,N}(undef, dims)` with `dims` their lengths converted by `Int` (`InexactError` first,
  for the first one without an equal `Int`); no axes allocate a 0-dimensional array; a tuple
  with another axis type goes to that type's own `similar(::Type{Array{T,N}}, axes)`.
* `IsInfinite`: `MethodError`, with no call into the iterator.
* `_similar_for`: the same allocations from the given shape (`0` for an unknown size). -/
def CollectAllocSpec : Prop :=
  ∀ (E U α Tag R V A C X : Type) (ops : BigIntegerOps) (tag : Type → Tag) (layout : Tag → Option MemoryLayout)
    (lengthQ : X → UM E U IntegerValue) (axesQ : X → UM E U (List (Axis R)))
    (axisStorage : Type → List (Axis R) → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (own : C → Type → SimilarArg R → UM E U V)
    (t : Type) (itr : X) (w : World U α),
    ops.Lawful →
    let arrayFor' := fun isz : IteratorSize =>
      (arrayFor (m := M E U α) (shapeOf lengthQ axesQ) (arrayForInner layout ops tag axisStorage)
        t itr isz).run.run w
    let similarFor' := fun (c : Container Tag A C) (isz : IteratorSize) (shp : Shape R) =>
      (similarFor (X := X) layout ops tag own axisSimilar c t itr isz shp).run.run w
    arrayFor' .sizeUnknown =
      (Sum.inl <$> fresh (tag t) [0] : M E U α (Sum (HeapArray Tag) V)).run.run w ∧
    arrayFor' .hasLength =
      (do
        let n ← intValue (← liftUser (lengthQ itr))
        Sum.inl <$> liftHeap (heapVectorAllocate layout (tag t) (JInt.wrap .i64 n)) :
        M E U α (Sum (HeapArray Tag) V)).run.run w ∧
    (∀ n, arrayFor' (.hasShape n) =
      (do axesAllocation layout (tag t) (axisStorage t) (← liftUser (axesQ itr)) :
        M E U α (Sum (HeapArray Tag) V)).run.run w) ∧
    arrayFor' .isInfinite =
      (fail (.base (.method "_similar_shape")) : M E U α (Sum (HeapArray Tag) V)).run.run w ∧
    (∀ c : BaseContainer Tag A,
      similarFor' (.base c) .sizeUnknown (.nothing none) =
        (Sum.inl <$> fresh (tag t) [0] : M E U α (Sum (HeapArray Tag) V)).run.run w ∧
      (∀ len, similarFor' (.base c) .hasLength (.length len) =
        (do Sum.inl <$> allocInts layout (tag t) [← intValue len] :
          M E U α (Sum (HeapArray Tag) V)).run.run w) ∧
      (∀ n axs, similarFor' (.base c) (.hasShape n) (.axes axs) =
        (axesAllocation layout (tag t) (axisSimilar c t) axs :
          M E U α (Sum (HeapArray Tag) V)).run.run w))
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round8
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
namespace Collectors
open JuliaLean.Proofs.base.array.round6dcollect2
open JuliaLean.base.generator (IteratorSize)
open JuliaLean.base.range (OneTo)
section adapters
variable {E U α Tag R V A C X : Type}

def toShapeInteger (ops : BigIntegerOps) (x : IntegerValue) : M E U α I :=
  match x with
  | .bit .i64 i => pure (JuliaLean.base.abstractarray.toShapeInt i)
  | x => JuliaLean.base.abstractarray.toShapeInteger
      (fun x => liftBase (convertInteger ops .i64 x)) x

def toShapeAxis (ops : BigIntegerOps) (r : OneTo IntegerValue) : M E U α I :=
  letI : JuliaLean.base.range.JConvert IntegerValue IntegerValue :=
    ⟨fun x => .ok (JuliaLean.base.number.convertSame x)⟩
  JuliaLean.base.abstractarray.toShapeOneTo
    (fun r => liftRange (JuliaLean.base.range.last_OrdinalRange (R := OneTo IntegerValue)
      (T := IntegerValue) (A := IntegerValue) r))
    (JuliaLean.base.abstractarray.toShapeIntegerHelper (toShapeInteger ops)) r

def shapeOf (lengthQ : X → M E U α IntegerValue)
    (axesQ : X → M E U α (List (Axis R))) (itr : X) : IteratorSize → M E U α (Shape R)
  | .sizeUnknown => pure (.nothing (similarShapeUnknown itr))
  | .hasLength => Shape.length <$> similarShapeLength lengthQ itr
  | .hasShape _ => Shape.axes <$> similarShapeAxes axesQ itr
  | .isInfinite => fail (.base (.method "_similar_shape"))

def similarInt (alloc : Type → List I → M E U α B)
    (own : C → Type → SimilarArg R → M E U α V) :
    Container Tag A C → Type → I → M E U α (Sum B V)
  | .own c, t, n => Sum.inr <$> own c t (.length (.bit .i64 n))
  | .base c, t, n => Sum.inl <$> JuliaLean.base.abstractarray.similarTypeVarargs
      (fun c t dims => baseSimilarDims alloc c t dims) c t [n]

def axesAllocation (layout : Tag → Option MemoryLayout) (target : Tag)
    (other : List (Axis R) → M E U α V) (axs : List (Axis R)) :
    M E U α (Sum (HeapArray Tag) V) :=
  match oneTos axs with
  | some rs => do Sum.inl <$> allocInts layout target (← rs.mapM (fun r => intValue r.stop))
  | none => Sum.inr <$> other axs

def arraySimilar (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → M E U α V) (t : Type) (axs : List (Axis R)) :
    M E U α (Sum (HeapArray Tag) V) :=
  match oneTos axs with
  | some [] => Sum.inl <$> similar421
      (fun dims => JuliaLean.base.abstractarray.similarStorageDims (allocUndef layout tag) t dims)
      ([] : List I)
  | some rs => Sum.inl <$> JuliaLean.base.abstractarray.similarStorageLegacyOneTo
      (JuliaLean.base.abstractarray.toShapeMixed (toShapeAxis ops))
      (fun t dims => similar421
        (fun dims => JuliaLean.base.abstractarray.similarStorageDims (allocUndef layout tag) t dims) dims)
      t rs
  | none => Sum.inr <$> (axisStorage t axs)

def arrayForInner (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → M E U α V) (t : Type) :
    IteratorSize → Shape R → M E U α (Sum (HeapArray Tag) V)
  | .sizeUnknown, .nothing _ => Sum.inl <$>
      arrayForUnknown (fun t n => liftHeap (heapVectorAllocate layout (tag t) n)) t
  | .hasLength, .length len => Sum.inl <$>
      arrayForLength (fun len => liftBase (convertInteger ops .i64 len))
        (fun t n => liftHeap (heapVectorAllocate layout (tag t) n)) t len
  | .hasShape _, .axes axs => arrayForShape (arraySimilar layout ops tag axisStorage) t axs
  | _, _ => fail (.base (.method "_array_for_inner"))

def similarLength (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → M E U α V) :
    Container Tag A C → Type → IntegerValue → M E U α (Sum (HeapArray Tag) V)
  | .own c, t, len => Sum.inr <$> (own c t (.length len))
  | .base c, t, len => Sum.inl <$> JuliaLean.base.abstractarray.similarTypeVarargs
      (fun c t (dims : List IntegerValue) => match dims with
        | [.bit .i64 n] => baseSimilarDims (allocUndef layout tag) c t [n]
        | dims => JuliaLean.base.abstractarray.similarLegacyOneTo
            (JuliaLean.base.abstractarray.toShapeMixed (toShapeInteger ops))
            (baseSimilarDims (allocUndef layout tag)) c t dims) c t [len]

def similarAxes (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → M E U α V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → M E U α V) :
    Container Tag A C → Type → List (Axis R) → M E U α (Sum (HeapArray Tag) V)
  | .own c, t, axs => Sum.inr <$> (own c t (.axes axs))
  | .base c, t, axs => match oneTos axs with
    | some [] => Sum.inl <$> baseSimilarDims (allocUndef layout tag) c t []
    | some rs => Sum.inl <$> JuliaLean.base.abstractarray.similarLegacyOneTo
        (JuliaLean.base.abstractarray.toShapeMixed (toShapeAxis ops))
        (baseSimilarDims (allocUndef layout tag)) c t rs
    | none => Sum.inr <$> (axisSimilar c t axs)

def similarFor (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → M E U α V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → M E U α V)
    (c : Container Tag A C) (t : Type) (itr : X) :
    IteratorSize → Shape R → M E U α (Sum (HeapArray Tag) V)
  | .sizeUnknown, .nothing _ => similarForUnknown (similarInt (allocUndef layout tag) own) c t itr
  | .hasLength, .length len => similarForLength (similarLength layout ops tag own) c t itr len
  | .hasShape _, .axes axs => similarForAxes (similarAxes layout ops tag own axisSimilar) c t itr axs
  | _, _ => fail (.base (.method "_similar_for"))
end adapters
end Collectors
end JuliaLean.Proofs.base.array.round8
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round8
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
namespace Collectors
open JuliaLean.Proofs.base.array.round6dcollect2
open JuliaLean.base.generator (IteratorSize)
open JuliaLean.base.range (OneTo)

def CollectAllocSpec : Prop :=
  ∀ (E U α Tag R V A C G X : Type) (ops : BigIntegerOps) (tag : Type → Tag)
    (elementLayout : Tag → MemoryLayout)
    (lengthQ : X → M E U α IntegerValue) (axesQ : X → M E U α (List (Axis R)))
    (axisStorage : Type → List (Axis R) → M E U α V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → M E U α V)
    (own : C → Type → SimilarArg R → M E U α V) (generic : G → Type → M E U α V)
    (t : Type) (itr : X) (w : World U α), ops.Lawful →
    let layout := fun target => some (elementLayout target)
    let arrayFor' := fun isz : IteratorSize =>
      (arrayFor (m := M E U α) (shapeOf lengthQ axesQ) (arrayForInner layout ops tag axisStorage)
        t itr isz).run.run w
    let similarFor' := fun (c : Container Tag A C) (isz : IteratorSize) (shp : Shape R) =>
      (similarFor (X := X) layout ops tag own axisSimilar c t itr isz shp).run.run w
    arrayFor' .sizeUnknown =
      (Sum.inl <$> fresh (tag t) [0] : M E U α (Sum (HeapArray Tag) V)).run.run w ∧
    arrayFor' .hasLength =
      (do let n ← intValue (← (lengthQ itr))
          Sum.inl <$> liftHeap (heapVectorAllocate layout (tag t) (JInt.wrap .i64 n)) :
        M E U α (Sum (HeapArray Tag) V)).run.run w ∧
    (∀ n, arrayFor' (.hasShape n) =
      (do axesAllocation layout (tag t) (axisStorage t) (← (axesQ itr)) :
        M E U α (Sum (HeapArray Tag) V)).run.run w) ∧
    arrayFor' .isInfinite =
      (fail (.base (.method "_similar_shape")) : M E U α (Sum (HeapArray Tag) V)).run.run w ∧
    (∀ c : BaseContainer Tag A,
      similarFor' (.base c) .sizeUnknown (.nothing none) =
        (Sum.inl <$> fresh (tag t) [0] : M E U α (Sum (HeapArray Tag) V)).run.run w ∧
      (∀ len, similarFor' (.base c) .hasLength (.length len) =
        (do Sum.inl <$> allocInts layout (tag t) [← intValue len] :
          M E U α (Sum (HeapArray Tag) V)).run.run w) ∧
      (∀ n axs, similarFor' (.base c) (.hasShape n) (.axes axs) =
        (axesAllocation layout (tag t) (axisSimilar c t) axs :
          M E U α (Sum (HeapArray Tag) V)).run.run w)) ∧
    (∀ c : C,
      similarFor' (.own c) .sizeUnknown (.nothing none) =
        (Sum.inr <$> (own c t (.length (.ofInt zero))) :
          M E U α (Sum (HeapArray Tag) V)).run.run w ∧
      (∀ len, similarFor' (.own c) .hasLength (.length len) =
        (Sum.inr <$> (own c t (.length len)) :
          M E U α (Sum (HeapArray Tag) V)).run.run w) ∧
      (∀ n axs, similarFor' (.own c) (.hasShape n) (.axes axs) =
        (Sum.inr <$> (own c t (.axes axs)) :
          M E U α (Sum (HeapArray Tag) V)).run.run w)) ∧
    (∀ (c : G) (isz : IteratorSize) (shp : Shape R),
      (similarForGeneric generic c t itr isz shp :
        M E U α V).run.run w = ((generic c t) : M E U α V).run.run w)
end Collectors
end JuliaLean.Proofs.base.array.round8
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section lifts
variable {E U α β : Type}

/-- The installed `Array` runtime primitives (array.lean `VectorM`). -/
def liftHeap (x : VectorM α β) : M E U α β := do
  let w ← get
  match x.run w.heap with
  | .ok (b, h) =>
    set { w with heap := h }
    pure b
  | .error e => fail (.base e)

/-- The installed growable-vector primitives (array.lean `MutationM`). -/
def liftMemory (x : MutationM α β) : M E U α β := do
  let w ← get
  let (r, s) := Id.run (x.run.run w.memory)
  set { w with memory := s }
  match r with
  | .ok b => pure b
  | .error e => fail (.base e)

def liftBase (x : Except Error β) : M E U α β :=
  match x with
  | .ok b => pure b
  | .error e => fail (.base e)

def liftArray (x : JuliaLean.base.abstractarray.Result β) : M E U α β :=
  match x with
  | .ok b => pure b
  | .error e => fail (.array e)
end lifts
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)

/-! ## Shapes and axes -/

/-- One axis returned by `axes(itr)`: a `Base.OneTo` of any `Integer` element type, or any other
`AbstractUnitRange` (a `UnitRange`, an offset axis, a user range type `R`). -/
inductive Axis (R : Type) where
  | oneTo (r : OneTo IntegerValue)
  | other (r : R)

/-- The `OneTo`s of an axes tuple, when every axis is one. -/
def oneTos {R : Type} : List (Axis R) → Option (List (OneTo IntegerValue))
  | [] => some []
  | .oneTo r :: rest => (oneTos rest).map (r :: ·)
  | .other _ :: _ => none

/-- `_similar_shape(itr, isz)` (array.jl:699-701): `nothing`, `length(itr)` or `axes(itr)`. -/
inductive Shape (R : Type) where
  | nothing (value : Option I)
  | length (n : IntegerValue)
  | axes (axs : List (Axis R))

/-- A container passed to `_similar_for` whose type uses Base's `similar(c, T, dims::Dims)`: an
`Array` (array.jl:419), a `UnitRange` such as the `1:1` of `collect(itr)`, or any other
AbstractArray (abstractarray.jl:834 for both, which ignores `c`'s contents). -/
inductive BaseContainer (Tag A : Type) where
  | array (a : HeapArray Tag)
  | range (r : UnitRange I)
  | other (a : A)

/-- `_similar_for`'s container: one with Base's `similar`, or an AbstractArray whose type defines
its own `similar(c, T, dims)` (a user array or package type `C`). -/
inductive Container (Tag A C : Type) where
  | base (c : BaseContainer Tag A)
  | own (c : C)

/-- The raw `dims` argument a container's own `similar(c, T, dims)` method receives. -/
inductive SimilarArg (R : Type) where
  | length (n : IntegerValue)
  | axes (axs : List (Axis R))
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section models
variable {E U α Tag R V A C X : Type}

/-- `to_shape` of an Integer (abstractarray.jl:840-841): `to_shape(i::Int) = i`, otherwise
`to_shape(i::Integer) = Int(i)` with int.jl's or the Integer type's conversion. -/
def toShapeIntegerValue (ops : BigIntegerOps) (x : IntegerValue) : M E U α I :=
  match x with
  | .bit .i64 i => pure (JuliaLean.base.abstractarray.toShapeInt i)
  | x => JuliaLean.base.abstractarray.toShapeInteger (fun x : IntegerValue => liftBase (x.toInt ops)) x

/-- `to_shape(r::AbstractOneTo) = _to_shape(last(r))` and `_to_shape(x::Integer) = to_shape(x)`
(abstractarray.jl:842-843), with range.jl's `last`. -/
def toShapeAxis (ops : BigIntegerOps) (r : OneTo IntegerValue) : M E U α I :=
  JuliaLean.base.abstractarray.toShapeOneTo
    (fun r => liftRange (JuliaLean.base.range.last_OrdinalRange (R := OneTo IntegerValue)
      (T := IntegerValue) (A := IntegerValue) r))
    (JuliaLean.base.abstractarray.toShapeIntegerHelper (toShapeIntegerValue ops)) r

/-- `Array{T,N}(undef, dims)` with `Int` dimensions: the installed allocator. -/
def allocUndef (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (t : Type) (dims : List I) : M E U α (HeapArray Tag) :=
  liftHeap (heapAllocateIntDims layout (tag t) dims)

/-- `similar(Array{T,N}, axs)` (array.jl:713's callee): a tuple of `OneTo`s goes through
abstractarray.jl:872 and `to_shape`, then array.jl:421 and abstractarray.jl:873 (`T(undef, dims)`);
the empty tuple is already `Dims` (array.jl:421); a tuple with another axis type has no Base
method, so the axis type's own `similar(::Type, axes)` method (`axisStorage`) runs. The storage
type `Array{T,N}` is passed to the abstractarray.jl models as its element type `t`, `N` being the
length of the dimension list. -/
def arraySimilar (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → UM E U V) (t : Type) (axs : List (Axis R)) :
    M E U α (Sum (HeapArray Tag) V) :=
  match oneTos axs with
  | some [] => Sum.inl <$> similar421
      (fun dims => JuliaLean.base.abstractarray.similarStorageDims (allocUndef layout tag) t dims)
      ([] : List I)
  | some rs => Sum.inl <$> JuliaLean.base.abstractarray.similarStorageLegacyOneTo
      (JuliaLean.base.abstractarray.toShapeMixed (toShapeAxis ops))
      (fun t dims => similar421
        (fun dims => JuliaLean.base.abstractarray.similarStorageDims (allocUndef layout tag) t dims) dims)
      t rs
  | none => Sum.inr <$> liftUser (axisStorage t axs)

/-- Dispatch of `_array_for_inner(T, isz, shp)` (array.jl:711-713). -/
def arrayForInner (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → UM E U V) (t : Type) :
    IteratorSize → Shape R → M E U α (Sum (HeapArray Tag) V)
  | .sizeUnknown, .nothing _ => Sum.inl <$>
      arrayForUnknown (fun t n => liftHeap (heapVectorAllocate layout (tag t) n)) t
  | .hasLength, .length len => Sum.inl <$>
      arrayForLength (fun len : IntegerValue => liftBase (len.toInt ops))
        (fun t n => liftHeap (heapVectorAllocate layout (tag t) n)) t len
  | .hasShape _, .axes axs => arrayForShape (arraySimilar layout ops tag axisStorage) t axs
  | _, _ => fail (.base (.method "_array_for_inner"))

/-- Dispatch of `_similar_shape(itr, isz)` (array.jl:699-701): `length(itr)` and `axes(itr)` are
calls into the iterator's methods; an `IsInfinite` iterator has no method. -/
def shapeOf (lengthQ : X → UM E U IntegerValue) (axesQ : X → UM E U (List (Axis R))) (itr : X) :
    IteratorSize → M E U α (Shape R)
  | .sizeUnknown => pure (.nothing (similarShapeUnknown itr))
  | .hasLength => Shape.length <$> similarShapeLength (fun itr => liftUser (lengthQ itr)) itr
  | .hasShape _ => Shape.axes <$> similarShapeAxes (fun itr => liftUser (axesQ itr)) itr
  | .isInfinite => fail (.base (.method "_similar_shape"))

/-- `similar(c, T, dims::Dims)`: array.jl:419 for an `Array`, abstractarray.jl:834 otherwise. -/
def baseSimilarDims (alloc : Type → List I → M E U α B) :
    BaseContainer Tag A → Type → List I → M E U α B
  | .array a, t, dims => similar419 (fun dims => alloc t dims) a dims
  | .range r, t, dims => JuliaLean.base.abstractarray.similarFallback alloc r t dims
  | .other a, t, dims => JuliaLean.base.abstractarray.similarFallback alloc a t dims

/-- `similar(c, T, n::Int)` (abstractarray.jl:823 then 834, or array.jl:419), or the container's
own method. -/
def similarInt (alloc : Type → List I → M E U α B)
    (own : C → Type → SimilarArg R → UM E U V) :
    Container Tag A C → Type → I → M E U α (Sum B V)
  | .own c, t, n => Sum.inr <$> liftUser (own c t (.length (.bit .i64 n)))
  | .base c, t, n => Sum.inl <$> JuliaLean.base.abstractarray.similarTypeVarargs
      (fun c t dims => baseSimilarDims alloc c t dims) c t [n]

/-- `similar(c, T, len)` for a length of any Integer type (abstractarray.jl:823; `(len,)` is
`Dims` for an `Int`, otherwise abstractarray.jl:832 converts it with `to_shape`), or the
container's own method. -/
def similarLength (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → UM E U V) :
    Container Tag A C → Type → IntegerValue → M E U α (Sum (HeapArray Tag) V)
  | .own c, t, len => Sum.inr <$> liftUser (own c t (.length len))
  | .base c, t, len => Sum.inl <$> JuliaLean.base.abstractarray.similarTypeVarargs
      (fun c t (dims : List IntegerValue) => match dims with
        | [.bit .i64 n] => baseSimilarDims (allocUndef layout tag) c t [n]
        | dims => JuliaLean.base.abstractarray.similarLegacyOneTo
            (JuliaLean.base.abstractarray.toShapeMixed (toShapeIntegerValue ops))
            (baseSimilarDims (allocUndef layout tag)) c t dims) c t [len]

/-- `similar(c, T, axs)`: the empty tuple is `Dims` (834/419); a tuple of `OneTo`s goes through
abstractarray.jl:832 and `to_shape`; a tuple with another axis type has no Base method, so the
axis type's own `similar(c, T, axes)` method (`axisSimilar`) runs; a container with its own
`similar` runs that. -/
def similarAxes (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V) :
    Container Tag A C → Type → List (Axis R) → M E U α (Sum (HeapArray Tag) V)
  | .own c, t, axs => Sum.inr <$> liftUser (own c t (.axes axs))
  | .base c, t, axs => match oneTos axs with
    | some [] => Sum.inl <$> baseSimilarDims (allocUndef layout tag) c t []
    | some rs => Sum.inl <$> JuliaLean.base.abstractarray.similarLegacyOneTo
        (JuliaLean.base.abstractarray.toShapeMixed (toShapeAxis ops))
        (baseSimilarDims (allocUndef layout tag)) c t rs
    | none => Sum.inr <$> liftUser (axisSimilar c t axs)

/-- Dispatch of `_similar_for(c::AbstractArray, T, itr, isz, shp)` (array.jl:703-708). -/
def similarFor (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (tag : Type → Tag)
    (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (c : Container Tag A C) (t : Type) (itr : X) :
    IteratorSize → Shape R → M E U α (Sum (HeapArray Tag) V)
  | .sizeUnknown, .nothing _ => similarForUnknown (similarInt (allocUndef layout tag) own) c t itr
  | .hasLength, .length len => similarForLength (similarLength layout ops tag own) c t itr len
  | .hasShape _, .axes axs => similarForAxes (similarAxes layout ops tag own axisSimilar) c t itr axs
  | _, _ => fail (.base (.method "_similar_for"))
end models
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section expected
variable {E U α Tag R V : Type}

/-- A fresh array of element type `target` and dimensions `dims`, every slot unassigned, at the
next heap handle; every existing heap object is unchanged. Used only for zero elements, which
`Array{T,N}(undef, dims)` allocates for every element type. -/
def fresh (target : Tag) (dims : List Nat) : M E U α (HeapArray Tag) := do
  let w ← get
  set { w with heap := w.heap ++ [List.replicate dims.prod none] }
  pure ⟨w.heap.length, target, dims, dims.map (fun n => (1, n))⟩

/-- `Array{T,N}(undef, dims)` for `Int` dimensions: the installed array runtime allocator
(array.lean `heapAllocateIntDims`), whose size checks and errors are its own. -/
def allocInts (layout : Tag → Option MemoryLayout) (target : Tag) (dims : List Int) : M E U α (HeapArray Tag) :=
  liftHeap (heapAllocateIntDims layout target (dims.map (JInt.wrap .i64)))

/-- `Int(x)`: the equal `Int`, or `InexactError`. -/
def intValue (x : IntegerValue) : M E U α Int :=
  if IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max then pure x.val else fail (.base .inexact)

/-- An array with the given axes: `OneTo` axes give a fresh array whose dimensions are their
lengths; any other axis type gives what that type's own `similar` method returns. -/
def axesAllocation (layout : Tag → Option MemoryLayout) (target : Tag) (other : List (Axis R) → UM E U V) (axs : List (Axis R)) :
    M E U α (Sum (HeapArray Tag) V) :=
  match oneTos axs with
  | some rs => do Sum.inl <$> allocInts layout target (← rs.mapM (fun r => intValue r.stop))
  | none => Sum.inr <$> liftUser (other axs)
end expected
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)

/-! ## `array-collect-known-eltype` -/

/-- The destination of a sized collection: a Base array or a user-typed array. -/
inductive Collected (Tag V : Type) where
  | array (a : HeapArray Tag)
  | vector (handle : Nat)
  | user (v : V)

def Collected.ofSized {Tag V : Type} : Sum (HeapArray Tag) V → Collected Tag V
  | .inl a => .array a
  | .inr v => .user v

def Collected.ofUnknown {Tag V : Type} : Sum Nat V → Collected Tag V
  | .inl h => .vector h
  | .inr v => .user v

/-- The operations of a user-typed destination array `V` (from its type's own `similar`): its
`eachindex`, the iteration of that index collection, its `setindex!` (with its own conversion)
and its `push!`. -/
structure UserDest (E U V β K K' S' : Type) where
  eachindex : V → UM E U K'
  start : K' → UM E U (Option (K × S'))
  next : K' → S' → UM E U (Option (K × S'))
  setindex : V → K → β → UM E U Unit
  push : V → β → UM E U Unit
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section collectModels
variable {E U α Tag R V A C β St K K' S' : Type}

/-- `eachindex(dest)` for a Base array (abstractarray.jl:384, `IndexStyle(::Type{<:Array}) =
IndexLinear()`, abstractarray.jl:394 `unchecked_oneto(length(A))`, the length read from the
installed array runtime). -/
def heapEachindex (a : HeapArray Tag) : M E U α (OneTo I) := do
  let n ← liftHeap (heapLength (α := α) a.handle)
  liftArray (JuliaLean.base.abstractarray.eachindexArray
    (fun _ => .ok JuliaLean.base.indices.IndexStyle_Type_Array)
    (fun _ a => JuliaLean.base.abstractarray.eachindexDense (m := JuliaLean.base.abstractarray.Result)
      (fun _ => .ok n) JuliaLean.base.range.unchecked_oneto a) a)

/-- `setindex!(A::Array{T}, x, i::Int)` (array.jl, `x isa T ? x : convert(T, x)`) and
`_setindex!` (array.jl:1036) on the installed array runtime. -/
def heapSetindex (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (t : Type) (a : HeapArray Tag) (i : I) (x : β) : M E U α Unit := do
  let _ ← setindexScalar (fun x => isa x t) (asTyped t) (fun x => liftUser (convert t x))
    (setindexTyped (fun (a : HeapArray Tag) i => liftHeap (heapBounds (α := α) a.handle i))
      (fun (a : HeapArray Tag) i _ => liftHeap (heapReference (α := α) a.handle i))
      (fun ref x _ => liftHeap (heapSet ref.1 x ref.2))) a x i
  pure ()

/-- `copyto!(dest::AbstractArray, src)` (abstractarray.jl:941) into a Base array or a user-typed
array, with range.jl's `OneTo` iteration for the Base array's indices. -/
def copyInto (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (d : UserDest E U V β K K' S') (t : Type) :
    Sum (HeapArray Tag) V → FiniteIterator (UM E U) β St → M E U α (Sum (HeapArray Tag) V)
  | .inl a, it => Sum.inl <$> JuliaLean.base.abstractarray.copytoIterable (m := M E U α)
      heapEachindex
      (fun r => liftRange (JuliaLean.base.range.JIterate1.iterate r))
      (fun r st => liftRange (JuliaLean.base.range.JIterate2.iterate r st))
      (heapSetindex isa asTyped convert t) a it
  | .inr v, it => Sum.inr <$> JuliaLean.base.abstractarray.copytoIterable (m := M E U α)
      (fun v => liftUser (d.eachindex v)) (fun inds => liftUser (d.start inds))
      (fun inds s => liftUser (d.next inds s)) (fun v i x => liftUser (d.setindex v i x)) v it

/-- `Array{T,1}(undef, (n,))` for a growable vector (the installed `MutableMemory` allocator). -/
def allocVector (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (t : Type) : List I → M E U α Nat
  | [n] => liftMemory (mutableAllocate (α := α) (layout (tag t)) 0 n)
  | _ => fail (.base (.method "Array"))

/-- `push!(a, x)` (array.jl:1361, `x isa T ? x : convert(T, x)`, `_growend!`) on the installed
growable-vector runtime, or the user-typed destination's own `push!`. -/
def pushInto (layout : Tag → MemoryLayoutMetadata) (tag : Type → Tag) (isa : β → Type → Bool)
    (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (d : UserDest E U V β K K' S') (t : Type) : Sum Nat V → β → M E U α Unit
  | .inl h, x => do
    let ms := mutableStorage (layout (tag t))
    let _ ← JuliaLean.base.array.push (fun x => isa x t) (asTyped t) (fun x => liftUser (convert t x))
      (fun h y => liftMemory (push1361 (growend ms pure (growendInternal ms))
        mutableLength mutableSet h y)) h x
    pure ()
  | .inr v, x => liftUser (d.push v x)

/-- Dispatch of `_collect(cont, itr, IteratorEltype(itr), IteratorSize(itr))`: array.jl:777 and
780 for a known element type; `IsInfinite` has no method; an unknown element type goes to
array.jl:855/858 (`unknownEltype`, other entries). -/
def collectDispatch (layout : Tag → MemoryLayoutMetadata) (ops : BigIntegerOps) (tag : Type → Tag)
    (eltype : FiniteIterator (UM E U) β St → Type)
    (lengthQ : FiniteIterator (UM E U) β St → UM E U IntegerValue)
    (axesQ : FiniteIterator (UM E U) β St → UM E U (List (Axis R)))
    (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (d : UserDest E U V β K K' S')
    (unknownEltype : Container Tag A C → FiniteIterator (UM E U) β St → IteratorSize →
      M E U α (Collected Tag V))
    (cont : Container Tag A C) (it : FiniteIterator (UM E U) β St) :
    IteratorEltype → IteratorSize → M E U α (Collected Tag V)
  | .hasEltype, .sizeUnknown => Collected.ofUnknown <$> collectKnownUnknown eltype
      (fun c t => similarForUnknown (similarInt (allocVector layout tag) own) c t it)
      (fun a x => pushInto layout tag isa asTyped convert d (eltype it) a x) cont it
  | .hasEltype, .isInfinite => fail (.base (.method "_collect"))
  | .hasEltype, isz => Collected.ofSized <$> collectKnownSized eltype (shapeOf lengthQ axesQ)
      (similarFor layout ops tag own axisSimilar) (copyInto isa asTyped convert d (eltype it)) cont it isz
  | .eltypeUnknown, isz => unknownEltype cont it isz
end collectModels
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section collectExpected
variable {E U α Tag V β St K S' : Type}

/-- The `copyto!(dest, src)` docstring (abstractarray.jl:1043: "Copy all elements from collection
`src` to array `dest`, whose length must be greater than or equal to the length `n` of `src`. The
first `n` elements of `dest` are overwritten, the other elements are left untouched."): each
element of `src` goes, in order, to the next index of the destination, whose index iteration
`next` follows; an element with no index left throws the `ArgumentError`. -/
def fillRef (it : FiniteIterator (UM E U) β St) (next : S' → M E U α (Option (K × S')))
    (set : K → β → M E U α Unit) : Option (K × S') → β → (st : St) → M E U α Unit
  | none, _, _ =>
    fail (.array (.julia (.argumentError "destination has fewer elements than required")))
  | some (i, s), x, st => do
    set i x
    let y ← next s
    match ← liftUser (it.next st) with
    | none => pure ()
    | some (x', ⟨st', _⟩) => fillRef it next set y x' st'
termination_by _ _ st => it.rank st
decreasing_by
  all_goals
    try simp_wf
    assumption

/-- Store `y` in the slot of 0-based position `k` of the Base array with handle `h`. -/
def writeSlot (h k : Nat) (y : α) : M E U α Unit :=
  modify fun w => { w with heap := w.heap.set h ((w.heap[h]?.getD []).set k (some y)) }

/-- The element `setindex!` stores for `x`: `x` itself when `x isa T`, else the user
`convert(T, x)`. -/
def stored (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (t : Type) (x : β) : M E U α α :=
  if isa x t then pure (asTyped t x) else liftUser (convert t x)

/-- `copyto!` into a fresh Base array of `n = prod(dims)` slots: the k-th element, stored by
`setindex!`, fills slot k. -/
def heapFill (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (t : Type) (it : FiniteIterator (UM E U) β St) (a : HeapArray Tag) : M E U α Unit := do
  let n := a.dimensions.prod
  match ← liftUser it.first with
  | none => pure ()
  | some (x, st) =>
    fillRef it (fun k => pure (if k + 1 < n then some (k + 1, k + 1) else none))
      (fun k x => do writeSlot a.handle k (← stored isa asTyped convert t x))
      (if 0 < n then some (0, 0) else none) x st

/-- `copyto!` into a user-typed array, through its `eachindex`, index iteration and
`setindex!`. -/
def userFill {K' : Type} (d : UserDest E U V β K K' S') (it : FiniteIterator (UM E U) β St)
    (v : V) : M E U α Unit := do
  let inds ← liftUser (d.eachindex v)
  let y ← liftUser (d.start inds)
  match ← liftUser it.first with
  | none => pure ()
  | some (x, st) =>
    fillRef it (fun s => liftUser (d.next inds s)) (fun i x => liftUser (d.setindex v i x)) y x st

/-- The elements of `it`, in order, each run through `store` before the next `iterate`, as user
calls: what `for x in itr; push!(a, x); end` asks of user code. -/
def storedItems (it : FiniteIterator (UM E U) β St) (store : β → UM E U α) : UM E U (List α) := do
  match ← it.first with
  | none => pure []
  | some (x, st) => go x st []
where
  go (x : β) (st : St) (acc : List α) : UM E U (List α) := do
    let y ← store x
    match ← it.next st with
    | none => pure (acc ++ [y])
    | some (x', ⟨st', _⟩) => go x' st' (acc ++ [y])
  termination_by it.rank st
  decreasing_by
    all_goals
      try simp_wf
      assumption
end collectExpected
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect3

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)

/-- `collect(itr)` (array.jl:771, docstring at array.jl:719-770: "Return an `Array` of all items in
a collection or iterator. ... If the argument is array-like or is an iterator with the `HasShape`
trait, the result will have the same shape and number of dimensions as the argument"), and
`collect_similar(cont, itr)` (array.jl:775) with `_collect(cont, itr, ::HasEltype, isz)`
(array.jl:777, 780), for every iterator whose `IteratorEltype` is `HasEltype` (its `iterate`,
`length` and `axes` are any user calls, `eltype(itr)` any type), every element conversion, and,
for `collect_similar`, every AbstractArray container. `collect(itr)` uses the container `1:1`;
array arguments dispatch to `collect(::AbstractArray)` (array.jl:773) and are not iterators here.

* Sized (`HasLength`, `HasShape`): the shape query runs once; with a Base-`similar` container
  the destination is the installed runtime's `Array{eltype(itr),N}(undef, dims)` for the
  dimensions of the approved `multidimcov-array-v2-collect-alloc`, and the k-th element of `itr`, stored as
  `x isa T ? x : convert(T, x)`, is in slot k, the remaining slots unassigned; an element beyond
  the array's length throws `ArgumentError` after the earlier stores; iteration and conversion
  exceptions propagate after the earlier stores. A user-typed destination (the container's own
  `similar`, or an axis type's own `similar` for non-`OneTo` axes) receives the elements, in
  order, at the successive indices of its own `eachindex`.
* `SizeUnknown` (array.jl:780) is not covered here: its outcome depends on the growable-vector
  allocation limit, which the installed `mutableStorage.allocate` and `mutableAllocate` do not
  model (proposal R6dc2.2).
* `IsInfinite`: `MethodError`. -/
def KnownEltypeCollectSpec : Prop :=
  ∀ (E U α Tag R V A C β St K K' S' : Type) (ops : BigIntegerOps) (tag : Type → Tag)
    (layout : Tag → MemoryLayoutMetadata)
    (eltype : FiniteIterator (UM E U) β St → Type)
    (iteratorEltype : FiniteIterator (UM E U) β St → IteratorEltype)
    (iteratorSize : FiniteIterator (UM E U) β St → IteratorSize)
    (lengthQ : FiniteIterator (UM E U) β St → UM E U IntegerValue)
    (axesQ : FiniteIterator (UM E U) β St → UM E U (List (Axis R)))
    (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (d : UserDest E U V β K K' S')
    (unknownEltype : Container Tag A C → FiniteIterator (UM E U) β St → IteratorSize →
      M E U α (Collected Tag V))
    (it : FiniteIterator (UM E U) β St) (w : World U α),
    ops.Lawful → iteratorEltype it = .hasEltype →
    let t := eltype it
    let dispatch := collectDispatch layout ops tag eltype lengthQ axesQ own axisSimilar isa asTyped
      convert d unknownEltype
    let viaCollect := (JuliaLean.base.array.collect (m := M E U α)
      (Container.base (BaseContainer.range (A := A) ⟨one, one⟩))
      iteratorEltype iteratorSize dispatch it).run.run w
    let viaSimilar := fun cont : Container Tag A C =>
      (collectSimilar (m := M E U α) iteratorEltype iteratorSize dispatch cont it).run.run w
    let sizedExpected := fun (cont : Container Tag A C) (isz : IteratorSize) =>
      (match cont, isz with
        | .own c, .hasLength => do
          let v ← liftUser (own c t (.length (← liftUser (lengthQ it))))
          userFill d it v
          pure (Collected.user v)
        | .own c, .hasShape _ => do
          let v ← liftUser (own c t (.axes (← liftUser (axesQ it))))
          userFill d it v
          pure (Collected.user v)
        | .base _, .hasLength => do
          let a ← allocInts layout (tag t) [← intValue (← liftUser (lengthQ it))]
          heapFill isa asTyped convert t it a
          pure (Collected.array a)
        | .base c, .hasShape _ => do
          match ← axesAllocation layout (tag t) (axisSimilar c t) (← liftUser (axesQ it)) with
          | .inl a =>
            heapFill isa asTyped convert t it a
            pure (Collected.array a)
          | .inr v =>
            userFill d it v
            pure (Collected.user v)
        | _, _ => fail (.base (.method "_collect")) : M E U α (Collected Tag V)).run.run w
    (∀ isz, isz = .hasLength ∨ (∃ n, isz = .hasShape n) → iteratorSize it = isz →
      viaCollect = sizedExpected (.base (.range ⟨one, one⟩)) isz ∧
      ∀ cont, viaSimilar cont = sizedExpected cont isz) ∧
    (iteratorSize it = .isInfinite →
      viaCollect = (fail (.base (.method "_collect")) : M E U α (Collected Tag V)).run.run w ∧
      ∀ cont, viaSimilar cont =
        (fail (.base (.method "_collect")) : M E U α (Collected Tag V)).run.run w)
end JuliaLean.Proofs.base.array.round6dcollect3
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
variable {α : Type}

/-- A `for x in xs` loop of steps that each follow a per-element plan, threading an invariant:
the loop follows the plans in sequence (`List.foldlM`), failing with the first plan error. -/
theorem forIn_follows {β π : Type} (step : β → MutationM α Unit)
    (planStep : π → β → Except Error π) (Inv : MutableMemory α → π → List β → Prop)
    (hstep : ∀ st g done x, Inv st g done →
      (∀ e, planStep g x = .error e → ((step x).run st).1 = .error e) ∧
      (∀ g', planStep g x = .ok g' → ∃ st', (step x).run st = (.ok (), st') ∧
        Inv st' g' (done ++ [x]))) :
    ∀ (xs : List β) (st : MutableMemory α) (g : π) (done : List β), Inv st g done →
      (∀ e, xs.foldlM planStep g = .error e →
        ((forIn xs PUnit.unit (fun x (_ : PUnit) => (do
          step x
          pure (ForInStep.yield PUnit.unit) : MutationM α (ForInStep PUnit)))).run st).1 = .error e) ∧
      (∀ g', xs.foldlM planStep g = .ok g' → ∃ st',
        (forIn xs PUnit.unit (fun x (_ : PUnit) => (do
          step x
          pure (ForInStep.yield PUnit.unit) : MutationM α (ForInStep PUnit)))).run st =
          (.ok PUnit.unit, st') ∧ Inv st' g' (done ++ xs)) := by
  intro xs
  induction xs with
  | nil =>
    intro st g done hinv
    refine ⟨fun e he => (by cases he), fun g' hg' => ?_⟩
    cases hg'
    exact ⟨st, rfl, by simpa using hinv⟩
  | cons x xs ih =>
    intro st g done hinv
    obtain ⟨herr, hok⟩ := hstep st g done x hinv
    refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
    · simp only [List.foldlM_cons] at he
      cases hp : planStep g x with
      | error e' =>
        rw [hp] at he
        cases he
        have h1 := herr _ hp
        simp only [List.forIn_cons, stateExcept_bind]
        cases hr : (step x).run st with
        | mk r st1 =>
          rw [hr] at h1
          simp only at h1
          subst h1
          rfl
      | ok g1 =>
        rw [hp] at he
        obtain ⟨st1, hr, hinv1⟩ := hok g1 hp
        have := (ih st1 g1 (done ++ [x]) hinv1).1 e he
        simp only [List.forIn_cons, stateExcept_bind, hr, stateExcept_pure]
        exact this
    · simp only [List.foldlM_cons] at hg'
      cases hp : planStep g x with
      | error e' =>
        rw [hp] at hg'
        cases hg'
      | ok g1 =>
        rw [hp] at hg'
        obtain ⟨st1, hr, hinv1⟩ := hok g1 hp
        obtain ⟨st2, hr2, hinv2⟩ := (ih st1 g1 (done ++ [x]) hinv1).2 g' hg'
        refine ⟨st2, ?_, by simpa using hinv2⟩
        simp only [List.forIn_cons, stateExcept_bind, hr, stateExcept_pure]
        exact hr2
end
end opusGrowth
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
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {α : Type}

theorem mapM_snoc_ok {β γ : Type} (f : β → Except Error γ) (x : β) (y : γ) (hx : f x = .ok y) :
    ∀ (done : List β) (ys : List γ), done.mapM f = .ok ys → (done ++ [x]).mapM f = .ok (ys ++ [y])
  | [], ys, h => by
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [List.mapM_cons, hx, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | d :: ds, ys, h => by
    rw [List.mapM_cons] at h
    cases hd : f d with
    | error e => simp [hd, Bind.bind, Except.bind] at h
    | ok z =>
      cases hds : ds.mapM f with
      | error e => simp [hd, hds, Bind.bind, Except.bind] at h
      | ok zs =>
        simp only [hd, hds, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.ok.injEq] at h
        subst h
        rw [List.cons_append, List.mapM_cons, mapM_snoc_ok f x y hx ds zs hds]
        simp [hd, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem mapM_except_ok {β : Type} : ∀ xs : List β, xs.mapM (fun x => (Except.ok x : Except Error β)) = .ok xs
  | [] => rfl
  | x :: xs => by
    rw [List.mapM_cons, mapM_except_ok xs]
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem pushesPlan_foldlM (l : MemoryLayout) {β : Type} :
    ∀ (xs : List β) (g : VectorGeometry), pushesPlan l g xs.length =
      xs.foldlM (fun g x => (Except.ok x : Except Error β).bind fun _ => growendPlan l g 1) g
  | [], _ => rfl
  | x :: xs, g => by
    simp only [List.length_cons, pushesPlan, List.foldlM_cons]
    rcases hp : growendPlan l g 1 with e | g'
    · rfl
    · exact pushesPlan_foldlM l xs g'

theorem convertPushPlan_foldlM (l : MemoryLayout) {β : Type} (conv : β → Except Error α) :
    ∀ (xs : List β) (g : VectorGeometry), convertPushPlan l conv g xs =
      xs.foldlM (fun g x => (conv x).bind fun _ => growendPlan l g 1) g
  | [], _ => rfl
  | x :: xs, g => by
    simp only [convertPushPlan, List.foldlM_cons]
    rcases hc : conv x with e | y
    · rfl
    · rcases hp : growendPlan l g 1 with e | g'
      · rfl
      · exact convertPushPlan_foldlM l conv xs g'

/-- The invariant of `_collect(T, itr, ::SizeUnknown)`: vector `H` is valid with geometry `g`
and holds the converted values pushed so far. -/
def CollectInv {β : Type} (H : Nat) (conv : β → Except Error α) (st : MutableMemory α)
    (g : VectorGeometry) (done : List β) : Prop :=
  ∃ mem off n slots, VecAt st H mem off n slots ∧ g = ⟨slots.length, off.val.toNat, n.val.toNat⟩ ∧
    ∃ ys, done.mapM conv = .ok ys ∧ vwWindow slots off n = ys.map some

/-- One step of the collecting loop, whose push of `x` converts it by `conv` and then follows the
`push!` growth plan. -/
def CollectStep {β : Type} (l : MemoryLayout) (conv : β → Except Error α)
    (step : Nat → β → MutationM α Unit) : Prop :=
  ∀ H st g done x, CollectInv H conv st g done →
    (∀ e, (conv x).bind (fun _ => growendPlan l g 1) = .error e → ((step H x).run st).1 = .error e) ∧
    (∀ g', (conv x).bind (fun _ => growendPlan l g 1) = .ok g' →
      ∃ st', (step H x).run st = (.ok (), st') ∧ CollectInv H conv st' g' (done ++ [x]))

theorem push1361_collectStep (l : DictLayout) {β : Type} (conv : β → Except Error α)
    (pushValue : Nat → β → MutationM α Unit)
    (hpush : ∀ H st x,
      (∀ e, conv x = .error e → (pushValue H x).run st = (.error e, st)) ∧
      (∀ y, conv x = .ok y → (pushValue H x).run st =
        (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
          (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) mutableLength mutableSet H y >>=
          fun _ => (pure () : MutationM α Unit)).run st)) :
    CollectStep l conv pushValue := by
  intro H st g done x hinv
  obtain ⟨mem, off, n, slots, h, rfl, ys, hys, hw⟩ := hinv
  cases hc : conv x with
  | error e =>
    refine ⟨fun e' he => ?_, fun g' hg' => ?_⟩
    · rw [(hpush H st x).1 e hc]
      simpa [Except.bind] using he
    · simp [Except.bind] at hg'
  | ok y =>
    have hpv := (hpush H st x).2 y hc
    obtain ⟨herr, hok⟩ := push_plan l h y
    refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
    · simp only [Except.bind] at he
      simp only [hpv, stateExcept_bind, herr e he]
    · simp only [Except.bind] at hg'
      obtain ⟨next, mem', off', slots', hrun, hv, _, _, hwin, hgeo, _⟩ := hok g' hg'
      refine ⟨next, ?_, mem', off', _, slots', hv, ?_, ys ++ [y], mapM_snoc_ok conv x y hc done ys hys, ?_⟩
      · simp only [hpv, stateExcept_bind, hrun, stateExcept_pure]
      · rw [← hgeo, VecAt.geometry hv]
      · rw [hwin, hw]; simp

theorem bind_run_error {β γ : Type} (action : MutationM α β) (next : β → MutationM α γ)
    (s : MutableMemory α) (e : Error) (h : (action.run s).1 = .error e) :
    ((action >>= next).run s).1 = .error e := by
  rw [stateExcept_bind]
  rcases hr : action.run s with ⟨r, st⟩
  rw [hr] at h
  simp only at h
  subst h
  rfl

/-- `_collect(T, itr, ::SizeUnknown)` (array.jl:701-709): `Vector{T}()` followed by one push per
element follows the per-element plans in sequence. -/
theorem collectUnknown_follows (l : MemoryLayout) {β : Type} (conv : β → Except Error α)
    (step : Nat → β → MutationM α Unit) (hstep : CollectStep l conv step)
    (xs : List β) (s : MutableMemory α) :
    FollowsSteps (xs.foldlM (fun g x => (conv x).bind fun _ => growendPlan l g 1) emptyGeometry)
      ((collectUnknown (mutableAllocate (some l) 0 zero) step xs).run s)
      (fun r next => ∃ ys, xs.mapM conv = .ok ys ∧ r = s.arrays.length ∧
        next.contents s.arrays.length = ys.map some ∧ next.validVector s.arrays.length) := by
  have hdef : (collectUnknown (mutableAllocate (some l) 0 zero) step xs).run s =
      ((do
        let a ← mutableAllocate (some l) 0 zero
        forIn xs PUnit.unit (fun x (_ : PUnit) => (do
          step a x
          pure (ForInStep.yield PUnit.unit) : MutationM α (ForInStep PUnit)))
        pure a : MutationM α Nat)).run s := rfl
  rw [hdef, stateExcept_bind, mutableAllocate_zero_run]
  simp only
  have h1 : VecAt ({ memories := s.memories ++ [[]], arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩] } : MutableMemory α) s.arrays.length s.memories.length one zero [] := by
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
  have hinv : CollectInv s.arrays.length conv ({ memories := s.memories ++ [[]], arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩] } : MutableMemory α) emptyGeometry [] :=
    ⟨_, _, _, _, h1, by rw [ival_one, ival_zero]; rfl, [], rfl, by simp [vwWindow]⟩
  have hloop := forIn_follows (step s.arrays.length)
    (fun g x => (conv x).bind fun _ => growendPlan l g 1)
    (fun st g done => CollectInv s.arrays.length conv st g done)
    (fun st g done x hi => hstep s.arrays.length st g done x hi) xs ({ memories := s.memories ++ [[]], arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩] } : MutableMemory α) emptyGeometry [] hinv
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · exact bind_run_error _ _ _ _ (hloop.1 e he)
  · obtain ⟨st', hr, mem, off, n, slots, hv, _, ys, hys, hw⟩ := hloop.2 g' hg'
    rw [List.nil_append] at hys
    refine ⟨s.arrays.length, st', ?_, ys, hys, rfl, ?_, hv.valid⟩
    · simp only [stateExcept_bind, hr, stateExcept_pure]
    · rw [hv.contents, hw]

theorem unknownTypedCollectionSpec : UnknownTypedCollectionSpec := by
  intro α l xs s
  dsimp only
  have hstep : CollectStep l (fun x => (Except.ok x : Except Error α)) (mutablePush (MemoryLayoutMetadata.ofRuntime l)) :=
    push1361_collectStep l _ _ (fun H st x => ⟨fun e he => (by cases he), fun y hy => (by
      cases hy; rfl)⟩)
  have := collectUnknown_follows l _ _ hstep xs s
  rw [pushesPlan_foldlM]
  refine ⟨this.1, fun g hg => ?_⟩
  obtain ⟨r, next, hrun, ys, hys, hr, hc, hv⟩ := this.2 g hg
  obtain rfl : xs = ys := Except.ok.inj ((mapM_except_ok xs).symm.trans hys)
  exact ⟨r, next, hrun, hr, hc, hv⟩

theorem collectingPush_hpush (l : DictLayout) {β : Type} (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (conv : β → Except Error α)
    (hconv : ∀ x, elementConversion already asTyped convert x = conv x) (H : Nat)
    (st : MutableMemory α) (x : β) :
    (∀ e, conv x = .error e → (collectingPush (MemoryLayoutMetadata.ofRuntime l) already asTyped convert H x).run st =
      (.error e, st)) ∧
    (∀ y, conv x = .ok y → (collectingPush (MemoryLayoutMetadata.ofRuntime l) already asTyped convert H x).run st =
      (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
          (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) mutableLength mutableSet H y >>=
          fun _ => (pure () : MutationM α Unit)).run st) := by
  refine ⟨fun e he => ?_, fun y hy => ?_⟩
  · have hv : (if already x then .ok (asTyped x) else convert x) = .error e := by
      have hc := hconv x
      unfold elementConversion at hc
      rw [hc]; exact he
    simp only [collectingPush, stateExcept_bind,
      (push_value_error already asTyped convert _ st H x e hv).1]
  · have hv : (if already x then .ok (asTyped x) else convert x) = .ok y := by
      have hc := hconv x
      unfold elementConversion at hc
      rw [hc]; exact hy
    simp only [collectingPush, stateExcept_bind,
      (push_value_ok already asTyped convert _ st H x y hv).1]

theorem unknownCollectionSpec : UnknownCollectionSpec := by
  intro α β l already asTyped convert xs s
  dsimp only
  have hstep := push1361_collectStep l (elementConversion already asTyped convert)
    (collectingPush (MemoryLayoutMetadata.ofRuntime l) already asTyped convert)
    (fun H st x => collectingPush_hpush l already asTyped convert _ (fun _ => rfl) H st x)
  rw [convertPushPlan_foldlM]
  exact collectUnknown_follows l _ _ hstep xs s

theorem unknownIntegerCollectionSpec : UnknownIntegerCollectionSpec := by
  intro T S xs s
  dsimp only
  have hstep := push1361_collectStep (bitIntegerRuntimeLayout T)
    (fun x : JInt S => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))
    (collectingPush (MemoryLayoutMetadata.ofRuntime (bitIntegerRuntimeLayout T)) (fun _ => false)
      (fun x : JInt S => JInt.wrap T x.val)
      (fun x : JInt S => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)))
    (fun H st x => collectingPush_hpush (bitIntegerRuntimeLayout T) (fun _ => false)
      (fun x : JInt S => JInt.wrap T x.val)
      (fun x : JInt S => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))
      (fun x : JInt S => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))
      (fun _ => rfl) H st x)
  have := collectUnknown_follows _ _ _ hstep xs s
  rw [convertPushPlan_foldlM]
  refine ⟨this.1, fun g hg => ?_⟩
  obtain ⟨r, next, hrun, ys, hys, hr, hc, hv⟩ := this.2 g hg
  by_cases hfit : ∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max
  · obtain rfl := Except.ok.inj ((bitinteger_array_mapM_success T xs hfit).symm.trans hys)
    refine ⟨r, next, hrun, hfit, hr, ?_, hv⟩
    rw [hc, List.map_map]
    rfl
  · have hbad : ∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max) :=
      Classical.byContradiction fun hno =>
        hfit fun x hx => Classical.byContradiction fun hn => hno ⟨x, hx, hn⟩
    have := (bitinteger_array_mapM_failure T xs hbad).symm.trans hys
    cases this

theorem completeUnknownCollectionSpec : CompleteUnknownCollectionSpec :=
  ⟨unknownTypedCollectionSpec, unknownCollectionSpec, unknownIntegerCollectionSpec⟩
end
end opusGrowth
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
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.Proofs.base.array.round6dcollect3
section
variable {E U α β St : Type}

theorem m_bind_run {γ δ : Type} (x : M E U α γ) (f : γ → M E U α δ) (w : World U α) :
    (x >>= f).run.run w = match x.run.run w with
      | (.ok a, w') => (f a).run.run w'
      | (.error e, w') => (.error e, w') := by
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases h : x.run.run w with ⟨r, w'⟩
  cases r <;> simp [h, ExceptT.bindCont] <;> rfl

theorem m_pure_run {γ : Type} (a : γ) (w : World U α) :
    (pure a : M E U α γ).run.run w = (.ok a, w) := rfl

theorem m_fail_run {γ : Type} (f : Fault E) (w : World U α) :
    (fail f : M E U α γ).run.run w = (.error f, w) := rfl

theorem liftUser_run {γ : Type} (x : UM E U γ) (w : World U α) :
    (liftUser x : M E U α γ).run.run w =
      match (x.run.run w.user) with
      | (.ok b, u) => (.ok b, { w with user := u })
      | (.error e, u) => (.error (.user e), { w with user := u }) := by
  simp only [liftUser, m_bind_run]
  show (match (Id.run (x.run.run w.user)) with
    | (r, u) => (set { w with user := u } >>= fun _ => match r with
      | .ok b => pure b
      | .error e => fail (.user e) : M E U α γ)).run.run w = _
  rcases h : x.run.run w.user with ⟨r, u⟩
  cases r <;> rfl

/-- One step of two runs agrees: both fail with the same error and world, or both succeed in the
same world with related results satisfying the invariant. -/
def StepAgree {γ1 γ2 : Type} (Rel : γ1 → γ2 → Prop) (P : World U α → Prop) :
    Except (Fault E) γ1 × World U α → Except (Fault E) γ2 × World U α → Prop
  | (.ok y1, w1), (.ok y2, w2) => w1 = w2 ∧ Rel y1 y2 ∧ P w1
  | (.error e1, w1), (.error e2, w2) => e1 = e2 ∧ w1 = w2
  | _, _ => False

/-- The `for x in itr` loop of `copyto!(dest, src)` over a destination index iteration, simulated by
`fillRef` with another index iteration related by `Rel`, under a world invariant `P` that user
calls preserve. -/
theorem copyLoop_sim {I1 S1 K S2 γ : Type} (it : FiniteIterator (UM E U) β St)
    (setM : I1 → β → M E U α Unit) (nextM : S1 → M E U α (Option (I1 × S1)))
    (setE : K → β → M E U α Unit) (nextE : S2 → M E U α (Option (K × S2)))
    (Rel : Option (I1 × S1) → Option (K × S2) → Prop) (P : World U α → Prop)
    (hnone : ∀ y1 y2, Rel y1 y2 → (y1 = none ↔ y2 = none))
    (huser : ∀ w u, P w → P { w with user := u })
    (hset : ∀ i s k s2 x w, P w → Rel (some (i, s)) (some (k, s2)) →
      (setM i x).run.run w = (setE k x).run.run w ∧
      ∀ w', (setM i x).run.run w = (.ok (), w') → P w')
    (hnext : ∀ i s k s2 w, P w → Rel (some (i, s)) (some (k, s2)) →
      StepAgree Rel P ((nextM s).run.run w) ((nextE s2).run.run w))
    (c : γ) :
    ∀ (n : Nat) (st : St), it.rank st = n → ∀ (x : β) (y1 : Option (I1 × S1)) (y2 : Option (K × S2))
      (w : World U α), P w → Rel y1 y2 →
      (do let _ ← iterFrom it (fun x (y : Option (I1 × S1)) => match y with
          | none => do
            throw (JuliaLean.base.abstractarray.ArrayError.julia
              (JlError.argumentError "destination has fewer elements than required"))
            pure (ForInStep.yield y)
          | some (i, st) => do
            setM i x
            let y ← nextM st
            pure (ForInStep.yield y)) x st y1
          pure c : M E U α γ).run.run w =
      (do fillRef it nextE setE y2 x st; pure c : M E U α γ).run.run w := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih st hst x y1 y2 w hP hR
  rw [iterFrom.eq_1]
  cases y2 with
  | none =>
    have := (hnone _ _ hR).mpr rfl
    subst this
    rw [fillRef.eq_1]
    rfl
  | some p2 =>
    obtain ⟨k, s2⟩ := p2
    cases y1 with
    | none => exact absurd ((hnone _ _ hR).mp rfl) (by simp)
    | some p1 =>
      obtain ⟨i, s⟩ := p1
      rw [fillRef.eq_2]
      obtain ⟨hs, hsP⟩ := hset i s k s2 x w hP hR
      simp only [bind_assoc, m_bind_run, hs]
      rcases hse : (setE k x).run.run w with ⟨r, w1⟩
      cases r with
      | error e => rfl
      | ok u =>
        have hP1 := hsP w1 (by rw [hs, hse])
        simp only []
        have hn := hnext i s k s2 w1 hP1 hR
        rcases hm : (nextM s).run.run w1 with ⟨r1, w2⟩
        rcases he : (nextE s2).run.run w1 with ⟨r2, w3⟩
        rw [hm, he] at hn
        cases r1 with
        | error e1 =>
          cases r2 with
          | error e2 => obtain ⟨rfl, rfl⟩ := hn; rfl
          | ok _ => exact (hn : False).elim
        | ok z1 =>
          cases r2 with
          | error _ => exact (hn : False).elim
          | ok z2 =>
            obtain ⟨rfl, hR2, hP2⟩ := hn
            simp only [m_pure_run, m_bind_run, liftUser_run]
            cases hi' : (it.next st).run.run w2.user with
            | mk r3 u3 =>
              cases r3 with
              | error e3 => rfl
              | ok o =>
                cases o with
                | none => rfl
                | some q =>
                  obtain ⟨x', st', hlt⟩ := q
                  have := ih _ (hst ▸ hlt) st' rfl x' z1 z2 { w2 with user := u3 } (huser w2 u3 hP2) hR2
                  simp only [m_bind_run] at this
                  exact this


theorem forIn_iter_eq {σ : Type} (it : FiniteIterator (UM E U) β St) (init : σ)
    (f : β → σ → M E U α (ForInStep σ)) :
    (forIn it init f : M E U α σ) = (do
      match ← liftUser it.first with
      | none => pure init
      | some (x, st) => iterFrom it f x st init) := rfl

/-- `copyto!` into a user-typed destination is `userFill`. -/
theorem copyUser_run {V K K' S' : Type} (d : UserDest E U V β K K' S') (v : V)
    (it : FiniteIterator (UM E U) β St) (w : World U α) :
    (JuliaLean.base.abstractarray.copytoIterable (m := M E U α)
      (fun v => liftUser (d.eachindex v)) (fun inds => liftUser (d.start inds))
      (fun inds s => liftUser (d.next inds s)) (fun v i x => liftUser (d.setindex v i x)) v it).run.run w =
      (do userFill d it v; pure v : M E U α V).run.run w := by
  unfold JuliaLean.base.abstractarray.copytoIterable userFill
  simp only [forIn_iter_eq, bind_assoc, m_bind_run]
  rcases h1 : (liftUser (d.eachindex v) : M E U α K').run.run w with ⟨r1, w1⟩
  cases r1 with
  | error e => rfl
  | ok inds =>
    simp only []
    rcases h2 : (liftUser (d.start inds) : M E U α (Option (K × S'))).run.run w1 with ⟨r2, w2⟩
    cases r2 with
    | error e => rfl
    | ok y =>
      simp only []
      rcases h3 : (liftUser it.first : M E U α (Option (β × St))).run.run w2 with ⟨r3, w3⟩
      cases r3 with
      | error e => rfl
      | ok o =>
        cases o with
        | none => rfl
        | some p =>
          obtain ⟨x, st⟩ := p
          simp only []
          have := copyLoop_sim it (fun i x => liftUser (d.setindex v i x))
            (fun s => liftUser (d.next inds s)) (fun i x => liftUser (d.setindex v i x))
            (fun s => liftUser (d.next inds s)) (fun a b => a = b) (fun _ => True)
            (fun y1 y2 h => by subst h; exact Iff.rfl) (fun _ _ _ => trivial)
            (fun i s k s2 x w _ hR => by
              cases hR; exact ⟨rfl, fun _ _ => trivial⟩)
            (fun i s k s2 w _ hR => by
              cases hR
              rcases (liftUser (d.next inds s) : M E U α (Option (K × S'))).run.run w with ⟨r, w'⟩
              cases r <;> simp [StepAgree])
            v (it.rank st) st rfl x y y w3 trivial rfl
          simp only [m_bind_run] at this
          exact this


theorem liftHeap_run {γ : Type} (x : VectorM α γ) (w : World U α) :
    (liftHeap x : M E U α γ).run.run w = match x.run w.heap with
      | .ok (b, h) => (.ok b, { w with heap := h })
      | .error e => (.error (.base e), w) := by
  unfold liftHeap
  simp only [m_bind_run]
  show (match x.run w.heap with
    | .ok (b, h) => (set { w with heap := h } >>= fun _ => pure b : M E U α γ)
    | .error e => fail (.base e)).run.run w = _
  rcases h : x.run w.heap with _ | ⟨b, h'⟩ <;> rfl

theorem heapEachindex_run {Tag : Type} (a : HeapArray Tag) (w : World U α)
    (sl : List (Option α)) (hs : w.heap[a.handle]? = some sl) :
    (heapEachindex (E := E) (U := U) a).run.run w =
      (.ok (JuliaLean.base.range.unchecked_oneto (JInt.wrap .i64 (sl.length : Int))), w) := by
  unfold heapEachindex
  simp only [m_bind_run, liftHeap_run, heapLength_run, hs]
  rfl

theorem writeSlot_run (h k : Nat) (y : α) (w : World U α) :
    (writeSlot (E := E) h k y).run.run w =
      (.ok (), { w with heap := w.heap.set h ((w.heap[h]?.getD []).set k (some y)) }) := rfl

/-- The store of `setindex!` on a Base array, after the element conversion. -/
theorem heapStore_run {Tag : Type} (a : HeapArray Tag) (i : I) (y : α) (w : World U α)
    (sl : List (Option α)) (hs : w.heap[a.handle]? = some sl) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ (sl.length : Int)) :
    (setindexTyped (m := M E U α) (fun (a : HeapArray Tag) i => liftHeap (heapBounds (α := α) a.handle i))
      (fun (a : HeapArray Tag) i _ => liftHeap (heapReference (α := α) a.handle i))
      (fun ref x _ => liftHeap (heapSet ref.1 x ref.2)) a y i).run.run w =
      (.ok a, { w with heap := w.heap.set a.handle (sl.set (i.val - 1).toNat (some y)) }) := by
  unfold setindexTyped
  simp only [m_bind_run, liftHeap_run, heapBounds_run, hs, h1, h2, and_self, ite_true]
  have hset := heapSet_run w.heap a.handle sl hs i h1 h2 y
  simp only [heapReference, vector_pure_run]
  rw [hset]
  rfl

theorem heapSetindex_run {Tag : Type} (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (t : Type) (a : HeapArray Tag) (i : I) (x : β) (w : World U α)
    (sl : List (Option α)) (hs : w.heap[a.handle]? = some sl) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ (sl.length : Int)) :
    (heapSetindex isa asTyped convert t a i x).run.run w =
      (do writeSlot a.handle (i.val - 1).toNat (← stored isa asTyped convert t x) : M E U α Unit).run.run w := by
  unfold heapSetindex setindexScalar stored
  cases hisa : isa x t
  · simp only [hisa, Bool.false_eq_true, ite_false, m_bind_run]
    rcases hc : (liftUser (convert t x) : M E U α α).run.run w with ⟨r, w1⟩
    cases r with
    | error e => rfl
    | ok y =>
      have hheap : w1.heap = w.heap := by
        rw [liftUser_run] at hc
        revert hc
        rcases (convert t x).run.run w.user with ⟨r', u⟩
        cases r' <;> intro hc <;> cases hc <;> rfl
      have hs1 : w1.heap[a.handle]? = some sl := by rw [hheap]; exact hs
      simp only []
      rw [heapStore_run a i y w1 sl hs1 h1 h2, writeSlot_run, hs1]
      rfl
  · simp only [hisa, ite_true, pure_bind, m_bind_run]
    rw [heapStore_run a i _ w sl hs h1 h2, writeSlot_run, hs]
    rfl


theorem iterate1_oneTo_eq (r : OneTo I) :
    JuliaLean.base.range.JIterate1.iterate r =
      .ok (if r.stop.val < 1 then none else some (JuliaLean.base.range.JOneunit.oneunit,
        JuliaLean.base.range.JOneunit.oneunit)) := by
  show JuliaLean.base.range.iterate_OrdinalRange r = _
  unfold JuliaLean.base.range.iterate_OrdinalRange
  rw [JuliaLean.Proofs.base.range.isempty_oneTo]
  by_cases h : r.stop.val < 1
  · simp [h, bind, Except.bind, pure, Except.pure]
  · simp [h, bind, Except.bind, pure, Except.pure, JuliaLean.Proofs.base.range.first_oneTo]

theorem stored_heap (isa : β → Type → Bool) (asTyped : Type → β → α) (convert : Type → β → UM E U α)
    (t : Type) (x : β) (w : World U α) :
    ((stored (E := E) isa asTyped convert t x).run.run w).2.heap = w.heap := by
  unfold stored
  split
  · rfl
  · rw [liftUser_run]
    rcases (convert t x).run.run w.user with ⟨r, u⟩
    cases r <;> rfl

def baseRel (n : Nat) : Option (I × I) → Option (Nat × Nat) → Prop
  | none, none => True
  | some (i, s), some (k, s2) => i.val = k + 1 ∧ s = i ∧ s2 = k ∧ k < n
  | _, _ => False

def baseInv {Tag : Type} (a : HeapArray Tag) (n : Nat) (w : World U α) : Prop :=
  ∃ sl : List (Option α), w.heap[a.handle]? = some sl ∧ sl.length = n

theorem baseRel_none (n : Nat) (y1 : Option (I × I)) (y2 : Option (Nat × Nat))
    (h : baseRel n y1 y2) : y1 = none ↔ y2 = none := by
  cases y1 with
  | none => cases y2 with
    | none => simp
    | some q => cases h
  | some q1 => cases y2 with
    | none => obtain ⟨_, _⟩ := q1; cases h
    | some q2 => simp

theorem baseRel_start (n : Nat) :
    baseRel n (if (n : Int) < 1 then none else some (JuliaLean.base.range.JOneunit.oneunit,
      JuliaLean.base.range.JOneunit.oneunit)) (if 0 < n then some (0, 0) else none) := by
  by_cases h0 : 0 < n
  · rw [if_neg (by omega), if_pos h0]
    refine ⟨?_, rfl, rfl, h0⟩
    rw [JuliaLean.Proofs.base.range.oneunit_iv]; rfl
  · rw [if_pos (by omega), if_neg h0]
    trivial

theorem baseSet {Tag : Type} (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (t : Type) (a : HeapArray Tag) (n : Nat)
    (i s : I) (k s2 : Nat) (x : β) (w : World U α) (hP : baseInv a n w)
    (hR : baseRel n (some (i, s)) (some (k, s2))) :
    (heapSetindex isa asTyped convert t a i x).run.run w =
      (do writeSlot a.handle k (← stored isa asTyped convert t x) : M E U α Unit).run.run w ∧
    ∀ w', (heapSetindex isa asTyped convert t a i x).run.run w = (.ok (), w') →
      baseInv a n w' := by
  obtain ⟨sl', hs', hl'⟩ := hP
  obtain ⟨hik, -, -, hk⟩ := hR
  have hk' : (i.val - 1).toNat = k := by omega
  rw [heapSetindex_run isa asTyped convert t a i x w sl' hs' (by omega) (by omega), hk']
  refine ⟨rfl, ?_⟩
  intro w' hw'
  rw [m_bind_run] at hw'
  have hh := stored_heap isa asTyped convert t x w (E := E)
  revert hw' hh
  rcases (stored (E := E) isa asTyped convert t x).run.run w with ⟨r1, w1⟩
  cases r1 with
  | error e => intro hw' _; cases hw'
  | ok y =>
    intro hw' hh
    dsimp only at hw'
    rw [writeSlot_run] at hw'
    cases hw'
    refine ⟨sl'.set k (some y), ?_, by simp [hl']⟩
    show (w1.heap.set a.handle _)[a.handle]? = _
    rw [hh, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hs').1, hs']
    rfl

theorem baseNext {Tag : Type} (a : HeapArray Tag) (n : Nat) (r : OneTo I)
    (hstop : r.stop.val = (n : Int)) (i s : I) (k s2 : Nat) (w : World U α)
    (hP : baseInv a n w) (hR : baseRel n (some (i, s)) (some (k, s2))) :
    StepAgree (baseRel n) (baseInv a n)
      ((liftRange (JuliaLean.base.range.JIterate2.iterate r s) : M E U α _).run.run w)
      ((pure (if s2 + 1 < n then some (s2 + 1, s2 + 1) else none) : M E U α _).run.run w) := by
  obtain ⟨hik, hs, hs2, hk⟩ := hR
  subst hs hs2
  by_cases hlt : s2 + 1 < n
  · obtain ⟨j, hj, hjv⟩ := JuliaLean.Proofs.base.range.iterate2_oneTo r s (by rw [hstop]; omega)
    simp only [liftRange, hj, m_pure_run, hlt, ite_true, StepAgree]
    exact ⟨trivial, ⟨by rw [hjv, hik]; omega, rfl, rfl, hlt⟩, hP⟩
  · rw [JuliaLean.Proofs.base.range.iterate2_oneTo_last r s (by rw [hstop]; omega)]
    simp only [liftRange, m_pure_run, hlt, ite_false, StepAgree]
    exact ⟨trivial, trivial, hP⟩

/-- `copyto!` through any destination interface whose `eachindex` and `start` do not touch the
world, simulated by a per-step plan (`copyLoop_sim`). -/
theorem copyGeneric_run {D Inds I1 S1 K S2 : Type}
    (eachindexF : D → M E U α Inds) (startF : Inds → M E U α (Option (I1 × S1)))
    (nextF : Inds → S1 → M E U α (Option (I1 × S1))) (setF : D → I1 → β → M E U α Unit)
    (setE : K → β → M E U α Unit) (nextE : S2 → M E U α (Option (K × S2)))
    (Rel : Option (I1 × S1) → Option (K × S2) → Prop) (P : World U α → Prop)
    (dest : D) (it : FiniteIterator (UM E U) β St) (w : World U α) (inds : Inds)
    (y1 : Option (I1 × S1)) (y2 : Option (K × S2))
    (heach : (eachindexF dest).run.run w = (.ok inds, w))
    (hstart : (startF inds).run.run w = (.ok y1, w))
    (hR0 : Rel y1 y2) (hP0 : P w)
    (hnone : ∀ y1 y2, Rel y1 y2 → (y1 = none ↔ y2 = none))
    (huser : ∀ w u, P w → P { w with user := u })
    (hset : ∀ i s k s2 x w, P w → Rel (some (i, s)) (some (k, s2)) →
      (setF dest i x).run.run w = (setE k x).run.run w ∧
      ∀ w', (setF dest i x).run.run w = (.ok (), w') → P w')
    (hnext : ∀ i s k s2 w, P w → Rel (some (i, s)) (some (k, s2)) →
      StepAgree Rel P ((nextF inds s).run.run w) ((nextE s2).run.run w)) :
    (JuliaLean.base.abstractarray.copytoIterable (m := M E U α) eachindexF startF nextF setF dest it).run.run w =
      (do
        match ← liftUser it.first with
        | none => pure ()
        | some (x, st) => fillRef it nextE setE y2 x st
        pure dest : M E U α D).run.run w := by
  unfold JuliaLean.base.abstractarray.copytoIterable
  simp only [forIn_iter_eq, m_bind_run, heach, hstart]
  rcases h3 : (liftUser it.first : M E U α (Option (β × St))).run.run w with ⟨r3, w3⟩
  cases r3 with
  | error e => rfl
  | ok o =>
    cases o with
    | none => simp only [m_pure_run]
    | some p =>
      obtain ⟨x, st⟩ := p
      have hP3 : P w3 := by
        rw [liftUser_run] at h3
        revert h3
        rcases it.first.run.run w.user with ⟨r', u⟩
        cases r' <;> intro h3 <;> cases h3 <;> exact huser w u hP0
      have key := copyLoop_sim it (setF dest) (nextF inds) setE nextE Rel P hnone huser hset hnext
        dest (it.rank st) st rfl x y1 y2 w3 hP3 hR0
      simp only [m_bind_run, m_pure_run] at key
      refine Eq.trans ?_ (Eq.trans key ?_)
      · rfl
      · exact (m_bind_run (fillRef it nextE setE y2 x st) (fun _ => pure dest) w3).symm


theorem heapFill_eq {Tag : Type} (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (t : Type) (a : HeapArray Tag)
    (it : FiniteIterator (UM E U) β St) :
    (do heapFill isa asTyped convert t it a; pure a : M E U α (HeapArray Tag)) =
      (do
        match ← liftUser it.first with
        | none => pure ()
        | some (x, st) =>
          fillRef it (fun k => pure (if k + 1 < a.dimensions.prod then some (k + 1, k + 1) else none))
            (fun k x => do writeSlot a.handle k (← stored isa asTyped convert t x))
            (if 0 < a.dimensions.prod then some (0, 0) else none) x st
        pure a : M E U α (HeapArray Tag)) := by
  unfold heapFill
  rw [bind_assoc]
  congr 1
  funext o
  rcases o with _ | ⟨x, st⟩
  · exact pure_bind _ _
  · rfl

theorem oneToWrap_stop (len : Nat) (h : len < 2 ^ 63) :
    (JuliaLean.base.range.unchecked_oneto (JInt.wrap .i64 (len : Int)) : OneTo I).stop.val = len := by
  show (JInt.wrap .i64 (len : Int)).val = _
  rw [ival_wrap _ (by omega)]

set_option maxRecDepth 16384 in
theorem copyBase_n {Tag : Type} (n : Nat) (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (t : Type) (a : HeapArray Tag)
    (it : FiniteIterator (UM E U) β St) (w : World U α) (sl : List (Option α))
    (hs : w.heap[a.handle]? = some sl) (hlen : sl.length = n)
    (hP : n < 2 ^ 63) :
    (JuliaLean.base.abstractarray.copytoIterable (m := M E U α)
      heapEachindex
      (fun r => liftRange (JuliaLean.base.range.JIterate1.iterate r))
      (fun r st => liftRange (JuliaLean.base.range.JIterate2.iterate r st))
      (heapSetindex isa asTyped convert t) a it).run.run w =
      (do
        match ← liftUser it.first with
        | none => pure ()
        | some (x, st) =>
          fillRef it (fun k => pure (if k + 1 < n then some (k + 1, k + 1) else none))
            (fun k x => do writeSlot a.handle k (← stored isa asTyped convert t x))
            (if 0 < n then some (0, 0) else none) x st
        pure a : M E U α (HeapArray Tag)).run.run w := by
  have heach := heapEachindex_run (E := E) a w sl hs
  have hstop := oneToWrap_stop sl.length (by omega)
  generalize (JuliaLean.base.range.unchecked_oneto (JInt.wrap .i64 (sl.length : Int)) : OneTo I) = R at heach hstop
  rw [hlen] at hstop
  have hstart : (liftRange (JuliaLean.base.range.JIterate1.iterate R) : M E U α _).run.run w =
      (.ok (if (n : Int) < 1 then none else
        some (JuliaLean.base.range.JOneunit.oneunit, JuliaLean.base.range.JOneunit.oneunit)), w) := by
    rw [iterate1_oneTo_eq, hstop]
    rfl
  exact (copyGeneric_run (E := E) heapEachindex
      (fun r => liftRange (JuliaLean.base.range.JIterate1.iterate r))
      (fun r st => liftRange (JuliaLean.base.range.JIterate2.iterate r st))
      (heapSetindex isa asTyped convert t)
      (fun k x => do writeSlot a.handle k (← stored isa asTyped convert t x))
      (fun k => pure (if k + 1 < n then some (k + 1, k + 1) else none))
      (baseRel n) (baseInv a n) a it w R
      (if (n : Int) < 1 then none else
        some (JuliaLean.base.range.JOneunit.oneunit, JuliaLean.base.range.JOneunit.oneunit))
      (if 0 < n then some (0, 0) else none)
      heach hstart (baseRel_start _) ⟨sl, hs, hlen⟩
      (baseRel_none _) (fun w u ⟨sl', h1, h2⟩ => ⟨sl', h1, h2⟩)
      (fun i s k s2 x w hP hR => baseSet isa asTyped convert t a _ i s k s2 x w hP hR)
      (fun i s k s2 w hP hR => baseNext a n R hstop i s k s2 w hP hR))

/-- `copyto!` into a Base array of `n = prod(dims)` slots is `heapFill`. -/
theorem copyBase_run {Tag : Type} (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (t : Type) (a : HeapArray Tag)
    (it : FiniteIterator (UM E U) β St) (w : World U α) (sl : List (Option α))
    (hs : w.heap[a.handle]? = some sl) (hlen : sl.length = a.dimensions.prod)
    (hP : a.dimensions.prod < 2 ^ 63) :
    (JuliaLean.base.abstractarray.copytoIterable (m := M E U α)
      heapEachindex
      (fun r => liftRange (JuliaLean.base.range.JIterate1.iterate r))
      (fun r st => liftRange (JuliaLean.base.range.JIterate2.iterate r st))
      (heapSetindex isa asTyped convert t) a it).run.run w =
      (do heapFill isa asTyped convert t it a; pure a : M E U α (HeapArray Tag)).run.run w :=
  (copyBase_n a.dimensions.prod isa asTyped convert t a it w sl hs hlen hP).trans
    (congrArg (fun z => z.run.run w) (heapFill_eq isa asTyped convert t a it).symm)
end
end
end opusGrowth
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
open JuliaLean.Proofs.base.array.round6dcollect3
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
open JuliaLean.base.range (OneTo)
section
variable {E U α R V A C X B Tag : Type}

theorem fail_bind {γ δ : Type} (f : Fault E) (g : γ → M E U α δ) :
    (fail f >>= g : M E U α δ) = fail f := rfl

theorem baseSimilarDims_eq (alloc : Type → List I → M E U α B) (c : BaseContainer Tag A)
    (t : Type) (dims : List I) : baseSimilarDims alloc c t dims = alloc t dims := by
  cases c <;> rfl

theorem wrap_ival (x : I) : JInt.wrap .i64 x.val = x :=
  Subtype.ext (ival_wrap _ (ival_bounds x))

theorem intValue_bit (i : I) : (intValue (.bit .i64 i) : M E U α Int) = pure i.val := by
  unfold intValue
  exact if_pos (show IntTy.i64.min ≤ (IntegerValue.bit .i64 i).val ∧
    (IntegerValue.bit .i64 i).val ≤ IntTy.i64.max from ival_bounds i)

/-- `to_shape` of an Integer length is `Int(len)`. -/
theorem toShapeIntegerValue_eq {ops : BigIntegerOps} (hops : ops.Lawful) (x : IntegerValue) :
    (toShapeIntegerValue ops x : M E U α I) = (do let v ← intValue x; pure (JInt.wrap .i64 v)) := by
  unfold toShapeIntegerValue
  split
  · rename_i i
    rw [intValue_bit, pure_bind, wrap_ival]
    rfl
  · simp only [JuliaLean.base.abstractarray.toShapeInteger, integerValue_toInt hops, intValue]
    split
    · rw [pure_bind]; rfl
    · rw [fail_bind]; rfl

/-- `similar(c, T, len)` for a Base container: `Array{T,1}(undef, Int(len))`. -/
theorem similarLength_base {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (own : C → Type → SimilarArg R → UM E U V)
    (c : BaseContainer Tag A) (t : Type) (len : IntegerValue) :
    (similarLength (α := α) layout ops tag own (.base c) t len) =
      (do Sum.inl <$> allocInts layout (tag t) [← intValue len]) := by
  simp only [similarLength, JuliaLean.base.abstractarray.similarTypeVarargs]
  split
  · rename_i n heq
    cases heq
    simp only [baseSimilarDims_eq, allocUndef, allocInts, intValue_bit, pure_bind, List.map_cons,
      List.map_nil, wrap_ival]
  · simp only [JuliaLean.base.abstractarray.similarLegacyOneTo,
      JuliaLean.base.abstractarray.toShapeMixed, List.mapM_cons, List.mapM_nil,
      toShapeIntegerValue_eq hops, baseSimilarDims_eq, allocUndef, allocInts, bind_assoc, pure_bind,
      List.map_cons, List.map_nil]
    rw [map_bind]


/-- `to_shape(r::OneTo)` is `Int(last(r))`. -/
theorem toShapeAxis_eq {ops : BigIntegerOps} (hops : ops.Lawful) (r : OneTo IntegerValue) :
    (toShapeAxis ops r : M E U α I) = (do let v ← intValue r.stop; pure (JInt.wrap .i64 v)) := by
  unfold toShapeAxis
  simp only [JuliaLean.base.abstractarray.toShapeOneTo,
    JuliaLean.base.abstractarray.toShapeIntegerHelper, toShapeIntegerValue_eq hops]
  rfl

theorem mapM_toShapeAxis {ops : BigIntegerOps} (hops : ops.Lawful) (rs : List (OneTo IntegerValue)) :
    (rs.mapM (toShapeAxis ops) : M E U α (List I)) =
      (do let vs ← rs.mapM (fun r => intValue r.stop); pure (vs.map (JInt.wrap .i64))) := by
  induction rs with
  | nil => simp only [List.mapM_nil, pure_bind, List.map_nil]
  | cons r rs ih =>
    simp only [List.mapM_cons, toShapeAxis_eq hops, ih, bind_assoc, pure_bind, List.map_cons]

/-- `similar(c, T, axs)` for a Base container: `OneTo` axes allocate their `Int` lengths. -/
theorem similarAxes_base {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (c : BaseContainer Tag A) (t : Type) (axs : List (Axis R)) :
    (similarAxes (α := α) layout ops tag own axisSimilar (.base c) t axs) =
      axesAllocation layout (tag t) (axisSimilar c t) axs := by
  simp only [similarAxes, axesAllocation]
  rcases h : oneTos axs with _ | rs
  · rfl
  · cases rs with
    | nil =>
      simp only [baseSimilarDims_eq, allocUndef, allocInts, List.mapM_nil, pure_bind, List.map_nil]
    | cons r rs =>
      simp only [JuliaLean.base.abstractarray.similarLegacyOneTo,
        JuliaLean.base.abstractarray.toShapeMixed, mapM_toShapeAxis hops, baseSimilarDims_eq,
        allocUndef, allocInts, bind_assoc, pure_bind, map_bind]

theorem similarFor_base_length {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (c : BaseContainer Tag A) (t : Type) (itr : X) (len : IntegerValue) :
    (similarFor (α := α) layout ops tag own axisSimilar (.base c) t itr .hasLength (.length len)) =
      (do Sum.inl <$> allocInts layout (tag t) [← intValue len]) :=
  similarLength_base hops layout tag own c t len

theorem similarFor_base_axes {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (own : C → Type → SimilarArg R → UM E U V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → UM E U V)
    (c : BaseContainer Tag A) (t : Type) (itr : X) (n : Nat) (axs : List (Axis R)) :
    (similarFor (α := α) layout ops tag own axisSimilar (.base c) t itr (.hasShape n) (.axes axs)) =
      axesAllocation layout (tag t) (axisSimilar c t) axs :=
  similarAxes_base hops layout tag own axisSimilar c t axs
end
end
end opusGrowth
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
open JuliaLean.Proofs.base.array.round6dcollect3
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
open JuliaLean.base.range (OneTo)
section
variable {α : Type}

theorem memorynew_none_run (n : I) (heap : VectorHeap α) :
    (memorynew (m := VectorM α) none (heapAllocate 0) heapAllocate n).run heap =
      .error (Error.typeError "GenericMemory") := rfl

theorem heapArrayUndef_none {Tag : Type} (layout : Tag → Option MemoryLayout) (target : Tag)
    (hl : layout target = none) (dims : List I) (heap : VectorHeap α) (a : HeapArray Tag)
    (heap' : VectorHeap α) : (heapArrayUndef layout target dims).run heap ≠ .ok (a, heap') := by
  intro h
  have key : ∀ (k : VectorM α I) (ds : List I),
      (do let mem ← newAsMemoryref (layout target) (heapAllocate 0) heapAllocate (← k)
          (pure ⟨mem, target, ds.map (fun d : I => d.val.toNat), ds.map (fun d : I => (1, d.val.toNat))⟩ :
            VectorM α (HeapArray Tag))).run heap ≠ .ok (a, heap') := by
    intro k ds hk
    rw [vector_bind_run] at hk
    rcases hr : k.run heap with _ | ⟨x, h1⟩ <;> rw [hr] at hk
    · cases hk
    · simp only [vector_bind_run, newAsMemoryref, memoryUndef, hl, memorynew_none_run] at hk
      cases hk
  match dims with
  | [m] =>
    simp only [heapArrayUndef, arrayUndef, arrayUndef1, memoryUndef, hl, vector_bind_run,
      memorynew_none_run] at h
    cases h
  | [] => exact key _ [] h
  | [m, n] => exact key _ [m, n] h
  | [m, n, o] => exact key _ [m, n, o] h
  | m :: n :: o :: p :: rest => exact key _ (m :: n :: o :: p :: rest) h

theorem intList_prod_nonneg (ds : List Int) (h : ∀ d ∈ ds, 0 ≤ d) : 0 ≤ ds.prod := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.prod_cons]
    exact Int.mul_nonneg (h d (List.mem_cons_self ..)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem intList_prod_toNat (ds : List Int) (h : ∀ d ∈ ds, 0 ≤ d) :
    (ds.map Int.toNat).prod = ds.prod.toNat := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := h d (List.mem_cons_self ..)
    have hds : ∀ y ∈ ds, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.prod_cons, ih hds, Int.toNat_mul hd (intList_prod_nonneg ds hds)]

/-- A successful `Array{T,N}(undef, dims)` leaves a fresh all-unassigned memory of `prod(dims)`
slots, fewer than `2^63`, at the array's handle. -/
theorem heapArrayUndef_post {Tag : Type} (layout : Tag → Option MemoryLayout) (target : Tag)
    (dims : List I) (heap : VectorHeap α) (a : HeapArray Tag) (heap' : VectorHeap α)
    (h : (heapArrayUndef layout target dims).run heap = .ok (a, heap')) :
    heap'[a.handle]? = some (List.replicate a.dimensions.prod none) ∧ a.dimensions.prod < 2 ^ 63 := by
  cases hl : layout target with
  | none => exact absurd h (heapArrayUndef_none layout target hl dims heap a heap')
  | some l =>
    rw [heapArrayUndef_run layout target l hl] at h
    unfold allocOutcome at h
    split at h
    · cases h
    · rename_i hnone
      cases h
      refine ⟨by simp, ?_⟩
      unfold arrayAllocError at hnone
      split at hnone
      · rename_i d hd
        have hf : memoryFits l d.toNat := by
          by_cases hc : d < 0 ∨ ¬ memoryFits l d.toNat
          · simp [hc] at hnone
          · exact Classical.byContradiction fun hn => hc (Or.inr hn)
        rw [hd]
        have := hf.1
        simp only [maxIntVal] at this
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.mul_one]
        omega
      · rename_i hne
        split at hnone
        · cases hnone
        · rename_i hbad
          split at hnone
          · cases hnone
          · rename_i hfit
            have hf := Classical.byContradiction hfit
            by_cases h2 : 2 ≤ (dims.map (fun d : I => d.val)).length
            · have hnn : ∀ d ∈ dims.map (fun d : I => d.val), 0 ≤ d := by
                intro d hd
                refine Classical.byContradiction fun hlt => hbad ⟨h2, Or.inl ⟨d, hd, Or.inl (by omega)⟩⟩
              rw [intList_prod_toNat _ hnn]
              have := hf.1
              simp only [maxIntVal] at this
              omega
            · have hlen : (dims.map (fun d : I => d.val)).length = 0 := by
                match hm : dims.map (fun d : I => d.val) with
                | [] => rfl
                | [d] => exact absurd hm (hne d)
                | _ :: _ :: _ => rw [hm] at h2; simp at h2
              rw [List.length_eq_zero_iff.mp hlen]
              simp
end
end
end opusGrowth
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
open JuliaLean.Proofs.base.array.round6dcollect3
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
open JuliaLean.base.range (OneTo)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
section
variable {E U α Tag R V A C β St K K' S' : Type}

theorem m_map_run {γ δ : Type} (f : γ → δ) (x : M E U α γ) (w : World U α) :
    (f <$> x).run.run w = match x.run.run w with
      | (.ok a, w') => (.ok (f a), w')
      | (.error e, w') => (.error e, w') := by
  rw [map_eq_pure_bind, m_bind_run]
  rcases x.run.run w with ⟨r, w'⟩
  cases r <;> rfl

theorem bind_run_congr {γ δ : Type} (x : M E U α γ) (f g : γ → M E U α δ) (w : World U α)
    (h : ∀ a w', x.run.run w = (.ok a, w') → (f a).run.run w' = (g a).run.run w') :
    (x >>= f).run.run w = (x >>= g).run.run w := by
  rw [m_bind_run, m_bind_run]
  rcases hx : x.run.run w with ⟨r, w'⟩
  cases r with
  | error e => rfl
  | ok a => exact h a w' hx

theorem copyInto_user (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (d : UserDest E U V β K K' S') (t : Type) (v : V)
    (it : FiniteIterator (UM E U) β St) (w : World U α) :
    (Collected.ofSized <$> copyInto (Tag := Tag) isa asTyped convert d t (.inr v) it).run.run w =
      (do userFill d it v; pure (Collected.user v) : M E U α (Collected Tag V)).run.run w := by
  simp only [copyInto]
  rw [m_map_run, m_map_run, copyUser_run, m_bind_run, m_bind_run]
  rcases (userFill (α := α) d it v).run.run w with ⟨r, w'⟩
  cases r <;> rfl

theorem copyInto_base (isa : β → Type → Bool) (asTyped : Type → β → α)
    (convert : Type → β → UM E U α) (d : UserDest E U V β K K' S') (t : Type) (a : HeapArray Tag)
    (it : FiniteIterator (UM E U) β St) (w : World U α)
    (hs : w.heap[a.handle]? = some (List.replicate a.dimensions.prod none))
    (hP : a.dimensions.prod < 2 ^ 63) :
    (Collected.ofSized <$> copyInto isa asTyped convert d t (.inl a) it).run.run w =
      (do heapFill isa asTyped convert t it a; pure (Collected.array a) :
        M E U α (Collected Tag V)).run.run w := by
  simp only [copyInto]
  rw [m_map_run, m_map_run, copyBase_run isa asTyped convert t a it w _ hs
    (List.length_replicate ..) hP, m_bind_run, m_bind_run]
  rcases (heapFill (E := E) isa asTyped convert t it a).run.run w with ⟨r, w'⟩
  cases r <;> rfl

theorem allocInts_post (layout : Tag → Option MemoryLayout) (target : Tag) (ds : List Int)
    (w : World U α) (a : HeapArray Tag) (w' : World U α)
    (h : (allocInts (E := E) layout target ds).run.run w = (.ok a, w')) :
    w'.heap[a.handle]? = some (List.replicate a.dimensions.prod none) ∧ a.dimensions.prod < 2 ^ 63 := by
  unfold allocInts at h
  rw [liftHeap_run] at h
  revert h
  rcases hr : (heapAllocateIntDims (α := α) layout target (ds.map (JInt.wrap .i64))).run w.heap with
    _ | ⟨b, h'⟩
  · intro h; cases h
  · intro h
    cases h
    exact heapArrayUndef_post layout target _ w.heap a h' hr

theorem axesAllocation_post (layout : Tag → Option MemoryLayout) (target : Tag)
    (other : List (Axis R) → UM E U V) (axs : List (Axis R)) (w : World U α) (a : HeapArray Tag)
    (w' : World U α) (h : (axesAllocation layout target other axs).run.run w = (.ok (.inl a), w')) :
    w'.heap[a.handle]? = some (List.replicate a.dimensions.prod none) ∧ a.dimensions.prod < 2 ^ 63 := by
  unfold axesAllocation at h
  split at h
  · rw [m_bind_run] at h
    split at h
    · rw [m_map_run] at h
      split at h
      · rename_i b w2 ha
        cases h
        exact allocInts_post layout target _ _ a w' ha
      · cases h
    · cases h
  · rw [m_map_run] at h
    revert h
    rcases (liftUser (other axs) : M E U α V).run.run w with ⟨r, w1⟩
    cases r <;> intro h <;> cases h


set_option maxHeartbeats 8000000 in
theorem knownEltypeCollectSpec : KnownEltypeCollectSpec := by
  intro E U α Tag R V A C β St K K' S' ops tag layout eltype iteratorEltype iteratorSize lengthQ axesQ
    own axisSimilar isa asTyped convert d unknownEltype it w hops hel
  dsimp only
  have sized : ∀ (cont : Container Tag A C) (isz : IteratorSize),
      (isz = .hasLength ∨ ∃ n, isz = .hasShape n) →
      (collectDispatch layout ops tag eltype lengthQ axesQ own axisSimilar isa asTyped convert d
        unknownEltype cont it .hasEltype isz).run.run w =
      (match cont, isz with
        | .own c, .hasLength => do
          let v ← liftUser (own c (eltype it) (.length (← liftUser (lengthQ it))))
          userFill d it v
          pure (Collected.user v)
        | .own c, .hasShape _ => do
          let v ← liftUser (own c (eltype it) (.axes (← liftUser (axesQ it))))
          userFill d it v
          pure (Collected.user v)
        | .base _, .hasLength => do
          let a ← allocInts layout (tag (eltype it)) [← intValue (← liftUser (lengthQ it))]
          heapFill isa asTyped convert (eltype it) it a
          pure (Collected.array a)
        | .base c, .hasShape _ => do
          match ← axesAllocation layout (tag (eltype it)) (axisSimilar c (eltype it)) (← liftUser (axesQ it)) with
          | .inl a =>
            heapFill isa asTyped convert (eltype it) it a
            pure (Collected.array a)
          | .inr v =>
            userFill d it v
            pure (Collected.user v)
        | _, _ => fail (.base (.method "_collect")) : M E U α (Collected Tag V)).run.run w := by
    intro cont isz hisz
    rcases hisz with rfl | ⟨n, rfl⟩ <;> cases cont with
    | base c =>
      unfold collectDispatch collectKnownSized
      simp only [shapeOf, similarShapeLength, similarShapeAxes, map_bind, bind_map_left]
      refine bind_run_congr _ _ _ w fun q w1 _ => ?_
      first
      | rw [similarFor_base_length hops]
        simp only [bind_assoc, bind_map_left]
        refine bind_run_congr _ _ _ w1 fun v w2 _ => ?_
        refine bind_run_congr _ _ _ w2 fun a w3 ha => ?_
        obtain ⟨hs, hP⟩ := allocInts_post layout _ _ w2 a w3 ha
        exact copyInto_base isa asTyped convert d _ a it w3 hs hP
      | rw [similarFor_base_axes hops]
        refine bind_run_congr _ _ _ w1 fun x w2 hx => ?_
        cases x with
        | inl a =>
          obtain ⟨hs, hP⟩ := axesAllocation_post layout _ _ q w1 a w2 hx
          exact copyInto_base isa asTyped convert d _ a it w2 hs hP
        | inr v => exact copyInto_user isa asTyped convert d _ v it w2
    | own c =>
      unfold collectDispatch collectKnownSized
      simp only [shapeOf, similarShapeLength, similarShapeAxes, map_bind, bind_map_left]
      refine bind_run_congr _ _ _ w fun q w1 _ => ?_
      simp only [similarFor, similarForLength, similarForAxes, similarLength, similarAxes,
        bind_map_left]
      refine bind_run_congr _ _ _ w1 fun v w2 _ => ?_
      exact copyInto_user isa asTyped convert d _ v it w2
  refine ⟨fun isz hisz hsz => ⟨?_, fun cont => ?_⟩, fun hinf => ⟨?_, fun cont => ?_⟩⟩
  · simp only [JuliaLean.base.array.collect, hel, hsz]
    exact sized _ _ hisz
  · simp only [JuliaLean.base.array.collectSimilar, hel, hsz]
    exact sized _ _ hisz
  · simp only [JuliaLean.base.array.collect, hel, hinf]
    rfl
  · simp only [JuliaLean.base.array.collectSimilar, hel, hinf]
    rfl
end
end
end opusGrowth
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
open JuliaLean.Proofs.base.array.round6dcollect2
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
open JuliaLean.base.range (OneTo)
open JuliaLean.base.generator (IteratorSize)
section
variable {E U α R V A C X B Tag : Type}

theorem m2_bind_run {γ δ : Type} (x : M E U α γ) (f : γ → M E U α δ) (w : World U α) :
    (x >>= f).run.run w = match x.run.run w with
      | (.ok a, w') => (f a).run.run w'
      | (.error e, w') => (.error e, w') := by
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases h : x.run.run w with ⟨r, w'⟩
  cases r <;> simp [h, ExceptT.bindCont] <;> rfl

theorem liftHeap2_run {γ : Type} (x : VectorM α γ) (w : World U α) :
    (liftHeap x : M E U α γ).run.run w = match x.run w.heap with
      | .ok (b, h) => (.ok b, { w with heap := h })
      | .error e => (.error (.base e), w) := by
  unfold liftHeap
  simp only [m2_bind_run]
  show (match x.run w.heap with
    | .ok (b, h) => (set { w with heap := h } >>= fun _ => pure b : M E U α γ)
    | .error e => fail (.base e)).run.run w = _
  rcases h : x.run w.heap with _ | ⟨b, h'⟩ <;> rfl

theorem m2_fail_bind {γ δ : Type} (f : Fault E) (g : γ → M E U α δ) :
    (fail f >>= g : M E U α δ) = fail f := rfl

theorem baseSimilarDims2_eq (alloc : Type → List I → M E U α B) (c : BaseContainer Tag A)
    (t : Type) (dims : List I) : baseSimilarDims alloc c t dims = alloc t dims := by
  cases c <;> rfl

theorem intValue2_bit (i : I) : (intValue (.bit .i64 i) : M E U α Int) = pure i.val := by
  unfold intValue
  exact if_pos (show IntTy.i64.min ≤ (IntegerValue.bit .i64 i).val ∧
    (IntegerValue.bit .i64 i).val ≤ IntTy.i64.max from ival_bounds i)

theorem liftBase_convert {ops : BigIntegerOps} (hops : ops.Lawful) (x : IntegerValue) :
    (liftBase (JuliaLean.Proofs.base.array.round8.convertInteger ops .i64 x) : M E U α I) =
      (do let v ← intValue x; pure (JInt.wrap .i64 v)) := by
  rw [convertInteger_i64 hops]
  unfold intValue
  split
  · rw [pure_bind]; rfl
  · rw [m2_fail_bind]; rfl

theorem toShapeInteger8_eq {ops : BigIntegerOps} (hops : ops.Lawful) (x : IntegerValue) :
    (JuliaLean.Proofs.base.array.round8.Collectors.toShapeInteger ops x : M E U α I) =
      (do let v ← intValue x; pure (JInt.wrap .i64 v)) := by
  unfold JuliaLean.Proofs.base.array.round8.Collectors.toShapeInteger
  split
  · rename_i i
    rw [intValue2_bit, pure_bind, wrap_ival]
    rfl
  · exact liftBase_convert hops _

theorem toShapeAxis8_eq {ops : BigIntegerOps} (hops : ops.Lawful) (r : OneTo IntegerValue) :
    (JuliaLean.Proofs.base.array.round8.Collectors.toShapeAxis ops r : M E U α I) =
      (do let v ← intValue r.stop; pure (JInt.wrap .i64 v)) := by
  unfold JuliaLean.Proofs.base.array.round8.Collectors.toShapeAxis
  simp only [JuliaLean.base.abstractarray.toShapeOneTo,
    JuliaLean.base.abstractarray.toShapeIntegerHelper, toShapeInteger8_eq hops]
  rfl

theorem mapM_toShapeAxis8 {ops : BigIntegerOps} (hops : ops.Lawful) (rs : List (OneTo IntegerValue)) :
    (rs.mapM (JuliaLean.Proofs.base.array.round8.Collectors.toShapeAxis ops) : M E U α (List I)) =
      (do let vs ← rs.mapM (fun r => intValue r.stop); pure (vs.map (JInt.wrap .i64))) := by
  induction rs with
  | nil => simp only [List.mapM_nil, pure_bind, List.map_nil]
  | cons r rs ih =>
    simp only [List.mapM_cons, toShapeAxis8_eq hops, ih, bind_assoc, pure_bind, List.map_cons]

theorem similarLength8_base {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (own : C → Type → SimilarArg R → M E U α V)
    (c : BaseContainer Tag A) (t : Type) (len : IntegerValue) :
    (JuliaLean.Proofs.base.array.round8.Collectors.similarLength layout ops tag own (.base c) t len) =
      (do Sum.inl <$> allocInts layout (tag t) [← intValue len]) := by
  simp only [JuliaLean.Proofs.base.array.round8.Collectors.similarLength, JuliaLean.base.abstractarray.similarTypeVarargs]
  split
  · rename_i n heq
    cases heq
    simp only [baseSimilarDims2_eq, allocUndef, allocInts, intValue2_bit, pure_bind, List.map_cons,
      List.map_nil, wrap_ival]
  · simp only [JuliaLean.base.abstractarray.similarLegacyOneTo,
      JuliaLean.base.abstractarray.toShapeMixed, List.mapM_cons, List.mapM_nil,
      toShapeInteger8_eq hops, baseSimilarDims2_eq, allocUndef, allocInts, bind_assoc, pure_bind,
      List.map_cons, List.map_nil]
    rw [map_bind]

theorem similarAxes8_base {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag) (own : C → Type → SimilarArg R → M E U α V)
    (axisSimilar : BaseContainer Tag A → Type → List (Axis R) → M E U α V)
    (c : BaseContainer Tag A) (t : Type) (axs : List (Axis R)) :
    (JuliaLean.Proofs.base.array.round8.Collectors.similarAxes layout ops tag own axisSimilar (.base c) t axs) =
      JuliaLean.Proofs.base.array.round8.Collectors.axesAllocation layout (tag t) (axisSimilar c t) axs := by
  simp only [JuliaLean.Proofs.base.array.round8.Collectors.similarAxes, JuliaLean.Proofs.base.array.round8.Collectors.axesAllocation]
  rcases h : oneTos axs with _ | rs
  · rfl
  · cases rs with
    | nil =>
      simp only [baseSimilarDims2_eq, allocUndef, allocInts, List.mapM_nil, pure_bind, List.map_nil]
    | cons r rs =>
      simp only [JuliaLean.base.abstractarray.similarLegacyOneTo,
        JuliaLean.base.abstractarray.toShapeMixed, mapM_toShapeAxis8 hops, baseSimilarDims2_eq,
        allocUndef, allocInts, bind_assoc, pure_bind, map_bind]

theorem arraySimilar8_eq {ops : BigIntegerOps} (hops : ops.Lawful)
    (layout : Tag → Option MemoryLayout) (tag : Type → Tag)
    (axisStorage : Type → List (Axis R) → M E U α V) (t : Type) (axs : List (Axis R)) :
    (JuliaLean.Proofs.base.array.round8.Collectors.arraySimilar layout ops tag axisStorage t axs) =
      JuliaLean.Proofs.base.array.round8.Collectors.axesAllocation layout (tag t) (axisStorage t) axs := by
  simp only [JuliaLean.Proofs.base.array.round8.Collectors.arraySimilar, JuliaLean.Proofs.base.array.round8.Collectors.axesAllocation]
  rcases h : oneTos axs with _ | rs
  · rfl
  · cases rs with
    | nil =>
      simp only [similar421, JuliaLean.base.abstractarray.similarStorageDims, allocUndef, allocInts,
        List.mapM_nil, pure_bind, List.map_nil]
    | cons r rs =>
      simp only [JuliaLean.base.abstractarray.similarStorageLegacyOneTo, similar421,
        JuliaLean.base.abstractarray.similarStorageDims,
        JuliaLean.base.abstractarray.toShapeMixed, mapM_toShapeAxis8 hops,
        allocUndef, allocInts, bind_assoc, pure_bind, map_bind]

/-- A zero-length `Vector{T}` on the heap is `fresh`. -/
theorem zeroVector_run (l : MemoryLayout) (layout : Tag → Option MemoryLayout) (target : Tag)
    (hl : layout target = some l) (dims : List I) (hd : dims.map (·.val) = [0]) (w : World U α) :
    (Sum.inl <$> liftHeap (heapArrayUndef layout target dims) : M E U α (Sum (HeapArray Tag) V)).run.run w =
      (Sum.inl <$> fresh target [0] : M E U α (Sum (HeapArray Tag) V)).run.run w := by
  have hrun := heapArrayUndef_run (α := α) layout target l hl dims w.heap
  rw [hd] at hrun
  have ho : allocOutcome (α := α) l target [0] w.heap =
      .ok (⟨w.heap.length, target, [0], [(1, 0)]⟩, w.heap ++ [List.replicate 0 none]) := by
    unfold allocOutcome arrayAllocError
    simp [memoryFits_zero]
  rw [ho] at hrun
  rw [map_eq_pure_bind, map_eq_pure_bind, m2_bind_run, m2_bind_run, liftHeap2_run, hrun]
  rfl


theorem collectAllocSpec : JuliaLean.Proofs.base.array.round8.Collectors.CollectAllocSpec := by
  intro E U α Tag R V A C G X ops tag elementLayout lengthQ axesQ axisStorage axisSimilar own generic
    t itr w hops
  dsimp only
  have hz : ([zero] : List I).map (·.val) = [0] := rfl
  refine ⟨?_, ?_, fun n => ?_, ?_, fun c => ⟨?_, fun len => ?_, fun n axs => ?_⟩,
    fun c => ⟨?_, fun len => ?_, fun n axs => ?_⟩, fun c isz shp => rfl⟩
  · simp only [arrayFor, JuliaLean.Proofs.base.array.round8.Collectors.shapeOf, pure_bind,
      JuliaLean.Proofs.base.array.round8.Collectors.arrayForInner, arrayForUnknown,
      heapVectorAllocate]
    exact zeroVector_run (elementLayout (tag t)) (fun target => some (elementLayout target)) (tag t) rfl [zero] hz w
  · congr 2
    simp only [arrayFor, JuliaLean.Proofs.base.array.round8.Collectors.shapeOf, similarShapeLength,
      bind_map_left, JuliaLean.Proofs.base.array.round8.Collectors.arrayForInner, arrayForLength,
      liftBase_convert hops, bind_assoc, pure_bind, map_bind]
  · congr 2
    simp only [arrayFor, JuliaLean.Proofs.base.array.round8.Collectors.shapeOf, similarShapeAxes,
      bind_map_left, JuliaLean.Proofs.base.array.round8.Collectors.arrayForInner, arrayForShape,
      arraySimilar8_eq hops]
  · rfl
  · simp only [JuliaLean.Proofs.base.array.round8.Collectors.similarFor, similarForUnknown,
      JuliaLean.Proofs.base.array.round8.Collectors.similarInt,
      JuliaLean.base.abstractarray.similarTypeVarargs, baseSimilarDims2_eq, allocUndef,
      heapAllocateIntDims]
    exact zeroVector_run (elementLayout (tag t)) (fun target => some (elementLayout target)) (tag t) rfl [zero] hz w
  · congr 2
    exact similarLength8_base hops _ tag own c t len
  · congr 2
    exact similarAxes8_base hops _ tag own axisSimilar c t axs
  · rfl
  · rfl
  · rfl
end
end
end opusGrowth
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
attribute [local irreducible] JInt.wrap wrapInt

theorem heapRemaining_val' (xs : List (Option α)) (hn : xs.length < 9223372036854775808) (i : I)
    (h1 : 1 ≤ i.val) :
    (JInt.wrap .i64 (xs.length : Int) - i + one).val = xs.length - i.val + 1 := by
  have hb := ival_bounds i
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := ival_wrap _ (by omega)
  have hs : (JInt.wrap .i64 (xs.length : Int) - i).val = xs.length - i.val := by
    rw [ival_sub (JInt.wrap .i64 (xs.length : Int)) i (by rw [hv]; omega), hv]
  rw [ival_add (JInt.wrap .i64 (xs.length : Int) - i) one (by rw [hs, ival_one]; omega), hs,
    ival_one]

theorem heapCheckedCopy_window_run' (heap : VectorHeap α) (dest src : Nat)
    (xs ys : List (Option α)) (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (hxn : xs.length < 9223372036854775808) (hyn : ys.length < 9223372036854775808) (di si n : I)
    (hn : 0 < n.val)
    (hdi : 1 ≤ di.val) (hde : di.val - 1 + n.val ≤ (ys.length : Int))
    (hsi : 1 ≤ si.val) (hse : si.val - 1 + n.val ≤ (xs.length : Int)) :
    (heapCheckedCopy (fun x => Except.ok (ε := Error) x) dest di src si n).run heap =
      .ok (dest, heap.set dest (ys.take (di.val - 1).toNat ++
        (xs.drop (si.val - 1).toNat).take n.val.toNat ++ ys.drop (di.val - 1 + n.val).toNat)) := by
  have hdy : di.val ≤ (ys.length : Int) := by clear hsrc hdest; omega
  have hsx : si.val ≤ (xs.length : Int) := by clear hsrc hdest; omega
  have hn0 : 0 ≤ n.val := Int.le_of_lt hn
  have hrd := heapRemaining_val' ys hyn di hdi
  have hrs := heapRemaining_val' xs hxn si hsi
  have hcd : (!decide (n.val ≤ (JInt.wrap .i64 (ys.length : Int) - di + one).val)) = false := by
    rw [hrd]; simp only [Bool.not_eq_false', decide_eq_true_eq]; clear hrs hsrc hdest; omega
  have hcs : (!decide (n.val ≤ (JInt.wrap .i64 (xs.length : Int) - si + one).val)) = false := by
    rw [hrs]; simp only [Bool.not_eq_false', decide_eq_true_eq]; clear hrd hcd hsrc hdest; omega
  have hld : (heapLength dest).run heap = .ok (JInt.wrap .i64 ys.length, heap) := by
    simp only [heapLength_run, hdest]
  have hls : (heapLength src).run heap = .ok (JInt.wrap .i64 xs.length, heap) := by
    simp only [heapLength_run, hsrc]
  have hwin := heapCopyReferences_window_run heap dest src xs ys hsrc hdest di si n
    hn0 hdi hde hsi hse
  rw [heapCheckedCopy_positive_eq _ _ _ _ _ _ hn]
  simp only [vector_bind_run, heapBounds_in heap dest ys hdest di hdi hdy,
    heapBounds_in heap src xs hsrc si hsi hsx, hld, hls, hcd, hcs,
    Bool.false_eq_true, ite_false, hwin, vector_pure_run]

theorem collectTo_nil {Tag : Type} (ie : HeapArray Tag → α → Bool)
    (st : HeapArray Tag → α → I → VectorM α Unit) (wd : HeapArray Tag → α → I → VectorM α (HeapArray Tag))
    (dest : HeapArray Tag) (offs : I) :
    collectTo (listIterator (m := VectorM α) []) ie st wd dest offs [] = pure dest := by
  rw [collectTo]
  rfl

theorem collectTo_cons {Tag : Type} (ie : HeapArray Tag → α → Bool)
    (st : HeapArray Tag → α → I → VectorM α Unit) (wd : HeapArray Tag → α → I → VectorM α (HeapArray Tag))
    (dest : HeapArray Tag) (offs : I) (x : α) (t : List α) :
    collectTo (listIterator (m := VectorM α) []) ie st wd dest offs (x :: t) =
      if ie dest x then (st dest x offs >>= fun _ =>
        collectTo (listIterator (m := VectorM α) []) ie st wd dest (offs + one) t)
      else (wd dest x offs >>= fun new =>
        collectTo (listIterator (m := VectorM α) []) ie st wd new (offs + one) t) := by
  rw [collectTo]
  rfl

theorem heapArrayUndef_dims_run {Tag : Type} (layout : Tag → MemoryLayout) (t : Tag) (dims : List Nat)
    (hfit : heapDimensionsFit dims = true) (heap : VectorHeap α) :
    (heapArrayUndef (fun t => some (layout t)) t (dims.map (fun n : Nat => JInt.wrap .i64 (Int.ofNat n)))).run heap =
      allocOutcome (layout t) t (dims.map (fun n : Nat => (n : Int))) heap := by
  rw [heapArrayUndef_run _ t (layout t) rfl, dims_wrap_val dims hfit]

theorem typedSimilar_run {Tag : Type} (layout : Tag → MemoryLayout) (dest : HeapArray Tag) (t : Tag)
    (heap : VectorHeap α) (hfit : heapDimensionsFit dest.dimensions = true) :
    (typedSimilar (fun t => some (layout t)) dest t : VectorM α (HeapArray Tag)).run heap =
      allocOutcome (layout t) t (dest.dimensions.map (fun n : Nat => (n : Int))) heap := by
  unfold typedSimilar heapAllocateArray
  simp only [hfit, Bool.not_true, Bool.false_eq_true, ite_false]
  exact heapArrayUndef_dims_run layout t _ hfit heap

/-- Dimensions whose allocation succeeds have fewer than `2^63` elements. -/
theorem dims_prod_lt {Tag : Type} (layout : Tag → MemoryLayout) (t : Tag) (dims : List Nat)
    (hfit : heapDimensionsFit dims = true)
    (herr : arrayAllocError (layout t) (dims.map (fun n : Nat => (n : Int))) = none) :
    dims.prod < 2 ^ 63 := by
  have hrun := heapArrayUndef_dims_run (α := Unit) layout t dims hfit []
  unfold allocOutcome at hrun
  rw [herr] at hrun
  have h2 := (heapArrayUndef_post _ t _ [] _ _ hrun).2
  simp only [dims_cast_toNat] at h2
  exact h2


theorem set_last {β : Type} (l : List β) (w v : β) : (l ++ [w]).set l.length v = l ++ [v] := by
  simp

theorem getElem?_last {β : Type} (l : List β) (w : β) : (l ++ [w])[l.length]? = some w := by
  simp

theorem offs_val (p : Nat) (hp : p + 1 < 2 ^ 63) : (JInt.wrap .i64 ((p : Int) + 1)).val = p + 1 :=
  ival_wrap _ (by omega)

theorem offs_succ (p : Nat) (hp : p + 2 < 2 ^ 63) :
    JInt.wrap .i64 ((p : Int) + 1) + one = JInt.wrap .i64 (((p + 1 : Nat) : Int) + 1) := by
  apply Subtype.ext
  show (JInt.wrap .i64 ((p : Int) + 1) + one).val = (JInt.wrap .i64 (((p + 1 : Nat) : Int) + 1)).val
  rw [ival_add _ _ (by rw [offs_val p (by omega), ival_one]; omega), offs_val p (by omega),
    offs_val (p + 1) (by omega), ival_one]
  omega

theorem offs_pred (p : Nat) (hp : p + 1 < 2 ^ 63) :
    (JInt.wrap .i64 ((p : Int) + 1) - one).val = p := by
  rw [ival_sub _ _ (by rw [offs_val p hp, ival_one]; omega), offs_val p hp, ival_one]
  omega

/-- The store `dest[offs] = x` into the first unassigned slot. -/
theorem typedSet_prefix_run {Tag : Type} (heap : VectorHeap α) (dest : HeapArray Tag)
    (pre : List α) (k : Nat) (x : α) (hs : heap[dest.handle]? = some (pre.map some ++ List.replicate k none))
    (hk : 0 < k) (offs : I) (hv : offs.val = pre.length + 1) :
    (typedSet dest x offs).run heap =
      .ok ((), heap.set dest.handle ((pre ++ [x]).map some ++ List.replicate (k - 1) none)) := by
  have hlen : ((pre.map some ++ List.replicate k none).length : Int) = pre.length + k := by simp
  unfold typedSet
  rw [heapSet_run heap dest.handle _ hs _ (by rw [hv]; omega) (by rw [hv, hlen]; omega) x]
  have hi : (offs.val - 1).toNat = (pre.map some).length := by
    rw [hv]; simp
  rw [hi, List.length_map, set_prefix_slot pre x k hk]

/-- The checked `copyto!(new, 1, dest, 1, p)` of `setindex_widen_up_to` into the fresh array
allocated last. -/
theorem widenCopy_run {Tag : Type} (heap : VectorHeap α) (new dest : HeapArray Tag)
    (pre : List α) (k : Nat) (hs : heap[dest.handle]? = some (pre.map some ++ List.replicate k none))
    (hnew : new.handle = heap.length) (hP : pre.length + k < 2 ^ 63) (o n : I) (ho : o.val = 1)
    (hn : n.val = pre.length) :
    (heapRangeCopy new o dest o n).run (heap ++ [List.replicate (pre.length + k) none]) =
      .ok ((), heap ++ [pre.map some ++ List.replicate k none]) := by
  by_cases h0 : pre.length = 0
  · have hpre : pre = [] := List.eq_nil_of_length_eq_zero h0
    subst hpre
    rw [heapRangeCopy_zero_run _ _ _ _ _ _ (by rw [hn]; rfl)]
    simp
  · have hd : (heap ++ [List.replicate (pre.length + k) none])[new.handle]? =
        some (List.replicate (pre.length + k) none) := by rw [hnew]; exact getElem?_last _ _
    have hlt : dest.handle < heap.length := by
      obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.mp hs; exact hl
    have hsrc : (heap ++ [List.replicate (pre.length + k) none])[dest.handle]? =
        some (pre.map some ++ List.replicate k none) := by
      rw [List.getElem?_append_left hlt]; exact hs
    have hl1 : (pre.map some ++ List.replicate k none).length < 9223372036854775808 := by
      simp only [List.length_append, List.length_map, List.length_replicate]; omega
    have hl2 : (List.replicate (pre.length + k) (none : Option α)).length < 9223372036854775808 := by
      simp only [List.length_replicate]; omega
    have hlen1 : ((pre.map some ++ List.replicate k none).length : Int) = pre.length + k := by
      simp only [List.length_append, List.length_map, List.length_replicate]; omega
    have hlen2 : ((List.replicate (pre.length + k) (none : Option α)).length : Int) = pre.length + k := by
      simp only [List.length_replicate]; omega
    unfold heapRangeCopy
    rw [vector_bind_run, heapCheckedCopy_window_run' _ new.handle dest.handle _ _ hsrc hd
      hl1 hl2 o o n (by rw [hn]; omega) (by rw [ho]; omega)
      (by rw [hn, ho, hlen2]; omega) (by rw [ho]; omega) (by rw [hn, ho, hlen1]; omega)]
    simp only [vector_pure_run, hn, ho]
    rw [hnew, set_last]
    have := widen_copy_window pre k
    simpa using this


/-- `setindex_widen_up_to(dest, x, offs)` when the joined element type can be allocated. -/
theorem typedWiden_ok_run {Tag : Type} (layout : Tag → MemoryLayout) (L : TypeLattice Tag α)
    (heap : VectorHeap α) (dest : HeapArray Tag) (pre : List α) (k : Nat) (x : α)
    (hs : heap[dest.handle]? = some (pre.map some ++ List.replicate k none))
    (hfit : heapDimensionsFit dest.dimensions = true) (hprod : dest.dimensions.prod = pre.length + k)
    (hk : 0 < k) (hP : pre.length + k < 2 ^ 63) (offs : I) (hv : offs.val = pre.length + 1)
    (hae : arrayAllocError (layout (L.join dest.elementType (L.typeof x)))
      (dest.dimensions.map (fun n : Nat => (n : Int))) = none) :
    (typedWiden (fun t => some (layout t)) L dest x offs).run heap =
      .ok (⟨heap.length, L.join dest.elementType (L.typeof x), dest.dimensions,
          dest.dimensions.map (fun n => (1, n))⟩,
        heap ++ [(pre ++ [x]).map some ++ List.replicate (k - 1) none]) := by
  have hn : (offs - one).val = pre.length := by
    have hb := ival_bounds offs
    rw [ival_sub _ _ (by rw [hv, ival_one]; omega), hv, ival_one]; omega
  have hsim := typedSimilar_run (α := α) layout dest (L.join dest.elementType (L.typeof x)) heap hfit
  unfold allocOutcome at hsim
  rw [hae, dims_cast_toNat] at hsim
  dsimp only at hsim
  rw [hprod] at hsim
  have hcopy := widenCopy_run heap ⟨heap.length, L.join dest.elementType (L.typeof x),
      dest.dimensions, dest.dimensions.map (fun n => (1, n))⟩ dest pre k hs rfl hP one (offs - one)
      ival_one hn
  have hset := typedSet_prefix_run (heap ++ [pre.map some ++ List.replicate k none])
      ⟨heap.length, L.join dest.elementType (L.typeof x),
      dest.dimensions, dest.dimensions.map (fun n => (1, n))⟩ pre k x (getElem?_last _ _) hk offs hv
  rw [set_last] at hset
  unfold typedWiden setindexWiden
  simp only [vector_bind_run, vector_pure_run, hsim, hcopy, hset]

theorem typedWiden_error_run {Tag : Type} (layout : Tag → MemoryLayout) (L : TypeLattice Tag α)
    (heap : VectorHeap α) (dest : HeapArray Tag) (x : α) (offs : I) (e : Error)
    (hfit : heapDimensionsFit dest.dimensions = true)
    (hae : arrayAllocError (layout (L.join dest.elementType (L.typeof x)))
      (dest.dimensions.map (fun n : Nat => (n : Int))) = some e) :
    (typedWiden (fun t => some (layout t)) L dest x offs).run heap = .error e := by
  have hsim := typedSimilar_run (α := α) layout dest (L.join dest.elementType (L.typeof x)) heap hfit
  unfold allocOutcome at hsim
  rw [hae] at hsim
  unfold typedWiden setindexWiden
  simp only [vector_bind_run, vector_pure_run, hsim]


/-- The `collect_to!` loop over the remaining values `xs`, from a general offset. -/
theorem typedCollectTo_main {Tag : Type} (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) :
    ∀ (xs : List α) (heap : VectorHeap α) (dest : HeapArray Tag) (pre : List α) (k : Nat) (offs : I),
    (xs ≠ [] → offs.val = pre.length + 1) →
    heap[dest.handle]? = some (pre.map some ++ List.replicate k none) →
    heapDimensionsFit dest.dimensions = true → dest.dimensions.prod = pre.length + k →
    arrayAllocError (layout dest.elementType) (dest.dimensions.map (fun n : Nat => (n : Int))) = none →
    xs.length ≤ k →
    (∀ v ∈ pre, L.isa v dest.elementType = true) →
    (∀ e, firstAllocError layout (dest.dimensions.map (fun n : Nat => (n : Int)))
        (wideningTypes L dest.elementType xs) = some e →
      (typedCollectTo (fun t => some (layout t)) L dest offs xs).run heap = .error e) ∧
    (firstAllocError layout (dest.dimensions.map (fun n : Nat => (n : Int)))
        (wideningTypes L dest.elementType xs) = none →
      ∃ r next, (typedCollectTo (fun t => some (layout t)) L dest offs xs).run heap = .ok (r, next) ∧
        next[r.handle]? = some ((pre ++ xs).map some ++ List.replicate (k - xs.length) none) ∧
        r.dimensions = dest.dimensions ∧
        (∀ v ∈ pre ++ xs, L.isa v r.elementType = true) ∧
        ((∀ v ∈ xs, L.isa v dest.elementType = true) → r = dest) ∧
        heap.length ≤ next.length ∧
        (∀ h, h < heap.length → h ≠ dest.handle → next[h]? = heap[h]?)) := by
  intro xs
  induction xs with
  | nil =>
    intro heap dest pre k offs _ _ _ _ _ _ hpre
    have hrun : (typedCollectTo (fun t => some (layout t)) L dest offs ([] : List α)).run heap =
        .ok (dest, heap) := by
      unfold typedCollectTo; rw [collectTo_nil]; rfl
    refine ⟨fun e he => by simp [wideningTypes, firstAllocError] at he, fun _ => ?_⟩
    refine ⟨dest, heap, hrun, ?_, rfl, ?_, fun _ => rfl, Nat.le_refl _, fun _ _ _ => rfl⟩
    · simpa using ‹heap[dest.handle]? = _›
    · simpa using hpre
  | cons x t ih =>
    intro heap dest pre k offs hvi hs hfit hprod herr hk hpre
    have hv := hvi (List.cons_ne_nil x t)
    have hP0 := dims_prod_lt layout dest.elementType dest.dimensions hfit herr
    have hP : pre.length + k < 2 ^ 63 := by rw [← hprod]; exact hP0
    have hk0 : 0 < k := by simp at hk; omega
    have hv' : t ≠ [] → (offs + one).val = (pre ++ [x]).length + 1 := by
      intro ht
      have ht1 : 1 ≤ t.length := List.length_pos_iff.mpr ht
      have hk2 : t.length + 1 ≤ k := by simpa using hk
      have hb := ival_bounds offs
      rw [ival_add _ _ (by rw [hv, ival_one]; omega), hv, ival_one]
      simp only [List.length_append, List.length_singleton]; omega
    have hlt : dest.handle < heap.length := by
      obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.mp hs; exact hl
    have hkk : k - 1 - t.length = k - (x :: t).length := by simp; omega
    have happ : (pre ++ [x]) ++ t = pre ++ x :: t := by simp
    by_cases hx : L.isa x dest.elementType = true
    · have htypes : wideningTypes L dest.elementType (x :: t) = wideningTypes L dest.elementType t := by
        simp [wideningTypes, hx]
      have hset := typedSet_prefix_run heap dest pre k x hs hk0 offs hv
      have hrun : (typedCollectTo (fun t => some (layout t)) L dest offs (x :: t)).run heap =
          (typedCollectTo (fun t => some (layout t)) L dest (offs + one) t).run
            (heap.set dest.handle ((pre ++ [x]).map some ++ List.replicate (k - 1) none)) := by
        unfold typedCollectTo
        rw [collectTo_cons]
        simp only [hx, ite_true, vector_bind_run, hset]
      have hs1 : (heap.set dest.handle ((pre ++ [x]).map some ++ List.replicate (k - 1) none))[dest.handle]? =
          some ((pre ++ [x]).map some ++ List.replicate (k - 1) none) := List.getElem?_set_self hlt
      have hpre1 : ∀ v ∈ pre ++ [x], L.isa v dest.elementType = true := by
        intro v hv1
        rcases List.mem_append.mp hv1 with h | h
        · exact hpre v h
        · rw [List.mem_singleton.mp h]; exact hx
      obtain ⟨ih1, ih2⟩ := ih _ dest (pre ++ [x]) (k - 1) (offs + one) hv' hs1 hfit
        (by rw [hprod]; simp; omega) herr (by simp at hk; omega) hpre1
      rw [htypes, hrun]
      refine ⟨ih1, fun he => ?_⟩
      obtain ⟨r, next, hr, hnr, hdim, hisa, hsame, hlen, hoth⟩ := ih2 he
      rw [happ, hkk] at hnr
      rw [happ] at hisa
      refine ⟨r, next, hr, hnr, hdim, hisa,
        fun hall => hsame (fun v hv2 => hall v (List.mem_cons_of_mem _ hv2)), ?_, ?_⟩
      · simpa using hlen
      · intro h hh hne
        rw [hoth h (by simpa using hh) hne, List.getElem?_set_ne (Ne.symm hne)]
    · have hxf : L.isa x dest.elementType = false := by simpa using hx
      have hrun0 : ∀ (w : VectorHeap α) (res : Except Error (HeapArray Tag × VectorHeap α)),
          (typedWiden (fun t => some (layout t)) L dest x offs).run heap = res →
          (typedCollectTo (fun t => some (layout t)) L dest offs (x :: t)).run heap =
            match res with
            | .error e => .error e
            | .ok (new, w') => (typedCollectTo (fun t => some (layout t)) L new (offs + one) t).run w' := by
        intro _ res hres
        unfold typedCollectTo
        rw [collectTo_cons]
        simp only [hxf, Bool.false_eq_true, ite_false, vector_bind_run, hres]
        cases res <;> rfl
      have htypes : wideningTypes L dest.elementType (x :: t) =
          L.join dest.elementType (L.typeof x) ::
            wideningTypes L (L.join dest.elementType (L.typeof x)) t := by
        simp [wideningTypes, hxf]
      rw [htypes]
      cases hae : arrayAllocError (layout (L.join dest.elementType (L.typeof x)))
          (dest.dimensions.map (fun n : Nat => (n : Int))) with
      | some e =>
        have hw := typedWiden_error_run layout L heap dest x offs e hfit hae
        rw [hrun0 heap _ hw]
        refine ⟨fun e' he => ?_, fun he => ?_⟩
        · simp only [firstAllocError, hae] at he
          cases he; rfl
        · simp [firstAllocError, hae] at he
      | none =>
        have hw := typedWiden_ok_run layout L heap dest pre k x hs hfit hprod hk0 hP offs hv hae
        rw [hrun0 heap _ hw]
        have hs1 : (heap ++ [(pre ++ [x]).map some ++ List.replicate (k - 1) none])[heap.length]? =
            some ((pre ++ [x]).map some ++ List.replicate (k - 1) none) := getElem?_last _ _
        have hpre1 : ∀ v ∈ pre ++ [x], L.isa v (L.join dest.elementType (L.typeof x)) = true := by
          intro v hv1
          rcases List.mem_append.mp hv1 with h | h
          · exact L.isa_join_left v _ _ (hpre v h)
          · rw [List.mem_singleton.mp h]; exact L.isa_join_right x _ _ (L.isa_typeof x)
        obtain ⟨ih1, ih2⟩ := ih _ ⟨heap.length, L.join dest.elementType (L.typeof x),
            dest.dimensions, dest.dimensions.map (fun n => (1, n))⟩ (pre ++ [x]) (k - 1) (offs + one)
            hv' hs1 hfit (by rw [hprod]; simp; omega) hae (by simp at hk; omega) hpre1
        refine ⟨fun e he => ih1 e (by simpa [firstAllocError, hae] using he), fun he => ?_⟩
        obtain ⟨r, next, hr, hnr, hdim, hisa, _, hlen, hoth⟩ :=
          ih2 (by simpa [firstAllocError, hae] using he)
        rw [happ, hkk] at hnr
        rw [happ] at hisa
        refine ⟨r, next, hr, hnr, hdim, hisa, fun hall => ?_, ?_, ?_⟩
        · exact absurd (hall x (List.mem_cons_self ..)) (by simp [hxf])
        · simp at hlen; omega
        · intro h hh hne
          have hne' : h ≠ heap.length := by omega
          rw [hoth h (by simp; omega) hne', List.getElem?_append_left hh]

theorem collectToSpec : JuliaLean.Proofs.base.array.CollectToSpec := by
  intro Tag α layout L heap dest pre xs k ints hs hfit hprod herr hk hpre types run
  have hP0 := dims_prod_lt layout dest.elementType dest.dimensions hfit herr
  exact typedCollectTo_main layout L xs heap dest pre k _
    (fun hne => offs_val pre.length (by
      have := List.length_pos_iff.mpr hne
      omega)) hs hfit
    hprod herr hk hpre


theorem collectWithFirstSpec : JuliaLean.Proofs.base.array.CollectWithFirstSpec := by
  intro Tag α layout L heap dest v1 itr xs k ints hs hfit hprod herr hk hv1 types run
  have hP0 := dims_prod_lt layout dest.elementType dest.dimensions hfit herr
  have hk0 : 0 < k := by omega
  have hs0 : heap[dest.handle]? = some (([] : List α).map some ++ List.replicate k none) := by
    simpa using hs
  have hset := typedSet_prefix_run heap dest [] k v1 hs0 hk0 one (by rw [ival_one]; rfl)
  have hlt : dest.handle < heap.length := by
    obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.mp hs; exact hl
  have hrun : run = (typedCollectTo (fun t => some (layout t)) L dest (one + one) xs).run
      (heap.set dest.handle (([] ++ [v1]).map some ++ List.replicate (k - 1) none)) := by
    show (typedCollectWithFirst (fun t => some (layout t)) L dest v1 itr xs).run heap = _
    unfold typedCollectWithFirst collectWithFirstArray
    simp only [vector_bind_run, vector_pure_run, hset]
  have hs1 : (heap.set dest.handle (([] ++ [v1]).map some ++ List.replicate (k - 1) none))[dest.handle]? =
      some (([] ++ [v1]).map some ++ List.replicate (k - 1) none) := List.getElem?_set_self hlt
  have hpre : ∀ v ∈ ([] : List α) ++ [v1], L.isa v dest.elementType = true := by
    intro v hv; simp at hv; rw [hv]; exact hv1
  obtain ⟨ih1, ih2⟩ := typedCollectTo_main layout L xs _ dest ([] ++ [v1]) (k - 1) (one + one)
    (fun _ => by rw [ival_add _ _ (by rw [ival_one]; omega), ival_one]; simp) hs1 hfit
    (by rw [hprod]; simp; omega) herr (by omega) hpre
  rw [hrun]
  refine ⟨ih1, fun he => ?_⟩
  obtain ⟨r, next, hr, hnr, hdim, hisa, hsame, _, _⟩ := ih2 he
  refine ⟨r, next, hr, ?_, hdim, ?_, hsame⟩
  · simpa using hnr
  · simpa using hisa

theorem collectToWideningSpec : JuliaLean.Proofs.base.array.CollectToWideningSpec :=
  ⟨collectToSpec, collectWithFirstSpec⟩
end
end
end opusGrowth
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
attribute [local irreducible] JInt.wrap wrapInt

theorem heapAllocateArray_dims_run {Tag : Type} (layout : Tag → MemoryLayout) (t : Tag)
    (shape : List Nat) (hfit : heapDimensionsFit shape = true) (heap : VectorHeap α) :
    (heapAllocateArray (fun t => some (layout t)) t shape : VectorM α (HeapArray Tag)).run heap =
      allocOutcome (layout t) t (shape.map (fun n : Nat => (n : Int))) heap := by
  unfold heapAllocateArray
  simp only [hfit, Bool.not_true, Bool.false_eq_true, ite_false]
  exact heapArrayUndef_dims_run layout t _ hfit heap

/-- The common post-condition of the three sized collectors, from their run equations. -/
theorem sized_post {Tag : Type} (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) (et : Tag)
    (shape : List Nat) (xs : List α) (heap : VectorHeap α)
    (hfit : heapDimensionsFit shape = true) (hlen : shape.prod = xs.length)
    (m : List α → VectorM α (HeapArray Tag))
    (hnil : xs = [] → (m xs).run heap =
      (heapAllocateArray (fun t => some (layout t)) et shape : VectorM α (HeapArray Tag)).run heap)
    (hcons : ∀ x t, xs = x :: t → (m xs).run heap =
      match (heapAllocateArray (fun t => some (layout t)) (L.typeof x) shape :
          VectorM α (HeapArray Tag)).run heap with
      | .error e => .error e
      | .ok (d, h') => (typedCollectWithFirst (fun t => some (layout t)) L d x xs t).run h') :
    let ints := shape.map (fun n : Nat => (n : Int))
    (xs = [] → (m xs).run heap = allocOutcome (layout et) et ints heap) ∧
    (∀ x t, xs = x :: t →
      let types := L.typeof x :: wideningTypes L (L.typeof x) t
      (∀ e, firstAllocError layout ints types = some e → (m xs).run heap = .error e) ∧
      (firstAllocError layout ints types = none →
        ∃ r next, (m xs).run heap = .ok (r, next) ∧
          next[r.handle]? = some (xs.map some) ∧ r.dimensions = shape ∧
          (∀ v ∈ xs, L.isa v r.elementType = true) ∧
          ((∀ v ∈ t, L.isa v (L.typeof x) = true) → r.elementType = L.typeof x))) := by
  intro ints
  refine ⟨fun h0 => by rw [hnil h0, heapAllocateArray_dims_run layout et shape hfit], ?_⟩
  intro x t hxs types
  have hrun := hcons x t hxs
  rw [heapAllocateArray_dims_run layout (L.typeof x) shape hfit] at hrun
  unfold allocOutcome at hrun
  cases hae : arrayAllocError (layout (L.typeof x)) ints with
  | some e =>
    rw [hae] at hrun
    refine ⟨fun e' he => ?_, fun he => ?_⟩
    · simp only [types, firstAllocError, hae] at he
      cases he; exact hrun
    · simp [types, firstAllocError, hae] at he
  | none =>
    rw [hae] at hrun
    dsimp only at hrun
    rw [dims_cast_toNat] at hrun
    have hk : shape.prod = t.length + 1 := by rw [hlen, hxs]; simp
    have hae' : arrayAllocError (layout (L.typeof x))
        ((⟨heap.length, L.typeof x, shape, shape.map (fun n => (1, n))⟩ : HeapArray Tag).dimensions.map
          (fun n : Nat => (n : Int))) = none := hae
    obtain ⟨h1, h2⟩ := collectWithFirstSpec Tag α layout L (heap ++ [List.replicate shape.prod none])
      ⟨heap.length, L.typeof x, shape, shape.map (fun n => (1, n))⟩ x xs t shape.prod
      (getElem?_last _ _) hfit rfl hae' (by omega) (L.isa_typeof x)
    refine ⟨fun e he => ?_, fun he => ?_⟩
    · rw [hrun]
      exact h1 e (by simpa [types, firstAllocError, hae] using he)
    · obtain ⟨r, next, hr, hnr, hdim, hisa, hsame⟩ := h2 (by simpa [types, firstAllocError, hae] using he)
      refine ⟨r, next, hrun.trans hr, ?_, hdim, ?_, fun hall => ?_⟩
      · rw [hnr, hxs, hk]; simp
      · rw [hxs]; exact hisa
      · rw [hsame hall]

theorem collectSizedSpec : JuliaLean.Proofs.base.array.CollectSizedSpec := by
  intro Tag α layout L et shape xs heap hfit hlen ints lay m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact sized_post layout L et shape xs heap hfit hlen _
      (fun h0 => by subst h0; rfl)
      (fun x t hxs => by
        subst hxs
        simp only [lay, typedCollectSized, collectUnknownSized, vector_bind_run, vector_pure_run, bind_pure]
        rcases hR : (heapAllocateArray (fun t => some (layout t)) (L.typeof x) shape :
            VectorM α (HeapArray Tag)).run heap with _ | ⟨d, h'⟩ <;>
          simp [hR, Bind.bind, Except.bind, StateT.bind])
  · exact sized_post layout L et shape xs heap hfit hlen _
      (fun h0 => by subst h0; rfl)
      (fun x t hxs => by
        subst hxs
        simp only [lay, typedCollectGenerator, collectGenerator, Bool.false_eq_true, ite_false,
          pure_bind, bind_pure, vector_bind_run, vector_pure_run]
        rcases hR : (heapAllocateArray (fun t => some (layout t)) (L.typeof x) shape :
            VectorM α (HeapArray Tag)).run heap with _ | ⟨d, h'⟩ <;>
          simp [hR])
  · exact sized_post layout L et shape xs heap hfit hlen _
      (fun h0 => by subst h0; rfl)
      (fun x t hxs => by
        subst hxs
        simp only [lay, typedCollect, JuliaLean.base.array.collect, typedCollectSized, collectUnknownSized,
          vector_bind_run, vector_pure_run, bind_pure]
        rcases hR : (heapAllocateArray (fun t => some (layout t)) (L.typeof x) shape :
            VectorM α (HeapArray Tag)).run heap with _ | ⟨d, h'⟩ <;>
          simp [hR, Bind.bind, Except.bind, StateT.bind])
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

/-- The complete unknown-size part of the typed-collection target is already established. -/
theorem allocationUnknownTypedCollectionPartial : CompleteUnknownCollectionSpec :=
  opusGrowth.completeUnknownCollectionSpec

/-- Type-changing conversion invokes precisely the native constructor path. -/
theorem allocationConvertChangesType {Tag α : Type} [DecidableEq Tag]
    (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (src : HeapArray Tag) (h : src.elementType ≠ target) :
    convertArray (fun a => a.elementType == target) id
      (heapArrayConstructor layout target check convert) pure src =
        heapArrayConstructor layout target check convert src := by
  simp only [convertArray, beq_iff_eq, h, ite_false, bind_pure]

/-- The exact copy phase of a sized collector after its length conversion and allocation. -/
theorem allocationSizedLengthAfterAllocation {Tag α β X Z : Type}
    (layout : Tag → Option MemoryLayout) (values : X → List β) (length : X → Z)
    (toInt : Z → Except Error I) (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (hcopy : SizedCopyLaw values convert copy)
    (target : Tag) (itr : X) (heap : VectorHeap α) (n : I)
    (hconvert : toInt (length itr) = .ok n)
    (hsize : (values itr).length < 2 ^ 63)
    (ha : (heapVectorAllocate layout target n).run heap =
      freshShapeAllocation target [(values itr).length] heap) :
    (sizedLengthCollect layout length toInt copy target itr).run heap =
      ((values itr).mapM convert).map
        (fun converted => collectedShape target [(values itr).length] converted heap) := by
  simp only [sizedLengthCollect, collectTyped, collectSized, similarShapeLength,
    arrayForLength, vector_bind_run, vector_pure_run, vector_lift_run, hconvert, Except.map, ha,
    freshShapeAllocation]
  exact sizedCopy_fresh values convert copy hcopy target [(values itr).length] itr heap
    (by simp only [List.prod_cons, List.prod_nil, Nat.mul_one])
    (by simpa only [List.prod_cons, List.prod_nil, Nat.mul_one] using hsize)

/-- A failed length conversion is observed before sized-collection allocation or copying. -/
theorem allocationSizedLengthConversionError {Tag α X Z : Type}
    (layout : Tag → Option MemoryLayout) (length : X → Z)
    (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) (heap : VectorHeap α) (e : Error)
    (he : toInt (length itr) = .error e) :
    (sizedLengthCollect layout length toInt copy target itr).run heap = .error e := by
  simp only [sizedLengthCollect, collectTyped, collectSized, similarShapeLength,
    arrayForLength, vector_bind_run, vector_pure_run, vector_lift_run, he, Except.map]

/-- A failed sized-collection allocation is observed before copying any iterator value. -/
theorem allocationSizedLengthAllocationError {Tag α X Z : Type}
    (layout : Tag → Option MemoryLayout) (length : X → Z)
    (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) (heap : VectorHeap α) (n : I) (e : Error)
    (hconvert : toInt (length itr) = .ok n)
    (he : (heapVectorAllocate layout target n).run heap = .error e) :
    (sizedLengthCollect layout length toInt copy target itr).run heap = .error e := by
  simp only [sizedLengthCollect, collectTyped, collectSized, similarShapeLength,
    arrayForLength, vector_bind_run, vector_pure_run, vector_lift_run, hconvert, Except.map, he]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion2
open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Completion2

/-- Typed collection discovers its iterator size before dispatch and forwards the original type and iterator. -/
def TypedCollectProtocol : Prop :=
  ∀ (T X S : Type) (t : T) (itr : X) (size : S) (initial : List Nat),
    (JuliaLean.base.array.Completion2.collectTyped (fun _ => call 0 (.ok size))
      (fun t x s => call 1 (.ok (t, x, s))) t itr).run initial =
        (.ok (t, itr, size), initial ++ [0, 1])

/-- Comprehension allocation discovers shape once before forwarding type, size trait and unchanged shape to the selected allocator. -/
def ArrayForProtocol : Prop :=
  ∀ (T X S Shape : Type) (t : T) (itr : X) (size : S) (shape : Shape) (initial : List Nat),
    (JuliaLean.base.array.Completion2.arrayFor (fun _ _ => call 0 (.ok shape))
      (fun t s shape => call 1 (.ok (t, s, shape))) t itr size).run initial =
        (.ok (t, size, shape), initial ++ [0, 1])

/-- Generic collection discovers element-type and size traits in order, using the singleton 1:1 range as its allocation template. -/
def CollectTraitsProtocol : Prop :=
  ∀ (X ET SZ : Type) (itr : X) (et : ET) (sz : SZ) (initial : List Nat),
    (JuliaLean.base.array.Completion2.collect (fun _ => call 0 (.ok et))
      (fun _ => call 1 (.ok sz)) (fun c x e s => call 2 (.ok (c, x, e, s))) itr).run initial =
        (.ok (⟨one, one⟩, itr, et, sz), initial ++ [0, 1, 2])

/-- Array collection forwards its original array and discovered axes to the index-shape collector, preserving axis discovery effects. -/
def CollectArrayAxesProtocol : Prop :=
  ∀ (A Axes : Type) (a : A) (axes : Axes) (initial : List Nat),
    (JuliaLean.base.array.Completion2.collectArray (fun _ => call 0 (.ok axes))
      (fun axes a => call 1 (.ok (axes, a))) a).run initial =
        (.ok (axes, a), initial ++ [0, 1])

/-- Collection with a template preserves the supplied template and iterator and discovers the two traits in source order. -/
def CollectSimilarProtocol : Prop :=
  ∀ (C X ET SZ : Type) (c : C) (itr : X) (et : ET) (sz : SZ) (initial : List Nat),
    (JuliaLean.base.array.Completion2.collectSimilar (fun _ => call 0 (.ok et))
      (fun _ => call 1 (.ok sz)) (fun c x e s => call 2 (.ok (c, x, e, s))) c itr).run initial =
        (.ok (c, itr, et, sz), initial ++ [0, 1, 2])

/-- A failed element-type observation is retained before length/axes discovery, allocation or copying. -/
def KnownSizedEltypeErrors : Prop :=
  ∀ (W X V Z Axes T C A Size : Type) (isLength : Size → Bool) (size : Size)
    (length : X → ExceptT Error (StateM W) V) (integer : V → Option Z)
    (axes : X → ExceptT Error (StateM W) Axes)
    (eltype : X → ExceptT Error (StateM W) T)
    (similar : C → T → X → Size → SizedShape Z Axes → ExceptT Error (StateM W) A)
    (copy : A → X → ExceptT Error (StateM W) A)
    (c : C) (itr : X) (before after : W) (error : Error),
    (eltype itr).run before = (.error error, after) →
    (JuliaLean.base.array.Completion2.collectKnownSized isLength size length integer axes eltype
      similar copy c itr).run before = (.error error, after)

/-- Unknown-sized collection propagates an element-type error before allocation or beginning iteration. -/
def KnownUnknownEltypeErrors : Prop :=
  ∀ (W X E T C A : Type) [ForIn (ExceptT Error (StateM W)) X E]
    (eltype : X → ExceptT Error (StateM W) T)
    (similar : C → T → X → ExceptT Error (StateM W) A)
    (push : A → E → ExceptT Error (StateM W) Unit)
    (c : C) (itr : X) (before after : W) (error : Error),
    (eltype itr).run before = (.error error, after) →
    (JuliaLean.base.array.Completion2.collectKnownUnknown eltype similar push c itr).run before =
      (.error error, after)

/-- Collection with a saved first element pushes it before resuming the iterator; a push error preserves its effects. -/
def CollectWithFirstPushErrors : Prop :=
  ∀ (W A E X St : Type) (push : A → E → ExceptT Error (StateM W) Unit)
    (grow : A → X → St → ExceptT Error (StateM W) A)
    (a : A) (value : E) (itr : X) (st : St) (before after : W) (error : Error),
    (push a value).run before = (.error error, after) →
    (JuliaLean.base.array.Completion2.collectWithFirst push grow a value itr st).run before =
      (.error error, after)

/-- Empty iteration returns the original destination without allocating; iteration errors preserve their complete state. -/
def GrowFirstEmptyAndErrors : Prop :=
  ∀ (W X E St T A : Type) (iterate : X → ExceptT Error (StateM W) (Option (E × St)))
    (typeof : E → T) (empty : A → T → ExceptT Error (StateM W) A)
    (push : A → E → ExceptT Error (StateM W) Unit)
    (grow : A → X → St → ExceptT Error (StateM W) A)
    (a : A) (itr : X) (before after : W),
    ((iterate itr).run before = (.ok none, after) →
      (JuliaLean.base.array.Completion2.growFirst iterate typeof empty push grow a itr).run before =
        (.ok a, after)) ∧
    (∀ error, (iterate itr).run before = (.error error, after) →
      (JuliaLean.base.array.Completion2.growFirst iterate typeof empty push grow a itr).run before =
        (.error error, after))

/-- Collect-to propagates an iteration error with its effects before any element store, index increment, widening or redispatch; no decreasing rank is required. -/
def CollectToIterationError : Prop :=
  ∀ (W A X E St Index : Type) (isElement : E → Bool)
    (set : A → E → Index → Exec W Unit) (increment : Index → Exec W Index)
    (widen : A → E → Index → Exec W A)
    (redispatch : A → X → Index → St → Exec W A)
    (dest : A) (itr : X) (index : Index) (st : St) (before after : W) (error : Error),
    collectToLoop (fun _ _ _ => some (.error error, after)) isElement set increment widen
      redispatch dest itr index st before = some (.error error, after)

/-- Grow-to reads the destination element type before any iteration; exceptions preserve state and divergent type discovery remains divergent. -/
def GrowToTypeDiscoveryError : Prop :=
  ∀ (W A X E St T : Type)
    (iterate : X → St → Exec W (Option (E × St))) (isElement : T → E → Bool)
    (push : A → E → Exec W Unit) (widen : A → E → Exec W A)
    (redispatch : A → X → St → Exec W A)
    (dest : A) (itr : X) (st : St) (before after : W) (error : Error),
    growTo (fun _ _ => some (.error error, after)) iterate isElement push widen redispatch
      dest itr st before = some (.error error, after) ∧
    growTo (fun _ _ => none) iterate isElement push widen redispatch
      dest itr st before = none
end JuliaLean.Proofs.base.array.Completion2


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- Widening observes the original container element type before joining types, creating a container, copying or pushing; the first failure retains its state. -/
def PushWidenEltypeErrors : Prop :=
  ∀ (W A E T N : Type) (eltype : A → ExceptT Error (StateM W) T) (typeof : E → T)
    (join : T → T → ExceptT Error (StateM W) T) (empty : A → T → ExceptT Error (StateM W) A)
    (length : A → ExceptT Error (StateM W) N) (sizehint : A → N → ExceptT Error (StateM W) A)
    (isSet : A → Bool) (union append : A → A → ExceptT Error (StateM W) Unit)
    (push : A → E → ExceptT Error (StateM W) Unit)
    (dest : A) (el : E) (before after : W) (error : Error),
    (eltype dest).run before = (.error error, after) →
    (JuliaLean.base.array.Completion3.pushWiden eltype typeof join empty length sizehint
      isSet union append push dest el).run before = (.error error, after)
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion4
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion4
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- The shaped iterator allocator forwards its selected element type and original axes unchanged to the type/axes-selected similar method. -/
def ArrayForShapeArguments : Prop :=
  ∀ (T Axes : Type) (t : T) (axes : Axes),
    JuliaLean.base.array.Completion4.arrayForShape (m := Id) (fun t axes => (t, axes)) t axes = (t, axes)

/-- Computing LinearIndices precedes reading its first index, storing the saved element, incrementing that index and resuming collection. -/
def CollectFirstLinearErrors : Prop :=
  ∀ (W A E X St Linear Index NextIndex R : Type)
    (linear : A → ExceptT Error (StateM W) Linear) (first : Linear → ExceptT Error (StateM W) Index)
    (set : A → E → Index → ExceptT Error (StateM W) Unit)
    (increment : Index → ExceptT Error (StateM W) NextIndex)
    (collect : A → X → NextIndex → St → ExceptT Error (StateM W) R)
    (a : A) (value : E) (itr : X) (st : St) (before after : W) (error : Error),
    (linear a).run before = (.error error, after) →
    (collectWithFirstArray linear first set increment collect a value itr st).run before =
      (.error error, after)

/-- Type joining precedes widened allocation, either LinearIndices construction, prefix copying and the new store. A type-join error preserves its effects. -/
def WidenTypeJoinErrors : Prop :=
  ∀ (W A E T Linear FirstIndex Index Count : Type)
    (elementType : A → T) (typeof : E → T) (join : T → T → ExceptT Error (StateM W) T)
    (similar : A → T → ExceptT Error (StateM W) A)
    (linear : A → ExceptT Error (StateM W) Linear) (first : Linear → ExceptT Error (StateM W) FirstIndex)
    (subtract : Index → FirstIndex → ExceptT Error (StateM W) Count)
    (copy : A → FirstIndex → A → FirstIndex → Count → ExceptT Error (StateM W) Unit)
    (set : A → E → Index → ExceptT Error (StateM W) Unit)
    (a : A) (el : E) (i : Index) (before after : W) (error : Error),
    (join (elementType a) (typeof el)).run before = (.error error, after) →
    (setindexWiden elementType typeof join similar linear first subtract copy set a el i).run before =
      (.error error, after)

/-- Length-bearing iterator allocation converts the length to Int before native allocation, preserving conversion errors, partial states and divergence. -/
def ArrayForLengthConversionFailures : Prop :=
  ∀ (State T Z : Type) (allocation : NativeAllocationBoundary State T)
    (toInt : Z → NativeCopyM (NativeCopyWorld State) I) (length : Z) (before : NativeCopyWorld State),
    FirstNativeFailure (toInt length)
      (JuliaLean.base.array.Completion4.arrayForLength allocation toInt length) before
end JuliaLean.Proofs.base.array.Completion4


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion6
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- Unknown-sized typed collection allocates an empty native Vector before
calling iterate or converting/pushing elements, retaining every allocation failure. -/
def UnknownCollectAllocationFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref E X : Type)
    [ForIn (NativeGrowthM State T) X E]
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (cast : E → Option T) (convert : E → NativeGrowthM State T E)
    (isAny : Bool) (asAny : E → T) (itr : X) (before : NativeGrowthWorld State T),
    FirstNativeFailure (nativeVectorUndef allocation zero)
      (JuliaLean.base.array.Completion6.collectUnknown layout elementType native ccall allocation access references
        cast convert isAny asAny itr) before

/-- In the length-bearing route, length discovery precedes Int conversion,
allocation and copying. Errors and divergence retain the original native world. -/
def SizedCollectLengthFailures : Prop :=
  ∀ (State T X Size V Z Axes A R : Type)
    (allocation : NativeAllocationBoundary State T) (embed : NativeCopyArray T → A)
    (isLength : Size → Bool) (length : X → NativeCopyM (NativeCopyWorld State) V)
    (integer : V → Option Z) (toInt : Z → NativeCopyM (NativeCopyWorld State) I)
    (axes : X → NativeCopyM (NativeCopyWorld State) Axes)
    (similar : Size → Axes → NativeCopyM (NativeCopyWorld State) A)
    (copy : A → X → NativeCopyM (NativeCopyWorld State) R)
    (itr : X) (size : Size) (before : NativeCopyWorld State),
    isLength size = true →
    FirstNativeFailure (length itr)
      (JuliaLean.base.array.Completion6.collectSized allocation embed isLength length integer toInt axes similar
        copy itr size) before
end JuliaLean.Proofs.base.array.Completion6


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- The unknown-size allocation starts an empty collection without altering prior objects.
Source: base/array.jl:711; src/genericmemory.c:75-102. -/
def ArrayForUnknownEmptyInvariant : Prop :=
  ∀ (α : Type) (layout : Option MemoryLayout) (before : MutableMemory α),
    match layout with
    | none => (arrayForUnknownRuntime (α := α) layout).run before =
        (.error (.typeError "GenericMemory"), before)
    | some _ => ∃ handle after,
        (arrayForUnknownRuntime (α := α) layout).run before = (.ok handle, after) ∧
        FreshVectorContents before after handle []

/-- This inference-only helper cannot return an iterator value at runtime.
The initial iterator's effects and failure are retained. A protocol-compliant
empty result throws nothing and a value/state pair reaches a non-Bool condition.
Source: base/array.jl:803-815; manual/control-flow.md:180-191. -/
def IteratorUpperBoundFailureInvariant : Prop :=
  ∀ (E World Iter State : Type)
    (run : Iter → Option State →
      JuliaLean.base.iterators.Exec E World (Option (JuliaLean.BootCov.JVal × State)))
    (itr : Iter) (before : World),
    let result := iteratorUpperBoundRuntime run itr before
    match run itr none before with
    | none => result = none
    | some (.error error, after) => result = some (.error (.inl error), after)
    | some (.ok none, after) => result = some (.error (.inr (.inl .thrownNothing)), after)
    | some (.ok (some _), after) => result = some (.error (.inr (.inl (.typeError "if"))), after)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array
theorem JuliaLean.Proofs.base.array.Completion2.TypedCollectProtocol_proven : JuliaLean.Proofs.base.array.Completion2.TypedCollectProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion2.TypedCollectProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectTyped, JuliaLean.base.array.collectTyped, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.ArrayForProtocol_proven : JuliaLean.Proofs.base.array.Completion2.ArrayForProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion2.ArrayForProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.arrayFor, JuliaLean.base.array.arrayFor, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.CollectTraitsProtocol_proven : JuliaLean.Proofs.base.array.Completion2.CollectTraitsProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion2.CollectTraitsProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collect, JuliaLean.base.array.collect, JuliaLean.base.array.one, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.CollectArrayAxesProtocol_proven : JuliaLean.Proofs.base.array.Completion2.CollectArrayAxesProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion2.CollectArrayAxesProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectArray, JuliaLean.base.array.collectArray, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.CollectSimilarProtocol_proven : JuliaLean.Proofs.base.array.Completion2.CollectSimilarProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion2.CollectSimilarProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectSimilar, JuliaLean.base.array.collectSimilar, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.KnownSizedEltypeErrors_proven : JuliaLean.Proofs.base.array.Completion2.KnownSizedEltypeErrors := by
  unfold JuliaLean.Proofs.base.array.Completion2.KnownSizedEltypeErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectKnownSized, JuliaLean.base.array.collectKnownSized, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.KnownUnknownEltypeErrors_proven : JuliaLean.Proofs.base.array.Completion2.KnownUnknownEltypeErrors := by
  unfold JuliaLean.Proofs.base.array.Completion2.KnownUnknownEltypeErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectKnownUnknown, JuliaLean.base.array.collectKnownUnknown, JuliaLean.base.array.push, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.CollectWithFirstPushErrors_proven : JuliaLean.Proofs.base.array.Completion2.CollectWithFirstPushErrors := by
  unfold JuliaLean.Proofs.base.array.Completion2.CollectWithFirstPushErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectWithFirst, JuliaLean.base.array.Completion2.grow, JuliaLean.base.array.collectWithFirst, JuliaLean.base.array.grow, JuliaLean.base.array.push, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.GrowFirstEmptyAndErrors_proven : JuliaLean.Proofs.base.array.Completion2.GrowFirstEmptyAndErrors := by
  unfold JuliaLean.Proofs.base.array.Completion2.GrowFirstEmptyAndErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.grow, JuliaLean.base.array.Completion2.growFirst, JuliaLean.base.array.empty, JuliaLean.base.array.grow, JuliaLean.base.array.growFirst, JuliaLean.base.array.push, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.CollectToIterationError_proven : JuliaLean.Proofs.base.array.Completion2.CollectToIterationError := by
  unfold JuliaLean.Proofs.base.array.Completion2.CollectToIterationError
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collectToLoop, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.GrowToTypeDiscoveryError_proven : JuliaLean.Proofs.base.array.Completion2.GrowToTypeDiscoveryError := by
  unfold JuliaLean.Proofs.base.array.Completion2.GrowToTypeDiscoveryError
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.growTo, JuliaLean.base.array.growTo, JuliaLean.base.array.push, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.PushWidenEltypeErrors_proven : JuliaLean.Proofs.base.array.Completion3.PushWidenEltypeErrors := by
  unfold JuliaLean.Proofs.base.array.Completion3.PushWidenEltypeErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.pushWiden, JuliaLean.base.array.empty, JuliaLean.base.array.push, JuliaLean.base.array.pushWiden, JuliaLean.base.array.sizehint, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.ArrayForShapeArguments_proven : JuliaLean.Proofs.base.array.Completion4.ArrayForShapeArguments := by
  unfold JuliaLean.Proofs.base.array.Completion4.ArrayForShapeArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.arrayForShape, JuliaLean.base.array.arrayForShape, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.CollectFirstLinearErrors_proven : JuliaLean.Proofs.base.array.Completion4.CollectFirstLinearErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.CollectFirstLinearErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.collect, JuliaLean.base.array.Completion4.collectWithFirstArray, JuliaLean.base.array.collect, JuliaLean.base.array.collectWithFirstArray, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.WidenTypeJoinErrors_proven : JuliaLean.Proofs.base.array.Completion4.WidenTypeJoinErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.WidenTypeJoinErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.setindexWiden, JuliaLean.base.array.setindexWiden, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion4.ArrayForLengthConversionFailures_proven : JuliaLean.Proofs.base.array.Completion4.ArrayForLengthConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion4.ArrayForLengthConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion4.arrayForLength]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion6.UnknownCollectAllocationFailures_proven : JuliaLean.Proofs.base.array.Completion6.UnknownCollectAllocationFailures := by
  unfold JuliaLean.Proofs.base.array.Completion6.UnknownCollectAllocationFailures
  intros
  simp only [JuliaLean.base.array.Completion6.collectUnknown, JuliaLean.base.array.Completion6.vectorUndef, JuliaLean.base.array.collectUnknown]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion6.SizedCollectLengthFailures_proven : JuliaLean.Proofs.base.array.Completion6.SizedCollectLengthFailures := by
  unfold JuliaLean.Proofs.base.array.Completion6.SizedCollectLengthFailures
  intros
  simp only [JuliaLean.base.array.Completion6.collectSized]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)

namespace JuliaLean.Proofs.base.array
def entriesCollect1 : List JuliaLean.Registry.Entry := [
  { id := "array-collect-sized-widening", juliaFile := "base/array.jl",
    juliaFns := ["collect(itr)", "collect(itr::Generator)",
      "_collect(c, itr, ::EltypeUnknown, isz::Union{HasLength,HasShape})"],
    statement := "Collecting a sized iterator of unknown element type gives an empty array of the inferred element type when the iterator is empty, and otherwise an array of the iterator's shape holding its values in order whose element type admits every value and is the type of the first value whenever every value is an instance of it.",
    source := "base/array.jl:660-697 (collect docstring), 771, 833-873",
    status := .proven, prop := ``CollectSizedSpec, thm := some ``opusGrowth.collectSizedSpec}
]
def entriesCollect2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-collect-array", juliaFile := "base/array.jl",
    juliaFns := ["collect(A::AbstractArray)", "_collect_indices(::Tuple{}, A)",
      "_collect_indices(indsA::Tuple{Vararg{OneTo}}, A)", "_collect_indices(indsA, A)"],
    statement := "`collect(A::AbstractArray)` (array.jl:773; `collect` docstring at array.jl:723-770: \"Return an `Array` of all items in a collection or iterator ... the result has the same shape and number of dimensions as `collection`\") for a heap array of any number of dimensions: a fresh array of the same element type and dimensions holding the same values in order, appended to the heap so no existing array changes; an unassigned slot raises `UndefRefError`.",
    source := "base/array.jl:723-770, array.jl:773", status := .todo,
    prop := ``ArrayCollectionSpec, thm := none,
    notes := "Incomplete allocation domain: ArrayCollectionSpec quantifies a live source independently of layout src.elementType and demands a successful fresh copy even when that layout is absent or arrayAllocError rejects its dimensions. Absent native metadata for a live array is not a Julia counterexample. Account for allocation errors with runtime-valid metadata; no exact full certificate was returned." },
  { id := "array-collect-known-eltype", juliaFile := "base/array.jl",
    juliaFns := ["collect(itr)", "collect_similar(cont, itr)",
      "_collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape})"],
    statement := "`collect(itr)` (array.jl:771; docstring at 719-770: \"Return an `Array` of all items in a collection or iterator ... an iterator with the `HasShape` trait, the result will have the same shape and number of dimensions as the argument\") and `collect_similar(cont, itr)` (775) through `_collect(cont, itr, ::HasEltype, isz)` (777), for every non-array iterator of known element type with a `HasLength` or `HasShape` size (user `iterate`, `length`, `axes`, any conversions): the size query runs once, Base-`similar` containers give the array allocated for the queried length or `OneTo` axes (as in collect-alloc) holding the k-th stored element (`x isa T ? x : convert(T, x)`) in slot k, extra elements throw `ArgumentError` after the earlier stores, missing ones leave slots unassigned, iteration and conversion exceptions propagate after the earlier stores, and user-typed destinations (own or axis-type `similar`) receive the elements in order at the successive indices of their own `eachindex`; `IsInfinite` throws `MethodError`. The `SizeUnknown` method (780) is blocked on model proposal R6dc2.2.",
    source := "base/array.jl:719-779", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round6dcollect3.KnownEltypeCollectSpec, thm := some ``opusGrowth.knownEltypeCollectSpec }
]
def entriesCollect3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-collect-typed", juliaFile := "base/array.jl",
    juliaFns := ["collect(::Type{T}, itr)",
      "_collect(::Type{T}, itr, isz::Union{HasLength,HasShape})",
      "_collect(::Type{T}, itr, isz::SizeUnknown)"],
    statement := "`collect(element_type, collection)` (array.jl:684; docstring at array.jl:672-683: \"Return an `Array` with the given element type of all items in a collection or iterable. The result has the same shape and number of dimensions as `collection`.\") through `_collect(T, itr, isz)` (array.jl:686, 688), for an iterator yielding `xs`: with a length of any BitInteger type that is the true count (`HasLength`), `Vector{T}(undef, Int(len))` and `copyto!` give a fresh vector of element type `T` holding the converted values (`InexactError` when the length is not an `Int`); with an unknown size, `Vector{T}()` and `push!` give a fresh valid vector of the converted values; a conversion error propagates in both.",
    source := "base/array.jl:672-683, array.jl:684, array.jl:686", status := .todo,
    prop := ``CompleteTypedCollectSpec, thm := none,
    notes := "Incomplete allocation domain: the sized/native conjuncts of CompleteTypedCollectSpec demand success without a present runtime-valid target layout or the allocator's byte-size checks. An absent-layout success demand is not a Julia counterexample. Unknown-size conjuncts already use ofRuntime layouts and retain allocation/growth outcomes through FollowsSteps. Returned allocation lemmas do not settle this full conjunction." }
]
def entriesCollect4 : List JuliaLean.Registry.Entry := [
{ id := "array-typed-collect-protocol", juliaFile := "base/array.jl",
  juliaFns := ["collect(::Type{T}, itr) where {T}"],
  statement := "Typed collection discovers its iterator size before dispatch and forwards the original type and iterator.",
  source := "base/array.jl:684-684", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.TypedCollectProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion2.TypedCollectProtocol_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-for-protocol", juliaFile := "base/array.jl",
  juliaFns := ["_array_for(::Type{T}, itr, isz) where {T}"],
  statement := "Comprehension allocation discovers shape once before forwarding type, size trait and unchanged shape to the selected allocator.",
  source := "base/array.jl:716-716", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.ArrayForProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion2.ArrayForProtocol_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-collect-traits-protocol", juliaFile := "base/array.jl",
  juliaFns := ["collect(itr)"],
  statement := "Generic collection discovers element-type and size traits in order, using the singleton 1:1 range as its allocation template.",
  source := "base/array.jl:771-771", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.CollectTraitsProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion2.CollectTraitsProtocol_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-collect-array-axes-protocol", juliaFile := "base/array.jl",
  juliaFns := ["collect(A::AbstractArray)"],
  statement := "Array collection forwards its original array and discovered axes to the index-shape collector, preserving axis discovery effects.",
  source := "base/array.jl:773-773", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.CollectArrayAxesProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion2.CollectArrayAxesProtocol_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-collect-similar-protocol", juliaFile := "base/array.jl",
  juliaFns := ["collect_similar(cont, itr)"],
  statement := "Collection with a template preserves the supplied template and iterator and discovers the two traits in source order.",
  source := "base/array.jl:775-775", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.CollectSimilarProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion2.CollectSimilarProtocol_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-known-sized-eltype-errors", juliaFile := "base/array.jl",
  juliaFns := ["_collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape})"],
  statement := "A failed element-type observation is retained before length/axes discovery, allocation or copying.",
  source := "base/array.jl:777-778", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.KnownSizedEltypeErrors, thm := some ``JuliaLean.Proofs.base.array.Completion2.KnownSizedEltypeErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-known-unknown-eltype-errors", juliaFile := "base/array.jl",
  juliaFns := ["_collect(cont, itr, ::HasEltype, isz::SizeUnknown)"],
  statement := "Unknown-sized collection propagates an element-type error before allocation or beginning iteration.",
  source := "base/array.jl:780-786", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.KnownUnknownEltypeErrors, thm := some ``JuliaLean.Proofs.base.array.Completion2.KnownUnknownEltypeErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-collect-with-first-push-errors", juliaFile := "base/array.jl",
  juliaFns := ["collect_to_with_first!(dest, v1, itr, st)"],
  statement := "Collection with a saved first element pushes it before resuming the iterator; a push error preserves its effects.",
  source := "base/array.jl:881-884", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.CollectWithFirstPushErrors, thm := some ``JuliaLean.Proofs.base.array.Completion2.CollectWithFirstPushErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-collect-to-iteration-error", juliaFile := "base/array.jl",
  juliaFns := ["collect_to!(dest::AbstractArray{T}, itr, offs, st) where T"],
  statement := "Collect-to propagates an iteration error with its effects before any element store, index increment, widening or redispatch; no decreasing rank is required.",
  source := "base/array.jl:895-912", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.CollectToIterationError, thm := some ``JuliaLean.Proofs.base.array.Completion2.CollectToIterationError_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-grow-first-empty-and-errors", juliaFile := "base/array.jl",
  juliaFns := ["grow_to!(dest, itr)"],
  statement := "Empty iteration returns the original destination without allocating; iteration errors preserve their complete state.",
  source := "base/array.jl:914-920", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.GrowFirstEmptyAndErrors, thm := some ``JuliaLean.Proofs.base.array.Completion2.GrowFirstEmptyAndErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-grow-to-type-discovery-error", juliaFile := "base/array.jl",
  juliaFns := ["grow_to!(dest, itr, st)"],
  statement := "Grow-to reads the destination element type before any iteration; exceptions preserve state and divergent type discovery remains divergent.",
  source := "base/array.jl:935-949", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.GrowToTypeDiscoveryError, thm := some ``JuliaLean.Proofs.base.array.Completion2.GrowToTypeDiscoveryError_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesCollect5 : List JuliaLean.Registry.Entry := [
{ id := "array-push-widen-eltype-errors", juliaFile := "base/array.jl",
  juliaFns := ["push_widen(dest, el)"],
  statement := "Widening observes the original container element type before joining types, creating a container, copying or pushing; the first failure retains its state.",
  source := "base/array.jl:922-933", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.PushWidenEltypeErrors, thm := some ``JuliaLean.Proofs.base.array.Completion3.PushWidenEltypeErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesCollect6 : List JuliaLean.Registry.Entry := [
{ id := "array-for-length-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_array_for_inner(::Type{T}, ::HasLength, len::Integer) where {T}"],
  statement := "Length-bearing iterator allocation converts the length to Int before native allocation, preserving conversion errors, partial states and divergence.",
  source := "base/array.jl:712-712", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.ArrayForLengthConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion4.ArrayForLengthConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-for-shape-arguments", juliaFile := "base/array.jl",
  juliaFns := ["_array_for_inner(::Type{T}, ::HasShape{N}, axs) where {T,N}"],
  statement := "The shaped iterator allocator forwards its selected element type and original axes unchanged to the type/axes-selected similar method.",
  source := "base/array.jl:713-713", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.ArrayForShapeArguments, thm := some ``JuliaLean.Proofs.base.array.Completion4.ArrayForShapeArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-collect-first-linear-errors", juliaFile := "base/array.jl",
  juliaFns := ["collect_to_with_first!(dest::AbstractArray, v1, itr, st)"],
  statement := "Computing LinearIndices precedes reading its first index, storing the saved element, incrementing that index and resuming collection.",
  source := "base/array.jl:875-879", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.CollectFirstLinearErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.CollectFirstLinearErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-widen-type-join-errors", juliaFile := "base/array.jl",
  juliaFns := ["setindex_widen_up_to(dest::AbstractArray{T}, el, i) where T"],
  statement := "Type joining precedes widened allocation, either LinearIndices construction, prefix copying and the new store. A type-join error preserves its effects.",
  source := "base/array.jl:886-893", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.WidenTypeJoinErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.WidenTypeJoinErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesCollect7 : List JuliaLean.Registry.Entry := [
{ id := "array-sized-collect-length-failures", juliaFile := "base/array.jl",
  juliaFns := ["_collect(::Type{T}, itr, isz::Union{HasLength,HasShape}) where {T}"],
  statement := "In the length-bearing route, length discovery precedes Int conversion, allocation and copying. Errors and divergence retain the original native world.",
  source := "base/array.jl:686-687", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion6.SizedCollectLengthFailures, thm := some ``JuliaLean.Proofs.base.array.Completion6.SizedCollectLengthFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-unknown-collect-allocation-failures", juliaFile := "base/array.jl",
  juliaFns := ["_collect(::Type{T}, itr, isz::SizeUnknown) where T"],
  statement := "Unknown-sized typed collection allocates an empty native Vector before calling iterate or converting/pushing elements, retaining every allocation failure.",
  source := "base/array.jl:688-694", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion6.UnknownCollectAllocationFailures, thm := some ``JuliaLean.Proofs.base.array.Completion6.UnknownCollectAllocationFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesCollect8 : List JuliaLean.Registry.Entry := [
  { id := "array-for-unknown-empty", juliaFile := "base/array.jl",
    juliaFns := ["_array_for_inner(::Type{T}, ::SizeUnknown, ::Nothing) where {T}"],
    statement := "Unknown-size collection allocation returns a fresh empty vector preserving prior objects, or a type error without mutation for invalid element layout.",
    source := "base/array.jl:711; src/genericmemory.c:75-102", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.ArrayForUnknownEmptyInvariant, thm := none },
  { id := "array-iterator-upper-bound-failure", juliaFile := "base/array.jl",
    juliaFns := ["_iterator_upper_bound(itr)"],
    statement := "The inference-only iterator helper retains initial iterator effects, errors and divergence; an empty protocol result throws nothing and a nonempty result raises TypeError at the non-Bool conditional, without returning a value.",
    source := "base/array.jl:803-815", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.IteratorUpperBoundFailureInvariant, thm := none }
]
end JuliaLean.Proofs.base.array

