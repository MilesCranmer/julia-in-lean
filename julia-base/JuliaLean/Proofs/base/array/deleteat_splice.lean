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
import JuliaLean.Proofs.base.array.collect
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

def DeleteatErrorUnchanged : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (xs : List α) (indices : List I) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some → xs.length < 2 ^ 62 →
    let operation := deleteatIterator (m := MutationM α) mutableLength
      (listIterator indices) Subtype.val (· + one)
      mutableBounds
      (pushDeleted mutableAssigned mutableGet
        (fun _ value => pure (pushNowhere value))
        (fun _ delta => pure (growendNowhere delta)))
      (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
      (· - ·) (deleteend (mutableStorage layout) pure) 0 ()
    let result := operation.run initial
    (∃ e, result.1 = .error e) → result.2.contents = xs.map some

def SpliceErrorAssigned : Prop :=
  ∀ (α β : Type) (layout : MemoryLayoutMetadata) (convert : β → Except Error α) (xs : List α) (lo hi : I) (ins : List β)
    (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    xs.length < 2 ^ 62 → lo.val ≤ hi.val + 1 →
    let remove := deleteatWindow (m := MutationM α) pure mutableLength Subtype.val
      (· + ·) (· - ·) (fun a b => decide (a ≤ b)) (· - ·)
      mutableCopy mutableCopy (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)
    let operation := spliceRange (m := MutationM α)
      (getindexUnitRange (fun x : I => pure (decide (x.val > 0)))
        (fun a (r : I × I) => do
          let n ← mutableLength a
          if !(r.1 > r.2) && !(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds)
        (fun r => pure (r.2 - r.1 + one)) (fun r => pure (r.2 - r.1 + one))
        (fun a n => similar419 (mutableAllocate layout a) a n)
        (fun _ => pure one) (fun r => pure r.1) mutableCopyto)
      (fun values => JInt.wrap .i64 values.length)
      (fun a r => do
        let _ ← deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
          (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
          (fun r => r.2 - r.1 + one) remove a r
        pure ())
      mutableLength Prod.fst Prod.snd (fun r => r.2 - r.1 + one) Subtype.val
      (· - ·) (· - ·) (fun a b => decide (a < b)) (· - ·) (· - ·)
      (· - ·) (· + one) (· + ·) (· - one) remove
      (growat (mutableStorage layout) pure pure
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))))
      (fun a value i => do
        let x ← liftM (convert value)
        mutableSet a x i)
      0 (lo, hi) ins
    let result := operation.run initial
    (∃ e, result.1 = .error e) → ∀ x ∈ result.2.contents, x.isSome = true

def DeleteatRangeSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (t : IntTy) (xs : List α) (lo hi : JInt t) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    xs.length < 2 ^ 62 → lo.val ≤ hi.val + 1 →
    IntTy.i64.min ≤ lo.val → hi.val ≤ IntTy.i64.max →
    let countType := if t.bits < 64 then IntTy.i64 else t
    let arithmeticType := IntTy.promote .i64 countType
    let remove := deleteatWindow (m := MutationM α)
      (fun i : JInt t => liftM (indexConvert i)) mutableLength
      (fun d : JInt countType => d.val)
      (fun a d => JInt.wrap arithmeticType (a.val + d.val))
      (fun a d => JInt.wrap arithmeticType (a.val - d.val))
      (fun a b => decide (a.val ≤ b.val))
      (fun a i => JInt.wrap arithmeticType (a.val - i.val))
      (fun a d b s n => do mutableCopy a (← liftM (indexConvert d)) b s n)
      (fun a d b s n => do mutableCopy a d b (← liftM (indexConvert s)) (← liftM (indexConvert n)))
      (deletebeg (mutableStorage layout) (fun d => liftM (indexConvert d)))
      (deleteend (mutableStorage layout) (fun d => liftM (indexConvert d)))
    let operation := deleteatRange (m := MutationM α)
      (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
      (fun _ _ => pure ()) (fun r => decide (r.1.val > r.2.val))
      (fun r => JInt.wrap countType (if r.1.val > r.2.val then 0 else r.2.val - r.1.val + 1))
      remove 0 (lo, hi)
    let result := operation.run initial
    (result.1, result.2.contents) =
      if lo.val > hi.val then (.ok 0, xs.map some)
      else if 1 ≤ lo.val ∧ hi.val ≤ (xs.length : Int) then
        (.ok 0, (xs.take (lo.val - 1).toNat ++ xs.drop hi.val.toNat).map some)
      else (.error .bounds, xs.map some)

def SafeStoreSpec : Prop := ∀ (α β : Type) (slots : I → Option α)
    (n : Nat) (i : I) (x : α) (v : β) (convert : β → Except Error α),
  1 ≤ i.val ∧ i.val ≤ (n : Int) →
  (safeSetindex1055 slotRefNew slotStore () x i).run slots =
    (.ok (), updateSlot slots i (some x)) ∧
  (safeSetindex1057 slotRefNew slotStore () x i).run slots =
    (.ok (), updateSlot slots i (some x)) ∧
  (safeSetindexConvert (fun v => slotLift (convert v))
    (safeSetindex1057 slotRefNew slotStore) () v i).run slots =
    match convert v with
    | .error e => (.error e, slots)
    | .ok y => (.ok (), updateSlot slots i (some y))

theorem safeStoreSpec : SafeStoreSpec := by
  intro α β slots n i x v convert _hb
  cases hc : convert v <;>
    simp [safeSetindex1055, safeSetindex1057, safeSetindexConvert, slotRefNew,
      slotStore, slotLift, hc, ExceptT.run, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]

@[simp] theorem stateExcept_ite (p : Prop) [Decidable p]
    (yes no : ExceptT Error (StateM σ) β) (old : σ) :
    (if p then yes else no).run old = if p then yes.run old else no.run old := by
  split <;> rfl

def objectRef {A R D : Type} (a : A) : StateM (A → R × D) R :=
  fun objects => ((objects a).1, objects)

def objectSize {A R D : Type} (a : A) : StateM (A → R × D) D :=
  fun objects => ((objects a).2, objects)

def objectSetRef {A R D : Type} [DecidableEq A] (a : A) (ref : R) : StateM (A → R × D) Unit :=
  fun objects => ((), fun k => if k = a then (ref, (objects k).2) else objects k)

def objectSetSize {A R D : Type} [DecidableEq A] (a : A) (dims : D) : StateM (A → R × D) Unit :=
  fun objects => ((), fun k => if k = a then ((objects k).1, dims) else objects k)

def TakeFieldsSpec : Prop :=
  ∀ (A R D : Type) [DecidableEq A] [DecidableEq R] [DecidableEq D]
    (objects : A → R × D) (dst src : A),
    (takeBang objectRef (fun x y => x == y) objectSetRef objectSize
      (fun x y => x == y) objectSetSize dst src).run objects =
      (dst, fun k => if k = dst then objects src else objects k)

theorem takeFieldsSpec : TakeFieldsSpec := by
  intro A R D _ _ _ objects dst src
  by_cases ha : dst = src
  · subst src
    simp [takeBang, objectRef, objectSize,
      StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    apply congrArg (fun f => (dst, f))
    funext k
    split <;> simp_all
  · have hrev : src ≠ dst := Ne.symm ha
    by_cases hr : (objects dst).1 = (objects src).1 <;>
      by_cases hs : (objects dst).2 = (objects src).2 <;>
      simp [takeBang, objectRef, objectSize, objectSetRef, objectSetSize, hrev, hr, hs,
        StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    all_goals
      apply congrArg (fun f => (dst, f))
      funext k
      by_cases hk : k = dst <;> simp_all
    all_goals exact Prod.ext hr hs

theorem unsupportedConstantAxesSpec : UnsupportedConstantAxesSpec := by
  intro α T Z similarAxes hsimilar element indices t dims old haxis
  simp only [constant647, stateExcept_bind, hsimilar old t dims haxis]

theorem documentedConstantDimensionsSpec : DocumentedConstantDimensionsSpec := by
  intro α T Z value allocate halloc element indices hindices t dims old typed actions
  have hc := constantArraySpec α T Z value allocate halloc.1 element indices hindices t dims old
  refine ⟨?_, ?_, ?_⟩
  · intro x he hvalid
    obtain ⟨fresh, ha⟩ := halloc.2.1 old t dims hvalid
    refine ⟨fresh, ?_⟩
    intro action hop
    have h := hc action hop
    simpa only [constantArrayResult, ha, he] using h
  · intro hrepresentable hnegative
    obtain ⟨message, ha⟩ := halloc.2.2.1 old t dims hrepresentable hnegative
    refine ⟨message, ?_⟩
    intro action hop
    have h := hc action hop
    simpa only [constantArrayResult, ha] using h
  · intro hout action hop
    have ha := halloc.2.2.2 old t dims hout
    have h := hc action hop
    simpa only [constantArrayResult, ha] using h

/-- The memory of vector `handle` satisfies `p`. -/
def vectorMemory {α : Type} (s : MutableMemory α) (handle : Nat) (p : Nat → Prop) : Prop :=
  ∀ v slots, s.arrays[handle]? = some v → s.memories[v.reference.1]? = some slots → p slots.length

def EmptyCollectorAllocationSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag) (heap : VectorHeap α),
    (arrayForUnknown (m := VectorM α) (heapVectorAllocate (α := α) layout) target).run heap =
      freshVectorAllocation target 0 heap

def IntegerCollectorAllocationSpec : Prop :=
  ∀ (Tag α Z : Type) (layout : Tag → Option MemoryLayout) (value : Z → Int) (toInt : Z → Except Error I),
    CollectorIntLaw value toInt →
    ∀ (target : Tag) (z : Z) (heap : VectorHeap α),
    (arrayForLength (fun x => (liftM (toInt x) : VectorM α I))
      (heapVectorAllocate (α := α) layout) target z).run heap =
      if IntTy.i64.min ≤ value z ∧ value z ≤ IntTy.i64.max then
        if value z < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target (value z).toNat heap
      else .error .inexact

def BitIntegerCollectorAllocationSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (S : IntTy) (target : Tag) (n : JInt S) (heap : VectorHeap α),
    (arrayForLength
      (fun x : JInt S => (liftM ((JuliaLean.base.int.convert .i64 x).mapError
        (fun _ => Error.inexact)) : VectorM α I))
      (heapVectorAllocate (α := α) layout) target n).run heap =
      if IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max then
        if n.val < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target n.val.toNat heap
      else .error .inexact

def CompleteCollectorAllocationSpec : Prop :=
  EmptyCollectorAllocationSpec ∧ IntegerCollectorAllocationSpec ∧
    BitIntegerCollectorAllocationSpec

theorem generalSizedShapeSpec : GeneralSizedShapeSpec := by
  intro Tag α β X Axes values axes similar policy convert copy hsimilar hcopy hbound
    target itr heap hlen
  simp only [genericSizedShapeCollect, collectTyped, collectSized, similarShapeAxes,
    arrayForShape, vector_bind_run, vector_pure_run]
  rw [hsimilar target (axes itr) heap]
  cases hp : policy (axes itr) with
  | error error => rfl
  | ok shape =>
    simp only [Except.bind, freshShapeAllocation]
    exact sizedCopy_fresh values convert copy hcopy target shape itr heap
      (hlen shape hp) (hbound (axes itr) shape hp)

def IteratorAllocatorRoutesSpec : Prop :=
  (∀ (Tag α X : Type) (layout : Tag → Option MemoryLayout) (target : Tag) (itr : X) (heap : VectorHeap α),
    (arrayFor (fun itr (_ : Unit) => pure (similarShapeUnknown itr))
      (fun t _ _ => arrayForUnknown (heapVectorAllocate (α := α) layout) t)
      target itr ()).run heap = freshVectorAllocation target 0 heap) ∧
  (∀ (Tag α X Z : Type) (layout : Tag → Option MemoryLayout) (length : X → Z) (value : Z → Int)
    (toInt : Z → Except Error I), CollectorIntLaw value toInt →
    ∀ (target : Tag) (itr : X) (heap : VectorHeap α),
    (arrayFor (fun itr (_ : Unit) => pure (similarShapeLength length itr))
      (fun t _ n => arrayForLength (fun n => liftM (toInt n)) (heapVectorAllocate layout) t n)
      target itr ()).run heap =
      if IntTy.i64.min ≤ value (length itr) ∧ value (length itr) ≤ IntTy.i64.max then
        if value (length itr) < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target (value (length itr)).toNat heap
      else .error .inexact) ∧
  (∀ (Tag α X Axes : Type) (layout : Tag → Option MemoryLayout) (axes : X → Axes)
    (toShape : Axes → VectorM α (List I)) (policy : Axes → Except Error (List I)),
    (∀ axs heap, (toShape axs).run heap = (policy axs).map (fun dims => (dims, heap))) →
    ∀ (target : Tag) (itr : X) (heap : VectorHeap α),
    (arrayFor (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
      (fun t _ axs => arrayForShape (shapedCollectorAllocate layout toShape) t axs)
      target itr ()).run heap =
      ((policy (axes itr)).bind intDimensionShape).bind
        (fun shape => freshShapeAllocation target shape heap))

def DefaultEltypeBoundSpec : Prop :=
  ∀ (X T α : Type) (values : X → List α) (typeof : α → T)
    (sub : T → T → Prop)
    (isGenerator functionIsType : X → Bool)
    (functionType inferredType : X → T) (promote : T → T),
    (∀ a b c, sub a b → sub b c → sub a c) →
    (∀ t, sub t (promote t)) →
    (∀ itr x, x ∈ values itr → sub (typeof x) (inferredType itr)) →
    (∀ itr, isGenerator itr = true → functionIsType itr = true →
      ∀ x ∈ values itr, sub (typeof x) (functionType itr)) →
    ∀ itr x, x ∈ values itr →
      sub (typeof x) (defaultEltype isGenerator functionIsType functionType inferredType promote itr)

theorem defaultEltypeBoundSpec : DefaultEltypeBoundSpec := by
  intro X T α values typeof sub gen istype ft inf promote trans hp hinf hft itr x hx
  unfold defaultEltype
  split
  · rename_i h
    have hh : gen itr = true ∧ istype itr = true := by simpa using h
    exact trans _ _ _ (hft itr hh.1 hh.2 x hx) (hp _)
  · exact trans _ _ _ (hinf itr x hx) (hp _)

abbrev knownLengthCollect {C Tag α X Z : Type} (layout : Tag → Option MemoryLayout) (elementType : X → Tag)
    (length : X → Z) (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (container : C) (itr : X) : VectorM α (HeapArray Tag) :=
  collectKnownSized elementType (fun itr (_ : Unit) => pure (similarShapeLength length itr))
    (fun c t itr (_ : Unit) n => similarForLength
      (fun c t n => do similar419 (heapVectorAllocate layout t) c (← liftM (toInt n)))
      c t itr n) copy container itr ()

def KnownLengthCollectionSpec : Prop :=
  ∀ (C Tag α X Z : Type) (layout : Tag → Option MemoryLayout) (elementType : X → Tag) (values : X → List α)
    (length : X → Z) (value : Z → Int) (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    CollectorIntLaw value toInt → SizedCopyLaw values (fun x => .ok x) copy →
    ∀ (container : C) itr heap, value (length itr) = (values itr).length →
    ∀ operation ∈ [
      knownLengthCollect layout elementType length toInt copy container,
      JuliaLean.base.array.collect container (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownLengthCollect layout elementType length toInt copy c itr),
      collectSimilar (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownLengthCollect layout elementType length toInt copy c itr) container],
    (operation itr).run heap =
      if (values itr).length < 2 ^ 63 then
        .ok (collectedShape (elementType itr) [(values itr).length] (values itr) heap)
      else .error .inexact

abbrev knownShapeCollect {C Tag α X Axes : Type} (layout : Tag → Option MemoryLayout) (elementType : X → Tag)
    (axes : X → Axes) (toShape : Axes → VectorM α (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (container : C) (itr : X) : VectorM α (HeapArray Tag) :=
  collectKnownSized elementType (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
    (fun c t itr (_ : Unit) axs => similarForAxes
      (fun _ t axs => shapedCollectorAllocate layout toShape t axs) c t itr axs)
    copy container itr ()

def KnownShapeCollectionSpec : Prop :=
  ∀ (C Tag α X Axes : Type) (layout : Tag → Option MemoryLayout) (elementType : X → Tag) (values : X → List α)
    (axes : X → Axes) (toShape : Axes → VectorM α (List I))
    (policy : Axes → Except Error (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    (∀ axs heap, (toShape axs).run heap = (policy axs).map (fun dims => (dims, heap))) →
    SizedCopyLaw values (fun x => .ok x) copy →
    ∀ (container : C) itr heap,
    (∀ dims shape, policy (axes itr) = .ok dims →
      intDimensionShape dims = .ok shape → shape.prod = (values itr).length) →
    ∀ operation ∈ [
      knownShapeCollect layout elementType axes toShape copy container,
      JuliaLean.base.array.collect container (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownShapeCollect layout elementType axes toShape copy c itr),
      collectSimilar (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownShapeCollect layout elementType axes toShape copy c itr) container],
    (operation itr).run heap =
      ((policy (axes itr)).bind intDimensionShape).map
        (fun shape => collectedShape (elementType itr) shape (values itr) heap)

abbrev knownUnknownCollect {C α : Type} (layout : MemoryLayoutMetadata) (container : C) (xs : List α) : MutationM α Nat :=
  collectKnownUnknown (fun _ => ())
    (fun c t => similarForUnknown
      (fun c (_ : Unit) n => similar419 (mutableAllocate layout 0) c n) c t xs)
    (mutablePush layout) container xs

def KnownUnknownCollectionSpec : Prop :=
  ∀ (C α : Type) (layout : MemoryLayoutMetadata) (container : C) (xs : List α) (heap : MutableMemory α),
    xs.length < 2 ^ 63 →
    ∀ operation ∈ [
      knownUnknownCollect layout container,
      JuliaLean.base.array.collect container (fun _ : List α => ()) (fun _ : List α => ())
        (fun c itr (_ _ : Unit) => knownUnknownCollect layout c itr),
      collectSimilar (fun _ : List α => ()) (fun _ : List α => ())
        (fun c itr (_ _ : Unit) => knownUnknownCollect layout c itr) container],
    ∃ next, (operation xs).run heap = (.ok heap.arrays.length, next) ∧
      next.contents heap.arrays.length = xs.map some ∧ next.validVector heap.arrays.length

abbrev keepatDeleteRange {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (r : I × I) : MutationM α Nat :=
  deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
    (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
    (fun r => r.2 - r.1 + one)
    (deleteatWindow pure mutableLength Subtype.val (· + ·) (· - ·)
      (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
      (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)) a r

@[simp] theorem keepatBind_run (action : KeepatM α β) (next : β → KeepatM α γ)
    (old : MutableMemory α) :
    ((action >>= next).run).run old =
      match (action.run).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok (.error e), fresh) => (.ok (.error e), fresh)
      | (.ok (.ok x), fresh) => ((next x).run).run fresh := by
  change (action.run >>= ExceptT.bindCont next).run old = _
  rw [stateExcept_bind]
  rcases h : (action.run).run old with ⟨result, fresh⟩
  cases result with
  | error e => rfl
  | ok result => cases result <;> rfl

@[simp] theorem keepatLift_run (action : MutationM α β) (old : MutableMemory α) :
    ((liftM action : KeepatM α β).run).run old =
      ((action.run old).1.map Except.ok, (action.run old).2) := by
  change (action >>= fun x => pure (Except.ok (ε := JuliaLean.base.abstractarray.ArrayError) x)).run old = _
  rw [stateExcept_bind]
  rcases h : action.run old with ⟨result, fresh⟩
  cases result <;> rfl

@[simp] theorem keepatIte_run (p : Prop) [Decidable p]
    (yes no : KeepatM α β) (old : MutableMemory α) :
    (((if p then yes else no).run).run old) =
      if p then ((yes.run).run old) else ((no.run).run old) := by
  split <;> rfl

abbrev keepatStore {α : Type} (a : Nat) (i : I) (x : α) : KeepatM α Unit :=
  liftM (do
    let _ ← setindexScalar (fun _ => true) id pure mutableTypedSet a x i
    pure ())

abbrev nativeKeepatIndices {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (indices : List I) : KeepatM α Nat :=
  keepat3129
    (JuliaLean.base.abstractarray.keepAtIndices
      (fun _ => pure one) (fun a => liftM (mutableLength (α := α) a))
      (fun p k => pure (decide (p < k))) (fun i k => pure (decide (i = k)))
      (fun a i => liftM (mutableGet a i)) keepatStore
      (fun _ i => pure (i + one)) (fun i j => pure (i, j))
      (fun a r => liftM (keepatDeleteRange (α := α) (layout := layout) a r))) a indices

abbrev nativeKeepatMask {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (mask : List Bool) : KeepatM α Nat :=
  keepat3154
    (JuliaLean.base.abstractarray.keepAtMask
      (fun mask => pure (JInt.wrap .i64 (mask.length : Int)))
      (fun a => liftM (mutableLength (α := α) a)) (fun _ => pure one)
      (fun a => liftM (mutableLength (α := α) a))
      (fun _ mask => pure ((List.range mask.length).map
        (fun k : Nat => JInt.wrap .i64 ((k : Int) + 1))))
      (fun mask i => pure (mask[(i.val - 1).toNat]?.getD false))
      (fun a i => liftM (mutableGet a i)) keepatStore
      (fun _ i => pure (i + one)) (fun i j => pure (i, j))
      (fun a r => liftM (keepatDeleteRange (α := α) (layout := layout) a r))) a mask

/-- Kept slots, including unassigned reference slots, retain their assignment
state and order under either documented form of keepat!. -/
def KeepatAssignedStateSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (initial : MutableMemory α) (xs : List (Option α)),
    initial.validVector 0 → initial.contents = xs → xs.length < 2 ^ 62 →
    (∀ indices : List I, indices.Pairwise (fun a b => a.val < b.val) →
      (∀ i ∈ indices, 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) →
      ∃ next, ((nativeKeepatIndices (layout := layout) 0 indices).run).run initial =
        (.ok (.ok 0), next) ∧ next.validVector 0 ∧
        (next.arrays[0]?.map (fun a => a.size.val)) = some (indices.length : Int) ∧
        next.contents = indices.map (fun i => (xs[(i.val - 1).toNat]?).join)) ∧
    (∀ mask : List Bool, mask.length = xs.length →
      ∃ next, ((nativeKeepatMask (layout := layout) 0 mask).run).run initial =
        (.ok (.ok 0), next) ∧ next.validVector 0 ∧
        (next.arrays[0]?.map (fun a => a.size.val)) =
          some (((xs.zip mask).filter (fun p => p.2)).length : Int) ∧
        next.contents = ((xs.zip mask).filter (fun p => p.2)).map Prod.fst) ∧
    (∀ mask : List Bool, mask.length < 2 ^ 63 → mask.length ≠ xs.length →
      ((nativeKeepatMask (layout := layout) 0 mask).run).run initial =
        (.ok (.error (.julia .boundsError)), initial))

def OrdinaryKeepatPrefixSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (x y z : α),
    (∃ next, (((nativeKeepatIndices (layout := layout) 0 [one, JInt.wrap .i64 2]).run).run
      (MutableMemory.initial [some x, some y, some z])) = (.ok (.ok 0), next) ∧
      next.contents = [some x, some y]) ∧
    (∃ next, (((nativeKeepatMask (layout := layout) 0 [true, true, false]).run).run
      (MutableMemory.initial [some x, some y, some z])) = (.ok (.ok 0), next) ∧
      next.contents = [some x, some y]) ∧
    (∃ next, (((nativeKeepatMask (layout := layout) 0 [true, true, false]).run).run
      (MutableMemory.initial [some x, none, some z])) = (.ok (.ok 0), next) ∧
      next.contents = [some x, none])

def keepatPrefixState (layout : MemoryLayoutMetadata) (x : α) (y z : Option α) : MutableMemory α :=
  ⟨[[some x, y, expectedUnset layout.runtime z] ++ List.replicate 32 none],
    [⟨(0, one), JInt.wrap .i64 2⟩]⟩

theorem keepatIndices_prefix_program {layout : MemoryLayoutMetadata} :
    nativeKeepatIndices (α := α) (layout := layout) 0 [one, JInt.wrap .i64 2] =
      (do
        let _ ← liftM (mutableGet (α := α) 0 one)
        let _ ← liftM (mutableGet (α := α) 0 (JInt.wrap .i64 2))
        let last ← liftM (mutableLength (α := α) 0)
        let _ ← liftM (keepatDeleteRange (α := α) (layout := layout) 0 (JInt.wrap .i64 3, last))
        pure 0 : KeepatM α Nat) := by
  have h12 : one + one = JInt.wrap .i64 2 := by decide
  have h23 : JInt.wrap .i64 2 + one = JInt.wrap .i64 3 := by decide
  have hlt : one < JInt.wrap .i64 2 := by decide
  simp [nativeKeepatIndices, keepat3129, JuliaLean.base.abstractarray.keepAtIndices,
    List.forIn_cons, List.forIn_nil, bind_assoc, h12, h23, hlt]

theorem keepatMask_prefix_program {layout : MemoryLayoutMetadata} :
    nativeKeepatMask (α := α) (layout := layout) 0 [true, true, false] =
      (do
        let n ← liftM (mutableLength (α := α) 0)
        if (3 : Int) != n.val then throw (.julia .boundsError)
        else do
          let last ← liftM (mutableLength (α := α) 0)
          liftM (keepatDeleteRange (α := α) (layout := layout) 0 (JInt.wrap .i64 3, last)) : KeepatM α Nat) := by
  have h1 : JInt.wrap .i64 1 = one := rfl
  have h12 : one + one = JInt.wrap .i64 2 := by decide
  have h23 : JInt.wrap .i64 2 + one = JInt.wrap .i64 3 := by decide
  have h3 : (JInt.wrap .i64 3).val = 3 := by decide
  have h1v : one.val = 1 := by decide
  have h2v : (JInt.wrap .i64 2).val = 2 := by decide
  simp [nativeKeepatMask, keepat3154, JuliaLean.base.abstractarray.keepAtMask,
    List.forIn_cons, List.forIn_nil, bind_assoc, h1, h12, h23, h3, h1v, h2v, List.range_succ]

set_option maxRecDepth 200000 in
theorem keepatDelete_prefix_run {layout : MemoryLayoutMetadata} (x : α) (y z : Option α) :
    (keepatDeleteRange (layout := layout) 0 (JInt.wrap .i64 3, JInt.wrap .i64 3)).run
      (MutableMemory.initial [some x, y, z]) =
      (.ok 0, keepatPrefixState layout x y z) := by
  have hd : JInt.wrap .i64 3 - JInt.wrap .i64 3 + one = one := by decide
  have he : decide (JInt.wrap .i64 3 > JInt.wrap .i64 3) = false := by decide
  have h13 : one ≤ JInt.wrap .i64 3 := by decide
  have h33 : JInt.wrap .i64 3 ≤ JInt.wrap .i64 3 := by decide
  have hp : JInt.wrap .i64 3 + one = JInt.wrap .i64 4 := by decide
  have h43 : JInt.wrap .i64 4 - JInt.wrap .i64 3 = one := by decide
  have h41 : JInt.wrap .i64 4 - one = JInt.wrap .i64 3 := by decide
  have h30 : JInt.wrap .i64 3 - JInt.wrap .i64 3 = zero := by decide
  have hb : ¬ JInt.wrap .i64 2 * JInt.wrap .i64 3 + one ≤ JInt.wrap .i64 3 := by decide
  have hu : ¬ JInt.rem .u64 one > JInt.rem .u64 (JInt.wrap .i64 3) := by decide
  have h32 : JInt.wrap .i64 3 - one = JInt.wrap .i64 2 := by decide
  have h23 : JInt.wrap .i64 2 + one = JInt.wrap .i64 3 := by decide
  have h14 : one + JInt.wrap .i64 3 = JInt.wrap .i64 4 := by decide
  have hr : intRange (JInt.wrap .i64 3) (JInt.wrap .i64 3) = [JInt.wrap .i64 3] := by decide
  have hv0 : zero.val = 0 := by decide
  have hv1 : one.val = 1 := by decide
  have hv3 : (JInt.wrap .i64 3).val = 3 := by decide
  have hw1 : wrapInt .i64 1 = 1 := by decide
  have hw2 : wrapInt .i64 2 = 2 := by decide
  have hw3 : wrapInt .i64 3 = 3 := by decide
  have hw4 : wrapInt .i64 4 = 4 := by decide
  simp [keepatDeleteRange, deleteatRange, deleteatWindow, deleteend,
    mutableStorage, mutableLength, mutableVector, mutableUnset, unsetindexInt,
    mutableBounds, mutableInBounds, mutableMemoryref, mutableRef, mutableCopy,
    unsafeCopyArray, mutableMemoryUnset, memoryWrite, memoryRead, keepatPrefixState, MutableMemory.initial,
    stateExcept_bind, stateExcept_pure, mutation_get_run, mutation_modify_run,
    List.forIn_cons, List.forIn_nil, unsetCell_result,
    hd, he, h13, h33, hp, h43, h41, h30, hb, hu, h32, h23, h14, hr, hv0, hv1, hv3,
    hw1, hw2, hw3, hw4, mutation_map_run]
  rfl

theorem keepatRead_first_run (x y z : α) :
    (mutableGet 0 one).run (MutableMemory.initial [some x, some y, some z]) =
      (.ok x, MutableMemory.initial [some x, some y, some z]) := by
  have hb : one ≤ JInt.wrap .i64 3 := by decide
  have hv : one.val = 1 := by decide
  simp [mutableGet, stateExcept_bind, mutableVector_run, MutableMemory.initial,
    hb, hv, memoryRead, mutation_get_run, stateExcept_pure]

theorem keepatRead_second_run (x y z : α) :
    (mutableGet 0 (JInt.wrap .i64 2)).run (MutableMemory.initial [some x, some y, some z]) =
      (.ok y, MutableMemory.initial [some x, some y, some z]) := by
  have hb : JInt.wrap .i64 2 ≤ JInt.wrap .i64 3 := by decide
  have hv1 : one.val = 1 := by decide
  have hv2 : (JInt.wrap .i64 2).val = 2 := by decide
  simp [mutableGet, stateExcept_bind, mutableVector_run, MutableMemory.initial,
    hb, hv1, hv2, memoryRead, mutation_get_run, stateExcept_pure]

theorem keepatMask_prefix_run {layout : MemoryLayoutMetadata} (x : α) (y z : Option α) :
    ((nativeKeepatMask (layout := layout) 0 [true, true, false]).run).run
      (MutableMemory.initial [some x, y, z]) =
      (.ok (.ok 0), keepatPrefixState layout x y z) := by
  let initial := MutableMemory.initial [some x, y, z]
  have hl : (mutableLength (α := α) 0).run initial = (.ok (JInt.wrap .i64 3), initial) :=
    mutableLength_run initial 0 ⟨(0, one), JInt.wrap .i64 3⟩ rfl
  rw [keepatMask_prefix_program, keepatBind_run, keepatLift_run, hl]
  simp only [Except.map]
  have hv : (JInt.wrap .i64 3).val = 3 := by decide
  simp only [hv, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rw [keepatBind_run, keepatLift_run, hl]
  simp only [Except.map]
  rw [keepatLift_run, keepatDelete_prefix_run]
  rfl

set_option maxRecDepth 32768 in
theorem ordinaryKeepatPrefixSpec : OrdinaryKeepatPrefixSpec := by
  intro α layout x y z
  refine ⟨⟨keepatPrefixState layout x (some y) (some z), ?_, rfl⟩,
    ⟨keepatPrefixState layout x (some y) (some z), ?_, rfl⟩,
    ⟨keepatPrefixState layout x none (some z), ?_, rfl⟩⟩
  · let initial := MutableMemory.initial [some x, some y, some z]
    have hl : (mutableLength (α := α) 0).run initial = (.ok (JInt.wrap .i64 3), initial) :=
      mutableLength_run initial 0 ⟨(0, one), JInt.wrap .i64 3⟩ rfl
    rw [keepatIndices_prefix_program, keepatBind_run, keepatLift_run, keepatRead_first_run]
    simp only [Except.map]
    rw [keepatBind_run, keepatLift_run, keepatRead_second_run]
    simp only [Except.map]
    rw [keepatBind_run, keepatLift_run, hl]
    simp only [Except.map]
    rw [keepatBind_run, keepatLift_run, keepatDelete_prefix_run]
    rfl
  · exact keepatMask_prefix_run x (some y) (some z)
  · exact keepatMask_prefix_run x none (some z)
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

/-! ### End deletion -/

theorem vwDeleteend_error {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (d : I)
    (hd : d.val < 0 ∨ n.val < d.val) :
    (deleteend (mutableStorage layout) pure handle d).run s =
      (.error (.argument "_deleteend! requires delta in 0:length(a)"), s) := by
  have hbig : JInt.rem .u64 d > JInt.rem .u64 n := by
    change (JInt.rem .u64 n).val < (JInt.rem .u64 d).val
    have hb := ival_bounds d
    rw [urem_val n h.2.2.2.1]
    rcases hd with hd | hd
    · rw [urem_neg_val d hd]; have := ival_bounds n; omega
    · rw [urem_val d (by have := h.2.2.2.1; omega)]; exact hd
  simp only [deleteend, ms_length, stateExcept_bind, stateExcept_pure,
    mutableLength_run s handle _ h.1, hbig, ite_true, stateExcept_throw]

/-! ## Growth at the end of a vector -/

/-- `_growend!(a, delta)` and `_growend_internal!(a, delta, len)` (array.jl:1171, 1212): a
negative `delta` raises `ArgumentError` with `a` untouched. Otherwise `_growend_internal!` keeps
the elements of `a` and leaves room for `delta` more slots after them in its memory, and
`_growend!` lengthens `a` by `delta`, keeping the old elements as its prefix; the vector stays
valid and no other array header changes. The only size precondition is that the memory length
plus `delta` is still an `Int`. -/
def GrowendSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (delta : I), s.validVector handle →
    let grow := growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) handle delta
    (delta.val < 0 → grow.run s = (.error (.argument "grow requires delta >= 0"), s)) ∧
    (0 ≤ delta.val →
      (∀ v slots, s.arrays[handle]? = some v → s.memories[v.reference.1]? = some slots →
        (slots.length : Int) + delta.val ≤ 9223372036854775807) →
      (∀ n : I, n.val = (s.contents handle).length →
        ∃ next, (growendInternal (mutableStorage layout) handle delta n).run s = (.ok (), next) ∧
          next.validVector handle ∧ next.contents handle = s.contents handle ∧
          (∀ v slots, next.arrays[handle]? = some v → next.memories[v.reference.1]? = some slots →
            v.reference.2.val - 1 + v.size.val + delta.val ≤ (slots.length : Int)) ∧
          ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      ∃ next, grow.run s = (.ok (), next) ∧ next.validVector handle ∧
        ((next.contents handle).length : Int) = (s.contents handle).length + delta.val ∧
        (next.contents handle).take (s.contents handle).length = s.contents handle ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?)

def DeleteendSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (d : I), s.validVector handle →
    let len : Int := (s.contents handle).length
    (d.val < 0 ∨ len < d.val →
      (deleteend (mutableStorage layout) pure handle d).run s =
        (.error (.argument "_deleteend! requires delta in 0:length(a)"), s)) ∧
    (0 ≤ d.val → d.val ≤ len → len - d.val < 9223372036854775807 →
      ∃ next, (deleteend (mutableStorage layout) pure handle d).run s = (.ok (), next) ∧
        next.contents handle = (s.contents handle).take (len - d.val).toNat ∧
        next.validVector handle)

def DeletebegSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (d : I), s.validVector handle →
    let len : Int := (s.contents handle).length
    (d.val < 0 ∨ len < d.val →
      (deletebeg (mutableStorage layout) pure handle d).run s =
        (.error (.argument "_deletebeg! requires delta in 0:length(a)"), s)) ∧
    (0 ≤ d.val → d.val ≤ len →
      ∃ next, (deletebeg (mutableStorage layout) pure handle d).run s = (.ok (), next) ∧
        next.contents handle = (s.contents handle).drop d.val.toNat ∧
        next.validVector handle)

def GrowbegSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (delta : I), s.validVector handle →
    let grow := growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle delta
    (delta.val < 0 → grow.run s = (.error (.argument "grow requires delta >= 0"), s)) ∧
    (0 ≤ delta.val →
      (∀ v slots, s.arrays[handle]? = some v → s.memories[v.reference.1]? = some slots →
        (slots.length : Int) + 2 * delta.val + 1 ≤ 9223372036854775807) →
      (∀ n : I, n.val = (s.contents handle).length →
        ∃ next, (growbegInternal (mutableStorage layout) handle delta n).run s = (.ok (), next) ∧
          (∀ v slots, next.arrays[handle]? = some v → next.memories[v.reference.1]? = some slots →
            v.size = n ∧ 1 ≤ v.reference.2.val ∧
            v.reference.2.val - 1 + delta.val + n.val ≤ (slots.length : Int) ∧
            (slots.drop (v.reference.2.val - 1 + delta.val).toNat).take n.val.toNat =
              s.contents handle) ∧
          ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      ∃ next, grow.run s = (.ok (), next) ∧ next.validVector handle ∧
        ((next.contents handle).length : Int) = (s.contents handle).length + delta.val ∧
        (next.contents handle).drop delta.val.toNat = s.contents handle ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?)

def ResizeIntSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (nl : I) (first : Bool), s.validVector handle →
    let len : Int := (s.contents handle).length
    let run := (resize (m := MutationM α) pure mutableLength JuliaLean.base.int.band
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
      (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure) handle nl first).run s
    (nl.val < 0 → run = (.error (.argument "new length must be ≥ 0"), s)) ∧
    (0 ≤ nl.val →
      (∀ v slots, s.arrays[handle]? = some v → s.memories[v.reference.1]? = some slots →
        (slots.length : Int) + 2 * nl.val + 1 ≤ 9223372036854775807) →
      ∃ next, run = (.ok handle, next) ∧ next.validVector handle ∧
        ((next.contents handle).length : Int) = nl.val ∧
        (first = false → (next.contents handle).take (min len nl.val).toNat =
          (s.contents handle).take (min len nl.val).toNat) ∧
        (first = true → (next.contents handle).drop (nl.val - min len nl.val).toNat =
          (s.contents handle).drop (len - min len nl.val).toNat))
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## `hcat` of same-type vectors -/

/-- Column-major order of a matrix given by its rows: column `j` lists entry `j` of every row. -/
def columnMajor {β : Type} (rows : List (List β)) : List β :=
  (List.range (rows.headD []).length).flatMap fun j => rows.filterMap fun r => r[j]?

/-- `hcat(Any[1], Any[2])` is a `Matrix{Int}`: the comprehension takes its element type from the
first value, so the promised `Matrix{Any}` (the type of `cat(Any[1], Any[2]; dims=2)`) fails. -/
def overallocationDivide (a b : I) : Except Error I :=
  match JuliaLean.base.int.checked_sdiv_int a b with
  | .ok v => .ok v
  | .error _ => .error .divide

theorem overallocationDivide_pos (a : I) (b : Int) (hb : 0 < b ∧ b ≤ 8) (ha : 0 ≤ a.val) :
    ∃ q : I, overallocationDivide a (JInt.wrap .i64 b) = .ok q ∧ q.val = a.val / b := by
  have hbv : (JInt.wrap .i64 b).val = b := ival_wrap b (by omega)
  refine ⟨JInt.wrap .i64 (a.val.tdiv b), ?_, tdiv_nonneg_val a b ha hb.1 hb.2⟩
  unfold overallocationDivide
  rw [JuliaLean.Proofs.base.int.checked_sdiv_int_eq rfl]
  have hne : ¬((JInt.wrap .i64 b).val = 0 ∨
      (a.val = IntTy.i64.min ∧ (JInt.wrap .i64 b).val = -1)) := by
    rw [hbv]; omega
  rw [if_neg hne, hbv]
  rfl

theorem ctlz_bounds (n : I) :
    0 ≤ (JuliaLean.base.int.ctlz_int n).val ∧ (JuliaLean.base.int.ctlz_int n).val ≤ 64 := by
  have hlz := JuliaLean.Proofs.base.int.leading_zeros_val n
  have hrem : (JuliaLean.base.int.leading_zeros n).val = (JuliaLean.base.int.ctlz_int n).val := by
    rw [show JuliaLean.base.int.leading_zeros n =
        JuliaLean.base.int.remT .i64 (JuliaLean.base.int.ctlz_int n) from rfl,
      JuliaLean.Proofs.base.int.remT_val]
    exact wrapInt_of_inRange .i64 _ (JuliaLean.base.int.ctlz_int n).property
  rw [← hrem, hlz]
  have hle : (if JuliaLean.Proofs.base.int.pattern n = 0 then IntTy.bits .i64
      else IntTy.bits .i64 - (JuliaLean.Proofs.base.int.pattern n).log2 - 1) ≤ 64 := by
    split <;> simp only [IntTy.bits] <;> omega
  omega

theorem shl_one_val (k : I) (h0 : 0 ≤ k.val) (h1 : k.val ≤ 56) :
    (JuliaLean.base.int.shl_Int one k).val = ((2 ^ k.val.toNat : Nat) : Int) := by
  have hp := JuliaLean.Proofs.base.int.pattern_shl_Int one k h0
  have hone : JuliaLean.Proofs.base.int.pattern one = 1 := by
    rw [JuliaLean.Proofs.base.int.pattern_of_nonneg one (by decide)]
    rfl
  have hle : 2 ^ k.val.toNat ≤ 72057594037927936 :=
    Nat.pow_le_pow_right (by decide) (show k.val.toNat ≤ 56 by omega)
  have hlt : 2 ^ k.val.toNat < 2 ^ IntTy.bits .i64 :=
    Nat.lt_of_le_of_lt hle (by decide)
  have h := JuliaLean.Proofs.base.int.val_eq_wrap_pattern (JuliaLean.base.int.shl_Int one k)
  rw [hp, hone, Nat.one_mul, Nat.mod_eq_of_lt hlt] at h
  rw [h]
  apply wrapInt_of_inRange
  have hf0 : (0 : Int) ≤ ((2 ^ k.val.toNat : Nat) : Int) := Int.natCast_nonneg _
  have hf1 : ((2 ^ k.val.toNat : Nat) : Int) ≤ ((72057594037927936 : Nat) : Int) :=
    Int.ofNat_le.mpr hle
  generalize ((2 ^ k.val.toNat : Nat) : Int) = F at hf0 hf1 ⊢
  clear hp h
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  omega

/-- `overallocation(maxsize)` (array.jl:1102) with the `ctlz_int`, `div` and `<<` of int.jl. -/
def overallocationInt (n : I) : Except Error I :=
  overallocation (m := Except Error) JuliaLean.base.int.ctlz_int overallocationDivide
    JuliaLean.base.int.shl_Int n

/-- The growth policy `overallocation(n)` (array.jl:1102-1112, whose comment states the
`n + 3n^(7/8) + n/8` target): for every nonnegative `Int` it returns at least `n`, strictly more
unless `n` is `typemax(Int)`, never overflows `Int`, and adds at most `n ÷ 8 + 3 * 2^56`. -/
def OverallocationSpec : Prop :=
  ∀ n : I, 0 ≤ n.val → ∃ r : I, overallocationInt n = .ok r ∧
    n.val ≤ r.val ∧ (n.val < 9223372036854775807 → n.val < r.val) ∧
    r.val ≤ n.val + n.val / 8 + 3 * 2 ^ 56

theorem overallocationSpec : OverallocationSpec := by
  intro n hn
  have hb := ival_bounds n
  obtain ⟨hc0, hc1⟩ := ctlz_bounds n
  have h64 : (JInt.wrap .i64 64).val = 64 := ival_wrap 64 (by decide)
  have he : (JInt.wrap .i64 64 - JuliaLean.base.int.ctlz_int n).val =
      64 - (JuliaLean.base.int.ctlz_int n).val := by
    rw [ival_sub (JInt.wrap .i64 64) (JuliaLean.base.int.ctlz_int n) (by rw [h64]; omega), h64]
  have h7 : (JInt.wrap .i64 7).val = 7 := ival_wrap 7 (by decide)
  have hm : ((JInt.wrap .i64 64 - JuliaLean.base.int.ctlz_int n) * JInt.wrap .i64 7).val =
      (64 - (JuliaLean.base.int.ctlz_int n).val) * 7 := by
    change wrapInt .i64 ((JInt.wrap .i64 64 - JuliaLean.base.int.ctlz_int n).val *
      (JInt.wrap .i64 7).val) = _
    rw [he, h7]
    exact wrapInt_of_inRange .i64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  obtain ⟨k, hkd, hkv⟩ := overallocationDivide_pos
    ((JInt.wrap .i64 64 - JuliaLean.base.int.ctlz_int n) * JInt.wrap .i64 7) 8
    ⟨by decide, by decide⟩ (by rw [hm]; omega)
  rw [hm] at hkv
  have hk0 : 0 ≤ k.val := by rw [hkv]; omega
  have hk1 : k.val ≤ 56 := by rw [hkv]; omega
  have hs := shl_one_val k hk0 hk1
  have hp1 : 1 ≤ 2 ^ k.val.toNat := Nat.one_le_two_pow
  have hp2 : 2 ^ k.val.toNat ≤ 72057594037927936 :=
    Nat.pow_le_pow_right (by decide) (show k.val.toNat ≤ 56 by omega)
  generalize hpdef : 2 ^ k.val.toNat = p at hs hp1 hp2
  obtain ⟨q, hqd, hqv⟩ := overallocationDivide_pos n 8 ⟨by decide, by decide⟩ hn
  have h3 : (JInt.wrap .i64 3).val = 3 := ival_wrap 3 (by decide)
  have hx : (JuliaLean.base.int.shl_Int one k * JInt.wrap .i64 3).val = (p : Int) * 3 := by
    change wrapInt .i64 ((JuliaLean.base.int.shl_Int one k).val * (JInt.wrap .i64 3).val) = _
    rw [hs, h3]
    exact wrapInt_of_inRange .i64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  have hextra : (JuliaLean.base.int.shl_Int one k * JInt.wrap .i64 3 + q).val =
      (p : Int) * 3 + n.val / 8 := by
    rw [ival_add (JuliaLean.base.int.shl_Int one k * JInt.wrap .i64 3) q
      (by rw [hx, hqv]; omega), hx, hqv]
  have hmax : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
  have hsub : (JInt.typemax .i64 - (JuliaLean.base.int.shl_Int one k * JInt.wrap .i64 3 + q)).val =
      9223372036854775807 - ((p : Int) * 3 + n.val / 8) := by
    rw [ival_sub (JInt.typemax .i64) (JuliaLean.base.int.shl_Int one k * JInt.wrap .i64 3 + q)
      (by rw [hmax, hextra]; omega), hmax, hextra]
  unfold overallocationInt overallocation
  simp only [hkd, hqd, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  by_cases hgt : 9223372036854775807 - ((p : Int) * 3 + n.val / 8) < n.val
  · rw [if_pos (show _ < n from (jlt_iff _ _).mpr (by rw [hsub]; exact hgt)), hmax]
    show _ ∧ _ ∧ _ ≤ n.val + n.val / 8 + 216172782113783808
    omega
  · rw [if_neg (fun h => hgt (by rw [← hsub]; exact (jlt_iff _ _).mp h))]
    rw [ival_add n (JuliaLean.base.int.shl_Int one k * JInt.wrap .i64 3 + q)
      (by rw [hextra]; omega), hextra]
    show _ ∧ _ ∧ _ ≤ n.val + n.val / 8 + 216172782113783808
    omega
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorDeletion

theorem vwDeleteat_negative {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (v : MutableVector)
    (ha : s.arrays[handle]? = some v) (i delta : I) (hd : delta.val < 0) :
    (vecDeleteat α (layout := layout) handle i delta).run s =
      (.error (.argument "_deleteat! requires delta >= 0"), s) := by
  have hnot : ¬ (0 ≤ delta.val) := by omega
  simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure,
    mutableLength_run s handle v ha, hnot, decide_false, Bool.not_false, ite_true,
    stateExcept_throw]

theorem vwDeleteat_index {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (v : MutableVector)
    (ha : s.arrays[handle]? = some v) (i delta : I) (hd : 0 ≤ delta.val)
    (hi : i.val < 1 ∨ v.size.val < i.val) :
    (vecDeleteat α (layout := layout) handle i delta).run s = (.error .bounds, s) := by
  have hnot : ¬ (one ≤ i ∧ i ≤ v.size) := by
    rw [jle_iff, jle_iff, ival_one]
    omega
  simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure,
    mutableLength_run s handle v ha, hd, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, hnot, decide_false, Bool.not_false, ite_true, stateExcept_throw]

theorem vwDeleteat_count {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (v : MutableVector)
    (ha : s.arrays[handle]? = some v) (i delta : I) (hd : 0 ≤ delta.val)
    (hn : v.size.val < 2 ^ 62) (hi1 : 1 ≤ i.val) (hin : i.val ≤ v.size.val)
    (hbig : v.size.val + 1 - i.val < delta.val) :
    (vecDeleteat α (layout := layout) handle i delta).run s = (.error .bounds, s) := by
  have hnb := ival_bounds v.size
  have hib := ival_bounds i
  have hin' : (one ≤ i ∧ i ≤ v.size) := ⟨by rw [jle_iff, ival_one]; exact hi1, hin⟩
  have hl1 : (v.size + one - i).val = v.size.val + 1 - i.val := by
    rw [ival_add_sub v.size one i (by rw [ival_one]; omega), ival_one]
  have hnot : ¬ (delta.val ≤ (v.size + one - i).val) := by rw [hl1]; omega
  simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure,
    mutableLength_run s handle v ha, hd, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, hin', and_self, hnot, decide_false, Bool.not_false, ite_true, stateExcept_throw]

theorem vwDeleteat_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i delta : I)
    (hsmall : n.val < 2 ^ 62) (hi1 : 1 ≤ i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ delta.val)
    (hdi : delta.val ≤ n.val + 1 - i.val) :
    ∃ next, (vecDeleteat α (layout := layout) handle i delta).run s = (.ok (), next) ∧ next.validVector handle ∧
      next.contents handle = (vwWindow slots off n).take (i.val - 1).toNat ++
        (vwWindow slots off n).drop (i.val - 1 + delta.val).toNat ∧
      (∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      (∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) ∧
      ∃ off' slots', VecAt next handle mem off' (n-delta) slots' := by
  have hnb := ival_bounds n
  have hib := ival_bounds i
  have hdb := ival_bounds delta
  have hn0 := h.2.2.2.1
  have hwl := vwWindow_length h
  have hlen := mutableLength_run s handle _ h.1
  have hin' : (one ≤ i ∧ i ≤ n) := ⟨by rw [jle_iff, ival_one]; exact hi1, by rw [jle_iff]; exact hin⟩
  have hl1 : (n + one - i).val = n.val + 1 - i.val := by
    rw [ival_add_sub n one i (by rw [ival_one]; omega), ival_one]
  have hcnt : delta.val ≤ (n + one - i).val := by rw [hl1]; exact hdi
  have h2i : (JInt.wrap .i64 2 * i).val = 2 * i.val := ival_two_mul i (by omega) (by omega)
  have hsum : (JInt.wrap .i64 2 * i + delta).val = 2 * i.val + delta.val := by
    rw [ival_add _ _ (by rw [h2i]; omega), h2i]
  by_cases hbr : 2 * i.val + delta.val ≤ n.val
  · have hle : (JInt.wrap .i64 2 * i + delta ≤ n) := by rw [jle_iff, hsum]; exact hbr
    have h1d : (one + delta).val = 1 + delta.val := by
      rw [ival_add _ _ (by rw [ival_one]; omega), ival_one]
    have him : (i - one).val = i.val - 1 := ival_sub_one i (by omega)
    obtain ⟨slots1, hcp, hv1, hw1⟩ := vwCopy_run s handle mem off n slots h (one + delta) one
      (i - one) (by rw [him]; omega) (by rw [h1d]; omega) (by rw [h1d, him]; omega)
      (by rw [ival_one]; exact Int.le_refl 1) (by rw [ival_one, him]; omega)
    obtain ⟨next, off', slots', hdel, hv2, hmem, harr, hw2⟩ :=
      vwDeletebeg_run (layout := layout) _ handle mem off n slots1 hv1 delta hd (by omega)
    refine ⟨next,?_,hv2.valid,?_,?_,?_,off',slots',hv2⟩
    · simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure, hlen, hd,
        decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hin', and_self, hcnt, hle,
        eq_self_iff_true, ite_true, hcp, hdel]
    · rw [hv2.contents, hw2, hw1, h1d, him, ival_one]
      rw [show (1 + delta.val - 1).toNat = delta.val.toNat by omega,
        show ((1 : Int) - 1).toNat = 0 by rfl,
        show (1 + delta.val - 1 + (i.val - 1)).toNat = delta.val.toNat + (i.val - 1).toNat by omega,
        show (i.val - 1 + delta.val).toNat = (i.val - 1).toNat + delta.val.toNat by omega]
      have := window_drop_prefix (vwWindow slots off n) delta.val.toNat (i.val.toNat) n.val.toNat
        hwl (by omega) (by omega)
      rw [show i.val.toNat - 1 = (i.val - 1).toNat by omega] at this
      exact this
    · intro h' hne
      rw [harr, List.getElem?_set_ne (by omega)]
    · intro m _ hne
      rw [hmem]
      simp only [List.getElem?_set_ne (Ne.symm hne)]
  · have hgt : ¬ (JInt.wrap .i64 2 * i + delta ≤ n) := by rw [jle_iff, hsum]; exact hbr
    have hid : (i + delta).val = i.val + delta.val := ival_add _ _ (by omega)
    have hn1 : (n + one).val = n.val + 1 := ival_add_one n (by omega)
    have hn1d : (n + one - delta).val = n.val + 1 - delta.val := by
      rw [ival_sub _ _ (by rw [hn1]; omega), hn1]
    have hk : (n + one - delta - i).val = n.val + 1 - delta.val - i.val := by
      rw [ival_sub _ _ (by rw [hn1d]; omega), hn1d]
    obtain ⟨slots1, hcp, hv1, hw1⟩ := vwCopy_run s handle mem off n slots h i (i + delta)
      (n + one - delta - i) (by rw [hk]; omega) hi1 (by rw [hk]; omega) (by rw [hid]; omega)
      (by rw [hid, hk]; omega)
    obtain ⟨next, slots', hdel, hv2, hmem, harr, hw2⟩ :=
      vwDeleteend_run (layout := layout) _ handle mem off n slots1 hv1 delta hd (by omega) (by omega)
    refine ⟨next,?_,hv2.valid,?_,?_,?_,off,slots',hv2⟩
    · simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure, hlen, hd,
        decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hin', and_self, hcnt, hgt,
        decide_false, hcp, hdel]
    · rw [hv2.contents, hw2, hw1, hid, hk]
      rw [show (i.val + delta.val - 1).toNat = i.val.toNat + delta.val.toNat - 1 by omega,
        show (n.val + 1 - delta.val - i.val).toNat = n.val.toNat + 1 - delta.val.toNat - i.val.toNat
          by omega,
        show (i.val - 1 + (n.val + 1 - delta.val - i.val)).toNat =
          (i.val.toNat - 1) + (n.val.toNat + 1 - delta.val.toNat - i.val.toNat) by omega,
        show (n.val - delta.val).toNat = n.val.toNat - delta.val.toNat by omega,
        show (i.val - 1).toNat = i.val.toNat - 1 by omega,
        show (i.val - 1 + delta.val).toNat = i.val.toNat - 1 + delta.val.toNat by omega]
      exact window_drop_suffix (vwWindow slots off n) delta.val.toNat i.val.toNat n.val.toNat
        hwl (by omega) (by omega)
    · intro h' hne
      rw [harr, List.getElem?_set_ne (by omega)]
    · intro m _ hne
      rw [hmem]
      simp only [List.getElem?_set_ne (Ne.symm hne)]

/-- `_deleteat!(a, i, delta)` (array.jl:1307), `deleteat!(a, i)` (array.jl:1894; docstring at
array.jl:1875-1893), `popat!(a, i)` and `popat!(a, i, default)` (array.jl:1736, 1743; docstring at
array.jl:1704-1735) for an `Int` index. A negative `delta` raises `ArgumentError`, and an index or
window outside the vector raises `BoundsError`, each with `a` untouched; otherwise exactly the
`delta` slots starting at `i` are removed and the later ones close the gap. `deleteat!` removes the
item at `i`; `popat!` returns it as well, raising `UndefRefError` (with `a` untouched) when that
slot is unassigned; `popat!(a, i, default)` returns `default` for an invalid index and changes
nothing. The size precondition `length(a) < 2^62` keeps `2i + delta` an `Int`. -/
def DeleteatSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (i delta : I), s.validVector handle →
    let xs := s.contents handle
    let len : Int := xs.length
    len < 2 ^ 62 →
    let remove := deleteatWindow (m := MutationM α) pure mutableLength Subtype.val (· + ·) (· - ·)
      (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
      (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)
    (delta.val < 0 →
      (remove handle i delta).run s = (.error (.argument "_deleteat! requires delta >= 0"), s)) ∧
    (0 ≤ delta.val → (i.val < 1 ∨ len < i.val ∨ len + 1 - i.val < delta.val) →
      (remove handle i delta).run s = (.error .bounds, s)) ∧
    (0 ≤ delta.val → 1 ≤ i.val → i.val ≤ len → delta.val ≤ len + 1 - i.val →
      ∃ next, (remove handle i delta).run s = (.ok (), next) ∧ next.validVector handle ∧
        next.contents handle = xs.take (i.val - 1).toNat ++ xs.drop (i.val - 1 + delta.val).toNat ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
    ((i.val < 1 ∨ len < i.val) →
      (deleteatIndex (fun _ => false) (fun _ _ => pure ()) remove handle i).run s =
        (.error .bounds, s)) ∧
    (1 ≤ i.val → i.val ≤ len →
      ∃ next, (deleteatIndex (fun _ => false) (fun _ _ => pure ()) remove handle i).run s =
        (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = xs.eraseIdx (i.val - 1).toNat) ∧
    ((i.val < 1 ∨ len < i.val) → (popat mutableGet remove handle i).run s = (.error .bounds, s)) ∧
    (1 ≤ i.val → xs[(i.val - 1).toNat]? = some none →
      (popat mutableGet remove handle i).run s = (.error .undefinedReference, s)) ∧
    (∀ x, 1 ≤ i.val → xs[(i.val - 1).toNat]? = some (some x) →
      ∃ next, (popat mutableGet remove handle i).run s = (.ok x, next) ∧
        next.validVector handle ∧ next.contents handle = xs.eraseIdx (i.val - 1).toNat) ∧
    (∀ default, (i.val < 1 ∨ len < i.val) →
      (popatDefault mutableLength Subtype.val mutableGet remove handle i default).run s =
        (.ok default, s)) ∧
    (∀ default, 1 ≤ i.val → xs[(i.val - 1).toNat]? = some none →
      (popatDefault mutableLength Subtype.val mutableGet remove handle i default).run s =
        (.error .undefinedReference, s)) ∧
    (∀ default x, 1 ≤ i.val → xs[(i.val - 1).toNat]? = some (some x) →
      ∃ next, (popatDefault mutableLength Subtype.val mutableGet remove handle i default).run s =
        (.ok x, next) ∧ next.validVector handle ∧
        next.contents handle = xs.eraseIdx (i.val - 1).toNat)

/-- The unmasked values of the first `k` positions of `w0`, in order. -/
def keptPrefix (w0 : List β) (mask : List Bool) (k : Nat) : List β :=
  (((w0.zip mask).take k).filter (fun p => !p.2)).map Prod.fst

theorem keptPrefix_succ (w0 : List β) (mask : List Bool) (k : Nat) (v : β) (b : Bool)
    (hw : w0[k]? = some v) (hm : mask[k]? = some b) :
    keptPrefix w0 mask (k + 1) = keptPrefix w0 mask k ++ (if b then [] else [v]) := by
  have hk1 : k < w0.length := (List.getElem?_eq_some_iff.mp hw).choose
  have hk2 : k < mask.length := (List.getElem?_eq_some_iff.mp hm).choose
  have hkz : k < (w0.zip mask).length := by simp only [List.length_zip]; omega
  have hz : (w0.zip mask)[k]? = some (v, b) := by
    rw [List.getElem?_eq_getElem hkz, List.getElem_zip]
    rw [List.getElem?_eq_getElem hk1] at hw
    rw [List.getElem?_eq_getElem hk2] at hm
    cases hw
    cases hm
    rfl
  simp only [keptPrefix, List.take_succ, hz, Option.toList_some, List.filter_append,
    List.map_append]
  cases b <;> simp

theorem keptPrefix_length_le (w0 : List β) (mask : List Bool) (k : Nat) :
    (keptPrefix w0 mask k).length ≤ k := by
  simp only [keptPrefix, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

theorem keptPrefix_full (w0 : List β) (mask : List Bool) :
    keptPrefix w0 mask mask.length = ((w0.zip mask).filter (fun p => !p.2)).map Prod.fst := by
  have hall : (w0.zip mask).take mask.length = w0.zip mask :=
    List.take_of_length_le (by simp only [List.length_zip]; omega)
  simp only [keptPrefix, hall]

theorem drop_succ_of_drop_eq (l w : List β) (k : Nat) (h : l.drop k = w.drop k) :
    l.drop (k + 1) = w.drop (k + 1) := by
  apply List.ext_getElem?
  intro i
  have := congrArg (fun l => l[1 + i]?) h
  simp only [List.getElem?_drop] at this ⊢
  rw [show k + 1 + i = k + (1 + i) by omega]
  exact this

/-- The state of the mask-deletion loop after `k` steps: the kept values of the first `k`
positions fill the start of the window, and the positions from `k` on are still the original
ones. -/
abbrev MaskInv (handle mem : Nat) (off n : I) (w0 : List (Option α)) (mask : List Bool)
    (k : Nat) (pq : I × I) (st : MutableMemory α) : Prop :=
  ∃ sl, VecAt st handle mem off n sl ∧ pq.2.val = k + 1 ∧
    pq.1.val = (keptPrefix w0 mask k).length + 1 ∧
    (vwWindow sl off n).take (keptPrefix w0 mask k).length = keptPrefix w0 mask k ∧
    (vwWindow sl off n).drop k = w0.drop k


theorem deleteatIndex_lengthToInt_run {α : Type} {layout : MemoryLayoutMetadata} {t : IntTy} (s : MutableMemory α) (handle : Nat)
    (i : JInt t) :
    (deleteatIndex (fun _ => false) (fun _ _ => pure ())
      (deleteatWindow (m := MutationM α) lengthToInt mutableLength Subtype.val (· + ·) (· - ·)
        (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
        (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)) handle i).run s =
    if IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max then
      (deleteatIndex (fun _ => false) (fun _ _ => pure ())
        (deleteatWindow (m := MutationM α) pure mutableLength Subtype.val (· + ·) (· - ·)
          (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
          (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)) handle
        (JInt.wrap .i64 i.val)).run s
    else (.error .inexact, s) := by
  by_cases hx : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max
  · simp only [hx, and_self, ite_true, deleteatIndex, deleteatWindow, lengthToInt,
      stateExcept_bind, stateExceptLift_run, bitinteger_array_conversion, stateExcept_pure,
      Bool.false_eq_true, ite_false]
  · simp only [hx, ite_false, deleteatIndex, deleteatWindow, lengthToInt, stateExcept_bind,
      stateExceptLift_run, bitinteger_array_conversion, stateExcept_pure, Bool.false_eq_true]

/-- `deleteat!(a, i)` (array.jl:1894; docstring at array.jl:1875-1893) through
`_deleteat!(a, i, 1)` (array.jl:1307) for an index of any BitInteger type: `Int(i)` raises
`InexactError` with `a` untouched when `i` is not an `Int` value; an index outside
`1:length(a)` raises `BoundsError` with `a` untouched; otherwise exactly `a[i]` is removed, the
other elements keeping their order, in a valid vector. The size precondition is
`length(a) < 2^62`. -/
def DeleteatIndexSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (t : IntTy) (s : MutableMemory α) (handle : Nat) (i : JInt t), s.validVector handle →
    let xs := s.contents handle
    (xs.length : Int) < 2 ^ 62 →
    let run := (deleteatIndex (fun _ => false) (fun _ _ => pure ())
      (deleteatWindow (m := MutationM α) lengthToInt mutableLength Subtype.val (· + ·) (· - ·)
        (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
        (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)) handle i).run s
    (¬ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) → run = (.error .inexact, s)) ∧
    (IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max → (i.val < 1 ∨ xs.length < i.val) →
      run = (.error .bounds, s)) ∧
    (1 ≤ i.val → i.val ≤ xs.length →
      ∃ next, run = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = xs.eraseIdx (i.val - 1).toNat)

def DeleteatMaskSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat) (mask : List Bool), s.validVector handle →
    ValidArraySlots layout.runtime (s.contents handle) →
    let xs := s.contents handle
    (xs.length : Int) < 2 ^ 62 →
    let run := (deleteatMask mutableLength
      (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
      (deleteend (mutableStorage layout) pure) handle mask).run s
    (mask.length ≠ xs.length → run = (.error .bounds, s)) ∧
    (mask.length = xs.length → ∃ next, run = (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle = ((xs.zip mask).filter (fun p => !p.2)).map Prod.fst)
end VectorDeletion
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section FindallFamily

/-- The fallback `Core.kwcall(kwargs, sizehint!, a, sz)` (array.jl:1647-1652) for collections
without keyword `sizehint!`: the `first` and `shrink` keywords must be `Bool` (a failing
`get(...)::Bool` raises first), any other keyword raises through `kwerr`, and otherwise the call is
exactly `sizehint!(a, sz)`. -/
def SizehintKwcallSpec : Prop :=
  ∀ (KW A Z : Type) (getBool : KW → String → Bool → Except Error Bool)
    (unknownNames : KW → List String) (kwerr : KW → A → Z → Except Error Unit)
    (sizehint : A → Z → Except Error A) (kw : KW) (a : A) (sz : Z),
    let run := sizehintKwcall getBool unknownNames kwerr sizehint kw a sz
    (∀ e, getBool kw "first" false = .error e → run = .error e) ∧
    (∀ b e, getBool kw "first" false = .ok b → getBool kw "shrink" true = .error e →
      run = .error e) ∧
    (∀ b c, getBool kw "first" false = .ok b → getBool kw "shrink" true = .ok c →
      (unknownNames kw ≠ [] → ∀ e, kwerr kw a sz = .error e → run = .error e) ∧
      (unknownNames kw = [] → run = sizehint a sz))

theorem sizehintKwcallSpec : SizehintKwcallSpec := by
  intro KW A Z getBool unknownNames kwerr sizehint kw a sz
  refine ⟨fun e he => ?_, fun b e hb he => ?_, fun b c hb hc => ⟨fun hne e he => ?_, fun hnil => ?_⟩⟩
  · simp only [sizehintKwcall, he]; rfl
  · simp only [sizehintKwcall, hb, he]; rfl
  · have hn : (unknownNames kw).isEmpty = false := by
      cases h : unknownNames kw
      · exact absurd h hne
      · rfl
    simp only [sizehintKwcall, hb, hc, hn, he]; rfl
  · simp only [sizehintKwcall, hb, hc, hnil]; rfl
end FindallFamily
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

/-- `_unique_filter!` (array.jl:3159-3167) through `_grow_filter!(seen)` and
`_shrink_filter!(keep)` (array.jl:3169-3170), as `filter` predicates over `xs`: the growing filter
keeps each value of `xs` not yet in `seen`, once, in order, and adds it to `seen`; the shrinking
filter keeps the first occurrence of each value of `keep`, in order, and removes it from `keep`. -/
def UniqueFilterSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (v xs seen : List α),
    (xs.filterM (growFilter setNotin setPush ())).run ⟨v, seen⟩ =
      (dedupFrom seen xs, ⟨v, seen ++ dedupFrom seen xs⟩) ∧
    (xs.filterM (shrinkFilter setIn setPop ())).run ⟨v, seen⟩ =
      (firstIn seen xs, ⟨v, firstInRest seen xs⟩)
end VectorSets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ### Deleting and splicing at a list of indices -/

/-- `_deleteat!(a, inds, dltd)` (array.jl:1965) for a vector `a` in mutable memory and the index
vector `inds` (a `Vector{Int}`, iterated in order), with `_push_deleted!` (array.jl:1947) handing
each removed slot to `push`, or to `growend` when it is unassigned. -/

abbrev mutableDeleteatIndices {α D : Type} (layout : MemoryLayoutMetadata) (push : D → α → MutationM α Unit)
    (grow : D → I → MutationM α Unit) (a : Nat) (inds : List I) (dltd : D) :
    MutationM α Nat :=
  deleteatIterator mutableLength (listIterator inds) Subtype.val (· + one) mutableBounds
    (pushDeleted mutableAssigned mutableGet push grow)
    (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
    (· - ·) (deleteend (mutableStorage layout) pure) a dltd

/-- `splice!(a, inds)` (array.jl:2148): the removed slots go to a fresh vector `eltype(a)[]`
through `push!` and `_growend!`. -/

abbrev mutableSpliceIndices {α : Type} (layout : MemoryLayoutMetadata) (a : Nat) (inds : List I) : MutationM α Nat :=
  spliceIndices (fun a => mutableAllocate layout a zero) mutableLength listIterator Subtype.val
    (· + one) mutableBounds mutableAssigned mutableGet
    (fun d v => mutablePush layout d v)
    (fun d n => growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) d n)
    mutableSet (mutableUnset layout.runtime) (· - ·) (deleteend (mutableStorage layout) pure) a inds

/-- `deleteat!(a, inds)` (array.jl:1940, 1941; docstring at array.jl:1903-1939: "Remove the items
at the indices given by `inds` ... `inds` can be ... a sorted and unique integer vector") and
`splice!(a, inds)` (array.jl:2148; docstring at array.jl:2083-2118: "Remove items at specified
indices, and return a collection containing the removed items. Subsequent items are shifted
left"), through `_deleteat!` and `_push_deleted!` (array.jl:1947-1997), for an `Int` index
vector: when the indices are strictly increasing and inside `1:length(a)`, `a` keeps exactly the
other slots in order (unassigned ones included) in a valid vector, and `splice!` returns a valid
fresh vector holding the removed slots in order (an unassigned removed slot stays unassigned).
When the indices before some index `i` are such indices, a first `i` outside `1:length(a)` or a
later `i` above `length(a)` raises `BoundsError`, and a later `i` not above its predecessor raises
`ArgumentError("indices must be unique and sorted")`. -/

def DeleteatIndicesSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (s : MutableMemory α) (a : Nat) (inds : List I),
    s.validVector a → vectorMemory s a (memoryFits l) →
    ValidArraySlots l (s.contents a) →
    let w := s.contents a
    let splice := mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime l) a inds
    let deletes : List (MutationM α Nat) :=
      [mutableDeleteatList (MemoryLayoutMetadata.ofRuntime l) a inds, mutableDeleteatVector (MemoryLayoutMetadata.ofRuntime l) a inds]
    let afterPushes := fun (k : Nat) (e : Error) =>
      match pushesPlan l emptyGeometry k with
      | .error e' => e'
      | .ok _ => e
    (inds.Pairwise (fun i j => i.val < j.val) →
      (∀ i ∈ inds, 1 ≤ i.val ∧ i.val ≤ (w.length : Int)) →
      let keep := (w.zipIdx.filter (fun p =>
        !(inds.any (fun i => decide (i.val = (p.2 : Int) + 1))))).map Prod.fst
      let removed := inds.map (fun i => w[(i.val - 1).toNat]?.join)
      (∀ op ∈ deletes, ∃ next, op.run s = (.ok a, next) ∧ next.validVector a ∧ next.contents a = keep) ∧
      FollowsSteps (pushesPlan l emptyGeometry inds.length) (splice.run s) (fun d next =>
        next.validVector a ∧ next.contents a = keep ∧ next.validVector d ∧ next.contents d = removed)) ∧
    (∀ pre i post, inds = pre ++ i :: post → pre.Pairwise (fun i j => i.val < j.val) →
      (∀ j ∈ pre, 1 ≤ j.val ∧ j.val ≤ (w.length : Int)) →
      (pre = [] → ¬(1 ≤ i.val ∧ i.val ≤ (w.length : Int)) →
        (∀ op ∈ deletes, (op.run s).1 = .error .bounds) ∧ (splice.run s).1 = .error .bounds) ∧
      (∀ j, pre.getLast? = some j → i.val ≤ j.val →
        (∀ op ∈ deletes, (op.run s).1 = .error (.argument "indices must be unique and sorted")) ∧
        (splice.run s).1 =
          .error (afterPushes pre.length (.argument "indices must be unique and sorted"))) ∧
      (∀ j, pre.getLast? = some j → j.val < i.val → (w.length : Int) < i.val →
        (∀ op ∈ deletes, (op.run s).1 = .error .bounds) ∧
        (splice.run s).1 = .error (afterPushes pre.length .bounds)))

/-- `splice!(a, i::Integer, ins)` (array.jl:2065) for an `Int` index on a vector in mutable
memory, the replacements `ins` iterated in order: `a[i]` (`getindex`), `_deleteat!(a, i, 1)`,
`only(ins)`, `_growat!(a, i, m-1)` and the converting stores `a[i+k-1] = x`. -/

abbrev mutableSpliceIndex {α : Type} (layout : MemoryLayoutMetadata) (already : α → Bool) (convert : α → Except Error α)
    (a : Nat) (i : I) (ins : List α) : MutationM α α :=
  spliceIndex mutableGet (fun ins => JInt.wrap .i64 ins.length) (vecDeleteat α (layout := layout))
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))))
    (fun ins => match ins with
      | [x] => pure x
      | _ => throw (.argument "Collection must contain exactly 1 element"))
    (fun a v i => do
      let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet
        a v i
      pure ())
    (· + ·) (· - one) a i ins

/-- `splice!(a, i::Integer, ins)` (array.jl:2065; docstring at array.jl:2015-2064: "Remove the
item at the given index, and return the removed item. Subsequent items are shifted left to fill
the resulting gap. If specified, replacement values from an ordered collection will be spliced in
place of the removed item") for an `Int` index: outside `1:length(a)` it raises `BoundsError` and
on an unassigned slot `UndefRefError`, both with nothing changed; otherwise, when every
replacement converts to the element type, it returns the old `a[i]` and `a` becomes
`a[1:i-1]`, the converted replacements in order, then `a[i+1:end]`, in a valid vector, and a
failing conversion raises its error. The size precondition is that the memory length plus
`2*length(ins) + 1` is an `Int`. -/

def SpliceIndexSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (s : MutableMemory α) (a : Nat) (i : I) (ins : List α)
    (already : α → Bool) (convert : α → Except Error α),
    s.validVector a → ins.length ≤ typemaxNat →
    let w := s.contents a
    let run := (mutableSpliceIndex (MemoryLayoutMetadata.ofRuntime l) already convert a i ins).run s
    let grow := if 2 ≤ ins.length then growatPlan l (geometryOf s a) i.val (ins.length - 1)
      else .ok (geometryOf s a)
    (¬(1 ≤ i.val ∧ i.val ≤ (w.length : Int)) → run = (.error .bounds, s)) ∧
    (1 ≤ i.val → i.val ≤ (w.length : Int) → w[(i.val - 1).toNat]? = some none →
      run = (.error .undefinedReference, s)) ∧
    (∀ v, 1 ≤ i.val → i.val ≤ (w.length : Int) → w[(i.val - 1).toNat]? = some (some v) →
      (∀ e, grow = .error e → run = (.error e, s)) ∧
      (∀ g, grow = .ok g →
        (∀ cs, ins.mapM (storedValue already convert) = .ok cs →
          ∃ next, run = (.ok v, next) ∧ next.validVector a ∧
            next.contents a = w.take (i.val - 1).toNat ++ cs.map some ++ w.drop i.val.toNat) ∧
        (∀ e, ins.mapM (storedValue already convert) = .error e → run.1 = .error e)))

/-- `splice!(a, r::AbstractUnitRange, ins)` (array.jl:2120) for an `Int` range `lo:hi` on a
vector in mutable memory, with the replacements `ins` converted by `convert` when stored. -/

abbrev mutableSpliceRange {α β : Type} (layout : MemoryLayoutMetadata) (convert : β → Except Error α) (a : Nat) (lo hi : I)
    (ins : List β) : MutationM α Nat :=
  spliceRange (m := MutationM α)
    (getindexUnitRange (fun x : I => pure (decide (x.val > 0)))
      (fun a (r : I × I) => do
        let n ← mutableLength a
        if !(r.1 > r.2) && !(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds)
      (fun r => pure (r.2 - r.1 + one)) (fun r => pure (r.2 - r.1 + one))
      (fun a n => similar419 (mutableAllocate layout a) a n)
      (fun _ => pure one) (fun r => pure r.1) mutableCopyto)
    (fun values => JInt.wrap .i64 values.length)
    (fun a r => do
      let _ ← deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
        (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
        (fun r => r.2 - r.1 + one) (vecDeleteat α (layout := layout)) a r
      pure ())
    mutableLength Prod.fst Prod.snd (fun r => r.2 - r.1 + one) Subtype.val
    (· - ·) (· - ·) (fun a b => decide (a < b)) (· - ·) (· - ·)
    (· - ·) (· + one) (· + ·) (· - one) (vecDeleteat α (layout := layout))
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))))
    (fun a value i => do
      let x ← liftM (convert value)
      mutableSet a x i)
    a (lo, hi) ins

/-- `splice!(a, lo:hi, ins)` (array.jl:2120; docstring at array.jl:2083-2118: "Remove items at
specified indices, and return a collection containing the removed items ... replacement values
... will be spliced in place of the removed items ... To insert `replacement` before an index `n`
without removing any items, use `splice!(collection, n:n-1, replacement)`") for an `Int` range
with `lo ≤ hi + 1`: a nonempty range reaching outside `1:length(a)` raises `BoundsError` with
nothing changed, as does an empty range `n:n-1` with `n` outside `1:length(a)+1` when there are
replacements; otherwise, when every replacement converts to the element type, it returns a valid
fresh vector of the removed slots `a[lo:hi]` and `a` becomes `a[1:lo-1]`, the converted
replacements in order, then `a[hi+1:end]`, in a valid vector. The size precondition is that the
memory length plus `2*length(ins) + 1` is an `Int`. -/

def SpliceRangeSpec : Prop :=
  ∀ (α β : Type) (l : DictLayout) (convert : β → Except Error α) (s : MutableMemory α) (a : Nat)
    (lo hi : I) (ins : List β),
    s.validVector a → lo.val ≤ hi.val + 1 → ins.length ≤ typemaxNat →
    let w := s.contents a
    let run := (mutableSpliceRange (MemoryLayoutMetadata.ofRuntime l) convert a lo hi ins).run s
    let d := (hi.val - lo.val + 1).toNat
    let pos : Int := if lo.val - 1 < (w.length : Int) - hi.val then lo.val else hi.val + 1
    let grow := if d < ins.length then growatPlan l (geometryOf s a) pos (ins.length - d)
      else .ok (geometryOf s a)
    (lo.val ≤ hi.val → ¬(1 ≤ lo.val ∧ hi.val ≤ (w.length : Int)) → run = (.error .bounds, s)) ∧
    ((hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ (w.length : Int)) →
      (¬ memoryFits l d → run = (.error (.argument genericMemorySizeMessage), s)) ∧
      (memoryFits l d →
        (∀ e, grow = .error e → run.1 = .error e ∧ run.2.contents a = w) ∧
        (∀ g, grow = .ok g →
          (∀ cs, ins.mapM convert = .ok cs →
            ∃ next v, run = (.ok v, next) ∧ next.validVector a ∧ next.validVector v ∧
              next.contents v = (w.drop (lo.val - 1).toNat).take d ∧
              next.contents a = w.take (lo.val - 1).toNat ++ cs.map some ++ w.drop hi.val.toNat) ∧
          (∀ e, ins.mapM convert = .error e → run.1 = .error e))))

/-- `deleteat!(a, lo:hi)` (array.jl:1900; docstring at array.jl:1871-1892: "Remove the items at
the indices given by `inds`") for a unit range of any BitInteger type whose endpoints are `Int`
values: an empty range changes nothing, an in-bounds range removes exactly `a[lo:hi]` keeping the
other elements in order, and a nonempty range reaching outside `1:length(a)` whose length is an
`Int` raises `BoundsError` with `a` unchanged. Ranges whose length overflows are
`arrayops-deleteat-range-overflow`. -/

def DeleteatRangeInboundsSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (t : IntTy) (xs : List α) (lo hi : JInt t) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    xs.length < 2 ^ 62 → lo.val ≤ hi.val + 1 →
    IntTy.i64.min ≤ lo.val → hi.val ≤ IntTy.i64.max →
    let countType := if t.bits < 64 then IntTy.i64 else t
    let arithmeticType := IntTy.promote .i64 countType
    let remove := deleteatWindow (m := MutationM α)
      (fun i : JInt t => liftM (indexConvert i)) mutableLength
      (fun d : JInt countType => d.val)
      (fun a d => JInt.wrap arithmeticType (a.val + d.val))
      (fun a d => JInt.wrap arithmeticType (a.val - d.val))
      (fun a b => decide (a.val ≤ b.val))
      (fun a i => JInt.wrap arithmeticType (a.val - i.val))
      (fun a d b s n => do mutableCopy a (← liftM (indexConvert d)) b s n)
      (fun a d b s n => do mutableCopy a d b (← liftM (indexConvert s)) (← liftM (indexConvert n)))
      (deletebeg (mutableStorage layout) (fun d => liftM (indexConvert d)))
      (deleteend (mutableStorage layout) (fun d => liftM (indexConvert d)))
    let operation := deleteatRange (m := MutationM α)
      (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
      (fun _ _ => pure ()) (fun r => decide (r.1.val > r.2.val))
      (fun r => JInt.wrap countType (if r.1.val > r.2.val then 0 else r.2.val - r.1.val + 1))
      remove 0 (lo, hi)
    let result := operation.run initial
    (lo.val > hi.val → (result.1, result.2.contents) = (.ok 0, xs.map some)) ∧
    (1 ≤ lo.val → lo.val ≤ hi.val → hi.val ≤ (xs.length : Int) →
      (result.1, result.2.contents) =
        (.ok 0, (xs.take (lo.val - 1).toNat ++ xs.drop hi.val.toNat).map some)) ∧
    (lo.val ≤ hi.val → ¬(1 ≤ lo.val ∧ hi.val ≤ (xs.length : Int)) →
      hi.val - lo.val + 1 ≤ countType.max →
      (result.1, result.2.contents) = (.error .bounds, xs.map some))

/-- `indcopy(sz::Dims, I::Vector)` (array.jl:2965, under "Copying subregions") for a vector of
`Int` index vectors with `length(I) ≤ length(sz)`: for each `i`, the destination entry lists the
positions within `I[i]` whose values lie in `1:sz[i]` (for the last `i`, in `1:prod(sz[i:end])`)
and the source entry lists those values, in order. `_findin` and vector indexing are given by
their documented results. -/

structure SlotArray (α : Type) where
  slots : List (Option α)

instance {α γ : Type} : ForIn (VectorM γ) (SlotArray α) α where
  forIn a init f := forIn a.slots init fun o b => match o with
    | some x => f x b
    | none => throw .undefinedReference

/-- `filter(f, a::Array)` (array.jl:3015) on the shared heap for an array with slots `slots`: a
fresh `Vector{T}` of `length(a)` slots, the stores `b[j] = ai`, `resize!(b, j-1)` keeping the
first `j-1` slots and `sizehint!` leaving them unchanged. `f` returns `none` for a non-`Bool`
result. -/

abbrev heapFilterArray {α : Type} (f : α → Except Error (Option Bool)) (slots : List (Option α)) :
    VectorM α Nat :=
  filterArray (fun a : SlotArray α => pure (JInt.wrap .i64 a.slots.length))
    (fun n => heapAllocate n.val.toNat)
    (fun b x j => heapSet b x j) (fun x => liftM (boolResult f x))
    (fun b n => modify fun heap => heap.set b ((heap[b]?.getD []).take n.val.toNat))
    heapLength (fun _ _ => pure ()) ⟨slots⟩

/-- `filter(f, a)` for an `Array` of any shape (array.jl:3015; docstring at array.jl:2990-3013:
"Return a copy of collection `a`, removing elements for which `f` is `false`"): when every
element is assigned and `f` returns a `Bool` for each, the result is a fresh vector holding, in
order, the elements for which `f` is `true`, and every existing array is unchanged; otherwise the
first element in iteration order that is unassigned (`UndefRefError`), on which `f` throws (its
error) or for which `f` returns a non-`Bool` (`TypeError`) decides the error. -/

def FilterArraySpec : Prop :=
  ∀ (α : Type) (f : α → Except Error (Option Bool)) (slots : List (Option α))
    (heap : VectorHeap α),
    slots.length < 2 ^ 62 →
    let run := (heapFilterArray f slots).run heap
    (∀ xs : List α, slots = xs.map some → ∀ bs, xs.mapM (boolResult f) = .ok bs →
      run = .ok (heap.length, heap ++ [((xs.zip bs).filter (·.2)).map (fun p => some p.1)])) ∧
    (∀ e, (slots.mapM (fun o => match o with
        | some x => boolResult f x
        | none => .error .undefinedReference)) = .error e → run = .error e)

/-- A `Vector` in mutable memory, iterated as Julia's `iterate(a, i)` does: `a[i]` is read when
the loop reaches `i`, for `i` in `1:length(a)`. -/

structure VectorRef where
  handle : Nat

instance {α : Type} : ForIn (MutationM α) VectorRef α where
  forIn a init f := do
    let n ← mutableLength a.handle
    forIn (intRange one n) init fun i b => do f (← mutableGet a.handle i) b

/-- `filter!(f, a::AbstractVector)` (array.jl:3061) for a `Vector` in mutable memory iterated
through its slots in order: the stores `a[j] = ai`, `nextind(a, j) = j + 1`, and for a `Vector`
`resize!(a, j-1)` (array.jl:1559) and `sizehint!(a, j-1)` (array.jl:1612). -/

abbrev mutableFilterBang {α : Type} (layout : MemoryLayoutMetadata) (f : α → Except Error (Option Bool)) (a : VectorRef) :
    MutationM α VectorRef :=
  filterBang (fun _ => pure one) (fun a => mutableLength a.handle)
    (fun a x i => mutableSet a.handle x i)
    (fun x => stateExceptLift (boolResult f x)) (fun _ j => pure (j + one)) (fun _ => true)
    (fun a n => do
      let _ ← resize (m := MutationM α) lengthToInt mutableLength JuliaLean.base.int.band
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
        (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure) a.handle n false
      pure ())
    (fun a n => do
      let _ ← sizehint (mutableStorage layout) lengthToInt
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a.handle n false true
      pure ())
    (fun _ _ _ => pure ()) a
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

def literalRef (_a : A) (i : I) (_checked : Bool) : LiteralM α I := fun slots => (i, slots)

def literalStore (i : I) (x : α) (_checked : Bool) : LiteralM α Unit :=
  fun slots => ((), slots.set (i.val - 1).toNat (some x))

/-- Lift a non-throwing state action into a state computation that can fail. -/
def liftLiteralState (action : StateM σ α) : StateT σ (Except Error) α :=
  fun state => .ok (action.run state)

def convertedLiteralSetter (convert : β → Except Error α) :
    A → β → I → StateT (List (Option α)) (Except Error) A :=
  safeSetindexConvert (fun x => StateT.lift (convert x))
    (safeSetindex1057 (fun a i b => liftLiteralState (literalRef a i b))
      (fun i x b => liftLiteralState (literalStore i x b)))

def literalAllocateAs (handle : A) (n : I) : LiteralM α A :=
  fun _ => (handle, List.replicate n.val.toNat none)

/-- A non-OneTo range axis selects the generic similar interface from abstractarray.jl. -/
inductive ConstructorAxis (Z : Type) where
  | integer : Z → ConstructorAxis Z
  | oneTo : Z → ConstructorAxis Z
  | range : Z → Z → ConstructorAxis Z

def unsupportedAxis : ConstructorAxis Z → Prop
  | .range _ _ => True
  | _ => False

def freshShapeAllocation {Tag α : Type} (target : Tag) (shape : List Nat)
    (heap : VectorHeap α) : Except Error (HeapArray Tag × VectorHeap α) :=
  .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
    heap ++ [List.replicate shape.prod none])

abbrev nativeLengthSimilar {C Tag α Z : Type} (layout : Tag → Option MemoryLayout) (toInt : Z → Except Error I)
    (c : C) (target : Tag) (n : Z) : VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarTypeVarargs
    (fun c t dims =>
      JuliaLean.base.abstractarray.similarOneTo
        (JuliaLean.base.abstractarray.toShapeMixed
          (JuliaLean.base.abstractarray.toShapeInteger (fun n => liftM (toInt n))))
        (fun c (_ : Type) dims => similar419 (heapAllocateIntDims layout t) c dims)
        c α dims) c target [n]

abbrev nativeAxesSimilar {C Tag α Axes : Type} (layout : Tag → Option MemoryLayout)
    (toShape : Axes → VectorM α (List I)) (c : C) (target : Tag) (axes : Axes) :
    VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarOneTo toShape
    (fun c (_ : Type) dims => similar419 (heapAllocateIntDims layout target) c dims) c α axes

abbrev knownLengthCollect {C Tag α X Z : Type} (layout : Tag → Option MemoryLayout) (elementType : X → Tag)
    (length : X → Z) (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (container : C) (itr : X) : VectorM α (HeapArray Tag) :=
  collectKnownSized elementType (fun itr (_ : Unit) => pure (similarShapeLength length itr))
    (fun c t itr (_ : Unit) n => similarForLength
      (fun c t n => do similar419 (heapVectorAllocate layout t) c (← liftM (toInt n)))
      c t itr n) copy container itr ()

abbrev knownShapeCollect {C Tag α X Axes : Type} (layout : Tag → Option MemoryLayout) (elementType : X → Tag)
    (axes : X → Axes) (toShape : Axes → VectorM α (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (container : C) (itr : X) : VectorM α (HeapArray Tag) :=
  collectKnownSized elementType (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
    (fun c t itr (_ : Unit) axs => similarForAxes
      (fun _ t axs => shapedCollectorAllocate layout toShape t axs) c t itr axs)
    copy container itr ()

abbrev knownUnknownCollect {C α : Type} (layout : MemoryLayoutMetadata) (container : C) (xs : List α) : MutationM α Nat :=
  collectKnownUnknown (fun _ => ())
    (fun c t => similarForUnknown
      (fun c (_ : Unit) n => similar419 (mutableAllocate layout 0) c n) c t xs)
    (mutablePush layout) container xs

/-- Native signed-range deletion, including both storage-shift directions. -/
abbrev keepatDeleteRange {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (r : I × I) : MutationM α Nat :=
  deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
    (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
    (fun r => r.2 - r.1 + one)
    (deleteatWindow pure mutableLength Subtype.val (· + ·) (· - ·)
      (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
      (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)) a r

abbrev KeepatM (α : Type) :=
  ExceptT JuliaLean.base.abstractarray.ArrayError (MutationM α)

abbrev keepatStore {α : Type} (a : Nat) (i : I) (x : α) : KeepatM α Unit :=
  liftM (do
    let _ ← setindexScalar (fun _ => true) id pure mutableTypedSet a x i
    pure ())

abbrev nativeKeepatIndices {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (indices : List I) : KeepatM α Nat :=
  keepat3129
    (JuliaLean.base.abstractarray.keepAtIndices
      (fun _ => pure one) (fun a => liftM (mutableLength (α := α) a))
      (fun p k => pure (decide (p < k))) (fun i k => pure (decide (i = k)))
      (fun a i => liftM (mutableGet a i)) keepatStore
      (fun _ i => pure (i + one)) (fun i j => pure (i, j))
      (fun a r => liftM (keepatDeleteRange (α := α) (layout := layout) a r))) a indices

abbrev nativeKeepatMask {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (mask : List Bool) : KeepatM α Nat :=
  keepat3154
    (JuliaLean.base.abstractarray.keepAtMask
      (fun mask => pure (JInt.wrap .i64 (mask.length : Int)))
      (fun a => liftM (mutableLength (α := α) a)) (fun _ => pure one)
      (fun a => liftM (mutableLength (α := α) a))
      (fun _ mask => pure ((List.range mask.length).map
        (fun k : Nat => JInt.wrap .i64 ((k : Int) + 1))))
      (fun mask i => pure (mask[(i.val - 1).toNat]?.getD false))
      (fun a i => liftM (mutableGet a i)) keepatStore
      (fun _ i => pure (i + one)) (fun i j => pure (i, j))
      (fun a r => liftM (keepatDeleteRange (α := α) (layout := layout) a r))) a mask
/-- Column-major order of a matrix given by its rows: column `j` lists entry `j` of every row. -/
def columnMajor {β : Type} (rows : List (List β)) : List β :=
  (List.range (rows.headD []).length).flatMap fun j => rows.filterMap fun r => r[j]?
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
section VectorDeletion
/-- `_deleteat!(a, i, delta)` over the concrete vector store. -/
abbrev vecDeleteat (α : Type) {layout : MemoryLayoutMetadata} : Nat → I → I → MutationM α Unit :=
  deleteatWindow (m := MutationM α) pure mutableLength Subtype.val (· + ·) (· - ·)
    (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
    (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)
end VectorDeletion
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
section GenericGrowth
/-- `push!(a, x)` (array.jl:1325-1350 docstring): the value is stored after every old element. -/
def PushesAtEnd (P : MutableMemory α → Prop) (handle : Nat)
    (push : Nat → α → MutationM α Unit) : Prop :=
  ∀ s x, P s → s.validVector handle → ∃ next, (push handle x).run s = (.ok (), next) ∧ P next ∧
    next.validVector handle ∧ next.contents handle = s.contents handle ++ [some x]
end GenericGrowth
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
section VectorSets

variable {α : Type} [DecidableEq α]

/-- `filter!(pred, v)` on the tracked vector. -/
def vecFilter (pred : α → SetM α Bool) (_ : Unit) : SetM α Unit := do
  let ys ← (← get).vec.filterM pred
  modify fun st => { st with vec := ys }
end VectorSets
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
section NewStatements

/-- `_deleteat!(a, inds, dltd)` (array.jl:1965) for a vector `a` in mutable memory and the index
vector `inds` (a `Vector{Int}`, iterated in order), with `_push_deleted!` (array.jl:1947) handing
each removed slot to `push`, or to `growend` when it is unassigned. -/
abbrev mutableDeleteatIndices {α D : Type} {layout : MemoryLayoutMetadata} (push : D → α → MutationM α Unit)
    (grow : D → I → MutationM α Unit) (a : Nat) (inds : List I) (dltd : D) :
    MutationM α Nat :=
  deleteatIterator mutableLength (listIterator inds) Subtype.val (· + one) mutableBounds
    (pushDeleted mutableAssigned mutableGet push grow)
    (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
    (· - ·) (deleteend (mutableStorage layout) pure) a dltd

/-- `deleteat!(a, inds)` (array.jl:1940): `_deleteat!` with the `Nowhere()` sink, whose `push!`
and `_growend!` (array.jl:1944-1945) do nothing. -/
abbrev mutableDeleteatList {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (inds : List I) : MutationM α Nat :=
  deleteatIndices mutableLength listIterator Subtype.val (· + one) mutableBounds
    mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
    (· - ·) (deleteend (mutableStorage layout) pure) a inds

/-- `deleteat!(a, inds::AbstractVector)` (array.jl:1941) for an `Int` index vector, which
`to_indices(a, (inds,))` returns unchanged. -/
abbrev mutableDeleteatVector {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (inds : List I) : MutationM α Nat :=
  deleteatIndexVector (fun _ inds => pure inds) id mutableLength listIterator Subtype.val
    (· + one) mutableBounds mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
    (· - ·) (deleteend (mutableStorage layout) pure) a inds

/-- `splice!(a, inds)` (array.jl:2148): the removed slots go to a fresh vector `eltype(a)[]`
through `push!` and `_growend!`. -/
abbrev mutableSpliceIndices {α : Type} (layout : MemoryLayoutMetadata) (a : Nat) (inds : List I) : MutationM α Nat :=
  spliceIndices (fun a => mutableAllocate layout a zero) mutableLength listIterator Subtype.val
    (· + one) mutableBounds mutableAssigned mutableGet
    (fun d v => mutablePush layout d v)
    (fun d n => growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) d n)
    mutableSet (mutableUnset layout.runtime) (· - ·) (deleteend (mutableStorage layout) pure) a inds

/-- `splice!(a, i::Integer, ins)` (array.jl:2065) for an `Int` index on a vector in mutable
memory, the replacements `ins` iterated in order: `a[i]` (`getindex`), `_deleteat!(a, i, 1)`,
`only(ins)`, `_growat!(a, i, m-1)` and the converting stores `a[i+k-1] = x`. -/
abbrev mutableSpliceIndex {α : Type} {layout : MemoryLayoutMetadata} (already : α → Bool) (convert : α → Except Error α)
    (a : Nat) (i : I) (ins : List α) : MutationM α α :=
  spliceIndex mutableGet (fun ins => JInt.wrap .i64 ins.length) (vecDeleteat α (layout := layout))
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))))
    (fun ins => match ins with
      | [x] => pure x
      | _ => throw (.argument "Collection must contain exactly 1 element"))
    (fun a v i => do
      let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet
        a v i
      pure ())
    (· + ·) (· - one) a i ins

/-- `splice!(a, r::AbstractUnitRange, ins)` (array.jl:2120) for an `Int` range `lo:hi` on a
vector in mutable memory, with the replacements `ins` converted by `convert` when stored. -/
abbrev mutableSpliceRange {α β : Type} (layout : MemoryLayoutMetadata) (convert : β → Except Error α) (a : Nat) (lo hi : I)
    (ins : List β) : MutationM α Nat :=
  spliceRange (m := MutationM α)
    (getindexUnitRange (fun x : I => pure (decide (x.val > 0)))
      (fun a (r : I × I) => do
        let n ← mutableLength a
        if !(r.1 > r.2) && !(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds)
      (fun r => pure (r.2 - r.1 + one)) (fun r => pure (r.2 - r.1 + one))
      (fun a n => similar419 (mutableAllocate layout a) a n)
      (fun _ => pure one) (fun r => pure r.1) mutableCopyto)
    (fun values => JInt.wrap .i64 values.length)
    (fun a r => do
      let _ ← deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
        (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
        (fun r => r.2 - r.1 + one) (vecDeleteat α (layout := layout)) a r
      pure ())
    mutableLength Prod.fst Prod.snd (fun r => r.2 - r.1 + one) Subtype.val
    (· - ·) (· - ·) (fun a b => decide (a < b)) (· - ·) (· - ·)
    (· - ·) (· + one) (· + ·) (· - one) (vecDeleteat α (layout := layout))
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))))
    (fun a value i => do
      let x ← liftM (convert value)
      mutableSet a x i)
    a (lo, hi) ins

/-- `reshape(v, dims)` (reshapedarray.jl) for the literal vector whose slots are the state: the
same elements under the dimensions `dims`, or `DimensionMismatch` when their product differs from
`length(v)`. -/
def literalReshape {α T : Type} (t : T) (dims : List I) :
    StateT (List (Option α)) (Except Error) (T × List Int) := do
  let slots ← get
  if (dims.map Subtype.val).prod = slots.length then pure (t, dims.map Subtype.val)
  else throw (.dimensionMismatch "new dimensions must be consistent with array size")

/-- Iterating an `Array` whose slots are `slots`: `iterate(a, i)` reads `a[i]`, which raises
`UndefRefError` on an unassigned slot. -/
structure SlotArray (α : Type) where
  slots : List (Option α)

instance {α γ : Type} : ForIn (VectorM γ) (SlotArray α) α where
  forIn a init f := forIn a.slots init fun o b => match o with
    | some x => f x b
    | none => throw .undefinedReference

/-- `filter(f, a::Array)` (array.jl:3015) on the shared heap for an array with slots `slots`: a
fresh `Vector{T}` of `length(a)` slots, the stores `b[j] = ai`, `resize!(b, j-1)` keeping the
first `j-1` slots and `sizehint!` leaving them unchanged. `f` returns `none` for a non-`Bool`
result. -/
abbrev heapFilterArray {α : Type} (f : α → Except Error (Option Bool)) (slots : List (Option α)) :
    VectorM α Nat :=
  filterArray (fun a : SlotArray α => pure (JInt.wrap .i64 a.slots.length))
    (fun n => heapAllocate n.val.toNat)
    (fun b x j => heapSet b x j) (fun x => liftM (boolResult f x))
    (fun b n => modify fun heap => heap.set b ((heap[b]?.getD []).take n.val.toNat))
    heapLength (fun _ _ => pure ()) ⟨slots⟩

/-- `filter!(f, a::AbstractVector)` (array.jl:3061) for a `Vector` in mutable memory iterated
through its slots in order: the stores `a[j] = ai`, `nextind(a, j) = j + 1`, and for a `Vector`
`resize!(a, j-1)` (array.jl:1559) and `sizehint!(a, j-1)` (array.jl:1612). -/
abbrev mutableFilterBang {α : Type} (layout : MemoryLayoutMetadata) (f : α → Except Error (Option Bool)) (a : VectorRef) :
    MutationM α VectorRef :=
  filterBang (fun _ => pure one) (fun a => mutableLength a.handle)
    (fun a x i => mutableSet a.handle x i)
    (fun x => stateExceptLift (boolResult f x)) (fun _ j => pure (j + one)) (fun _ => true)
    (fun a n => do
      let _ ← resize (m := MutationM α) lengthToInt mutableLength JuliaLean.base.int.band
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
        (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure) a.handle n false
      pure ())
    (fun a n => do
      let _ ← sizehint (mutableStorage layout) lengthToInt
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a.handle n false true
      pure ())
    (fun _ _ _ => pure ()) a

/-- `collect_to_with_first!(dest, v1, itr, st)` (array.jl:881) for a destination that is not an
`AbstractArray`, here a typed vector reached through `push!`. -/
def typedCollectWithFirstPush {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) :
    TypedVector Tag → α → List α → List α → MutationM α (TypedVector Tag) :=
  collectWithFirst (typedPush layout) (fun d _ st => typedGrowTo layout L d st)
end NewStatements
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
/-- `_deleteat!(a, i, delta)` (array.jl:1307; the window removal behind `deleteat!`, `popat!` and
`splice!`, docstrings at array.jl:1875-1893 and 1704-1735) for an index and a count of any
`Integer` types (every BitInteger width, `Bool`, `BigInt` and user-defined integers): an index with
no equal `Int` raises `InexactError`; a negative `delta` raises `ArgumentError`; an index outside
`1:length(a)` or a window `i:i+delta-1` reaching past the end raises `BoundsError`; each error
leaves the store unchanged. Otherwise exactly the `delta` slots starting at `i` are removed, the
later ones closing the gap (unassigned slots included), in a valid vector, and no other array
header changes. The size precondition `length(a) < 2^62` keeps `2i + delta` an `Int`. -/
def DeleteatWindowSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (i delta : IntegerValue),
    s.validVector handle →
    let xs := s.contents handle
    let len : Int := xs.length
    len < 2 ^ 62 →
    let run := (windowDelete α (layout := layout) ops handle i delta).run s
    (¬ i.fits → run = (.error .inexact, s)) ∧
    (i.fits → delta.val < 0 →
      run = (.error (.argument "_deleteat! requires delta >= 0"), s)) ∧
    (i.fits → 0 ≤ delta.val → (i.val < 1 ∨ len < i.val ∨ len + 1 - i.val < delta.val) →
      run = (.error .bounds, s)) ∧
    (0 ≤ delta.val → 1 ≤ i.val → i.val ≤ len → delta.val ≤ len + 1 - i.val →
      ∃ next, run = (.ok (), next) ∧ next.validVector handle ∧
        next.contents handle = xs.take (i.val - 1).toNat ++ xs.drop (i.val - 1 + delta.val).toNat ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?)


def GrowendSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (delta : IntegerValue),
    s.validVector handle →
    let len : Int := (s.contents handle).length
    let g := geometryOf s handle
    let grow := growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) (integerToInt ops)
      (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) handle delta
    let internal := fun d n : I => (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s
    (¬ delta.fits → grow.run s = (.error .inexact, s)) ∧
    (delta.fits → delta.val < 0 → grow.run s = (.error (.argument "grow requires delta >= 0"), s)) ∧
    (delta.fits → 0 ≤ delta.val →
      Follows s (growendPlan l g delta.val.toNat) (grow.run s) (fun _ next =>
        next.validVector handle ∧ ((next.contents handle).length : Int) = len + delta.val ∧
        (next.contents handle).take (s.contents handle).length = s.contents handle ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      ∀ d n : I, d.val = delta.val → n.val = len →
        Follows s (growendInternalPlan l g delta.val.toNat) (internal d n) (fun _ next =>
          next.validVector handle ∧ next.contents handle = s.contents handle ∧
          (∀ w slots, next.arrays[handle]? = some w → next.memories[w.reference.1]? = some slots →
            w.reference.2.val - 1 + w.size.val + d.val ≤ (slots.length : Int)) ∧
          ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?))

def DeleteendSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (d : IntegerValue),
    s.validVector handle →
    let len : Int := (s.contents handle).length
    let run := (deleteend (mutableStorage layout) (integerToInt ops) handle d).run s
    (¬ d.fits → run = (.error .inexact, s)) ∧
    (d.fits → (d.val < 0 ∨ len < d.val) →
      run = (.error (.argument "_deleteend! requires delta in 0:length(a)"), s)) ∧
    (0 ≤ d.val → d.val ≤ len →
      ∃ next, run = (.ok (), next) ∧
        next.contents handle = (s.contents handle).take (len - d.val).toNat ∧
        next.validVector handle ∧ ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?)

def DeletebegSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (d : IntegerValue),
    s.validVector handle →
    let len : Int := (s.contents handle).length
    let run := (deletebeg (mutableStorage layout) (integerToInt ops) handle d).run s
    (¬ d.fits → run = (.error .inexact, s)) ∧
    (d.fits → (d.val < 0 ∨ len < d.val) →
      run = (.error (.argument "_deletebeg! requires delta in 0:length(a)"), s)) ∧
    (0 ≤ d.val → d.val ≤ len →
      ∃ next, run = (.ok (), next) ∧
        next.contents handle = (s.contents handle).drop d.val.toNat ∧
        next.validVector handle ∧ ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?)

def GrowbegSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (delta : IntegerValue),
    s.validVector handle →
    let len : Int := (s.contents handle).length
    let g := geometryOf s handle
    let grow := growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) (integerToInt ops)
      (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) handle delta
    let internal := fun d n : I => (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s
    (¬ delta.fits → grow.run s = (.error .inexact, s)) ∧
    (delta.fits → delta.val < 0 → grow.run s = (.error (.argument "grow requires delta >= 0"), s)) ∧
    (delta.fits → 0 ≤ delta.val →
      Follows s (growbegPlan l g delta.val.toNat) (grow.run s) (fun _ next =>
        next.validVector handle ∧ ((next.contents handle).length : Int) = len + delta.val ∧
        (next.contents handle).drop delta.val.toNat = s.contents handle ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      ∀ d n : I, d.val = delta.val → n.val = len →
        Follows s (growbegInternalPlan l g delta.val.toNat) (internal d n) (fun _ next =>
          (∀ w slots, next.arrays[handle]? = some w → next.memories[w.reference.1]? = some slots →
            w.size = n ∧ 1 ≤ w.reference.2.val ∧
            w.reference.2.val - 1 + d.val + n.val ≤ (slots.length : Int) ∧
            (slots.drop (w.reference.2.val - 1 + d.val).toNat).take n.val.toNat =
              s.contents handle) ∧
          ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?))

def GrowatSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (i delta : IntegerValue),
    s.validVector handle →
    let w := s.contents handle
    let run := (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) (integerToInt ops) (integerToInt ops)
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      handle i delta).run s
    (¬ delta.fits → run = (.error .inexact, s)) ∧
    (delta.fits → ¬ i.fits → run = (.error .inexact, s)) ∧
    (delta.fits → i.fits → delta.val < 0 →
      run = (.error (.argument "grow requires delta >= 0"), s)) ∧
    (delta.fits → i.fits → 0 ≤ delta.val →
      Follows s (growatPlan l (geometryOf s handle) i.val delta.val.toNat) run (fun _ next =>
        next.validVector handle ∧
        ((next.contents handle).length : Int) = w.length + delta.val ∧
        (next.contents handle).take (i.val - 1).toNat = w.take (i.val - 1).toNat ∧
        (next.contents handle).drop (i.val - 1 + delta.val).toNat = w.drop (i.val - 1).toNat ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?))
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
namespace IntegerUnitRange

def lastValue : IntegerUnitRange → Int
  | .bit _ r => r.stop.val
  | .big _ hi => hi
end IntegerUnitRange
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

/-- `deleteat!(a::Vector, r::AbstractUnitRange{<:Integer})` (array.jl:1900; docstring at
array.jl:1910-1939: "Remove the items at the indices given by `inds`, and return the modified
`a`. Subsequent items are shifted to fill the resulting gap.") for a unit range of any `Integer`
element type (`hi ≥ lo - 1`, the normalized stop) on a vector whose slots may be unassigned, with
range.jl's `isempty`, `first` and checked `length` (`length(r)` is evaluated before `_deleteat!`
starts) and the model's `_deleteat!`: an empty range returns `a` unchanged; otherwise a length that
overflows raises `OverflowError`, a first index with no equal `Int` raises `InexactError`, a range
inside `1:length(a)` removes exactly `a[lo:hi]` (the others, unassigned ones included, keeping
their order) and returns `a`, and any other range raises `BoundsError`; no error changes `a`. -/
def DeleteatRangeSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (xs : List (Option α)) (r : IntegerUnitRange) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs → xs.length < 2 ^ 62 →
    r.first.val ≤ r.lastValue + 1 →
    let operation := deleteatRange (m := MutationM α)
      (fun _ => false) (fun a _ => pure a) IntegerUnitRange.first IntegerValue.isBool
      (fun _ _ => pure ()) IntegerUnitRange.isempty (IntegerUnitRange.length ops)
      (fun a f count => do windowDelete α (layout := layout) ops a f (← stateExceptLift count)) 0 r
    let lo := r.first.val
    let hi := r.lastValue
    let result := operation.run initial
    (hi < lo → result = (.ok 0, initial)) ∧
    (lo ≤ hi → (∃ e, r.length ops = .error e) → result = (.error .overflow, initial)) ∧
    (lo ≤ hi → (∃ n, r.length ops = .ok n) → ¬ r.first.fits → result = (.error .inexact, initial)) ∧
    (lo ≤ hi → 1 ≤ lo → hi ≤ (xs.length : Int) →
      result.1 = .ok 0 ∧ result.2.validVector 0 ∧
      result.2.contents = xs.take (lo - 1).toNat ++ xs.drop hi.toNat) ∧
    (lo ≤ hi → (∃ n, r.length ops = .ok n) → r.first.fits → ¬ (1 ≤ lo ∧ hi ≤ (xs.length : Int)) →
      result = (.error .bounds, initial))

def DeleteatSortedIndicesSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (xs : List (Option α)) (indices : List I) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs → xs.length < 2 ^ 62 →
    ValidArraySlots layout.runtime xs →
    let operation := deleteatIterator (m := MutationM α) mutableLength
      (listIterator indices) Subtype.val (· + one)
      mutableBounds
      (pushDeleted mutableAssigned mutableGet
        (fun _ value => pure (pushNowhere value))
        (fun _ delta => pure (growendNowhere delta)))
      (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
      (· - ·) (deleteend (mutableStorage layout) pure) 0 ()
    let result := operation.run initial
    let inside := fun (i : I) => 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)
    (indices = [] → result = (.ok 0, initial)) ∧
    (indices.Pairwise (fun a b => a.val < b.val) → (∀ i ∈ indices, inside i) →
      result.1 = .ok 0 ∧ result.2.validVector 0 ∧
      result.2.contents = ((xs.zipIdx 1).filter (fun p =>
        !indices.any (fun i => decide (i.val = (p.2 : Int))))).map Prod.fst) ∧
    (indices.Pairwise (fun a b => a.val < b.val) → (∃ i ∈ indices, ¬ inside i) →
      result.1 = .error .bounds) ∧
    ((∀ i ∈ indices, inside i) → ¬ indices.Pairwise (fun a b => a.val < b.val) →
      result.1 = .error (.argument "indices must be unique and sorted"))

def firstConversionError (convert : β → Except Error α) (values : List β) : Option Error :=
  values.findSome? (fun v => match convert v with
    | .error e => some e
    | .ok _ => none)

/-- `length(r)` of a `UnitRange{Int}`: range.jl's checked `length` (`lengthUnit`). -/
def intUnitRangeLength (r : I × I) : Except Error I :=
  match JuliaLean.Proofs.base.range.lengthUnit (t := .i64) ⟨r.1, r.2⟩ with
  | .ok n => .ok n
  | .error _ => .error .overflow

/-- `splice!(a::Vector, r::AbstractUnitRange{<:Integer}, ins)` (array.jl:2120; docstring at
array.jl:2061-2096) on a vector whose slots may be unassigned, with an in-bounds `UnitRange{Int}`
`lo:hi` (`hi ≥ lo - 1`, an empty range inserting before `lo`) and range.jl's checked `length`: when
some replacement value cannot be converted to the element type (`a[f+k-1] = x`, the Array
`setindex!` with `convert(T, x)`, any user conversion), the call raises the error of the first such
value, in the order of `ins`. Nothing is promised about `a` after the error. -/
def SpliceConversionErrorSpec : Prop :=
  ∀ (α β : Type) (layout : MemoryLayoutMetadata) (convert : β → Except Error α) (xs : List (Option α)) (lo hi : I) (ins : List β)
    (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs →
    xs.length < 2 ^ 62 → ins.length < 2 ^ 62 → lo.val ≤ hi.val + 1 →
    1 ≤ lo.val → hi.val ≤ (xs.length : Int) →
    let remove := deleteatWindow (m := MutationM α) pure mutableLength Subtype.val
      (· + ·) (· - ·) (fun a b => decide (a ≤ b)) (· - ·)
      mutableCopy mutableCopy (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)
    let rangeLength := fun r => match intUnitRangeLength r with
      | .ok n => n
      | .error _ => zero
    let operation := spliceRange (m := MutationM α)
      (getindexUnitRange (fun x : I => pure (decide (x.val > 0)))
        (fun a (r : I × I) => do
          let n ← mutableLength a
          if !(r.1 > r.2) && !(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds)
        (fun r => pure (rangeLength r)) (fun r => pure (rangeLength r))
        (fun a n => similar419 (mutableAllocate layout a) a n)
        (fun _ => pure one) (fun r => pure r.1) mutableCopyto)
      (fun values => JInt.wrap .i64 values.length)
      (fun a r => do
        let _ ← deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
          (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
          (fun r => stateExceptLift (intUnitRangeLength r))
          (fun a f count => do remove a f (← count)) a r
        pure ())
      mutableLength Prod.fst Prod.snd rangeLength Subtype.val
      (· - ·) (· - ·) (fun a b => decide (a < b)) (· - ·) (· - ·)
      (· - ·) (· + one) (· + ·) (· - one) remove
      (growat (mutableStorage layout) pure pure
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))))
      (fun a value i => do
        let x ← liftM (convert value)
        mutableSet a x i)
      0 (lo, hi) ins
    ∀ e, firstConversionError convert ins = some e → (operation.run initial).1 = .error e

def KeepatAssignedStateSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (initial : MutableMemory α) (xs : List (Option α)),
    initial.validVector 0 → initial.contents = xs → xs.length < 2 ^ 62 →
    (∀ indices : List I, indices.Pairwise (fun a b => a.val < b.val) →
      (∀ i ∈ indices, 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) →
      ((∀ i ∈ indices, xs[(i.val - 1).toNat]? ≠ some none) →
        ∃ next, ((nativeKeepatIndices (layout := layout) 0 indices).run).run initial =
          (.ok (.ok 0), next) ∧ next.validVector 0 ∧
          next.contents = indices.map (fun i => xs[(i.val - 1).toNat]?.getD none)) ∧
      ((∃ i ∈ indices, xs[(i.val - 1).toNat]? = some none) →
        (((nativeKeepatIndices (layout := layout) 0 indices).run).run initial).1 = .error .undefinedReference)) ∧
    (∀ mask : List Bool, mask.length = xs.length →
      ((∀ p ∈ xs.zip mask, p.2 = true → p.1.isSome) →
        ∃ next, ((nativeKeepatMask (layout := layout) 0 mask).run).run initial =
          (.ok (.ok 0), next) ∧ next.validVector 0 ∧
          next.contents = ((xs.zip mask).filter (fun p => p.2)).map Prod.fst) ∧
      ((∃ p ∈ xs.zip mask, p.2 = true ∧ p.1 = none) →
        (((nativeKeepatMask (layout := layout) 0 mask).run).run initial).1 = .error .undefinedReference)) ∧
    (∀ mask : List Bool, mask.length < 2 ^ 63 → mask.length ≠ xs.length →
      ((nativeKeepatMask (layout := layout) 0 mask).run).run initial =
        (.ok (.error (.julia .boundsError)), initial))

/-- `Set{T}()` (set.jl). -/
def setNew {K : Type} : SetVecM K Unit :=
  modify (fun _ => JuliaLean.base.set.setConstructorEmpty (K := K) 0)

/-- `x ∈ s` for the `Set` (set.jl `in(x, s::Set) = haskey(s.dict, x)`). -/
def setHas {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (x : K) (_ : Unit) :
    SetVecM K Bool := do
  setLiftR (JuliaLean.base.set.setIn ops x (← get))

/-- `x ∉ s` (operators.jl `∉(x, itr) = !∈(x, itr)`). -/
def setLacks {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (x : K) (u : Unit) :
    SetVecM K Bool := do
  return !(← setHas ops x u)

/-- `push!(s::Set, x)` (set.jl). -/
def setAdd {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (_ : Unit) (x : K) :
    SetVecM K Unit := do
  let s ← setLiftR (JuliaLean.base.set.setPush ops (identityKey ops) x (← get))
  modify (fun _ => s)

/-- `pop!(s::Set, x)` (set.jl). -/
def setRemove {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (_ : Unit) (x : K) :
    SetVecM K Unit := do
  let (_, s) ← setLiftR (JuliaLean.base.set.setPopKeyModel ops x (← get))
  modify (fun _ => s)

/-- A fresh `Set` holding `zs`, filtered through a `_unique_filter!` predicate over `ys`; the kept
values and the membership of `probe` afterwards. -/
def uniqueFilterRun {K : Type} (ops : JuliaLean.base.set.DictRuntime K)
    (predicate : Unit → K → SetVecM K Bool) (zs ys probe : List K) :
    SetVecM K (List K × List Bool) := do
  setNew
  for z in zs do
    setAdd ops () z
  let kept ← ys.filterM (predicate ())
  let after ← probe.mapM (fun y => setHas ops y ())
  pure (kept, after)

/-- Complete concrete Set adapter replacing round12SetDictRuntime. Key layout
metadata distinguishes a non-isbits union from a pointer-bearing inline value.
keyIsBits remains *only* the source copy dispatch, not the unset dispatch. -/
def setDictRuntime {K : Type} (hash : K → JInt .u64) (equal : K → K → Bool)
    (keyIsBits : Bool)
    (keyLayout : JuliaLean.src.genericmemory_c.DictLayout) : JuliaLean.base.set.DictRuntime K :=
  { hash := hash
    equal := equal
    tablesz := JuliaLean.Proofs.base.dict.round2.jlTablesz
    maxValues := JuliaLean.Proofs.base.dict.round2.jlMaxValues keyLayout.metadata.runtimeType.elementTag
    cld := fun x => .ok (JuliaLean.Proofs.base.dict.round2.jlCld2 x)
    fillSlots := JuliaLean.Proofs.base.dict.round2.memFill
    unsetKey := JuliaLean.Proofs.base.dict.round2.memUnset keyLayout
    unsetValue := JuliaLean.Proofs.base.dict.round2.memUnset JuliaLean.src.genericmemory_c.nothingDictLayout
    copySlots := JuliaLean.Proofs.base.dict.round2.memCopySlots
    copyKeys := JuliaLean.Proofs.base.dict.round2.memCopy keyIsBits
    copyValues := JuliaLean.Proofs.base.dict.round2.memCopy true }

/-- `_unique_filter!(pred, update!, state)` (array.jl:3159) through `_grow_filter!(seen)` and
`_shrink_filter!(keep)` (array.jl:3169-3170) as `filter` predicates over `ys`, with the `Set`
`seen` (respectively `keep`) holding the values `zs` (set.jl `push!`/`pop!`/`in`): the growing
filter keeps each value of `ys` that is not yet in the set, once, in order, adding it to the set;
the shrinking filter keeps the first occurrence of each value of `ys` that is in the set, in
order, removing it from the set. -/
def UniqueFilterSpec : Prop :=
  ∀ (K : Type) (hash : K → JInt .u64) (equal : K → K → Bool)
    (keyIsBits : Bool) (keyLayout : JuliaLean.src.genericmemory_c.DictLayout)
    (s : MutableMemory K) (ys zs : List K),
    let ops := setDictRuntime hash equal keyIsBits keyLayout
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
    let grown := setVecRun (uniqueFilterRun ops (growFilter (setLacks ops) (setAdd ops)) zs ys ys) s
    let shrunk := setVecRun (uniqueFilterRun ops (shrinkFilter (setHas ops) (setRemove ops)) zs ys zs) s
    let fresh := firstOccurrences ops.equal (ys.filter (fun y => !zs.any (ops.equal y)))
    let kept := firstOccurrences ops.equal (ys.filter (fun y => zs.any (ops.equal y)))
    grown = (.ok (fresh, ys.map (fun _ => true)), s) ∧
    shrunk = (.ok (kept, zs.map (fun z => !kept.any (ops.equal z))), s)

/-- `intersect(itr, itrs...)` (array.jl:3198; docstring in abstractset.jl: "Construct the set
containing those elements which appear in all of the arguments. The first argument controls what
kind of container is returned. If this is an array, it maintains the order in which elements
first appear.") for arguments holding values of any types: with `T = promote_eltype(itr,
itrs...)` (`isT`), `Set{T}(itr)` (set.jl, keys converted by dict.jl), abstractset.jl's
`intersect!`, `_shrink_filter!` and the typed literal, when every conversion `convert(T, x)` of a
value of `itr` succeeds the result is a fresh valid vector of the distinct values of `itr` (under
`isequal`) that appear in every other argument, in order of first appearance, converted to `T`;
when a conversion fails, an error is raised. -/
def IntersectSpec : Prop :=
  ∀ (K : Type) (ops : JuliaLean.base.set.DictRuntime K) (isT : K → Bool)
    (convert : K → Except Error K) (layout : Option MemoryLayout) (s : MutableMemory K) (itr : List K) (itrs : List (List K)),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops → ConvertsTo isT convert →
    itr.length < 2 ^ 62 →
    let toT := fun x => if isT x then Except.ok x else convert x
    let key := convertingKey ops isT convert
    let inAll := fun (x : K) => itrs.all (fun l => l.any (ops.equal x))
    let run := setVecRun (intersect (m := SetVecM K) (fun _ _ => ())
      (setFromValuesKey ops key)
      (fun u itrs => do
        setRunG ops key
          (JuliaLean.base.abstractset.intersectBangAbstractSetMany (setCallsKey K ops key)) itrs
        pure u)
      (shrinkFilter (setHasG ops) (setRemoveG ops)) (setVecLiteralConv layout isT convert) itr itrs) s
    ((∀ x ∈ itr, ∃ y, toT x = .ok y) →
      ∃ h ys, run.1 = .ok h ∧ run.2.validVector h ∧
        ((firstOccurrences ops.equal itr).filter inAll).mapM toT = .ok ys ∧
        run.2.contents h = ys.map some) ∧
    ((∃ x ∈ itr, ∀ y, toT x ≠ .ok y) → ∃ e, run.1 = .error e)

def SetdiffSpec : Prop :=
  ∀ (K : Type) (ops : JuliaLean.base.set.DictRuntime K) (isT : K → Bool)
    (convert : K → Except Error K) (layout : Option MemoryLayout) (s : MutableMemory K) (itr : List K) (itrs : List (List K)),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops → ConvertsTo isT convert →
    itr.length < 2 ^ 62 → (∀ x ∈ itr, isT x = true) →
    let key := convertingKey ops isT convert
    let inNone := fun (x : K) => itrs.all (fun l => !l.any (ops.equal x))
    let run := setVecRun (setdiff (m := SetVecM K) (fun _ => ()) (setFromValuesKey ops key)
      (fun u itrs => do
        setRunG ops key
          (JuliaLean.base.abstractset.setdiffBangAbstractSetMany (setCallsKey K ops key)) itrs
        pure u)
      (shrinkFilter (setHasG ops) (setRemoveG ops)) (setVecLiteralConv layout isT convert) itr itrs) s
    ∃ h, run.1 = .ok h ∧ run.2.validVector h ∧
      run.2.contents h = ((firstOccurrences ops.equal itr).filter inNone).map some

/-- The `push!`es of `grow_to!(dest, itr, st)` (array.jl:935-951) from element type `t` and
geometry `g` over `xs`, with `push_widen` (array.jl:922-933) for a value that is not an instance:
`sizehint!(empty(dest, T'), length(dest))`, `append!(new, dest)`, `push!(new, el)` on the
`promote_typejoin` type `T'`. The result is the final element type and geometry. -/
def growToPlan {Tag α : Type} (layout : Tag → MemoryLayout) (L : TypeLattice Tag α) :
    Tag → VectorGeometry → List α → Except Error (Tag × VectorGeometry)
  | t, g, [] => .ok (t, g)
  | t, g, x :: xs =>
    if L.isa x t then (growendPlan (layout t) g 1).bind fun g' => growToPlan layout L t g' xs
    else
      let u := L.join t (L.typeof x)
      (sizehintPlan (layout u) emptyGeometry g.length false true).bind fun g1 =>
        (growendPlan (layout u) g1 g.length).bind fun g2 =>
          (growendPlan (layout u) g2 1).bind fun g3 => growToPlan layout L u g3 xs

def GrowToSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → DictLayout) (L : TypeLattice Tag α) (s : MutableMemory α)
    (h : Nat) (t et : Tag) (v1 : α) (xs : List α),
    s.validVector h → s.contents h = [] →
    let lay := fun u => MemoryLayoutMetadata.ofRuntime (layout u)
    let g := geometryOf s h
    let grown := fun (start : List α) (r : TypedVector Tag) (next : MutableMemory α) =>
      next.validVector r.2 ∧ next.contents r.2 = (start ++ xs).map some ∧
      (∀ v ∈ start ++ xs, L.isa v r.1 = true) ∧ ((∀ v ∈ xs, L.isa v t = true) → r = (t, h))
    FollowsSteps (growToPlan layout L t g xs) ((typedGrowTo lay L (t, h) xs).run s) (grown []) ∧
    (L.isa v1 t = true →
      FollowsSteps ((growendPlan (layout t) g 1).bind fun g' => growToPlan layout L t g' xs)
        ((typedCollectWithFirstPush lay L (t, h) v1 [] xs).run s) (grown [v1])) ∧
    FollowsSteps
      (match xs with
       | [] => .ok (et, emptyGeometry)
       | x :: rest => (growendPlan (layout (L.typeof x)) emptyGeometry 1).bind fun g' =>
           growToPlan layout L (L.typeof x) g' rest)
      ((typedCollectUnknown lay L et xs).run s)
      (fun r next => next.validVector r.2 ∧ next.contents r.2 = xs.map some ∧ (xs = [] → r.1 = et) ∧
        (∀ v ∈ xs, L.isa v r.1 = true) ∧
        (∀ x rest, xs = x :: rest → (∀ v ∈ rest, L.isa v (L.typeof x) = true) → r.1 = L.typeof x))

def literalNtupleOfValue {α : Type} (f : I → I) (k : IntegerValue) :
    StateT (List (Option α)) (Except Error) (List I) :=
  if k.val < 0 then throw (.argument ("tuple length should be ≥ 0, got " ++ toString k.val))
  else pure ((List.range k.val.toNat).map (fun j : Nat => f (JInt.wrap .i64 ((j : Int) + 1))))

/-- `_cat(n, x::Integer...)` (array.jl:2363), the method of `cat(x::Integer...; dims = n)`
(`cat` docstring in abstractarray.jl: "Concatenate the input arrays along the dimensions specified
in `dims`"), for a dimension of every `Integer` type: the integers are promoted to one type by
`[x...]` (`vect`, array.jl:183; promotion and conversion are promotion.jl's, any functions here)
and, for `n ≥ 1`, the result has dimensions `(1, ..., 1, length(x))` with `n - 1` leading ones,
holding them in order; when `n - 1` (the promoted `-` of int.jl, or the integer type's) is
negative, `ntuple` raises `ArgumentError`. A failing conversion raises its error. -/
def CatIntegersSpec : Prop :=
  ∀ (α β T : Type) (ops : BigIntegerOps) (promote : List β → T) (convert : T → β → Except Error α)
    (homogeneous : Bool) (n : IntegerValue) (xs : List β) (old : List (Option α)),
    ops.Lawful → xs.length < 2 ^ 62 →
    let run := (catIntegers (m := StateT (List (Option α)) (Except Error))
      (fun vals => vectPromoted (fun vs => pure (promote vs)) (fun t vals =>
        typedLiteral (fun k => liftLiteralState (literalAllocateAs t k))
          (convertedLiteralSetter (convert t)) homogeneous vals) vals)
      (fun n o => n.subInt ops o) literalNtupleOfValue literalReshape n xs).run old
    (∀ e, xs.mapM (convert (promote xs)) = .error e → run = .error e) ∧
    (∀ ys, xs.mapM (convert (promote xs)) = .ok ys →
      ((n.subInt ops one).val < 0 → ∃ message, run = .error (.argument message)) ∧
      (1 ≤ n.val → run = .ok ((promote xs,
        List.replicate (n.val - 1).toNat 1 ++ [(xs.length : Int)]), ys.map some)))

def FilterBangSpec : Prop :=
  ∀ (K : Type) (layout : MemoryLayoutMetadata) (f : K → Except Error (Option Bool)),
    EveryAbstractVector layout 0 (fun σ V contents valid s =>
      let run := setVecRunG (vecFilterBangG (fun x => liftV (baseLift (boolResult f x)))
        (⟨V⟩ : VectorOf σ K)) s
      (∀ xs : List K, contents s = xs.map some →
        (∀ bs, xs.mapM (boolResult f) = .ok bs → (∃ w, run.1 = .ok w) ∧ valid run.2 ∧
          contents run.2 = ((xs.zip bs).filter (·.2)).map (fun p => some p.1)) ∧
        (∀ e, xs.mapM (boolResult f) = .error e → run.1 = .error e)) ∧
      (∀ (pre : List K) rest, contents s = pre.map some ++ none :: rest →
        (∀ bs, pre.mapM (boolResult f) = .ok bs → run.1 = .error .undefinedReference) ∧
        (∀ e, pre.mapM (boolResult f) = .error e → run.1 = .error e)))

/-- `Int(n)` for a length of every `Integer` type. -/
def valueToInt (ops : BigIntegerOps) (n : IntegerValue) : Except Error I := n.toInt ops

def IteratorAllocationSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (target : Tag)
    (l : MemoryLayout) (heap : VectorHeap α) (n : IntegerValue) (axs : List I),
    layout target = some l → ops.Lawful →
    let toInt := fun len => liftM (valueToInt ops len)
    let byLength := (arrayForLength toInt (heapVectorAllocate (α := α) layout) target n).run heap
    (arrayForUnknown (heapVectorAllocate (α := α) layout) target).run heap =
      freshShapeAllocation target [0] heap ∧
    (¬ n.fits → byLength = .error .inexact) ∧
    (n.fits → byLength = allocOutcome l target [n.val] heap ∧
      (arrayFor (fun (len : IntegerValue) (_ : Unit) => pure len)
        (fun T _ len => arrayForLength toInt (heapVectorAllocate (α := α) layout) T len)
        target n ()).run heap = allocOutcome l target [n.val] heap) ∧
    (arrayForShape (shapedCollectorAllocate (α := α) layout pure) target axs).run heap =
      allocOutcome l target (axs.map (fun d => d.val)) heap

def SimilarForSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps) (target : Tag) (heap : VectorHeap α) (c : HeapArray Tag)
    (n : IntegerValue) (axs : List I),
    ops.Lawful → heapDimensionsFit c.dimensions = true → c.dimensions.prod < 2 ^ 63 →
    let byLength := (similarForLength
      (fun c T len => nativeLengthSimilar layout (valueToInt ops) c T len) c target () n).run heap
    (similarForGeneric (fun c T => heapSimilarType layout T c) c target () () ()).run heap =
      freshShapeAllocation target c.dimensions heap ∧
    (similarForUnknown (fun c T (n : I) => nativeLengthSimilar layout (fun n : I => .ok n) c T n)
      c target ()).run heap = freshShapeAllocation target [0] heap ∧
    (0 ≤ n.val → n.val < 2 ^ 63 → byLength = freshShapeAllocation target [n.val.toNat] heap) ∧
    (¬ n.fits → byLength = .error .inexact) ∧
    (n.fits → n.val < 0 → ∃ message, byLength = .error (.argument message)) ∧
    ((∀ d ∈ axs, 0 ≤ d.val) → (axs.map (fun d => d.val.toNat)).prod < 2 ^ 63 →
      (similarForAxes (fun c T axs => nativeAxesSimilar layout pure c T axs) c target () axs).run heap =
        freshShapeAllocation target (axs.map (fun d => d.val.toNat)) heap)

def CompleteIteratorAllocatorsSpec : Prop := IteratorAllocationSpec ∧ SimilarForSpec

def KnownEltypeCollectionSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → MemoryLayoutMetadata) (t : IntTy) (eltype : Tag) (length : List α → JInt t) (axes : List α → List I)
    (cont : HeapArray Tag) (xs : List α) (heap : VectorHeap α) (s : MutableMemory α),
    xs.length < 2 ^ 62 →
    ((length xs).val = xs.length →
      (knownLengthCollect layout (fun _ => eltype) length indexConvert
        (heapIterCopy (fun _ => true) id (fun x => .ok x)) cont xs).run heap =
        .ok (freshHeapArray eltype [xs.length] (xs.map some) heap)) ∧
    ((∀ d ∈ axes xs, 0 ≤ d.val) → ((axes xs).map (fun d => d.val.toNat)).prod = xs.length →
      (knownShapeCollect layout (fun _ => eltype) axes pure
        (heapIterCopy (fun _ => true) id (fun x => .ok x)) cont xs).run heap =
        .ok (freshHeapArray eltype ((axes xs).map (fun d => d.val.toNat)) (xs.map some) heap)) ∧
    (∃ next, (knownUnknownCollect (layout eltype) cont xs).run s = (.ok s.arrays.length, next) ∧
      next.validVector s.arrays.length ∧ next.contents s.arrays.length = xs.map some)

def rangeGetIndices (r : I × I) (ks : List I) : VectorM I (Nat × Nat) :=
  JuliaLean.base.multidimensional.getindexAbstract (m := VectorM I)
    (fun (r : I × I) (is : List (List I)) => do
      for ks in is do
        for k in ks do
          if !(1 ≤ k.val ∧ k.val ≤ (unitRangeLength r).val) then throw .bounds)
    (fun (_ : Unit) a is => pure (JuliaLean.base.multidimensional.maybeReshapeLinear a is))
    (JuliaLean.base.multidimensional.unsafeGetindex (m := VectorM I) (AX := Nat)
      (fun is : List (List I) => is.map List.length)
      (fun _ shape => do
        let h ← heapAllocate (α := I) shape.prod
        pure (h, shape.prod))
      (fun d => [d.2]) (fun n => JInt.wrap .i64 n)
      (fun _ _ => throw (.dimensionMismatch "output array is the wrong size"))
      (JuliaLean.base.multidimensional.unsafeGetindexBangOne
        (JuliaLean.base.multidimensional.generateUnsafeGetindexBody (m := VectorM I)
          (fun d : Nat × Nat => intRange one (JInt.wrap .i64 d.2))
          (fun _ => pure (one, one)) (fun _ (s : I) => pure (s + one, s + one))
          (fun ks : List I => ks)
          (fun (r : I × I) (j : List I) => pure (r.1 + (j.headD one - one)))
          (fun (d : Nat × Nat) (v : I) (k : I) => do heapSet d.1 v k; pure d))))
    () r [ks]

/-- `filter(f, a::AbstractArray)` (array.jl:3027) for a unit range `lo:hi` of `Int`, whose
`IndexStyle` is `IndexLinear`, so the logical-indexing branch is never taken (its callees are
no-ops here): `idxs = Vector{Int}(undef, length(a))` is a fresh heap vector, `eachindex(a)` is
`1:length(a)`, `a[idx] = lo + (idx - 1)`, `f(ai)::Bool` is `boolResult f`, `resize!(idxs, j-1)`
keeps the first `j-1` slots, `res = a[idxs]` is `rangeGetIndices`, `empty!(idxs)` empties the
buffer and `sizehint!(idxs, 0)` leaves it unchanged. -/
def rangeFilter (f : I → Except Error (Option Bool)) (r : I × I) : VectorM I (Nat × Nat) :=
  filterAbstractArray (m := VectorM I) (fun _ => pure true) (fun _ => (pure () : VectorM I Unit))
    (fun _ mask _ => pure mask) (fun _ _ => pure (0, 0))
    (fun r => pure (unitRangeLength r))
    (fun n => heapAllocate (α := I) n.val.toNat)
    (fun r => pure (intRange one (unitRangeLength r)))
    (fun idxs idx j => heapSet idxs idx j)
    (fun (r : I × I) (k : I) => pure (r.1 + (k - one)))
    (fun x => liftM (boolResult f x))
    (fun b n => modify fun heap => heap.set b ((heap[b]?.getD []).take n.val.toNat))
    (fun r idxs => do
      let slots ← heapSlots (α := I) idxs
      rangeGetIndices r (slots.filterMap id))
    (fun idxs => modify fun (heap : VectorHeap I) => heap.set idxs [])
    (fun _ _ => pure ()) r

/-- `filter(f, a)` for an abstract array that is not an `Array` (array.jl:3027; docstring at
array.jl:2990-3013: "Return a copy of collection `a`, removing elements for which `f` is
`false`", with the example `filter(isodd, 1:10)`), for a unit range `lo:hi` of `Int`: when `f`
returns a `Bool` for every element, the result is a fresh `Vector{Int}` holding, in order, the
elements of the range for which `f` is `true`, the index buffer the call allocates ends empty, and
every existing array is unchanged; otherwise the first element on which `f` throws (its error) or
returns a non-`Bool` (`TypeError`) decides the error. -/
def FilterAbstractArraySpec : Prop :=
  ∀ (f : I → Except Error (Option Bool)) (lo hi : I) (heap : VectorHeap I),
    hi.val - lo.val + 1 < 2 ^ 62 →
    let values := (List.range (hi.val - lo.val + 1).toNat).map
      (fun (k : Nat) => JInt.wrap .i64 (lo.val + k))
    let run := (rangeFilter f (lo, hi)).run heap
    (∀ bs, values.mapM (boolResult f) = .ok bs →
      let kept := ((values.zip bs).filter (·.2)).map (fun p => some p.1)
      run = .ok ((heap.length + 1, kept.length), heap ++ [[], kept])) ∧
    (∀ e, values.mapM (boolResult f) = .error e → run = .error e)

def FilterCurriedSpec : Prop :=
  ∀ (F A B σ τ : Type) (showInt typeName : Int → String)
    (stableTypeFunction : (F → A → Unit → B) → σ) (stableTypeValue : F → τ)
    (filter : F → A → B) (f : F) (x : A),
    ∃ fix,
      filterFix1 showInt typeName stableTypeFunction stableTypeValue
        (fun g a _ => filter g a) f = .ok fix ∧
      JuliaLean.base.operators.fixOneCall fix x () = filter f x

/-- `deleteat!([1, 2, 3], -1:typemax(Int))`: `length(r)` wraps to a negative count and
`_deleteat!` raises `ArgumentError` instead of `BoundsError`. -/
theorem deleteatRangeSpec_refuted : ¬ DeleteatRangeSpec := by
  intro h
  have bad := (h Int ⟨none, boxedDictLayout, True.intro⟩ exactIntegerOps exactIntegerOps_lawful [some 1, some 2, some 3]
    (.bit .i64 ⟨JInt.wrap .i64 (-1), JInt.typemax .i64⟩)
    (MutableMemory.initial [some 1, some 2, some 3]) (by decide) rfl (by decide) (by decide)).2.2.2.2
    (by decide) ⟨_, rfl⟩ (by unfold IntegerValue.fits; decide) (by decide)
  have errors := congrArg Prod.fst bad
  revert errors
  decide
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round9
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4

def LiveMemorySize (s : MutableMemory α) (a : Nat) : Prop :=
  ∀ vector slots, s.arrays[a]? = some vector → s.memories[vector.reference.1]? = some slots →
    slots.length < maxIntVal

def clearSpan {unsetRuntime : DictLayout} (slots : List (Option α)) (start count : Nat) : List (Option α) :=
  slots.mapIdx (fun index value => if start ≤ index ∧ index < start + count then expectedUnset unsetRuntime value else value)

def deletionState {unsetRuntime : DictLayout} (s : MutableMemory α) (a : Nat) (vector : MutableVector)
    (slots : List (Option α)) (count : Nat) (front : Bool) : MutableMemory α :=
  let offset := (vector.reference.2.val - 1).toNat
  let newlen := vector.size.val.toNat - count
  let start := if front then offset else offset + newlen
  let reference := if front && newlen != 0 then
    (vector.reference.1, JInt.wrap .i64 (vector.reference.2.val + count)) else vector.reference
  { s with
    memories := s.memories.set vector.reference.1 (clearSpan (unsetRuntime := unsetRuntime) slots start count)
    arrays := s.arrays.set a { vector with reference := reference, size := JInt.wrap .i64 newlen } }

def DeletebegSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (a : Nat) (d : IntegerValue), s.validVector a → LiveMemorySize s a →
    let n := (s.contents a).length
    let run := (deletebeg (mutableStorage layout) (integerToInt ops) a d).run s
    (¬d.fits → run = (.error .inexact, s)) ∧
    (d.fits → (d.val < 0 ∨ (n : Int) < d.val) →
      ∃ error : Error, run = (.error error, s)) ∧
    (0 ≤ d.val → d.val ≤ n → ∀ vector slots,
      s.arrays[a]? = some vector → s.memories[vector.reference.1]? = some slots →
      let after := deletionState (unsetRuntime := layout.runtime) s a vector slots d.val.toNat true
      run = (.ok (), after) ∧ after.validVector a ∧
      after.contents a = (s.contents a).drop d.val.toNat)

def DeleteendSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (a : Nat) (d : IntegerValue), s.validVector a → LiveMemorySize s a →
    let n := (s.contents a).length
    let run := (deleteend (mutableStorage layout) (integerToInt ops) a d).run s
    (¬d.fits → run = (.error .inexact, s)) ∧
    (d.fits → (d.val < 0 ∨ (n : Int) < d.val) →
      ∃ error : Error, run = (.error error, s)) ∧
    (0 ≤ d.val → d.val ≤ n → ∀ vector slots,
      s.arrays[a]? = some vector → s.memories[vector.reference.1]? = some slots →
      let after := deletionState (unsetRuntime := layout.runtime) s a vector slots d.val.toNat false
      run = (.ok (), after) ∧ after.validVector a ∧
      after.contents a = (s.contents a).take (n - d.val.toNat))
end JuliaLean.Proofs.base.array.round9
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem deleteatSpec : DeleteatSpec := by
  intro α layout s handle i delta hvalid
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hwl := vwWindow_length h
  have hc := h.contents
  have hn0 := h.2.2.2.1
  have hnb := ival_bounds n
  have hib := ival_bounds i
  have hlen : ((s.contents handle).length : Int) = n.val := by rw [hc, hwl]; omega
  have ha := h.1
  have hsz : (⟨(mem, off), n⟩ : MutableVector).size = n := rfl
  simp only
  intro hsmall
  rw [hlen] at hsmall
  have hone : (one : I).val = 1 := ival_one
  -- the in-range single deletion, shared by `deleteat!` and `popat!`
  have hdel1 : 1 ≤ i.val → i.val ≤ n.val → ∃ next,
      (vecDeleteat α (layout := layout) handle i one).run s = (.ok (), next) ∧ next.validVector handle ∧
      next.contents handle = (s.contents handle).eraseIdx (i.val - 1).toNat := by
    intro hi1 hin
    obtain ⟨next, hrun, hv, hcn, _⟩ := vwDeleteat_run (layout := layout) s handle mem off n slots h i one hsmall hi1
      hin (by rw [hone]; omega) (by rw [hone]; omega)
    refine ⟨next, hrun, hv, ?_⟩
    rw [hcn, hc, List.eraseIdx_eq_take_drop_succ, hone,
      show (i.val - 1 + 1).toNat = (i.val - 1).toNat + 1 by omega]
  have hget := fun (hi1 : 1 ≤ i.val) (hin : i.val ≤ n.val) =>
    vwGet_run s handle mem off n slots h i ⟨hi1, hin⟩
  refine ⟨fun hd => vwDeleteat_negative (layout := layout) s handle _ ha i delta hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro hd hbad
    rw [hlen] at hbad
    rcases hbad with hbad | hbad | hbad
    · exact vwDeleteat_index (layout := layout) s handle _ ha i delta hd (Or.inl hbad)
    · exact vwDeleteat_index (layout := layout) s handle _ ha i delta hd (Or.inr hbad)
    · by_cases hi : i.val < 1 ∨ n.val < i.val
      · exact vwDeleteat_index (layout := layout) s handle _ ha i delta hd hi
      · exact vwDeleteat_count (layout := layout) s handle _ ha i delta hd hsmall (show 1 ≤ i.val by omega)
          (show i.val ≤ n.val by omega) hbad
  · intro hd hi1 hin hdi
    rw [hlen] at hin hdi
    obtain ⟨next,hrun,hv,hcn,hfa,_,_⟩ := vwDeleteat_run (layout := layout) s handle mem off n slots h i delta hsmall
      hi1 hin hd hdi
    exact ⟨next, hrun, hv, by rw [hcn, hc], hfa⟩
  · intro hbad
    rw [hlen] at hbad
    have := vwDeleteat_index (layout := layout) s handle _ ha i one (by rw [hone]; omega) hbad
    simp only [deleteatIndex, Bool.false_eq_true, ite_false, stateExcept_bind, stateExcept_pure,
      this]
  · intro hi1 hin
    rw [hlen] at hin
    obtain ⟨next, hrun, hv, hcn⟩ := hdel1 hi1 hin
    refine ⟨next, ?_, hv, hcn⟩
    simp only [deleteatIndex, Bool.false_eq_true, ite_false, stateExcept_bind, stateExcept_pure,
      hrun]
  · intro hbad
    rw [hlen] at hbad
    simp only [popat, stateExcept_bind, vwGet_outside s handle _ ha i hbad]
  · intro hi1 hnone
    have hin : i.val ≤ n.val := by
      have := (List.getElem?_eq_some_iff.mp hnone).choose
      rw [hc, hwl] at this
      omega
    rw [hc] at hnone
    simp only [popat, stateExcept_bind, hget hi1 hin, hnone]
  · intro x hi1 hx
    have hin : i.val ≤ n.val := by
      have := (List.getElem?_eq_some_iff.mp hx).choose
      rw [hc, hwl] at this
      omega
    obtain ⟨next, hrun, hv, hcn⟩ := hdel1 hi1 hin
    rw [hc] at hx
    refine ⟨next, ?_, hv, hcn⟩
    simp only [popat, stateExcept_bind, hget hi1 hin, hx, hrun, stateExcept_pure]
  · intro default hbad
    rw [hlen] at hbad
    have hnot : ¬ (1 ≤ i.val ∧ i.val ≤ n.val) := by omega
    simp only [popatDefault, stateExcept_bind, mutableLength_run s handle _ ha, hsz, hnot,
      ite_false, stateExcept_pure]
  · intro default hi1 hnone
    have hin : i.val ≤ n.val := by
      have := (List.getElem?_eq_some_iff.mp hnone).choose
      rw [hc, hwl] at this
      omega
    rw [hc] at hnone
    have hyes : (1 ≤ i.val ∧ i.val ≤ n.val) := ⟨hi1, hin⟩
    simp only [popatDefault, stateExcept_bind, mutableLength_run s handle _ ha, hsz, hyes,
      and_self, ite_true, hget hi1 hin, hnone]
  · intro default x hi1 hx
    have hin : i.val ≤ n.val := by
      have := (List.getElem?_eq_some_iff.mp hx).choose
      rw [hc, hwl] at this
      omega
    obtain ⟨next, hrun, hv, hcn⟩ := hdel1 hi1 hin
    rw [hc] at hx
    have hyes : (1 ≤ i.val ∧ i.val ≤ n.val) := ⟨hi1, hin⟩
    refine ⟨next, ?_, hv, hcn⟩
    simp only [popatDefault, stateExcept_bind, mutableLength_run s handle _ ha, hsz, hyes,
      and_self, ite_true, hget hi1 hin, hx, hrun, stateExcept_pure]

theorem deleteatIndexSpec : DeleteatIndexSpec := by
  intro α layout t s handle i hvalid
  simp only
  intro hsmall
  rw [deleteatIndex_lengthToInt_run (layout := layout)]
  have hspec := deleteatSpec α layout s handle (JInt.wrap .i64 i.val) one hvalid hsmall
  refine ⟨fun hx => by simp only [hx, ite_false], fun hlo hhi hbad => ?_, fun hi1 hin => ?_⟩
  · have hx : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := ⟨hlo, hhi⟩
    have hw : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hx
    simp only [hx, and_self, ite_true]
    exact hspec.2.2.2.1 (by rw [hw]; exact hbad)
  · have hx : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max :=
      ⟨Int.le_trans (by decide) hi1,
        Int.le_trans hin (Int.le_trans (Int.le_of_lt hsmall) (by decide))⟩
    have hw : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hx
    simp only [hx, and_self, ite_true]
    have hr := hspec.2.2.2.2.1 (by rw [hw]; exact hi1) (by rw [hw]; exact hin)
    rw [hw] at hr
    exact hr
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round7
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

/-- Clearing just the removed physical slots leaves every other reference slot intact. -/
def clearSpan {unsetRuntime : DictLayout} (slots : List (Option α)) (start count : Nat) : List (Option α) :=
  slots.mapIdx (fun index value => if start ≤ index ∧ index < start + count then expectedUnset unsetRuntime value else value)

/-- Full heap and header frame for front/back deletion. -/
def deletionState {unsetRuntime : DictLayout} (s : MutableMemory α) (a : Nat) (vector : MutableVector)
    (slots : List (Option α)) (count : Nat) (front : Bool) : MutableMemory α :=
  let offset := (vector.reference.2.val - 1).toNat
  let newlen := vector.size.val.toNat - count
  let start := if front then offset else offset + newlen
  let reference := if front && newlen != 0 then
    (vector.reference.1, JInt.wrap .i64 (vector.reference.2.val + count)) else vector.reference
  { s with
    memories := s.memories.set vector.reference.1 (clearSpan (unsetRuntime := unsetRuntime) slots start count)
    arrays := s.arrays.set a { vector with reference := reference, size := JInt.wrap .i64 newlen } }

/-- Live backing Memory may come from the ordinary allocator or non-union unsafe_wrap. -/
def LiveVectorLayout (layout : MemoryLayout) (capacity : Nat) : Prop :=
  capacity < maxIntVal ∧
  capacity * (if layout.isboxed then 8 else layout.size) +
    (if layout.isunion then capacity else 0) < maxIntVal ∧
  (layout.isunion = true → memoryFits layout capacity)

/-- The operations required by filter!: indexed stores and valid tail deletion. -/
def SupportsFilter (U : UserVector σ K) : Prop :=
  (∀ s x i, 0 ≤ U.offset s i → U.offset s i < (U.slots s).length →
    ∃ after, U.setAt s x i = .ok after ∧ U.first after = U.first s ∧
      U.slots after = (U.slots s).set (U.offset s i).toNat (some x)) ∧
  (∀ s j k, 0 ≤ U.offset s j → U.offset s j ≤ (U.slots s).length →
    U.offset s k = (U.slots s).length - 1 →
    ∃ after, U.deleteRange s j k = .ok after ∧ U.first after = U.first s ∧
      U.slots after = (U.slots s).take (U.offset s j).toNat)

/-- Nonempty axes have native endpoints. Empty axes may wrap their last endpoint. -/
def UserAxes (U : UserVector σ K) (s : σ) : Prop :=
  (U.slots s).length ≤ 9223372036854775807 ∧
  ((U.slots s).length ≠ 0 →
    IntTy.i64.min ≤ (U.first s).val + (U.slots s).length - 1 ∧
    (U.first s).val + (U.slots s).length - 1 ≤ IntTy.i64.max)

/-- The native-Int-axis filtering domain, including a last index of typemax(Int). -/
def EveryAbstractVectorIn {K : Type} (layout : DictLayout)
    (P : (σ : Type) → VectorOps σ K → (σ → List (Option K)) → (σ → Prop) → σ → Prop) : Prop :=
  (∀ (s : MutableMemory K) (h : Nat), s.validVector h →
    vectorMemory s h (LiveVectorLayout layout) →
    P (MutableMemory K) (storeVectorOps (MemoryLayoutMetadata.ofRuntime layout) h) (fun s => s.contents h)
      (fun s => s.validVector h) s) ∧
  (∀ (σ : Type) (U : UserVector σ K), SupportsFilter U → ∀ s, UserAxes U s →
    P σ (userVectorOps U) U.slots (fun _ => True) s)

def filterVector {σ K : Type} (predicate : K → SetVecG σ K Bool) (v : VectorOf σ K) :
    SetVecG σ K (VectorOf σ K) :=
  filterBang (fun v => liftV v.ops.firstindex) (fun v => liftV v.ops.lastindex)
    (fun v value index => liftV (v.ops.setAt value index)) predicate
    (fun _ index => liftV (baseLift (nextIntIndex index)))
    (fun v => v.ops.isVector) (fun v n => liftV (v.ops.resizeTo n))
    (fun v n => liftV (v.ops.sizehintTo n)) (fun v j k => liftV (v.ops.deleteRange j k)) v

/-- The documented filtering promise for native-Int-axis vectors. -/
def NativeAxisFilterBangSpec : Prop :=
  ∀ (K : Type) (layout : DictLayout) (f : K → Except Error (Option Bool)),
    EveryAbstractVectorIn layout (fun σ V contents valid s =>
      let run := setVecRunG (filterVector (fun x => liftV (baseLift (boolResult f x)))
        (⟨V⟩ : VectorOf σ K)) s
      (∀ xs : List K, contents s = xs.map some →
        (∀ bs, xs.mapM (boolResult f) = .ok bs → (∃ v, run.1 = .ok v) ∧ valid run.2 ∧
          contents run.2 = ((xs.zip bs).filter (·.2)).map (fun p => some p.1)) ∧
        (∀ error, xs.mapM (boolResult f) = .error error → run.1 = .error error)) ∧
      (∀ (pre : List K) rest, contents s = pre.map some ++ none :: rest →
        (∀ bs, pre.mapM (boolResult f) = .ok bs → run.1 = .error .undefinedReference) ∧
        (∀ error, pre.mapM (boolResult f) = .error error → run.1 = .error error)))

private def maxAxisFirst : I := JInt.wrap .i64 9223372036854775807

private def maxAxisVector : UserVector (List (Option Unit)) Unit where
  first := fun _ => maxAxisFirst
  slots := id
  setAt := fun s x i =>
    let offset := i.val - maxAxisFirst.val
    if 0 ≤ offset ∧ offset < (s.length : Int) then
      .ok (s.set offset.toNat (some x))
    else .error .bounds
  pushBack := fun s x => .ok (s ++ [some x])
  deleteRange := fun s j k =>
    let firstOffset := j.val - maxAxisFirst.val
    let lastOffset := k.val - maxAxisFirst.val
    if 0 ≤ firstOffset ∧ firstOffset ≤ (s.length : Int) ∧
        lastOffset = (s.length : Int) - 1 then
      .ok (s.take firstOffset.toNat)
    else .error .bounds

private theorem maxAxisVector_supports : SupportsFilter maxAxisVector := by
  constructor
  · intro s x i hlow hhigh
    change 0 ≤ i.val - maxAxisFirst.val at hlow
    change i.val - maxAxisFirst.val < (s.length : Int) at hhigh
    refine ⟨s.set (i.val - maxAxisFirst.val).toNat (some x), ?_, rfl, rfl⟩
    simp [maxAxisVector, hlow, hhigh]
    omega
  · intro s j k hlow hlength hlast
    change 0 ≤ j.val - maxAxisFirst.val at hlow
    change j.val - maxAxisFirst.val ≤ (s.length : Int) at hlength
    change k.val - maxAxisFirst.val = (s.length : Int) - 1 at hlast
    refine ⟨s.take (j.val - maxAxisFirst.val).toNat, ?_, rfl, ?_⟩
    · simp [maxAxisVector, hlow, hlength, hlast]
      omega
    · simp [maxAxisVector, UserVector.offset]

private theorem maxAxisVector_user_axes :
    UserAxes maxAxisVector ([some ()] : List (Option Unit)) := by
  constructor
  · decide
  · intro _
    have hfirst : maxAxisFirst.val = 9223372036854775807 := by
      dsimp [maxAxisFirst]
      decide
    change IntTy.i64.min ≤ maxAxisFirst.val + (1 : Int) - 1 ∧
      maxAxisFirst.val + (1 : Int) - 1 ≤ IntTy.i64.max
    rw [hfirst]
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
private def maxAxisFilterRun :
    Except Error (VectorOf (List (Option Unit)) Unit) × List (Option Unit) :=
  setVecRunG
    (filterVector (fun x => liftV (baseLift (boolResult (fun _ : Unit => .ok (some true)) x)))
      (⟨userVectorOps maxAxisVector⟩ : VectorOf (List (Option Unit)) Unit))
    ([some ()] : List (Option Unit))

set_option maxRecDepth 32768 in
private theorem maxAxisFilterRun_error :
    maxAxisFilterRun.1 = .error .bounds := by
  rfl

theorem nativeAxisFilterBangSpec_refuted : ¬ NativeAxisFilterBangSpec := by
  intro hspec
  let layout : DictLayout := boxedDictLayout
  let predicate : Unit → Except Error (Option Bool) := fun _ => .ok (some true)
  let initial : List (Option Unit) := [some ()]
  let vector : VectorOf (List (Option Unit)) Unit := ⟨userVectorOps maxAxisVector⟩
  let run := setVecRunG
    (filterVector (fun x => liftV (baseLift (boolResult predicate x))) vector) initial
  have hsupports : SupportsFilter maxAxisVector := maxAxisVector_supports
  have haxes : UserAxes maxAxisVector initial := maxAxisVector_user_axes
  have hproperty := (hspec Unit layout predicate).2
    (List (Option Unit)) maxAxisVector hsupports initial haxes
  have hcontents : maxAxisVector.slots initial = [some ()] := rfl
  have hpredicates : ([()] : List Unit).mapM (boolResult predicate) = .ok [true] := by
    rfl
  have hsuccess : ∃ result, run.1 = .ok result := by
    simpa [run, vector] using ((hproperty.1 [()] hcontents).1 [true] hpredicates).1
  have hrun : run.1 = .error .bounds := by
    exact maxAxisFilterRun_error
  rcases hsuccess with ⟨result, hresult⟩
  rw [hrun] at hresult
  cases hresult
end round7
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
section
variable {α : Type}

theorem growend_toInt_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf Error m]
    {A Mem R Z : Type} (st : Storage m A Mem R) (toInt : Z → m I) (internal : A → I → I → m Unit)
    (a : A) (d : Z) :
    growend st toInt internal a d = toInt d >>= growend st pure internal a := by
  unfold growend
  simp only [pure_bind]

theorem growendInternal_follows (l : DictLayout) {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (d : I)
    (hd : 0 ≤ d.val) :
    Follows s (growendInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat)
      ((growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s) (fun _ next =>
        next.validVector handle ∧ next.contents handle = vwWindow slots off n ∧
        (∀ w sl, next.arrays[handle]? = some w → next.memories[w.reference.1]? = some sl →
          w.reference.2.val - 1 + w.size.val + d.val ≤ (sl.length : Int)) ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds d
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hother : ∀ (v : MutableVector) h2, h2 ≠ handle → (s.arrays.set handle v)[h2]? = s.arrays[h2]? :=
    fun _ _ hne => List.getElem?_set_ne (fun he => hne he.symm)
  by_cases hov : off.val - 1 + n.val + d.val ≤ 9223372036854775807
  · have hovN : ¬ (typemaxNat < off.val.toNat - 1 + (n.val.toNat + d.val.toNat)) := by
      unfold typemaxNat; omega
    by_cases hs : n.val + d.val < off.val - 1 ∧ (n.val + d.val) / 4 < off.val - 1 - (n.val + d.val)
    · obtain ⟨newoff, slots', hint, hnewoff, hlen, hwin'⟩ :=
        growendInternal_slide (layout := MemoryLayoutMetadata.ofRuntime l) h' d hd hov hs.1 hs.2
      have hsN : n.val.toNat + d.val.toNat < off.val.toNat - 1 ∧
          (n.val.toNat + d.val.toNat) / 4 < off.val.toNat - 1 - (n.val.toNat + d.val.toNat) := by
        omega
      have hplan : growendInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
          .ok ⟨slots.length, (n.val.toNat + d.val.toNat) / 8 + 1, n.val.toNat⟩ := by
        simp only [growendInternalPlan, hovN, hsN, ite_false, ite_true, and_self]
      have hv : VecAt { s with
          memories := s.memories.set mem slots'
          arrays := s.arrays.set handle ⟨(mem, newoff), n⟩ } handle mem newoff n slots' :=
        ⟨List.getElem?_set_self halt, List.getElem?_set_self hlt, by omega, hn0,
          by rw [hlen, hnewoff]; omega, by rw [hlen]; exact hc⟩
      refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' _ => ?_⟩
      refine ⟨(), _, hint, hv.valid, by rw [hv.contents]; exact hwin', ?_, hother _⟩
      intro w sl hw hsl
      rw [List.getElem?_set_self halt] at hw
      cases hw
      rw [List.getElem?_set_self hlt] at hsl
      cases hsl
      simp only
      rw [hlen, hnewoff]
      omega
    · obtain ⟨hnf, hok⟩ := growendInternal_alloc l h' d hd hov hs
      have hsN : ¬ (n.val.toNat + d.val.toNat < off.val.toNat - 1 ∧
          (n.val.toNat + d.val.toNat) / 4 < off.val.toNat - 1 - (n.val.toNat + d.val.toNat)) := by
        omega
      have hkN : max (overallocationNat slots.length) (off.val.toNat - 1 + (n.val.toNat + d.val.toNat)) =
          max (overallocationNat slots.length) (off.val - 1 + n.val + d.val).toNat := by
        congr 1; omega
      have hplan : growendInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
          allocationPlan l (max (overallocationNat slots.length) (off.val - 1 + n.val + d.val).toNat)
            ⟨max (overallocationNat slots.length) (off.val - 1 + n.val + d.val).toNat,
              off.val.toNat, n.val.toNat⟩ := by
        simp only [growendInternalPlan, hovN, hsN, ite_false, hkN]
      generalize hk : max (overallocationNat slots.length) (off.val - 1 + n.val + d.val).toNat = k
        at hplan hnf hok
      have hkge : (off.val - 1 + n.val + d.val).toNat ≤ k := by rw [← hk]; exact Nat.le_max_right _ _
      by_cases hfit : memoryFits l k
      · obtain ⟨D, hint, hDlen, hDwin⟩ := hok hfit
        have hk63 : k < 2 ^ 63 := by have := hfit.1; unfold maxIntVal at this; omega
        have hMlt : s.memories.length < (s.memories ++ [List.replicate k none]).length := by simp
        have hv : VecAt { s with
            memories := (s.memories ++ [List.replicate k none]).set s.memories.length D
            arrays := s.arrays.set handle ⟨(s.memories.length, off), n⟩ } handle
            s.memories.length off n D :=
          ⟨List.getElem?_set_self halt, List.getElem?_set_self hMlt, ho, hn0,
            by rw [hDlen]; omega, by rw [hDlen]; exact hk63⟩
        have hplan' : growendInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
            .ok ⟨k, off.val.toNat, n.val.toNat⟩ := by
          rw [hplan]; simp only [allocationPlan, hfit, ite_true]
        refine ⟨fun e he => (by rw [hplan'] at he; cases he), fun g' _ => ?_⟩
        refine ⟨(), _, hint, hv.valid, by rw [hv.contents]; exact hDwin, ?_, hother _⟩
        intro w sl hw hsl
        rw [List.getElem?_set_self halt] at hw
        cases hw
        rw [List.getElem?_set_self hMlt] at hsl
        cases hsl
        simp only
        rw [hDlen]
        omega
      · refine ⟨fun e he => ?_, fun g' hg' => by
          rw [hplan] at hg'; simp only [allocationPlan, hfit, ite_false] at hg'; cases hg'⟩
        rw [hplan] at he
        simp only [allocationPlan, hfit, ite_false] at he
        cases he
        exact hnf hfit
  · have hplan : growendInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
        .error .overflow := by
      have hovN : typemaxNat < off.val.toNat - 1 + (n.val.toNat + d.val.toNat) := by
        unfold typemaxNat; omega
      simp only [growendInternalPlan, hovN, ite_true]
    have hrun : (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s = (.error .overflow, s) := by
      by_cases hov1 : n.val + d.val ≤ 9223372036854775807
      · exact growendInternal_overflow2 h' d hd hov1 (by omega)
      · exact growendInternal_overflow1 h' d (by omega)
    refine ⟨fun e he => ?_, fun g' hg' => by rw [hplan] at hg'; cases hg'⟩
    rw [hplan] at he
    cases he
    exact hrun

theorem growendSpec : round4.GrowendSpec := by
  intro α l ops hops s handle delta hvalid
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hn0 := h.2.2.2.1
  have hlen := vwWindow_length h
  dsimp only
  rw [VecAt.geometry h, h.contents, growend_toInt_eq, stateExcept_bind, integerToInt_run,
    integerValue_toInt hops]
  refine ⟨fun hf => by rw [if_neg (show ¬ (IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max) from hf)], fun hf hneg => ?_, fun hf hpos => ⟨?_, ?_⟩⟩
  · rw [if_pos (show IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max from hf)]
    exact growend_neg_run s handle _ (by rw [ival_wrap _ (show -9223372036854775808 ≤ delta.val ∧ delta.val ≤ 9223372036854775807 from hf)]; exact hneg)
  · rw [if_pos (show IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max from hf)]
    have hx : (JInt.wrap .i64 delta.val).val = delta.val := ival_wrap _ (show -9223372036854775808 ≤ delta.val ∧ delta.val ≤ 9223372036854775807 from hf)
    obtain ⟨herr, hok⟩ := growend_plan l h (JInt.wrap .i64 delta.val) (by rw [hx]; exact hpos)
    rw [hx] at herr hok
    refine ⟨herr, fun g' hg' => ?_⟩
    obtain ⟨next, mem', off', slots', hrun, hv, harr, hnd, hwin, -⟩ := hok g' hg'
    refine ⟨(), next, hrun, hv.valid, ?_, ?_, ?_⟩
    · rw [hv.contents, vwWindow_length hv, hnd, hlen]
      omega
    · rw [hv.contents, hlen]
      exact hwin
    · intro h2 hne
      rw [harr]
      exact List.getElem?_set_ne (fun he => hne he.symm)
  · intro d n' hd hn'
    have hnn : n' = n := Subtype.ext (by rw [hn', hlen]; omega)
    subst hnn
    rw [← hd]
    exact growendInternal_follows l h d (by rw [hd]; exact hpos)
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
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
variable {α : Type}


theorem iteratorAllocationSpec : round4.IteratorAllocationSpec := by
  intro Tag α layout ops target l heap n axs hl hops
  dsimp only
  have hvec : ∀ x : I, (heapVectorAllocate (α := α) layout target x).run heap =
      allocOutcome l target [x.val] heap := fun x => heapArrayUndef_run layout target l hl [x] heap
  have hconv := integerValue_toInt hops n
  have hlen : (arrayForLength (fun len => liftM (round4.valueToInt ops len))
      (heapVectorAllocate (α := α) layout) target n).run heap =
      if IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max then allocOutcome l target [n.val] heap
      else .error .inexact := by
    simp only [arrayForLength, vector_bind_run, vector_lift_run, round4.valueToInt, hconv]
    by_cases hf : IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max
    · simp only [hf, and_self, ite_true, Except.map, hvec, ival_wrap _ (show -9223372036854775808 ≤ n.val ∧
        n.val ≤ 9223372036854775807 from hf)]
    · simp only [hf, ite_false, Except.map]
  refine ⟨?_, fun hf => ?_, fun hf => ⟨?_, ?_⟩, ?_⟩
  · simp only [arrayForUnknown, hvec]
    unfold allocOutcome round4.freshShapeAllocation arrayAllocError
    simp [memoryFits_zero, ival_zero]
  · rw [hlen, if_neg (show ¬ (IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max) from hf)]
  · rw [hlen, if_pos (show IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max from hf)]
  · simp only [arrayFor, vector_bind_run, vector_pure_run]
    rw [hlen, if_pos (show IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max from hf)]
  · exact heapArrayUndef_run layout target l hl axs heap
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
namespace JuliaLean.Proofs.base.array.round10

open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
open JuliaLean.Proofs.base.array.round6b

/-- `_growbeg!` and `_growbeg_internal!` (base/array.jl:1116-1167; public-operation docstrings at
base/array.jl:1452-1477, 1753-1771, 1844-1860). An existing backing Memory has fewer than
`MAXINTVAL` slots, the element-count limit accepted by `unsafe_wrap` (base/pointer.jl:111-115;
src/array.c:91-101; src/genericmemory.c:118-161). The `validVector` premise keeps the vector window
inside that memory, so its end arithmetic is representable. -/
def GrowbegSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (handle : Nat) (delta : IntegerValue),
    s.validVector handle → vectorMemory s handle (fun memlen => memlen < maxIntVal) →
    let len : Int := (s.contents handle).length
    let g := geometryOf s handle
    let grow := growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) (integerToInt ops)
      (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) handle delta
    let internal := fun d n : I => (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s
    (¬ delta.fits → grow.run s = (.error .inexact, s)) ∧
    (delta.fits → delta.val < 0 → grow.run s = (.error (.argument "grow requires delta >= 0"), s)) ∧
    (delta.fits → 0 ≤ delta.val →
      Follows s (growbegPlan l g delta.val.toNat) (grow.run s) (fun _ next =>
        next.validVector handle ∧ ((next.contents handle).length : Int) = len + delta.val ∧
        (next.contents handle).drop delta.val.toNat = s.contents handle ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      ∀ d n : I, d.val = delta.val → n.val = len →
        Follows s (growbegInternalPlan l g delta.val.toNat) (internal d n) (fun _ next =>
          (∀ w slots, next.arrays[handle]? = some w → next.memories[w.reference.1]? = some slots →
            w.size = n ∧ 1 ≤ w.reference.2.val ∧
            w.reference.2.val - 1 + d.val + n.val ≤ (slots.length : Int) ∧
            (slots.drop (w.reference.2.val - 1 + d.val).toNat).take n.val.toNat =
              s.contents handle) ∧
          ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?))
end JuliaLean.Proofs.base.array.round10
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
section
variable {α : Type}

theorem growbegInternal_inplace0 {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val) (hedge : off.val + n.val ≤ 9223372036854775807)
    (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1))
    (hi1 : n.val + delta.val < slots.length)
    (hi2 : ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val)) :
    ∃ (newoff : I) (slots' : List (Option α)),
      (growbegInternal (mutableStorage layout) handle delta n).run s =
        (.ok (), { s with
          memories := s.memories.set mem slots'
          arrays := s.arrays.set handle ⟨(mem, newoff), n⟩ }) ∧
      newoff.val = (slots.length - (n.val + delta.val)) / 2 + 1 ∧ slots'.length = slots.length ∧
      (slots'.drop (newoff.val - 1 + delta.val).toNat).take n.val.toNat = vwWindow slots off n := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  obtain ⟨hnd, hadd1, hmul, hadd2, hadd3, hn2d1⟩ := growbegInternal_facts0 (layout := layout) h' delta hd hov
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := layout) s n hn0
  have hml := mutableMemLength_run (layout := layout) s mem slots hm
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  -- name every computed Int so later steps never see nested wraps
  generalize JInt.wrap .i64 (slots.length : Int) = WL at hml hL hc2 hc3
  generalize n + delta = NL at hnd hadd1
  generalize JInt.wrap .i64 2 * delta = D2 at hmul hadd2 hadd3 hn2d1
  generalize n + D2 = A2 at hadd2 hadd3 hn2d1
  generalize A2 + one = A3 at hadd3 hn2d1
  have hKv : (max c A3).val = (K : Int) := by
    rw [imax_val, hcv, hn2d1, hK]; omega
  have hKlo : n.val + 2 * delta.val + 1 ≤ (K : Int) := by rw [← hKv, imax_val, hn2d1]; omega
  clear hcv hK
  have hMb := ival_bounds (max c A3)
  have hKsub : (max c A3 - NL).val = (K : Int) - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hKv, hnd]; omega), hKv, hnd]
  generalize hQ0 : ((K : Int) - (n.val + delta.val)) / 2 = Q0 at hi2
  have hQ0b : 0 ≤ Q0 := by omega
  obtain ⟨Q, hdivA, hQ⟩ : ∃ Q : I, ((mutableStorage layout).divide (max c A3 - NL)
      (JInt.wrap .i64 2)).run s = (.ok Q, s) ∧ Q.val = Q0 :=
    ⟨_, ms_divide_run (layout := layout) s _ _ (by rw [wval2']; decide),
      by rw [wval2', tdiv_nonneg_val _ 2 (by rw [hKsub]; omega) (by decide) (by decide), hKsub, hQ0]⟩
  clear hQ0 hKsub
  have hLsub : (WL - NL).val = slots.length - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hL, hnd]; omega), hL, hnd]
  have hbr : (decide (NL < WL) && decide (Q + one < WL - NL)) = true := by
    have h1 : NL < WL := by rw [jlt_iff, hnd, hL]; exact hi1
    have h2 : Q + one < WL - NL := by
      rw [jlt_iff, hLsub, ival_add_one Q (by rw [hQ]; omega), hQ]; exact hi2
    simp only [h1, h2, decide_true, Bool.and_self]
  generalize hQ1 : ((slots.length : Int) - (n.val + delta.val)) / 2 = Q1
  have hQ1b : 2 * Q1 ≤ slots.length - (n.val + delta.val) ∧ 0 ≤ Q1 := by omega
  obtain ⟨Q', hdivB, hQ'⟩ : ∃ Q' : I, ((mutableStorage layout).divide (WL - NL)
      (JInt.wrap .i64 2)).run s = (.ok Q', s) ∧ Q'.val = Q1 :=
    ⟨_, ms_divide_run (layout := layout) s _ _ (by rw [wval2']; decide),
      by rw [wval2', tdiv_nonneg_val _ 2 (by rw [hLsub]; omega) (by decide) (by decide), hLsub, hQ1]⟩
  clear hQ1
  simp only [growbegInternal, ms_ref, ms_memory, ms_offset, ms_memoryref, ms_copyMemory,
    ms_unsetMemory, stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ ha, hml, hadd1,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    hcrun, hmul, hadd2, hadd3, hdivA, hbr, ite_true, hdivB]
  have hno : (Q' + one).val = Q1 + 1 := by rw [ival_add_one Q' (by rw [hQ']; omega), hQ']
  generalize Q' + one = newoff at hno ⊢
  clear hbr hdivA hdivB hi2 hQ0b hcrun hmul hadd2 hadd3 hn2d1 hQ hQ' hLsub hKv hMb
  have hdo : (newoff + delta).val = Q1 + 1 + delta.val := by
    rw [ival_add _ _ (by rw [hno]; omega), hno]
  have hmove := vwMemoryMove_run s mem mem (newoff + delta) off n slots slots hm hm hn0
    (by rw [hdo]; omega) (by rw [hdo]; omega) ho he hc
  simp only [hmove]
  generalize hS1 : slots.take ((newoff + delta).val - 1).toNat ++
      (slots.drop (off.val - 1).toNat).take n.val.toNat ++
      slots.drop ((newoff + delta).val - 1 + n.val).toNat = S1
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have hS1len : S1.length = slots.length := by
    rw [← hS1]
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [hdo]
    omega
  have hon : (off + n).val = off.val + n.val := ival_add _ _ (by omega)
  have hm1 : (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one).val = min (Q1 + 1 + delta.val) (off.val + n.val) - 1 := by
    rw [ival_sub_one _ (by rw [imin_val_native, hdo, hon]; omega),
      imin_val_native, hdo, hon]
  have hjs : ∀ j ∈ intRange off (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one),
      1 ≤ j.val ∧ j.val ≤ (S1.length : Int) := by
    intro j hj
    have hr := intRange_mem _ _ j hj
    rw [hm1] at hr
    rw [hS1len]
    omega
  rw [vwClearLoop_run mem _ _ S1 (List.getElem?_set_self hlt) ?hjs]
  case hjs => exact hjs
  simp only [List.set_set]
  generalize hS2 : vwClear (unsetRuntime := layout.runtime) S1 (intRange off (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one)) = S2
  have href2 : (mutableRef handle).run { s with memories := s.memories.set mem S2 } =
      (.ok (mem, off), { s with memories := s.memories.set mem S2 }) :=
    mutableRef_run { s with memories := s.memories.set mem S2 } handle _ ha
  have hset := ms_setRef_run (layout := layout)
    { s with memories := s.memories.set mem S2 } handle ⟨(mem, off), n⟩ ha (mem, newoff)
  simp only [href2, sameRef_self, Bool.not_true, Bool.false_eq_true, ite_false, stateExcept_bind,
    stateExcept_pure, hset]
  refine ⟨newoff, S2, rfl, hno, by rw [← hS2, vwClear_length, hS1len], ?_⟩
  have hk : ∀ j ∈ intRange off (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one),
      (j.val - 1).toNat < (newoff.val - 1 + delta.val).toNat := by
    intro j hj
    have hr := intRange_mem _ _ j hj
    rw [hm1] at hr
    omega
  have hdrop := vwClear_drop (unsetRuntime := layout.runtime) S1 _ _ hk
  have hA : (slots.take ((newoff + delta).val - 1).toNat).length = (newoff.val - 1 + delta.val).toNat := by
    rw [List.length_take, hdo, hno]; omega
  have hW : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  rw [← hS2, hdrop, ← hS1, take_three hA hW]
  rfl

theorem growbegInternal_alloc0 (l : DictLayout) {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val)
    (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1))
    (hns : ¬ (n.val + delta.val < slots.length ∧
      ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val))) :
    (¬ memoryFits l K → (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
      (.error (.argument genericMemorySizeMessage), s)) ∧
    (memoryFits l K → ∃ (newoff : I) (D : List (Option α)),
      (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
        (.ok (), { s with
          memories := (s.memories ++ [List.replicate K none]).set s.memories.length D
          arrays := s.arrays.set handle ⟨(s.memories.length, newoff), n⟩ }) ∧
      newoff.val = ((K : Int) - (n.val + delta.val)) / 2 + 1 ∧ D.length = K ∧
      (D.drop (newoff.val - 1 + delta.val).toNat).take n.val.toNat = vwWindow slots off n) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  obtain ⟨hnd, hadd1, hmul, hadd2, hadd3, hn2d1⟩ := growbegInternal_facts0 (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hov
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := MemoryLayoutMetadata.ofRuntime l) s n hn0
  have hml := mutableMemLength_run (layout := MemoryLayoutMetadata.ofRuntime l) s mem slots hm
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  generalize JInt.wrap .i64 (slots.length : Int) = WL at hml hL hc2 hc3
  generalize n + delta = NL at hnd hadd1
  generalize JInt.wrap .i64 2 * delta = D2 at hmul hadd2 hadd3 hn2d1
  generalize n + D2 = A2 at hadd2 hadd3 hn2d1
  generalize A2 + one = A3 at hadd3 hn2d1
  have hKv : (max c A3).val = (K : Int) := by
    rw [imax_val, hcv, hn2d1, hK]; omega
  have hKlo : n.val + 2 * delta.val + 1 ≤ (K : Int) := by rw [← hKv, imax_val, hn2d1]; omega
  clear hcv hK
  have hMb := ival_bounds (max c A3)
  have hKsub : (max c A3 - NL).val = (K : Int) - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hKv, hnd]; omega), hKv, hnd]
  generalize hQ0 : ((K : Int) - (n.val + delta.val)) / 2 = Q0 at hns ⊢
  have hQ0b : 2 * Q0 ≤ (K : Int) - (n.val + delta.val) ∧ 0 ≤ Q0 := by omega
  obtain ⟨Q, hdivA, hQ⟩ : ∃ Q : I, ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).divide (max c A3 - NL)
      (JInt.wrap .i64 2)).run s = (.ok Q, s) ∧ Q.val = Q0 :=
    ⟨_, ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s _ _ (by rw [wval2']; decide),
      by rw [wval2', tdiv_nonneg_val _ 2 (by rw [hKsub]; omega) (by decide) (by decide), hKsub, hQ0]⟩
  clear hQ0 hKsub
  have hLsub : (WL - NL).val = slots.length - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hL, hnd]; omega), hL, hnd]
  have hbr : (decide (NL < WL) && decide (Q + one < WL - NL)) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases hs1 : n.val + delta.val < slots.length
    · right
      rw [decide_eq_false_iff_not, jlt_iff, hLsub, ival_add_one Q (by rw [hQ]; omega), hQ]
      exact fun h2 => hns ⟨hs1, h2⟩
    · left
      rw [decide_eq_false_iff_not, jlt_iff, hnd, hL]
      exact hs1
  have hA := arrayNewMemorySpec α l s mem (max c A3)
  simp only at hA
  have hK0 : 0 ≤ (max c A3).val := by rw [hKv]; omega
  have hKn : (max c A3).val.toNat = K := by rw [hKv]; omega
  rw [hKn] at hA
  simp only [growbegInternal, ms_ref, ms_memory, ms_offset, ms_memoryref, ms_copyMemory,
    stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ ha, hml, hadd1,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    hcrun, hmul, hadd2, hadd3, hdivA, hbr]
  have hno : (Q + one).val = Q0 + 1 := by rw [ival_add_one Q (by rw [hQ]; omega), hQ]
  generalize Q + one = newoff at hno ⊢
  clear hbr hdivA hns hcrun hmul hadd2 hadd3 hn2d1 hQ hLsub
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  refine ⟨fun hnf => ?_, fun hfit => ?_⟩
  · have hE : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c A3)).run s =
        (.error (.argument genericMemorySizeMessage), s) := hA.2.1 hK0 hnf
    simp only [hE]
  · have hOk : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c A3)).run s =
        (.ok s.memories.length, { s with memories := s.memories ++ [List.replicate K none] }) :=
      hA.2.2 hK0 hfit
    have hk63 : K < 2 ^ 63 := by have := hfit.1; unfold maxIntVal at this; omega
    have hdM : ({ s with memories := s.memories ++ [List.replicate K none] } : MutableMemory α).memories[s.memories.length]? =
        some (List.replicate K none) := by simp
    have hsM : ({ s with memories := s.memories ++ [List.replicate K none] } : MutableMemory α).memories[mem]? =
        some slots := by
      show (s.memories ++ [List.replicate K none])[mem]? = some slots
      rw [List.getElem?_append_left hlt]; exact hm
    have hdo : (newoff + delta).val = Q0 + 1 + delta.val := by
      rw [ival_add _ _ (by rw [hno]; omega), hno]
    have hmove := vwMemoryMove_run { s with memories := s.memories ++ [List.replicate K none] }
      s.memories.length mem (newoff + delta) off n (List.replicate K none) slots hdM hsM hn0
      (by rw [hdo]; omega) (by rw [List.length_replicate, hdo]; omega) ho he
      (by rw [List.length_replicate]; exact hk63)
    simp only [hOk, hmove]
    generalize hD : (List.replicate K none).take ((newoff + delta).val - 1).toNat ++
        (slots.drop (off.val - 1).toNat).take n.val.toNat ++
        (List.replicate K none).drop ((newoff + delta).val - 1 + n.val).toNat = D
    have href2 : (mutableRef handle).run
        { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D } =
        (.ok (mem, off), { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D }) :=
      mutableRef_run { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D }
        handle _ ha
    have hset := ms_setRef_run (layout := MemoryLayoutMetadata.ofRuntime l)
      { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D }
      handle ⟨(mem, off), n⟩ ha (s.memories.length, newoff)
    simp only [stateExcept_bind, href2, sameRef_self, Bool.not_true, Bool.false_eq_true,
      ite_false, stateExcept_pure, hset]
    have hA' : ((List.replicate K (none : Option α)).take ((newoff + delta).val - 1).toNat).length =
        (newoff.val - 1 + delta.val).toNat := by
      rw [List.length_take, List.length_replicate, hdo, hno]; omega
    have hW : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
      simp only [List.length_take, List.length_drop]; omega
    refine ⟨newoff, D, rfl, hno, ?_, ?_⟩
    · rw [← hD]
      simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
      rw [hdo]
      omega
    · rw [← hD, take_three hA' hW]
      rfl

theorem growbegInternal_overflow0 {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val) (hov1 : n.val + delta.val ≤ 9223372036854775807)
    (hov : 9223372036854775807 < n.val + 2 * delta.val + 1) :
    (growbegInternal (mutableStorage layout) handle delta n).run s = (.error .overflow, s) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have hadd1 := ms_checkedAdd_run (layout := layout) s n delta (by omega)
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := layout) s n hn0
  by_cases h2 : 2 * delta.val ≤ 9223372036854775807
  · have hmul := ms_checkedMul_run (layout := layout) s (JInt.wrap .i64 2) delta (by rw [wval2']; omega)
    have h2d : (JInt.wrap .i64 2 * delta).val = 2 * delta.val := by
      rw [show JInt.wrap .i64 2 * delta = JInt.wrap .i64 ((JInt.wrap .i64 2).val * delta.val) from rfl,
        wval2']
      exact ival_wrap _ (by omega)
    by_cases h3 : n.val + 2 * delta.val ≤ 9223372036854775807
    · have hadd2 := ms_checkedAdd_run (layout := layout) s n (JInt.wrap .i64 2 * delta)
        (by rw [h2d]; omega)
      have hn2d : (n + JInt.wrap .i64 2 * delta).val = n.val + 2 * delta.val := by
        rw [ival_add _ _ (by rw [h2d]; omega), h2d]
      have hadd3 := ms_checkedAdd_overflow (layout := layout) s (n + JInt.wrap .i64 2 * delta) one
        (by rw [hn2d, ival_one]; omega)
      simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
        mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1,
        gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
        hcrun, hmul, hadd2, hadd3]
    · have hadd2 := ms_checkedAdd_overflow (layout := layout) s n (JInt.wrap .i64 2 * delta)
        (by rw [h2d]; omega)
      simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
        mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1,
        gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
        hcrun, hmul, hadd2]
  · have hmul := ms_checkedMul_overflow (layout := layout) s (JInt.wrap .i64 2) delta
      (by rw [wval2']; omega)
    simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
      mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1,
      gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      hcrun, hmul]

theorem growbeg_toInt_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf Error m]
    {A Mem R Z : Type} (st : Storage m A Mem R) (toInt : Z → m I) (internal : A → I → I → m Unit)
    (a : A) (d : Z) :
    growbeg st toInt internal a d = toInt d >>= growbeg st pure internal a := by
  unfold growbeg
  simp only [pure_bind]

theorem growbeg_neg_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat)
    (x : I) (hx : x.val < 0) :
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle x).run s =
      (.error (.argument "grow requires delta >= 0"), s) := by
  have hz : ¬ x.val = 0 := by omega
  have hn : ¬ (x ≥ zero) := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  simp only [growbeg, stateExcept_bind, stateExcept_pure, hz, ite_false, hn, decide_false,
    Bool.not_false, ite_true, stateExcept_throw]

/-- `_growbeg_internal!` when `len + delta` is not an `Int`: `OverflowError`, store unchanged. -/
theorem growbegInternal_overflowAdd {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hov1 : 9223372036854775807 < n.val + delta.val) :
    (growbegInternal (mutableStorage layout) handle delta n).run s = (.error .overflow, s) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hadd1 := ms_checkedAdd_overflow (layout := layout) s n delta (by omega)
  simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
    mutableRef_run s handle _ ha, hadd1]

/-- `_growbeg_internal!(a, d, len)` on a valid vector, called with its length, follows
`growbegInternalPlan`: the data lands `d` slots after the new offset, in a memory long enough. -/
theorem growbegInternal_follows (l : DictLayout) {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (d : I)
    (hd : 0 ≤ d.val) (hedge : off.val + n.val ≤ 9223372036854775807) :
    Follows s (growbegInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat)
      ((growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s) (fun _ next =>
        (∀ w sl, next.arrays[handle]? = some w → next.memories[w.reference.1]? = some sl →
          w.size = n ∧ 1 ≤ w.reference.2.val ∧
          w.reference.2.val - 1 + d.val + n.val ≤ (sl.length : Int) ∧
          (sl.drop (w.reference.2.val - 1 + d.val).toNat).take n.val.toNat = vwWindow slots off n) ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds d
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hother : ∀ (v : MutableVector) h2, h2 ≠ handle → (s.arrays.set handle v)[h2]? = s.arrays[h2]? :=
    fun _ _ hne => List.getElem?_set_ne (fun he => hne he.symm)
  by_cases hov : n.val + 2 * d.val + 1 ≤ 9223372036854775807
  · have hovN : ¬ (typemaxNat < n.val.toNat + 2 * d.val.toNat + 1) := by unfold typemaxNat; omega
    obtain ⟨K, hK⟩ : ∃ K, K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * d.val.toNat + 1) :=
      ⟨_, rfl⟩
    have hKlo : n.val.toNat + 2 * d.val.toNat + 1 ≤ K := by rw [hK]; exact Nat.le_max_right _ _
    by_cases hs : n.val + d.val < slots.length ∧
        ((K : Int) - (n.val + d.val)) / 2 + 1 < slots.length - (n.val + d.val)
    · obtain ⟨newoff, slots', hint, hnewoff, hlen, hwin'⟩ :=
        growbegInternal_inplace0 (layout := MemoryLayoutMetadata.ofRuntime l) h' d hd hedge hov K hK hs.1 hs.2
      have hsN : n.val.toNat + d.val.toNat < slots.length ∧
          (max (overallocationNat n.val.toNat) (n.val.toNat + 2 * d.val.toNat + 1) -
            (n.val.toNat + d.val.toNat)) / 2 + 1 < slots.length - (n.val.toNat + d.val.toNat) := by
        rw [← hK]; omega
      have hplan : growbegInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
          .ok ⟨slots.length, (slots.length - (n.val.toNat + d.val.toNat)) / 2 + 1, n.val.toNat⟩ := by
        simp only [growbegInternalPlan, hovN, hsN, ite_false, ite_true, and_self]
      refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' hg' => ?_⟩
      refine ⟨(), _, hint, ?_, hother _⟩
      intro w sl hw hsl
      rw [List.getElem?_set_self halt] at hw
      cases hw
      rw [List.getElem?_set_self hlt] at hsl
      cases hsl
      refine ⟨rfl, by simp only; omega, by simp only; rw [hlen, hnewoff]; omega, ?_⟩
      exact hwin'
    · obtain ⟨hnf, hok⟩ := growbegInternal_alloc0 l h' d hd hov K hK hs
      have hsN : ¬ (n.val.toNat + d.val.toNat < slots.length ∧
          (max (overallocationNat n.val.toNat) (n.val.toNat + 2 * d.val.toNat + 1) -
            (n.val.toNat + d.val.toNat)) / 2 + 1 < slots.length - (n.val.toNat + d.val.toNat)) := by
        rw [← hK]; omega
      have hplan : growbegInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
          allocationPlan l K ⟨K, (K - (n.val.toNat + d.val.toNat)) / 2 + 1, n.val.toNat⟩ := by
        simp only [growbegInternalPlan, hovN, hsN, ite_false]
        rw [← hK]
      by_cases hfit : memoryFits l K
      · obtain ⟨newoff, D, hint, hnewoff, hDlen, hDwin⟩ := hok hfit
        have hMlt : s.memories.length < (s.memories ++ [List.replicate K none]).length := by simp
        have hplan' : growbegInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
            .ok ⟨K, (K - (n.val.toNat + d.val.toNat)) / 2 + 1, n.val.toNat⟩ := by
          rw [hplan]; simp only [allocationPlan, hfit, ite_true]
        refine ⟨fun e he => (by rw [hplan'] at he; cases he), fun g' _ => ?_⟩
        refine ⟨(), _, hint, ?_, hother _⟩
        intro w sl hw hsl
        rw [List.getElem?_set_self halt] at hw
        cases hw
        rw [List.getElem?_set_self hMlt] at hsl
        cases hsl
        refine ⟨rfl, by simp only; omega, by simp only; rw [hDlen, hnewoff]; omega, ?_⟩
        exact hDwin
      · refine ⟨fun e he => ?_, fun g' hg' => by
          rw [hplan] at hg'; simp only [allocationPlan, hfit, ite_false] at hg'; cases hg'⟩
        rw [hplan] at he
        simp only [allocationPlan, hfit, ite_false] at he
        cases he
        exact hnf hfit
  · have hplan : growbegInternalPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ d.val.toNat =
        .error .overflow := by
      have hovN : typemaxNat < n.val.toNat + 2 * d.val.toNat + 1 := by unfold typemaxNat; omega
      simp only [growbegInternalPlan, hovN, ite_true]
    have hrun : (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle d n).run s = (.error .overflow, s) := by
      by_cases hov1 : n.val + d.val ≤ 9223372036854775807
      · exact growbegInternal_overflow0 h' d hd hov1 (by omega)
      · exact growbegInternal_overflowAdd h' d (by omega)
    refine ⟨fun e he => ?_, fun g' hg' => by rw [hplan] at hg'; cases hg'⟩
    rw [hplan] at he
    cases he
    exact hrun

theorem growbegSpec : JuliaLean.Proofs.base.array.round10.GrowbegSpec := by
  intro α l ops hops s handle delta hvalid hmem
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hedge : off.val + n.val ≤ 9223372036854775807 := by
    have hm := hmem _ slots h.1 h.2.1
    have hb := h.2.2.2.2.1
    simp only [maxIntVal] at hm
    omega
  have hn0 := h.2.2.2.1
  have hlen := vwWindow_length h
  dsimp only
  rw [VecAt.geometry h, h.contents, growbeg_toInt_eq, stateExcept_bind, integerToInt_run,
    integerValue_toInt hops]
  refine ⟨fun hf => by rw [if_neg (show ¬ (IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max) from hf)], fun hf hneg => ?_, fun hf hpos => ⟨?_, ?_⟩⟩
  · rw [if_pos (show IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max from hf)]
    exact growbeg_neg_run s handle _ (by rw [ival_wrap _ (show -9223372036854775808 ≤ delta.val ∧ delta.val ≤ 9223372036854775807 from hf)]; exact hneg)
  · rw [if_pos (show IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max from hf)]
    have hx : (JInt.wrap .i64 delta.val).val = delta.val := ival_wrap _ (show -9223372036854775808 ≤ delta.val ∧ delta.val ≤ 9223372036854775807 from hf)
    obtain ⟨herr, hok⟩ := growbeg_plan l h (JInt.wrap .i64 delta.val) (by rw [hx]; exact hpos)
    rw [hx] at herr hok
    refine ⟨herr, fun g' hg' => ?_⟩
    obtain ⟨next, mem', off', slots', hrun, hv, harr, hnd, hwin, -⟩ := hok g' hg'
    refine ⟨(), next, hrun, hv.valid, ?_, ?_, ?_⟩
    · rw [hv.contents, vwWindow_length hv, hnd, hlen]
      omega
    · rw [hv.contents]
      exact hwin
    · intro h2 hne
      rw [harr]
      exact List.getElem?_set_ne (fun he => hne he.symm)
  · intro d n' hd hn'
    have hnn : n' = n := Subtype.ext (by rw [hn', hlen]; omega)
    subst hnn
    rw [← hd]
    exact growbegInternal_follows l h d (by rw [hd]; exact hpos) hedge
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

/-- A deleted position: the read cursor `q` moves on, nothing is written. -/
theorem maskInv_skip (handle mem : Nat) (off n : I) (w0 : List (Option α)) (mask : List Bool)
    (k : Nat) (pq : I × I) (st : MutableMemory α) (v : Option α)
    (hw : w0[k]? = some v) (hm : mask[k]? = some true) (hk : (k : Int) + 2 ≤ 9223372036854775807)
    (h : MaskInv handle mem off n w0 mask k pq st) :
    MaskInv handle mem off n w0 mask (k + 1) (pq.1, pq.2 + one) st := by
  obtain ⟨sl, hv, hq, hp, htake, hdrop⟩ := h
  have hsucc := keptPrefix_succ w0 mask k v true hw hm
  simp only [ite_true, List.append_nil] at hsucc
  refine ⟨sl, hv, ?_, ?_, ?_, ?_⟩
  · show (pq.2 + one).val = _
    have := ival_add_one pq.2 (by omega)
    push_cast; omega
  · rw [hsucc]; exact hp
  · rw [hsucc]; exact htake
  · exact drop_succ_of_drop_eq _ _ k hdrop
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
namespace solArray
section
open JuliaLean JuliaLean.base.array
open _root_.JuliaLean.Proofs.base.array.JuliaLean.Proofs.base.array
set_option maxHeartbeats 1000000
attribute [local irreducible] JInt.wrap wrapInt

local instance (d : round4.IntegerValue) : Decidable d.fits := by
  unfold round4.IntegerValue.fits
  infer_instance

private def clearedSlots (slots : List (Option α)) (off : I) (js : List I) : List (Option α) :=
  js.foldl (fun sl j => sl.set (off.val - 1 + j.val - 1).toNat none) slots

private theorem clearedSlots_get_hit (slots : List (Option α)) (off : I) (js : List I) (k : Nat)
    (hk : k < slots.length) :
    (clearedSlots slots off js)[k]? =
      if ∃ j ∈ js, k = (off.val - 1 + j.val - 1).toNat then some none else slots[k]? := by
  induction js generalizing slots with
  | nil => simp only [clearedSlots, List.foldl_nil, List.not_mem_nil, false_and, exists_false, ite_false]
  | cons j js ih =>
    simp only [clearedSlots, List.foldl_cons] at ⊢
    change (clearedSlots (slots.set (off.val - 1 + j.val - 1).toNat none) off js)[k]? = _
    rw [ih _ (by simpa using hk)]
    by_cases hr : ∃ q ∈ js, k = (off.val - 1 + q.val - 1).toNat
    · simp only [hr, ite_true]
      rw [if_pos (by obtain ⟨q,hq,he⟩ := hr; exact ⟨q,List.mem_cons_of_mem _ hq,he⟩)]
    · rw [if_neg hr]
      by_cases hj : k = (off.val - 1 + j.val - 1).toNat
      · rw [if_pos ⟨j, List.mem_cons_self, hj⟩]
        rw [← hj, List.getElem?_set_self hk]
      · rw [List.getElem?_set_ne (Ne.symm hj)]
        rw [if_neg (by
          rintro ⟨q, hq, he⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hj he
          · exact hr ⟨q, hq, he⟩)]

private theorem set_raw_self (slots : List (Option α)) (i : Nat) :
    slots.set i (slots[i]?).join = slots := by
  apply List.ext_getElem?
  intro j
  by_cases hji : j = i
  · subst j
    by_cases hi : i < slots.length
    · rw [List.getElem?_set_self hi, List.getElem?_eq_getElem hi]
      rfl
    · rw [List.getElem?_eq_none (by simpa only [List.length_set] using (Nat.le_of_not_lt hi)),
        List.getElem?_eq_none (by omega)]
  · exact List.getElem?_set_ne (Ne.symm hji)

private theorem vwUnset_layout {unsetRuntime : DictLayout} (slots : List (Option α))
    (off : I) (js : List I) :
    vwUnset (unsetRuntime := unsetRuntime) slots off js =
      if unsetClears unsetRuntime then clearedSlots slots off js else slots := by
  cases hc : unsetClears unsetRuntime with
  | false =>
    simp only [hc, Bool.false_eq_true, ite_false]
    induction js generalizing slots with
    | nil => rfl
    | cons j js ih =>
      simpa only [vwUnset, List.foldl_cons, expectedUnset, hc,
        Bool.false_eq_true, ite_false, set_raw_self] using ih slots
  | true =>
    simp only [hc, ite_true]
    induction js generalizing slots with
    | nil => rfl
    | cons j js ih =>
      simpa only [vwUnset, clearedSlots, List.foldl_cons, expectedUnset, hc, ite_true] using
        ih (slots.set (off.val - 1 + j.val - 1).toNat none)

 theorem vwUnset_get_hit {unsetRuntime : DictLayout} (slots : List (Option α)) (off : I) (js : List I) (k : Nat)
    (hk : k < slots.length) :
    (vwUnset (unsetRuntime := unsetRuntime) slots off js)[k]? =
      if ∃ j ∈ js, k = (off.val - 1 + j.val - 1).toNat then some (expectedUnset unsetRuntime (slots[k]?).join) else slots[k]? := by
  rw [vwUnset_layout]
  cases hc : unsetClears unsetRuntime with
  | false =>
    simp [hc, expectedUnset, List.getElem?_eq_getElem hk]
  | true =>
    simpa only [hc, ite_true, expectedUnset] using clearedSlots_get_hit slots off js k hk

 theorem intRange_mem_iff (lo hi j : I) : j ∈ intRange lo hi ↔ lo.val ≤ j.val ∧ j.val ≤ hi.val := by
  constructor
  · exact intRange_mem lo hi j
  · intro h
    refine List.mem_map.mpr ⟨(j.val-lo.val).toNat, List.mem_range.mpr (by omega), ?_⟩
    apply Subtype.ext
    rw [ival_wrap _ (by have := ival_bounds j; omega)]
    omega

theorem vwUnset_range {unsetRuntime : DictLayout} (slots : List (Option α)) (off lo hi : I)
    (ho : 1 ≤ off.val) (hl : 1 ≤ lo.val) (hh : lo.val ≤ hi.val + 1) :
    vwUnset (unsetRuntime := unsetRuntime) slots off (intRange lo hi) =
      round9.clearSpan (unsetRuntime := unsetRuntime) slots (off.val - 1 + lo.val - 1).toNat (hi.val - lo.val + 1).toNat := by
  have hit (k : Nat) : (∃ j ∈ intRange lo hi, k = (off.val - 1 + j.val - 1).toNat) ↔
      (off.val - 1 + lo.val - 1).toNat ≤ k ∧
        k < (off.val - 1 + lo.val - 1).toNat + (hi.val - lo.val + 1).toNat := by
    constructor
    · rintro ⟨j, hj, hk⟩
      have hj' := intRange_mem lo hi j hj
      omega
    · intro hk
      have hjbounds : lo.val ≤ (k : Int) - off.val + 2 ∧ (k : Int) - off.val + 2 ≤ hi.val := by omega
      have hjv : (JInt.wrap .i64 ((k : Int) - off.val + 2)).val = (k : Int) - off.val + 2 :=
        ival_wrap _ (by have := ival_bounds lo; have := ival_bounds hi; omega)
      exact ⟨_, (intRange_mem_iff ..).mpr (by rw [hjv]; exact hjbounds), by rw [hjv]; omega⟩
  apply List.ext_getElem?
  intro k
  by_cases hk : k < slots.length
  · rw [vwUnset_get_hit slots off _ k hk]
    simp only [round9.clearSpan, List.getElem?_mapIdx]
    simp only [hit k, List.getElem?_eq_getElem hk, Option.map_some]
    split <;> rfl
  · have hu : (vwUnset (unsetRuntime := unsetRuntime) slots off (intRange lo hi)).length = slots.length := vwUnset_length (unsetRuntime := unsetRuntime) ..
    have hc : (round9.clearSpan (unsetRuntime := unsetRuntime) slots (off.val - 1 + lo.val - 1).toNat
      (hi.val - lo.val + 1).toNat).length = slots.length := by simp [round9.clearSpan]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem deleteend_physical {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {a mem : Nat} {off n : I} {slots : List (Option α)}
    (h : VecAt s a mem off n slots) (d : I) (hd : 0 ≤ d.val) (hdn : d.val ≤ n.val)
    (hmax : n.val < 9223372036854775807) :
    (deleteend (mutableStorage layout) pure a d).run s =
      (.ok (), round9.deletionState (unsetRuntime := layout.runtime) s a ⟨(mem,off),n⟩ slots d.val.toNat false) := by
  have hn0 := h.2.2.2.1
  have ho := h.2.2.1
  have hsub : (n - d).val = n.val - d.val := ival_sub _ _ (by have := ival_bounds n; omega)
  have hlo : (n - d + one).val = n.val - d.val + 1 := by
    rw [ival_add _ _ (by rw [hsub, ival_one]; have := ival_bounds n; omega), hsub, ival_one]
  have hsmall : ¬ (JInt.rem .u64 d > JInt.rem .u64 n) := by
    change ¬ ((JInt.rem .u64 n).val < (JInt.rem .u64 d).val)
    rw [urem_val n hn0, urem_val d hd]
    omega
  have hjs : ∀ j ∈ intRange (n-d+one) n, 1 ≤ j.val ∧ j.val ≤ n.val := by
    intro j hj
    have := intRange_mem _ _ j hj
    omega
  have hloop := vwUnsetLoop_run (unsetRuntime := layout.runtime) a mem off n (intRange (n-d+one) n) s slots h hjs
  have hlt := (List.getElem?_eq_some_iff.mp h.2.1).choose
  have hmidv : VecAt {s with
      memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n-d+one) n))}
      a mem off n (vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n-d+one) n)) :=
    ⟨h.1,List.getElem?_set_self hlt,h.2.2.1,hn0,
      by rw [vwUnset_length]; exact h.2.2.2.2.1,
      by rw [vwUnset_length]; exact h.2.2.2.2.2⟩
  have hsize := vwSetSize_run (layout := layout) _ a mem off n _ hmidv (n-d)
  have hclear : vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n-d+one) n) =
      round9.clearSpan (unsetRuntime := layout.runtime) slots ((off.val-1).toNat + (n.val.toNat-d.val.toNat)) d.val.toNat := by
    rw [vwUnset_range slots off _ n h.2.2.1 (by rw [hlo]; omega) (by rw [hlo]; omega)]
    congr 1 <;> rw [hlo] <;> omega
  have hsizeEq : n-d = JInt.wrap .i64 ((n.val.toNat-d.val.toNat : Nat) : Int) := by
    apply Subtype.ext
    rw [hsub, ival_wrap _ (by have := ival_bounds n; omega)]
    omega
  simp only [deleteend, ms_length, ms_unsetArray, stateExcept_bind, stateExcept_pure,
    mutableLength_run s a _ h.1, hsmall, ite_false, hloop, hsize]
  rw [hclear, hsizeEq]
  rfl

theorem deletebeg_physical {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {a mem : Nat} {off n : I} {slots : List (Option α)}
    (h : VecAt s a mem off n slots) (d : I) (hd : 0 ≤ d.val) (hdn : d.val ≤ n.val)
    (hmax : slots.length < 9223372036854775807) :
    (deletebeg (mutableStorage layout) pure a d).run s =
      (.ok (), round9.deletionState (unsetRuntime := layout.runtime) s a ⟨(mem,off),n⟩ slots d.val.toNat true) := by
  have hn0 := h.2.2.2.1
  have hsub : (n - d).val = n.val - d.val := ival_sub _ _ (by have := ival_bounds n; omega)
  have hsmall : ¬ (JInt.rem .u64 d > JInt.rem .u64 n) := by
    change ¬ ((JInt.rem .u64 n).val < (JInt.rem .u64 d).val)
    rw [urem_val n hn0, urem_val d hd]
    omega
  have hjs : ∀ j ∈ intRange one d, 1 ≤ j.val ∧ j.val ≤ n.val := by
    intro j hj
    have := intRange_mem one d j hj
    simp only [ival_one] at this
    omega
  have hloop := vwUnsetLoop_run (unsetRuntime := layout.runtime) a mem off n (intRange one d) s slots h hjs
  have hlt := (List.getElem?_eq_some_iff.mp h.2.1).choose
  have halt := (List.getElem?_eq_some_iff.mp h.1).choose
  have hmidv : VecAt {s with memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d))}
      a mem off n (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d)) :=
    ⟨h.1,List.getElem?_set_self hlt,h.2.2.1,hn0,
      by rw [vwUnset_length]; exact h.2.2.2.2.1,
      by rw [vwUnset_length]; exact h.2.2.2.2.2⟩
  have hsize := vwSetSize_run (layout := layout) _ a mem off n _ hmidv (n-d)
  have hmid2 : VecAt {s with
      memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d))
      arrays := s.arrays.set a ⟨(mem,off),n-d⟩}
      a mem off (n-d) (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d)) :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hlt,h.2.2.1,by omega,
      by rw [vwUnset_length,hsub]; have := h.2.2.2.2.1; omega,
      by rw [vwUnset_length]; exact h.2.2.2.2.2⟩
  have hclear : vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d) =
      round9.clearSpan (unsetRuntime := layout.runtime) slots (off.val-1).toNat d.val.toNat := by
    simpa [ival_one] using vwUnset_range (unsetRuntime := layout.runtime) slots off one d h.2.2.1 (by rw [ival_one]; omega)
      (by rw [ival_one]; omega)
  have hsizeEq : n-d = JInt.wrap .i64 ((n.val.toNat-d.val.toNat : Nat) : Int) := by
    apply Subtype.ext
    rw [hsub, ival_wrap _ (by have := ival_bounds n; omega)]
    omega
  by_cases hz : n.val-d.val = 0
  · have hne : ((n-d).val != 0) = false := by rw [hsub,hz]; rfl
    have hcount : n.val.toNat-d.val.toNat = 0 := by omega
    simp only [deletebeg, ms_length, ms_unsetArray, stateExcept_bind, stateExcept_pure,
      mutableLength_run s a _ h.1, hsmall, ite_false, hloop, hsize, hne, Bool.false_eq_true]
    rw [hclear,hsizeEq]
    simp [round9.deletionState,hcount]
  · have hne : ((n-d).val != 0) = true := by rw [hsub]; simpa using hz
    have hcount : n.val.toNat-d.val.toNat ≠ 0 := by omega
    have haddr : (off+(d+one)-one).val = off.val+d.val := by
      have h1 : (d+one).val = d.val+1 := ival_add_one d (by
        have := h.2.2.1; have := h.2.2.2.2.1; omega)
      rw [ival_add_sub_one off (d+one) (by rw [h1]; have := h.2.2.1; have := h.2.2.2.2.1; omega),h1]
      omega
    have hrefEq : off+(d+one)-one = JInt.wrap .i64 (off.val+d.val.toNat) := by
      apply Subtype.ext
      rw [haddr,ival_wrap _ (by have := h.2.2.1; have := h.2.2.2.2.1; omega)]
      omega
    have href := mutableRef_run _ a _ hmid2.1
    have hset := vwSetRef_run (layout := layout) _ a mem off (n-d) _ hmid2 (mem,off+(d+one)-one)
    simp only [deletebeg, ms_length, ms_unsetArray, ms_ref, ms_shiftref, stateExcept_bind,
      stateExcept_pure, mutableLength_run s a _ h.1, hsmall, ite_false, hloop, hsize, hne,
      ite_true,href,hset,List.set_set]
    rw [hclear,hsizeEq,hrefEq]
    simp [round9.deletionState,hcount]

theorem deletion_convert (ops : round4.BigIntegerOps) (hops : ops.Lawful) (d : round4.IntegerValue) :
    round9.convertInteger ops .i64 d =
      if d.fits then .ok (JInt.wrap .i64 d.val) else .error .inexact := by
  exact opusGrowth.convertInteger_i64 hops d

theorem deletebeg_integer_run {α : Type} (layout : MemoryLayoutMetadata)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α)
    (a : Nat) (d : round4.IntegerValue) :
    (deletebeg (mutableStorage layout) (round9.integerToInt ops) a d).run s =
      if d.fits then (deletebeg (mutableStorage layout) pure a (JInt.wrap .i64 d.val)).run s
      else (.error .inexact,s) := by
  have heq : deletebeg (mutableStorage (α := α) layout) (round9.integerToInt ops) a d =
      round9.integerToInt ops d >>= fun delta => deletebeg (mutableStorage layout) pure a delta := by
    simp only [deletebeg,pure_bind,bind_assoc]
  rw [heq,stateExcept_bind]
  rw [show (round9.integerToInt ops d : MutationM α I).run s =
    (round9.convertInteger ops .i64 d,s) from rfl]
  rw [deletion_convert ops hops d]
  by_cases hf : d.fits <;> simp only [hf,ite_true,ite_false]

theorem deleteend_integer_run {α : Type} (layout : MemoryLayoutMetadata)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α)
    (a : Nat) (d : round4.IntegerValue) :
    (deleteend (mutableStorage layout) (round9.integerToInt ops) a d).run s =
      if d.fits then (deleteend (mutableStorage layout) pure a (JInt.wrap .i64 d.val)).run s
      else (.error .inexact,s) := by
  have heq : deleteend (mutableStorage (α := α) layout) (round9.integerToInt ops) a d =
      round9.integerToInt ops d >>= fun delta => deleteend (mutableStorage layout) pure a delta := by
    simp only [deleteend,pure_bind,bind_assoc]
  rw [heq,stateExcept_bind]
  rw [show (round9.integerToInt ops d : MutationM α I).run s =
    (round9.convertInteger ops .i64 d,s) from rfl]
  rw [deletion_convert ops hops d]
  by_cases hf : d.fits <;> simp only [hf,ite_true,ite_false]

theorem deletebegSpec : round9.DeletebegSpec := by
  intro α layout ops hops s a d hvalid hsize
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  have hlen : (s.contents a).length = n.val.toNat := by rw [h.contents,vwWindow_length h]
  have hmax : slots.length < 9223372036854775807 := hsize _ _ h.1 h.2.1
  have hn0 := h.2.2.2.1
  dsimp only
  rw [deletebeg_integer_run layout ops hops s a d]
  refine ⟨fun hn => by rw [if_neg hn], ?_, ?_⟩
  · intro hf hd
    rw [if_pos hf]
    have hdv : (JInt.wrap .i64 d.val).val = d.val := ival_wrap _ hf
    refine ⟨.argument "_deletebeg! requires delta in 0:length(a)", ?_⟩
    exact vwDeletebeg_error s a mem off n slots h _ (by rw [hdv]; rw [hlen] at hd; omega)
  · intro hd hdn vector slots' ha hm
    have hf : d.fits := by
      have := ival_bounds n
      change IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max
      rw [hlen] at hdn
      change -9223372036854775808 ≤ d.val ∧ d.val ≤ 9223372036854775807
      omega
    rw [if_pos hf]
    have hdv : (JInt.wrap .i64 d.val).val = d.val := ival_wrap _ hf
    have hv : vector = ⟨(mem,off),n⟩ := Option.some.inj (ha.symm.trans h.1)
    subst vector
    have hs : slots' = slots := Option.some.inj (hm.symm.trans h.2.1)
    subst slots'
    have hdN : (JInt.wrap .i64 d.val).val.toNat = d.val.toNat := by rw [hdv]
    have hdn' : (JInt.wrap .i64 d.val).val ≤ n.val := by rw [hdv]; rw [hlen] at hdn; omega
    have hp := deletebeg_physical (layout := layout) h _ (by rw [hdv]; exact hd) hdn' hmax
    rw [hdN] at hp
    obtain ⟨next,off',sl',hr,hv',_,_,hw⟩ := vwDeletebeg_run (layout := layout) s a mem off n slots h _
      (by rw [hdv]; exact hd) hdn'
    rw [hp] at hr
    have heq := (Prod.mk.inj hr).2
    cases heq
    refine ⟨hp,hv'.valid,?_⟩
    rw [hv'.contents,hw,hdN,← h.contents]

theorem deleteendSpec : round9.DeleteendSpec := by
  intro α layout ops hops s a d hvalid hsize
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  have hlen : (s.contents a).length = n.val.toNat := by rw [h.contents,vwWindow_length h]
  have hmax : slots.length < 9223372036854775807 := hsize _ _ h.1 h.2.1
  have hn0 := h.2.2.2.1
  have hnmax : n.val < 9223372036854775807 := by
    have := h.2.2.1; have := h.2.2.2.2.1; omega
  dsimp only
  rw [deleteend_integer_run layout ops hops s a d]
  refine ⟨fun hn => by rw [if_neg hn], ?_, ?_⟩
  · intro hf hd
    rw [if_pos hf]
    have hdv : (JInt.wrap .i64 d.val).val = d.val := ival_wrap _ hf
    refine ⟨.argument "_deleteend! requires delta in 0:length(a)", ?_⟩
    exact vwDeleteend_error s a mem off n slots h _ (by rw [hdv]; rw [hlen] at hd; omega)
  · intro hd hdn vector slots' ha hm
    have hf : d.fits := by
      have := ival_bounds n
      change IntTy.i64.min ≤ d.val ∧ d.val ≤ IntTy.i64.max
      rw [hlen] at hdn
      change -9223372036854775808 ≤ d.val ∧ d.val ≤ 9223372036854775807
      omega
    rw [if_pos hf]
    have hdv : (JInt.wrap .i64 d.val).val = d.val := ival_wrap _ hf
    have hv : vector = ⟨(mem,off),n⟩ := Option.some.inj (ha.symm.trans h.1)
    subst vector
    have hs : slots' = slots := Option.some.inj (hm.symm.trans h.2.1)
    subst slots'
    have hdN : (JInt.wrap .i64 d.val).val.toNat = d.val.toNat := by rw [hdv]
    have hdn' : (JInt.wrap .i64 d.val).val ≤ n.val := by rw [hdv]; rw [hlen] at hdn; omega
    have hp := deleteend_physical (layout := layout) h _ (by rw [hdv]; exact hd) hdn' hnmax
    rw [hdN] at hp
    obtain ⟨next,sl',hr,hv',_,_,hw⟩ := vwDeleteend_run (layout := layout) s a mem off n slots h _
      (by rw [hdv]; exact hd) hdn' (by rw [hdv]; omega)
    rw [hp] at hr
    have heq := (Prod.mk.inj hr).2
    cases heq
    refine ⟨hp,hv'.valid,?_⟩
    rw [hv'.contents,hw,← h.contents,hlen]
    congr 1
    rw [hdv]
    omega
end
end solArray
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

/-- The deletion mask of the index list `inds` over the positions of `w`. -/
def indexMask {β : Type} (w : List β) (inds : List I) : List Bool :=
  w.zipIdx.map (fun p => inds.any (fun i => decide (i.val = (p.2 : Int) + 1)))

theorem indexMask_length {β : Type} (w : List β) (inds : List I) :
    (indexMask w inds).length = w.length := by
  simp [indexMask]

theorem indexMask_get {β : Type} (w : List β) (inds : List I) (j : Nat) (hj : j < w.length) :
    (indexMask w inds)[j]? = some (inds.any (fun i => decide (i.val = (j : Int) + 1))) := by
  simp [indexMask, List.getElem?_zipIdx, List.getElem?_eq_getElem hj]

theorem indexMask_keep {β : Type} (w : List β) (inds : List I) :
    ((w.zip (indexMask w inds)).filter (fun p => !p.2)).map Prod.fst =
      (w.zipIdx.filter (fun p => !(inds.any (fun i => decide (i.val = (p.2 : Int) + 1))))).map
        Prod.fst := by
  have hz : w.zip (indexMask w inds) =
      w.zipIdx.map (fun p => (p.1, inds.any (fun i => decide (i.val = (p.2 : Int) + 1)))) := by
    apply List.ext_getElem
    · simp [indexMask]
    · intro j h1 h2
      simp [List.getElem_zip, indexMask, List.getElem_zipIdx]
  rw [hz, List.filter_map, List.map_map]
  rfl

theorem keptPrefix_all_false {β : Type} (w : List β) (mask : List Bool) :
    ∀ k, k ≤ w.length → k ≤ mask.length → (∀ j, j < k → mask[j]? = some false) →
      keptPrefix w mask k = w.take k := by
  intro k
  induction k with
  | zero => intro _ _ _; simp [keptPrefix]
  | succ k ih =>
    intro hw hm hf
    have hk : k < w.length := by omega
    rw [keptPrefix_succ w mask k w[k] false (List.getElem?_eq_getElem hk) (hf k (by omega)),
      ih (by omega) (by omega) (fun j hj => hf j (by omega))]
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    simp only [Bool.false_eq_true, ite_false, Option.toList_some]

/-- The checked first index and the start of the index loop: positions before `i1` stay in
place and `i1` is skipped. -/
theorem maskInv_start (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (mask : List Bool)
    (hml : mask.length = n.val.toNat) (i1 : I) (hi1 : 1 ≤ i1.val ∧ i1.val ≤ n.val)
    (hsmall : n.val < 9223372036854775806)
    (hbefore : ∀ j : Nat, (j : Int) + 1 < i1.val → mask[j]? = some false)
    (hat : mask[(i1.val - 1).toNat]? = some true) :
    MaskInv handle mem off n (vwWindow slots off n) mask (i1.val.toNat) (i1, i1 + one) s := by
  have hwl := vwWindow_length h
  have hk : (i1.val - 1).toNat < (vwWindow slots off n).length := by rw [hwl]; omega
  have hpre := keptPrefix_all_false (vwWindow slots off n) mask (i1.val - 1).toNat (by omega)
    (by omega) (fun j hj => hbefore j (by omega))
  have h0 : MaskInv handle mem off n (vwWindow slots off n) mask (i1.val - 1).toNat (i1, i1) s := by
    refine ⟨slots, h, by show i1.val = _; omega, ?_, ?_, rfl⟩
    · show i1.val = _
      rw [hpre, List.length_take, hwl]; omega
    · rw [hpre, List.length_take, Nat.min_eq_left (by omega)]
  have h1 := maskInv_skip handle mem off n (vwWindow slots off n) mask _ (i1, i1) s _
    (List.getElem?_eq_getElem hk) hat (by omega) h0
  have hidx : (i1.val - 1).toNat + 1 = i1.val.toNat := by omega
  rw [hidx] at h1
  exact h1




/-- The last-processed cursor `q` after the indices `pre'`, starting from `d`. -/
def qlast (pre' : List I) (d : Int) : Int := (pre'.getLast?.map (fun x => x.val + 1)).getD d

theorem qlast_cons (x : I) (t : List I) (d : Int) : qlast (x :: t) d = qlast t (x.val + 1) := by
  cases t with
  | nil => rfl
  | cons y u =>
    simp only [qlast, List.getLast?_cons_cons]
    cases hl : (y :: u).getLast? with
    | none => simp at hl
    | some z => rfl



/-- `_deleteat!` whose first index is outside `1:length(a)`: `BoundsError`. -/
theorem deleteIter_err0 {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I)
    (post : List I) (hbad : ¬ (1 ≤ i.val ∧ i.val ≤ n.val)) :
    ((deleteatIterator (m := MutationM α) mutableLength (listIterator (i :: post)) Subtype.val
        (· + one) mutableBounds
        (pushDeleted mutableAssigned mutableGet (fun (_ : Unit) x => pure (pushNowhere x))
          (fun (_ : Unit) d => pure (growendNowhere d)))
        (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)) (· - ·)
        (deleteend (mutableStorage layout) pure) handle ()).run s).1 = .error .bounds := by
  have hlen := mutableLength_run s handle _ h.1
  have hfirst : ((listIterator (m := MutationM α) (i :: post)).first).run s =
      (.ok (some (i, post)), s) := rfl
  have hb : (mutableBounds handle i).run s = (.error .bounds, s) := by
    rw [vwBounds_run s handle mem off n slots h i, if_neg hbad]
  unfold deleteatIterator
  simp only [stateExcept_bind, hlen, hfirst, hb]
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
variable {α : Type}

/-- `_growend_internal!` moving the data to a new memory, with the new memory's slots spelled
out: unassigned before the offset and after the copied window. -/
theorem growendInternal_alloc_eq (l : DictLayout) {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val)
    (hov : off.val - 1 + n.val + delta.val ≤ 9223372036854775807)
    (hns : ¬ (n.val + delta.val < off.val - 1 ∧
      (n.val + delta.val) / 4 < off.val - 1 - (n.val + delta.val))) :
    let k : Nat := max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat
    memoryFits l k →
      (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
        (.ok (), { s with
          memories := (s.memories ++ [List.replicate k none]).set s.memories.length
            ((List.replicate k none).take (off.val - 1).toNat ++
              (slots.drop (off.val - 1).toNat).take n.val.toNat ++
              (List.replicate k none).drop (off.val - 1 + n.val).toNat)
          arrays := s.arrays.set handle ⟨(s.memories.length, off), n⟩ }) := by
  intro k hfit
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by omega)
  have hsum1 : -9223372036854775808 ≤ n.val + delta.val ∧ n.val + delta.val ≤ 9223372036854775807 := by
    omega
  have hsum2 : -9223372036854775808 ≤ (off - one).val + (n + delta).val ∧
      (off - one).val + (n + delta).val ≤ 9223372036854775807 := by
    rw [hoff1, hnd]; omega
  have hnm : (off - one + (n + delta)).val = off.val - 1 + n.val + delta.val := by
    rw [ival_add _ _ hsum2, hoff1, hnd]; omega
  have hadd1 := ms_checkedAdd_run (layout := MemoryLayoutMetadata.ofRuntime l) s n delta hsum1
  have hadd2 := ms_checkedAdd_run (layout := MemoryLayoutMetadata.ofRuntime l) s (off - one) (n + delta) hsum2
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  have hdiv4 := ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s (n + delta) (JInt.wrap .i64 4) (by rw [wval4]; decide)
  have hq4 : (JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 4).val)).val =
      (n.val + delta.val) / 4 := by
    rw [wval4, tdiv_nonneg_val (n + delta) 4 (by omega) (by decide) (by decide), hnd]
  have hdiff : (off - one - (n + delta)).val = off.val - 1 - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hoff1, hnd]; omega), hoff1, hnd]
  have hbranch : (decide (n + delta < off - one) &&
      decide (JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 4).val) < off - one - (n + delta))) =
        false := by
    rw [Bool.and_eq_false_iff]
    by_cases hs1 : n.val + delta.val < off.val - 1
    · right
      rw [decide_eq_false_iff_not, jlt_iff, hq4, hdiff]
      omega
    · left
      rw [decide_eq_false_iff_not, jlt_iff, hnd, hoff1]
      exact hs1
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := MemoryLayoutMetadata.ofRuntime l) s
    (JInt.wrap .i64 (slots.length : Int)) (by rw [hL]; omega)
  rw [hL, Int.toNat_natCast] at hcv
  have hKv : (max c (off - one + (n + delta))).val = (k : Int) := by
    rw [imax_val, hcv, hnm]
    simp only [k]
    omega
  have hA := arrayNewMemorySpec α l s mem (max c (off - one + (n + delta)))
  simp only at hA
  have hK0 : 0 ≤ (max c (off - one + (n + delta))).val := by rw [hKv]; omega
  have hKn : (max c (off - one + (n + delta))).val.toNat = k := by rw [hKv]; omega
  rw [hKn] at hA
  simp only [growendInternal, ms_ref, ms_memory, ms_offset, ms_memoryref, ms_copyRef, ms_sameMem,
    ms_sameRef, ms_unsetMemory, stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1, hadd2,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    hdiv4, hbranch, hcrun]
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have hkge : (off.val - 1 + n.val + delta.val).toNat ≤ k := Nat.le_max_right _ _
  have hOk : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c (off - one + (n + delta)))).run s =
      (.ok s.memories.length, { s with memories := s.memories ++ [List.replicate k none] }) :=
    hA.2.2 hK0 hfit
  have hk63 : k < 2 ^ 63 := by have := hfit.1; unfold maxIntVal at this; omega
  have hdM : ({ s with memories := s.memories ++ [List.replicate k none] } : MutableMemory α).memories[s.memories.length]? =
      some (List.replicate k none) := by simp
  have hsM : ({ s with memories := s.memories ++ [List.replicate k none] } : MutableMemory α).memories[mem]? =
      some slots := by
    show (s.memories ++ [List.replicate k none])[mem]? = some slots
    rw [List.getElem?_append_left hlt]; exact hm
  have hmove := vwMemoryMove_run { s with memories := s.memories ++ [List.replicate k none] }
    s.memories.length mem off off n (List.replicate k none) slots hdM hsM hn0 ho
    (by rw [List.length_replicate]; omega) ho he (by rw [List.length_replicate]; exact hk63)
  have hne : (s.memories.length == mem) = false := by rw [beq_eq_false_iff_ne]; omega
  simp only [hOk, hmove, hne, Bool.false_eq_true, ite_false]
  generalize hD : (List.replicate k none).take (off.val - 1).toNat ++
      (slots.drop (off.val - 1).toNat).take n.val.toNat ++
      (List.replicate k none).drop (off.val - 1 + n.val).toNat = D
  have href2 : (mutableRef handle).run
      { s with memories := (s.memories ++ [List.replicate k none]).set s.memories.length D } =
      (.ok (mem, off), { s with memories := (s.memories ++ [List.replicate k none]).set s.memories.length D }) :=
    mutableRef_run { s with memories := (s.memories ++ [List.replicate k none]).set s.memories.length D }
      handle _ ha
  have hset := ms_setRef_run (layout := MemoryLayoutMetadata.ofRuntime l)
    { s with memories := (s.memories ++ [List.replicate k none]).set s.memories.length D }
    handle ⟨(mem, off), n⟩ ha (s.memories.length, off)
  simp only [stateExcept_bind, href2, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false, hset]
  all_goals rfl
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
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

theorem vecAt_congr {s s' : MutableMemory α} {h m : Nat} {off n : I} {sl : List (Option α)}
    (hv : VecAt s h m off n sl) (ha : s'.arrays[h]? = s.arrays[h]?)
    (hm : s'.memories[m]? = s.memories[m]?) : VecAt s' h m off n sl := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  exact ⟨by rw [ha]; exact h1, by rw [hm]; exact h2, h3, h4, h5, h6⟩

theorem maskInv_congr {handle mem : Nat} {off n : I} {w0 : List (Option α)} {mask : List Bool}
    {k : Nat} {pq : I × I} {st st' : MutableMemory α}
    (h : MaskInv handle mem off n w0 mask k pq st) (ha : st'.arrays[handle]? = st.arrays[handle]?)
    (hm : st'.memories[mem]? = st.memories[mem]?) : MaskInv handle mem off n w0 mask k pq st' := by
  obtain ⟨sl, hv, rest⟩ := h
  exact ⟨sl, vecAt_congr hv ha hm, rest⟩

/-- Every slot from position `k` on is unassigned (or absent). -/
def TailNone (l : List (Option α)) (k : Nat) : Prop := ∀ j, k ≤ j → l[j]?.join = none

/-- The `splice!` result vector `dh` while `_deleteat!(a, inds, dh)` runs on vector `a` (memory
`amem`): a valid vector at offset 1 in its own memory, holding `done`, with geometry `g` and
unassigned slots after its last element. -/
def DltInv (a amem dh : Nat) (st : MutableMemory α) (g : VectorGeometry)
    (done : List (Option α)) : Prop :=
  ∃ md nd dsl, VecAt st dh md one nd dsl ∧ dh ≠ a ∧ md ≠ amem ∧
    g = ⟨dsl.length, 1, nd.val.toNat⟩ ∧ vwWindow dsl one nd = done ∧ TailNone dsl nd.val.toNat

theorem dltInv_congr {a amem dh : Nat} {st st' : MutableMemory α} {g : VectorGeometry}
    {done : List (Option α)} (h : DltInv a amem dh st g done)
    (ha : st'.arrays[dh]? = st.arrays[dh]?)
    (hm : ∀ m, m ≠ amem → st'.memories[m]? = st.memories[m]?) : DltInv a amem dh st' g done := by
  obtain ⟨md, nd, dsl, hv, h1, h2, rest⟩ := h
  exact ⟨md, nd, dsl, vecAt_congr hv ha (hm md h2), h1, h2, rest⟩

theorem vwWindow_one (l : List (Option α)) (n : I) : vwWindow l one n = l.take n.val.toNat := by
  simp [vwWindow, ival_one]

theorem tailNone_get (l : List (Option α)) (k : Nat) (ht : TailNone l k) (hk : k < l.length) :
    l[k]? = some none := by
  have := ht k (Nat.le_refl _)
  rw [List.getElem?_eq_getElem hk] at this ⊢
  simpa using this

theorem tailNone_mono {l : List (Option α)} {k k' : Nat} (ht : TailNone l k) (hk : k ≤ k') :
    TailNone l k' :=
  fun j hj => ht j (by omega)

theorem tailNone_set {l : List (Option α)} {k : Nat} (ht : TailNone l k) (i : Nat) (hi : i < k)
    (v : Option α) : TailNone (l.set i v) k := by
  intro j hj
  rw [List.getElem?_set_ne (by omega)]
  exact ht j hj

/-- `_growend!(d, 1)` on a vector at offset 1 whose slots after the last element are unassigned:
the new last slot is unassigned and the offset stays 1. -/
theorem growendOne (l : DictLayout) {s : MutableMemory α} {dh md : Nat} {nd : I}
    {dsl : List (Option α)} (h : VecAt s dh md one nd dsl) (ht : TailNone dsl nd.val.toNat) :
    (∀ e, growendPlan l ⟨dsl.length, 1, nd.val.toNat⟩ 1 = .error e →
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) dh one).run s
        = (.error e, s)) ∧
    (∀ g', growendPlan l ⟨dsl.length, 1, nd.val.toNat⟩ 1 = .ok g' →
      ∃ next md' dsl',
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) dh one).run s
          = (.ok (), next) ∧
        VecAt next dh md' one (nd + one) dsl' ∧
        next.arrays = s.arrays.set dh ⟨(md', one), nd + one⟩ ∧
        (nd + one).val = nd.val + 1 ∧
        dsl'.take nd.val.toNat = dsl.take nd.val.toNat ∧
        dsl'[nd.val.toNat]? = some none ∧
        TailNone dsl' (nd.val.toNat + 1) ∧
        g' = ⟨dsl'.length, 1, nd.val.toNat + 1⟩ ∧
        (∀ m, m < s.memories.length → m ≠ md → next.memories[m]? = s.memories[m]?) ∧
        (md' = md ∨ md' = s.memories.length)) := by
  obtain ⟨herr, hok⟩ := growend_plan l h one (by rw [ival_one]; decide)
  have h1 : (one : I).val.toNat = 1 := by rw [ival_one]; rfl
  rw [h1] at herr hok
  refine ⟨herr, fun g' hg' => ?_⟩
  obtain ⟨next, mem', off', slots', hrun, _, _, hnd, _, hgeo, _, _, _⟩ := hok g' hg'
  rw [ival_one] at hnd
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  rw [ival_one] at he
  have hnb := ival_bounds nd
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hd1 : 0 ≤ (one : I).val := by rw [ival_one]; decide
  by_cases hfast : nd.val < (dsl.length : Int)
  · have hr := growend_fast (layout := MemoryLayoutMetadata.ofRuntime l) h' one hd1 (by rw [ival_one]; omega)
    have hn := (Prod.mk.inj (hr.symm.trans hrun)).2
    subst hn
    have hv : VecAt { s with arrays := s.arrays.set dh ⟨(md, one), nd + one⟩ } dh md one
        (nd + one) dsl :=
      ⟨List.getElem?_set_self halt, hm, by rw [ival_one]; decide, by omega,
        by rw [ival_one, hnd]; omega, hc⟩
    have hk : nd.val.toNat < dsl.length := by omega
    refine ⟨_, md, dsl, hr, hv, rfl, hnd, rfl, tailNone_get dsl _ ht hk,
      tailNone_mono ht (Nat.le_succ _), ?_, fun _ _ _ => rfl, Or.inl rfl⟩
    rw [← hgeo, VecAt.geometry hv, hnd, h1]
    simp only [VectorGeometry.mk.injEq, true_and]
    omega
  · have hnl : nd.val = dsl.length := by omega
    have hslow : (dsl.length : Int) - ((one : I).val - 1) - nd.val < (one : I).val := by
      rw [ival_one]; omega
    by_cases hov : nd.val + 1 ≤ 9223372036854775807
    · have hov' : (one : I).val - 1 + nd.val + (one : I).val ≤ 9223372036854775807 := by
        rw [ival_one]; omega
      have hns : ¬ (nd.val + (one : I).val < (one : I).val - 1 ∧
          (nd.val + (one : I).val) / 4 < (one : I).val - 1 - (nd.val + (one : I).val)) := by
        rw [ival_one]; omega
      by_cases hfit : memoryFits l
          (max (overallocationNat dsl.length) ((one : I).val - 1 + nd.val + (one : I).val).toNat)
      · have hint := growendInternal_alloc_eq l h' one hd1 hov' hns hfit
        have hr := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' one hd1 hslow _ _ hint
        rw [setSize_after s _ dh _ halt] at hr
        obtain ⟨K, hK⟩ : ∃ K, K = max (overallocationNat dsl.length)
            ((one : I).val - 1 + nd.val + (one : I).val).toNat := ⟨_, rfl⟩
        have h1v : (one : I).val = 1 := ival_one
        have hkge : nd.val.toNat + 1 ≤ K := by
          have := Nat.le_max_right (overallocationNat dsl.length)
            ((one : I).val - 1 + nd.val + (one : I).val).toNat
          rw [← hK] at this; omega
        have hk63 : K < 2 ^ 63 := by
          rw [hK]; have := hfit.1; unfold maxIntVal at this; omega
        have e1 : ((one : I).val - 1).toNat = 0 := by rw [ival_one]; rfl
        have e2 : ((one : I).val - 1 + nd.val).toNat = dsl.length := by rw [ival_one]; omega
        have hnl' : nd.val.toNat = dsl.length := by omega
        have hD : (List.replicate (max (overallocationNat dsl.length)
              ((one : I).val - 1 + nd.val + (one : I).val).toNat) none).take ((one : I).val - 1).toNat ++
            (dsl.drop ((one : I).val - 1).toNat).take nd.val.toNat ++
            (List.replicate (max (overallocationNat dsl.length)
              ((one : I).val - 1 + nd.val + (one : I).val).toNat) none).drop ((one : I).val - 1 + nd.val).toNat =
            dsl ++ List.replicate (K - dsl.length) none := by
          rw [← hK, e1, e2, hnl', List.take_zero, List.drop_zero, List.take_length, List.drop_replicate,
            List.nil_append]
        have hr2 : (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
            dh one).run s = (.ok (), { s with
              memories := (s.memories ++ [List.replicate K none]).set s.memories.length
                (dsl ++ List.replicate (K - dsl.length) none)
              arrays := s.arrays.set dh ⟨(s.memories.length, one), nd + one⟩ }) := by
          rw [← hD, hK]; exact hr
        have hn := (Prod.mk.inj (hr2.symm.trans hrun)).2
        subst hn
        have hDlen : (dsl ++ List.replicate (K - dsl.length) (none : Option α)).length = K := by
          simp only [List.length_append, List.length_replicate]; omega
        have hMlt : s.memories.length < (s.memories ++ [List.replicate K (none : Option α)]).length := by
          simp
        have hv : VecAt { s with
            memories := (s.memories ++ [List.replicate K none]).set s.memories.length
              (dsl ++ List.replicate (K - dsl.length) none)
            arrays := s.arrays.set dh ⟨(s.memories.length, one), nd + one⟩ } dh
            s.memories.length one (nd + one) (dsl ++ List.replicate (K - dsl.length) none) :=
          ⟨List.getElem?_set_self halt, List.getElem?_set_self hMlt, by rw [ival_one]; decide,
            by omega, by rw [hDlen, ival_one, hnd]; omega, by rw [hDlen]; exact hk63⟩
        refine ⟨_, s.memories.length, _, hr2, hv, rfl, hnd, ?_, ?_, ?_, ?_, ?_, Or.inr rfl⟩
        · first
          | rw [hnl', List.take_append_of_le_length (Nat.le_refl _)]
          | simp [hnl']
        · rw [hnl', List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_replicate]
          rw [if_pos (by omega)]
        · intro j hj
          rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
          split <;> rfl
        · rw [← hgeo, VecAt.geometry hv, hnd, h1, hDlen]
          simp only [VectorGeometry.mk.injEq, true_and]
          omega
        · intro m hm' _
          show ((s.memories ++ [List.replicate K none]).set s.memories.length _)[m]? = _
          rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hm']
      · have hr := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' one hd1 hslow _ _
          ((growendInternal_alloc l h' one hd1 hov' hns).1 hfit)
        have := hr.symm.trans hrun
        exact absurd (congrArg Prod.fst this) (by simp)
    · have hr := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' one hd1 hslow _ _
        (growendInternal_overflow1 h' one (by rw [ival_one]; omega))
      have := hr.symm.trans hrun
      exact absurd (congrArg Prod.fst this) (by simp)

/-- `push!(d, x)` on a vector at offset 1 whose slots after the last element are unassigned. -/
theorem pushOne (l : DictLayout) {s : MutableMemory α} {dh md : Nat} {nd : I}
    {dsl : List (Option α)} (h : VecAt s dh md one nd dsl) (ht : TailNone dsl nd.val.toNat) (x : α) :
    (∀ e, growendPlan l ⟨dsl.length, 1, nd.val.toNat⟩ 1 = .error e →
      (mutablePush (MemoryLayoutMetadata.ofRuntime l) dh x).run s = (.error e, s)) ∧
    (∀ g', growendPlan l ⟨dsl.length, 1, nd.val.toNat⟩ 1 = .ok g' →
      ∃ next md' dsl', (mutablePush (MemoryLayoutMetadata.ofRuntime l) dh x).run s = (.ok (), next) ∧
        VecAt next dh md' one (nd + one) dsl' ∧
        next.arrays = s.arrays.set dh ⟨(md', one), nd + one⟩ ∧
        (nd + one).val = nd.val + 1 ∧
        dsl'.take (nd.val.toNat + 1) = dsl.take nd.val.toNat ++ [some x] ∧
        TailNone dsl' (nd.val.toNat + 1) ∧
        g' = ⟨dsl'.length, 1, nd.val.toNat + 1⟩ ∧
        (∀ m, m < s.memories.length → m ≠ md → next.memories[m]? = s.memories[m]?) ∧
        (md' = md ∨ md' = s.memories.length)) := by
  obtain ⟨herr, hok⟩ := growendOne l h ht
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · simp only [mutablePush, push1361, stateExcept_bind, herr e he]
  · obtain ⟨next, md', dsl', hrun, hv, harr, hnd, hpre, hlast, htail, hg, hframe, hmd⟩ := hok g' hg'
    have hnb := ival_bounds nd
    have hn0 := h.2.2.2.1
    have hset := vwSet_run next dh md' one (nd + one) dsl' hv (nd + one)
      ⟨by omega, Int.le_refl _⟩ x
    have hidx : ((one : I).val - 1 + (nd + one).val - 1).toNat = nd.val.toNat := by
      rw [ival_one, hnd]; omega
    rw [hidx] at hset
    have hlen : nd.val.toNat < dsl'.length := (List.getElem?_eq_some_iff.mp hlast).choose
    refine ⟨{ next with memories := next.memories.set md' (dsl'.set nd.val.toNat (some x)) }, md',
      dsl'.set nd.val.toNat (some x), ?_, hv.set nd.val.toNat (some x), harr, hnd, ?_, ?_, ?_, ?_, hmd⟩
    · simp only [mutablePush, push1361, stateExcept_bind, hrun, mutableLength_run next dh _ hv.1,
        hset, stateExcept_pure]
    · rw [list_set_take_succ _ _ _ hlen, hpre]
    · exact tailNone_set htail _ (by omega) _
    · rw [List.length_set]; exact hg
    · intro m hm hne
      have hne' : m ≠ md' := by
        rcases hmd with rfl | rfl
        · exact hne
        · omega
      show (next.memories.set md' _)[m]? = _
      rw [List.getElem?_set_ne (fun he => hne' he.symm)]
      exact hframe m hm hne
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
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- `_push_deleted!(dltds, a, i)` for `splice!(a, inds)`: `push!(dltds, a[i])` for an assigned
slot, `_growend!(dltds, 1)` for an unassigned one. -/
abbrev spliceSink (l : DictLayout) : Nat → Nat → I → MutationM α Unit :=
  pushDeleted mutableAssigned mutableGet (fun d v => mutablePush (MemoryLayoutMetadata.ofRuntime l) d v)
    (fun d n => growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) d n)

/-- One `_push_deleted!` into the `splice!` result: it follows `growendPlan`, appends slot `i` of
`a` (unassigned stays unassigned) and leaves `a`'s header and memory alone. -/
theorem sinkStep (l : DictLayout) {st : MutableMemory α} {a mem dh : Nat} {off n : I}
    {sl : List (Option α)} (hv : VecAt st a mem off n sl) (i : I) (hi : 1 ≤ i.val ∧ i.val ≤ n.val)
    {g : VectorGeometry} {done : List (Option α)} (hD : DltInv a mem dh st g done) :
    (∀ e, growendPlan l g 1 = .error e → (spliceSink l dh a i).run st = (.error e, st)) ∧
    (∀ g', growendPlan l g 1 = .ok g' → ∃ st', (spliceSink l dh a i).run st = (.ok (), st') ∧
      st'.arrays[a]? = st.arrays[a]? ∧ st'.memories[mem]? = st.memories[mem]? ∧
      DltInv a mem dh st' g' (done ++ [(vwWindow sl off n)[(i.val - 1).toNat]?.join])) := by
  obtain ⟨md, nd, dsl, hvd, hne, hmd, rfl, rfl, ht⟩ := hD
  have hasg := vwAssigned_run st a mem off n sl hv i hi
  have hget := vwGet_run st a mem off n sl hv i hi
  have hwl := vwWindow_length hv
  have hlt : (i.val - 1).toNat < (vwWindow sl off n).length := by rw [hwl]; omega
  obtain ⟨v, hw⟩ : ∃ v, (vwWindow sl off n)[(i.val - 1).toNat]? = some v :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [hw] at hasg hget
  rw [hw, Option.join_some]
  have hmemlt : mem < st.memories.length := (List.getElem?_eq_some_iff.mp hv.2.1).choose
  have hnb := ival_bounds nd
  have hn0 := hvd.2.2.2.1
  cases v with
  | some x =>
    obtain ⟨herr, hok⟩ := pushOne l hvd ht x
    refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
    · simp only [pushDeleted, stateExcept_bind, hasg, Option.join_some, Option.isSome_some, ite_true,
        hget, herr e he]
    · obtain ⟨next, md', dsl', hrun, hv', harr, hnd, htake, htail, hg, hframe, hmd'⟩ := hok g' hg'
      have hk : (nd + one).val.toNat = nd.val.toNat + 1 := by rw [hnd]; omega
      refine ⟨next, ?_, ?_, hframe mem hmemlt (fun h => hmd h.symm), md', nd + one, dsl', hv', hne,
        ?_, ?_, ?_, ?_⟩
      · simp only [pushDeleted, stateExcept_bind, hasg, Option.join_some, Option.isSome_some,
          ite_true, hget, hrun]
      · rw [harr, List.getElem?_set_ne hne]
      · rcases hmd' with rfl | rfl
        · exact hmd
        · omega
      · rw [hk]; exact hg
      · rw [vwWindow_one, vwWindow_one, hk]; exact htake
      · rw [hk]; exact htail
  | none =>
    obtain ⟨herr, hok⟩ := growendOne l hvd ht
    refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
    · simp only [pushDeleted, stateExcept_bind, hasg, Option.join_some, Option.isSome_none,
        Bool.false_eq_true, ite_false, herr e he]
    · obtain ⟨next, md', dsl', hrun, hv', harr, hnd, hpre, hlast, htail, hg, hframe, hmd'⟩ :=
        hok g' hg'
      have hk : (nd + one).val.toNat = nd.val.toNat + 1 := by rw [hnd]; omega
      refine ⟨next, ?_, ?_, hframe mem hmemlt (fun h => hmd h.symm), md', nd + one, dsl', hv', hne,
        ?_, ?_, ?_, ?_⟩
      · simp only [pushDeleted, stateExcept_bind, hasg, Option.join_some, Option.isSome_none,
          Bool.false_eq_true, ite_false, hrun]
      · rw [harr, List.getElem?_set_ne hne]
      · rcases hmd' with rfl | rfl
        · exact hmd
        · omega
      · rw [hk]; exact hg
      · rw [vwWindow_one, vwWindow_one, hk, List.take_succ, hpre, hlast]
        rfl
      · rw [hk]; exact htail
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
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt


/-- `_deleteat!` of `splice!` whose first index is outside `1:length(a)`: `BoundsError`. -/
theorem spliceIter_err0 (l : DictLayout) (s : MutableMemory α) (handle mem dh : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I)
    (post : List I) (hbad : ¬ (1 ≤ i.val ∧ i.val ≤ n.val)) :
    ((deleteatIterator (m := MutationM α) mutableLength (listIterator (i :: post)) Subtype.val
        (· + one) mutableBounds (spliceSink l)
        (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)) (· - ·)
        (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) handle dh).run s).1 = .error .bounds := by
  have hlen := mutableLength_run s handle _ h.1
  have hfirst : ((listIterator (m := MutationM α) (i :: post)).first).run s =
      (.ok (some (i, post)), s) := rfl
  have hb : (mutableBounds handle i).run s = (.error .bounds, s) := by
    rw [vwBounds_run s handle mem off n slots h i, if_neg hbad]
  unfold deleteatIterator
  simp only [stateExcept_bind, hlen, hfirst, hb]


theorem spliceIndices_eq (l : DictLayout) (a : Nat) (inds : List I) :
    mutableSpliceIndices (α := α) (MemoryLayoutMetadata.ofRuntime l) a inds = (do
      let dltds ← mutableAllocate (MemoryLayoutMetadata.ofRuntime l) a zero
      let _ ← deleteatIterator (m := MutationM α) mutableLength (listIterator inds) Subtype.val
        (· + one) mutableBounds (spliceSink l)
        (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)) (· - ·)
        (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) a dltds
      pure dltds) := rfl

/-- The fresh `eltype(a)[]` of `splice!`. -/
abbrev spliceStart (s : MutableMemory α) : MutableMemory α :=
  { memories := s.memories ++ [[]], arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩] }

theorem splice_ok_of (l : DictLayout) (a : Nat) (inds : List I) (s : MutableMemory α)
    (x : Nat) (st : MutableMemory α)
    (h : (deleteatIterator (m := MutationM α) mutableLength (listIterator inds) Subtype.val
        (· + one) mutableBounds (spliceSink l)
        (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)) (· - ·)
        (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) a s.arrays.length).run (spliceStart s) =
        (.ok x, st)) :
    (mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime l) a inds).run s = (.ok s.arrays.length, st) := by
  have hA : (mutableAllocate (α := α) (MemoryLayoutMetadata.ofRuntime l) a zero).run s = (.ok s.arrays.length, spliceStart s) :=
    mutableAllocate_zero_run l s
  rw [spliceIndices_eq]
  simp only [stateExcept_bind, hA, h, stateExcept_pure]

theorem splice_err_of (l : DictLayout) (a : Nat) (inds : List I) (s : MutableMemory α)
    (e : Error)
    (h : ((deleteatIterator (m := MutationM α) mutableLength (listIterator inds) Subtype.val
        (· + one) mutableBounds (spliceSink l)
        (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)) (· - ·)
        (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) a s.arrays.length).run (spliceStart s)).1 =
        .error e) :
    ((mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime l) a inds).run s).1 = .error e := by
  have hA : (mutableAllocate (α := α) (MemoryLayoutMetadata.ofRuntime l) a zero).run s = (.ok s.arrays.length, spliceStart s) :=
    mutableAllocate_zero_run l s
  rw [spliceIndices_eq]
  simp only [stateExcept_bind, hA]
  revert h
  cases (deleteatIterator (m := MutationM α) mutableLength (listIterator inds) Subtype.val
      (· + one) mutableBounds (spliceSink l)
      (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)) (· - ·)
      (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) a s.arrays.length).run (spliceStart s) with
  | mk r st =>
    intro h
    dsimp only at h
    subst h
    rfl

theorem spliceStart_vecAt {s : MutableMemory α} {a mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s a mem off n slots) :
    VecAt (spliceStart s) a mem off n slots :=
  vecAt_congr h (List.getElem?_append_left (List.getElem?_eq_some_iff.mp h.1).choose)
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp h.2.1).choose)

theorem spliceStart_dltInv {s : MutableMemory α} {a mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s a mem off n slots) :
    DltInv a mem s.arrays.length (spliceStart s) emptyGeometry [] := by
  have ha := (List.getElem?_eq_some_iff.mp h.1).choose
  have hm := (List.getElem?_eq_some_iff.mp h.2.1).choose
  refine ⟨s.memories.length, zero, [], ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩,
    by omega, by omega, by rw [ival_zero]; rfl, by simp [vwWindow], fun j _ => by simp⟩
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array

theorem spliceIndex_outside {α : Type} (l : DictLayout) (s : MutableMemory α)
    (a : Nat) (i : I) (ins : List α) (already : α → Bool)
    (convert : α → Except Error α) (hvalid : s.validVector a)
    (hout : i.val < 1 ∨ (s.contents a).length < i.val) :
    (mutableSpliceIndex (MemoryLayoutMetadata.ofRuntime l) already convert a i ins).run s = (.error .bounds, s) := by
  obtain ⟨_, _, n, _, h⟩ := validVector_vecAt hvalid
  have hwl := vwWindow_length h
  have hc := h.contents
  have hn0 := h.2.2.2.1
  have hlen : ((s.contents a).length : Int) = n.val := by rw [hc, hwl]; omega
  have hi : i.val < 1 ∨ n.val < i.val := by rw [← hlen]; exact hout
  unfold mutableSpliceIndex
  simp only [spliceIndex, stateExcept_bind, vwGet_outside s a _ h.1 i hi]

theorem spliceIndex_undefined {α : Type} (l : DictLayout) (s : MutableMemory α)
    (a : Nat) (i : I) (ins : List α) (already : α → Bool)
    (convert : α → Except Error α) (hvalid : s.validVector a)
    (hi1 : 1 ≤ i.val) (hin : i.val ≤ (s.contents a).length)
    (hslot : (s.contents a)[(i.val - 1).toNat]? = some none) :
    (mutableSpliceIndex (MemoryLayoutMetadata.ofRuntime l) already convert a i ins).run s =
      (.error .undefinedReference, s) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hwl := vwWindow_length h
  have hc := h.contents
  have hn0 := h.2.2.2.1
  have hlen : ((s.contents a).length : Int) = n.val := by rw [hc, hwl]; omega
  have hi : 1 ≤ i.val ∧ i.val ≤ n.val := by rw [← hlen]; exact ⟨hi1, hin⟩
  have hslot' : (vwWindow slots off n)[(i.val - 1).toNat]? = some none := by
    rw [← hc]
    exact hslot
  have hget := vwGet_run s a mem off n slots h i hi
  rw [hslot'] at hget
  unfold mutableSpliceIndex
  simp only [spliceIndex, stateExcept_bind, hget]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000

theorem spliceIndex_one {m : Type → Type} [Monad m] [LawfulMonad m]
    [ForIn m Ins β] (get : A → Z → m α) (length : Ins → I)
    (deleteat growat : A → Z → I → m Unit) (only : Ins → m β)
    (set : A → β → Z → m Unit) (add : Z → I → Z) (sub : Z → Z)
    (a : A) (i : Z) (ins : Ins) (x : β)
    (hlen : length ins = one) (honly : only ins = pure x) :
    spliceIndex get length deleteat growat only set add sub a i ins =
      (do let value ← get a i; set a x i; pure value) := by
  have hn : (one : I) ≠ zero := by decide
  simp only [spliceIndex, hlen, hn, ite_false, ite_true, honly, pure_bind]

theorem spliceIndex_single_eq (layout : MemoryLayoutMetadata) (already : α → Bool)
    (convert : α → Except Error α) (a : Nat) (i : I) (x : α) :
    mutableSpliceIndex layout already convert a i [x] =
      (do let value ← mutableGet a i
          let replacement ← stateExceptLift (storedValue already convert x)
          mutableSet a replacement i
          pure value) := by
  unfold mutableSpliceIndex
  rw [spliceIndex_one (m := MutationM α) (Ins := List α) (ins := [x]) (x := x)
    (length := fun xs : List α => JInt.wrap .i64 xs.length) (hlen := rfl) (honly := rfl)]
  simp only [convertingSet_eq, bind_assoc]

theorem spliceIndex_single (layout : MemoryLayoutMetadata) (already : α → Bool)
    (convert : α → Except Error α) (s : MutableMemory α) (a mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s a mem off n slots) (i : I) (x value : α)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val)
    (hslot : (vwWindow slots off n)[(i.val - 1).toNat]? = some (some value)) :
    (∀ replacement, storedValue already convert x = .ok replacement →
      ∃ after, (mutableSpliceIndex layout already convert a i [x]).run s = (.ok value, after) ∧
        after.validVector a ∧
        after.contents a = (s.contents a).set (i.val - 1).toNat (some replacement)) ∧
    (∀ error, storedValue already convert x = .error error →
      (mutableSpliceIndex layout already convert a i [x]).run s = (.error error, s)) := by
  have hg := vwGet_run s a mem off n slots h i hi
  rw [hslot] at hg
  refine ⟨fun replacement hc => ?_, fun error hc => ?_⟩
  · let after : MutableMemory α :=
      { s with memories := s.memories.set mem (slots.set (off.val - 1 + i.val - 1).toNat (some replacement)) }
    have hv : VecAt after a mem off n
        (slots.set (off.val - 1 + i.val - 1).toNat (some replacement)) := h.set _ _
    refine ⟨after, ?_, hv.valid, ?_⟩
    · rw [spliceIndex_single_eq]
      simp only [stateExcept_bind, hg, stateExceptLift_run, hc,
        vwSet_run s a mem off n slots h i hi replacement, stateExcept_pure]
      rfl
    · rw [hv.contents, vwWindow_set slots off n i (some replacement) h.2.2.1 hi.1,
        ← h.contents]
  · rw [spliceIndex_single_eq]
    simp only [stateExcept_bind, hg, stateExceptLift_run, hc]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array

theorem spliceIndex_zero {m : Type → Type} [Monad m] [LawfulMonad m]
    [ForIn m Ins β] (get : A → Z → m α) (length : Ins → I)
    (deleteat growat : A → Z → I → m Unit) (only : Ins → m β)
    (set : A → β → Z → m Unit) (add : Z → I → Z) (sub : Z → Z)
    (a : A) (i : Z) (ins : Ins) (hlen : length ins = zero) :
    spliceIndex get length deleteat growat only set add sub a i ins =
      (do let value ← get a i; deleteat a i one; pure value) := by
  simp only [spliceIndex, hlen, ite_true]

theorem spliceIndex_empty_eq (layout : MemoryLayoutMetadata) (already : α → Bool)
    (convert : α → Except Error α) (a : Nat) (i : I) :
    mutableSpliceIndex layout already convert a i [] =
      (do let value ← mutableGet a i
          vecDeleteat α (layout := layout) a i one
          pure value) := by
  unfold mutableSpliceIndex
  rw [spliceIndex_zero (m := MutationM α) (Ins := List α) (ins := [])
    (length := fun xs : List α => JInt.wrap .i64 xs.length) (hlen := rfl)]

theorem spliceIndex_empty (layout : MemoryLayoutMetadata) (already : α → Bool)
    (convert : α → Except Error α) (s : MutableMemory α) (a mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s a mem off n slots) (i : I) (value : α)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val)
    (hslot : (vwWindow slots off n)[(i.val - 1).toNat]? = some (some value)) :
    ∃ after, (mutableSpliceIndex layout already convert a i []).run s = (.ok value, after) ∧
      after.validVector a ∧ after.contents a = (s.contents a).eraseIdx (i.val - 1).toNat := by
  have hg := vwGet_run s a mem off n slots h i hi
  rw [hslot] at hg
  obtain ⟨after, hd, hv, hcontents, _⟩ := deleteOne_run (layout := layout) s a mem off n slots h i one
    hi.1 hi.2 ival_one
  refine ⟨after, ?_, hv, ?_⟩
  · rw [spliceIndex_empty_eq]
    simp only [stateExcept_bind, hg, hd, stateExcept_pure]
  · rw [hcontents, ival_one, ← h.contents, List.eraseIdx_eq_take_drop_succ]
    rw [show (i.val - 1 + 1).toNat = (i.val - 1).toNat + 1 by have := hi.1; omega]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
set_option maxHeartbeats 1000000

theorem convertingStep_eq (already : α → Bool) (convert : α → Except Error α)
    (a : Nat) (x : α) (j k : I) :
    (do let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet a x j
        pure (ForInStep.yield (k + one))) =
      (do let value ← stateExceptLift (storedValue already convert x)
          mutableSet a value j
          pure (ForInStep.yield (k + one))) := by
  unfold setindexScalar storedValue
  cases hx : already x <;>
    simp only [hx, Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc, mutableSet,
      mutableTypedSet]
  all_goals rfl

theorem spliceStores_run {α β : Type} (layout : Option MemoryLayout)
    (convert : β → Except Error α) (a mem : Nat) (off n i : I) (hi : 1 ≤ i.val) :
    ∀ (xs : List β) (cs : List α) (s : MutableMemory α) (slots : List (Option α))
      (p : Nat) (k : I),
    VecAt s a mem off n slots →
    i.val - 1 + p + xs.length ≤ n.val →
    (xs ≠ [] → k.val = p + 1) →
    xs.mapM convert = .ok cs →
    ∃ finalK after,
      (forIn xs k (fun x k => do
        let value ← stateExceptLift (convert x)
        mutableSet a value (i + k - one)
        pure (ForInStep.yield (k + one)))).run s = (.ok finalK, after) ∧
      after.validVector a ∧
      after.contents a =
        (s.contents a).take (i.val - 1 + p).toNat ++ cs.map some ++
          (s.contents a).drop (i.val - 1 + p + cs.length).toNat ∧
      after.arrays = s.arrays ∧
      ∀ m, m ≠ mem → after.memories[m]? = s.memories[m]? := by
  intro xs
  induction xs with
  | nil =>
    intro cs s slots p k hv hcap hk hmap
    have hcs : cs = [] := by simpa [List.mapM_nil, pure, Except.pure] using hmap.symm
    subst cs
    refine ⟨k,s,rfl,hv.valid,?_,rfl,fun _ _ => rfl⟩
    simpa using (List.take_append_drop (i.val - 1 + p).toNat (s.contents a)).symm
  | cons x xs ih =>
    intro cs s slots p k hv hcap hk hmap
    have hkval := hk (by simp)
    cases hc : convert x with
    | error error => simp [List.mapM_cons, hc, Bind.bind, Except.bind, pure, Except.pure] at hmap
    | ok replacement =>
      cases hm : xs.mapM convert with
      | error error => simp [List.mapM_cons, hc, hm, Bind.bind, Except.bind, pure, Except.pure] at hmap
      | ok tail =>
        have hcs : cs = replacement :: tail := by
          simpa [List.mapM_cons, hc, hm, Bind.bind, Except.bind, pure, Except.pure] using hmap.symm
        subst cs
        have hn0 := hv.2.2.2.1
        have hnb := ival_bounds n
        have hj : (i + k - one).val = i.val + p := by
          rw [ival_add_sub_one i k (by simp only [List.length_cons] at hcap; rw [hkval]; omega), hkval]
          omega
        have hjin : 1 ≤ (i + k - one).val ∧ (i + k - one).val ≤ n.val := by
          rw [hj]
          simp only [List.length_cons] at hcap
          omega
        let mid : MutableMemory α :=
          { s with memories := s.memories.set mem (slots.set (off.val - 1 + (i + k - one).val - 1).toNat (some replacement)) }
        have hmid : VecAt mid a mem off n
            (slots.set (off.val - 1 + (i + k - one).val - 1).toNat (some replacement)) := hv.set _ _
        have hw : mid.contents a = (s.contents a).set (i.val - 1 + p).toNat (some replacement) := by
          rw [hmid.contents, vwWindow_set slots off n (i + k - one) (some replacement)
            hv.2.2.1 hjin.1, ← hv.contents, hj]
          congr 2 <;> omega
        have hnext : xs ≠ [] → (k + one).val = (p + 1 : Nat) + 1 := by
          intro hne
          have hxlen : 0 < xs.length := List.length_pos_iff.mpr hne
          simp only [List.length_cons] at hcap
          rw [ival_add_one k (by rw [hkval]; omega), hkval]
          omega
        obtain ⟨finalK,after,hrun,hvalid,hcontents,harrays,hOther⟩ := ih tail mid _ (p + 1) (k + one)
          hmid (by simp only [List.length_cons] at hcap; omega) hnext hm
        refine ⟨finalK,after,?_,hvalid,?_,harrays,?_⟩
        · simp only [List.forIn_cons,stateExcept_bind,stateExceptLift_run,hc,
            vwSet_run s a mem off n slots hv (i + k - one) hjin replacement,stateExcept_pure]
          exact hrun
        · rw [hcontents, hw]
          have hq : (i.val - 1 + p).toNat < (s.contents a).length := by
            rw [hv.contents, vwWindow_length hv]
            simp only [List.length_cons] at hcap
            omega
          have hq1 : (i.val - 1 + (p + 1 : Nat)).toNat = (i.val - 1 + p).toNat + 1 := by omega
          have hqtail : (i.val - 1 + (p + 1 : Nat) + tail.length).toNat =
              (i.val - 1 + p).toNat + 1 + tail.length := by omega
          rw [hq1, hqtail, list_set_take_succ _ _ _ hq, list_set_drop_of_lt _ _ _ _ (by omega)]
          simp only [List.map_cons, List.length_cons, List.append_assoc, List.singleton_append]
          congr 4 <;> omega
        · intro m hne
          rw [hOther m hne]
          change (s.memories.set mem _)[m]? = s.memories[m]?
          exact List.getElem?_set_ne (Ne.symm hne)
end solArrayGrow
end JuliaLean.Proofs.base.array

