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

/-- The complete documented isbitsunion contract, including every union cardinality. -/
def IsBitsUnionDocumented : Prop :=
  (∀ ms : List Layout, 2 ≤ ms.length → (ms.map Layout.name).Nodup → (∀ d ∈ ms, d.WF) →
    (isbitsunion unionType storedInline (.union ms) = true ↔ ∀ d ∈ ms, d.isbits = true) ∧
      allocatedinline storedInline (.union ms) = isbitsunion unionType storedInline (.union ms)) ∧
  (∀ t : StoredType, (∀ ms, t ≠ .union ms) → isbitsunion unionType storedInline t = false) ∧
  (∀ d : Layout, d.WF → d.isbits = true → allocatedinline storedInline (.dt d) = true) ∧
  (∀ d : Layout, d.mayInline = false → allocatedinline storedInline (.dt d) = false) ∧
  allocatedinline storedInline .any = false ∧ allocatedinline storedInline .bottom = false ∧
    ∀ n, allocatedinline storedInline (.abstractDT n) = false

def valTypes : List Layout := (List.range 127).map fun i => ⟨i, true, true, false, false, 0, 1⟩

def IsBitsUnionSmall : Prop := ∀ ms : List Layout,
  2 ≤ ms.length → ms.length < 127 → (∀ d ∈ ms, d.WF) →
    (isbitsunion unionType storedInline (.union ms) = true ↔ ∀ d ∈ ms, d.isbits = true)

theorem isBitsUnionSmall : IsBitsUnionSmall := by
  intro ms hlow hhigh hwf
  have heq : ∀ d ∈ ms, inlineAlloc d true = d.isbits := by
    intro d hd
    simpa [inlineAlloc] using (hwf d hd).1.symm
  by_cases hall : ms.all (fun d => inlineAlloc d true) = true
  · have hb : ∀ d ∈ ms, d.isbits = true := by
      intro d hd
      rw [← heq d hd]
      exact List.all_eq_true.mp hall d hd
    have htest : isbitsunion unionType storedInline (.union ms) = true := by
      simp [isbitsunion, unionType, allocatedinline, storedInline, unionInlineCount, hall,
        show 0 < ms.length by omega, hhigh, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    exact ⟨fun _ => hb, fun _ => htest⟩
  · have hfalse : ms.all (fun d => inlineAlloc d true) = false := by
      cases h : ms.all (fun d => inlineAlloc d true) <;> simp_all
    have htest : isbitsunion unionType storedInline (.union ms) = false := by
      simp [isbitsunion, unionType, allocatedinline, storedInline, unionInlineCount, hfalse,
        JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    constructor
    · intro h
      rw [htest] at h
      contradiction
    · intro hb
      apply False.elim
      apply hall
      apply List.all_eq_true.mpr
      intro d hd
      rw [heq d hd]
      exact hb d hd

def WrapMemoryIntegerSpec : Prop :=
  ∀ (nativeInt : Bool) (len capacity : Nat),
    len ≤ capacity → capacity < 2 ^ 63 →
    wrapMemoryLength (m := Except Error)
      (fun n : Nat => .ok (JInt.wrap .i64 n))
      (fun cap : Nat => .ok (JInt.wrap .i64 cap, one))
      (fun ref dims =>
        if nativeInt then
          wrapCheck Prod.fst id Prod.snd
            (fun ds => .ok (JInt.wrap .i64 (ds.foldl (fun n d => n * d.val) 1)))
            ref (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int)))
        else .error (.method "_wrap"))
      (fun _ dims => .ok dims) capacity len = .ok [JInt.wrap .i64 len]

theorem wrapMemoryIntegerSpec_refuted : ¬ WrapMemoryIntegerSpec := by
  intro h
  have bad := h false 2 3 (by decide) (by decide)
  change Except.error (Error.method "_wrap") = Except.ok [JInt.wrap .i64 2] at bad
  cases bad

/-- Observable result of wrapping memory: the original reference and dimensions. -/
abbrev Wrapped (α : Type) := (List (Option α) × I) × List I

def wrapContract (operation : List Int → Except Error (Wrapped α))
    (memory : List (Option α)) (offset : I) : Prop :=
  (∀ dims, (∀ d ∈ dims, IntTy.i64.min ≤ d ∧ d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, d < 0) →
    ∃ message, operation dims = .error (.argument message)) ∧
  (∀ dims, (∀ d ∈ dims, 0 ≤ d ∧ d < IntTy.i64.max) →
    dims.foldr (· * ·) 1 ≤ IntTy.i64.max →
    (dims.foldr (· * ·) 1 ≤ (memory.length : Int) + 1 - offset.val →
      operation dims = .ok ((memory, offset), dims.map (JInt.wrap .i64))) ∧
    ((memory.length : Int) + 1 - offset.val < dims.foldr (· * ·) 1 →
      ∃ message, operation dims = .error (.dimensionMismatch message))) ∧
  (∀ dims, (∃ d ∈ dims, d < IntTy.i64.min ∨ IntTy.i64.max < d) →
    operation dims = .error .inexact)

/-- The complete old wrap contract, for tuple dimensions, scalar dimensions,
MemoryRef and Memory, including aliasing and conversion errors.
The singleton law is the external Core.checked_dims method in boot.jl:813. -/
def WrapDocumented : Prop :=
  ∀ (checkedDims : List I → Except Error I),
    (∀ d, checkedDims [d] = .ok d) →
    ∀ (α : Type) (memory : List (Option α)) (offset : I),
      memory.length < 2 ^ 63 → 1 ≤ offset.val → offset.val ≤ (memory.length : Int) + 1 →
      let toInt := fun n : Int => (JInt.convert (IntTy.i64.name) .i64 n).mapError (fun _ => Error.inexact)
      let check := wrapCheck Prod.fst (fun mem : List (Option α) => JInt.wrap .i64 mem.length)
        Prod.snd checkedDims
      let newArray := fun ref dims => Except.ok (ref, dims)
      wrapContract
        (wrapRefDims (fun ds => ds.mapM toInt) check newArray (memory, offset)) memory offset ∧
      wrapContract
        (wrapMemoryDims (fun ds => ds.mapM toInt) (fun mem => .ok (mem, one))
          check newArray memory) memory one ∧
      wrapContract
        (fun ds => match ds with
          | [l] => wrapRefLength toInt check newArray (memory, offset) l
          | _ => .error (.method "wrap")) memory offset ∧
      wrapContract
        (fun ds => match ds with
          | [l] => wrapMemoryLength toInt (fun mem => .ok (mem, one))
              (fun ref ds => check ref (ds.map (JInt.wrap .i64))) newArray memory l
          | _ => .error (.method "wrap")) memory one ∧
      wrapMemory (fun mem => Except.ok (mem, one))
        (fun mem => JInt.wrap .i64 mem.length) newArray memory =
          .ok ((memory, one), [JInt.wrap .i64 memory.length])

theorem wrapDocumented_refuted : ¬ WrapDocumented := by
  intro h
  let check : List I → Except Error I := fun ds =>
    .ok (ds.foldr (· * ·) one)
  have single : ∀ d, check [d] = .ok d := by
    intro d
    dsimp [check]
    congr 1
    apply Subtype.ext
    change wrapInt .i64 (d.val * one.val) = d.val
    rw [show one.val = 1 from rfl, Int.mul_one]
    exact wrapInt_of_inRange .i64 d.val d.property
  have hc := h check single Unit [none, none, none] one (by decide) (by decide) (by decide)
  obtain ⟨message, bad⟩ := hc.2.2.1.1 [-1]
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        subst d; decide)
    ⟨-1, by simp, by decide⟩
  have actual :
      wrapRefLength (m := Except Error)
        (fun n : Int => (JInt.convert (IntTy.i64.name) .i64 n).mapError (fun _ => Error.inexact))
        (wrapCheck Prod.fst (fun mem : List (Option Unit) => JInt.wrap .i64 mem.length)
          Prod.snd check)
        (fun ref dims => .ok (ref, dims))
        ([none, none, none], one) (-1) =
        .ok (([none, none, none], one), [JInt.wrap .i64 (-1)]) := by rfl
  change (wrapRefLength (m := Except Error) _ _ _ _ (-1) : Except Error (Wrapped Unit)) =
    Except.error (.argument message) at bad
  rw [actual] at bad
  cases bad

theorem iterator_upper_runtime_nonboolean (α : Type) (value : α) (tail : List α) :
    iteratorUpperBound (m := Except Error) (listIterator (value :: tail)) (.ok ())
      (fun _ => .error (.typeError "if")) = .error (.typeError "if") := by
  rw [iteratorUpperBound]
  change iteratorUpperBound.loop (m := Except Error) (listIterator (value :: tail)) (Except.ok ())
    (fun _ => Except.error (.typeError "if")) value tail = _
  rw [iteratorUpperBound.loop.eq_1]
  rfl

def EmptyLiteralSpec : Prop := ∀ (α : Type) (old : List (Option α)),
  (vectEmpty (literalAllocate (α := α))).run old = ((), []) ∧
  (anyLiteralEmpty (literalAllocate (α := α))).run old = ((), [])

def DimensionSuffixSpec : Prop :=
  ∀ (Z : Type) (value : Z → Int) (toInt : Z → Except Error I)
    (size : List I → I → Except Error I),
    (∀ n, toInt n = (JInt.convert (IntTy.i64.name) .i64 (value n)).mapError (fun _ => Error.inexact)) →
    (∀ dims i, size dims i =
      if 1 ≤ i.val then .ok (dims[(i.val - 1).toNat]?.getD one) else .error .bounds) →
    ∀ (dims : List I) (n : Z), dims.length < 2 ^ 63 →
      (1 ≤ value n →
        asizeFrom value toInt (fun dims => JInt.wrap .i64 dims.length) size dims n =
          .ok (dims.drop (value n - 1).toNat)) ∧
      (IntTy.i64.min ≤ value n → value n ≤ 0 →
        asizeFrom value toInt (fun dims => JInt.wrap .i64 dims.length) size dims n =
          .error .bounds) ∧
      (value n < IntTy.i64.min →
        asizeFrom value toInt (fun dims => JInt.wrap .i64 dims.length) size dims n =
          .error .inexact)

def ArrayStorageSizeSpec : Prop :=
  ∀ (aligned : StoredType → I)
    (_hbits : ∀ d : Layout, d.WF → d.isbits = true → d.size < 2 ^ 63 →
      (aligned (.dt d)).val = (d.size : Int))
    (_hboxed : ∀ t, allocatedinline storedInline t = false → aligned t = JInt.wrap .i64 8),
    (∀ (d : Layout) (n : I), d.WF → d.isbits = true → d.size < 2 ^ 63 → 0 ≤ n.val →
      n.val * (d.size : Int) ≤ IntTy.i64.max →
      (elsizeArray aligned (.dt d)).val = (d.size : Int) ∧
      (sizeofArray id (fun _ => elsizeArray aligned (.dt d)) n).val =
        n.val * (d.size : Int)) ∧
    (∀ t, allocatedinline storedInline t = false → (elsizeArray aligned t).val = 8) ∧
    elsizeBottom.val = 0 ∧
    ∀ (α : Type) (args : List α), elsizeBottomArgs (m := Except Error) args =
      .error (.method "elsize")

theorem arrayStorageSizeSpec : ArrayStorageSizeSpec := by
  intro aligned hbits hboxed
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro d n hw hb hd hn hmax
    have hs := hbits d hw hb hd
    refine ⟨hs, ?_⟩
    change wrapInt .i64 (n.val * (aligned (.dt d)).val) = _
    rw [hs]
    apply wrapInt_of_inRange
    constructor
    · have hm : 0 ≤ n.val * (d.size : Int) := Int.mul_nonneg hn (Int.natCast_nonneg _)
      have : IntTy.i64.min ≤ 0 := by decide
      omega
    · exact hmax
  · intro t ht
    change (aligned t).val = 8
    rw [hboxed t ht]
    rfl
  · intro α args
    rfl

def PointerStrideSpec : Prop :=
  ∀ (align : I → I → I)
    (_halign : ∀ d : Layout, d.WF → d.size < 2 ^ 63 → d.align < 2 ^ 63 →
      align (JInt.wrap .i64 d.size) (JInt.wrap .i64 d.align) = JInt.wrap .i64 d.size)
    (d : Layout) (_hw : d.WF) (_hsize : d.size < 2 ^ 63) (_hal : d.align < 2 ^ 63) (e : Error),
  let isAny : StoredType → Bool := fun t => match t with | .any => true | _ => false
  let isDT : StoredType → Bool := fun t => match t with | .dt _ | .abstractDT _ => true | _ => false
  let coreSize : StoredType → Except Error I := fun t =>
    match t with | .dt t => .ok (JInt.wrap .i64 t.size) | _ => .error e
  let alignment : StoredType → Except Error I := fun t =>
    match t with | .dt t => .ok (JInt.wrap .i64 t.align) | _ => .error e
  (elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8) coreSize alignment align (.dt d) =
    .ok (JInt.wrap .i64 d.size)) ∧
  (elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8) coreSize alignment align .any =
    .ok (JInt.wrap .i64 8)) ∧
  (elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8) coreSize alignment align .bottom =
    .error e) ∧
  (∀ members, elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8)
    coreSize alignment align (.union members) = .error e) ∧
  (∀ name, elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8)
    coreSize alignment align (.abstractDT name) = .error e)

theorem pointerStrideSpec : PointerStrideSpec := by
  intro align halign d hw hsize hal e isAny isDT coreSize alignment
  simp [elsizePtr, isAny, isDT, coreSize, alignment, halign d hw hsize hal,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

def PromotedLiteralContents : Prop := ∀ (α β T : Type)
    (promote : List β → T) (convert : T → β → Except Error α)
    (homogeneous : Bool) (xs : List β) (old : List (Option α)),
  xs.length < 2 ^ 63 →
  (vectPromoted (fun vals => pure (promote vals)) (fun t vals =>
    typedLiteral (fun n => liftLiteralState (literalAllocateAs t n))
      (convertedLiteralSetter (convert t)) homogeneous vals) xs).run old =
    (xs.mapM (convert (promote xs))).map (fun ys => (promote xs, ys.map some))

theorem promotedLiteralContents : PromotedLiteralContents := by
  intro α β T promote convert homogeneous xs old hn
  have hp : (pure (promote xs) : StateT (List (Option α)) (Except Error) T).run old =
      .ok (promote xs, old) := rfl
  rw [vectPromoted, StateT.run_bind, hp, except_ok_bind]
  exact convertedLiteralContents α β T (promote xs) (convert (promote xs))
    homogeneous xs old hn

def StorageSizesSpec : Prop := ArrayStorageSizeSpec ∧ PointerStrideSpec

def FreshArray {B α : Type} (shape : B → List I) (slots : B → List (Option α))
    (dims : List I) (a : B) : Prop :=
  shape a = dims ∧ slots a = List.replicate ((dims.map (fun d : I => d.val)).prod.toNat) none

def SimilarShapeSpec : Prop :=
  ∀ (α A B : Type) (shape : B → List I) (slots : B → List (Option α))
    (allocate : List I → Except Error B),
    (∀ dims, (∀ d ∈ dims, 0 ≤ d.val) → (dims.map (fun d => d.val)).prod ≤ IntTy.i64.max →
      ∃ b, allocate dims = .ok b ∧ FreshArray shape slots dims b) →
    (∀ dims, (∃ d ∈ dims, d.val < 0) →
      ∃ message, allocate dims = .error (.argument message)) →
    ∀ (size : A → I → Except Error I) (a : A) (n m : I) (dims : List I),
    size a one = .ok n → size a (JInt.wrap .i64 2) = .ok m →
    (0 ≤ n.val → ∀ result ∈
        [similar414 size (fun n => allocate [n]) a,
         similar416 size (fun n => allocate [n]) a,
         similar418 (fun n => allocate [n]) a n],
      ∃ b, result = .ok b ∧ FreshArray shape slots [n] b) ∧
    (0 ≤ n.val → 0 ≤ m.val → n.val * m.val ≤ IntTy.i64.max →
      ∀ result ∈ [similar415 size (fun n m => allocate [n, m]) a,
        similar417 size (fun n m => allocate [n, m]) a],
      ∃ b, result = .ok b ∧ FreshArray shape slots [n, m] b) ∧
    ((∀ d ∈ dims, 0 ≤ d.val) → (dims.map (fun d => d.val)).prod ≤ IntTy.i64.max →
      ∀ result ∈ [similar419 allocate a dims, similar420 allocate a dims,
        similar421 (similar420 allocate a) dims],
      ∃ b, result = .ok b ∧ FreshArray shape slots dims b) ∧
    ((∃ d ∈ dims, d.val < 0) →
      ∀ result ∈ [similar419 allocate a dims, similar420 allocate a dims,
        similar421 (similar420 allocate a) dims],
      ∃ message, result = .error (.argument message)) ∧
    (n.val < 0 → ∃ message, similar418 (fun n => allocate [n]) a n = .error (.argument message))

def MixedConstantArraySpec : Prop :=
  ∀ (α T Z : Type) (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)),
    TaggedAllocationShapeLaw value allocate →
    ∀ (element : T → Except Error α) (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (t : T) (dims : List (Sum Z Z)) (old : I → Option α),
    let typed := fun t dims => constant637 (allocate t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims
    ∀ action ∈ [constantMixedDims dimensionArgument typed t dims,
      constantTypedVarargs (constantMixedDims dimensionArgument typed) t dims,
      constantDefaultType t (constantMixedDims dimensionArgument typed) dims,
      constantVarargs (constantDefaultType t (constantMixedDims dimensionArgument typed)) dims],
      action.run old =
        constantArrayResult value t (dims.map (fun d => d.elim id id))
          ((allocate t (dims.map (fun d => d.elim id id))).run old) (element t)

theorem mixedConstantArraySpec : MixedConstantArraySpec := by
  intro α T Z value allocate halloc element indices hindices t dims old typed action hop
  have hmap : dims.map dimensionArgument = dims.map (fun d => d.elim id id) := by
    apply List.map_congr_left
    intro d _
    cases d <;> rfl
  have hc := constantArraySpec α T Z value allocate halloc element indices hindices t
    (dims.map (fun d => d.elim id id)) old
    (typed t (dims.map (fun d => d.elim id id))) (by simp [typed])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;>
    simpa only [constantMixedDims, constantTypedVarargs, constantDefaultType, constantVarargs,
      hmap] using hc

def CompleteConstantArraySpec : Prop :=
  ConstantArraySpec ∧ MixedConstantArraySpec ∧ UnsupportedConstantAxesSpec ∧
    DocumentedConstantDimensionsSpec

theorem heapAllocateArray_inexact_run (layout : Tag → Option MemoryLayout) (target : Tag)
    (dims : List Nat) (heap : VectorHeap α)
    (hd : heapDimensionsFit dims = false) :
    (heapAllocateArray layout target dims).run heap = .error .inexact := by
  simp only [heapAllocateArray, hd, Bool.not_false, ite_true,
    vector_bind_run, vector_throw_run]

def heapArrayDimensionError (dims : List Nat) : Error :=
  if heapDimensionsFit dims then .argument "invalid Array dimensions" else .inexact

def normalizedHeapAxes (axes : List (Int × Nat)) : List (Int × Nat) :=
  axes.map (fun p => (if p.2 = 0 then 1 else p.1, p.2))

def HeapAxesLaw (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (message : String) : Prop :=
  ∀ heap dest src, (check dest src).run heap =
    if normalizedHeapAxes dest = normalizedHeapAxes src then .ok (true, heap)
    else .error (.dimensionMismatch message)

theorem heapArrayCopy_run (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : HeapArray Tag) (xs ys : List (Option α))
    (hsrc : heap[src.handle]? = some xs) (hdest : heap[dest.handle]? = some ys)
    (hlen : ys.length = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapArrayCopy convert dest src).run heap =
      if xs = [] then .ok (dest, heap)
      else (xs.mapM convert).map (fun values => (dest, heap.set dest.handle values)) := by
  simp only [heapArrayCopy, vector_bind_run,
    heapWholeCopy_run convert heap dest.handle src.handle xs ys hsrc hdest hlen hn]
  by_cases hz : xs = []
  · simp only [hz, ite_true, vector_pure_run]
  · simp only [hz, ite_false]
    cases hc : xs.mapM convert <;> rfl

def HeapArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String),
    HeapAxesLaw check message →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (heapArrayConstructor layout target check convert src).run heap =
      if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message)

def HeapAbstractArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String),
    HeapAxesLaw check message →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (abstractArrayConstructor
      (fun a => similar419 (heapAllocateArray layout target) a a.dimensions)
      (heapArrayAxesCopy check convert) src).run heap =
      if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message)

def HeapArrayConvertSpec : Prop :=
  ∀ (Tag α : Type) [DecidableEq Tag] (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String),
    HeapAxesLaw check message →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let result := (convertArray (fun a => a.elementType == target) id
      (heapArrayConstructor layout target check convert) pure src).run heap
    (src.elementType = target → result = .ok (src, heap)) ∧
    (src.elementType ≠ target →
      result = if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message))

structure ForeignHeapArray (Tag : Type) where
  view : HeapArray Tag

def HeapGenericCopyLaw {Tag α : Type}
    (convert : Option α → Except Error (Option α))
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag)) : Prop :=
  ∀ heap dest src xs ys, heap[src.view.handle]? = some xs → heap[dest.handle]? = some ys →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    normalizedHeapAxes dest.axes = normalizedHeapAxes src.view.axes →
    (copy dest src).run heap =
      (xs.mapM convert).map (fun values => (dest, heap.set dest.handle values))

def ForeignHeapArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag))
    (cast : ForeignHeapArray Tag → HeapArray Tag) (message : String),
    HeapAxesLaw check message → HeapGenericCopyLaw convert copy →
    ∀ (heap : VectorHeap α) (src : ForeignHeapArray Tag) (xs : List (Option α)),
    heap[src.view.handle]? = some xs → src.view.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.view.dimensions = true →
    let constructor := arrayConstructor (fun s : ForeignHeapArray Tag => pure s.view.dimensions)
      (heapAllocateArray layout target) (JuliaLean.base.abstractarray.copytoAxesCheck
        (fun a : HeapArray Tag => pure a.axes) (fun s : ForeignHeapArray Tag => pure s.view.axes) check copy)
    ∀ operation ∈ [constructor, convertArray (fun _ => false) cast constructor pure],
      (operation src).run heap =
        if normalizedHeapAxes (src.view.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.view.axes then
          (xs.mapM convert).map (fun values =>
            (HeapArray.mk heap.length target src.view.dimensions
              (src.view.dimensions.map (fun n => (1, n))), heap ++ [values]))
        else .error (.dimensionMismatch message)

def ForeignHeapAbstractConstructorSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag))
    (similar : ForeignHeapArray Tag → VectorM α (HeapArray Tag)) (message : String),
    HeapAxesLaw check message → HeapGenericCopyLaw convert copy →
    (∀ heap src dest next, (similar src).run heap = .ok (dest, next) →
      dest.handle = heap.length ∧ dest.elementType = target ∧
      dest.dimensions = src.view.dimensions ∧
      next = heap ++ [List.replicate src.view.dimensions.prod none]) →
    ∀ (heap : VectorHeap α) (src : ForeignHeapArray Tag) (xs : List (Option α)),
    heap[src.view.handle]? = some xs → src.view.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    (abstractArrayConstructor similar (JuliaLean.base.abstractarray.copytoAxesCheck
      (fun a : HeapArray Tag => pure a.axes) (fun s : ForeignHeapArray Tag => pure s.view.axes) check copy)
      src).run heap =
      match (similar src).run heap with
      | .error e => .error e
      | .ok (dest, _) =>
        if normalizedHeapAxes dest.axes = normalizedHeapAxes src.view.axes then
          (xs.mapM convert).map (fun values => (dest, heap ++ [values]))
        else .error (.dimensionMismatch message)

theorem foreignHeapAbstractConstructorSpec : ForeignHeapAbstractConstructorSpec := by
  intro Tag α target check convert copy similar message hcheck hcopy hsimilar heap src xs hs hl hn
  have hsl : src.view.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  simp only [abstractArrayConstructor, vector_bind_run]
  cases ha : (similar src).run heap with
  | error e => rfl
  | ok pair =>
    obtain ⟨dest, next⟩ := pair
    obtain ⟨hd, ht, hdim, hnext⟩ := hsimilar heap src dest next ha
    have hsrc : next[src.view.handle]? = some xs := by
      simpa only [hnext, List.getElem?_append_left hsl] using hs
    have hdest : next[dest.handle]? = some (List.replicate src.view.dimensions.prod none) := by
      simp [hnext, hd]
    simp only [JuliaLean.base.abstractarray.copytoAxesCheck, vector_bind_run, vector_pure_run]
    rw [hcheck next dest.axes src.view.axes]
    by_cases hax : normalizedHeapAxes dest.axes = normalizedHeapAxes src.view.axes
    · simp only [hax, ite_true]
      rw [hcopy next dest src xs (List.replicate src.view.dimensions.prod none)
        hsrc hdest (by simp [hl]) hn hax]
      cases hc : xs.mapM convert <;> simp [hnext, hd, List.set_append_right]
    · simp only [hax, ite_false]

def HeapNativeDimensionErrorsSpec : Prop :=
  ∀ (Tag α : Type) [DecidableEq Tag] (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (heap : VectorHeap α) (src : HeapArray Tag),
    (heapDimensionsFit src.dimensions = false ∨ 2 ^ 63 ≤ src.dimensions.prod) →
    ((heapArrayConstructor layout target check convert src).run heap =
      .error (heapArrayDimensionError src.dimensions)) ∧
    ((abstractArrayConstructor
      (fun a => similar419 (heapAllocateArray layout target) a a.dimensions)
      (heapArrayAxesCopy check convert) src).run heap =
      .error (heapArrayDimensionError src.dimensions)) ∧
    ((convertArray (fun a => a.elementType == target) id
      (heapArrayConstructor layout target check convert) pure src).run heap =
      if src.elementType = target then .ok (src, heap)
      else .error (heapArrayDimensionError src.dimensions))

def HeapForeignDimensionErrorsSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag))
    (cast : ForeignHeapArray Tag → HeapArray Tag)
    (heap : VectorHeap α) (src : ForeignHeapArray Tag),
    (heapDimensionsFit src.view.dimensions = false ∨ 2 ^ 63 ≤ src.view.dimensions.prod) →
    let constructor := arrayConstructor (fun s : ForeignHeapArray Tag => pure s.view.dimensions)
      (heapAllocateArray layout target) (JuliaLean.base.abstractarray.copytoAxesCheck
        (fun a : HeapArray Tag => pure a.axes) (fun s : ForeignHeapArray Tag => pure s.view.axes) check copy)
    ∀ operation ∈ [constructor, convertArray (fun _ => false) cast constructor pure],
      (operation src).run heap = .error (heapArrayDimensionError src.view.dimensions)

def TypedHeapConstructionSpec : Prop :=
  ∀ (Tag α β : Type) [DecidableEq Tag] (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM (Sum α β) Bool)
    (convert : β → Except Error α)
    (slotConvert : Option (Sum α β) → Except Error (Option (Sum α β)))
    (message : String),
    HeapAxesLaw check message →
    (∀ x, slotConvert (some (.inr x)) = (convert x).map (fun y => some (.inl y))) →
    ∀ (heap : VectorHeap (Sum α β)) (src : HeapArray Tag) (xs : List β),
    heap[src.handle]? = some (xs.map (fun x => some (.inr x))) →
    src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let expected := if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
      (xs.mapM convert).map (fun values =>
        (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
          heap ++ [values.map (fun y => some (.inl y))]))
      else .error (.dimensionMismatch message)
    (∀ operation ∈ [heapArrayConstructor layout target check slotConvert,
      abstractArrayConstructor
        (fun a => similar419 (heapAllocateArray layout target) a a.dimensions)
        (heapArrayAxesCopy check slotConvert)],
      (operation src).run heap = expected) ∧
    (src.elementType ≠ target →
      (convertArray (fun a => a.elementType == target) id
        (heapArrayConstructor layout target check slotConvert) pure src).run heap = expected)

def BitIntegerHeapConstructionSpec : Prop :=
  ∀ (T S : IntTy)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM (Sum (JInt T) (JInt S)) Bool)
    (slotConvert : Option (Sum (JInt T) (JInt S)) → Except Error (Option (Sum (JInt T) (JInt S))))
    (message : String),
    HeapAxesLaw check message →
    (∀ x, slotConvert (some (.inr x)) =
      ((JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)).map (fun y => some (.inl y))) →
    ∀ (heap : VectorHeap (Sum (JInt T) (JInt S))) (src : HeapArray IntTy) (xs : List (JInt S)),
    heap[src.handle]? = some (xs.map (fun x => some (.inr x))) →
    src.elementType = S → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes →
    let intLayout := fun t : IntTy => some (MemoryLayout.mk (t.bits / 8) false false)
    let operations := [heapArrayConstructor intLayout T check slotConvert,
      abstractArrayConstructor (fun a => similar419 (heapAllocateArray intLayout T) a a.dimensions)
        (heapArrayAxesCopy check slotConvert)]
    (∀ operation ∈ operations,
      (∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max) →
      (operation src).run heap =
        .ok (⟨heap.length, T, src.dimensions, src.dimensions.map (fun n => (1, n))⟩,
          heap ++ [xs.map (fun x => some (.inl (JInt.wrap T x.val)))])) ∧
    (∀ operation ∈ operations,
      (∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max)) →
      (operation src).run heap = .error .inexact)

def CompleteHeapArrayConstructorSpec : Prop :=
  HeapArrayConstructorSpec ∧ ForeignHeapArrayConstructorSpec ∧
    HeapNativeDimensionErrorsSpec ∧ HeapForeignDimensionErrorsSpec ∧
    TypedHeapConstructionSpec ∧ BitIntegerHeapConstructionSpec
def CompleteHeapArrayConvertSpec : Prop :=
  HeapArrayConvertSpec ∧ ForeignHeapArrayConstructorSpec ∧
    HeapNativeDimensionErrorsSpec ∧ HeapForeignDimensionErrorsSpec ∧
    TypedHeapConstructionSpec ∧ BitIntegerHeapConstructionSpec
def CompleteHeapAbstractConstructorSpec : Prop :=
  HeapAbstractArrayConstructorSpec ∧ ForeignHeapAbstractConstructorSpec ∧
    HeapNativeDimensionErrorsSpec ∧ TypedHeapConstructionSpec ∧ BitIntegerHeapConstructionSpec

theorem mutableOverallocation_run {layout : MemoryLayoutMetadata} (n : I) :
    ∃ capacity : I, ∀ s : MutableMemory α,
      ((mutableStorage layout).overallocation n).run s = (.ok capacity, s) := by
  simp only [mutableStorage, overallocation, stateExcept_bind, stateExcept_pure]
  exact ⟨_, fun _ => rfl⟩

theorem mutableDivideFour_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x : I) :
    ((mutableStorage layout).divide x (JInt.wrap .i64 4)).run s =
      (.ok (JInt.wrap .i64 (x.val.tdiv 4)), s) := rfl

theorem memoryWrites_prefix_run (values : List (Option α)) (s : MutableMemory α)
    (mem : Nat) (written suffix : List (Option α))
    (hm : s.memories[mem]? = some (written ++ suffix))
    (hfit : values.length ≤ suffix.length)
    (hcapacity : written.length + suffix.length < 2 ^ 63) :
    (forIn (values.zipIdx written.length) () (fun (pair : Option α × Nat) _ => do
      memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1
      pure (ForInStep.yield ()))).run s =
      (.ok (), {s with memories := s.memories.set mem (written ++ values ++ suffix.drop values.length)}) := by
  induction values generalizing s written suffix with
  | nil =>
    have hself : s.memories.set mem (written ++ suffix) = s.memories := by
      obtain ⟨h, hv⟩ := List.getElem?_eq_some_iff.mp hm
      rw [← hv]
      exact List.set_getElem_self h
    simp only [List.zipIdx_nil, List.forIn_nil, stateExcept_pure,
      List.append_nil, List.length_nil, List.drop_zero, hself]
  | cons x xs ih =>
    cases suffix with
    | nil => simp only [List.length_nil, List.length_cons] at hfit; omega
    | cons y ys =>
      have hp : written.length < 2 ^ 63 := by simp only [List.length_cons] at hcapacity; omega
      have hk : wrapInt .i64 (written.length : Int) = written.length := by
        apply wrapInt_of_inRange
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
        omega
      have haddr : (one + JInt.wrap .i64 (written.length : Int)).val = written.length + 1 := by
        change wrapInt .i64 (1 + wrapInt .i64 (written.length : Int)) = _
        rw [hk]
        have hh : wrapInt .i64 (1 + (written.length : Int)) = 1 + written.length := by
          apply wrapInt_of_inRange
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
          simp only [List.length_cons] at hcapacity
          omega
        rw [hh]
        omega
      have hb : 1 ≤ (one + JInt.wrap .i64 (written.length : Int)).val ∧
          (one + JInt.wrap .i64 (written.length : Int)).val ≤
            ((written ++ y :: ys).length : Int) := by
        rw [haddr]
        simp only [List.length_append, List.length_cons]
        omega
      have hset : (written ++ y :: ys).set
          ((one + JInt.wrap .i64 (written.length : Int)).val - 1).toNat x =
          (written ++ [x]) ++ ys := by
        rw [haddr]
        simp
      let mid : MutableMemory α :=
        {s with memories := s.memories.set mem ((written ++ [x]) ++ ys)}
      have hmLt := (List.getElem?_eq_some_iff.mp hm).choose
      have hmid : mid.memories[mem]? = some ((written ++ [x]) ++ ys) :=
        List.getElem?_set_self hmLt
      have hrest := ih mid (written ++ [x]) ys hmid (by simpa using hfit)
        (by simp only [List.length_append, List.length_cons,
          List.length_nil] at *; omega)
      simp only [List.zipIdx_cons, List.forIn_cons, stateExcept_bind,
        memoryWrite_run s mem (written ++ y :: ys) hm _ hb, hset, stateExcept_pure]
      have hindex : written.length + 1 = (written ++ [x]).length := by simp
      rw [hindex]
      change (forIn (xs.zipIdx (written ++ [x]).length) ()
        (fun (pair : Option α × Nat) _ => do
          memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1
          pure (ForInStep.yield ())) : MutationM α Unit).run mid = _
      rw [hrest]
      simp [mid, List.append_assoc]

theorem memoryMove_prefix_run (s : MutableMemory α) (dest src : Nat)
    (destination source : List (Option α))
    (hd : s.memories[dest]? = some destination) (hs : s.memories[src]? = some source)
    (n : I) (hn : 0 ≤ n.val)
    (hnd : n.val ≤ (destination.length : Int)) (hns : n.val ≤ (source.length : Int))
    (hcap : destination.length < 2 ^ 63) :
    (memoryMove dest one src one n).run s =
      (.ok (), {s with memories := (s.memories.set dest
        (source.take n.val.toNat ++ destination.drop n.val.toNat))}) := by
  have htake : (source.take n.val.toNat).length = n.val.toNat := by
    rw [List.length_take]
    omega
  have hw := memoryWrites_prefix_run (source.take n.val.toNat) s dest [] destination
    (by simpa using hd) (by rw [htake]; omega) (by simpa using hcap)
  simp only [List.length_nil, List.nil_append, htake] at hw
  simp only [memoryMove, stateExcept_bind, memoryRead_run s src source hs,
    memoryRead_run s dest destination hd, show one.val = 1 from rfl, Int.sub_self,
    Int.zero_add, hn, hnd, hns, Int.le_refl, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, Int.toNat_zero, List.drop_zero]
  simp only [hw, stateExcept_pure]

@[simp] theorem jint_i64_sub_zero (x : I) : x - zero = x := by
  apply Subtype.ext
  change wrapInt .i64 (x.val - 0) = x.val
  rw [Int.sub_zero]
  exact wrapInt_of_inRange .i64 x.val x.property

@[simp] theorem jint_i64_zero_add (x : I) : zero + x = x := by
  apply Subtype.ext
  change wrapInt .i64 (0 + x.val) = x.val
  rw [Int.zero_add]
  exact wrapInt_of_inRange .i64 x.val x.property

@[simp] theorem jint_i64_sub_self (x : I) : x - x = zero := by
  apply Subtype.ext
  change wrapInt .i64 (x.val - x.val) = 0
  rw [Int.sub_self]
  rfl

def CollectorState (s : MutableMemory α) (handle : Nat) (n : I) : Prop :=
  ∃ (mem : Nat) (slots : List (Option α)),
    s.arrays[handle]? = some ⟨(mem, one), n⟩ ∧ s.memories[mem]? = some slots ∧
    0 ≤ n.val ∧ n.val ≤ (slots.length : Int) ∧ slots.length < 2 ^ 63

theorem collectorState_valid (s : MutableMemory α) (handle : Nat) (n : I)
    (h : CollectorState s handle n) : s.validVector handle := by
  obtain ⟨mem, slots, ha, hm, hn, hend, hcap⟩ := h
  simp only [MutableMemory.validVector, ha, hm, show one.val = 1 from rfl]
  exact ⟨hn, by decide, by omega, hcap⟩

def allocatedEmptyVector (s : MutableMemory α) : MutableMemory α := {
  memories := s.memories ++ [[]]
  arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩]}

theorem allocatedEmptyVector_state (s : MutableMemory α) :
    CollectorState (allocatedEmptyVector s) s.arrays.length zero ∧
      (allocatedEmptyVector s).contents s.arrays.length = [] := by
  have ha : (allocatedEmptyVector s).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), zero⟩ := by simp [allocatedEmptyVector]
  have hm : (allocatedEmptyVector s).memories[s.memories.length]? = some [] := by
    simp [allocatedEmptyVector]
  constructor
  · exact ⟨s.memories.length, [], ha, hm, by decide,
      by change (0 : Int) ≤ 0; decide, by change (0 : Nat) < 2 ^ 63; decide⟩
  · simp only [MutableMemory.contents, ha, hm, Option.getD_some, List.drop_nil, List.take_nil]

def SimilarAllocationLaw {C Tag α : Type}
    (similar : C → Tag → List I → VectorM α (HeapArray Tag)) : Prop :=
  ∀ c target dims heap, (∀ dim ∈ dims, 0 ≤ dim.val) →
    (dims.map (fun dim => dim.val.toNat)).prod < 2 ^ 63 →
    (similar c target dims).run heap =
      let shape := dims.map (fun dim => dim.val.toNat)
      .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
        heap ++ [List.replicate shape.prod none])


def UnknownSimilarInterfaceSpec : Prop :=
  ∀ (C Tag α X : Type)
    (similar : C → Tag → I → VectorM α (HeapArray Tag)),
    (∀ c target n heap, 0 ≤ n.val →
      (similar c target n).run heap =
        freshVectorAllocation target n.val.toNat heap) →
    ∀ (container : C) (target : Tag) (itr : X) (heap : VectorHeap α),
    (similarForUnknown similar container target itr).run heap =
      freshVectorAllocation target 0 heap

theorem unknownSimilarInterfaceSpec : UnknownSimilarInterfaceSpec := by
  intro C Tag α X similar hlaw container target itr heap
  have h := hlaw container target zero heap (by change (0 : Int) ≤ 0; omega)
  simpa only [similarForUnknown, show zero.val = 0 from rfl, Int.toNat_zero] using h

def UnknownSimilarNativeSpec : Prop :=
  ∀ (SourceTag Tag α X : Type) (layout : Tag → Option MemoryLayout) (container : HeapArray SourceTag)
    (target : Tag) (itr : X) (heap : VectorHeap α),
    (similarForUnknown
      (fun c t n => JuliaLean.base.abstractarray.similarTypeVarargs
        (fun c t dims => similar419 (heapAllocateIntDims (α := α) layout t) c dims)
        c t [n]) container target itr).run heap =
      .ok (⟨heap.length, target, [0], [(1, 0)]⟩, heap ++ [[]])

def CompleteUnknownSimilarSpec : Prop :=
  UnknownSimilarInterfaceSpec ∧ UnknownSimilarNativeSpec

theorem intDimensionShape_bound (dims : List I) (shape : List Nat)
    (h : intDimensionShape dims = .ok shape) : shape.prod < 2 ^ 63 := by
  cases hnegative : dims.any (fun dim => decide (dim.val < 0)) with
  | true =>
    simp only [intDimensionShape, hnegative, ite_true] at h
    cases h
  | false =>
    simp only [intDimensionShape, hnegative, Bool.false_eq_true, ite_false] at h
    by_cases hprod : (dims.map (fun dim => dim.val.toNat)).prod < 2 ^ 63
    · simp only [hprod, ite_true] at h
      rw [← Except.ok.inj h]
      exact hprod
    · simp only [hprod, ite_false] at h
      cases h

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

def SimilarIteratorAllocatorsSpec : Prop :=
  (∀ (C Tag α X Z : Type) (layout : Tag → Option MemoryLayout) (value : Z → Int) (toInt : Z → Except Error I),
    CollectorIntLaw value toInt → ∀ (c : C) (target : Tag) (itr : X) n (heap : VectorHeap α),
    (similarForLength (nativeLengthSimilar layout toInt) c target itr n).run heap =
      if IntTy.i64.min ≤ value n ∧ value n ≤ IntTy.i64.max then
        if value n < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target (value n).toNat heap
      else .error .inexact) ∧
  (∀ (C Tag α X Axes : Type) (layout : Tag → Option MemoryLayout) (toShape : Axes → VectorM α (List I))
    (policy : Axes → Except Error (List I)),
    (∀ axs heap, (toShape axs).run heap = (policy axs).map (fun dims => (dims, heap))) →
    ∀ (c : C) (target : Tag) (itr : X) axs heap,
    (similarForAxes (nativeAxesSimilar layout toShape) c target itr axs).run heap =
      ((policy axs).bind intDimensionShape).bind
        (fun shape => freshShapeAllocation target shape heap)) ∧
  (∀ (C Tag α X Size Shape : Type) (size : C → List Nat)
    (similar : C → Tag → VectorM α (HeapArray Tag)),
    (∀ c target heap, (similar c target).run heap = freshShapeAllocation target (size c) heap) →
    ∀ c target (itr : X) (isz : Size) (shape : Shape) heap,
    (similarForGeneric similar c target itr isz shape).run heap =
      freshShapeAllocation target (size c) heap)
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
theorem VecAt.header {s : MutableMemory α} (h : VecAt s handle mem off n slots)
    (mem' : Nat) (off' n' : I) (slots' : List (Option α))
    (hm : (s.memories.set mem slots')[mem']? = some slots')
    (ho : 1 ≤ off'.val) (hn : 0 ≤ n'.val) (he : off'.val - 1 + n'.val ≤ (slots'.length : Int))
    (hc : slots'.length < 2 ^ 63) :
    VecAt { s with
      memories := s.memories.set mem slots'
      arrays := s.arrays.set handle ⟨(mem', off'), n'⟩ } handle mem' off' n' slots' := by
  have hlt := (List.getElem?_eq_some_iff.mp h.1).choose
  exact ⟨List.getElem?_set_self hlt, hm, ho, hn, he, hc⟩
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `reverse(v, start, stop)` (array.jl:2248; docstring at array.jl:2222-2247: "Return a copy of
`v` reversed from start to stop") on a fully assigned vector, with indices of any BitInteger
type: for `1 ≤ start ≤ stop + 1 ≤ length(v) + 1` it returns a fresh vector equal to `v` with
`v[start:stop]` reversed, leaving `v` unchanged. -/

def literalNtuple {α : Type} (f : I → I) (k : I) : StateT (List (Option α)) (Except Error) (List I) :=
  if k.val < 0 then throw (.argument ("tuple length should be ≥ 0, got " ++ toString k.val))
  else pure (List.map (fun j : Nat => f (JInt.wrap .i64 ((j : Int) + 1))) (List.range k.val.toNat))

/-- `reshape(v, dims)` (reshapedarray.jl) for the literal vector whose slots are the state: the
same elements under the dimensions `dims`, or `DimensionMismatch` when their product differs from
`length(v)`. -/

def literalReshape {α T : Type} (t : T) (dims : List I) :
    StateT (List (Option α)) (Except Error) (T × List Int) := do
  let slots ← get
  if (dims.map Subtype.val).prod = slots.length then pure (t, dims.map Subtype.val)
  else throw (.dimensionMismatch "new dimensions must be consistent with array size")
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

/-- Observable result of wrapping memory: the original reference and dimensions. -/
abbrev Wrapped (α : Type) := (List (Option α) × I) × List I

def wrapContract (operation : List Int → Except Error (Wrapped α))
    (memory : List (Option α)) (offset : I) : Prop :=
  (∀ dims, (∀ d ∈ dims, IntTy.i64.min ≤ d ∧ d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, d < 0) →
    ∃ message, operation dims = .error (.argument message)) ∧
  (∀ dims, (∀ d ∈ dims, 0 ≤ d ∧ d < IntTy.i64.max) →
    dims.foldr (· * ·) 1 ≤ IntTy.i64.max →
    (dims.foldr (· * ·) 1 ≤ (memory.length : Int) + 1 - offset.val →
      operation dims = .ok ((memory, offset), dims.map (JInt.wrap .i64))) ∧
    ((memory.length : Int) + 1 - offset.val < dims.foldr (· * ·) 1 →
      ∃ message, operation dims = .error (.dimensionMismatch message))) ∧
  (∀ dims, (∃ d ∈ dims, d < IntTy.i64.min ∨ IntTy.i64.max < d) →
    operation dims = .error .inexact)

def restoreIndexing : Expr Atom → Expr Atom
  | .atom x => .atom x
  | .node h args => .node h (args.map restoreIndexing)
  | .ref xs args => .ref (restoreIndexing xs) (args.map restoreIndexing)
  | .assign lhs rhs => .assign (restoreIndexing lhs) (restoreIndexing rhs)
  | .safeGet xs args => .ref (restoreIndexing xs) (args.map restoreIndexing)
  | .safeSet xs x args =>
      .assign (.ref (restoreIndexing xs) (args.map restoreIndexing)) (restoreIndexing x)
  | .escape x => .escape (restoreIndexing x)
termination_by e => sizeOf e

def literalAllocate (n : I) : LiteralM α Unit :=
  fun _ => ((), List.replicate n.val.toNat none)

def slotRef (_a : Unit) (i : I) : SlotM α I := fun slots => (.ok i, slots)

def slotRefNew (_a : Unit) (i : I) (_checked : Bool) : SlotM α I :=
  fun slots => (.ok i, slots)

def slotStore (i : I) (x : α) (_checked : Bool) : SlotM α Unit :=
  fun slots => (.ok (), updateSlot slots i (some x))

abbrev ByteMemory := Nat → JInt .u8

/-- Fresh array handles retain their type and dimensions while stores change only slots. -/
abbrev arrayShapeFiller {A α : Type} (shape : A → List Nat) (indices : List Nat → List I) :=
  fillBang (fun _ : α => true) id (fun x => (pure x : SlotM α α))
    (fillTyped (fun a => (pure (indices (shape a)) : SlotM α (List I)))
      (fun a x i => do
        let _ ← setindexScalar (fun _ : α => true) id (fun x => (pure x : SlotM α α))
          (setindexTyped (fun a i => slotBounds (shape a).prod () i)
            (fun _ i checked => slotRefNew () i checked) slotStore) a x i
        pure ()))

abbrev constructorFiller {α : Type} (indices : List Nat → List I) :=
  arrayShapeFiller (α := α) id indices

def heapArrayDimensionError (dims : List Nat) : Error :=
  if heapDimensionsFit dims then .argument "invalid Array dimensions" else .inexact

def heapArrayCopy {Tag α : Type} (convert : Option α → Except Error (Option α))
    (dest src : HeapArray Tag) : VectorM α (HeapArray Tag) := do
  let handle ← heapWholeCopy convert dest.handle src.handle
  pure { dest with handle := handle }

def heapArrayAxesCopy {Tag α : Type}
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) :=
  JuliaLean.base.abstractarray.copytoAxesCheck
    (fun a : HeapArray Tag => pure a.axes) (fun a : HeapArray Tag => pure a.axes)
    check (heapArrayCopy convert)

def heapArrayConstructor {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) :=
  arrayConstructor (fun a : HeapArray Tag => pure a.dimensions)
    (heapAllocateArray layout target) (heapArrayAxesCopy check convert)

def normalizedHeapAxes (axes : List (Int × Nat)) : List (Int × Nat) :=
  axes.map (fun p => (if p.2 = 0 then 1 else p.1, p.2))

/-- Non-Array implementations use the generic AbstractArray interfaces. -/
structure ForeignHeapArray (Tag : Type) where
  view : HeapArray Tag

def collectedShape {Tag α : Type} (target : Tag) (shape : List Nat)
    (values : List α) (heap : VectorHeap α) : HeapArray Tag × VectorHeap α :=
  (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
    heap ++ [values.map some])

def intDimensionShape (dims : List I) : Except Error (List Nat) :=
  if dims.any (fun dim => decide (dim.val < 0)) then
    .error (.argument "invalid Array dimensions")
  else
    let shape := dims.map (fun dim => dim.val.toNat)
    if shape.prod < 2 ^ 63 then .ok shape
    else .error (.argument "invalid Array dimensions")
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
section HeapRanges

/-- `vcat(arrays::Vector{T}...)` (array.jl:2346) with the native allocator for element type
`target` and the source `unsafe_copyto!`. -/
abbrev heapVcat {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag) (arrays : List (HeapArray Tag)) :
    VectorM α (HeapArray Tag) :=
  vcat (fun a => heapLength a.handle) (fun n => heapAllocateIntDims layout target [n])
    heapColonMemoryCopy arrays
end HeapRanges
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

/-- `pushfirst!(a, x)` (array.jl:1753-1770 docstring): the value is stored before every old
element. -/
def PushesAtFront (P : MutableMemory α → Prop) (handle : Nat)
    (pushfirst : Nat → α → MutationM α Unit) : Prop :=
  ∀ s x, P s → s.validVector handle → ∃ next, (pushfirst handle x).run s = (.ok (), next) ∧
    P next ∧ next.validVector handle ∧ next.contents handle = some x :: s.contents handle

/-- `reverse!(a, 1, n)` (array.jl:2291-2316 docstring) reverses the first `n` elements. -/
def ReversesPrefix (P : MutableMemory α → Prop) (handle : Nat)
    (reverse : Nat → I → I → MutationM α Unit) : Prop :=
  ∀ s (n : I), P s → s.validVector handle → 0 ≤ n.val →
    n.val ≤ ((s.contents handle).length : Int) →
    ∃ next, (reverse handle one n).run s = (.ok (), next) ∧ P next ∧ next.validVector handle ∧
      next.contents handle = ((s.contents handle).take n.val.toNat).reverse ++
        (s.contents handle).drop n.val.toNat

/-- An action that only changes capacity, as `sizehint!` (array.jl:1576-1610 docstring) does. -/
def KeepsContents (P : MutableMemory α → Prop) (handle : Nat) (act : MutationM α Unit) : Prop :=
  ∀ s, P s → s.validVector handle → ∃ next, act.run s = (.ok (), next) ∧ P next ∧
    next.validVector handle ∧ next.contents handle = s.contents handle
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

/-- `Set{T}()` for the tracked set. -/
def setEmpty : SetM α Unit := modify fun st => { st with set := [] }
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
/-- The value of `A[i]` for an `Int` index on a heap array with slots `xs`, or `none` when the read
raises. -/
def heapReadable (xs : List (Option α)) (i : I) : Option (Option α) :=
  if 1 ≤ i.val ∧ i.val ≤ (xs.length : Int) then xs[(i.val - 1).toNat]? else none

/-- `ntuple(f, k)` (ntuple.jl, no model): `(f(1), ..., f(k))`, and `ArgumentError` for `k < 0`. -/
def literalNtuple {α : Type} (f : I → I) (k : I) : StateT (List (Option α)) (Except Error) (List I) :=
  if k.val < 0 then throw (.argument ("tuple length should be ≥ 0, got " ++ toString k.val))
  else pure (List.map (fun j : Nat => f (JInt.wrap .i64 ((j : Int) + 1))) (List.range k.val.toNat))
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

/-- The `similar` methods for `Array` (array.jl:414-421, `similar` docstring in abstractarray.jl:
"Create an uninitialized mutable array with the given element type and size, based upon the given
source array.") on the shared heap, with `Vector{T}(undef, n)`, `Matrix{T}(undef, n, m)` and
`Array{T,N}(undef, dims)` the Core allocators of the store (`heapVectorAllocate`,
`heapAllocateIntDims`): each returns a fresh array of the requested element type (the source's
element type when none is given) and the requested dimensions (`size(a, 1)`, `size(a, 2)` by
default), with only unassigned slots, appended to the heap so that no existing array changes; a
negative dimension raises `ArgumentError`, as does a memory over Julia's size limit. -/
def SimilarShapeSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (heap : VectorHeap α) (a : HeapArray Tag)
    (S : Tag) (la lS : MemoryLayout) (m : I) (dims : List I),
    layout a.elementType = some la → layout S = some lS →
    heapDimensionsFit a.dimensions = true →
    let n1 : Int := (a.dimensions[0]?.getD 1 : Nat)
    let n2 : Int := (a.dimensions[1]?.getD 1 : Nat)
    let ints := dims.map (fun d => d.val)
    (a.dimensions.length = 1 →
      (similar414 heapSize (heapVectorAllocate layout a.elementType) a).run heap =
        allocOutcome la a.elementType [n1] heap ∧
      (similar416 heapSize (heapVectorAllocate layout S) a).run heap = allocOutcome lS S [n1] heap) ∧
    (a.dimensions.length = 2 →
      (similar415 heapSize (fun n m => heapAllocateIntDims layout a.elementType [n, m]) a).run heap =
        allocOutcome la a.elementType [n1, n2] heap ∧
      (similar417 heapSize (fun n m => heapAllocateIntDims layout S [n, m]) a).run heap =
        allocOutcome lS S [n1, n2] heap) ∧
    (similar418 (heapVectorAllocate layout a.elementType) a m).run heap =
      allocOutcome la a.elementType [m.val] heap ∧
    (similar419 (heapAllocateIntDims layout S) a dims).run heap = allocOutcome lS S ints heap ∧
    (similar420 (heapAllocateIntDims layout a.elementType) a dims).run heap =
      allocOutcome la a.elementType ints heap ∧
    (similar421 (fun dims => heapAllocateIntDims (α := α) layout S dims) dims).run heap =
      allocOutcome lS S ints heap

def IsBitsUnionDocumented : Prop :=
  (∀ ms : List Layout, 2 ≤ ms.length → (ms.map Layout.name).Nodup → (∀ d ∈ ms, d.WF) →
    (isbitsunion unionType storedInline (.union ms) = true ↔ ∀ d ∈ ms, d.isbits = true)) ∧
  isbitsunion unionType storedInline .bottom = true ∧
  (∀ d : Layout, isbitsunion unionType storedInline (.dt d) = false) ∧
  isbitsunion unionType storedInline .any = false ∧
  (∀ n, isbitsunion unionType storedInline (.abstractDT n) = false) ∧
  (∀ d : Layout, d.WF → d.isbits = true → allocatedinline storedInline (.dt d) = true) ∧
  allocatedinline storedInline .any = false ∧
  (∀ n, allocatedinline storedInline (.abstractDT n) = false)

/-- The one-based positions, as `Int` keys, of the elements of `xs` passing `test`. -/
def matchingKeys {α : Type} (test : α → Bool) (xs : List α) : List I :=
  ((xs.zipIdx 1).filter (fun p => test p.1)).map (fun p => JInt.wrap .i64 (p.2 : Int))

def DimensionSuffixSpec : Prop :=
  ∀ (Tag α : Type) (ops : BigIntegerOps) (heap : VectorHeap α) (a : HeapArray Tag)
    (n : IntegerValue),
    ops.Lawful → heapDimensionsFit a.dimensions = true → a.dimensions.length < 2 ^ 62 →
    1 ≤ n.val →
    (asizeFrom (m := VectorM α) IntegerValue.val
      (fun n => match n.toInt ops with
        | .ok k => pure k
        | .error e => throw e)
      (fun a : HeapArray Tag => JInt.wrap .i64 (a.dimensions.length : Int)) heapSize a n).run heap =
      .ok ((a.dimensions.drop (n.val - 1).toNat).map (fun (d : Nat) => JInt.wrap .i64 (d : Int)),
        heap)

/-- `_checkaxs(axes(dest), axes(src))` (abstractarray.jl) for heap-array axes, with range
equality: unit ranges are equal when both are empty or have the same first element and length. -/
def heapCheckAxes {α : Type} (d s : List (Int × Nat)) : VectorM α Bool :=
  runAHM (JuliaLean.base.abstractarray.checkAxes (m := AHM α)
    (fun d s => normalizedHeapAxes d == normalizedHeapAxes s)
    (fun ax => toString (ax.map Prod.snd)) d s)

/-- `copyto_axcheck!(dest, src)` (abstractarray.jl) between heap arrays, with the elementwise copy
`copyto!(dest::Array, src::Array)` of array.jl (each value through `convert`). -/
def heapAxcheckCopy {Tag α : Type} (convert : α → Except Error α) :
    HeapArray Tag → HeapArray Tag → VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.copytoAxesCheck
    (fun a : HeapArray Tag => pure a.axes) (fun a : HeapArray Tag => pure a.axes)
    heapCheckAxes
    (heapArrayCopy (fun o => match o with
      | some x => (convert x).map some
      | none => .ok none))

/-- The common hypotheses on a source heap array holding the values `xs`, with `OneTo` axes. -/
def HeapSource {Tag α : Type} (heap : VectorHeap α) (src : HeapArray Tag) (xs : List α) : Prop :=
  heap[src.handle]? = some (xs.map some) ∧ src.dimensions.prod = xs.length ∧
  xs.length < 2 ^ 62 ∧ heapDimensionsFit src.dimensions = true ∧
  src.axes = src.dimensions.map (fun n => (1, n))

/-- `Array{T,N}(x::AbstractArray{S,N})` (array.jl:664; `Array` constructor docstring in boot.jl
and the manual's "Construct an array of the given type from the elements of `x`") for a fully
assigned heap array `x`: `Array{T,N}(undef, size(x))` and `copyto_axcheck!` give a fresh array of
element type `T` and `x`'s dimensions holding `convert(T, x[i])` in order (any user conversion,
whose first error propagates). -/
def ArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag) (convert : α → Except Error α) (heap : VectorHeap α)
    (src : HeapArray Tag) (xs : List α),
    HeapSource heap src xs →
    (arrayConstructor (fun a : HeapArray Tag => pure a.dimensions) (heapAllocateArray layout target)
      (heapAxcheckCopy convert) src).run heap =
      (xs.mapM convert).map (fun values =>
        freshHeapArray target src.dimensions (values.map some) heap)

def AbstractArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (target : Tag) (convert : α → Except Error α) (heap : VectorHeap α)
    (src : HeapArray Tag) (xs : List α),
    HeapSource heap src xs →
    (abstractArrayConstructor (heapSimilarType layout target) (heapAxcheckCopy convert) src).run heap =
      (xs.mapM convert).map (fun values =>
        freshHeapArray target src.dimensions (values.map some) heap)

def ConvertArraySpec : Prop :=
  ∀ (Tag α : Type) [DecidableEq Tag] (layout : Tag → Option MemoryLayout) (target : Tag) (convert : α → Except Error α)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List α),
    HeapSource heap src xs →
    let result := (convertArray (fun a : HeapArray Tag => decide (a.elementType = target)) id
      (arrayConstructor (fun a : HeapArray Tag => pure a.dimensions) (heapAllocateArray layout target)
        (heapAxcheckCopy convert)) pure src).run heap
    (src.elementType = target → result = .ok (src, heap)) ∧
    (src.elementType ≠ target → result = (xs.mapM convert).map (fun values =>
      freshHeapArray target src.dimensions (values.map some) heap))

/-- `copyto_unaliased!(IndexStyle(dest), dest, IndexStyle(src), src)` (abstractarray.jl) between
heap arrays, both `IndexLinear`: `LinearIndices` are `1:length`, `checkbounds(Bool, inds, i)` on
them, and the element reads and writes are the Array `getindex`/`setindex!`. -/
def heapUnaliasedCopy {Tag α : Type} (dest src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  let linear := fun (a : HeapArray Tag) =>
    (pure (intRange one (JInt.wrap .i64 (a.dimensions.prod : Int))) : AHM α (List I))
  runAHM (JuliaLean.base.abstractarray.copytoUnaliased (m := AHM α)
    (fun s : HeapArray Tag => pure (s.dimensions.prod == 0))
    linear linear
    (fun inds : List I => pure (inds.headD one))
    (fun inds : List I => pure (inds.headD one)) (fun inds : List I => pure (inds.getLastD one))
    (fun a b => pure (a - b)) (fun a b => pure (a + b))
    (fun inds i => pure (decide (inds.headD one ≤ i ∧ i ≤ inds.getLastD zero)))
    (fun isLinear : Bool => isLinear)
    (fun s i => liftM (heapGet s.handle i)) (fun d i x => liftM (heapSet d.handle x i))
    (fun i => pure (i - one)) (fun i => pure (i + one)) (fun d i x => liftM (heapSet d.handle x i))
    linear linear (fun a b => a == b) (fun a b => pure (a.zip b))
    (fun s i => liftM (heapGet s.handle i)) (fun s i => liftM (heapGet s.handle i))
    (fun d i x => liftM (heapSet d.handle x i))
    true dest true src)

/-- `_collect_indices(axes(A), A)` (array.jl:788, 793) for a heap array, whose axes are `OneTo`s
(or none, for zero dimensions). -/
def heapCollectIndices {Tag α : Type} (layout : Tag → Option MemoryLayout) (axes : List (Int × Nat)) (src : HeapArray Tag) :
    VectorM α (HeapArray Tag) :=
  if axes = [] then
    collectIndicesZero (fun a : HeapArray Tag => heapAllocateArray layout a.elementType []) collectHeapEmpty
      (fun _ => true) (fun _ => true) (fun _ d _ s => heapUnaliasedCopy d s) src
  else
    collectIndicesOneTo (fun ax : Int × Nat => JInt.wrap .i64 (ax.2 : Int))
      (fun a dims => heapAllocateIntDims layout a.elementType dims) collectHeapEmpty
      (fun _ => true) (fun _ => true) (fun _ d _ s => heapUnaliasedCopy d s) axes src

/-- `collect(A::AbstractArray)` (array.jl:773; `collect` docstring at array.jl:723-770: "Return an
`Array` of all items in a collection or iterator ... the result has the same shape and number of
dimensions as `collection`") for a heap array of any number of dimensions: a fresh array of the
same element type and dimensions holding the same values in order, appended to the heap so no
existing array changes; an unassigned slot raises `UndefRefError`. -/
def ArrayCollectionSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 62 →
    heapDimensionsFit src.dimensions = true → src.axes = src.dimensions.map (fun n => (1, n)) →
    let run := (collectArray HeapArray.axes (heapCollectIndices layout) src).run heap
    (none ∈ xs → run = .error .undefinedReference) ∧
    (∀ values : List α, xs = values.map some →
      run = .ok (freshHeapArray src.elementType src.dimensions xs heap))

def EmptyLiteralSpec : Prop :=
  ∀ (α : Type) (initial : MutableMemory α),
    (∀ h, h < initial.arrays.length → initial.validVector h) →
    ∀ literal ∈ [vectEmpty (m := MutationM α) (mutableAllocate (some ⟨8, true, false⟩) 0),
        anyLiteralEmpty (m := MutationM α) (mutableAllocate (some ⟨8, true, false⟩) 0)],
    ∃ next, literal.run initial = (.ok initial.arrays.length, next) ∧
      next.validVector initial.arrays.length ∧ next.contents initial.arrays.length = [] ∧
      ∀ h, h < initial.arrays.length →
        next.arrays[h]? = initial.arrays[h]? ∧ next.contents h = initial.contents h ∧
        ∀ v w, next.arrays[h]? = some v → next.arrays[initial.arrays.length]? = some w →
          v.reference.1 ≠ w.reference.1

theorem boxedEmptyAllocate_run (α : Type) (initial : MutableMemory α) :
    (mutableAllocate (α := α) (some ⟨8, true, false⟩) 0 zero).run initial =
      (.ok initial.arrays.length, allocatedEmptyVector initial) := rfl

theorem validVector_memory_lt {α : Type} (s : MutableMemory α) (h : Nat) (v : MutableVector)
    (hv : s.arrays[h]? = some v) (hvalid : s.validVector h) :
    v.reference.1 < s.memories.length := by
  simp only [MutableMemory.validVector, hv] at hvalid
  split at hvalid
  · exact hvalid.elim
  · rename_i slots hs
    exact (List.getElem?_eq_some_iff.mp hs).1

theorem emptyLiteralSpec : EmptyLiteralSpec := by
  intro α initial hvalid literal hlit
  have hrun : literal.run initial = (.ok initial.arrays.length, allocatedEmptyVector initial) := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hlit
    rcases hlit with rfl | rfl <;> exact boxedEmptyAllocate_run α initial
  obtain ⟨hstate, hcontents⟩ := allocatedEmptyVector_state initial
  refine ⟨allocatedEmptyVector initial, hrun, collectorState_valid _ _ _ hstate, hcontents, ?_⟩
  intro h hh
  obtain ⟨v, hv⟩ : ∃ v, initial.arrays[h]? = some v := ⟨_, List.getElem?_eq_getElem hh⟩
  have hmem := validVector_memory_lt initial h v hv (hvalid h hh)
  have harr : (allocatedEmptyVector initial).arrays[h]? = initial.arrays[h]? := by
    simp only [allocatedEmptyVector]
    exact List.getElem?_append_left hh
  refine ⟨harr, ?_, ?_⟩
  · simp only [MutableMemory.contents, harr, hv]
    simp only [allocatedEmptyVector]
    rw [List.getElem?_append_left hmem]
  · intro v' w hv' hw
    rw [harr, hv] at hv'
    cases hv'
    have hw' : (allocatedEmptyVector initial).arrays[initial.arrays.length]? =
        some ⟨(initial.memories.length, one), zero⟩ := by
      simp [allocatedEmptyVector]
    rw [hw'] at hw
    cases hw
    exact Nat.ne_of_lt hmem
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

/-- The installed growable-vector primitives (array.lean `MutationM`). -/
def liftMemory (x : MutationM α β) : M E U α β := do
  let w ← get
  let (r, s) := Id.run (x.run.run w.memory)
  set { w with memory := s }
  match r with
  | .ok b => pure b
  | .error e => fail (.base e)
end lifts
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6b
open JuliaLean JuliaLean.base.array

def OpaqueIntegerOps.ComparisonLaw (ops : OpaqueIntegerOps) : Prop :=
  ∀ a b, ops.less a b = decide (a < b)

def nativeLessInteger (ops : OpaqueIntegerOps) (n : I) : IntegerArgument → Bool
  | .bit _ x => JuliaLean.base.int.lt n x
  | .boolean b => JuliaLean.base.int.lt n (JuliaLean.base.int.ofBool .i64 b)
  | .opaque v => ops.less n.val v

def integerLessNative (ops : OpaqueIntegerOps) : IntegerArgument → I → Bool
  | .bit _ x, n => JuliaLean.base.int.lt x n
  | .boolean b, n => JuliaLean.base.int.lt (JuliaLean.base.int.ofBool .i64 b) n
  | .opaque v, n => ops.less v n.val
/-- Canonical Union nodes contain at least two distinct well-formed DataTypes. -/
def ValidStoredType : StoredType → Prop
  | .dt d => d.WF
  | .union members => 2 ≤ members.length ∧
      (members.map Layout.name).Nodup ∧ ∀ d ∈ members, d.WF
  | _ => True

def IsBitsUnionSpec : Prop :=
  (∀ u : StoredType, ValidStoredType u →
    (isbitsunion unionType storedInline u = true ↔
      match u with
      | .union members => ∀ d ∈ members, d.isbits = true
      | _ => False)) ∧
  (∀ d : Layout, d.WF → d.isbits = true →
    allocatedinline storedInline (.dt d) = true) ∧
  (∀ u : StoredType, ValidStoredType u → allocatedinline storedInline u = true →
    match u with
    | .dt d => d.mayInline = true
    | .union members => ∀ d ∈ members, d.isbits = true
    | _ => False)

theorem isBitsUnionSpec_refuted : ¬ IsBitsUnionSpec := by
  intro h
  have hn : (valTypes.map Layout.name).Nodup := by
    simp [valTypes, List.map_map, Function.comp_def, List.nodup_range]
  have hwf : ∀ d ∈ valTypes, d.WF := by
    intro d hd
    simp only [valTypes, List.mem_map] at hd
    obtain ⟨i, _, rfl⟩ := hd
    exact ⟨rfl, ⟨0, rfl⟩, Nat.dvd_zero 1⟩
  have hb : ∀ d ∈ valTypes, d.isbits = true := by
    intro d hd
    simp only [valTypes, List.mem_map] at hd
    obtain ⟨i, _, rfl⟩ := hd
    rfl
  have hlen : valTypes.length = 127 := by simp [valTypes]
  have hvalid : ValidStoredType (.union valTypes) := by
    simp only [ValidStoredType]
    exact ⟨by rw [hlen]; omega, hn, hwf⟩
  have hall : valTypes.all (fun d => inlineAlloc d true) = true := by
    simp [valTypes, inlineAlloc]
  have hz : isbitsunion unionType storedInline (.union valTypes) = false := by
    simp [isbitsunion, unionType, allocatedinline, storedInline, unionInlineCount, hall, hlen,
      JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
  have htrue : isbitsunion unionType storedInline (.union valTypes) = true :=
    (h.1 (.union valTypes) hvalid).mpr hb
  rw [hz] at htrue
  cases htrue

abbrev DimensionM (α : Type) :=
  Except (Sum Error JuliaLean.base.abstractarray.ArrayError) α

def arrayDimensions (a : HeapArray Tag) : List I :=
  JuliaLean.base.essentials.sizeArray
    (fun a : HeapArray Tag => fun _ =>
      a.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int))) a

def dimensionSize (a : HeapArray Tag) (d : I) : DimensionM I :=
  (JuliaLean.base.abstractarray.sizeDim
    (fun d : I => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
    (fun a => .ok (arrayDimensions a)) a d).mapError Sum.inr

def DimensionSuffixSpec : Prop :=
  ∀ (ops : OpaqueIntegerOps), ops.ConversionLaw → ops.ComparisonLaw →
  ∀ (Tag : Type) (a : HeapArray Tag) (n : IntegerArgument),
    heapDimensionsFit a.dimensions = true → a.dimensions.length < 2 ^ 63 →
    let rank : I := JInt.wrap .i64 a.dimensions.length
    let fits := IntTy.i64.min ≤ n.value ∧ n.value ≤ IntTy.i64.max
    let run := asizeFrom (m := DimensionM) IntegerArgument.value
      (fun n => (convertInteger ops .i64 n).mapError Sum.inl)
      (fun a : HeapArray Tag => JInt.wrap .i64 a.dimensions.length) dimensionSize a n
    (nativeLessInteger ops rank n = true → run = .ok []) ∧
    (nativeLessInteger ops rank n = false → ¬ fits →
      run = .error (.inl .inexact)) ∧
    (nativeLessInteger ops rank n = false → fits →
      integerLessNative ops n one = true →
      run = .error (.inr (.julia .boundsError))) ∧
    (nativeLessInteger ops rank n = false → fits →
      integerLessNative ops n one = false →
      run = .ok ((a.dimensions.drop (n.value - 1).toNat).map
        (fun d : Nat => JInt.wrap .i64 d)))

private theorem arrayDimensions_length (a : HeapArray Tag) :
    (arrayDimensions a).length = a.dimensions.length := by
  simp [arrayDimensions, JuliaLean.base.essentials.sizeArray]

private theorem dimensionSize_at (a : HeapArray Tag) (i : I)
    (hi : 1 ≤ i.val) (hend : i.val ≤ (a.dimensions.length : Int)) :
    dimensionSize a i =
      .ok ((arrayDimensions a)[(i.val - 1).toNat]?.getD one) := by
  have hconvert :
      JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 i) = .ok i := by
    have hcore : JuliaLean.JInt.convert "convert" .i64 i.val = .ok i := by
      simp [JuliaLean.JInt.convert, i.property]
    change (JuliaLean.JInt.convert "convert" .i64 i.val).mapError
      JuliaLean.base.abstractarray.ArrayError.julia = .ok i
    exact congrArg (Except.mapError JuliaLean.base.abstractarray.ArrayError.julia) hcore
  have hlen := arrayDimensions_length a
  have hidx : (i.val - 1).toNat < (arrayDimensions a).length := by
    rw [hlen]
    omega
  have htuple :
      JuliaLean.base.abstractarray.tupleGet (arrayDimensions a) i =
        .ok ((arrayDimensions a)[(i.val - 1).toNat]?.getD one) := by
    unfold JuliaLean.base.abstractarray.tupleGet
    rw [if_neg (by omega), List.getElem?_eq_getElem hidx]
    simp
  have hsize :
      JuliaLean.base.abstractarray.sizeDim
        (fun d => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
        (fun a' => .ok (arrayDimensions a')) a i =
        .ok ((arrayDimensions a)[(i.val - 1).toNat]?.getD one) := by
    unfold JuliaLean.base.abstractarray.sizeDim
    simp only [hconvert, Bind.bind, Pure.pure, Except.bind]
    have hle : i.val ≤ ((arrayDimensions a).length : Int) := by
      rw [hlen]
      exact hend
    rw [if_pos hle, htuple]
  unfold dimensionSize
  rw [hsize]
  rfl

private theorem dimensionSize_nonpositive (a : HeapArray Tag) (i : I)
    (hi : i.val ≤ 0) :
    dimensionSize a i = .error (.inr (.julia .boundsError)) := by
  have hconvert :
      JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 i) = .ok i := by
    have hcore : JuliaLean.JInt.convert "convert" .i64 i.val = .ok i := by
      simp [JuliaLean.JInt.convert, i.property]
    change (JuliaLean.JInt.convert "convert" .i64 i.val).mapError
      JuliaLean.base.abstractarray.ArrayError.julia = .ok i
    exact congrArg (Except.mapError JuliaLean.base.abstractarray.ArrayError.julia) hcore
  have hlen := arrayDimensions_length a
  have htuple :
      JuliaLean.base.abstractarray.tupleGet (arrayDimensions a) i =
        .error (.julia .boundsError) := by
    unfold JuliaLean.base.abstractarray.tupleGet
    rw [if_pos (by omega)]
  have hsize :
      JuliaLean.base.abstractarray.sizeDim
        (fun d => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
        (fun a' => .ok (arrayDimensions a')) a i =
        .error (.julia .boundsError) := by
    unfold JuliaLean.base.abstractarray.sizeDim
    simp only [hconvert, Bind.bind, Pure.pure, Except.bind]
    have hle : i.val ≤ ((arrayDimensions a).length : Int) := by
      rw [hlen]
      omega
    rw [if_pos hle, htuple]
  unfold dimensionSize
  rw [hsize]
  rfl



private theorem mapM_ok_of_mem_any {α β ε : Type} (f : α → Except ε β)
    (g : α → β) (xs : List α) (h : ∀ x ∈ xs, f x = .ok (g x)) :
    xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have htail : ∀ y ∈ xs, f y = .ok (g y) := by
        intro y hy
        exact h y (by simp [hy])
      simp [List.mapM_cons, hx, ih htail, Except.bind, Bind.bind, Pure.pure, Except.pure]

private theorem dimensionRangeSuffixRuntime (a : HeapArray Tag) (hsize : a.dimensions.length < 2 ^ 63)
    (i : I) (hi : 1 ≤ i.val) (hend : i.val ≤ (a.dimensions.length : Int)) :
    (intRange i (JInt.wrap .i64 (a.dimensions.length : Int))).mapM (dimensionSize a) =
      .ok ((arrayDimensions a).drop (i.val - 1).toNat) := by
  have hdim : (JInt.wrap .i64 (a.dimensions.length : Int)).val = a.dimensions.length := by
    change wrapInt .i64 (a.dimensions.length : Int) = a.dimensions.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  let offset := (i.val - 1).toNat
  let count := a.dimensions.length - offset
  have hcount : ((a.dimensions.length : Int) - i.val + 1).toNat = count := by
    dsimp [count, offset]
    omega
  have hj : ∀ k, k < count →
      (JInt.wrap .i64 (i.val + (k : Int))).val = i.val + (k : Int) := by
    intro k hk
    change wrapInt .i64 (i.val + (k : Int)) = _
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    dsimp [count, offset] at hk
    omega
  unfold intRange
  rw [hdim, hcount, List.mapM_map]
  simp only [Function.comp_def]
  have hs : ∀ k ∈ List.range count,
      dimensionSize a (JInt.wrap .i64 (i.val + (k : Int))) =
        .ok ((arrayDimensions a)[offset + k]?.getD one) := by
    intro k hk
    have hk' := List.mem_range.mp hk
    have hvalue := hj k hk'
    have hpos : 1 ≤ i.val + (k : Int) := by omega
    have hbound : i.val + (k : Int) ≤ (a.dimensions.length : Int) := by
      dsimp [count] at hk'
      omega
    rw [dimensionSize_at a _ (by rw [hvalue]; exact hpos) (by rw [hvalue]; exact hbound)]
    have hidx : (i.val + (k : Int) - 1).toNat = offset + k := by
      dsimp [offset]
      omega
    rw [hvalue, hidx]
  have hmap := mapM_ok_of_mem_any
    (fun (k : Nat) => dimensionSize a (JInt.wrap .i64 (i.val + (k : Int))))
    (fun (k : Nat) => (arrayDimensions a)[offset + k]?.getD one) (List.range count) hs
  rw [hmap]
  apply congrArg Except.ok
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_drop]
    rw [arrayDimensions_length a]
  · intro k hk hk'
    have hoff : offset ≤ a.dimensions.length := by
      dsimp [offset]
      have hnonneg : 0 ≤ i.val - 1 := by omega
      have htoNat : ((i.val - 1).toNat : Int) = i.val - 1 :=
        Int.toNat_of_nonneg hnonneg
      have hcast : ((i.val - 1).toNat : Int) ≤ a.dimensions.length := by
        rw [htoNat]
        omega
      exact_mod_cast hcast
    have hlt : offset + k < a.dimensions.length := by
      simp only [List.length_map, List.length_range] at hk
      dsimp [count] at hk
      omega
    have hlt' : offset + k < (arrayDimensions a).length := by
      rw [arrayDimensions_length a]
      exact hlt
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop,
      List.getElem?_eq_getElem hlt', Option.getD_some]
    rfl
private theorem nativeLessInteger_exact (ops : OpaqueIntegerOps)
    (hcmp : ops.ComparisonLaw) (i : I) (n : IntegerArgument) :
    nativeLessInteger ops i n = decide (i.val < n.value) := by
  cases n with
  | bit t x =>
      simp [nativeLessInteger, IntegerArgument.value, JuliaLean.Proofs.base.int.lt_eq]
      rfl
  | boolean b =>
      have hb : (JuliaLean.base.int.ofBool .i64 b).val = (if b then 1 else 0) := by
        cases b <;> decide
      simp only [nativeLessInteger, IntegerArgument.value, JuliaLean.Proofs.base.int.lt_eq]
      rw [hb]
      rfl
  | «opaque» v =>
      exact hcmp i.val v

private theorem integerLessNative_exact (ops : OpaqueIntegerOps)
    (hcmp : ops.ComparisonLaw) (n : IntegerArgument) (i : I) :
    integerLessNative ops n i = decide (n.value < i.val) := by
  cases n with
  | bit t x =>
      simp [integerLessNative, IntegerArgument.value, JuliaLean.Proofs.base.int.lt_eq]
      rfl
  | boolean b =>
      have hb : (JuliaLean.base.int.ofBool .i64 b).val = (if b then 1 else 0) := by
        cases b <;> decide
      simp only [integerLessNative, IntegerArgument.value, JuliaLean.Proofs.base.int.lt_eq]
      rw [hb]
      rfl
  | «opaque» v =>
      exact hcmp v i.val

private theorem convertIntegerI64 (ops : OpaqueIntegerOps)
    (hconv : ops.ConversionLaw) (n : IntegerArgument) :
    convertInteger ops .i64 n =
      if IntTy.i64.min ≤ n.value ∧ n.value ≤ IntTy.i64.max
      then .ok (JInt.wrap .i64 n.value) else .error .inexact := by
  cases n with
  | bit t x =>
      by_cases h : IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max
      · have hwrap : JInt.wrap .i64 x.val = (⟨x.val, h⟩ : I) := by
          apply Subtype.ext
          change wrapInt .i64 x.val = x.val
          exact wrapInt_of_inRange .i64 x.val h
        simp [convertInteger, IntegerArgument.value, JuliaLean.base.int.convert,
          JuliaLean.JInt.convert, Except.mapError, h, hwrap]
      · simp [convertInteger, IntegerArgument.value, JuliaLean.base.int.convert,
          JuliaLean.JInt.convert, Except.mapError, h]
  | boolean b =>
      cases b <;> simp [convertInteger, IntegerArgument.value, JuliaLean.base.int.ofBool,
        JuliaLean.base.int.lit, JuliaLean.JInt.wrap, wrapInt, IntTy.min, IntTy.max,
        IntTy.signed, IntTy.bits]
  | «opaque» v =>
      change ops.convert .i64 v =
        if IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max
        then .ok (JInt.wrap .i64 v) else .error .inexact
      rw [hconv .i64 v]
private theorem listRangeHead (n : Nat) (hn : 0 < n) :
    ∃ tail, List.range n = 0 :: tail := by
  cases n with
  | zero => omega
  | succ k =>
      induction k with
      | zero => exact ⟨[], by decide⟩
      | succ k ih =>
          obtain ⟨tail, htail⟩ := ih (by omega)
          refine ⟨tail ++ [k + 1], ?_⟩
          rw [List.range_succ, htail]
          simp

private theorem intRangeHead (lo hi : I)
    (hcount : 0 < (hi.val - lo.val + 1).toNat) :
    ∃ tail, intRange lo hi = lo :: tail := by
  obtain ⟨tail, htail⟩ := listRangeHead _ hcount
  refine ⟨tail.map (fun k : Nat => JInt.wrap .i64 (lo.val + (k : Int))), ?_⟩
  unfold intRange
  rw [htail, List.map_cons]
  have hzero : JInt.wrap .i64 lo.val = lo := by
    apply Subtype.ext
    change wrapInt .i64 lo.val = lo.val
    exact wrapInt_of_inRange .i64 lo.val lo.property
  simp only [Int.ofNat_zero, Int.add_zero, hzero]

private theorem intRange_mapM_error (lo hi : I) {ε β : Type} (f : I → Except ε β)
    (e : ε) (hcount : 0 < (hi.val - lo.val + 1).toNat) (hfirst : f lo = .error e) :
    (intRange lo hi).mapM f = .error e := by
  obtain ⟨tail, htail⟩ := intRangeHead lo hi hcount
  rw [htail]
  simp [List.mapM_cons, hfirst, Except.bind, Bind.bind, Pure.pure, Except.pure]


private theorem list_drop_map {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    (xs.map f).drop n = (xs.drop n).map f := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons x xs => exact ih xs

theorem dimensionSuffixSpec : DimensionSuffixSpec := by
  dsimp only [DimensionSuffixSpec]
  intro ops hconv hcmp Tag a n hdim hlen
  let rk : I := JInt.wrap .i64 (a.dimensions.length : Int)
  have hrkVal : rk.val = a.dimensions.length := by
    change wrapInt .i64 (a.dimensions.length : Int) = a.dimensions.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hwrapVal :
      (JInt.wrap .i64 (a.dimensions.length : Int)).val = a.dimensions.length := by
    simpa [rk] using hrkVal
  have hnative : nativeLessInteger ops rk n =
      decide ((a.dimensions.length : Int) < n.value) := by
    rw [nativeLessInteger_exact ops hcmp rk n, hrkVal]
  constructor
  · intro hless
    have hgt : (a.dimensions.length : Int) < n.value := of_decide_eq_true (by
      rw [hnative] at hless
      exact hless)
    change asizeFrom (m := DimensionM) IntegerArgument.value
      (fun n => (convertInteger ops .i64 n).mapError Sum.inl)
      (fun a : HeapArray Tag => JInt.wrap .i64 a.dimensions.length)
      dimensionSize a n = .ok []
    simp [asizeFrom, Except.pure, hwrapVal, hgt]
  constructor
  · intro hless hfits
    change ¬ (IntTy.i64.min ≤ n.value ∧ n.value ≤ IntTy.i64.max) at hfits
    have hfalse : decide ((a.dimensions.length : Int) < n.value) = false := by
      rw [← hnative]
      exact hless
    have hnotgt : ¬ n.value > (a.dimensions.length : Int) :=
      of_decide_eq_false hfalse
    have hconvErr :
        (convertInteger ops .i64 n).mapError Sum.inl =
          (Except.error
            (Sum.inl Error.inexact : Sum Error JuliaLean.base.abstractarray.ArrayError) :
            DimensionM I) := by
      rw [convertIntegerI64 ops hconv n]
      simp [hfits, Except.mapError]
    change asizeFrom (m := DimensionM) IntegerArgument.value
      (fun n => (convertInteger ops .i64 n).mapError Sum.inl)
      (fun a : HeapArray Tag => JInt.wrap .i64 a.dimensions.length)
      dimensionSize a n = .error (.inl .inexact)
    simp [asizeFrom, Except.bind, Bind.bind, Except.pure, Pure.pure,
      hwrapVal, hnotgt, hconvErr]
  constructor
  · intro hless hfits hlessOne
    change IntTy.i64.min ≤ n.value ∧ n.value ≤ IntTy.i64.max at hfits
    have hfalse : decide ((a.dimensions.length : Int) < n.value) = false := by
      rw [← hnative]
      exact hless
    have hnotgt : ¬ n.value > (a.dimensions.length : Int) :=
      of_decide_eq_false hfalse
    have hbound : n.value ≤ (a.dimensions.length : Int) := by omega
    have hone : decide (n.value < 1) = true := by
      have hcmpOne := integerLessNative_exact ops hcmp n one
      rw [hcmpOne] at hlessOne
      exact hlessOne
    have hnonpos : n.value ≤ 0 := by
      have hlt : n.value < 1 := of_decide_eq_true hone
      omega
    let first : I := ⟨n.value, hfits⟩
    have hfirstVal : first.val = n.value := rfl
    have hwrapFirst : JInt.wrap .i64 n.value = first := by
      apply Subtype.ext
      change wrapInt .i64 n.value = n.value
      exact wrapInt_of_inRange .i64 n.value hfits
    have hconvFirst :
        ((convertInteger ops .i64 n).mapError Sum.inl : DimensionM I) = .ok first := by
      rw [convertIntegerI64 ops hconv n]
      simp [first, hfits, hwrapFirst, Except.mapError]
    have hfirstError : dimensionSize a first = .error (.inr (.julia .boundsError)) :=
      dimensionSize_nonpositive a first (by rw [hfirstVal]; exact hnonpos)
    have hcount : 0 < (rk.val - first.val + 1).toNat := by
      rw [hrkVal, hfirstVal]
      have hn : 0 ≤ (a.dimensions.length : Int) - n.value + 1 := by omega
      have hp : 0 < (a.dimensions.length : Int) - n.value + 1 := by omega
      have ht := Int.toNat_of_nonneg hn
      have hp' : 0 < (((a.dimensions.length : Int) - n.value + 1).toNat : Int) := by
        rw [ht]
        exact hp
      exact_mod_cast hp'
    have hmapError :
        (intRange first rk).mapM (dimensionSize a) =
          .error (.inr (.julia .boundsError)) :=
      intRange_mapM_error first rk (dimensionSize a) (.inr (.julia .boundsError))
        hcount hfirstError
    change asizeFrom (m := DimensionM) IntegerArgument.value
      (fun n => (convertInteger ops .i64 n).mapError Sum.inl)
      (fun a : HeapArray Tag => JInt.wrap .i64 a.dimensions.length)
      dimensionSize a n = .error (.inr (.julia .boundsError))
    simp [asizeFrom, Except.bind, Bind.bind, hwrapVal, rk, hnotgt, hconvFirst, hmapError]
  · intro hless hfits hnotLessOne
    change IntTy.i64.min ≤ n.value ∧ n.value ≤ IntTy.i64.max at hfits
    have hfalse : decide ((a.dimensions.length : Int) < n.value) = false := by
      rw [← hnative]
      exact hless
    have hnotgt : ¬ n.value > (a.dimensions.length : Int) :=
      of_decide_eq_false hfalse
    have hbound : n.value ≤ (a.dimensions.length : Int) := by omega
    have hone : decide (n.value < 1) = false := by
      have hcmpOne := integerLessNative_exact ops hcmp n one
      rw [hcmpOne] at hnotLessOne
      exact hnotLessOne
    have hgeOne : 1 ≤ n.value := by
      have hlt : ¬ n.value < 1 := of_decide_eq_false hone
      omega
    let first : I := ⟨n.value, hfits⟩
    have hfirstVal : first.val = n.value := rfl
    have hwrapFirst : JInt.wrap .i64 n.value = first := by
      apply Subtype.ext
      change wrapInt .i64 n.value = n.value
      exact wrapInt_of_inRange .i64 n.value hfits
    have hconvFirst :
        ((convertInteger ops .i64 n).mapError Sum.inl : DimensionM I) = .ok first := by
      rw [convertIntegerI64 ops hconv n]
      simp [first, hfits, hwrapFirst, Except.mapError]
    have hmap :
        (intRange first rk).mapM (dimensionSize a) =
          .ok ((arrayDimensions a).drop (n.value - 1).toNat) :=
      dimensionRangeSuffixRuntime a hlen first
        (by rw [hfirstVal]; exact hgeOne)
        (by rw [hfirstVal]; exact hbound)
    have hdrop :
        (arrayDimensions a).drop (n.value - 1).toNat =
          (a.dimensions.drop (n.value - 1).toNat).map
            (fun d : Nat => JInt.wrap .i64 (d : Int)) := by
      simp [arrayDimensions, JuliaLean.base.essentials.sizeArray]
    have hdropIndex : (n.value - 1).toNat = n.value.toNat - 1 := by omega
    change asizeFrom (m := DimensionM) IntegerArgument.value
      (fun n => (convertInteger ops .i64 n).mapError Sum.inl)
      (fun a : HeapArray Tag => JInt.wrap .i64 a.dimensions.length)
      dimensionSize a n =
        .ok ((a.dimensions.drop (n.value - 1).toNat).map
          (fun d : Nat => JInt.wrap .i64 (d : Int)))
    have hmapDrop := list_drop_map
      (fun d : Nat => JInt.wrap .i64 (d : Int)) a.dimensions ((n.value - 1).toNat)
    simp [asizeFrom, Except.bind, Bind.bind, hwrapVal, rk, hnotgt, hconvFirst, hmap]
    rw [← hdropIndex, hdrop]
    exact hmapDrop.symm
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

theorem dimension_wrap_val (dims : List Nat) (hfit : heapDimensionsFit dims = true) (k : Nat) :
    (JInt.wrap .i64 ((dims[k]?.getD 1 : Nat) : Int)).val = ((dims[k]?.getD 1 : Nat) : Int) := by
  have hall : ∀ x ∈ dims, x < 2 ^ 63 := by
    intro x hx
    have := List.all_eq_true.mp hfit x hx
    simpa using this
  apply ival_wrap
  cases h : dims[k]? with
  | none => simp
  | some x =>
    have := hall x (List.mem_of_getElem? h)
    simp only [Option.getD_some]
    omega

theorem heapSize_one {Tag : Type} (a : HeapArray Tag) (heap : VectorHeap α) :
    (round4.heapSize (α := α) a one).run heap =
      .ok (JInt.wrap .i64 ((a.dimensions[0]?.getD 1 : Nat) : Int), heap) := by
  have h1 : (one : I).val = 1 := rfl
  simp only [round4.heapSize, h1, show ¬ ((1 : Int) < 1) by decide, ite_false]
  rfl

theorem heapSize_two {Tag : Type} (a : HeapArray Tag) (heap : VectorHeap α) :
    (round4.heapSize (α := α) a (JInt.wrap .i64 2)).run heap =
      .ok (JInt.wrap .i64 ((a.dimensions[1]?.getD 1 : Nat) : Int), heap) := by
  simp only [round4.heapSize, wval2', show ¬ ((2 : Int) < 1) by decide, ite_false]
  rfl

theorem similarShapeSpec : round4.SimilarShapeSpec := by
  intro Tag α layout heap a S la lS m dims hla hlS hfit
  dsimp only
  have hv0 := dimension_wrap_val a.dimensions hfit 0
  have hv1 := dimension_wrap_val a.dimensions hfit 1
  have hvec : ∀ (t : Tag) (l : MemoryLayout), layout t = some l → ∀ x : I,
      (heapVectorAllocate (α := α) layout t x).run heap = allocOutcome l t [x.val] heap :=
    fun t l hl x => heapArrayUndef_run layout t l hl [x] heap
  have hmat : ∀ (t : Tag) (l : MemoryLayout), layout t = some l → ∀ ds : List I,
      (heapAllocateIntDims (α := α) layout t ds).run heap = allocOutcome l t (ds.map (·.val)) heap :=
    fun t l hl ds => heapArrayUndef_run layout t l hl ds heap
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [similar414, vector_bind_run, heapSize_one, hvec _ _ hla, hv0]
  · simp only [similar416, vector_bind_run, heapSize_one, hvec _ _ hlS, hv0]
  · simp only [similar415, vector_bind_run, heapSize_one, heapSize_two, hmat _ _ hla,
      List.map_cons, List.map_nil, hv0, hv1]
  · simp only [similar417, vector_bind_run, heapSize_one, heapSize_two, hmat _ _ hlS,
      List.map_cons, List.map_nil, hv0, hv1]
  · exact hvec _ _ hla m
  · exact hmat _ _ hlS dims
  · exact hmat _ _ hla dims
  · exact hmat _ _ hlS dims
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

 theorem MultidimcovArrayV2ElsizeSizeof_proven : JuliaLean.Proofs.base.array.StorageSizesSpec :=
  ⟨arrayStorageSizeSpec, pointerStrideSpec⟩
end JuliaLean.ChatGPT.Batch4.Group2
end


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

/-- The constructor's copy phase is correct whenever its actual allocation succeeds. -/
theorem allocationConstructorAfterAllocation {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String)
    (hcheck : HeapAxesLaw check message)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hl : src.dimensions.prod = xs.length)
    (hn : xs.length < 2 ^ 63)
    (ha : (heapAllocateArray layout target src.dimensions).run heap =
      .ok (⟨heap.length, target, src.dimensions, src.dimensions.map (fun n => (1,n))⟩,
        heap ++ [List.replicate src.dimensions.prod none])) :
    (heapArrayConstructor layout target check convert src).run heap =
      if normalizedHeapAxes (src.dimensions.map (fun n => (1,n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1,n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message) := by
  let dest : HeapArray Tag :=
    ⟨heap.length, target, src.dimensions, src.dimensions.map (fun n => (1,n))⟩
  let next := heap ++ [List.replicate src.dimensions.prod none]
  have hsl : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  have hsrc : next[src.handle]? = some xs := by
    simpa only [next, List.getElem?_append_left hsl] using hs
  have hdest : next[dest.handle]? = some (List.replicate src.dimensions.prod none) := by
    simp only [dest, next, List.getElem?_append, Nat.lt_irrefl, ite_false,
      Nat.sub_self, List.getElem?_cons_zero]
  simp only [heapArrayConstructor, arrayConstructor, vector_bind_run, vector_pure_run, ha,
    heapArrayAxesCopy, JuliaLean.base.abstractarray.copytoAxesCheck]
  rw [hcheck]
  by_cases hax : normalizedHeapAxes (src.dimensions.map (fun n => (1,n))) = normalizedHeapAxes src.axes
  · simp only [hax, ite_true]
    rw [heapArrayCopy_run convert next dest src xs (List.replicate src.dimensions.prod none)
      hsrc hdest (by rw [List.length_replicate, hl]) hn]
    by_cases hx : xs = []
    · subst xs
      have hd0 : src.dimensions.prod = 0 := hl
      simp only [hd0, List.replicate_zero, ite_true, List.mapM_nil, Pure.pure, Except.pure, Except.map,
        dest, next]
    · simp only [hx, ite_false]
      cases hc : xs.mapM convert <;>
        simp only [Except.map, dest, next, List.set_append, Nat.lt_irrefl, ite_false,
          Nat.sub_self, List.set_cons_zero]
  · simp only [hax, ite_false]

/-- Allocation failure propagates before either axis checking or element conversion. -/
theorem allocationConstructorError {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (src : HeapArray Tag) (e : Error)
    (ha : (heapAllocateArray layout target src.dimensions).run heap = .error e) :
    (heapArrayConstructor layout target check convert src).run heap = .error e := by
  simp only [heapArrayConstructor, arrayConstructor, vector_bind_run, vector_pure_run, ha]

/-- The native constructor contract on the successful allocation domain. -/
theorem allocationConstructorOnDomain {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag) (el : MemoryLayout)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String)
    (hcheck : HeapAxesLaw check message)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hlen : src.dimensions.prod = xs.length)
    (hn : xs.length < 2 ^ 63) (hfit : heapDimensionsFit src.dimensions = true)
    (hel : layout target = some el)
    (ha : arrayAllocError el (src.dimensions.map (fun n : Nat => (n : Int))) = none) :
    (heapArrayConstructor layout target check convert src).run heap =
      if normalizedHeapAxes (src.dimensions.map (fun n => (1,n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1,n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message) :=
  allocationConstructorAfterAllocation layout target check convert message hcheck heap src xs
    hs hlen hn (allocationNaturalDimensionsSuccess layout target el src.dimensions heap hel hfit ha)

/-- Native allocation errors take precedence over both the axis check and conversion. -/
theorem allocationConstructorDomainError {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag) (el : MemoryLayout)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (src : HeapArray Tag) (e : Error)
    (hel : layout target = some el) (hfit : heapDimensionsFit src.dimensions = true)
    (ha : arrayAllocError el (src.dimensions.map (fun n : Nat => (n : Int))) = some e) :
    (heapArrayConstructor layout target check convert src).run heap = .error e := by
  apply allocationConstructorError layout target check convert heap src e
  rw [allocationNaturalDimensionsRun layout target el src.dimensions heap hel hfit]
  simp only [allocOutcome, ha]

/-- The abstract-array constructor shares the native constructor's allocation and copy path. -/
theorem allocationAbstractConstructorEq {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (src : HeapArray Tag) :
    abstractArrayConstructor
      (fun a => similar419 (heapAllocateArray layout target) a a.dimensions)
      (heapArrayAxesCopy check convert) src =
        heapArrayConstructor layout target check convert src := by
  simp only [heapArrayConstructor, arrayConstructor, abstractArrayConstructor, similar419,
    pure_bind]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192




/- Complete sorted deletion and splice proof -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c
open JuliaLean.Proofs.base.array

/-- An increasing second index above the source length produces the specified bounds error. -/
theorem deleteSecondAboveLength {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (hv : VecAt s a mem off n slots) (i j : I) (post : List I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) (hroom : i.val < 9223372036854775807)
    (hj : n.val < j.val) :
    (mutableDeleteatList layout a (i :: j :: post)).run s = (.error .bounds, s) ∧
    (mutableDeleteatVector layout a (i :: j :: post)).run s = (.error .bounds, s) := by
  have hinc : (i + one).val = i.val + 1 := ival_add_one i (by omega)
  have hbad : ¬ ((i + one).val ≤ j.val ∧ j.val ≤ n.val) := by omega
  have hnotlt : ¬ j.val < (i + one).val := by rw [hinc]; omega
  have hrun := deleteSecondInvalid layout s a mem off n slots hv i j post hi hbad
  rw [if_neg hnotlt] at hrun
  exact ⟨hrun, (opusGrowth.deleteatVector_run layout a (i :: j :: post) s).trans hrun⟩
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

/-- Already-converted arrays retain object identity and do not invoke the
constructor. Constructor errors and failed result assertions retain effects. -/
def ConvertCheckedIdentityAndErrors : Prop :=
  ∀ (W V A : Type) (cast : V → Option A)
    (constructor : V → ExceptT Error (StateM W) V)
    (a : V) (before after : W),
    (∀ value, cast a = some value →
      (JuliaLean.base.array.Completion.convertChecked cast constructor a).run before =
        (.ok value, before)) ∧
    (cast a = none → ∀ error,
      (constructor a).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.convertChecked cast constructor a).run before =
        (.error error, after)) ∧
    (cast a = none → ∀ value,
      (constructor a).run before = (.ok value, after) → cast value = none →
      (JuliaLean.base.array.Completion.convertChecked cast constructor a).run before =
        (.error (.typeError "convert(Array)"), after))

/-- A successful length observation must satisfy the Integer assertion. Both
an exception and a bad returned type preserve length's resulting state. -/
def SimilarLengthErrors : Prop :=
  ∀ (W X V Z : Type) (length : X → ExceptT Error (StateM W) V)
    (integer : V → Option Z) (itr : X) (before after : W),
    (∀ error, (length itr).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.similarShapeLength length integer itr).run before =
        (.error error, after)) ∧
    (∀ value, (length itr).run before = (.ok value, after) → integer value = none →
      (JuliaLean.base.array.Completion.similarShapeLength length integer itr).run before =
        (.error (.typeError "_similar_shape"), after))

/-- Axis discovery occurs once on the original iterator and preserves the
returned axis object, including errors and effects from custom arrays. -/
def SimilarAxesProtocol : Prop :=
  ∀ (X Axes : Type) (itr : X) (answer : Except Error Axes) (initial : List Nat),
    (JuliaLean.base.array.Completion.similarShapeAxes
      (fun _ => call 0 answer) itr).run initial = (answer, initial ++ [0])

/-- The selected similar method receives the original container and type,
with exactly the dimensions promised by this iterator-size overload. -/
def SimilarGenericArguments : Prop :=
  ∀ (C T X S Shape : Type) (c : C) (t : T) (itr : X) (size : S) (shape : Shape) (initial : List Nat),
    (similarForGeneric (fun c t => call 0 (.ok (c, t))) c t itr size shape).run initial =
      (.ok (c, t), initial ++ [0])

/-- The selected similar method receives the original container and type,
with exactly the dimensions promised by this iterator-size overload. -/
def SimilarUnknownArguments : Prop :=
  ∀ (C T X : Type) (c : C) (t : T) (itr : X) (initial : List Nat),
    (similarForUnknown (fun c t n => call 0 (.ok (c, t, n))) c t itr).run initial =
      (.ok (c, t, zero), initial ++ [0])

/-- The selected similar method receives the original container and type,
with exactly the dimensions promised by this iterator-size overload. -/
def SimilarLengthArguments : Prop :=
  ∀ (C T X Z : Type) (c : C) (t : T) (itr : X) (n : Z) (initial : List Nat),
    (similarForLength (fun c t n => call 0 (.ok (c, t, n))) c t itr n).run initial =
      (.ok (c, t, n), initial ++ [0])

/-- The selected similar method receives the original container and type,
with exactly the dimensions promised by this iterator-size overload. -/
def SimilarAxesArguments : Prop :=
  ∀ (C T X Axes : Type) (c : C) (t : T) (itr : X) (axes : Axes) (initial : List Nat),
    (similarForAxes (fun c t axes => call 0 (.ok (c, t, axes))) c t itr axes).run initial =
      (.ok (c, t, axes), initial ++ [0])

/-- Throwing the argument-error helper never changes the mutable world. -/
def ThrowArgumentState : Prop :=
  ∀ (W A : Type) (message : String) (state : W),
    (throwArgument (m := ExceptT Error (StateM W)) (α := A) message).run state =
      (.error (.argument message), state)
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion2
open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Completion2

/-- For native Int axes, converting a OneTo to a dimension returns its endpoint, including zero. -/
def OneToDimensionEndpoint : Prop :=
  ∀ (stop : I),
    letI : JuliaLean.base.range.JConvert I I := ⟨fun x => .ok (JuliaLean.base.number.convertSame x)⟩
    JuliaLean.base.array.Completion2.toDimOneTo (JuliaLean.base.range.OneTo.mk stop) = .ok stop

/-- Invalid wrapping preserves storage and reports all supplied sizes in its DimensionMismatch message. -/
def InvalidWrapDimensionError : Prop :=
  ∀ (W A Len Dims Product : Type)
    (renderLength : Len → String) (renderDims : Dims → String)
    (renderProduct : Product → String) (len : Len) (dims : Dims) (product : Product) (state : W),
    (JuliaLean.base.array.invalidWrapError (m := ExceptT Error (StateM W)) (α := A)
      renderLength renderDims renderProduct len dims product).run state =
      (.error (.dimensionMismatch (
        "Attempted to wrap a MemoryRef of length " ++ renderLength len ++
        " with an Array of size dims=" ++ renderDims dims ++
        " which is invalid because prod(dims) = " ++ renderProduct product ++
        " > " ++ renderLength len ++
        " so that the array would have more elements than the underlying memory can store.")), state)

theorem InvalidWrapDimensionError_proven : InvalidWrapDimensionError := by
  unfold InvalidWrapDimensionError
  intros
  rfl

end JuliaLean.Proofs.base.array.Completion2


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- A heterogeneous literal discovers its promoted type before forwarding every original value, in order, to the typed literal constructor. -/
def PromotedLiteralArguments : Prop :=
  ∀ (E T : Type) (values : List E) (ty : T) (initial : List Nat),
    (JuliaLean.base.array.Completion3.vectPromoted (fun _ => call 0 (.ok ty))
      (fun t xs => call 1 (.ok (t, xs))) values).run initial =
        (.ok (ty, values), initial ++ [0, 1])

/-- The fallback rejects a non-Bool first keyword before testing shrink, rejecting unknown keywords or calling positional sizehint; storage remains unchanged. -/
def SizehintKeywordTypeErrors : Prop :=
  ∀ (W V A Z R : Type) (names : List String) (field : String → Option V)
    (boolCast : V → Option Bool) (sizehint : A → Z → ExceptT Error (StateM W) R)
    (a : A) (sz : Z) (value : V) (world : W),
    field "first" = some value → boolCast value = none →
    (JuliaLean.base.array.Completion3.sizehintKwcall names field boolCast sizehint a sz).run world =
      (.error (.typeError "sizehint!:first"), world)
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion4
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion4
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- A dimension number greater than the immutable rank returns the empty tuple before Int conversion, tuple construction or size observations, retaining comparison effects. -/
def DimensionSuffixEmpty : Prop :=
  ∀ (W Z SumIndex Index Extent A : Type) (rank : I)
    (greater : Z → I → M W (Option Bool)) (toInt : Z → M W I)
    (add : I → Z → M W SumIndex) (subtractOne : SumIndex → M W Index)
    (size : A → Index → M W Extent) (a : A) (n : Z) (before after : W),
    (greater n rank).run.run before = (.ok (.ok (some true)), after) →
    (JuliaLean.base.array.Completion4.asizeFrom rank greater toInt add subtractOne size a n).run.run before =
      (.ok (.ok []), after)

/-- Array promotion retains an existing array type when its element type already matches the promoted element type, preferring the left type when both match. -/
def PromoteArrayPreservesMatchingContainer : Prop :=
  ∀ (T : Type) [DecidableEq T] (promote join : T → T → T) (a b left right : T),
    (promote a b = a → JuliaLean.base.array.Completion4.promoteArrayRule (m := Id) promote join a b left right = left) ∧
    (promote a b ≠ a → promote a b = b →
      JuliaLean.base.array.Completion4.promoteArrayRule (m := Id) promote join a b left right = right)
end JuliaLean.Proofs.base.array.Completion4


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion7
open JuliaLean JuliaLean.base.array

/-- AbstractArray conversion allocates through the source array's similar
method before checking axes or copying, retaining similar's errors and effects. -/
def AbstractConstructorSimilarErrors : Prop :=
  ∀ (W S A Axes : Type)
    (similar : S → ExceptT JuliaLean.base.abstractarray.ArrayError (StateM W) A)
    (axesDest : A → ExceptT JuliaLean.base.abstractarray.ArrayError (StateM W) Axes)
    (axesSrc : S → ExceptT JuliaLean.base.abstractarray.ArrayError (StateM W) Axes)
    (eq : Axes → Axes → ExceptT JuliaLean.base.abstractarray.ArrayError (StateM W) Bool)
    (showAxes : Axes → ExceptT JuliaLean.base.abstractarray.ArrayError (StateM W) String)
    (copy : A → S → ExceptT JuliaLean.base.abstractarray.ArrayError (StateM W) A)
    (a : S) (before after : W) (error : JuliaLean.base.abstractarray.ArrayError),
    (similar a).run before = (.error error, after) →
    (JuliaLean.base.array.Completion7.abstractArrayConstructor similar axesDest axesSrc eq showAxes copy a).run before =
      (.error error, after)
end JuliaLean.Proofs.base.array.Completion7


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Models1Group13

/-- All argument tuples in the selected homogeneous dispatch are covered,
including sizes rejected by the native allocation checks. This describes the
result's contents and fresh identity, not the writing loop.
Julia source: base/array.jl:159-166,170-173.
Documentation: doc/src/manual/arrays.md:96-107.
Allocation: src/genericmemory.c:55-102, with MAXINTVAL = 2^63-1.
The nonempty premise selects this overload instead of the `vect()` overload;
the tuple's native length bound is carried by `TupleArgs` itself. -/
def VectHomogeneousContract : Prop :=
  ∀ (α : Type) (layout : Option MemoryLayout) (args : TupleArgs α)
    (before : MutableMemory α), args.values ≠ [] →
    let run := (vectHomogeneous layout args).run before
    match layout with
    | none => ∃ context, run = (.error (.typeError context), before)
    | some metadata =>
      let n := args.values.length
      let bytes := n * (if metadata.isboxed then 8 else metadata.size) +
        (if metadata.isunion then n else 0)
      if n < 2 ^ 63 - 2 ∧ bytes < 2 ^ 63 - 2 then
        ∃ handle after, run = (.ok handle, after) ∧
          FreshVectorContents before after handle args.values
      else
        ∃ message, run = (.error (.argument message), before)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean
open JuliaLean.base.array.Models1Group13
abbrev IntResult (World : Type) :=
  Option (Except (NativeError × World) (JInt .i64 × World))

/-- Native observations for the Ptr branch after its initial type check.
The Core payload query precedes the layout observation. -/
def ObservePointerAfterCheck
    (types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym)
    (elementType : V) (before : World) (observed : LayoutObservation World) : Prop :=
  ObserveNative (types.coreSizeof elementType) before
    (fun payload after observed =>
      match types.asDatatype elementType with
      | none =>
          observed = .failed (.foreignError "MethodError" "datatype_alignment") after
      | some datatype =>
          ObserveAlignment types datatype after
            (fun alignment final observed =>
              observed = .inlineExtent payload.val alignment final) observed)
    observed

/-- Complete Ptr native protocol, including inconsistent primitive inputs:
if a non-DataType's Core.sizeof(Any) unexpectedly succeeds, observe the subsequent
source calls too. No input is omitted by assuming native success or a law. -/
def ObservePointerLayout
    (types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym)
    (elementType : V) (before : World) (observed : LayoutObservation World) : Prop :=
  if types.egal elementType types.any then
    observed = .pointerSlot before
  else if (types.asDatatype elementType).isSome then
    ObservePointerAfterCheck types elementType before observed
  else
    ObserveNative (types.coreSizeof types.any) before
      (fun _ after => ObservePointerAfterCheck types elementType after) observed

/-- All protocol outcomes are constrained: failure/divergence exactly, successful
world exactly, and successful numeric values by independent storage arithmetic.
The existential stride does not assume that the implementation succeeds. -/
def StrideMatches (observed : LayoutObservation World) (result : IntResult World) : Prop :=
  match observed with
  | .diverged => result = none
  | .failed error after => result = some (.error (error, after))
  | .pointerSlot after =>
      ∃ stride : JInt .i64, result = some (.ok (stride, after)) ∧ stride.val = 8
  | .inlineExtent payload alignment after =>
      ∃ stride : JInt .i64,
        result = some (.ok (stride, after)) ∧ MinimalAlignedWord payload alignment stride

/-- base/array.jl:218; minimal extent/alignment is the obvious storage invariant.
Every native boundary input and initial world is quantified. Existence of an
observation is part of the conclusion, preventing vacuous unobserved branches.
No correctness premise is imposed on the source model or native callbacks. -/
def ElsizeArrayRuntimeSpec : Prop :=
  ∀ (World V D N Mod P Sym Ref : Type)
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (elementType : V) (before : World),
    ∃ observed : LayoutObservation World,
      ObserveArrayLayout runtime elementType before observed ∧
      StrideMatches observed (elsizeArrayRuntime runtime elementType before)

/-- base/array.jl:219-225. Includes Any, non-DataTypes, ordinary datatypes,
native errors and divergence, and all state changes preceding an error. -/
def ElsizePtrRuntimeSpec : Prop :=
  ∀ (World V D N Mod P Sym : Type)
    (types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym)
    (elementType : V) (before : World),
    ∃ observed : LayoutObservation World,
      ObservePointerLayout types elementType before observed ∧
      StrideMatches observed (elsizePtrRuntime types elementType before)

/-- Independent mathematical element count. Empty dimensions mean one element;
a zero dimension means zero elements. -/
def MathematicalCount (header : SizeHeader V) : Int :=
  (header.dimensions.map (fun dimension => dimension.val)).prod

/-- Necessary live-header representation invariants, not constructor-success
assumptions: machine rank, nonnegative machine dimensions, and a logical window
that fits a representable live backing-memory capacity. The capacity bound
matches the existing round6e.validMemory boundary and admits unsafe_wrap sizes.
These are necessary header representation invariants, not a complete byte/address
constructibility certificate: this predicate has no type/layout/address witness.
A byte-level installation may add that existing native validity witness without
requiring ordinary allocator success. -/
def SizeHeaderValid (header : SizeHeader V) : Prop :=
  header.dimensions.length < 2 ^ 63 ∧
  (∀ dimension ∈ header.dimensions, 0 ≤ dimension.val) ∧
  ∃ (capacity offset : JInt .i64),
    0 ≤ capacity.val ∧ capacity.val < (2 : Int) ^ 63 - 1 ∧
    0 ≤ offset.val ∧ offset.val + MathematicalCount header ≤ capacity.val

/-- Byte accounting from independent dimension arithmetic and native payload
metadata. Alignment uses least sufficient padding; no selector byte is counted. -/
def StorageBytesMatch (count : Int) (observed : LayoutObservation World)
    (result : IntResult World) : Prop :=
  match observed with
  | .diverged => result = none
  | .failed error after => result = some (.error (error, after))
  | .pointerSlot after =>
      ∃ bytes : JInt .i64, result = some (.ok (bytes, after)) ∧
        bytes.val % (2 : Int) ^ 64 = (count * 8) % (2 : Int) ^ 64
  | .inlineExtent payload alignment after =>
      ∃ bytes : JInt .i64, result = some (.ok (bytes, after)) ∧
        (count = 0 → bytes.val = 0) ∧
        (∀ k : Nat, alignment = (2 : Int) ^ k →
          ∃ padded : Int,
            payload ≤ padded ∧ padded < payload + alignment ∧ padded % alignment = 0 ∧
            bytes.val % (2 : Int) ^ 64 = (count * padded) % (2 : Int) ^ 64)

/-- base/array.jl:229. The entire observation, including native failures and
divergence, is constrained even for a zero-element array. Headers satisfying the
necessary representation invariants can have any rank and assigned/unassigned
cells; no cell is read by sizeof. -/
def SizeofArrayRuntimeSpec : Prop :=
  ∀ (World V D N Mod P Sym Ref : Type)
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (header : SizeHeader V) (before : World),
    SizeHeaderValid header →
    ∃ observed : LayoutObservation World,
      ObserveArrayLayout runtime header.elementType before observed ∧
      StorageBytesMatch (MathematicalCount header) observed
        (sizeofArrayRuntime runtime header before)

/-- Rank/shape independence is a metamorphic invariant: same element type and
same mathematical count imply the same complete outcome, including errors,
divergence and final world. It detects accidental rank-dependent accounting;
it is not sufficient by itself because a constant implementation would pass. -/
def SizeofSameCountSpec : Prop :=
  ∀ (World V D N Mod P Sym Ref : Type)
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (a b : SizeHeader V) (before : World),
    SizeHeaderValid a → SizeHeaderValid b →
    a.elementType = b.elementType → MathematicalCount a = MathematicalCount b →
    sizeofArrayRuntime runtime a before = sizeofArrayRuntime runtime b before
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Source base/array.jl:414: all valid selected-rank source headers keep
exactly their complete shape, with the source element type. Mathematical native
allocation checks and raw native allocation/header outcomes are specified for
every metadata input, including failures, effects and divergence. No successful
allocation or content/freshness law is assumed. -/
def Similar414NativeContract : Prop :=
  ∀ (State T : Type) (allocation : NativeAllocationBoundary State T)
    (before : NativeCopyWorld State) (array : NativeRankArray T 1),
    NativeCopyArrayValid before array.val →
      NativeCopyObserve (nativeSimilar414 allocation array) before =
        NativeUndefRequest allocation array.val.dimensions before

/-- Source base/array.jl:415: all valid selected-rank source headers keep
exactly their complete shape, with the source element type. Mathematical native
allocation checks and raw native allocation/header outcomes are specified for
every metadata input, including failures, effects and divergence. No successful
allocation or content/freshness law is assumed. -/
def Similar415NativeContract : Prop :=
  ∀ (State T : Type) (allocation : NativeAllocationBoundary State T)
    (before : NativeCopyWorld State) (array : NativeRankArray T 2),
    NativeCopyArrayValid before array.val →
      NativeCopyObserve (nativeSimilar415 allocation array) before =
        NativeUndefRequest allocation array.val.dimensions before

/-- Source base/array.jl:416: all valid selected-rank source headers keep
exactly their complete shape, with the requested element type. Mathematical native
allocation checks and raw native allocation/header outcomes are specified for
every metadata input, including failures, effects and divergence. No successful
allocation or content/freshness law is assumed. -/
def Similar416NativeContract : Prop :=
  ∀ (State T S : Type) (allocation : NativeAllocationBoundary State S)
    (before : NativeCopyWorld State) (array : NativeRankArray T 1),
    NativeCopyArrayValid before array.val →
      NativeCopyObserve (nativeSimilar416 allocation array) before =
        NativeUndefRequest allocation array.val.dimensions before

/-- Source base/array.jl:417: all valid selected-rank source headers keep
exactly their complete shape, with the requested element type. Mathematical native
allocation checks and raw native allocation/header outcomes are specified for
every metadata input, including failures, effects and divergence. No successful
allocation or content/freshness law is assumed. -/
def Similar417NativeContract : Prop :=
  ∀ (State T S : Type) (allocation : NativeAllocationBoundary State S)
    (before : NativeCopyWorld State) (array : NativeRankArray T 2),
    NativeCopyArrayValid before array.val →
      NativeCopyObserve (nativeSimilar417 allocation array) before =
        NativeUndefRequest allocation array.val.dimensions before

/-- Source base/array.jl:418: every native Int dimension reaches the proper
Vector/Memory checks, including negative, zero, typemax and native-size rejection.
The source's contents/rank do not select the requested shape. Native allocation
and Core header outcomes remain fully observed without a success premise. -/
def Similar418NativeContract : Prop :=
  ∀ (State T : Type) (allocation : NativeAllocationBoundary State T)
    (before : NativeCopyWorld State) (array : NativeCopyArray T) (dimension : I),
    NativeCopyObserve (nativeSimilar418 allocation array dimension) before =
      NativeUndefRequest allocation [dimension] before

/-- Source base/array.jl:419: every constructible native size tuple is covered,
with arbitrary requested element type S, all Array/Memory rejection branches,
and every native outcome. The output rank is the tuple length and its shape is
exactly that tuple, without making claims about uninitialized payload values. -/
def Similar419NativeContract : Prop :=
  ∀ (State T S : Type) (allocation : NativeAllocationBoundary State S)
    (before : NativeCopyWorld State) (array : NativeCopyArray T) (dimensions : TupleArgs I),
    NativeCopyObserve (nativeSimilar419 allocation array dimensions) before =
      NativeUndefRequest allocation dimensions.values before

/-- Source base/array.jl:420: every constructible native size tuple is covered,
retaining the source element type T. Errors, partial native effects and divergence
follow the independent mathematical allocation/header protocol. -/
def Similar420NativeContract : Prop :=
  ∀ (State T : Type) (allocation : NativeAllocationBoundary State T)
    (before : NativeCopyWorld State) (array : NativeCopyArray T) (dimensions : TupleArgs I),
    NativeCopyObserve (nativeSimilar420 allocation array dimensions) before =
      NativeUndefRequest allocation dimensions.values before

/-- Source base/array.jl:421: the input Array type's rank does not constrain
the requested dimensions. Every native size tuple is handled with its own rank,
selected element type T, complete dimension/byte-size errors and native outcomes.
The old rank and new tuple length are deliberately not equated. -/
def Similar421NativeContract : Prop :=
  ∀ (State T : Type) (allocation : NativeAllocationBoundary State T)
    (before : NativeCopyWorld State) (sourceRank : I) (dimensions : TupleArgs I),
    NativeCopyObserve (nativeSimilar421 allocation sourceRank dimensions) before =
      NativeUndefRequest allocation dimensions.values before
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Memory growth preserves the source Memory element layout when requesting
new capacity. Mathematical counts and byte-size checks specify every native
Int input, including rejection, errors, mutation and divergence.
Source: base/array.jl:1114; src/genericmemory.c:55-102. -/
def ArrayNewMemoryRequestInvariant : Prop :=
  ∀ (State T : Type) (allocation : NativeAllocationBoundary State T)
    (memory : NativeCopyMemory T) (newLength : I) (before : NativeCopyWorld State),
    let metadata : MemoryLayout :=
      ⟨memory.layoutBytes.val.toNat, decide (memory.arrayElement = 1),
        decide (memory.arrayElement = 2)⟩
    NativeCopyObserve (nativeArrayNewMemory allocation memory newLength) before =
      NativeMemoryRequest { allocation with layout := some metadata } newLength.val before
        (fun allocated after => some (.ok (allocated, after)))
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array
theorem JuliaLean.Proofs.base.array.Completion.ConvertCheckedIdentityAndErrors_proven : JuliaLean.Proofs.base.array.Completion.ConvertCheckedIdentityAndErrors := by
  unfold JuliaLean.Proofs.base.array.Completion.ConvertCheckedIdentityAndErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.convertChecked, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.SimilarLengthErrors_proven : JuliaLean.Proofs.base.array.Completion.SimilarLengthErrors := by
  unfold JuliaLean.Proofs.base.array.Completion.SimilarLengthErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.similarShapeLength, JuliaLean.base.array.similarShapeLength, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.SimilarGenericArguments_proven : JuliaLean.Proofs.base.array.Completion.SimilarGenericArguments := by
  unfold JuliaLean.Proofs.base.array.Completion.SimilarGenericArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.similarForGeneric, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.SimilarUnknownArguments_proven : JuliaLean.Proofs.base.array.Completion.SimilarUnknownArguments := by
  unfold JuliaLean.Proofs.base.array.Completion.SimilarUnknownArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.similarForUnknown, JuliaLean.base.array.zero, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.SimilarLengthArguments_proven : JuliaLean.Proofs.base.array.Completion.SimilarLengthArguments := by
  unfold JuliaLean.Proofs.base.array.Completion.SimilarLengthArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.similarForLength, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.SimilarAxesArguments_proven : JuliaLean.Proofs.base.array.Completion.SimilarAxesArguments := by
  unfold JuliaLean.Proofs.base.array.Completion.SimilarAxesArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.similarForAxes, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.ThrowArgumentState_proven : JuliaLean.Proofs.base.array.Completion.ThrowArgumentState := by
  unfold JuliaLean.Proofs.base.array.Completion.ThrowArgumentState
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.throwArgument, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.OneToDimensionEndpoint_proven : JuliaLean.Proofs.base.array.Completion2.OneToDimensionEndpoint := by
  unfold JuliaLean.Proofs.base.array.Completion2.OneToDimensionEndpoint
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.toDimOneTo, JuliaLean.base.array.toDimOneTo, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.PromotedLiteralArguments_proven : JuliaLean.Proofs.base.array.Completion3.PromotedLiteralArguments := by
  unfold JuliaLean.Proofs.base.array.Completion3.PromotedLiteralArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.vectPromoted, JuliaLean.base.array.vectPromoted, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.SizehintKeywordTypeErrors_proven : JuliaLean.Proofs.base.array.Completion3.SizehintKeywordTypeErrors := by
  unfold JuliaLean.Proofs.base.array.Completion3.SizehintKeywordTypeErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.sizehintKwcall, JuliaLean.base.array.sizehint, JuliaLean.base.array.sizehintKwcall, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.DimensionSuffixEmpty_proven : JuliaLean.Proofs.base.array.Completion4.DimensionSuffixEmpty := by
  unfold JuliaLean.Proofs.base.array.Completion4.DimensionSuffixEmpty
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.asizeFrom, JuliaLean.base.array.asizeFrom, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.PromoteArrayPreservesMatchingContainer_proven : JuliaLean.Proofs.base.array.Completion4.PromoteArrayPreservesMatchingContainer := by
  unfold JuliaLean.Proofs.base.array.Completion4.PromoteArrayPreservesMatchingContainer
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.promoteArrayRule, JuliaLean.base.array.promoteArrayRule, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion7.AbstractConstructorSimilarErrors_proven : JuliaLean.Proofs.base.array.Completion7.AbstractConstructorSimilarErrors := by
  unfold JuliaLean.Proofs.base.array.Completion7.AbstractConstructorSimilarErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion7.abstractArrayConstructor, JuliaLean.base.array.abstractArrayConstructor, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesArray1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-convert-array", juliaFile := "base/array.jl",
    juliaFns := ["convert(::Type{T}, ::AbstractArray) where T<:Array"],
    statement := "`convert(::Type{T}, a::AbstractArray) where {T<:Array}` (array.jl:657; `convert` docstring in essentials.jl: \"If `x` is already of type `T`, return `x` itself\") for a fully assigned heap array: an array already of the requested element type is returned itself with the heap unchanged; otherwise `T(a)` builds a fresh converted array.",
    source := "base/array.jl:657", status := .todo,
    prop := ``CompleteHeapArrayConvertSpec, thm := none,
    notes := "Incomplete allocation domain: CompleteHeapArrayConvertSpec's copying conjuncts demand allocation success with layout target = none or byte sizes rejected by arrayAllocError. Such absent-metadata native success is not a Julia operation. Preserve the same-type identity case; copying must account for allocator errors with runtime-valid metadata. No exact full certificate was returned." },
  { id := "multidimcov-array-v2-array-constructor", juliaFile := "base/array.jl",
    juliaFns := ["Array{T,N}(::AbstractArray{S,N})"],
    statement := "`Array{T,N}(x::AbstractArray{S,N})` (array.jl:664; `Array` constructor docstring in boot.jl and the manual's \"Construct an array of the given type from the elements of `x`\") for a fully assigned heap array `x`: `Array{T,N}(undef, size(x))` and `copyto_axcheck!` give a fresh array of element type `T` and `x`'s dimensions holding `convert(T, x[i])` in order (any user conversion, whose first error propagates).",
    source := "base/array.jl:664", status := .todo,
    prop := ``CompleteHeapArrayConstructorSpec, thm := none,
    notes := "Incomplete allocation domain: CompleteHeapArrayConstructorSpec includes success claims with layout target = none and an element-count bound that does not ensure allocator byte-size validity. Absent-metadata native success is not a Julia operation. Account for arrayAllocError before conversion using runtime-valid metadata; returned on-domain lemmas do not settle the exact conjunction." },
  { id := "multidimcov-array-v2-abstractarray-constructor", juliaFile := "base/array.jl",
    juliaFns := ["AbstractArray{T,N}(::AbstractArray{S,N})"],
    statement := "`AbstractArray{T,N}(A::AbstractArray{S,N})` (array.jl:665) for a fully assigned heap array: `similar(A, T)` and `copyto_axcheck!` give a fresh array of element type `T` and `A`'s dimensions holding the converted values in order.",
    source := "base/array.jl:665", status := .todo,
    prop := ``CompleteHeapAbstractConstructorSpec, thm := none,
    notes := "Incomplete allocation domain: CompleteHeapAbstractConstructorSpec's similar-and-copy claims omit the present runtime-valid target layout and allocator byte-size/error cases. A successful native array with absent metadata has no Julia counterpart. Account for allocation errors before copying; returned on-domain constructor lemmas do not settle the exact conjunction." }
]
def entriesArray2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-similar", juliaFile := "base/array.jl",
    juliaFns := ["similar(::Vector{T})", "similar(::Matrix{T})", "similar(::Vector{T}, ::Type)",
      "similar(::Matrix{T}, ::Type)", "similar(::Array{T}, ::Int)",
      "similar(::Array, ::Type, ::Dims)", "similar(::Array{T}, ::Dims)",
      "similar(::Type{Array{T,N}}, ::Dims)"],
    statement := "The `similar` methods for `Array` (array.jl:414-421, `similar` docstring in abstractarray.jl: \"Create an uninitialized mutable array with the given element type and size, based upon the given source array.\") on the shared heap, with `Vector{T}(undef, n)`, `Matrix{T}(undef, n, m)` and `Array{T,N}(undef, dims)` the Core allocators of the store (`heapVectorAllocate`, `heapAllocateIntDims`): each returns a fresh array of the requested element type (the source's element type when none is given) and the requested dimensions (`size(a, 1)`, `size(a, 2)` by default), with only unassigned slots, appended to the heap so that no existing array changes; a negative dimension raises `ArgumentError`.",
    source := "base/array.jl:414-421", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.SimilarShapeSpec, thm := some ``opusGrowth.similarShapeSpec,
    notes := "" }
]
def entriesArray3 : List JuliaLean.Registry.Entry := [
  { id := "array-empty-literal", juliaFile := "base/array.jl",
    juliaFns := ["vect()", "getindex(::Type{Any})"],
    statement := "`vect()` (array.jl:158, the empty literal `[]`; `vect(X...)` docstring at array.jl:168-181: \"Create a `Vector` ... containing the argument list\") and `getindex(::Type{Any})` (array.jl:471, `Any[]`; docstring at array.jl:424-444: \"Construct a 1-d array of the specified type\"), each `Vector{Any}()`, through the store's `Array` allocation: every call returns a new valid empty vector whose memory no existing array shares, and every existing array keeps its header and contents.",
    source := "base/array.jl:158, array.jl:168-181, array.jl:424-444, array.jl:471", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.EmptyLiteralSpec, thm := some ``JuliaLean.Proofs.base.array.round4.emptyLiteralSpec,
    notes := "" },
  { id := "multidimcov-array-v2-vect-typed", juliaFile := "base/array.jl",
    juliaFns := ["vect(X::T...)", "getindex(::Type{Any}, vals...)"],
    statement := "Homogeneous vector literals contain exactly their arguments in order, including empty inputs.",
    source := "base/array.jl:158-186,445-471", status := .proven,
    prop := ``LiteralContents, thm := some ``literalContents}
]
def entriesArray4 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-vect-promote", juliaFile := "base/array.jl",
    juliaFns := ["vect(X...)"],
    statement := "Mixed vector literals have the promoted element type and the arguments converted to that type in order; conversion errors propagate.",
    source := "base/array.jl:168-186", status := .proven,
    prop := ``PromotedLiteralContents, thm := some ``promotedLiteralContents}
]
def entriesArray5 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-elsize-sizeof", juliaFile := "base/array.jl",
    juliaFns := ["elsize(::Type{A}) where {T,A<:Array{T}}", "elsize(::Type{Ptr{T}})",
      "elsize(::Type{Union{}})", "elsize(::Type{Union{}}, slurp...)", "sizeof(::Array)"],
    statement := "Inline element strides equal their runtime sizes, boxed arrays use pointer strides, sizeof counts element bytes, pointer strides respect alignment, and bottom-type queries return zero or MethodError for extra arguments.",
    source := "base/array.jl:218-229; runtime layout interface", status := .proven,
    prop := ``StorageSizesSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2ElsizeSizeof_proven}
]
def entriesArray6 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-wrap-negative-length", juliaFile := "base/array.jl",
    juliaFns := ["_wrap(::MemoryRef, ::Dims)",
      "wrap(::Type{Array}, ::MemoryRef, ::Tuple)", "wrap(::Type{Array}, ::Memory, ::Tuple)",
      "wrap(::Type{Array}, ::MemoryRef, ::Integer)", "wrap(::Type{Array}, ::Memory, ::Integer)",
      "wrap(::Type{Array}, ::Memory)"],
    statement := "Wrapping preserves memory and requested nonnegative dimensions, rejects excessive size and negative dimensions, and checks Int conversion.",
    source := "base/array.jl:3228-3231 (docstring),3236-3274", status := .refuted,
    prop := ``WrapDocumented, thm := some ``wrapDocumented_refuted,
    issue := "none found (queries: wrap Memory negative dimensions)",
    notes := "The singleton Core.checked_dims method returns a negative size unchanged, and _wrap accepts it." },
  { id := "arraycov-wrap-memory-unsigned", juliaFile := "base/array.jl",
    juliaFns := ["wrap(::Type{Array}, ::Memory, ::Integer)"],
    statement := "Memory wrapping accepts every nonnegative Int-representable Integer length that fits.",
    source := "base/array.jl:3228-3231 (docstring),3265-3269", status := .refuted,
    prop := ``WrapMemoryIntegerSpec, thm := some ``wrapMemoryIntegerSpec_refuted,
    issue := "none found (queries: wrap Memory unsigned MethodError)",
    notes := "The Memory overload passes the unconverted length to _wrap, whose tuple method requires Int." }
]
def entriesArray7 : List JuliaLean.Registry.Entry := [
  { id := "array-isbitsunion-small", juliaFile := "base/array.jl", juliaFns := ["isbitsunion(::Type)"],
    statement := "A union of 2 through 126 well-formed concrete members is isbitsunion exactly when every member is isbitstype.",
    source := "base/array.jl:192-206 (docstring)", status := .proven,
    prop := ``IsBitsUnionSmall, thm := some ``isBitsUnionSmall}
]
def entriesArray8 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-isbitsunion-many-members", juliaFile := "base/array.jl",
    juliaFns := ["isbitsunion(::Type)", "allocatedinline(::Type)"],
    statement := "Across every canonical StoredType, isbitsunion classifies exactly Unions whose members are isbitstype and rejects non-Union types, including Bottom. Concrete isbits DataTypes allocate inline; inline allocation requires eligible DataType or isbits Union members.",
    source := "base/array.jl:190-206", status := .refuted,
    prop := ``JuliaLean.Proofs.base.array.round6b.IsBitsUnionSpec, thm := some ``JuliaLean.Proofs.base.array.round6b.isBitsUnionSpec_refuted,
    issue := "none found (queries: isbitsunion 127; isbitsunion members)",
    notes := "" }
]
def entriesArray9 : List JuliaLean.Registry.Entry := [
{ id := "array-throw-argument-state", juliaFile := "base/array.jl",
  juliaFns := ["_throw_argerror(s)"],
  statement := "Throwing the argument-error helper never changes the mutable world.",
  source := "base/array.jl:321-321", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.ThrowArgumentState, thm := some ``JuliaLean.Proofs.base.array.Completion.ThrowArgumentState_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
def entriesArray10 : List JuliaLean.Registry.Entry := [
{ id := "array-convert-checked-identity-and-errors", juliaFile := "base/array.jl",
  juliaFns := ["convert(::Type{T}, a::AbstractArray) where {T<:Array}"],
  statement := "Already-converted arrays retain object identity and do not invoke the constructor. Constructor errors and failed result assertions retain effects.",
  source := "base/array.jl:657-657", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.ConvertCheckedIdentityAndErrors, thm := some ``JuliaLean.Proofs.base.array.Completion.ConvertCheckedIdentityAndErrors_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-similar-generic-arguments", juliaFile := "base/array.jl",
  juliaFns := ["_similar_for(c, ::Type{T}, itr, isz, shp) where {T}"],
  statement := "The selected similar method receives the original container and type, with exactly the dimensions promised by this iterator-size overload.",
  source := "base/array.jl:697-697", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.SimilarGenericArguments, thm := some ``JuliaLean.Proofs.base.array.Completion.SimilarGenericArguments_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-similar-length-errors", juliaFile := "base/array.jl",
  juliaFns := ["_similar_shape(itr, ::HasLength)"],
  statement := "A successful length observation must satisfy the Integer assertion. Both an exception and a bad returned type preserve length's resulting state.",
  source := "base/array.jl:700-700", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.SimilarLengthErrors, thm := some ``JuliaLean.Proofs.base.array.Completion.SimilarLengthErrors_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-similar-axes-protocol", juliaFile := "base/array.jl",
  juliaFns := ["_similar_shape(itr, ::HasShape)"],
  statement := "Axis discovery occurs once on the original iterator and preserves the returned axis object, including errors and effects from custom arrays.",
  source := "base/array.jl:701-701", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion.SimilarAxesProtocol, thm := none,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-similar-unknown-arguments", juliaFile := "base/array.jl",
  juliaFns := ["_similar_for(c::AbstractArray, ::Type{T}, itr, ::SizeUnknown, ::Nothing) where {T}"],
  statement := "The selected similar method receives the original container and type, with exactly the dimensions promised by this iterator-size overload.",
  source := "base/array.jl:703-704", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.SimilarUnknownArguments, thm := some ``JuliaLean.Proofs.base.array.Completion.SimilarUnknownArguments_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-similar-length-arguments", juliaFile := "base/array.jl",
  juliaFns := ["_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasLength, len::Integer) where {T}"],
  statement := "The selected similar method receives the original container and type, with exactly the dimensions promised by this iterator-size overload.",
  source := "base/array.jl:705-706", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.SimilarLengthArguments, thm := some ``JuliaLean.Proofs.base.array.Completion.SimilarLengthArguments_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-similar-axes-arguments", juliaFile := "base/array.jl",
  juliaFns := ["_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasShape, axs) where {T}"],
  statement := "The selected similar method receives the original container and type, with exactly the dimensions promised by this iterator-size overload.",
  source := "base/array.jl:707-708", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.SimilarAxesArguments, thm := some ``JuliaLean.Proofs.base.array.Completion.SimilarAxesArguments_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
def entriesArray11 : List JuliaLean.Registry.Entry := [
{ id := "array-one-to-dimension-endpoint", juliaFile := "base/array.jl",
  juliaFns := ["to_dim(d::OneTo)"],
  statement := "For native Int axes, converting a OneTo to a dimension returns its endpoint, including zero.",
  source := "base/array.jl:483-483", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.OneToDimensionEndpoint, thm := some ``JuliaLean.Proofs.base.array.Completion2.OneToDimensionEndpoint_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesArray12 : List JuliaLean.Registry.Entry := [
{ id := "array-invalid-wrap-dimension-error", juliaFile := "base/array.jl",
  juliaFns := ["invalid_wrap_err(len, dims, proddims)"],
  statement := "Invalid wrap throws DimensionMismatch without changing array storage; its message reports the available MemoryRef length, requested array dimensions and product, and explains that the product exceeds the available length.",
  source := "base/array.jl:3244-3247", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.InvalidWrapDimensionError, thm := some ``JuliaLean.Proofs.base.array.Completion2.InvalidWrapDimensionError_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-promoted-literal-arguments", juliaFile := "base/array.jl",
  juliaFns := ["vect(X...)"],
  statement := "A heterogeneous literal discovers its promoted type before forwarding every original value, in order, to the typed literal constructor.",
  source := "base/array.jl:183-186", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.PromotedLiteralArguments, thm := some ``JuliaLean.Proofs.base.array.Completion3.PromotedLiteralArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesArray13 : List JuliaLean.Registry.Entry := [
{ id := "array-sizehint-keyword-type-errors", juliaFile := "base/array.jl",
  juliaFns := ["Core.kwcall(kwargs::NamedTuple{names}, ::typeof(sizehint!), a, sz) where names"],
  statement := "The fallback rejects a non-Bool first keyword before testing shrink, rejecting unknown keywords or calling positional sizehint; storage remains unchanged.",
  source := "base/array.jl:1647-1652", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.SizehintKeywordTypeErrors, thm := some ``JuliaLean.Proofs.base.array.Completion3.SizehintKeywordTypeErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesArray14 : List JuliaLean.Registry.Entry := [
{ id := "array-dimension-suffix-empty", juliaFile := "base/array.jl",
  juliaFns := ["asize_from(a::Array, n)"],
  statement := "A dimension number greater than the immutable rank returns the empty tuple before Int conversion, tuple construction or size observations, retaining comparison effects.",
  source := "base/array.jl:188-188", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.DimensionSuffixEmpty, thm := some ``JuliaLean.Proofs.base.array.Completion4.DimensionSuffixEmpty_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesArray15 : List JuliaLean.Registry.Entry := [
{ id := "array-promote-array-preserves-matching-container", juliaFile := "base/array.jl",
  juliaFns := ["promote_rule(a::Type{Array{T,n}}, b::Type{Array{S,n}}) where {T,n,S}"],
  statement := "Array promotion retains an existing array type when its element type already matches the promoted element type, preferring the left type when both match.",
  source := "base/array.jl:659-659", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.PromoteArrayPreservesMatchingContainer, thm := some ``JuliaLean.Proofs.base.array.Completion4.PromoteArrayPreservesMatchingContainer_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesArray16 : List JuliaLean.Registry.Entry := [
{ id := "array-abstract-constructor-similar-errors", juliaFile := "base/array.jl",
  juliaFns := ["AbstractArray{T,N}(A::AbstractArray{S,N}) where {T,N,S}"],
  statement := "AbstractArray conversion allocates through the source array's similar method before checking axes or copying, retaining similar's errors and effects.",
  source := "base/array.jl:665-665", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion7.AbstractConstructorSimilarErrors, thm := some ``JuliaLean.Proofs.base.array.Completion7.AbstractConstructorSimilarErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesArray17 : List JuliaLean.Registry.Entry := [
{ id := "array-vect-homogeneous", juliaFile := "base/array.jl",
    juliaFns := ["vect(X::T...) where T"],
    statement := "The selected nonempty homogeneous vect overload allocates a fresh vector containing the argument values in order, preserves existing objects, and reports allocation type or size errors without mutation for the entire machine-sized tuple domain.",
    source := "base/array.jl:159-173; doc/src/manual/arrays.md:96-107; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.VectHomogeneousContract,
    thm := none,
    notes := "Existing allocation/slot boundary; physical OOM, GC and empty-memory identity are not modeled. No allocation-success or callee-correctness hypothesis." },
{ id := "array-elsize-array-runtime",
    juliaFile := "base/array.jl",
    juliaFns := ["elsize(::Type{A}) where {T,A<:Array{T}}"],
    statement := "Across the existing native type/layout and RefValue interfaces, Array elsize preserves every error, divergence and state effect; a boxed element uses an eight-byte pointer slot, while a valid inline alignment yields the mathematically least sufficient aligned extent.",
    source := "base/array.jl:218; base/runtime_internals.jl:668-688",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.ElsizeArrayRuntimeSpec,
    thm := none,
    notes := "Composes installed alignedSizeof, uniontypeLayout, datatypeAlignment, alignInt and native Array length. TypeOps, C-call and RefValue operands remain their existing runtime/interface boundaries; no correctness law is assumed. Header validity records necessary native representation constraints, not a complete physical byte-address witness." },
  { id := "array-elsize-ptr-runtime",
    juliaFile := "base/array.jl",
    juliaFns := ["elsize(::Type{Ptr{T}}) where T"],
    statement := "Ptr elsize handles Any, non-DataTypes and datatype layouts in source order, preserving native errors, divergence and resulting state; valid alignments produce the mathematically least sufficient padded payload size.",
    source := "base/array.jl:219-225; base/runtime_internals.jl:642-656",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.ElsizePtrRuntimeSpec,
    thm := none,
    notes := "Composes installed alignedSizeof, uniontypeLayout, datatypeAlignment, alignInt and native Array length. TypeOps, C-call and RefValue operands remain their existing runtime/interface boundaries; no correctness law is assumed. Header validity records necessary native representation constraints, not a complete physical byte-address witness." },
  { id := "array-sizeof-array-runtime",
    juliaFile := "base/array.jl",
    juliaFns := ["sizeof(a::Array)"],
    statement := "For every native-sized Array header projection, sizeof accounts for the mathematical element count times the independently aligned payload stride modulo the native word width, omits union selector bytes, and preserves layout failures and divergence even for empty arrays.",
    source := "base/array.jl:229; base/essentials.jl:12-13,1296",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.SizeofArrayRuntimeSpec,
    thm := none,
    notes := "Composes installed alignedSizeof, uniontypeLayout, datatypeAlignment, alignInt and native Array length. TypeOps, C-call and RefValue operands remain their existing runtime/interface boundaries; no correctness law is assumed. Header validity records necessary native representation constraints, not a complete physical byte-address witness." },
  { id := "array-sizeof-same-count",
    juliaFile := "base/array.jl",
    juliaFns := ["sizeof(a::Array)"],
    statement := "Arrays of the same element type and mathematical element count have the same complete sizeof outcome regardless of shape or rank, including native errors, divergence and final state.",
    source := "base/array.jl:229; base/essentials.jl:12-13,1296",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.SizeofSameCountSpec,
    thm := none,
    notes := "Composes installed alignedSizeof, uniontypeLayout, datatypeAlignment, alignInt and native Array length. TypeOps, C-call and RefValue operands remain their existing runtime/interface boundaries; no correctness law is assumed. Header validity records necessary native representation constraints, not a complete physical byte-address witness." }
]
def entriesArray18 : List JuliaLean.Registry.Entry := [
{ id := "array-similar-414-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Vector{T}) where {T}"],
    statement := "Every valid Vector source requests exactly its source shape and element type through the actual native allocation/header protocol, retaining all dimension/type/byte-size errors and native effects or divergence.",
    source := "base/array.jl:414; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar414NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-415-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Matrix{T}) where {T}"],
    statement := "Every valid Matrix source requests exactly its complete source shape and element type through the actual native allocation/header protocol, retaining all dimension/type/byte-size errors and native effects or divergence.",
    source := "base/array.jl:415; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar415NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-416-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Vector{T}, S::Type) where {T}"],
    statement := "Every valid Vector source requests its shape with the selected new element type through the native allocation/header protocol, including every type/size/native error, partial state and divergence.",
    source := "base/array.jl:416; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar416NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-417-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Matrix{T}, S::Type) where {T}"],
    statement := "Every valid Matrix source requests its complete shape with the selected new element type through the native allocation/header protocol, including every dimension/type/size/native error, partial state and divergence.",
    source := "base/array.jl:417; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar417NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-418-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Array{T}, m::Int) where {T}"],
    statement := "For every native Int length, similar requests a Vector of the source element type and that exact length, with independent negative/zero/native-size rejection and exact native allocation/header outcomes.",
    source := "base/array.jl:418; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar418NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-419-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Array, T::Type, dims::Dims{N}) where {N}"],
    statement := "For every representable native dimension tuple and selected new element type, similar requests exactly that shape and rank; independent dimension/type/byte-size checks and raw native outcomes determine the complete result.",
    source := "base/array.jl:419; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar419NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-420-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(a::Array{T}, dims::Dims{N}) where {T,N}"],
    statement := "For every representable native dimension tuple, similar retains the source element type and requests exactly that shape and rank, including all mathematical dimension/type/byte-size errors and native outcomes.",
    source := "base/array.jl:420; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar420NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." },
  { id := "array-similar-421-native-protocol",
    juliaFile := "base/array.jl", juliaFns := ["similar(::Type{Array{T,N}}, dims::Dims) where {T,N}"],
    statement := "The source Array type rank is discarded: every representable requested dimension tuple selects the result rank and exact shape, retaining the element type and all dimension/type/byte-size/native errors, effects and divergence.",
    source := "base/array.jl:421; base/boot.jl:782-838; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.Similar421NativeContract,
    thm := none,
    notes := "Protocol at existing raw Memory allocation and Core header identity boundaries. No all-None bits payload, allocation-success premise, native correctness law or freshness assertion. Output reference/type/shape fields are constructed concretely; every native failure/state/divergence is preserved." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesArray19 : List JuliaLean.Registry.Entry := [
  { id := "array-new-memory-request", juliaFile := "base/array.jl",
    juliaFns := ["array_new_memory(mem::Memory, newlen::Int)"],
    statement := "Every native requested capacity uses the source Memory element layout and independent mathematical element/byte-size checks, retaining every native allocation outcome and state.",
    source := "base/array.jl:1114; src/genericmemory.c:55-102", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.ArrayNewMemoryRequestInvariant, thm := none }
]
end JuliaLean.Proofs.base.array

