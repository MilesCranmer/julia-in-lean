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

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c

/-- Observable assignment effect of non-atomic unsetting, from native layout fields. -/
def unsetClears (layout : DictLayout) : Bool :=
  isBoxed layout.metadata || (!isUnion layout.metadata && decide (0 ≤ layout.metadata.memoryLayout.firstptr.val))

def expectedUnset {α : Type} (layout : DictLayout) (old : Option α) : Option α :=
  if unsetClears layout then none else old

/-- Pointer-free and isbits-union arrays have an assigned value in every visible slot. -/
def ValidArraySlots {α : Type} (layout : DictLayout) (slots : List (Option α)) : Prop :=
  unsetClears layout = false → ∀ index, index < slots.length → (slots[index]?).join.isSome = true

private def clearingEffect : Effect → Bool
  | .storePointerNull _ _ | .storeBitsZero _ _ | .memsetZero _ _ => true
  | _ => false

private theorem slotEffects_diagonal {α : Type} (effects : List Effect) (index : Nat)
    (slots : Nat → Option α) :
    interpretSlots effects index slots index =
      if effects.any clearingEffect then none else slots index := by
  induction effects generalizing slots with
  | nil => rfl
  | cons effect effects ih =>
    change interpretSlots effects index (interpretSlotEffect index slots effect) index = _
    rw [ih]
    cases effect <;> cases h : effects.any clearingEffect <;>
      simp [List.any_cons, clearingEffect, interpretSlotEffect, h]

private theorem unsetEffects_clears (layout : DictLayout) (index : Nat) :
    (dictUnsetEffects layout index).any clearingEffect = unsetClears layout := by
  unfold dictUnsetEffects
  split <;> rename_i effects he
  all_goals
    cases hb : isBoxed layout.metadata with
    | true =>
      simp only [memoryrefUnsetProgram, hb, Bool.true_eq_false, Bool.false_eq_true,
        ite_true, pure, Except.pure] at he
      all_goals cases he
      all_goals simp [unsetClears, hb, clearingEffect]
    | false =>
      cases hu : isUnion layout.metadata with
      | true =>
        simp [memoryrefUnsetProgram, hb, hu, pure, Except.pure] at he
        all_goals cases he
        all_goals simp [unsetClears, hb, hu]
      | false =>
        by_cases hp : layout.metadata.memoryLayout.firstptr.val < 0
        · simp [memoryrefUnsetProgram, hb, hu, hp, pure, Except.pure] at he
          all_goals cases he
          all_goals simp [unsetClears, hb, hu, show ¬ 0 ≤ layout.metadata.memoryLayout.firstptr.val by omega]
        · obtain ⟨dt, hdt⟩ := layout.inlineDatatype hb hu (by omega)
          simp [memoryrefUnsetProgram, hb, hu, hp, hdt, layout.unlocked,
            pure, Except.pure, bind, Except.bind] at he
          all_goals
            cases he
            simp [unsetClears, hb, hu, clearingEffect, List.any_append,
              List.any_map, show 0 ≤ layout.metadata.memoryLayout.firstptr.val by omega]

theorem unsetCell_result {α : Type} (layout : DictLayout) (index : Nat) (old : Option α) :
    unsetCell layout index old = expectedUnset layout old := by
  change interpretSlots (dictUnsetEffects layout (index - 1)) index (fun _ => old) index = _
  rw [slotEffects_diagonal, unsetEffects_clears]
  rfl

/-- The native layout of Int64 indices produced by membership/findin helpers. -/
def int64ElementLayout : JuliaLean.base.runtime_internals.DataTypeLayout :=
  nativeLayout 8 0 0 (-1) 8 128

def int64RuntimeMetadata : Metadata :=
  { runtimeType :=
      { identity := 4
        layout := genericMemoryHeader 8 8 0 (-1)
        elementType := .datatype ⟨int64ElementLayout, int64ElementLayout, fun _ => 0⟩
        elementTag := .bitInteger .i64
        kind := .notAtomic }
    typeofBottom := none
    owner := 0
    mutexBytes := 0 }

def int64RuntimeLayout : DictLayout where
  metadata := int64RuntimeMetadata
  nonAtomicKind := rfl
  nonAtomicFlag := rfl
  unlocked := rfl
  inlineDatatype := by
    intro _ _ _
    exact ⟨⟨int64ElementLayout, int64ElementLayout, fun _ => 0⟩, rfl⟩
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.round6e
open JuliaLean

abbrev I := JInt .i64
abbrev U := JInt .u64
abbrev Byte := JInt .u8

structure Memory (T : Type) extends JuliaLean.base.pointer.PointerMemoryObject T where
  identity : Nat
  capacity : Nat

abbrev Ref (T : Type) := JuliaLean.base.genericmemory.GenericMemoryRef (Memory T) U

structure ArrayObject (T : Type) where
  identity : Nat
  ref : Ref T
  dimensions : List I

structure World (σ : Type) where
  bytes : JuliaLean.base.pointer.ByteHeap
  nextMemory : Nat
  nextArray : Nat
  other : σ

abbrev M (ε σ α : Type) :=
  ExceptT (Sum JuliaLean.base.array.Error ε) (StateM (World σ)) α

/-- `ptr_or_offset` is an element offset for a union or a zero-size layout. -/
def memoryref (memory : Memory T) : Ref T :=
  ⟨memory, if memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0 then JInt.wrap .u64 0
    else memory.ptr.address⟩

def pointer (reference : Ref T) : JuliaLean.base.pointer.Ptr Unit :=
  JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid
    ⟨reference.mem.toPointerMemoryObject, reference.ptr_or_offset⟩

def payloadAddress (reference : Ref T) (byte : Nat) : Nat :=
  JuliaLean.base.pointer.addressMod ((pointer reference).address.val.toNat + byte)

def payload (heap : JuliaLean.base.pointer.ByteHeap) (reference : Ref T) (n : Nat) : List Byte :=
  (List.range (n * reference.mem.layoutBytes.val.toNat)).map
    (fun byte => heap.readByte (payloadAddress reference byte))

/-- Scalar dimension multiplication uses the installed variadic and integer models. -/
def nativeMultiply (values : List I) : I :=
  match values with
  | [] => JuliaLean.base.tuple.prodEmpty
  | [x] => JuliaLean.base.operators.unaryMulNumber x
  | [x, y] => JuliaLean.base.int.binop JuliaLean.base.int.mul x y
  | x :: y :: z :: rest =>
    (JuliaLean.base.operators.naryOperator (Acc := fun _ : Unit => I)
      (Elem := fun _ : Unit => I)
      (fun (a b : I) => JuliaLean.base.int.binop JuliaLean.base.int.mul a b)
      (fun (ab c : I) => ⟨(), JuliaLean.base.int.binop JuliaLean.base.int.mul ab c⟩)
      (fun acc value => ⟨(), JuliaLean.base.int.binop JuliaLean.base.int.mul acc.2 value.2⟩)
      x y z (rest.map (fun value => ⟨(), value⟩))).2

def nativeProduct (dimensions : List I) : I :=
  match dimensions with
  | [] => JuliaLean.base.tuple.prodEmpty
  | _ :: _ => JuliaLean.base.tuple.prodIntTuple nativeMultiply dimensions

def size (array : ArrayObject T) : List I :=
  JuliaLean.base.essentials.sizeArray (fun value _ => value.dimensions) array

def length (array : ArrayObject T) : I :=
  match array.dimensions with
  | [dimension] => JuliaLean.base.essentials.lengthArray1
      (fun (_ : ArrayObject T) (_ : String) => dimension)
      (fun (value : I) (_ : Nat) => value) array
  | _ => JuliaLean.base.essentials.lengthAbstract size nativeProduct array

def newArray (reference : Ref T) (dimensions : List I) : M ε σ (ArrayObject T) := do
  let old ← get
  set { old with nextArray := old.nextArray + 1 }
  pure ⟨old.nextArray, reference, dimensions⟩
end JuliaLean.Proofs.base.array.round6e


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def literalFilterCollectOps {m : Type → Type} [Monad m] {E T B : Type}
    (defaultB : m B) (literal : List E → m B) :
    TypedCollectOps m (FilterGenerator m (List E) E) E T Unit Unit B where
  size _ := ()
  sized _ := true
  unknown _ := false
  shape _ _ := pure ()
  arrayForInner _ _ _ := defaultB
  copyto _ g := do literal (← g.iter.itr.filterM g.iter.flt)
  emptyVector _ := defaultB
  push _ _ := pure ()

/-- A single fresh allocation's reference slots. These primitives belong to
`essentials.jl` and `memory.jl`; stores in literals use array.jl's safe setter. -/
abbrev LiteralM (α : Type) := StateM (List (Option α))

def literalAllocate (n : I) : LiteralM α Unit :=
  fun _ => ((), List.replicate n.val.toNat none)

def literalRef (_a : A) (i : I) (_checked : Bool) : LiteralM α I := fun slots => (i, slots)

def literalStore (i : I) (x : α) (_checked : Bool) : LiteralM α Unit :=
  fun slots => ((), slots.set (i.val - 1).toNat (some x))

theorem literal_counter (k : Nat) (hk : k + 1 < 2 ^ 63) :
    (JInt.wrap .i64 (k + 1)).val = k + 1 := by
  change wrapInt .i64 ((k : Int) + 1) = (k : Int) + 1
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  omega

theorem literal_write_tail (tail done : List α) (handle : A)
    (hn : done.length + tail.length < 2 ^ 63) :
    ((tail.foldlM (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (JInt.wrap .i64 (done.length + 1), handle)).run
        (done.map some ++ List.replicate tail.length none)).2 =
      (done ++ tail).map some := by
  induction tail generalizing done with
  | nil =>
    simp only [List.foldlM_nil, List.length_nil, List.replicate_zero, List.append_nil]
    rfl
  | cons x tail ih =>
    have hi := literal_counter done.length (by simp only [List.length_cons] at hn; omega)
    have hnext : JInt.wrap .i64 (done.length + 1) + one =
        JInt.wrap .i64 ((done ++ [x]).length + 1) := by
      apply Subtype.ext
      change wrapInt .i64 ((JInt.wrap .i64 (done.length + 1)).val + one.val) = _
      rw [hi]
      rw [show one.val = 1 from rfl]
      change wrapInt .i64 ((done.length : Int) + 1 + 1) =
        wrapInt .i64 (((done ++ [x]).length : Int) + 1)
      apply congrArg (wrapInt .i64)
      simp only [List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_one]
    have hslot :
        (done.map some ++ List.replicate (x :: tail).length none).set
          ((JInt.wrap .i64 (done.length + 1)).val - 1).toNat (some x) =
          (done ++ [x]).map some ++ List.replicate tail.length none := by
      rw [hi]
      simp [List.length_map, List.replicate_succ, List.map_append, List.append_assoc]
    have hind := ih (done ++ [x]) (by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hn
      omega)
    rw [List.foldlM_cons]
    change ((tail.foldlM (m := LiteralM α) (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (JInt.wrap .i64 (done.length + 1) + one, handle)).run
      ((done.map some ++ List.replicate (x :: tail).length none).set
        ((JInt.wrap .i64 (done.length + 1)).val - 1).toNat (some x))).2 = _
    rw [hslot, hnext]
    simpa only [List.append_assoc, List.singleton_append] using hind

def LiteralContents : Prop := ∀ (α : Type) (xs : List α) (old : List (Option α)),
  xs.length < 2 ^ 63 →
  (vectTyped literalAllocate (safeSetindex1057 literalRef literalStore) xs).run old =
    ((), xs.map some) ∧
  (typedLiteral literalAllocate (safeSetindex1057 literalRef literalStore) true xs).run old =
    ((), xs.map some) ∧
  (typedLiteral literalAllocate (safeSetindex1057 literalRef literalStore) false xs).run old =
    ((), xs.map some) ∧
  (anyLiteral literalAllocate (safeSetindex1055 literalRef literalStore) xs).run old =
    ((), xs.map some)

theorem state_unit_finish (action : StateM σ (β × Unit)) (state : σ) :
    ((do let (_, a) ← action; pure a) : StateM σ Unit).run state =
      ((), (action.run state).2) := by
  rfl

theorem vectTyped_state_run (allocate : I → StateM σ A)
    (store : A → α → I → StateM σ A) (xs : List α) (state : σ) :
    (vectTyped allocate store xs).run state =
      (writeValues store ((allocate (JInt.wrap .i64 xs.length)).run state).1 xs).run
        ((allocate (JInt.wrap .i64 xs.length)).run state).2 := by
  rfl

theorem typedLiteral_eq_vect [Monad m] (allocate : I → m A)
    (store : A → α → I → m A) (homogeneous : Bool) (xs : List α) :
    typedLiteral allocate store homogeneous xs = vectTyped allocate store xs := by
  cases homogeneous <;> rfl

theorem anyLiteral_eq_vect [Monad m] (allocate : I → m A)
    (store : A → α → I → m A) (xs : List α) :
    anyLiteral allocate store xs = vectTyped allocate store xs := by
  rfl

theorem literalContents : LiteralContents := by
  intro α xs old hn
  have hlen : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
    change wrapInt .i64 (xs.length : Int) = xs.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have h := literal_write_tail xs [] () (by simpa using hn)
  simp only [List.length_nil, Int.natCast_zero, Int.zero_add, List.map_nil,
    List.nil_append] at h
  have hw : (writeValues (safeSetindex1057 literalRef literalStore) () xs).run
      (List.replicate xs.length none) = ((), xs.map some) := by
    rw [writeValues, state_unit_finish]
    exact congrArg (fun s => ((), s)) h
  have ha : (literalAllocate (α := α) (JInt.wrap .i64 xs.length)).run old =
      ((), List.replicate xs.length none) := by
    change ((), List.replicate (JInt.wrap .i64 xs.length).val.toNat none) = _
    rw [hlen, Int.toNat_natCast]
  have hv : (vectTyped literalAllocate (safeSetindex1057 literalRef literalStore) xs).run old =
      ((), xs.map some) := by
    rw [vectTyped_state_run, ha]
    exact hw
  refine ⟨hv, ?_, ?_, ?_⟩
  · rw [typedLiteral_eq_vect]
    exact hv
  · rw [typedLiteral_eq_vect]
    exact hv
  · rw [anyLiteral_eq_vect]
    exact hv

/-- Fixed-length, one-based memory primitives from essentials.jl and memory.jl. -/
abbrev SlotM (α : Type) := ExceptT Error (StateM (I → Option α))

def updateSlot (slots : I → Option α) (i : I) (value : Option α) : I → Option α :=
  fun j => if j = i then value else slots j

def slotBounds (n : Nat) (_a : Unit) (i : I) : SlotM α Unit :=
  fun slots => (if 1 ≤ i.val ∧ i.val ≤ (n : Int) then .ok () else .error .bounds, slots)

def slotRefNew (_a : Unit) (i : I) (_checked : Bool) : SlotM α I :=
  fun slots => (.ok i, slots)

def slotStore (i : I) (x : α) (_checked : Bool) : SlotM α Unit :=
  fun slots => (.ok (), updateSlot slots i (some x))

def slotLift (value : Except Error α) : SlotM β α := fun slots => (value, slots)

theorem mapM_ok_of_mem (f : α → Except Error β) (g : α → β) (xs : List α)
    (h : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

/-- Lift a non-throwing state action into a state computation that can fail. -/
def liftLiteralState (action : StateM σ α) : StateT σ (Except Error) α :=
  fun state => .ok (action.run state)

theorem fold_converted_state (step : S → α → StateM σ S)
    (convert : β → Except Error α) (xs : List β) (start : S) (state : σ) :
    (xs.foldlM (fun s x => do
      let y ← StateT.lift (convert x)
      liftLiteralState (step s y)) start).run state =
      (do
        let ys ← xs.mapM convert
        pure ((ys.foldlM step start).run state) : Except Error (S × σ)) := by
  induction xs generalizing start state with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldlM_cons, List.mapM_cons]
    cases hc : convert x with
    | error e =>
      simp [StateT.lift, StateT.run, StateT.bind, Except.bind, Bind.bind]
    | ok y =>
      cases hs : step start y state with
      | mk next state' =>
        have h := ih next state'
        cases ht : xs.mapM convert <;>
          simpa [StateT.run_bind, StateT.lift, hc, ht, hs, liftLiteralState,
            StateT.run, StateT.bind, Except.bind, Except.pure, Bind.bind, Pure.pure,
            List.foldlM_cons] using h

theorem state_finish [Monad m] [LawfulMonad m] (action : StateT σ m (β × A)) (state : σ) :
    ((do let (_, a) ← action; pure a) : StateT σ m A).run state =
      (fun p => (p.1.2, p.2)) <$> (action.run state) := by
  simp only [bind_pure_comp, StateT.run_map]

def convertedLiteralSetter (convert : β → Except Error α) :
    A → β → I → StateT (List (Option α)) (Except Error) A :=
  safeSetindexConvert (fun x => StateT.lift (convert x))
    (safeSetindex1057 (fun a i b => liftLiteralState (literalRef a i b))
      (fun i x b => liftLiteralState (literalStore i x b)))

theorem converted_literal_step (convert : β → Except Error α) (p : I × A) (x : β) :
    (do
      let a ← convertedLiteralSetter convert p.2 x p.1
      pure (p.1 + one, a)) =
    (do
      let y ← StateT.lift (convert x)
      liftLiteralState (do
        let a ← safeSetindex1057 literalRef literalStore p.2 y p.1
        pure (p.1 + one, a))) := by
  funext state
  cases hc : convert x <;>
    simp [convertedLiteralSetter, safeSetindexConvert, safeSetindex1057,
      liftLiteralState, literalRef, literalStore, hc, StateT.run, StateT.bind,
      StateT.lift, StateT.pure, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem converted_length (convert : β → Except Error α) (xs : List β)
    (ys : List α) (h : xs.mapM convert = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst ys
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hc : convert x <;> cases ht : xs.mapM convert <;>
      simp [hc, ht, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    subst ys
    simp only [List.length_cons]
    rw [ih _ ht]

def literalAllocateAs (handle : A) (n : I) : LiteralM α A :=
  fun _ => (handle, List.replicate n.val.toNat none)

theorem literal_keeps_handle (xs : List α) (i : I) (handle : A) (old : List (Option α)) :
    ((xs.foldlM (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (i, handle)).run old).1.2 = handle := by
  induction xs generalizing i old with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldlM_cons]
    change ((xs.foldlM (m := LiteralM α) (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (i + one, handle)).run
      (old.set (i.val - 1).toNat (some x))).1.2 = handle
    exact ih (i + one) _

def ConvertedLiteralContents : Prop := ∀ (α β A : Type) (handle : A)
    (convert : β → Except Error α) (homogeneous : Bool) (xs : List β) (old : List (Option α)),
  xs.length < 2 ^ 63 →
  (typedLiteral (fun n => liftLiteralState (literalAllocateAs handle n))
    (convertedLiteralSetter convert) homogeneous xs).run old =
      (xs.mapM convert).map (fun ys => (handle, ys.map some))

theorem except_ok_bind (x : S) (f : S → Except Error A) :
    (Except.ok x >>= f) = f x := by rfl

theorem except_finish (value : Except Error S) (f : S → A) (g : A → B) :
    g <$> (do let x ← value; pure (f x)) = value.map (fun x => g (f x)) := by
  cases value <;> rfl

theorem vectTyped_fallible_run (handle : A) (store : A → β → I →
    StateT (List (Option α)) (Except Error) A) (xs : List β) (old : List (Option α)) :
    (vectTyped (fun n => liftLiteralState (literalAllocateAs handle n)) store xs).run old =
      (writeValues store handle xs).run
        (List.replicate (JInt.wrap .i64 xs.length).val.toNat none) := by
  have ha : (liftLiteralState (literalAllocateAs (α := α) handle
      (JInt.wrap .i64 xs.length))).run old =
        .ok (handle, List.replicate (JInt.wrap .i64 xs.length).val.toNat none) := by
    rfl
  rw [vectTyped, StateT.run_bind, ha, except_ok_bind]

theorem convertedLiteralContents : ConvertedLiteralContents := by
  intro α β A handle convert homogeneous xs old hn
  rw [typedLiteral_eq_vect]
  have hlen : (JInt.wrap .i64 (xs.length : Int)).val.toNat = xs.length := by
    have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
      change wrapInt .i64 (xs.length : Int) = xs.length
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega
    rw [hv, Int.toNat_natCast]
  rw [vectTyped_fallible_run, hlen]
  rw [writeValues, state_finish]
  simp only [converted_literal_step]
  rw [fold_converted_state, except_finish]
  cases hc : xs.mapM convert with
  | error e => rfl
  | ok ys =>
    have hy : ys.length = xs.length := converted_length convert xs ys hc
    have hw := literal_write_tail ys [] handle (by simp only [List.length_nil, Nat.zero_add, hy]; exact hn)
    simp only [List.length_nil, Int.natCast_zero, Int.zero_add, List.map_nil, List.nil_append] at hw
    simp only [Except.map]
    apply congrArg Except.ok
    apply Prod.ext
    · exact literal_keeps_handle ys one handle _
    · simpa only [hy, one] using hw

abbrev CopyM (α : Type) := ExceptT Error (StateM (Nat → Option α))

@[simp] theorem stateExcept_pure (x : β) (old : σ) :
    (pure x : ExceptT Error (StateM σ) β).run old = (.ok x, old) := rfl

@[simp] theorem stateExcept_bind (action : ExceptT Error (StateM σ) β)
    (next : β → ExceptT Error (StateM σ) γ) (old : σ) :
    (action >>= next).run old =
      match action.run old with
      | (.error e, state) => (.error e, state)
      | (.ok x, state) => (next x).run state := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action old with
  | mk r state =>
    cases r <;> rfl

@[simp] theorem stateExcept_throw (e : Error) (old : σ) :
    (throw e : ExceptT Error (StateM σ) β).run old = (.error e, old) := rfl

theorem copy_remaining (len : Nat) (i : Int) (hlen : len < 2 ^ 63)
    (hi : 1 ≤ i ∧ i ≤ (len : Int)) :
    (JInt.wrap .i64 ((JInt.wrap .i64 len).val - i) + one).val =
      (len : Int) - i + 1 := by
  have hl : (JInt.wrap .i64 len).val = len := by
    change wrapInt .i64 (len : Int) = len
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
    omega
  have hs : (JInt.wrap .i64 ((len : Int) - i)).val = (len : Int) - i := by
    change wrapInt .i64 ((len : Int) - i) = (len : Int) - i
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
    omega
  change wrapInt .i64 ((JInt.wrap .i64 ((JInt.wrap .i64 len).val - i)).val + one.val) = _
  rw [hl, hs]
  change wrapInt .i64 ((len : Int) - i + 1) = _
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
  omega

theorem fill_loop {K α : Type} [DecidableEq K] (keys : List K)
    (step : K → ExceptT Error (StateM (K → Option α)) Unit) (x : α)
    (hlaw : ∀ old i, i ∈ keys →
      (step i).run old = (.ok (), fun j => if j = i then some x else old j))
    (old : K → Option α) :
    (forIn keys () (fun i _ => do step i; pure (ForInStep.yield ()))).run old =
      (.ok (), fun j => if j ∈ keys then some x else old j) := by
  induction keys generalizing old with
  | nil =>
    simp [ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.pure, Pure.pure]
  | cons i keys ih =>
    have hstep := hlaw old i (by simp)
    have htail : ∀ old i, i ∈ keys →
        (step i).run old = (.ok (), fun j => if j = i then some x else old j) := by
      intro old j hj
      exact hlaw old j (by simp [hj])
    simp only [List.forIn_cons, stateExcept_bind, stateExcept_pure, hstep]
    rw [ih htail]
    congr 1
    funext j
    by_cases hj : j = i <;> simp [List.mem_cons, hj]

def stateExceptLift {σ β : Type} (value : Except Error β) : ExceptT Error (StateM σ) β :=
  fun state => (value, state)

@[simp] theorem stateExceptLift_run (value : Except Error β) (old : σ) :
    (stateExceptLift value).run old = (value, old) := rfl

abbrev arrayShapeFiller {A α : Type} (shape : A → List Nat) (indices : List Nat → List I) :=
  fillBang (fun _ : α => true) id (fun x => (pure x : SlotM α α))
    (fillTyped (fun a => (pure (indices (shape a)) : SlotM α (List I)))
      (fun a x i => do
        let _ ← setindexScalar (fun _ : α => true) id (fun x => (pure x : SlotM α α))
          (setindexTyped (fun a i => slotBounds (shape a).prod () i)
            (fun _ i checked => slotRefNew () i checked) slotStore) a x i
        pure ()))

def filledShape (old : I → Option α) (dims : List Nat) (x : α) : I → Option α :=
  fun j => if 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int) then some x else old j

theorem arrayShapeFiller_run {A α : Type} (shape : A → List Nat)
    (indices : List Nat → List I)
    (hindices : ∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int))
    (a : A) (hdims : (shape a).prod < 2 ^ 63) (x : α) (old : I → Option α) :
    (arrayShapeFiller shape indices a x).run old =
      (.ok a, filledShape old (shape a) x) := by
  let step := fun i => do
    let _ ← setindexScalar (fun _ : α => true) id (fun x => (pure x : SlotM α α))
      (setindexTyped (fun a i => slotBounds (shape a).prod () i)
        (fun _ i checked => slotRefNew () i checked) slotStore) a x i
    pure ()
  have hs : ∀ state i, i ∈ indices (shape a) →
      (step i).run state = (.ok (), fun j => if j = i then some x else state j) := by
    intro state i hi
    have hb := (hindices (shape a) hdims i).mp hi
    simp [step, setindexScalar, setindexTyped, slotBounds, slotRefNew, slotStore,
      hb, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    rfl
  have hloop := fill_loop (indices (shape a)) step x hs old
  simp only [hindices (shape a) hdims] at hloop
  simp only [arrayShapeFiller, fillBang, ite_true, fillTyped,
    stateExcept_bind, stateExcept_pure]
  simp only [step, id_eq] at hloop ⊢
  rw [hloop]
  rfl

def dimensionArgument (d : Sum Z Z) : Z :=
  match d with
  | .inl integer => toDimInteger integer
  | .inr endpoint => toDimOneTo id endpoint

def validAllocationDimensions (value : Z → Int) (dims : List Z) : Prop :=
  (∀ d ∈ dims, 0 ≤ value d ∧ value d ≤ IntTy.i64.max) ∧
    (dims.map value).prod ≤ IntTy.i64.max

/-- A non-OneTo range axis selects the generic similar interface from abstractarray.jl. -/
inductive ConstructorAxis (Z : Type) where
  | integer : Z → ConstructorAxis Z
  | oneTo : Z → ConstructorAxis Z
  | range : Z → Z → ConstructorAxis Z

def unsupportedAxis : ConstructorAxis Z → Prop
  | .range _ _ => True
  | _ => False

def TaggedAllocationShapeLaw (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)) : Prop :=
  ∀ old t dims a fresh, (allocate t dims).run old = (.ok a, fresh) →
    a = (t, dims.map (fun d => (value d).toNat)) ∧ a.2.prod < 2 ^ 63

def constantArrayResult (value : Z → Int) (t : T) (dims : List Z)
    (allocation : Except Error (T × List Nat) × (I → Option α))
    (element : Except Error α) : Except Error (T × List Nat) × (I → Option α) :=
  match allocation with
  | (.error e, fresh) => (.error e, fresh)
  | (.ok _, fresh) =>
    match element with
    | .error e => (.error e, fresh)
    | .ok x =>
      let shape := dims.map (fun d => (value d).toNat)
      (.ok (t, shape), filledShape fresh shape x)

def ConstantArraySpec : Prop :=
  ∀ (α T Z : Type) (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)),
    TaggedAllocationShapeLaw value allocate →
    ∀ (element : T → Except Error α) (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (t : T) (dims : List Z) (old : I → Option α),
    let typed := fun t dims => constant637 (allocate t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims
    ∀ action ∈ [typed t dims, constantTypedVarargs typed t dims,
      constant642 (allocate t) (stateExceptLift (element t)) (arrayShapeFiller Prod.snd indices) dims,
      constant647 (similar421 (similar420 (allocate t) ())) (stateExceptLift (element t))
        (arrayShapeFiller Prod.snd indices) dims,
      constantDefaultType t typed dims, constantVarargs (constantDefaultType t typed) dims],
      action.run old = constantArrayResult value t dims ((allocate t dims).run old) (element t)

theorem constantArraySpec : ConstantArraySpec := by
  intro α T Z value allocate halloc element indices hindices t dims old typed action hop
  have hcore : (typed t dims).run old =
      constantArrayResult value t dims ((allocate t dims).run old) (element t) := by
    cases ha : (allocate t dims).run old with
    | mk result fresh =>
      cases result with
      | error e =>
        simp only [typed, constant637, stateExcept_bind, ha, constantArrayResult]
      | ok a =>
        obtain ⟨hshape, hn⟩ := halloc old t dims a fresh ha
        cases he : element t with
        | error e =>
          simp only [typed, constant637, stateExcept_bind, stateExceptLift_run,
            ha, he, constantArrayResult]
        | ok x =>
          simp only [typed, constant637, stateExcept_bind, stateExcept_pure,
            stateExceptLift_run, ha, he, constantArrayResult]
          rw [arrayShapeFiller_run Prod.snd indices hindices a hn x fresh]
          simp only [hshape]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcore

def UnsupportedConstantAxesSpec : Prop :=
  ∀ (α T Z : Type)
    (similarAxes : T → List (ConstructorAxis Z) → SlotM α (T × List Nat)),
    (∀ old t dims, (∃ d ∈ dims, unsupportedAxis d) →
      (similarAxes t dims).run old = (.error (.method "similar"), old)) →
    ∀ (element : T → Except Error α) (indices : List Nat → List I)
      (t : T) (dims : List (ConstructorAxis Z)) (old : I → Option α),
    (∃ d ∈ dims, unsupportedAxis d) →
    (constant647 (similarAxes t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims).run old = (.error (.method "similar"), old)

def TaggedCheckedAllocationLaw (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)) : Prop :=
  TaggedAllocationShapeLaw value allocate ∧
  (∀ old t dims, validAllocationDimensions value dims →
    ∃ fresh, (allocate t dims).run old = (.ok (t, dims.map (fun d => (value d).toNat)), fresh)) ∧
  (∀ old t dims, (∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, value d < 0) →
    ∃ message, (allocate t dims).run old = (.error (.argument message), old)) ∧
  (∀ old t dims, (∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
    (allocate t dims).run old = (.error .inexact, old))

def DocumentedConstantDimensionsSpec : Prop :=
  ∀ (α T Z : Type) (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)),
    TaggedCheckedAllocationLaw value allocate →
    ∀ (element : T → Except Error α) (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (t : T) (dims : List Z) (old : I → Option α),
    let typed := fun t dims => constant637 (allocate t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims
    let actions := [typed t dims, constantTypedVarargs typed t dims,
      constant642 (allocate t) (stateExceptLift (element t)) (arrayShapeFiller Prod.snd indices) dims,
      constant647 (similar421 (similar420 (allocate t) ())) (stateExceptLift (element t))
        (arrayShapeFiller Prod.snd indices) dims,
      constantDefaultType t typed dims, constantVarargs (constantDefaultType t typed) dims]
    (∀ x, element t = .ok x → validAllocationDimensions value dims →
      ∃ fresh, ∀ action ∈ actions, action.run old =
        (.ok (t, dims.map (fun d => (value d).toNat)),
          filledShape fresh (dims.map (fun d => (value d).toNat)) x)) ∧
    ((∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
      (∃ d ∈ dims, value d < 0) →
      ∃ message, ∀ action ∈ actions, action.run old = (.error (.argument message), old)) ∧
    ((∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
      ∀ action ∈ actions, action.run old = (.error .inexact, old))

@[simp] theorem vector_pure_run (x : β) (heap : VectorHeap α) :
    (pure x : VectorM α β).run heap = .ok (x, heap) := rfl

@[simp] theorem vector_bind_run (action : VectorM α β) (next : β → VectorM α γ)
    (heap : VectorHeap α) :
    (action >>= next).run heap =
      match action.run heap with
      | .error e => .error e
      | .ok (x, state) => (next x).run state := by
  simp only [StateT.run, StateT.bind, Bind.bind, Except.bind]
  cases h : action heap with
  | error e => rfl
  | ok pair => cases pair; rfl

@[simp] theorem vector_throw_run (e : Error) (heap : VectorHeap α) :
    (throw e : VectorM α β).run heap = .error e := rfl

@[simp] theorem vector_lift_run (value : Except Error β) (heap : VectorHeap α) :
    (liftM value : VectorM α β).run heap = value.map (fun x => (x, heap)) := by
  cases value <;> rfl

@[simp] theorem vector_modify_run (f : VectorHeap α → VectorHeap α) (heap : VectorHeap α) :
    (modify f : VectorM α Unit).run heap = .ok ((), f heap) := rfl

@[simp] theorem vector_get_run (heap : VectorHeap α) :
    (get : VectorM α (VectorHeap α)).run heap = .ok (heap, heap) := rfl

@[simp] theorem heapSlots_run (handle : Nat) (heap : VectorHeap α) :
    (heapSlots handle).run heap =
      match heap[handle]? with
      | none => .error .bounds
      | some slots => .ok (slots, heap) := by
  simp only [heapSlots, vector_bind_run, vector_get_run]
  cases heap[handle]? <;> rfl

@[simp] theorem heapLength_run (handle : Nat) (heap : VectorHeap α) :
    (heapLength handle).run heap =
      match heap[handle]? with
      | none => .error .bounds
      | some slots => .ok (JInt.wrap .i64 slots.length, heap) := by
  simp only [heapLength, vector_bind_run, heapSlots_run]
  cases heap[handle]? <;> rfl

@[simp] theorem heapBounds_run (handle : Nat) (i : I) (heap : VectorHeap α) :
    (heapBounds handle i).run heap =
      match heap[handle]? with
      | none => .error .bounds
      | some slots =>
        if 1 ≤ i.val ∧ i.val ≤ (slots.length : Int) then .ok ((), heap) else .error .bounds := by
  simp only [heapBounds, vector_bind_run, heapSlots_run]
  cases heap[handle]? with
  | none => rfl
  | some slots =>
    by_cases hb : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int) <;>
      simp only [hb, and_self, decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, vector_pure_run, vector_throw_run]

theorem heapCopyReferences_whole_run (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : Nat) (xs ys : List (Option α))
    (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (hlen : ys.length = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapCopyReferences convert (dest, one) (src, one) (JInt.wrap .i64 xs.length)).run heap =
      (xs.mapM convert).map (fun values => ((), heap.set dest values)) := by
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
    change wrapInt .i64 (xs.length : Int) = xs.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  have hb : 0 ≤ (xs.length : Int) ∧ 1 ≤ (1 : Int) ∧
      (1 : Int) - 1 + xs.length ≤ ys.length ∧
      1 ≤ (1 : Int) ∧ (1 : Int) - 1 + xs.length ≤ xs.length := by omega
  simp only [heapCopyReferences, vector_bind_run, heapSlots_run,
    hsrc, hdest, hv, hlen, show one.val = 1 from rfl,
    Int.sub_self, Int.zero_add, Int.le_refl, Int.natCast_nonneg, and_self,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    Int.toNat_zero, Int.toNat_natCast, List.drop_zero, List.take_length, vector_lift_run]
  cases hc : xs.mapM convert with
  | error e => simp only [Except.map]
  | ok values =>
    have hdrop : ys.drop xs.length = [] := by rw [← hlen]; exact List.drop_length
    simp only [Except.map, List.take_zero, hdrop,
      List.nil_append, List.append_nil, vector_modify_run]

theorem heapCheckedCopy_zero_eq (convert : Option α → Except Error (Option α))
    (dest src : Nat) (di si n : I) (hn : n.val = 0) :
    heapCheckedCopy convert dest di src si n = pure dest := by
  simp only [heapCheckedCopy, copyto288, copytoImpl, hn, decide_true, pure_bind, ite_true]

theorem heapCheckedCopy_positive_eq (convert : Option α → Except Error (Option α))
    (dest src : Nat) (di si n : I) (hn : 0 < n.val) :
    heapCheckedCopy convert dest di src si n = (do
      heapBounds dest di
      if !(n.val ≤ ((← heapLength dest) - di + one).val) then
        let _ ← heapLength dest
        return Empty.elim (← throw .bounds)
      heapBounds src si
      if !(n.val ≤ ((← heapLength src) - si + one).val) then
        let _ ← heapLength src
        return Empty.elim (← throw .bounds)
      heapCopyReferences convert (dest, di) (src, si) n
      pure dest) := by
  have hn0 : n.val ≠ 0 := by omega
  simp only [heapCheckedCopy, copyto288, copytoImpl, hn0, hn, decide_true, decide_false,
    Bool.not_true, Bool.false_eq_true, ite_false, heapReference, pure_bind, bind_assoc]

theorem heapWholeCopy_run (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : Nat) (xs ys : List (Option α))
    (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (hlen : ys.length = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapWholeCopy convert dest src).run heap =
      if xs = [] then .ok (dest, heap)
      else (xs.mapM convert).map (fun values => (dest, heap.set dest values)) := by
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
    change wrapInt .i64 (xs.length : Int) = xs.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  simp only [heapWholeCopy, copyto325, copyto2arg, vector_bind_run,
    vector_pure_run, heapLength_run, hsrc]
  by_cases hz : xs = []
  · simp only [ite_eq_left hz]
    rw [heapCheckedCopy_zero_eq convert dest src one one (JInt.wrap .i64 xs.length)
      (by rw [hv]; simp only [hz, List.length_nil, Int.natCast_zero])]
    exact vector_pure_run _ _
  · have hp : 0 < xs.length := List.length_pos_iff.mpr hz
    have hbi : 1 ≤ (1 : Int) ∧ (1 : Int) ≤ xs.length := by omega
    have hsrem := copy_remaining xs.length 1 hn hbi
    have hn0 : (xs.length : Int) ≠ 0 := by omega
    simp only [ite_eq_right hz]
    rw [heapCheckedCopy_positive_eq convert dest src one one (JInt.wrap .i64 xs.length)
      (by rw [hv]; omega)]
    have hremain : (JInt.wrap .i64 (xs.length : Int) - one + one).val = xs.length := by
      change (JInt.wrap .i64 ((JInt.wrap .i64 (xs.length : Int)).val - one.val) + one).val = _
      rw [show one.val = 1 from rfl]
      simpa only [Int.sub_add_cancel] using hsrem
    simp only [vector_bind_run, vector_pure_run, heapLength_run, heapBounds_run,
      hsrc, hdest, hlen, hv, show one.val = 1 from rfl, hbi, hremain, Int.le_refl,
      and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [heapCopyReferences_whole_run convert heap dest src xs ys hsrc hdest hlen hn]
    cases xs.mapM convert <;> simp only [Except.map]

@[simp] theorem heapAllocate_run (n : Nat) (heap : VectorHeap α) :
    (heapAllocate n).run heap = .ok (heap.length, heap ++ [List.replicate n none]) := rfl

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

theorem bitinteger_array_conversion (T : IntTy) (x : JInt S) :
    (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact) =
      if T.min ≤ x.val ∧ x.val ≤ T.max
      then .ok (JInt.wrap T x.val) else .error .inexact := by
  by_cases h : T.min ≤ x.val ∧ x.val ≤ T.max
  · simp only [JuliaLean.base.int.convert, JInt.convert, h, and_self, ite_true, dite_true, Except.mapError,
      Except.ok.injEq]
    apply Subtype.ext
    change x.val = wrapInt T x.val
    exact (wrapInt_of_inRange T x.val h).symm
  · simp [JuliaLean.base.int.convert, JInt.convert, h, Except.mapError]
@[simp] theorem mutation_get_run (s : MutableMemory α) :
    (get : MutationM α (MutableMemory α)).run s = (.ok s, s) := rfl

@[simp] theorem mutation_modify_run (f : MutableMemory α → MutableMemory α)
    (s : MutableMemory α) :
    (modify f : MutationM α Unit).run s = (.ok (), f s) := rfl

@[simp] theorem mutableVector_run (s : MutableMemory α) (handle : Nat) :
    (mutableVector handle).run s =
      match s.arrays[handle]? with
      | none => (.error .bounds, s)
      | some a => (.ok a, s) := by
  simp only [mutableVector, stateExcept_bind, mutation_get_run]
  cases s.arrays[handle]? <;> rfl

theorem mutableLength_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) :
    (mutableLength handle).run s = (.ok a.size, s) := by
  simp only [mutableLength, stateExcept_bind, mutableVector_run, ha, stateExcept_pure]

theorem mutableRef_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) :
    (mutableRef handle).run s = (.ok a.reference, s) := by
  simp only [mutableRef, stateExcept_bind, mutableVector_run, ha, stateExcept_pure]

theorem memoryRead_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) :
    (memoryRead mem).run s = (.ok slots, s) := by
  simp only [memoryRead, stateExcept_bind, mutation_get_run, hm, stateExcept_pure]

theorem memoryWrite_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int)) (x : Option α) :
    (memoryWrite mem i x).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (i.val - 1).toNat x)}) := by
  simp only [memoryWrite, stateExcept_bind, memoryRead_run s mem slots hm, hi,
    and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    mutation_modify_run]

theorem mutableMemLength_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) :
    ((mutableStorage layout).memLength mem).run s = (.ok (JInt.wrap .i64 slots.length), s) := by
  change (do
    let xs ← memoryRead mem
    pure (JInt.wrap .i64 (xs.length : Int)) : MutationM α I).run s = _
  simp only [stateExcept_bind, memoryRead_run s mem slots hm, stateExcept_pure]

theorem mutableCheckedAdd_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x y : I)
    (h : IntTy.i64.min ≤ x.val + y.val ∧ x.val + y.val ≤ IntTy.i64.max) :
    ((mutableStorage layout).checkedAdd x y).run s = (.ok (x + y), s) := by
  change (if _ then (pure (x + y) : MutationM α I) else throw Error.overflow).run s = _
  simp only [h, and_self, ite_true, stateExcept_pure]
theorem mutableSet_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (slots : List (Option α))
    (hm : s.memories[a.reference.1]? = some slots) (i : I) (x : α)
    (hb : one ≤ i ∧ i ≤ a.size)
    (hr : 1 ≤ (a.reference.2 + i - one).val ∧
      (a.reference.2 + i - one).val ≤ (slots.length : Int)) :
    (mutableSet handle x i).run s =
      (.ok (), {s with memories := (s.memories.set a.reference.1
        (slots.set ((a.reference.2 + i - one).val - 1).toNat (some x)))}) := by
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds, stateExcept_bind,
    mutableLength_run s handle a ha, stateExcept_pure, hb, and_self, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false, mutableMemoryref,
    mutableRef_run s handle a ha, memoryWrite_run s a.reference.1 slots hm _ hr]

theorem collectorLengthFits (capacity : Nat) (hcap : capacity < 2 ^ 63) :
    (JInt.wrap .i64 (capacity : Int)).val = capacity := by
  change wrapInt .i64 (capacity : Int) = capacity
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (capacity : Int) ∧
    (capacity : Int) ≤ 9223372036854775807
  change capacity < 9223372036854775808 at hcap
  omega

/-- Julia's `GenericMemory` size limit (`_new_genericmemory_`, genericmemory.c:55-73): a memory of
`nel` elements with element layout `l` is allocated exactly when neither `nel` nor its byte size
(`nel * elsz`, plus one selector byte per element for an isbits Union; a boxed element is
pointer-sized, 8 bytes) reaches `MAXINTVAL - 1`; otherwise `ArgumentError` is thrown. -/
def memoryFits (l : MemoryLayout) (nel : Nat) : Prop :=
  nel < maxIntVal - 1 ∧
    nel * (if l.isboxed then 8 else l.size) + (if l.isunion then nel else 0) < maxIntVal - 1

instance (l : MemoryLayout) (nel : Nat) : Decidable (memoryFits l nel) := by
  unfold memoryFits; infer_instance

/-- The error `Array{T,N}(undef, dims)` raises for `Int` dimensions `dims` and element layout `l`
(boot.jl:779-845 with genericmemory.c:55-73), if any. One dimension: `Memory{T}(undef, d)`
rejects a negative `d` (read as `size_t`) or a memory over the size limit; zero dimensions
allocate one element; two or more: `checked_dims` rejects a negative or `typemax(Int)`
dimension and a product beyond `typemax(Int)` with "invalid Array dimensions", then the memory
of `prod(dims)` elements must fit. -/
def arrayAllocError (l : MemoryLayout) (dims : List Int) : Option Error :=
  match dims with
  | [d] => if d < 0 ∨ ¬ memoryFits l d.toNat then some (.argument genericMemorySizeMessage) else none
  | _ =>
    if 2 ≤ dims.length ∧ ((∃ d ∈ dims, d < 0 ∨ d = 9223372036854775807) ∨
        9223372036854775807 < dims.prod) then
      some (.argument "invalid Array dimensions")
    else if ¬ memoryFits l dims.prod.toNat then some (.argument genericMemorySizeMessage)
    else none

/-- The outcome of `Array{T,N}(undef, dims)` on the shared heap: `arrayAllocError`, or a fresh array
of element type `target` and dimensions `dims`, every slot unassigned, at the next handle. -/
def allocOutcome {Tag α : Type} (l : MemoryLayout) (target : Tag) (dims : List Int)
    (heap : VectorHeap α) : Except Error (HeapArray Tag × VectorHeap α) :=
  match arrayAllocError l dims with
  | some e => .error e
  | none =>
    let shape := dims.map Int.toNat
    .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
      heap ++ [List.replicate shape.prod none])

/-- `typemax(Int)`. -/
def typemaxNat : Nat := 9223372036854775807

/-- `overallocation(maxsize)` (array.jl:1101-1112) for `0 ≤ maxsize ≤ typemax(Int)`: with `exp2`
the bit length of `maxsize` (`64 - leading_zeros(maxsize)`), it adds
`extra = 3 * 2^(7 * exp2 ÷ 8) + maxsize ÷ 8`, saturating at `typemax(Int)`. -/
def overallocationNat (n : Nat) : Nat :=
  let exp2 := if n = 0 then 0 else n.log2 + 1
  let extra := 2 ^ (exp2 * 7 / 8) * 3 + n / 8
  if typemaxNat - extra < n then typemaxNat else n + extra

/-- The memory length, the 1-based offset of the first element in that memory, and the length
of a `Vector`. -/
structure VectorGeometry where
  memlen : Nat
  offset : Nat
  length : Nat

/-- The geometry of vector `h` of the store. -/
def geometryOf {α : Type} (s : MutableMemory α) (h : Nat) : VectorGeometry :=
  match s.arrays[h]? with
  | none => ⟨0, 1, 0⟩
  | some v => ⟨(s.memories[v.reference.1]?.getD []).length, v.reference.2.val.toNat, v.size.val.toNat⟩

/-- A fresh `Vector{T}(undef, 0)` (`T[]`, `empty(v, T)`): a new empty memory. -/
def emptyGeometry : VectorGeometry := ⟨0, 1, 0⟩

/-- `array_new_memory(mem, k)` (array.jl:1114) for element layout `l`: the size `ArgumentError`
beyond Julia's limit, otherwise the vector continues with geometry `g`. -/
def allocationPlan (l : MemoryLayout) (k : Nat) (g : VectorGeometry) : Except Error VectorGeometry :=
  if memoryFits l k then .ok g else .error (.argument genericMemorySizeMessage)

/-- `_growend_internal!(a, d, len)` (array.jl:1171-1210): `checked_add(offset - 1, len + d)`, then
either the in-place slide (offset far enough advanced) or a new memory of
`max(overallocation(memlen), offset - 1 + len + d)`. The length is not changed here. -/
def growendInternalPlan (l : MemoryLayout) (g : VectorGeometry) (d : Nat) :
    Except Error VectorGeometry :=
  let newlen := g.length + d
  if typemaxNat < g.offset - 1 + newlen then .error .overflow
  else if newlen < g.offset - 1 ∧ newlen / 4 < g.offset - 1 - newlen then
    .ok ⟨g.memlen, newlen / 8 + 1, g.length⟩
  else
    let k := max (overallocationNat g.memlen) (g.offset - 1 + newlen)
    allocationPlan l k ⟨k, g.offset, g.length⟩

/-- `_growend!(a, d)` (array.jl:1212-1223) for `d ≥ 0`: no memory request when the spare room
after the last element holds `d` slots. -/
def growendPlan (l : MemoryLayout) (g : VectorGeometry) (d : Nat) : Except Error VectorGeometry :=
  if d ≤ g.memlen - (g.offset - 1) - g.length then .ok { g with length := g.length + d }
  else (growendInternalPlan l g d).map fun g' => { g' with length := g.length + d }

/-- `_growbeg_internal!(a, d, len)` (array.jl:1116-1149): `checked_add(len, checked_mul(2, d), 1)`,
then either the in-place recentring or a new memory of `max(overallocation(len), len + 2d + 1)`;
the data lands `d` slots after the new offset. The length is not changed here. -/
def growbegInternalPlan (l : MemoryLayout) (g : VectorGeometry) (d : Nat) :
    Except Error VectorGeometry :=
  let newlen := g.length + d
  if typemaxNat < g.length + 2 * d + 1 then .error .overflow
  else
    let k := max (overallocationNat g.length) (g.length + 2 * d + 1)
    if newlen < g.memlen ∧ (k - newlen) / 2 + 1 < g.memlen - newlen then
      .ok ⟨g.memlen, (g.memlen - newlen) / 2 + 1, g.length⟩
    else allocationPlan l k ⟨k, (k - newlen) / 2 + 1, g.length⟩

/-- `_growbeg!(a, d)` (array.jl:1151-1169) for `d ≥ 0`: nothing for `d = 0`; `checked_add(len, d)`;
no memory request when the offset leaves `d` free slots in front. -/
def growbegPlan (l : MemoryLayout) (g : VectorGeometry) (d : Nat) : Except Error VectorGeometry :=
  if d = 0 then .ok g
  else if typemaxNat < g.length + d then .error .overflow
  else if d ≤ g.offset - 1 then .ok ⟨g.memlen, g.offset - d, g.length + d⟩
  else (growbegInternalPlan l g d).map fun g' => { g' with length := g.length + d }

/-- `_growat!(a, i, d)` (array.jl:1225-1270) for `d ≥ 0`: `_growbeg!` at `i = 1`, `_growend!` at
`i = len + 1`, `BoundsError` outside `1:len+1`, then an in-place shift toward the preferred end when
there is room, otherwise a new memory of `max(overallocation(memlen), len + 2d + 1)`. -/
def growatPlan (l : MemoryLayout) (g : VectorGeometry) (i : Int) (d : Nat) :
    Except Error VectorGeometry :=
  let n := g.length
  let newlen := n + d
  if i = 1 then growbegPlan l g d
  else if n < typemaxNat ∧ i = n + 1 then growendPlan l g d
  else if ¬ (1 < i ∧ i ≤ n) then .error .bounds
  else if typemaxNat < g.offset - 1 + newlen then .error .overflow
  else if i ≤ ((n / 2 : Nat) : Int) ∧ d ≤ g.offset - 1 then .ok ⟨g.memlen, g.offset - d, newlen⟩
  else if ¬ i ≤ ((n / 2 : Nat) : Int) ∧ g.offset - 1 + newlen ≤ g.memlen then
    .ok { g with length := newlen }
  else if typemaxNat < n + 2 * d + 1 then .error .overflow
  else
    let k := max (overallocationNat g.memlen) (n + 2 * d + 1)
    allocationPlan l k ⟨k, (k - newlen) / 2 + 1, newlen⟩

/-- `sizehint!(a, sz; first, shrink)` (array.jl:1612-1643): `sz' = max(sz, len)`; within the
memory, a shrinking reallocation to `sz'` only when it saves more than `memlen ÷ 8` slots;
otherwise `_growbeg!`/`_growend!` by `sz' - len` with the length (and front offset) restored. -/
def sizehintPlan (l : MemoryLayout) (g : VectorGeometry) (sz : Int) (first shrink : Bool) :
    Except Error VectorGeometry :=
  let target := max sz.toNat g.length
  let inc := target - g.length
  if target ≤ g.memlen then
    if !shrink || g.memlen - target ≤ g.memlen / 8 then .ok g
    else allocationPlan l target ⟨target, if first && g.length != 0 then inc + 1 else 1, g.length⟩
  else if first then (growbegPlan l g inc).map fun g' => ⟨g'.memlen, g'.offset + inc, g.length⟩
  else (growendPlan l g inc).map fun g' => { g' with length := g.length }

/-- `k` successive `push!`es (`_growend!(a, 1)` each, array.jl:1361). -/
def pushesPlan (l : MemoryLayout) : VectorGeometry → Nat → Except Error VectorGeometry
  | g, 0 => .ok g
  | g, k + 1 => (growendPlan l g 1).bind fun g' => pushesPlan l g' k

/-- `run` follows `plan`: when the plan fails with `e`, `run` throws `e` and leaves the store `s`
unchanged; when it succeeds, `run` returns normally and `post` holds of its result and store. -/
def Follows {α ρ : Type} (s : MutableMemory α) (plan : Except Error VectorGeometry)
    (run : Except Error ρ × MutableMemory α) (post : ρ → MutableMemory α → Prop) : Prop :=
  (∀ e, plan = .error e → run = (.error e, s)) ∧
  (∀ g, plan = .ok g → ∃ r next, run = (.ok r, next) ∧ post r next)

/-- `run` follows a multi-step `plan`: its first failure `e` is the error `run` throws (after the
earlier steps took effect); when every step succeeds, `run` returns normally and `post` holds. -/
def FollowsSteps {α ρ π : Type} (plan : Except Error π)
    (run : Except Error ρ × MutableMemory α) (post : ρ → MutableMemory α → Prop) : Prop :=
  (∀ e, plan = .error e → run.1 = .error e) ∧
  (∀ g, plan = .ok g → ∃ r next, run = (.ok r, next) ∧ post r next)

def freshVectorAllocation {Tag α : Type} (target : Tag) (n : Nat) (heap : VectorHeap α) :
    Except Error (HeapArray Tag × VectorHeap α) :=
  .ok (⟨heap.length, target, [n], [(1, n)]⟩, heap ++ [List.replicate n none])

/-- `Int(len)` keeps a representable Integer value and rejects an out-of-range one. -/
def CollectorIntLaw {Z : Type} (value : Z → Int) (toInt : Z → Except Error I) : Prop :=
  ∀ z, toInt z =
    if IntTy.i64.min ≤ value z ∧ value z ≤ IntTy.i64.max
    then .ok (JInt.wrap .i64 (value z)) else .error .inexact

def freshShapeAllocation {Tag α : Type} (target : Tag) (shape : List Nat)
    (heap : VectorHeap α) : Except Error (HeapArray Tag × VectorHeap α) :=
  .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
    heap ++ [List.replicate shape.prod none])

def collectedShape {Tag α : Type} (target : Tag) (shape : List Nat)
    (values : List α) (heap : VectorHeap α) : HeapArray Tag × VectorHeap α :=
  (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
    heap ++ [values.map some])

/-- The documented equal-size iterable-copy interface includes conversion and the frame rule. -/
def SizedCopyLaw {Tag α β X : Type} (values : X → List β)
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)) : Prop :=
  ∀ dest itr heap slots, heap[dest.handle]? = some slots →
    dest.dimensions.prod = slots.length → slots.length = (values itr).length →
    slots.length < 2 ^ 63 →
    (copy dest itr).run heap =
      ((values itr).mapM convert).map
        (fun converted => (dest, heap.set dest.handle (converted.map some)))

theorem sizedCopy_fresh {Tag α β X : Type} (values : X → List β)
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (hcopy : SizedCopyLaw values convert copy) (target : Tag) (shape : List Nat)
    (itr : X) (heap : VectorHeap α) (hlen : shape.prod = (values itr).length)
    (hsize : shape.prod < 2 ^ 63) :
    (copy ⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩ itr).run
      (heap ++ [List.replicate shape.prod none]) =
      ((values itr).mapM convert).map
        (fun converted => collectedShape target shape converted heap) := by
  have h := hcopy ⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩
    itr (heap ++ [List.replicate shape.prod none]) (List.replicate shape.prod none)
    (by simp) (by simp) (by simpa using hlen) (by simpa using hsize)
  simpa only [List.set_append, Nat.lt_irrefl, ite_false, Nat.sub_self,
    List.set_cons_zero, collectedShape] using h

def intDimensionShape (dims : List I) : Except Error (List Nat) :=
  if dims.any (fun dim => decide (dim.val < 0)) then
    .error (.argument "invalid Array dimensions")
  else
    let shape := dims.map (fun dim => dim.val.toNat)
    if shape.prod < 2 ^ 63 then .ok shape
    else .error (.argument "invalid Array dimensions")

abbrev shapedCollectorAllocate {Tag α Axes : Type} (layout : Tag → Option MemoryLayout)
    (toShape : Axes → VectorM α (List I)) (target : Tag) (axes : Axes) :
    VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarStorageOneTo toShape
    (fun ty dims => JuliaLean.base.abstractarray.similarStorageDims
      (fun _ dims => heapAllocateIntDims layout target dims) ty dims)
    (HeapArray Tag) axes
theorem heapNatDimension_value (dims : List Nat) (hfit : heapDimensionsFit dims = true)
    (n : Nat) (hn : n ∈ dims) : (JInt.wrap .i64 (n : Int)).val = n := by
  have hb := List.all_eq_true.mp hfit n hn
  exact collectorLengthFits n (of_decide_eq_true hb)

abbrev genericSizedShapeCollect {Tag α X Axes : Type} (axes : X → Axes)
    (similar : Tag → Axes → VectorM α (HeapArray Tag))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
        (fun t _ axs => arrayForShape similar t axs) copy t itr ()) target itr

def GeneralSizedShapeSpec : Prop :=
  ∀ (Tag α β X Axes : Type) (values : X → List β) (axes : X → Axes)
    (similar : Tag → Axes → VectorM α (HeapArray Tag))
    (policy : Axes → Except Error (List Nat))
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    (∀ target axs heap, (similar target axs).run heap =
      (policy axs).bind (fun shape => freshShapeAllocation target shape heap)) →
    SizedCopyLaw values convert copy →
    (∀ axs shape, policy axs = .ok shape → shape.prod < 2 ^ 63) →
    ∀ target itr heap,
    (∀ shape, policy (axes itr) = .ok shape → shape.prod = (values itr).length) →
    (genericSizedShapeCollect axes similar copy target itr).run heap =
      (policy (axes itr)).bind (fun shape => ((values itr).mapM convert).map
        (fun converted => collectedShape target shape converted heap))

def collectReadSlot : Option α → Except Error (Option α)
  | none => .error .undefinedReference
  | some x => .ok (some x)

/-- The external unaliased-copy interface reads source elements in linear order,
retains the allocated header, and changes only the destination's slots. -/
def CollectUnaliasedLaw {Tag α Style : Type}
    (destStyle srcStyle : HeapArray Tag → Style)
    (copy : Style → HeapArray Tag → Style → HeapArray Tag → VectorM α (HeapArray Tag)) : Prop :=
  ∀ heap dest src xs ys, heap[src.handle]? = some xs → heap[dest.handle]? = some ys →
    dest.elementType = src.elementType → dest.dimensions.prod = xs.length →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    (copy (destStyle dest) dest (srcStyle src) src).run heap =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap.set dest.handle values))

/-- The Cartesian-copy interface pairs the destination's one-based Cartesian
indices with the source's original axes, in the same linear order. -/
def CollectCartesianLaw {Tag α Indices : Type}
    (cartesian : List (Int × Nat) → Indices)
    (copy : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag)) : Prop :=
  ∀ heap dest src xs ys, heap[src.handle]? = some xs → heap[dest.handle]? = some ys →
    dest.elementType = src.elementType → dest.dimensions.prod = xs.length →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    (copy dest (cartesian dest.axes) src (cartesian src.axes)).run heap =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap.set dest.handle values))

abbrev collectHeapEmpty {Tag α : Type} (a : HeapArray Tag) : VectorM α Bool := do
  let xs ← heapSlots a.handle
  pure xs.isEmpty

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

abbrev KeepatM (α : Type) :=
  ExceptT JuliaLean.base.abstractarray.ArrayError (MutationM α)

@[simp] theorem mutation_map_run (f : β → γ) (action : StateM (MutableMemory α) β)
    (s : MutableMemory α) :
    (f <$> action).run s = (f (action.run s).1, (action.run s).2) := rfl

inductive IndcopyTupleIndex (R : Type) where
  | range (value : R)
  | vector (values : List I)

def indcopyRangeEntry : IndcopyTupleIndex R → Option R
  | .range r => some r
  | .vector _ => none

/-- Core tuple/vector indexing, including bounds checking. -/
def indcopyCoreGet (xs : List α) (i : I) : Jl α :=
  if 1 ≤ i.val then
    match xs[(i.val - 1).toNat]? with
    | none => .error .boundsError
    | some x => .ok x
  else .error .boundsError

/-- The tuple-of-ranges method is the actual source definition. A tuple with
any index-vector entry has no applicable method and raises Core's MethodError
at this dispatch, as confirmed on the pinned nightly. Range-valued _findin and
range slicing are external methods from range.jl. -/
def tupleIndcopy {R : Type} (values : R → List I)
    (find : R → I → I → Jl R) (get : R → R → Jl R)
    (dims : List I) (indices : List (IndcopyTupleIndex R)) :
    Jl (List (List I) × List (List I)) :=
  match indices.mapM indcopyRangeEntry with
  | none => .error (.methodError "indcopy")
  | some ranges =>
    (indcopyTuple
      (fun dims : List I => JInt.wrap .i64 (dims.length : Int)) indcopyCoreGet
      (fun indices : List R => JInt.wrap .i64 (indices.length : Int)) indcopyCoreGet
      find get pure dims ranges).map (fun p => (p.1.map values, p.2.map values))

theorem ival_bounds (x : I) : -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 :=
  x.property

theorem ival_add (a b : I)
    (h : -9223372036854775808 ≤ a.val + b.val ∧ a.val + b.val ≤ 9223372036854775807) :
    (a + b).val = a.val + b.val := wrapInt_of_inRange .i64 _ h

theorem ival_sub (a b : I)
    (h : -9223372036854775808 ≤ a.val - b.val ∧ a.val - b.val ≤ 9223372036854775807) :
    (a - b).val = a.val - b.val := wrapInt_of_inRange .i64 _ h

theorem ival_wrap (x : Int) (h : -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807) :
    (JInt.wrap .i64 x).val = x := wrapInt_of_inRange .i64 _ h

theorem wrap64_eq (x : Int) :
    wrapInt .i64 x = (x + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 := rfl

theorem ival_add_sub (a b c : I)
    (h : -9223372036854775808 ≤ a.val + b.val - c.val ∧
      a.val + b.val - c.val ≤ 9223372036854775807) :
    (a + b - c).val = a.val + b.val - c.val := by
  change wrapInt .i64 (wrapInt .i64 (a.val + b.val) - c.val) = _
  rw [wrap64_eq, wrap64_eq]
  omega

@[simp] theorem ival_one : one.val = 1 := rfl
@[simp] theorem ival_zero : zero.val = 0 := rfl

theorem jlt_iff (a b : I) : a < b ↔ a.val < b.val := Iff.rfl
theorem jle_iff (a b : I) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

theorem urem_val (x : I) (h : 0 ≤ x.val) : (JInt.rem .u64 x).val = x.val := by
  have hb := ival_bounds x
  change x.val % 2 ^ 64 = x.val
  omega

theorem urem_neg_val (x : I) (h : x.val < 0) : (JInt.rem .u64 x).val = x.val + 2 ^ 64 := by
  have hb := ival_bounds x
  change x.val % 2 ^ 64 = x.val + 2 ^ 64
  omega

theorem wval4 : (JInt.wrap .i64 4).val = 4 := ival_wrap 4 (by decide)
theorem wval8 : (JInt.wrap .i64 8).val = 8 := ival_wrap 8 (by decide)

theorem ival_sub_one (x : I) (h : -9223372036854775807 ≤ x.val) : (x - one).val = x.val - 1 := by
  have hb := ival_bounds x
  rw [ival_sub x one (by rw [ival_one]; omega), ival_one]

theorem ival_add_one (x : I) (h : x.val ≤ 9223372036854775806) : (x + one).val = x.val + 1 := by
  have hb := ival_bounds x
  rw [ival_add x one (by rw [ival_one]; omega), ival_one]

theorem ival_add_sub_one (a b : I)
    (h : -9223372036854775808 ≤ a.val + b.val - 1 ∧ a.val + b.val - 1 ≤ 9223372036854775807) :
    (a + b - one).val = a.val + b.val - 1 := by
  rw [ival_add_sub a b one (by rw [ival_one]; exact h), ival_one]
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

/-- Vector `handle` is the window of `n` slots starting at one-based offset `off`
of memory `mem`, whose slots are `slots`. -/
def VecAt (s : MutableMemory α) (handle mem : Nat) (off n : I) (slots : List (Option α)) : Prop :=
  s.arrays[handle]? = some ⟨(mem, off), n⟩ ∧ s.memories[mem]? = some slots ∧
    1 ≤ off.val ∧ 0 ≤ n.val ∧ off.val - 1 + n.val ≤ (slots.length : Int) ∧ slots.length < 2 ^ 63

/-- The live elements of a vector window. -/
def vwWindow (slots : List (Option α)) (off n : I) : List (Option α) :=
  (slots.drop (off.val - 1).toNat).take n.val.toNat

theorem VecAt.contents {s : MutableMemory α} (h : VecAt s handle mem off n slots) :
    s.contents handle = vwWindow slots off n := by
  simp only [MutableMemory.contents, h.1, h.2.1, Option.getD_some, vwWindow]

theorem VecAt.valid {s : MutableMemory α} (h : VecAt s handle mem off n slots) :
    s.validVector handle := by
  obtain ⟨ha, hm, ho, hn, he, hc⟩ := h
  simp only [MutableMemory.validVector, ha, hm]
  exact ⟨hn, ho, he, hc⟩

theorem validVector_vecAt {s : MutableMemory α} (h : s.validVector handle) :
    ∃ mem off n slots, VecAt s handle mem off n slots := by
  unfold MutableMemory.validVector at h
  split at h
  · exact h.elim
  · rename_i a ha
    split at h
    · exact h.elim
    · rename_i slots hm
      exact ⟨a.reference.1, a.reference.2, a.size, slots, by rw [ha], hm, h.2.1, h.1,
        h.2.2.1, h.2.2.2⟩

theorem vwWindow_length (h : VecAt s handle mem off n slots) :
    (vwWindow slots off n).length = n.val.toNat := by
  obtain ⟨_, _, ho, hn, he, _⟩ := h
  simp only [vwWindow, List.length_take, List.length_drop]
  omega

/-- Sequential single-slot writes of `values` starting at one-based address `d + k`. -/
theorem vwMemoryWrites_run (mem : Nat) (d : I) (hd : 1 ≤ d.val) (values : List (Option α)) :
    ∀ (k : Nat) (s : MutableMemory α) (pre suf : List (Option α)),
      s.memories[mem]? = some (pre ++ suf) →
      (pre.length : Int) = d.val - 1 + k →
      values.length ≤ suf.length → pre.length + suf.length < 2 ^ 63 →
      (forIn (values.zipIdx k) () (fun (pair : Option α × Nat) _ => do
          memoryWrite mem (d + JInt.wrap .i64 pair.2) pair.1
          pure (ForInStep.yield ()))).run s =
        (.ok (), {s with memories := s.memories.set mem (pre ++ values ++ suf.drop values.length)}) := by
  induction values with
  | nil =>
    intro k s pre suf hm _ _ _
    have hself : s.memories.set mem (pre ++ suf) = s.memories := by
      obtain ⟨h, hv⟩ := List.getElem?_eq_some_iff.mp hm
      rw [← hv]
      exact List.set_getElem_self h
    simp only [List.zipIdx_nil, List.forIn_nil, stateExcept_pure, List.append_nil,
      List.length_nil, List.drop_zero, hself]
  | cons v vs ih =>
    intro k s pre suf hm hpre hfit hcap
    cases suf with
    | nil => simp at hfit
    | cons y ys =>
      have hb := ival_bounds d
      simp only [List.length_cons] at hfit hcap
      have hk : (JInt.wrap .i64 (k : Int)).val = k := ival_wrap _ (by omega)
      have haddr : (d + JInt.wrap .i64 (k : Int)).val = pre.length + 1 := by
        rw [ival_add _ _ (by rw [hk]; omega), hk]
        omega
      have hwrite := memoryWrite_run s mem (pre ++ y :: ys) hm (d + JInt.wrap .i64 (k : Int))
        (by rw [haddr]; simp only [List.length_append, List.length_cons]; omega) v
      have hset : (pre ++ y :: ys).set ((d + JInt.wrap .i64 (k : Int)).val - 1).toNat v =
          (pre ++ [v]) ++ ys := by
        rw [haddr]
        simp
      let mid : MutableMemory α :=
        {s with memories := s.memories.set mem ((pre ++ [v]) ++ ys)}
      have hmLt := (List.getElem?_eq_some_iff.mp hm).choose
      have hmid : mid.memories[mem]? = some ((pre ++ [v]) ++ ys) :=
        List.getElem?_set_self hmLt
      have hrest := ih (k + 1) mid (pre ++ [v]) ys hmid
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by omega) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      simp only [List.zipIdx_cons, List.forIn_cons, stateExcept_bind, hwrite, hset,
        stateExcept_pure]
      change (forIn (vs.zipIdx (k + 1)) ()
        (fun (pair : Option α × Nat) _ => do
          memoryWrite mem (d + JInt.wrap .i64 pair.2) pair.1
          pure (ForInStep.yield ())) : MutationM α Unit).run mid = _
      rw [hrest]
      simp [mid, List.append_assoc]

/-- `memoryMove` with arbitrary in-bounds offsets, including overlapping moves within one
memory: the moved values are the source snapshot. -/
theorem vwMemoryMove_run (s : MutableMemory α) (dest src : Nat) (doffs soffs n : I)
    (destination source : List (Option α))
    (hd : s.memories[dest]? = some destination) (hs : s.memories[src]? = some source)
    (hn : 0 ≤ n.val) (hdo : 1 ≤ doffs.val)
    (hde : doffs.val - 1 + n.val ≤ (destination.length : Int))
    (hso : 1 ≤ soffs.val) (hse : soffs.val - 1 + n.val ≤ (source.length : Int))
    (hcap : destination.length < 2 ^ 63) :
    (memoryMove dest doffs src soffs n).run s =
      (.ok (), { s with
        memories := s.memories.set dest
          (destination.take (doffs.val - 1).toNat ++
            (source.drop (soffs.val - 1).toNat).take n.val.toNat ++
            destination.drop (doffs.val - 1 + n.val).toNat) }) := by
  have hpre : (destination.take (doffs.val - 1).toNat).length = (doffs.val - 1).toNat := by
    rw [List.length_take]
    omega
  have hvals : ((source.drop (soffs.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
    simp only [List.length_take, List.length_drop]
    omega
  have hw := vwMemoryWrites_run dest doffs hdo ((source.drop (soffs.val - 1).toNat).take n.val.toNat)
    0 s (destination.take (doffs.val - 1).toNat) (destination.drop (doffs.val - 1).toNat)
    (by rw [List.take_append_drop]; exact hd) (by rw [hpre]; omega)
    (by rw [hvals, List.length_drop]; omega)
    (by rw [List.length_take, List.length_drop]; omega)
  rw [hvals, List.drop_drop] at hw
  have hsum : (doffs.val - 1).toNat + n.val.toNat = (doffs.val - 1 + n.val).toNat := by omega
  rw [hsum] at hw
  simp only [memoryMove, stateExcept_bind, memoryRead_run s src source hs,
    memoryRead_run s dest destination hd, hn, hdo, hde, hso, hse, and_self, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [hw, stateExcept_pure]

/-! ### Header updates -/

@[simp] theorem ms_length {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).length = mutableLength := rfl
@[simp] theorem ms_ref {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).ref = mutableRef := rfl
@[simp] theorem ms_memory {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).memory = Prod.fst := rfl
@[simp] theorem ms_offset {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).offset = Prod.snd := rfl
@[simp] theorem ms_unsetArray {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).unsetArray = mutableUnset layout.runtime := rfl
@[simp] theorem ms_copyMemory {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).copyMemory = memoryMove := rfl
@[simp] theorem ms_copyRef {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).copyRef =
    fun d s n => memoryMove d.1 d.2 s.1 s.2 n := rfl
@[simp] theorem ms_unsetMemory {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).unsetMemory =
    mutableMemoryUnset layout.runtime := rfl
@[simp] theorem ms_memoryref {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).memoryref =
    fun mem offset => pure (mem, offset) := rfl
@[simp] theorem ms_shiftref {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).shiftref =
    fun ref offset => pure (ref.1, ref.2 + offset - one) := rfl
@[simp] theorem ms_sameRef {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).sameRef = fun a b => a == b := rfl
@[simp] theorem ms_sameMem {layout : MemoryLayoutMetadata} : (mutableStorage (α := α) layout).sameMem = fun a b => a == b := rfl

theorem vwSetSize_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (n' : I) :
    ((mutableStorage layout).setSize handle n').run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨(mem, off), n'⟩}) := by
  change (do
    let v ← mutableVector handle
    modify fun s => { s with arrays := s.arrays.set handle { v with size := n' } } :
      MutationM α Unit).run s = _
  simp only [stateExcept_bind, mutableVector_run, h.1, mutation_modify_run]

theorem vwSetRef_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (ref : Nat × I) :
    ((mutableStorage layout).setRef handle ref).run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨ref, n⟩}) := by
  change (do
    let v ← mutableVector handle
    modify fun s => { s with arrays := s.arrays.set handle { v with reference := ref } } :
      MutationM α Unit).run s = _
  simp only [stateExcept_bind, mutableVector_run, h.1, mutation_modify_run]

theorem intRange_mem (lo hi j : I) (hj : j ∈ intRange lo hi) : lo.val ≤ j.val ∧ j.val ≤ hi.val := by
  simp only [intRange, List.mem_map, List.mem_range] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  have hl := ival_bounds lo
  have hh := ival_bounds hi
  rw [ival_wrap _ (by omega)]
  omega

theorem ms_setRef_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (v : MutableVector)
    (ha : s.arrays[handle]? = some v) (ref : Nat × I) :
    ((mutableStorage layout).setRef handle ref).run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨ref, v.size⟩}) := by
  change (do
    let v ← mutableVector handle
    modify fun s => { s with arrays := s.arrays.set handle { v with reference := ref } } :
      MutationM α Unit).run s = _
  simp only [stateExcept_bind, mutableVector_run, ha, mutation_modify_run]

theorem ms_setSize_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (v : MutableVector)
    (ha : s.arrays[handle]? = some v) (n' : I) :
    ((mutableStorage layout).setSize handle n').run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨v.reference, n'⟩}) := by
  change (do
    let v ← mutableVector handle
    modify fun s => { s with arrays := s.arrays.set handle { v with size := n' } } :
      MutationM α Unit).run s = _
  simp only [stateExcept_bind, mutableVector_run, ha, mutation_modify_run]

theorem ms_divide_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x y : I) (hy : y.val ≠ 0) :
    ((mutableStorage layout).divide x y).run s = (.ok (JInt.wrap .i64 (x.val.tdiv y.val)), s) := by
  change (if y.val = 0 then (throw Error.divide : MutationM α I) else pure _).run s = _
  simp only [hy, ite_false, stateExcept_pure]

theorem ms_checkedAdd_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x y : I)
    (h : -9223372036854775808 ≤ x.val + y.val ∧ x.val + y.val ≤ 9223372036854775807) :
    ((mutableStorage layout).checkedAdd x y).run s = (.ok (x + y), s) := mutableCheckedAdd_run s x y h

theorem ms_checkedMul_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x y : I)
    (h : -9223372036854775808 ≤ x.val * y.val ∧ x.val * y.val ≤ 9223372036854775807) :
    ((mutableStorage layout).checkedMul x y).run s = (.ok (x * y), s) := by
  have h' : IntTy.i64.min ≤ x.val * y.val ∧ x.val * y.val ≤ IntTy.i64.max := h
  change (if _ then (pure (x * y) : MutationM α I) else throw Error.overflow).run s = _
  simp only [h', and_self, ite_true, stateExcept_pure]

theorem tdiv_nonneg_val (x : I) (k : Int) (hx : 0 ≤ x.val) (hk : 0 < k) (hk' : k ≤ 8) :
    (JInt.wrap .i64 (x.val.tdiv k)).val = x.val / k := by
  rw [Int.tdiv_eq_ediv_of_nonneg hx]
  have hb := ival_bounds x
  apply ival_wrap
  constructor
  · exact Int.le_trans (by decide) (Int.ediv_nonneg hx (Int.le_of_lt hk))
  · exact Int.le_trans (Int.ediv_le_self _ hx) hb.2

/-- Memory-level clearing, `unsetindex!(mem, j)`. -/
theorem mutableMemoryUnset_run (runtime : DictLayout) (s : MutableMemory α)
    (mem : Nat) (slots : List (Option α)) (hm : s.memories[mem]? = some slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int)) :
    (mutableMemoryUnset runtime mem i).run s =
      (.ok (), {s with memories := (s.memories.set mem
        (slots.set (i.val - 1).toNat (expectedUnset runtime (slots[(i.val - 1).toNat]?).join)))}) := by
  have hk : (i.val - 1).toNat < slots.length := by omega
  have hw := memoryWrite_run s mem slots hm i hi
    (expectedUnset runtime (slots[(i.val - 1).toNat]?).join)
  simpa only [mutableMemoryUnset, stateExcept_bind, memoryRead_run s mem slots hm,
    List.getElem?_eq_getElem hk, stateExcept_pure, unsetCell_result, Option.join_some] using hw

def vwClear {unsetRuntime : DictLayout} (slots : List (Option α)) (js : List I) : List (Option α) :=
  js.foldl (fun sl j => sl.set (j.val - 1).toNat (expectedUnset unsetRuntime (sl[(j.val - 1).toNat]?).join)) slots

theorem vwClear_length {unsetRuntime : DictLayout} (slots : List (Option α)) (js : List I) :
    (vwClear (unsetRuntime := unsetRuntime) slots js).length = slots.length := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwClear, List.foldl_cons] at ih ⊢
    rw [ih, List.length_set]

theorem vwClear_take {unsetRuntime : DictLayout} (slots : List (Option α)) (js : List I) (k : Nat)
    (h : ∀ j ∈ js, k ≤ (j.val - 1).toNat) :
    (vwClear (unsetRuntime := unsetRuntime) slots js).take k = slots.take k := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwClear, List.foldl_cons] at ih ⊢
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact List.take_set_of_le (h j List.mem_cons_self)

theorem vwClear_drop {unsetRuntime : DictLayout} (slots : List (Option α)) (js : List I) (k : Nat)
    (h : ∀ j ∈ js, (j.val - 1).toNat < k) :
    (vwClear (unsetRuntime := unsetRuntime) slots js).drop k = slots.drop k := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwClear, List.foldl_cons] at ih ⊢
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact List.drop_set_of_lt (h j List.mem_cons_self)

theorem vwClearLoop_run {unsetRuntime : DictLayout} (mem : Nat) (js : List I) :
    ∀ (s : MutableMemory α) (slots : List (Option α)), s.memories[mem]? = some slots →
      (∀ j ∈ js, 1 ≤ j.val ∧ j.val ≤ (slots.length : Int)) →
      (forIn js PUnit.unit (fun j _ => do
          (mutableMemoryUnset unsetRuntime) mem j
          pure (ForInStep.yield PUnit.unit))).run s =
        (.ok PUnit.unit, { s with memories := s.memories.set mem (vwClear (unsetRuntime := unsetRuntime) slots js) }) := by
  induction js with
  | nil =>
    intro s slots hm _
    have hself : s.memories.set mem slots = s.memories := by
      obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp hm
      rw [← hv]
      exact List.set_getElem_self hlt
    simp only [List.forIn_nil, stateExcept_pure, vwClear, List.foldl_nil, hself]
  | cons j js ih =>
    intro s slots hm hj
    have hstep := mutableMemoryUnset_run unsetRuntime s mem slots hm j (hj j List.mem_cons_self)
    have hlt := (List.getElem?_eq_some_iff.mp hm).choose
    have hrest := ih { s with memories := s.memories.set mem (slots.set (j.val - 1).toNat (expectedUnset unsetRuntime (slots[(j.val - 1).toNat]?).join)) }
      (slots.set (j.val - 1).toNat (expectedUnset unsetRuntime (slots[(j.val - 1).toNat]?).join)) (List.getElem?_set_self hlt)
      (fun j' hj' => by rw [List.length_set]; exact hj j' (List.mem_cons_of_mem _ hj'))
    simp only [List.forIn_cons, stateExcept_bind, hstep, stateExcept_pure]
    rw [hrest]
    simp [vwClear, List.foldl_cons]

theorem take_three {A W B : List β} (hA : A.length = a) (hW : W.length = w) :
    ((A ++ W ++ B).drop a).take w = W := by
  subst hA hW
  rw [List.append_assoc, List.drop_left, List.take_left]

/-! ### Clearing slots -/

/-- Slots after Julia's `unsetindex!(a, j)` for every `j` of `js`. -/
def vwUnset {unsetRuntime : DictLayout} (slots : List (Option α)) (off : I) (js : List I) : List (Option α) :=
  js.foldl (fun sl j => sl.set (off.val - 1 + j.val - 1).toNat (expectedUnset unsetRuntime (sl[(off.val - 1 + j.val - 1).toNat]?).join)) slots

theorem vwUnset_length {unsetRuntime : DictLayout} (slots : List (Option α)) (off : I) (js : List I) :
    (vwUnset (unsetRuntime := unsetRuntime) slots off js).length = slots.length := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwUnset, List.foldl_cons] at ih ⊢
    rw [ih, List.length_set]

theorem vwUnset_take {unsetRuntime : DictLayout} (slots : List (Option α)) (off : I) (js : List I) (k : Nat)
    (h : ∀ j ∈ js, k ≤ (off.val - 1 + j.val - 1).toNat) :
    (vwUnset (unsetRuntime := unsetRuntime) slots off js).take k = slots.take k := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwUnset, List.foldl_cons] at ih ⊢
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact List.take_set_of_le (h j List.mem_cons_self)

theorem vwUnset_drop {unsetRuntime : DictLayout} (slots : List (Option α)) (off : I) (js : List I) (k : Nat)
    (h : ∀ j ∈ js, (off.val - 1 + j.val - 1).toNat < k) :
    (vwUnset (unsetRuntime := unsetRuntime) slots off js).drop k = slots.drop k := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwUnset, List.foldl_cons] at ih ⊢
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact List.drop_set_of_lt (h j List.mem_cons_self)

theorem vwUnset_get {unsetRuntime : DictLayout} (slots : List (Option α)) (off : I) (js : List I) (k : Nat)
    (h : ∀ j ∈ js, k ≠ (off.val - 1 + j.val - 1).toNat) :
    (vwUnset (unsetRuntime := unsetRuntime) slots off js)[k]? = slots[k]? := by
  induction js generalizing slots with
  | nil => rfl
  | cons j js ih =>
    simp only [vwUnset, List.foldl_cons] at ih ⊢
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact List.getElem?_set_ne (fun he => h j List.mem_cons_self he.symm)

theorem vwMutableUnset_run {unsetRuntime : DictLayout} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (j : I)
    (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    ((mutableUnset unsetRuntime) handle j).run s =
      (.ok (), { s with
        memories := s.memories.set mem (slots.set (off.val - 1 + j.val - 1).toNat (expectedUnset unsetRuntime (slots[(off.val - 1 + j.val - 1).toNat]?).join)) }) := by
  obtain ⟨ha, hm, ho, hn, he, hc⟩ := h
  have hb := ival_bounds off
  have hjb := ival_bounds j
  have haddr : (off + j - one).val = off.val + j.val - 1 :=
    ival_add_sub_one _ _ (by omega)
  have hin : (one ≤ j ∧ j ≤ n) := ⟨by rw [jle_iff, ival_one]; omega, hj.2⟩
  have hw := mutableMemoryUnset_run unsetRuntime s mem slots hm (off + j - one) (by rw [haddr]; omega)
  simp only [mutableUnset, unsetindexInt, mutableBounds, mutableInBounds, mutableLength,
    mutableMemoryref, mutableRef, stateExcept_bind, mutableVector_run, ha, stateExcept_pure,
    hin, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hw]
  rw [haddr, show off.val + j.val - 1 - 1 = off.val - 1 + j.val - 1 by omega]

theorem vwUnsetLoop_run {unsetRuntime : DictLayout} (handle mem : Nat) (off n : I) (js : List I) :
    ∀ (s : MutableMemory α) (slots : List (Option α)), VecAt s handle mem off n slots →
      (∀ j ∈ js, 1 ≤ j.val ∧ j.val ≤ n.val) →
      (forIn js PUnit.unit (fun j _ => do
          (mutableUnset unsetRuntime) handle j
          pure (ForInStep.yield PUnit.unit))).run s =
        (.ok PUnit.unit, {s with memories := s.memories.set mem (vwUnset (unsetRuntime := unsetRuntime) slots off js)}) := by
  induction js with
  | nil =>
    intro s slots h _
    have hself : s.memories.set mem slots = s.memories := by
      obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp h.2.1
      rw [← hv]
      exact List.set_getElem_self hlt
    simp only [List.forIn_nil, stateExcept_pure, vwUnset, List.foldl_nil, hself]
  | cons j js ih =>
    intro s slots h hj
    have hstep := vwMutableUnset_run (unsetRuntime := unsetRuntime) s handle mem off n slots h j (hj j List.mem_cons_self)
    have hlt := (List.getElem?_eq_some_iff.mp h.2.1).choose
    have hmid : VecAt { s with
        memories := s.memories.set mem (slots.set (off.val - 1 + j.val - 1).toNat (expectedUnset unsetRuntime (slots[(off.val - 1 + j.val - 1).toNat]?).join)) }
        handle mem off n (slots.set (off.val - 1 + j.val - 1).toNat (expectedUnset unsetRuntime (slots[(off.val - 1 + j.val - 1).toNat]?).join)) := by
      obtain ⟨ha, _, ho, hn, he, hc⟩ := h
      exact ⟨ha, List.getElem?_set_self hlt, ho, hn, by rw [List.length_set]; exact he,
        by rw [List.length_set]; exact hc⟩
    have hrest := ih _ _ hmid (fun j' hj' => hj j' (List.mem_cons_of_mem _ hj'))
    simp only [List.forIn_cons, stateExcept_bind, hstep, stateExcept_pure]
    rw [hrest]
    simp [vwUnset, List.foldl_cons]

theorem vwDeleteend_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (d : I)
    (hd : 0 ≤ d.val) (hdn : d.val ≤ n.val) (hmax : n.val - d.val < 9223372036854775807) :
    ∃ next slots', (deleteend (mutableStorage layout) pure handle d).run s = (.ok (), next) ∧
      VecAt next handle mem off (n - d) slots' ∧
      next.memories = s.memories.set mem slots' ∧
      next.arrays = s.arrays.set handle ⟨(mem, off), n - d⟩ ∧
      vwWindow slots' off (n - d) = (vwWindow slots off n).take (n.val - d.val).toNat := by
  have hnb := ival_bounds n
  have hdb := ival_bounds d
  have hn0 := h.2.2.2.1
  have hsub : (n - d).val = n.val - d.val := ival_sub _ _ (by omega)
  have hsmall : ¬ (JInt.rem .u64 d > JInt.rem .u64 n) := by
    change ¬ ((JInt.rem .u64 n).val < (JInt.rem .u64 d).val)
    rw [urem_val n hn0, urem_val d hd]
    omega
  have hlo : (n - d + one).val = n.val - d.val + 1 := by
    rw [ival_add (n - d) one (by rw [hsub]; simp only [ival_one]; omega), hsub]
    simp
  have hjs : ∀ j ∈ intRange (n - d + one) n, 1 ≤ j.val ∧ j.val ≤ n.val := by
    intro j hj
    have := intRange_mem _ _ j hj
    omega
  have hloop := vwUnsetLoop_run (unsetRuntime := layout.runtime) handle mem off n (intRange (n - d + one) n) s slots h hjs
  have hlt := (List.getElem?_eq_some_iff.mp h.2.1).choose
  have halt := (List.getElem?_eq_some_iff.mp h.1).choose
  have hmidv : VecAt { s with
      memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n - d + one) n)) }
      handle mem off n (vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n - d + one) n)) := by
    obtain ⟨ha, _, ho, hn, he, hc⟩ := h
    exact ⟨ha, List.getElem?_set_self hlt, ho, hn, by rw [vwUnset_length]; exact he,
      by rw [vwUnset_length]; exact hc⟩
  have hsize := vwSetSize_run (layout := layout) _ handle mem off n _ hmidv (n - d)
  refine ⟨{ s with
      memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n - d + one) n))
      arrays := s.arrays.set handle ⟨(mem, off), n - d⟩ },
    vwUnset (unsetRuntime := layout.runtime) slots off (intRange (n - d + one) n), ?_, ?_, rfl, rfl, ?_⟩
  · simp only [deleteend, ms_length, ms_unsetArray, stateExcept_bind, stateExcept_pure,
      mutableLength_run s handle _ h.1, hsmall, ite_false, hloop, hsize]
  · obtain ⟨_, _, ho, _, he, hc⟩ := h
    refine ⟨List.getElem?_set_self halt, List.getElem?_set_self hlt, ho, by omega,
      by rw [vwUnset_length, hsub]; omega, by rw [vwUnset_length]; exact hc⟩
  · have hk : ∀ j ∈ intRange (n - d + one) n,
        (off.val - 1).toNat + (n.val - d.val).toNat ≤ (off.val - 1 + j.val - 1).toNat := by
      intro j hj
      have := intRange_mem _ _ j hj
      have := h.2.2.1
      omega
    simp only [vwWindow, hsub, List.take_take, List.take_drop]
    rw [show min ((off.val - 1).toNat + (n.val - d.val).toNat)
        ((off.val - 1).toNat + n.val.toNat) = (off.val - 1).toNat + (n.val - d.val).toNat by omega,
      vwUnset_take _ _ _ _ hk]

theorem vwDeletebeg_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (d : I)
    (hd : 0 ≤ d.val) (hdn : d.val ≤ n.val) :
    ∃ next off' slots', (deletebeg (mutableStorage layout) pure handle d).run s = (.ok (), next) ∧
      VecAt next handle mem off' (n - d) slots' ∧
      next.memories = s.memories.set mem slots' ∧
      next.arrays = s.arrays.set handle ⟨(mem, off'), n - d⟩ ∧
      vwWindow slots' off' (n - d) = (vwWindow slots off n).drop d.val.toNat := by
  have hnb := ival_bounds n
  have hdb := ival_bounds d
  have hob := ival_bounds off
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hsub : (n - d).val = n.val - d.val := ival_sub _ _ (by omega)
  have hsmall : ¬ (JInt.rem .u64 d > JInt.rem .u64 n) := by
    change ¬ ((JInt.rem .u64 n).val < (JInt.rem .u64 d).val)
    rw [urem_val n hn0, urem_val d hd]
    omega
  have hjs : ∀ j ∈ intRange one d, 1 ≤ j.val ∧ j.val ≤ n.val := by
    intro j hj
    have := intRange_mem _ _ j hj
    simp only [ival_one] at this
    omega
  have h' : VecAt s handle mem off n slots := ⟨ha, hm, ho, hn0, he, hc⟩
  have hloop := vwUnsetLoop_run (unsetRuntime := layout.runtime) handle mem off n (intRange one d) s slots h' hjs
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hmidv : VecAt { s with memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d)) }
      handle mem off n (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d)) :=
    ⟨ha, List.getElem?_set_self hlt, ho, hn0, by rw [vwUnset_length]; exact he,
      by rw [vwUnset_length]; exact hc⟩
  have hsize := vwSetSize_run (layout := layout) _ handle mem off n _ hmidv (n - d)
  have hmid2 : VecAt { s with
      memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d))
      arrays := s.arrays.set handle ⟨(mem, off), n - d⟩ } handle mem off (n - d)
      (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d)) :=
    ⟨List.getElem?_set_self halt, List.getElem?_set_self hlt, ho, by omega,
      by rw [vwUnset_length]; omega, by rw [vwUnset_length]; exact hc⟩
  have hdrop : ∀ j ∈ intRange one d,
      (off.val - 1 + j.val - 1).toNat < (off.val - 1).toNat + d.val.toNat := by
    intro j hj
    have := intRange_mem _ _ j hj
    simp only [ival_one] at this
    omega
  by_cases hz : n.val - d.val = 0
  · have hne : ((n - d).val != 0) = false := by rw [hsub, hz]; rfl
    refine ⟨_, off, vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d), ?_, hmid2, rfl, rfl, ?_⟩
    · simp only [deletebeg, ms_length, ms_unsetArray, stateExcept_bind, stateExcept_pure,
        mutableLength_run s handle _ ha, hsmall, ite_false, hloop, hsize, hne,
        Bool.false_eq_true, ite_false, stateExcept_pure]
    · have hl : (vwWindow slots off n).length = n.val.toNat := vwWindow_length h'
      have hl' : (vwWindow (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d)) off (n - d)).length = 0 := by
        rw [vwWindow_length hmid2, hsub, hz]; rfl
      rw [List.length_eq_zero_iff.mp hl']
      symm
      apply List.drop_eq_nil_of_le
      omega
  · have hne : ((n - d).val != 0) = true := by rw [hsub]; simpa using hz
    have haddr : (off + (d + one) - one).val = off.val + d.val := by
      have h1 : (d + one).val = d.val + 1 := ival_add_one d (by omega)
      rw [ival_add_sub_one off (d + one) (by rw [h1]; omega), h1]
      omega
    have href := mutableRef_run _ handle _ hmid2.1
    have hset := vwSetRef_run (layout := layout) _ handle mem off (n - d) _ hmid2 (mem, off + (d + one) - one)
    refine ⟨{ s with
        memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d))
        arrays := s.arrays.set handle ⟨(mem, off + (d + one) - one), n - d⟩ },
      off + (d + one) - one, vwUnset (unsetRuntime := layout.runtime) slots off (intRange one d), ?_, ?_, rfl, rfl, ?_⟩
    · simp only [deletebeg, ms_length, ms_unsetArray, ms_ref, ms_shiftref, stateExcept_bind,
        stateExcept_pure, mutableLength_run s handle _ ha, hsmall, ite_false, hloop, hsize, hne,
        ite_true, href, hset, List.set_set]
    · exact ⟨List.getElem?_set_self (by simpa using halt), List.getElem?_set_self hlt,
        by rw [haddr]; omega, by omega, by rw [vwUnset_length, haddr, hsub]; omega,
        by rw [vwUnset_length]; exact hc⟩
    · simp only [vwWindow, haddr, hsub, List.drop_take, List.drop_drop]
      rw [show (off.val + d.val - 1).toNat = (off.val - 1).toNat + d.val.toNat by omega,
        vwUnset_drop _ _ _ _ hdrop,
        show (n.val - d.val).toNat = n.val.toNat - d.val.toNat by omega]

/-! ### Element reads -/

theorem vwGet_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) :
    (mutableGet handle i).run s =
      ((match (vwWindow slots off n)[(i.val - 1).toNat]? with
        | some (some x) => .ok x
        | _ => .error .undefinedReference), s) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hi1 : (1 : Int) ≤ i.val := hi.1
  have hi2 : i ≤ n := hi.2
  have hidx : (vwWindow slots off n)[(i.val - 1).toNat]? = slots[(off.val + i.val - 2).toNat]? := by
    simp only [vwWindow, List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega)]
    congr 1
    omega
  have hlt : (off.val + i.val - 2).toNat < slots.length := by omega
  simp only [mutableGet, stateExcept_bind, mutableVector_run, ha, hi1, hi2, and_self,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false, memoryRead_run s mem slots hm]
  rw [hidx, List.getElem?_eq_getElem hlt]
  cases slots[(off.val + i.val - 2).toNat] <;> rfl

def EmptySpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat), s.validVector handle →
    ∃ next, (empty mutableLength (deleteend (mutableStorage layout) pure) handle).run s = (.ok handle, next) ∧
      next.contents handle = [] ∧ next.validVector handle

/-! ## Growth at the end of a vector -/

theorem vwSet_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) (x : α) :
    (mutableSet handle x i).run s =
      (.ok (), { s with
        memories := s.memories.set mem (slots.set (off.val - 1 + i.val - 1).toNat (some x)) }) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hib := ival_bounds i
  have haddr : (off + i - one).val = off.val + i.val - 1 :=
    ival_add_sub_one _ _ (by omega)
  have hr := mutableSet_run s handle _ ha slots hm i x
    ⟨by rw [jle_iff, ival_one]; exact hi.1, hi.2⟩ (by simp only; rw [haddr]; omega)
  rw [hr]
  simp only [haddr]
  rw [show off.val + i.val - 1 - 1 = off.val - 1 + i.val - 1 by omega]

theorem VecAt.set {s : MutableMemory α} (h : VecAt s handle mem off n slots) (k : Nat)
    (v : Option α) :
    VecAt { s with memories := s.memories.set mem (slots.set k v) } handle mem off n
      (slots.set k v) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  exact ⟨ha, List.getElem?_set_self hlt, ho, hn0, by rw [List.length_set]; exact he,
    by rw [List.length_set]; exact hc⟩

theorem vwWindow_set (slots : List (Option α)) (off n i : I) (v : Option α)
    (ho : 1 ≤ off.val) (hi : 1 ≤ i.val) :
    vwWindow (slots.set (off.val - 1 + i.val - 1).toNat v) off n =
      (vwWindow slots off n).set (i.val - 1).toNat v := by
  simp only [vwWindow]
  rw [show (off.val - 1 + i.val - 1).toNat = (off.val - 1).toNat + (i.val - 1).toNat by omega,
    ← List.set_drop, List.take_set]

theorem list_set_last (l xs : List β) (k : Nat) (v : β) (hl : l.length = k + 1)
    (ht : l.take k = xs) : l.set k v = xs ++ [v] := by
  have hk : xs.length = k := by rw [← ht, List.length_take]; omega
  have hd : (l.drop k).length = 1 := by rw [List.length_drop]; omega
  obtain ⟨y, hy⟩ : ∃ y, l.drop k = [y] := by
    match h : l.drop k with
    | [y] => exact ⟨y, rfl⟩
    | [] => rw [h] at hd; simp at hd
    | _ :: _ :: _ => rw [h] at hd; simp at hd
  rw [← List.take_append_drop k l, ht, hy, List.set_append_right _ _ (by omega), hk]
  simp

theorem wval2 : (JInt.wrap .i64 2).val = 2 := ival_wrap 2 (by decide)

theorem ival_two_mul (d : I) (h : 0 ≤ d.val) (hd : 2 * d.val ≤ 9223372036854775807) :
    (JInt.wrap .i64 2 * d).val = 2 * d.val := by
  rw [show JInt.wrap .i64 2 * d = JInt.wrap .i64 ((JInt.wrap .i64 2).val * d.val) from rfl, wval2]
  exact ival_wrap _ (by omega)

def lengthToInt {α : Type} {t : IntTy} (x : JInt t) : MutationM α I :=
  stateExceptLift ((JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact))
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem unsafeCopyArray_vector_run {Tag α : Type} (heap next : VectorHeap α)
    (dest source : HeapArray Tag) (doffs soffs n : I) (hn : n.val ≠ 0)
    (hc : (heapCopyReferences (fun x => Except.ok (ε := Error) x)
      (dest.handle, doffs) (source.handle, soffs) n).run heap = .ok ((), next)) :
    (do
      let _ ← unsafeCopyArray (fun n : I => decide (n.val = 0))
        (fun a i => pure (a.handle, i)) (fun a i => pure (a.handle, i))
        (heapCopyReferences (fun x => .ok x)) dest doffs source soffs n
      pure () : VectorM α Unit).run heap = .ok ((), next) := by
  simp only [unsafeCopyArray, hn, decide_false, Bool.false_eq_true, ite_false,
    vector_bind_run, vector_pure_run, hc]

def heapColonMemoryCopy {Tag α : Type} (dest : HeapArray Tag) (doffs : I)
    (source : HeapArray Tag) (soffs n : I) : VectorM α Unit := do
  let _ ← unsafeCopyArray (fun n : I => decide (n.val = 0))
    (fun a i => pure (a.handle, i)) (fun a i => pure (a.handle, i))
    (heapCopyReferences (fun x => .ok x)) dest doffs source soffs n
  pure ()
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section HeapRanges

attribute [local irreducible] JInt.wrap wrapInt

/-! ## Range indexing, range assignment and concatenation on the shared heap -/

theorem except_mapM_ok (ys : List (Option α)) :
    ys.mapM (fun x => Except.ok (ε := Error) x) = .ok ys := by
  induction ys with
  | nil => rfl
  | cons x ys ih =>
    simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem heapCopyReferences_window_run (heap : VectorHeap α) (dest src : Nat)
    (xs ys : List (Option α)) (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (di si n : I) (hn : 0 ≤ n.val) (hdi : 1 ≤ di.val)
    (hde : di.val - 1 + n.val ≤ (ys.length : Int))
    (hsi : 1 ≤ si.val) (hse : si.val - 1 + n.val ≤ (xs.length : Int)) :
    (heapCopyReferences (fun x => Except.ok (ε := Error) x) (dest, di) (src, si) n).run heap =
      .ok ((), heap.set dest (ys.take (di.val - 1).toNat ++
        (xs.drop (si.val - 1).toNat).take n.val.toNat ++ ys.drop (di.val - 1 + n.val).toNat)) := by
  have hb : 0 ≤ n.val ∧ 1 ≤ di.val ∧ di.val - 1 + n.val ≤ (ys.length : Int) ∧
      1 ≤ si.val ∧ si.val - 1 + n.val ≤ (xs.length : Int) := ⟨hn, hdi, hde, hsi, hse⟩
  simp only [heapCopyReferences, vector_bind_run, heapSlots_run, hsrc, hdest]
  rw [if_neg (by simp [hb])]
  simp only [vector_bind_run, vector_lift_run, except_mapM_ok, Except.map, vector_modify_run]


theorem heapLength_of_slots (heap : VectorHeap α) (handle : Nat) (xs : List (Option α))
    (hs : heap[handle]? = some xs) (hn : xs.length < 2 ^ 62) :
    (heapLength handle).run heap = .ok (JInt.wrap .i64 xs.length, heap) ∧
      (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
  refine ⟨by simp only [heapLength_run, hs], ival_wrap _ ?_⟩
  change xs.length < 4611686018427387904 at hn
  omega

/-- The source `unsafe_copyto!(dest, doffs, src, soffs, n)` on two heap arrays copies the
`n`-slot source window into the destination window, reading the source first. -/
theorem heapUnsafeCopy_run {Tag α : Type} (heap : VectorHeap α) (dest src : HeapArray Tag)
    (xs ys : List (Option α)) (hsrc : heap[src.handle]? = some xs)
    (hdest : heap[dest.handle]? = some ys) (di si n : I) (hn : 0 < n.val) (hdi : 1 ≤ di.val)
    (hde : di.val - 1 + n.val ≤ (ys.length : Int))
    (hsi : 1 ≤ si.val) (hse : si.val - 1 + n.val ≤ (xs.length : Int)) :
    (heapColonMemoryCopy dest di src si n).run heap =
      .ok ((), heap.set dest.handle (ys.take (di.val - 1).toNat ++
        (xs.drop (si.val - 1).toNat).take n.val.toNat ++ ys.drop (di.val - 1 + n.val).toNat)) := by
  unfold heapColonMemoryCopy
  apply unsafeCopyArray_vector_run
  · omega
  · exact heapCopyReferences_window_run heap dest.handle src.handle xs ys hsrc hdest di si n
      (by omega) hdi hde hsi hse

theorem heapUnsafeCopy_zero_run {Tag α : Type} (heap : VectorHeap α) (dest src : HeapArray Tag)
    (di si n : I) (hn : n.val = 0) :
    (heapColonMemoryCopy dest di src si n).run heap = .ok ((), heap) := by
  simp only [heapColonMemoryCopy, unsafeCopyArray, hn, decide_true, ite_true, vector_bind_run,
    vector_pure_run]

theorem heapBounds_in (heap : VectorHeap α) (handle : Nat) (xs : List (Option α))
    (hs : heap[handle]? = some xs) (i : I) (h1 : 1 ≤ i.val) (h2 : i.val ≤ (xs.length : Int)) :
    (heapBounds handle i).run heap = .ok ((), heap) := by
  simp only [heapBounds_run, hs]
  exact if_pos ⟨h1, h2⟩

/-- `length(lo:hi)` of a `UnitRange{Int}`. -/
def unitRangeLength (r : I × I) : I := if r.2 < r.1 then zero else r.2 - r.1 + one

/-- `copyto!(X, firstindex(X), A, first(I), lI)`: the checked `copyto!` of array.jl:288. -/
def heapRangeCopy {Tag α : Type} (x : HeapArray Tag) (xi : I) (a : HeapArray Tag) (si n : I) :
    VectorM α Unit := do
  let _ ← heapCheckedCopy (fun v => .ok v) x.handle xi a.handle si n
  pure ()

/-- One step of the copying loop of `vcat` (array.jl:2353-2358) into the fresh vector `arr`. -/
def vcatCopyStep {Tag α : Type} (arr a : HeapArray Tag) (nd : I) : VectorM α (ForInStep I) := do
  let na ← heapLength a.handle
  let l ← heapLength arr.handle
  if (!decide (nd + na ≤ one + l)) = true then
    throw (Error.assertion "Concurrent modification of arrays?")
  heapColonMemoryCopy arr nd a one na
  pure (ForInStep.yield (nd + na))

/-- One run of the copying step whose assertion passed and whose copy succeeded. -/
theorem vcatCopyStep_run {Tag α : Type} (arr a : HeapArray Tag) (nd na l : I)
    (h0 h1 : VectorHeap α)
    (hal : (heapLength (α := α) a.handle).run h0 = .ok (na, h0))
    (harl : (heapLength (α := α) arr.handle).run h0 = .ok (l, h0))
    (hcond : decide (nd + na ≤ one + l) = true)
    (hcopy : (heapColonMemoryCopy arr nd a one na).run h0 = .ok ((), h1)) :
    (vcatCopyStep arr a nd).run h0 = .ok (.yield (nd + na), h1) := by
  simp only [vcatCopyStep, vector_bind_run, hal, harl, hcond, Bool.not_true, Bool.false_eq_true,
    ite_false, hcopy, vector_pure_run]
end HeapRanges
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000


/-! ## Widening collectors over typed heap arrays -/

/-- The part of Julia's type system the widening collectors consult: `isa v t` is `v isa t`,
`typeof v` is the concrete type of `v`, and `join` is `promote_typejoin`, which is a supertype of
both arguments. -/
structure TypeLattice (Tag α : Type) where
  typeof : α → Tag
  isa : α → Tag → Bool
  join : Tag → Tag → Tag
  isa_typeof : ∀ v, isa v (typeof v) = true
  isa_join_left : ∀ v s t, isa v s = true → isa v (join s t) = true
  isa_join_right : ∀ v s t, isa v t = true → isa v (join s t) = true
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section TypedCollect

attribute [local irreducible] JInt.wrap wrapInt

/-- `dest[i] = el` (the `@inbounds` store of `collect_to!`) on a typed heap array. -/
def typedSet {Tag α : Type} (a : HeapArray Tag) (x : α) (i : I) : VectorM α Unit :=
  heapSet a.handle x i

/-- `similar(dest, T)`: a fresh array of `dest`'s shape with element type `T`. -/
def typedSimilar {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (t : Tag) : VectorM α (HeapArray Tag) :=
  heapAllocateArray layout t a.dimensions

/-- `setindex_widen_up_to(dest, el, i)` (array.jl:886) on typed heap arrays, with the checked
`copyto!` of array.jl:288. -/
def typedWiden {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) :
    HeapArray Tag → α → I → VectorM α (HeapArray Tag) :=
  setindexWiden (fun t u => pure (L.join t u)) (·.elementType) L.typeof (typedSimilar layout) (fun _ => pure one) heapRangeCopy
    typedSet

/-- `collect_to!(dest, itr, offs, st)` (array.jl:895) where the remaining iteration from `st`
yields `xs`; the list iterator's step does not depend on its initial list. -/
def typedCollectTo {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (dest : HeapArray Tag) (offs : I)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  collectTo (listIterator []) (fun a el => L.isa el a.elementType) typedSet (typedWiden layout L)
    dest offs xs

theorem heapSet_run {α : Type} (heap : VectorHeap α) (handle : Nat) (slots : List (Option α))
    (hs : heap[handle]? = some slots) (i : I) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ (slots.length : Int)) (x : α) :
    (heapSet handle x i).run heap =
      .ok ((), heap.set handle (slots.set (i.val - 1).toNat (some x))) := by
  have hlt : (i.val - 1).toNat < slots.length := by clear hs; omega
  simp only [heapSet, vector_bind_run, heapSlots_run, hs, vector_lift_run, vectorGet,
    if_pos (And.intro h1 h2), List.getElem?_eq_getElem hlt, Except.map, vector_modify_run]

/-- Writing slot `pre.length + 1` of `pre ++ [none, ...]`. -/
theorem set_prefix_slot {β : Type} (pre : List β) (x : β) (k : Nat) (hk : 0 < k) :
    (pre.map some ++ List.replicate k none).set pre.length (some x) =
      (pre ++ [x]).map some ++ List.replicate (k - 1) none := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.set_append_right _ _ (by simp)]
  simp [List.replicate_succ]

/-- `collect_to_with_first!(dest::AbstractArray, v1, itr, st)` (array.jl:875) on a typed heap
array, continuing with `collect_to!`. -/
def typedCollectWithFirst {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) :
    HeapArray Tag → α → List α → List α → VectorM α (HeapArray Tag) :=
  collectWithFirstArray (fun _ => pure one) typedSet (fun d _ i st => typedCollectTo layout L d i st)
end TypedCollect
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Moving `k` slots from offset `s` to offset `d` inside the window `[o, o + n)`, reading every
source slot before any write. -/
theorem window_move (l : List β) (o d s k n : Nat) (hd : d + k ≤ n) (hs : s + k ≤ n)
    (hn : o + n ≤ l.length) :
    ((l.take (o + d) ++ (l.drop (o + s)).take k ++ l.drop (o + d + k)).drop o).take n =
      ((l.drop o).take n).take d ++ (((l.drop o).take n).drop s).take k ++
        ((l.drop o).take n).drop (d + k) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
    List.length_take, List.length_drop]
  repeat' split
  all_goals first | rfl | (congr 1; omega) | (exfalso; omega)
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorDeletion

theorem mutableMemoryref_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (i : I) :
    (mutableMemoryref handle i).run s = (.ok (a.reference.1, a.reference.2 + i - one), s) := by
  simp only [mutableMemoryref, stateExcept_bind, mutableRef_run s handle a ha, stateExcept_pure]

theorem memories_set_self {s : MutableMemory α} {mem : Nat} {slots : List (Option α)}
    (hm : s.memories[mem]? = some slots) : s.memories.set mem slots = s.memories := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hm
  rw [← hget]
  exact List.set_getElem_self hlt

/-- `unsafe_copyto!(a, doffs, a, soffs, k)` inside one vector window (array.jl:276), with
memmove semantics. -/
theorem vwCopy_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (doffs soffs k : I)
    (hk : 0 ≤ k.val) (hd1 : 1 ≤ doffs.val) (hde : doffs.val - 1 + k.val ≤ n.val)
    (hs1 : 1 ≤ soffs.val) (hse : soffs.val - 1 + k.val ≤ n.val) :
    ∃ slots', (mutableCopy handle doffs handle soffs k).run s =
        (.ok (), { s with memories := s.memories.set mem slots' }) ∧
      VecAt { s with memories := s.memories.set mem slots' } handle mem off n slots' ∧
      vwWindow slots' off n = (vwWindow slots off n).take (doffs.val - 1).toNat ++
        ((vwWindow slots off n).drop (soffs.val - 1).toNat).take k.val.toNat ++
        (vwWindow slots off n).drop (doffs.val - 1 + k.val).toNat := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hdb := ival_bounds doffs
  have hsb := ival_bounds soffs
  have hkb := ival_bounds k
  by_cases hz : k.val = 0
  · have hself := memories_set_self hm
    refine ⟨slots, ?_, ?_, ?_⟩
    · rw [hself]
      have hz' : (k.val == 0) = true := by rw [hz]; rfl
      simp only [mutableCopy, unsafeCopyArray, hz', eq_self_iff_true, ite_true, stateExcept_bind,
        stateExcept_pure]
      try rfl
    · rw [hself]
      exact ⟨ha, hm, ho, hn0, he, hc⟩
    · rw [hz]
      simp
  · have hz' : (k.val == 0) = false := by simp [hz]
    have hdaddr : (off + doffs - one).val = off.val + doffs.val - 1 :=
      ival_add_sub_one _ _ (by omega)
    have hsaddr : (off + soffs - one).val = off.val + soffs.val - 1 :=
      ival_add_sub_one _ _ (by omega)
    have hmv := vwMemoryMove_run s mem mem (off + doffs - one) (off + soffs - one) k slots slots
      hm hm hk (by rw [hdaddr]; omega) (by rw [hdaddr]; omega) (by rw [hsaddr]; omega)
      (by rw [hsaddr]; omega) hc
    refine ⟨slots.take ((off + doffs - one).val - 1).toNat ++
        (slots.drop ((off + soffs - one).val - 1).toNat).take k.val.toNat ++
        slots.drop ((off + doffs - one).val - 1 + k.val).toNat, ?_, ?_, ?_⟩
    · simp only [mutableCopy, unsafeCopyArray, hz', Bool.false_eq_true, ite_false,
        stateExcept_bind, mutableMemoryref_run s handle _ ha, hmv, stateExcept_pure]
    · have hlen : (slots.take ((off + doffs - one).val - 1).toNat ++
          (slots.drop ((off + soffs - one).val - 1).toNat).take k.val.toNat ++
          slots.drop ((off + doffs - one).val - 1 + k.val).toNat).length = slots.length := by
        simp only [List.length_append, List.length_take, List.length_drop, hdaddr, hsaddr]
        omega
      have hlt := (List.getElem?_eq_some_iff.mp hm).choose
      exact ⟨ha, List.getElem?_set_self hlt, ho, hn0, by rw [hlen]; exact he,
        by rw [hlen]; exact hc⟩
    · rw [hdaddr, hsaddr]
      simp only [vwWindow]
      rw [show (off.val + doffs.val - 1 - 1).toNat = (off.val - 1).toNat + (doffs.val - 1).toNat
          by omega,
        show (off.val + soffs.val - 1 - 1).toNat = (off.val - 1).toNat + (soffs.val - 1).toNat
          by omega,
        show (off.val + doffs.val - 1 - 1 + k.val).toNat =
          (off.val - 1).toNat + (doffs.val - 1).toNat + k.val.toNat by omega,
        show (doffs.val - 1 + k.val).toNat = (doffs.val - 1).toNat + k.val.toNat by omega]
      exact window_move slots _ _ _ _ _ (by omega) (by omega) (by omega)

/-- `_deleteat!(a, i, delta)` over the concrete vector store. -/
abbrev vecDeleteat (α : Type) {layout : MemoryLayoutMetadata} : Nat → I → I → MutationM α Unit :=
  deleteatWindow (m := MutationM α) pure mutableLength Subtype.val (· + ·) (· - ·)
    (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
    (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure)

theorem window_drop_prefix (w : List β) (d i n : Nat) (hw : w.length = n) (hb : d + i ≤ n + 1)
    (hi : 1 ≤ i) :
    (w.take d ++ (w.drop 0).take (i - 1) ++ w.drop (d + (i - 1))).drop d =
      w.take (i - 1) ++ w.drop (i - 1 + d) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
    List.length_take, List.length_drop, hw]
  repeat' split
  all_goals first | rfl | (congr 1; omega) | (exfalso; omega)

theorem window_drop_suffix (w : List β) (d i n : Nat) (hw : w.length = n) (hi : 1 ≤ i)
    (hdi : d + i ≤ n + 1) :
    (w.take (i - 1) ++ (w.drop (i + d - 1)).take (n + 1 - d - i) ++
      w.drop (i - 1 + (n + 1 - d - i))).take (n - d) =
      w.take (i - 1) ++ w.drop (i - 1 + d) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
    List.length_take, List.length_drop, hw]
  repeat' split
  all_goals first | rfl | (congr 1; omega) | (exfalso; omega) |
    (symm; exact List.getElem?_eq_none (by omega)) | exact List.getElem?_eq_none (by omega)


theorem vwGet_outside (s : MutableMemory α) (handle : Nat) (v : MutableVector)
    (ha : s.arrays[handle]? = some v) (i : I) (hi : i.val < 1 ∨ v.size.val < i.val) :
    (mutableGet handle i).run s = (.error .bounds, s) := by
  have hnot : ¬ ((1 : Int) ≤ i.val ∧ i ≤ v.size) := by
    rw [jle_iff]
    omega
  simp only [mutableGet, stateExcept_bind, mutableVector_run, ha, hnot, decide_false,
    Bool.not_false, ite_true, stateExcept_throw]

theorem vwAssigned_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (q : I)
    (hq : 1 ≤ q.val ∧ q.val ≤ n.val) :
    (mutableAssigned handle q).run s =
      (.ok ((vwWindow slots off n)[(q.val - 1).toNat]?.join.isSome), s) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hqb := ival_bounds q
  have haddr : (off + q - one).val = off.val + q.val - 1 := ival_add_sub_one _ _ (by omega)
  have hin : (one ≤ q ∧ q ≤ n) := ⟨by rw [jle_iff, ival_one]; omega, by rw [jle_iff]; omega⟩
  have hidx : (vwWindow slots off n)[(q.val - 1).toNat]? =
      slots[((off + q - one).val - 1).toNat]? := by
    simp only [vwWindow, List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega), haddr]
    congr 1
    omega
  simp only [mutableAssigned, isassignedVector, mutableInBounds, mutableLength, mutableMemoryref,
    mutableRef, stateExcept_bind, mutableVector_run, ha, stateExcept_pure, hin, and_self,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false, memoryRead_run s mem slots hm, hidx]

/-- `_copy_item!(a, p, q)` stores assigned sources and applies native unset semantics
to the destination when the source is unassigned. -/
theorem vwCopyItem_run {unsetRuntime : DictLayout} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (p q : I)
    (hp : 1 ≤ p.val ∧ p.val ≤ n.val) (hq : 1 ≤ q.val ∧ q.val ≤ n.val) :
    ∃ slots', (copyItem mutableAssigned mutableGet mutableSet (mutableUnset unsetRuntime) handle p q).run s =
        (.ok (), { s with memories := s.memories.set mem slots' }) ∧
      VecAt { s with memories := s.memories.set mem slots' } handle mem off n slots' ∧
      vwWindow slots' off n = (vwWindow slots off n).set (p.val - 1).toNat
        (match (vwWindow slots off n)[(q.val - 1).toNat]?.join with
          | some value => some value
          | none => expectedUnset unsetRuntime (slots[(off.val - 1 + p.val - 1).toNat]?).join) := by
  have hasg := vwAssigned_run s handle mem off n slots h q hq
  have hwl := vwWindow_length h
  have ho := h.2.2.1
  have hlt : (q.val - 1).toNat < (vwWindow slots off n).length := by rw [hwl]; omega
  obtain ⟨v, hv⟩ : ∃ v, (vwWindow slots off n)[(q.val - 1).toNat]? = some v :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [hv] at hasg ⊢
  have hget := vwGet_run s handle mem off n slots h q hq
  rw [hv] at hget
  cases v with
  | some x =>
    refine ⟨slots.set (off.val - 1 + p.val - 1).toNat (some x), ?_, h.set _ _, ?_⟩
    · simp only [copyItem, stateExcept_bind, hasg, Option.join_some, Option.isSome_some,
        ite_true, hget, vwSet_run s handle mem off n slots h p hp x]
    · rw [vwWindow_set _ _ _ _ _ ho hp.1]
      rfl
  | none =>
    refine ⟨slots.set (off.val - 1 + p.val - 1).toNat (expectedUnset unsetRuntime (slots[(off.val - 1 + p.val - 1).toNat]?).join), ?_, h.set _ _, ?_⟩
    · simp only [copyItem, stateExcept_bind, hasg, Option.join_some, Option.isSome_none,
        Bool.false_eq_true, ite_false, vwMutableUnset_run s handle mem off n slots h p hp]
    · rw [vwWindow_set _ _ _ _ _ ho hp.1]
      rfl

theorem list_set_take_self (l : List β) (j : Nat) (v : β) : (l.set j v).take j = l.take j := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_set]
  by_cases hi : i < j
  · rw [if_pos hi, if_pos hi, if_neg (by omega)]
  · rw [if_neg hi, if_neg hi]

theorem list_set_take_succ (l : List β) (j : Nat) (v : β) (hj : j < l.length) :
    (l.set j v).take (j + 1) = l.take j ++ [v] := by
  rw [List.take_succ, list_set_take_self, List.getElem?_set_self hj]
  rfl

theorem list_set_drop_of_lt (l : List β) (j k : Nat) (v : β) (h : j < k) :
    (l.set j v).drop k = l.drop k := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_drop, List.getElem?_set]
  rw [if_neg (by omega)]
end VectorDeletion
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section FindallFamily

/-- `array_new_memory(mem, newlen)` (array.jl:1114) on the concrete store: a fresh memory of
`newlen` unassigned slots is appended and returned, every existing memory (including `mem`) is
untouched; a negative length, or a memory over Julia's size limit (`memoryFits`), raises
`ArgumentError` with the store unchanged. -/
def ArrayNewMemorySpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (s : MutableMemory α) (mem : Nat) (n : I),
    let run := (arrayNewMemory (mutableStorage (α := α) (MemoryLayoutMetadata.ofRuntime l)).allocate mem n).run s
    (n.val < 0 → run = (.error (.argument genericMemorySizeMessage), s)) ∧
    (0 ≤ n.val → ¬ memoryFits l n.val.toNat →
      run = (.error (.argument genericMemorySizeMessage), s)) ∧
    (0 ≤ n.val → memoryFits l n.val.toNat →
      run = (.ok s.memories.length,
        { s with memories := s.memories ++ [List.replicate n.val.toNat none] }))
theorem newGenericMemoryLargeLength (α : Type) (s : MutableMemory α)
    (nel : Nat) (isunion : Bool) (elsz : Nat)
    (hlarge : maxIntVal - 1 ≤ nel) :
    (newGenericMemory (mutableFreshMemory (α := α) 0) mutableFreshMemory nel isunion elsz).run s =
      (.error (.argument genericMemorySizeMessage), s) := by
  have hlarge' : 9223372036854775806 ≤ nel := by simpa [maxIntVal] using hlarge
  have hnonzero : nel ≠ 0 := by omega
  simp [newGenericMemory, hlarge', hnonzero, maxIntVal]

theorem arrayNewMemoryNegativeRun (α : Type) (l : DictLayout)
    (s : MutableMemory α) (mem : Nat) (n : I) (hn : n.val < 0) :
    (arrayNewMemory (mutableStorage (α := α) (MemoryLayoutMetadata.ofRuntime l)).allocate mem n).run s =
      (.error (.argument genericMemorySizeMessage), s) := by
  have hnRange : -(2 ^ 63 : Int) ≤ n.val ∧ n.val ≤ 2 ^ 63 - 1 := by
    simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using n.property
  have hmod : n.val % (2 ^ 64 : Int) = n.val + 2 ^ 64 := by omega
  have hnonneg : 0 ≤ n.val + (2 ^ 64 : Int) := by omega
  have hnotle : ¬ n.val + 18446744073709551616 ≤ 0 := by omega
  have hcast : (((n.val + (2 ^ 64 : Int)).toNat : Nat) : Int) = n.val + (2 ^ 64 : Int) :=
    Int.toNat_of_nonneg hnonneg
  have hthreshold : 9223372036854775806 ≤ (n.val + 18446744073709551616).toNat := by omega
  change (memoryUndef (MemoryLayoutMetadata.ofRuntime l) (mutableFreshMemory 0) mutableFreshMemory n).run s = _
  simp only [memoryUndef, memorynew, MemoryLayoutMetadata.ofRuntime]
  change (allocGenericMemory (some (allocationSummary l)) (mutableFreshMemory 0) mutableFreshMemory (n.val % 2 ^ 64).toNat).run s = _
  simp only [allocGenericMemory]
  rw [hmod]
  simp [newGenericMemory, sizeMulOverflow, sizeAddOverflow, maxIntVal,
    hnotle, hthreshold]

theorem arrayNewMemoryValidRun (α : Type) (l : DictLayout)
    (s : MutableMemory α) (mem : Nat) (n : I)
    (hn : 0 ≤ n.val) (hfit : memoryFits l n.val.toNat) :
    (arrayNewMemory (mutableStorage (α := α) (MemoryLayoutMetadata.ofRuntime l)).allocate mem n).run s =
      (.ok s.memories.length,
        {s with memories := s.memories ++ [List.replicate n.val.toNat none]}) := by
  have hmod : n.val % (2 ^ 64 : Int) = n.val := by
    have hrange : n.val ≤ 2 ^ 63 - 1 := by
      simpa [IntTy.max, IntTy.signed, IntTy.bits] using n.property.2
    omega
  have hcast : (n.val.toNat : Int) = n.val := Int.toNat_of_nonneg hn
  change (memoryUndef (MemoryLayoutMetadata.ofRuntime l) (mutableFreshMemory 0) mutableFreshMemory n).run s = _
  simp only [memoryUndef, memorynew, MemoryLayoutMetadata.ofRuntime]
  change (allocGenericMemory (some (allocationSummary l)) (mutableFreshMemory 0) mutableFreshMemory (n.val % 2 ^ 64).toNat).run s = _
  simp only [allocGenericMemory]
  rw [hmod]
  by_cases hz : n.val.toNat = 0
  · have hzeroVal : n.val = 0 := by rw [← hcast]; exact_mod_cast hz
    simp [hz, hzeroVal, mutableFreshMemory] <;> rfl
  · have hpos : 0 < n.val := by rw [← hcast]; omega
    have hnotle : ¬ n.val ≤ 0 := by omega
    generalize hl : allocationSummary l = alloc at *
    cases alloc with
    | mk size isboxed isunion =>
      have hfit' : n.val.toNat < maxIntVal - 1 ∧
          n.val.toNat * (if isboxed then 8 else size) + (if isunion then n.val.toNat else 0) < maxIntVal - 1 := by
        simpa [memoryFits] using hfit
      have hfirst : ¬ 9223372036854775806 ≤ n.val.toNat := by
        dsimp [maxIntVal] at hfit'
        omega
      have hfirstGuard : ¬ maxIntVal ≤ n.val.toNat + 1 := by
        dsimp [maxIntVal] at hfit' ⊢
        omega
      have hprod : n.val.toNat * (if isboxed then 8 else size) < 2 ^ 64 := by
        dsimp [maxIntVal] at hfit'
        omega
      have hmul : sizeMulOverflow n.val.toNat (if isboxed then 8 else size) =
          (n.val.toNat * (if isboxed then 8 else size), false) := by
        unfold sizeMulOverflow
        rw [Nat.mod_eq_of_lt hprod]
        simp [Nat.not_le_of_gt hprod]
      cases isunion
      · have hbytes : ¬ 9223372036854775806 ≤ n.val.toNat * (if isboxed then 8 else size) := by
          dsimp [maxIntVal] at hfit'
          omega
        have hbytesGuard : ¬ maxIntVal ≤ n.val.toNat * (if isboxed then 8 else size) + 1 := by
          dsimp [maxIntVal] at hfit' ⊢
          omega
        simp [newGenericMemory, hnotle, hfirstGuard, hbytesGuard, hfirst, hbytes,
          hmul, mutableFreshMemory] <;> rfl
      · have hsum : n.val.toNat * (if isboxed then 8 else size) + n.val.toNat < 2 ^ 64 := by
          dsimp [maxIntVal] at hfit'
          omega
        have hsum' : n.val.toNat + n.val.toNat * (if isboxed then 8 else size) < 2 ^ 64 := by omega
        have hbytes : ¬ 9223372036854775806 ≤ n.val.toNat + n.val.toNat * (if isboxed then 8 else size) := by
          dsimp [maxIntVal] at hfit'
          omega
        have hbytesGuard : ¬ maxIntVal ≤ (n.val.toNat + n.val.toNat * (if isboxed then 8 else size)) + 1 := by
          dsimp [maxIntVal] at hfit' ⊢
          omega
        have hadd : sizeAddOverflow n.val.toNat (n.val.toNat * (if isboxed then 8 else size)) =
            (n.val.toNat + n.val.toNat * (if isboxed then 8 else size), false) := by
          unfold sizeAddOverflow
          rw [Nat.mod_eq_of_lt hsum']
          simp [Nat.not_le_of_gt hsum']
        simp [newGenericMemory, hnotle, hfirstGuard, hbytesGuard, hfirst, hbytes,
          hmul, hadd, mutableFreshMemory] <;> rfl

theorem arrayNewMemoryOverlimitRun (α : Type) (l : DictLayout)
    (s : MutableMemory α) (mem : Nat) (n : I)
    (hn : 0 ≤ n.val) (hnot : ¬ memoryFits l n.val.toNat) :
    (arrayNewMemory (mutableStorage (α := α) (MemoryLayoutMetadata.ofRuntime l)).allocate mem n).run s =
      (.error (.argument genericMemorySizeMessage), s) := by
  have hmod : n.val % (2 ^ 64 : Int) = n.val := by
    have hrange : n.val ≤ 2 ^ 63 - 1 := by
      simpa [IntTy.max, IntTy.signed, IntTy.bits] using n.property.2
    omega
  have hcast : (n.val.toNat : Int) = n.val := Int.toNat_of_nonneg hn
  have hnonzero : n.val.toNat ≠ 0 := by
    intro hz
    apply hnot
    simp [memoryFits, hz, maxIntVal]
  have hnotle : ¬ n.val ≤ 0 := by
    intro hle
    have hzero : n.val = 0 := by omega
    apply hnot
    simp [memoryFits, hcast, hzero, maxIntVal]
  change (memoryUndef (MemoryLayoutMetadata.ofRuntime l) (mutableFreshMemory 0) mutableFreshMemory n).run s = _
  simp only [memoryUndef, memorynew, MemoryLayoutMetadata.ofRuntime]
  change (allocGenericMemory (some (allocationSummary l)) (mutableFreshMemory 0) mutableFreshMemory (n.val % 2 ^ 64).toNat).run s = _
  simp only [allocGenericMemory]
  rw [hmod]
  simp only [if_neg hnonzero]
  generalize hl : allocationSummary l = alloc at *
  cases alloc with
  | mk size isboxed isunion =>
    let width := if isboxed then 8 else size
    change (newGenericMemory (mutableFreshMemory 0) mutableFreshMemory n.val.toNat isunion width).run s = _
    cases isunion
    · have hnot' : ¬ (n.val.toNat < maxIntVal - 1 ∧ n.val.toNat * width < maxIntVal - 1) := by
        simpa [memoryFits, width] using hnot
      by_cases hlen : n.val.toNat < maxIntVal - 1
      · have hbad : 9223372036854775806 ≤ n.val.toNat * width := by
          dsimp [maxIntVal] at hnot' hlen ⊢
          omega
        by_cases hov : 2 ^ 64 ≤ n.val.toNat * width
        · have hmul : sizeMulOverflow n.val.toNat width =
              (n.val.toNat * width % 2 ^ 64, true) := by
            unfold sizeMulOverflow
            simp [hov]
          simp [newGenericMemory, width, hmul, hnotle, mutableFreshMemory]
        · have hprod : n.val.toNat * width < 2 ^ 64 := by omega
          have hmul : sizeMulOverflow n.val.toNat width =
              (n.val.toNat * width, false) := by
            unfold sizeMulOverflow
            rw [Nat.mod_eq_of_lt hprod]
            simp [Nat.not_le_of_gt hprod]
          have hbad' : maxIntVal - 1 ≤ n.val.toNat * width := by
            simpa [maxIntVal] using hbad
          simp [newGenericMemory, width, hmul, hbad', hnotle, mutableFreshMemory]
      · have hlenbad : maxIntVal - 1 ≤ n.val.toNat := by
          dsimp [maxIntVal] at hlen ⊢
          omega
        exact newGenericMemoryLargeLength α s n.val.toNat false width hlenbad
    · have hnot' : ¬ (n.val.toNat < maxIntVal - 1 ∧
          n.val.toNat * width + n.val.toNat < maxIntVal - 1) := by
        simpa [memoryFits, width] using hnot
      by_cases hlen : n.val.toNat < maxIntVal - 1
      · have hbad : 9223372036854775806 ≤ n.val.toNat * width + n.val.toNat := by
          dsimp [maxIntVal] at hnot' hlen ⊢
          omega
        have hfirstGuard : ¬ maxIntVal ≤ n.val.toNat + 1 := by
          dsimp [maxIntVal] at hlen ⊢
          omega
        by_cases hov : 2 ^ 64 ≤ n.val.toNat * width
        · have hmul : sizeMulOverflow n.val.toNat width =
              (n.val.toNat * width % 2 ^ 64, true) := by
            unfold sizeMulOverflow
            simp [hov]
          simp [newGenericMemory, width, hmul, hfirstGuard, hnotle, mutableFreshMemory]
        · have hprod : n.val.toNat * width < 2 ^ 64 := by omega
          have hmul : sizeMulOverflow n.val.toNat width =
              (n.val.toNat * width, false) := by
            unfold sizeMulOverflow
            rw [Nat.mod_eq_of_lt hprod]
            simp [Nat.not_le_of_gt hprod]
          by_cases haddOver : 2 ^ 64 ≤ n.val.toNat + n.val.toNat * width
          · have hadd : sizeAddOverflow n.val.toNat (n.val.toNat * width) =
                ((n.val.toNat + n.val.toNat * width) % 2 ^ 64, true) := by
              unfold sizeAddOverflow
              simp [haddOver]
            simp [newGenericMemory, width, hmul, hadd, hfirstGuard, hnotle, mutableFreshMemory]
          · have hsum : n.val.toNat + n.val.toNat * width < 2 ^ 64 := by omega
            have hadd : sizeAddOverflow n.val.toNat (n.val.toNat * width) =
                (n.val.toNat + n.val.toNat * width, false) := by
              unfold sizeAddOverflow
              rw [Nat.mod_eq_of_lt hsum]
              simp [Nat.not_le_of_gt hsum]
            have hbytesGuard : maxIntVal ≤ (n.val.toNat + n.val.toNat * width) + 1 := by
              dsimp [maxIntVal] at hbad ⊢
              omega
            simp [newGenericMemory, width, hmul, hadd, hbytesGuard, hfirstGuard,
              hnotle, mutableFreshMemory]
      · have hlenbad : maxIntVal - 1 ≤ n.val.toNat := by
          dsimp [maxIntVal] at hlen ⊢
          omega
        exact newGenericMemoryLargeLength α s n.val.toNat true width hlenbad

theorem arrayNewMemorySpec : ArrayNewMemorySpec := by
  intro α l s mem n
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro hn
    exact arrayNewMemoryNegativeRun α l s mem n hn
  · intro hn hnot
    exact arrayNewMemoryOverlimitRun α l s mem n hn hnot
  · intro hn hfit
    exact arrayNewMemoryValidRun α l s mem n hn hfit
end FindallFamily
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

/-- One vector and one set. -/
structure VecSet (α : Type) where
  vec : List α
  set : List α

abbrev SetM (α : Type) := StateM (VecSet α)
end VectorSets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

/-- `x ∉ seen` for the tracked set. -/
def setNotin (x : α) (_ : Unit) : SetM α Bool := do
  return !decide (x ∈ (← get).set)

/-- `x ∈ keep` for the tracked set. -/
def setIn (x : α) (_ : Unit) : SetM α Bool := do
  return decide (x ∈ (← get).set)

/-- `push!(seen, x)`. -/
def setPush (_ : Unit) (x : α) : SetM α Unit :=
  modify fun st => { st with set := st.set ++ [x] }

/-- `pop!(keep, x)`. -/
def setPop (_ : Unit) (x : α) : SetM α Unit :=
  modify fun st => { st with set := st.set.erase x }

/-- The values of `xs` not in `seen`, each once, in order of first appearance. -/
def dedupFrom (seen : List α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ seen then dedupFrom seen xs else x :: dedupFrom (seen ++ [x]) xs

/-- The first occurrence in `xs` of each value of `keep`, in order. -/
def firstIn (keep : List α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ keep then x :: firstIn (keep.erase x) xs else firstIn keep xs

/-- What remains of `keep` after `firstIn keep xs` has taken its values. -/
def firstInRest (keep : List α) : List α → List α
  | [] => keep
  | x :: xs => if x ∈ keep then firstInRest (keep.erase x) xs else firstInRest keep xs
end VectorSets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The value `setindex!(A::Array{T}, x, i::Int)` (array.jl:1031) stores: `x` itself when it is
already a `T`, otherwise `convert(T, x)`. -/

def storedValue (already : α → Bool) (convert : α → Except Error α) (x : α) : Except Error α :=
  if already x then .ok x else convert x

/-- `deleteat!(a, inds)` (array.jl:1940): `_deleteat!` with the `Nowhere()` sink, whose `push!`
and `_growend!` (array.jl:1944-1945) do nothing. -/

abbrev mutableDeleteatList {α : Type} (layout : MemoryLayoutMetadata) (a : Nat) (inds : List I) : MutationM α Nat :=
  deleteatIndices mutableLength listIterator Subtype.val (· + one) mutableBounds
    mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
    (· - ·) (deleteend (mutableStorage layout) pure) a inds

/-- `deleteat!(a, inds::AbstractVector)` (array.jl:1941) for an `Int` index vector, which
`to_indices(a, (inds,))` returns unchanged. -/

abbrev mutableDeleteatVector {α : Type} (layout : MemoryLayoutMetadata) (a : Nat) (inds : List I) : MutationM α Nat :=
  deleteatIndexVector (fun _ inds => pure inds) id mutableLength listIterator Subtype.val
    (· + one) mutableBounds mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
    (· - ·) (deleteend (mutableStorage layout) pure) a inds

/-- `f(ai)::Bool` for a predicate returning any value: `TypeError` unless the value is a `Bool`. -/

def boolResult (f : α → Except Error (Option Bool)) (x : α) : Except Error Bool :=
  match f x with
  | .error e => .error e
  | .ok (some b) => .ok b
  | .ok none => .error (.typeError "typeassert")
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

/-- A single fresh allocation's reference slots. These primitives belong to
`essentials.jl` and `memory.jl`; stores in literals use array.jl's safe setter. -/
abbrev LiteralM (α : Type) := StateM (List (Option α))

/-- Fixed-length, one-based memory primitives from essentials.jl and memory.jl. -/
abbrev SlotM (α : Type) := ExceptT Error (StateM (I → Option α))

def updateSlot (slots : I → Option α) (i : I) (value : Option α) : I → Option α :=
  fun j => if j = i then value else slots j

def slotBounds (n : Nat) (_a : Unit) (i : I) : SlotM α Unit :=
  fun slots => (if 1 ≤ i.val ∧ i.val ≤ (n : Int) then .ok () else .error .bounds, slots)

def stateExceptLift {σ β : Type} (value : Except Error β) : ExceptT Error (StateM σ) β :=
  fun state => (value, state)

abbrev shapedCollectorAllocate {Tag α Axes : Type} (layout : Tag → Option MemoryLayout)
    (toShape : Axes → VectorM α (List I)) (target : Tag) (axes : Axes) :
    VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarStorageOneTo toShape
    (fun ty dims => JuliaLean.base.abstractarray.similarStorageDims
      (fun _ dims => heapAllocateIntDims layout target dims) ty dims)
    (HeapArray Tag) axes

abbrev collectHeapEmpty {Tag α : Type} (a : HeapArray Tag) : VectorM α Bool := do
  let xs ← heapSlots a.handle
  pure xs.isEmpty

/-- The range's iteration values, defined without indexing arithmetic. -/
def steppedRangeValues (first step : Int) (n : Nat) : List Int :=
  (List.range n).map (fun k : Nat => first + (k : Int) * step)
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
section VectorWindows
/-- `Int(n)` (boot.jl) for a length of any BitInteger type, as the model's `toInt`. -/
def lengthToInt {α : Type} {t : IntTy} (x : JInt t) : MutationM α I :=
  stateExceptLift ((JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact))
end VectorWindows
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

def heapColonMemoryCopy {Tag α : Type} (dest : HeapArray Tag) (doffs : I)
    (source : HeapArray Tag) (soffs n : I) : VectorM α Unit := do
  let _ ← unsafeCopyArray (fun n : I => decide (n.val = 0))
    (fun a i => pure (a.handle, i)) (fun a i => pure (a.handle, i))
    (heapCopyReferences (fun x => .ok x)) dest doffs source soffs n
  pure ()
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
/-- `length(lo:hi)` of a `UnitRange{Int}`. -/
def unitRangeLength (r : I × I) : I := if r.2 < r.1 then zero else r.2 - r.1 + one

/-- `copyto!(X, firstindex(X), A, first(I), lI)`: the checked `copyto!` of array.jl:288. -/
def heapRangeCopy {Tag α : Type} (x : HeapArray Tag) (xi : I) (a : HeapArray Tag) (si n : I) :
    VectorM α Unit := do
  let _ ← heapCheckedCopy (fun v => .ok v) x.handle xi a.handle si n
  pure ()
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
/-- The part of Julia's type system the widening collectors consult: `isa v t` is `v isa t`,
`typeof v` is the concrete type of `v`, and `join` is `promote_typejoin`, which is a supertype of
both arguments. -/
structure TypeLattice (Tag α : Type) where
  typeof : α → Tag
  isa : α → Tag → Bool
  join : Tag → Tag → Tag
  isa_typeof : ∀ v, isa v (typeof v) = true
  isa_join_left : ∀ v s t, isa v s = true → isa v (join s t) = true
  isa_join_right : ∀ v s t, isa v t = true → isa v (join s t) = true
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
/-- `dest[i] = el` (the `@inbounds` store of `collect_to!`) on a typed heap array. -/
def typedSet {Tag α : Type} (a : HeapArray Tag) (x : α) (i : I) : VectorM α Unit :=
  heapSet a.handle x i

/-- `similar(dest, T)`: a fresh array of `dest`'s shape with element type `T`. -/
def typedSimilar {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (t : Tag) : VectorM α (HeapArray Tag) :=
  heapAllocateArray layout t a.dimensions

/-- `setindex_widen_up_to(dest, el, i)` (array.jl:886) on typed heap arrays, with the checked
`copyto!` of array.jl:288. -/
def typedWiden {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) :
    HeapArray Tag → α → I → VectorM α (HeapArray Tag) :=
  setindexWiden (fun t u => pure (L.join t u)) (·.elementType) L.typeof (typedSimilar layout) (fun _ => pure one) heapRangeCopy
    typedSet

/-- `collect_to!(dest, itr, offs, st)` (array.jl:895) where the remaining iteration from `st`
yields `xs`; the list iterator's step does not depend on its initial list. -/
def typedCollectTo {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) (dest : HeapArray Tag) (offs : I)
    (xs : List α) : VectorM α (HeapArray Tag) :=
  collectTo (listIterator []) (fun a el => L.isa el a.elementType) typedSet (typedWiden layout L)
    dest offs xs

/-- `collect_to_with_first!(dest::AbstractArray, v1, itr, st)` (array.jl:875) on a typed heap
array, continuing with `collect_to!`. -/
def typedCollectWithFirst {Tag α : Type} (layout : Tag → Option MemoryLayout) (L : TypeLattice Tag α) :
    HeapArray Tag → α → List α → List α → VectorM α (HeapArray Tag) :=
  collectWithFirstArray (fun _ => pure one) typedSet (fun d _ i st => typedCollectTo layout L d i st)
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
section VectorSets
/-- One vector and one set. -/
structure VecSet (α : Type) where
  vec : List α
  set : List α

abbrev SetM (α : Type) := StateM (VecSet α)
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
section VectorSets

variable {α : Type} [DecidableEq α]

/-- `x ∈ keep` for the tracked set. -/
def setIn (x : α) (_ : Unit) : SetM α Bool := do
  return decide (x ∈ (← get).set)

/-- `push!(seen, x)`. -/
def setPush (_ : Unit) (x : α) : SetM α Unit :=
  modify fun st => { st with set := st.set ++ [x] }
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

/-- `f(ai)::Bool` for a predicate returning any value: `TypeError` unless the value is a `Bool`. -/
def boolResult (f : α → Except Error (Option Bool)) (x : α) : Except Error Bool :=
  match f x with
  | .error e => .error e
  | .ok (some b) => .ok b
  | .ok none => .error (.typeError "typeassert")

/-- A `Vector` in mutable memory, iterated as Julia's `iterate(a, i)` does: `a[i]` is read when
the loop reaches `i`, for `i` in `1:length(a)`. -/
structure VectorRef where
  handle : Nat

instance {α : Type} : ForIn (MutationM α) VectorRef α where
  forIn a init f := do
    let n ← mutableLength a.handle
    forIn (intRange one n) init fun i b => do f (← mutableGet a.handle i) b

/-- A typed vector in mutable memory: its element type and handle. -/
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
      let _ ← sizehint (mutableStorage (layout d.1)) pure
        (growbeg (mutableStorage (layout d.1)) pure (growbegInternal (mutableStorage (layout d.1))))
        (growend (mutableStorage (layout d.1)) pure (growendInternal (mutableStorage (layout d.1)))) d.2 n false true
      pure d)
    (fun _ => false) (fun _ _ => pure ())
    (fun new dest => do
      let _ ← appendVector (m := MutationM α) (fun _ => false) pure mutableLength pure
        (growend (mutableStorage (layout new.1)) pure (growendInternal (mutableStorage (layout new.1)))) mutableLength
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

/-- `_collect(c, itr, ::EltypeUnknown, ::SizeUnknown)` (array.jl:855) for an iterator yielding
`xs` with inferred element type `et`, `_similar_for` allocating a fresh empty vector of that
type. -/
def typedCollectUnknown {Tag α : Type} (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag α) (et : Tag) (xs : List α) :
    MutationM α (TypedVector Tag) :=
  collectEltypeUnknown (fun _ => et)
    (fun (c : Nat) t _ (_ : Unit) => typedEmpty layout (t, c) t)
    (typedGrowFirst layout L) 0 xs ()
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

/-! ## Round four: arguments of every documented type

The `::Integer` methods of array.jl accept every `Integer` type. `IntegerValue` is such an
argument: a BitInteger of any width (int.jl, whose operations are the `JuliaLean.base.int`
definitions), a `Bool`, or a value of an `Integer` type with no Lean model, given by its
mathematical value: `BigInt` (gmp.jl is not modelled) and user-defined `Integer` types. The
operations array.jl applies to a `Bool` or an unmodelled integer (`Int(x)`, `+`, `-`, `*`, `<=`)
are the typed parameters of `BigIntegerOps`; their only laws (`BigIntegerOps.Lawful`) are the
documented ones: `convert(Int, x)` returns the `Int` equal to `x` or throws `InexactError`, and
`BigInt` arithmetic and comparison are exact. -/

/-- `Int(x)` succeeds for a BitInteger `x`: its value lies in `typemin(Int):typemax(Int)`. -/
def intFits {t : IntTy} (x : JInt t) : Prop := IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max

/-- A Julia `Integer` argument. -/
inductive IntegerValue where
  | bit (t : IntTy) (x : JInt t)
  | bool (b : Bool)
  | big (v : Int)
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
namespace IntegerValue

/-- The mathematical value (`true` is 1). -/
def val : IntegerValue → Int
  | .bit _ x => x.val
  | .bool b => if b then 1 else 0
  | .big v => v

def isBool : IntegerValue → Bool
  | .bool _ => true
  | _ => false

/-- `Int(x)` succeeds: the value lies in `typemin(Int):typemax(Int)`. -/
def fits (x : IntegerValue) : Prop := IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max

/-- An `Int` argument. -/
def ofInt (x : I) : IntegerValue := .bit .i64 x
end IntegerValue
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

/-- The operations array.jl applies to a `Bool` (boot.jl's conversions of `Bool`) or to an
`Integer` of a type with no Lean model (`BigInt`, gmp.jl; user-defined integers): typed
parameters. `convert t v` is `convert(T, x)` to the BitInteger type `T` of width `t`. -/
structure BigIntegerOps where
  convert : (t : IntTy) → Int → Except Error (JInt t)
  add : Int → Int → Int
  sub : Int → Int → Int
  mul : Int → Int → Int
  le : Int → Int → Bool

/-- The documented laws of those operations: `convert(T, x)` returns the `T` equal to `x`, or
throws `InexactError` when there is none; `+`, `-`, `*` and `<=` are exact. -/
def BigIntegerOps.Lawful (ops : BigIntegerOps) : Prop :=
  (∀ t v, ops.convert t v = if t.min ≤ v ∧ v ≤ t.max then .ok (JInt.wrap t v)
    else .error .inexact) ∧
  (∀ a b, ops.add a b = a + b) ∧ (∀ a b, ops.sub a b = a - b) ∧ (∀ a b, ops.mul a b = a * b) ∧
  (∀ a b, ops.le a b = decide (a ≤ b))
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
namespace IntegerValue

/-- `convert(T, x)` to a BitInteger type: int.jl's `convert` for a BitInteger, the parameter
otherwise. -/
def convertTo (ops : BigIntegerOps) (t : IntTy) : IntegerValue → Except Error (JInt t)
  | .bit _ x => (JuliaLean.base.int.convert t x).mapError (fun _ => .inexact)
  | .bool b => ops.convert t (if b then 1 else 0)
  | .big v => ops.convert t v

/-- `Int(x)`. -/
def toInt (ops : BigIntegerOps) (x : IntegerValue) : Except Error I := x.convertTo ops .i64

/-- `x` is a value of the BitInteger type of width `t` itself (`x isa T`). -/
def isBit (t : IntTy) : IntegerValue → Bool
  | .bit u _ => decide (u = t)
  | _ => false

/-- `x + y` for an `Int` `x` (promotion.jl: both operands converted to `promote_type(Int, T)`):
int.jl's promoted `+` for a BitInteger `y` and for a `Bool` (promoted to `Int`), `BigInt` `+`
otherwise. -/
def addInt (ops : BigIntegerOps) (x : I) : IntegerValue → IntegerValue
  | .bit _ y => .bit _ (JuliaLean.base.int.binop JuliaLean.base.int.add x y)
  | .bool b => .bit .i64 (JuliaLean.base.int.add x (JInt.wrap .i64 (if b then 1 else 0)))
  | .big v => .big (ops.add x.val v)

/-- `x - y` for an `Int` `x`, promoted as in `addInt`. -/
def subFromInt (ops : BigIntegerOps) (x : I) : IntegerValue → IntegerValue
  | .bit _ y => .bit _ (JuliaLean.base.int.binop JuliaLean.base.int.sub x y)
  | .bool b => .bit .i64 (JuliaLean.base.int.sub x (JInt.wrap .i64 (if b then 1 else 0)))
  | .big v => .big (ops.sub x.val v)

/-- `y - x` for an `Int` `x`, promoted as in `addInt`. -/
def subInt (ops : BigIntegerOps) (y : IntegerValue) (x : I) : IntegerValue :=
  match y with
  | .bit _ y => .bit _ (JuliaLean.base.int.binop JuliaLean.base.int.sub y x)
  | .bool b => .bit .i64 (JuliaLean.base.int.sub (JInt.wrap .i64 (if b then 1 else 0)) x)
  | .big v => .big (ops.sub v x.val)

/-- `y <= x` for an `Int` `x`: int.jl's mixed `<=`, or the parameter. -/
def leInt (ops : BigIntegerOps) (y : IntegerValue) (x : I) : Bool :=
  match y with
  | .bit _ y => JuliaLean.base.int.le y x
  | .bool b => JuliaLean.base.int.le (JInt.wrap .i64 (if b then 1 else 0)) x
  | .big v => ops.le v x.val

/-- `x <= y` for an `Int` `x`. -/
def intLe (ops : BigIntegerOps) (x : I) (y : IntegerValue) : Bool :=
  match y with
  | .bit _ y => JuliaLean.base.int.le x y
  | .bool b => JuliaLean.base.int.le x (JInt.wrap .i64 (if b then 1 else 0))
  | .big v => ops.le x.val v
end IntegerValue
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

/-- `Int(x)` in the vector store. -/
def integerToInt {α : Type} (ops : BigIntegerOps) (x : IntegerValue) : MutationM α I :=
  stateExceptLift (x.toInt ops)

/-- indices.jl's errors as array.jl's. -/
def indexError : JuliaLean.base.indices.IndexError → Error
  | .methodError fn _ => .method fn
  | .argumentError message => .argument message
  | .dimensionMismatch message => .dimensionMismatch message
  | .boundsError => .bounds
  | .core _ => .inexact

/-- `to_index(a, i)` for an `Array` `a` and an `Integer` `i` (indices.jl): `to_index_Array`
(`reinterpret(Int, i)` for a `UInt`, `convert(Int, i)` for every other BitInteger),
`to_index(::Bool)`'s `ArgumentError`, and `to_index(i::Integer) = convert(Int, i)` for the other
integers. -/
def arrayToIndex (ops : BigIntegerOps) : IntegerValue → Except Error I
  | .bit t x => (JuliaLean.base.indices.to_index_Array t () x).mapError indexError
  | .bool b => (JuliaLean.base.indices.to_index_Bool b).mapError indexError
  | .big v => (JuliaLean.base.indices.to_index_Integer
      (fun v => (ops.convert .i64 v).mapError (fun _ => .core (.inexactError "Int64"))) pure v).mapError
      indexError

/-- `a[i]` for a `Vector` of the store and an `Integer` `i` (abstractarray.jl's
`getindex(A, I...)` through `to_indices`): `to_index(a, i)`, then the Array read of essentials.jl. -/
def vectorGetInteger {α : Type} (ops : BigIntegerOps) (a : Nat) (i : IntegerValue) :
    MutationM α α := do
  mutableGet a (← stateExceptLift (arrayToIndex ops i))

/-- A documented valid index of a vector of length `n`: an index that is not a `Bool`, with value
in `1:n`. -/
def IntegerValue.validIndex (i : IntegerValue) (n : Nat) : Prop :=
  i.isBool = false ∧ 1 ≤ i.val ∧ i.val ≤ (n : Int)


/-! ### Deletion inside a vector, every `Integer` index and count type -/

/-- `_deleteat!(a, i, delta)` (array.jl:1307) on the concrete vector store, for an index and a
count of any `Integer` types: `Int(i)` is `IntegerValue.toInt`; the mixed `Int`/`delta`
arithmetic `i + delta`, `2i + delta`, `len + 1 - delta - i` and `<=` is promotion.jl's promoted
arithmetic (`IntegerValue.addInt`, `subFromInt`, `subInt`, `leInt`); `unsafe_copyto!` is the
memory.jl copy `mutableCopy` (which takes `Int` offsets, reached through `Int(·)`), and
`_deletebeg!` / `_deleteend!` are the model's. -/
abbrev windowDelete (α : Type) {layout : MemoryLayoutMetadata} (ops : BigIntegerOps) :
    Nat → IntegerValue → IntegerValue → MutationM α Unit :=
  deleteatWindow (m := MutationM α) (integerToInt ops) mutableLength IntegerValue.val
    (fun a d => d.addInt ops a) (fun a d => d.subFromInt ops a)
    (fun p l => p.leInt ops l) (fun m i => m.subInt ops i)
    (fun a d b s n => do mutableCopy a (← integerToInt ops d) b s n)
    (fun a d b s n => do mutableCopy a d b (← integerToInt ops s) (← integerToInt ops n))
    (deletebeg (mutableStorage layout) (integerToInt ops)) (deleteend (mutableStorage layout) (integerToInt ops))

def heapArrayLength {Tag α : Type} (a : HeapArray Tag) : VectorM α I := heapLength a.handle

/-- `eachindex(IndexLinear(), A::Union{Array, Memory}) = unchecked_oneto(length(A))`
(abstractarray.jl:394, `eachindexDense`). -/
def heapLinearIndices {Tag α : Type} (a : HeapArray Tag) :
    VectorM α (JuliaLean.base.range.OneTo I) :=
  JuliaLean.base.abstractarray.eachindexDense heapArrayLength
    (fun n : I => (⟨n⟩ : JuliaLean.base.range.OneTo I)) a

/-- `checkbounds(A, i)` for an Array of any shape or a Memory and an `Integer` index `i`
(abstractarray.jl): `checkindex(Bool, inds::AbstractUnitRange, i::Real)` (`checkindexReal`) over
the linear indices, with range.jl's `first`/`last` of `OneTo` and the promoted `<=`;
`BoundsError` when it is false. -/
def heapCheckLinear {Tag α : Type} (ops : BigIntegerOps) (a : HeapArray Tag) (i : IntegerValue) :
    VectorM α Unit := do
  let inds ← heapLinearIndices a
  let inbounds := JuliaLean.base.abstractarray.checkindexReal
    (fun r => .ok (JuliaLean.base.range.first_OneTo r))
    (fun r => match JuliaLean.base.range.last_OrdinalRange (T := I) (A := I) r with
      | .ok v => .ok v
      | .error _ => .error (.julia .boundsError))
    (fun l i => .ok (IntegerValue.intLe ops l i)) (fun i l => .ok (IntegerValue.leInt ops i l))
    inds i
  match inbounds with
  | .ok true => pure ()
  | _ => throw .bounds

/-- `_copyto_impl!(dest, doffs, src, soffs, n)` (array.jl:299) between Arrays of any shape or
Memories on the shared heap, for offsets and a count of any `Integer` types: `checkbounds` and
`length` as above, `length(dest) - doffs + 1` (reached only after `checkbounds(dest, doffs)`, so
exact), `Int(·)`, `memoryref(ref, i)` (`heapReference`) and the memory.jl
`unsafe_copyto!(::MemoryRef, ::MemoryRef, n)`, which reads the whole source window, applies the
element copy `convert` (the identity for equal element types; for different element types the
memory.jl conversion, a parameter with no law) and then writes (`heapCopyReferences`). -/
abbrev heapCopyImpl (α Tag : Type) (ops : BigIntegerOps)
    (convert : Option α → Except Error (Option α)) :
    HeapArray Tag → IntegerValue → HeapArray Tag → IntegerValue → IntegerValue →
      VectorM α (HeapArray Tag) :=
  copytoImpl
    (fun n => pure (decide (n.val = 0))) (fun n => pure (decide (n.val > 0)))
    heapArrayLength heapArrayLength (heapCheckLinear ops) (heapCheckLinear ops)
    (fun len d => pure (JInt.wrap .i64 (len.val - d.val)))
    (fun len s => pure (JInt.wrap .i64 (len.val - s.val)))
    (fun a b => pure (a + b)) (fun a b => pure (a + b))
    (fun n rem => pure (decide (n.val ≤ rem.val)))
    (fun n rem => pure (decide (n.val ≤ rem.val)))
    (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
    (fun d => StateT.lift (d.toInt ops)) (fun s => StateT.lift (s.toInt ops))
    (fun n => StateT.lift (n.toInt ops))
    (fun a i => heapReference a.handle i) (fun a i => heapReference a.handle i)
    (heapCopyReferences convert)

abbrev ByteM := StateT JuliaLean.base.pointer.ByteHeap (Except Error)

/-- A C call of cmem.jl run on the current byte heap; a failed `ccall` argument conversion is
Julia's `InexactError`. -/
def byteCall (call : JuliaLean.base.pointer.ByteHeap → Jl (JuliaLean.base.pointer.ByteHeap × β)) :
    ByteM β := do
  match call (← get) with
  | .ok (heap, r) => set heap; pure r
  | .error _ => throw .inexact

def bytePtr (address : Nat) : JuliaLean.base.pointer.Ptr Unit := ⟨JInt.wrap .u64 address⟩

/-- The C library of cmem.lean: `StandardC.standardCMemoryOps`. -/
abbrev cLibrary : JuliaLean.base.cmem.CMemoryOps := JuliaLean.base.cmem.StandardC.standardCMemoryOps

/-- A mutable `AbstractArray` of a type whose indexing has no Lean model (any user-defined array
type): its state `σ`, and `eachindex(A)`, reading `A[i]` and `setindex!(A, x, i)` as typed
parameters. -/
structure MutableArrayInterface (σ K α : Type) where
  eachindex : σ → List K
  get : σ → K → Option α
  set : σ → α → K → Except Error σ

/-- The documented interface laws (manual, "Interfaces: Abstract Arrays"; `setindex!` docstring:
"Store values from array `X` within some subset of `A`"): `setindex!(A, x, i)` at an index of
`eachindex(A)` succeeds, keeps the index set, stores `x` at `i` and changes no other element. -/
def MutableArrayInterface.Lawful {σ K α : Type} (A : MutableArrayInterface σ K α) : Prop :=
  ∀ s x i, i ∈ A.eachindex s → ∃ s', A.set s x i = .ok s' ∧ A.eachindex s' = A.eachindex s ∧
    A.get s' i = some x ∧ ∀ j, j ≠ i → A.get s' j = A.get s j

def heapSize {Tag α : Type} (a : HeapArray Tag) (d : I) : VectorM α I :=
  if d.val < 1 then throw .bounds
  else pure (JInt.wrap .i64 ((a.dimensions[(d.val - 1).toNat]?.getD 1 : Nat) : Int))

inductive IntegerUnitRange where
  | bit (t : IntTy) (r : JuliaLean.base.range.UnitRange (JInt t))
  | big (lo hi : Int)
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

def first : IntegerUnitRange → IntegerValue
  | .bit _ r => .bit _ r.start
  | .big lo _ => .big lo

/-- `isempty(r)`: range.jl's `isempty(r::AbstractUnitRange)` (`first(r) > last(r)`). -/
def isempty : IntegerUnitRange → Bool
  | .bit _ r => decide (r.stop.val < r.start.val)
  | .big lo hi => decide (hi < lo)

/-- `length(r)`: range.jl's checked `length` for a BitInteger `UnitRange` (`lengthUnit`, which can
raise `OverflowError`), `last - first + 1` in `BigInt` otherwise. -/
def length (ops : BigIntegerOps) : IntegerUnitRange → Except Error IntegerValue
  | .bit _ r => match JuliaLean.Proofs.base.range.lengthUnit r with
    | .ok n => .ok (.bit _ n)
    | .error _ => .error .overflow
  | .big lo hi => .ok (.big (ops.add (ops.sub hi lo) 1))
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

def identityKey {K : Type} (ops : JuliaLean.base.set.DictRuntime K) :
    JuliaLean.base.dict.KeyConv K K :=
  ⟨some, fun x => .ok x, ops.equal⟩

/-- A failing set.jl or dict.jl operation. -/
def setResultLift {β σ : Type} (r : Except γ β) : ExceptT Error (StateM σ) β :=
  match r with
  | .ok b => pure b
  | .error _ => throw (Error.assertion "Set operation failed")

/-- `Set(b)` (set.jl): a fresh `Set` holding the values of `b`, inserted with set.jl's `push!`. -/
def setOfValues {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (values : List K) :
    MutationM I (JuliaLean.base.set.SetModel K) :=
  setResultLift (values.foldlM (fun s x => JuliaLean.base.set.setPush ops (identityKey ops) x s)
    (JuliaLean.base.set.setConstructorEmpty (K := K) 0))

/-- `_findin(x, b)` (array.jl:2905: `_findin(a, Set(b))`) and `_findin(x, b::AbstractSet)`
(array.jl:2898): `Set(b)` is set.jl's, `ai in b` set.jl's `in`, and the indices are pushed with
the store's `push!` into a fresh `Vector{Int}()`. -/
def setFindin {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (xs ys : List K) :
    MutationM I Nat :=
  findin (setOfValues ops)
    (findinSet (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
      (fun values => (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1)))
      (fun x s => setResultLift (JuliaLean.base.set.setIn ops x s))
      (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout))) xs ys

def vectorSizehint {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (sz : I) (first shrink : Bool) : MutationM α Unit := do
  let _ ← sizehint (mutableStorage layout) pure
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a sz first shrink
  pure ()

/-- `push!(a::Vector{T}, item::T)` (array.jl:1361) with `_growend!` on the store. -/
def vectorPushTyped {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (x : α) : MutationM α Unit := do
  let _ ← push1361 (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
    mutableLength mutableSet a x
  pure ()

abbrev SetVecM (K : Type) := StateT (JuliaLean.base.set.SetModel K) (MutationM K)

/-- A failing `Set` operation (a `KeyError` from `pop!`, or a dictionary error). -/
def setLiftR {K β : Type} (r : JuliaLean.base.set.Result β) : SetVecM K β :=
  match r with
  | .ok b => pure b
  | .error _ => throw (Error.assertion "Set operation failed")

/-- The members of a `Set`, in its iteration order (set.jl `iterate`). -/
def setMembers {K : Type} (s : JuliaLean.base.set.SetModel K) : List K :=
  match JuliaLean.base.set.setKeyTrace JuliaLean.base.set.setIterate s with
  | .ok keys => keys
  | .error _ => []

/-- abstractset.jl's `Calls` interface for a `Set{T}` (`.inl`) and a plain iterable given by its
values (`.inr`), with set.jl's operations; `push!` converts a key with `key` (dict.jl's
`setindex!` key conversion: a value already of type `T` is kept, otherwise `convert(T, x)` must be
`isequal` to `x`); the members abstractset.jl's `union!`, `symdiff!`, `intersect!` and `setdiff!`
call on these arguments are set.jl's, the others raise. -/
def setCallsKey (K : Type) (ops : JuliaLean.base.set.DictRuntime K)
    (key : JuliaLean.base.dict.KeyConv K K) : JuliaLean.base.abstractset.Calls K where
  C := Sum (JuliaLean.base.set.SetModel K) (List K)
  Error := JuliaLean.base.set.Error
  elements := fun c => match c with
    | .inl s => setMembers s
    | .inr xs => xs
  equal := ops.equal
  hasLength := fun c => c.isLeft
  length := fun c => match c with
    | .inl s => .ok (JuliaLean.base.set.setLength s)
    | .inr xs => .ok (JInt.wrap .i64 xs.length)
  hasFastIn := fun c => c.isLeft
  isAbstractSet := fun c => c.isLeft
  isIntegerRange := fun _ => false
  isEmptyRange := fun _ => false
  member := fun c x => match c with
    | .inl s => JuliaLean.base.set.setIn ops x s
    | .inr _ => .error (.assertion "in(x, itr) is not called on a plain iterable here")
  makeSet := fun c => match c with
    | .inl s => .ok (.inl s)
    | .inr xs => do
        let s ← xs.foldlM (fun s x => JuliaLean.base.set.setPush ops key x s)
          (JuliaLean.base.set.setConstructorEmpty (K := K) 0)
        pure (.inl s)
  empty := fun _ => .ok (.inl (JuliaLean.base.set.setConstructorEmpty (K := K) 0))
  emptyMutable := fun _ _ => .ok (.inl (JuliaLean.base.set.setConstructorEmpty (K := K) 0))
  emptyMutableDefault := fun _ => .ok (.inl (JuliaLean.base.set.setConstructorEmpty (K := K) 0))
  copy := fun c => match c with
    | .inl s => .ok (.inl (JuliaLean.base.set.setCopy ops s))
    | .inr xs => .ok (.inr xs)
  copyMutable := fun c => match c with
    | .inl s => .ok (.inl (JuliaLean.base.set.setCopyMutable ops s))
    | .inr xs => .ok (.inr xs)
  sizehint := fun c n shrink => match c with
    | .inl s => (fun s => .inl s) <$> JuliaLean.base.set.setSizehint ops n shrink s
    | .inr xs => .ok (.inr xs)
  push := fun c x => match c with
    | .inl s => (fun s => .inl s) <$> JuliaLean.base.set.setPush ops key x s
    | .inr _ => .error (.assertion "push! is not called on a plain iterable here")
  delete := fun c x => match c with
    | .inl s => (fun s => .inl s) <$> JuliaLean.base.set.setDelete ops x s
    | .inr _ => .error (.assertion "delete! is not called on a plain iterable here")
  filterBang := fun pred c => match c with
    | .inl s => do
        let s ← (setMembers s).foldlM (fun s k => do
          if ← pred k then pure s else JuliaLean.base.set.setDelete ops k s) s
        pure (.inl s)
    | .inr _ => .error (.assertion "filter! is not called on a plain iterable here")
  promoteEltype := fun _ _ => .ok .other
  elementType := fun _ => .other
  subtype := fun _ _ => false
  sameType := fun _ _ => false
  intLength := fun n => .ok n
  findminLength := fun _ => .error (.assertion "unused")
  setindex := fun _ _ _ => .error (.assertion "unused")
  getindex := fun _ _ => .error (.assertion "unused")
  extrema := fun _ => .error (.assertion "unused")
  step := fun _ => .error (.assertion "unused")
  minimum := fun _ => .error (.assertion "unused")
  abs := fun _ => .error (.assertion "unused")
  lessThan := fun _ _ => .error (.assertion "unused")
  mod := fun _ _ => .error (.assertion "unused")
  addWithOverflow := fun a b => (JInt.wrap .i64 (a.val + b.val),
    !(IntTy.i64.min ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.i64.max))

/-- Iterating a store vector inside `SetVecM`, as Julia's `iterate(a, i)` reads `a[i]`. -/
instance {K : Type} : ForIn (SetVecM K) VectorRef K where
  forIn a init f := do
    let n ← StateT.lift (mutableLength (α := K) a.handle)
    forIn (intRange one n) init fun i b => do f (← StateT.lift (mutableGet a.handle i)) b

/-- The values of `xs` at their first appearance, under the equality `equal`. -/
def firstOccurrences {K : Type} (equal : K → K → Bool) (xs : List K) : List K :=
  xs.foldl (fun out x => if out.any (equal x) then out else out ++ [x]) []

/-- Running a `SetVecM` method from an empty `Set` on the store `s`: the returned vector and the
store afterwards. -/
def setVecRun {K β : Type} (action : SetVecM K β) (s : MutableMemory K) :
    Except Error β × MutableMemory K :=
  let r := (action.run (JuliaLean.base.set.setConstructorEmpty (K := K) 0)).run s
  (r.1.map Prod.fst, r.2)


/-! ### Set operations on every `AbstractVector`, and on values of every type

`union!`, `symdiff!`, `intersect!` and `setdiff!` (array.jl:3180-3194) are defined for every
`AbstractVector`. The statements below hold for a `Vector` of the store (array.jl's own indexing,
`push!`, and the `Vector` branch of `filter!`: `resize!` and `sizehint!`) and for any mutable
vector type with no Lean model, given by its state and its documented operations (`UserVector`;
its `firstindex` may differ from 1, and `filter!` reaches its `deleteat!(a, j:lastindex(a))`
branch). Slots may be unassigned: reading one raises `UndefRefError`. Values of every Julia type
live in one type `K` (the universe of the values involved); `isT x` says that `x isa T` for the
element type `T` of the `Set{T}` or array being built, and `convert(T, x)` is user-extensible, a
parameter whose only law is its documented result type ("Convert `x` to a value of type `T`"). -/

/-- The monad of a vector held in a state `σ`: a failing step keeps the state it reached. -/
abbrev BaseM (σ : Type) := ExceptT Error (StateM σ)

/-- A typed parameter's result, raised as a Julia error. -/
def baseLift {σ β : Type} (value : Except Error β) : BaseM σ β :=
  match value with
  | .ok b => pure b
  | .error e => throw e

/-- The operations of an `AbstractVector` that array.jl's set-like operators call: `firstindex`,
`lastindex`, `length`, reading `a[i]`, `a[i] = x`, `push!`, whether `a isa Vector`, and the
shrinking steps of `filter!` (`resize!`/`sizehint!` for a `Vector`, `deleteat!(a, j:k)`
otherwise). -/
structure VectorOps (σ K : Type) where
  firstindex : BaseM σ I
  lastindex : BaseM σ I
  length : BaseM σ I
  getAt : I → BaseM σ K
  setAt : K → I → BaseM σ Unit
  pushBack : K → BaseM σ Unit
  isVector : Bool
  resizeTo : I → BaseM σ Unit
  sizehintTo : I → BaseM σ Unit
  deleteRange : I → I → BaseM σ Unit

/-- The vector a set-like operator receives and returns. -/
structure VectorOf (σ K : Type) where
  ops : VectorOps σ K

/-- The vector's state and the one `Set` the operator allocates. -/
abbrev SetVecG (σ K : Type) := StateT (JuliaLean.base.set.SetModel K) (BaseM σ)

def liftV {σ K β : Type} (action : BaseM σ β) : SetVecG σ K β := StateT.lift action

def setLiftRG {σ K β : Type} (r : JuliaLean.base.set.Result β) : SetVecG σ K β :=
  match r with
  | .ok b => pure b
  | .error _ => throw (Error.assertion "Set operation failed")

/-- `Set{T}()` (set.jl). -/
def setNewG {σ K : Type} : SetVecG σ K Unit :=
  modify (fun _ => JuliaLean.base.set.setConstructorEmpty (K := K) 0)

/-- `x ∈ s` (set.jl `in(x, s::Set) = haskey(s.dict, x)`, no key conversion). -/
def setHasG {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K) (x : K) (_ : Unit) :
    SetVecG σ K Bool := do
  setLiftRG (JuliaLean.base.set.setIn ops x (← get))

/-- `pop!(s::Set, x)` (set.jl). -/
def setRemoveG {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K) (_ : Unit) (x : K) :
    SetVecG σ K Unit := do
  let (_, s) ← setLiftRG (JuliaLean.base.set.setPopKeyModel ops x (← get))
  modify (fun _ => s)

/-- Runs an abstractset.jl operation (with `setCallsKey`) on the `Set` of the state with plain
iterables `itrs`, and stores the resulting `Set`. -/
def setRunG {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K)
    (key : JuliaLean.base.dict.KeyConv K K)
    (operation : (setCallsKey K ops key).C → List (setCallsKey K ops key).C →
      Except (setCallsKey K ops key).Error (setCallsKey K ops key).C)
    (itrs : List (List K)) : SetVecG σ K Unit := do
  let start : Sum (JuliaLean.base.set.SetModel K) (List K) := .inl (← get)
  let r : Except JuliaLean.base.set.Error (Sum (JuliaLean.base.set.SetModel K) (List K)) :=
    operation start (itrs.map (fun xs => (Sum.inr xs : Sum (JuliaLean.base.set.SetModel K) (List K))))
  match ← setLiftRG r with
  | .inl s => modify (fun _ => s)
  | .inr _ => throw (Error.assertion "set operation returned a non-Set")

/-- `Set{T}(itr)` (set.jl `Set{T}(itr) = union!(Set{T}(), itr)`, abstractset.jl's `union!`) as
the `Set` of the state, its keys converted with `key`. -/
def setFromValuesKey {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K)
    (key : JuliaLean.base.dict.KeyConv K K) (_ : Unit) (itr : List K) : SetVecG σ K Unit := do
  setNewG
  setRunG ops key (JuliaLean.base.abstractset.unionBangAbstractSetMany (setCallsKey K ops key)) [itr]

/-- dict.jl's key conversion for a `Set{T}`: a value with `isT x` is kept, any other is
`convert(T, x)` (which dict.jl then requires to be `isequal` to `x`). -/
def convertingKey {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (isT : K → Bool)
    (convert : K → Except Error K) : JuliaLean.base.dict.KeyConv K K :=
  ⟨fun x => if isT x then some x else none,
   fun x => match convert x with
     | .ok y => .ok y
     | .error _ => .error .thrownDict,
   ops.equal⟩

/-- `convert(T, x)` returns a value of type `T` (its documented result type; Julia's
`convert(T, x)::T` assertion). -/
def ConvertsTo {K : Type} (isT : K → Bool) (convert : K → Except Error K) : Prop :=
  ∀ x y, convert x = .ok y → isT y = true

/-- Iterating an `AbstractArray` (abstractarray.jl `iterate(A::AbstractArray)`: `A[i]` for `i` in
`eachindex(A) = firstindex(A):lastindex(A)`). -/
instance {σ K : Type} : ForIn (SetVecG σ K) (VectorOf σ K) K where
  forIn v init f := do
    let first ← liftV v.ops.firstindex
    let last ← liftV v.ops.lastindex
    forIn (intRange first last) init fun i b => do f (← liftV (v.ops.getAt i)) b

/-- `filter!(f, a::AbstractVector)` (array.jl:3061) with `nextind(a, j) = j + 1`
(abstractarray.jl). -/
def vecFilterBangG {σ K : Type} (pred : K → SetVecG σ K Bool) (v : VectorOf σ K) :
    SetVecG σ K (VectorOf σ K) :=
  filterBang (fun v => liftV v.ops.firstindex) (fun v => liftV v.ops.lastindex)
    (fun v x i => liftV (v.ops.setAt x i)) pred (fun _ j => pure (j + one))
    (fun v => v.ops.isVector) (fun v n => liftV (v.ops.resizeTo n))
    (fun v n => liftV (v.ops.sizehintTo n)) (fun v j k => liftV (v.ops.deleteRange j k)) v

/-- Running a `SetVecG` method from an empty `Set` on the vector state `s`. -/
def setVecRunG {σ K β : Type} (action : SetVecG σ K β) (s : σ) : Except Error β × σ :=
  let r := (action.run (JuliaLean.base.set.setConstructorEmpty (K := K) 0)).run s
  (r.1.map Prod.fst, r.2)

/-- A `Vector` of the store (handle `h`): array.jl's indexing (`getindex`/`setindex!` of
essentials.jl and array.jl), `push!` (array.jl:1361), `resize!` (array.jl:1559) and `sizehint!`
(array.jl:1612); `firstindex` is 1 and `lastindex` the length. -/
def storeVectorOps {K : Type} (layout : MemoryLayoutMetadata) (h : Nat) : VectorOps (MutableMemory K) K where
  firstindex := pure one
  lastindex := mutableLength (α := K) h
  length := mutableLength (α := K) h
  getAt i := mutableGet (α := K) h i
  setAt x i := mutableSet h x i
  pushBack x := vectorPushTyped (layout := layout) h x
  isVector := true
  resizeTo n := do
    let _ ← JuliaLean.base.array.resize (m := MutationM K) lengthToInt mutableLength
      JuliaLean.base.int.band
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
      (deletebeg (mutableStorage layout) pure) (deleteend (mutableStorage layout) pure) h n false
    pure ()
  sizehintTo n := vectorSizehint (layout := layout) h n false true
  deleteRange _ _ := throw (.assertion "deleteat! is not reached for a Vector")

/-- A mutable `AbstractVector` of a type with no Lean model (any user-defined vector type): its
state `σ`, its `firstindex`, its slots in index order (`none` for an unassigned one), and
`setindex!`, `push!` and `deleteat!(a, j:k)` as typed parameters. -/
structure UserVector (σ K : Type) where
  first : σ → I
  slots : σ → List (Option K)
  setAt : σ → K → I → Except Error σ
  pushBack : σ → K → Except Error σ
  deleteRange : σ → I → I → Except Error σ

/-- The position in `slots` of the index `i`. -/
def UserVector.offset {σ K : Type} (U : UserVector σ K) (s : σ) (i : I) : Int :=
  i.val - (U.first s).val

/-- The documented interface laws (manual, "Interfaces: Abstract Arrays"; docstrings of
`setindex!`: "Store values from array `X` within some subset of `A`", `push!`: "Insert one or more
`items` in `collection`... at the end", `deleteat!`: "Remove the items at the indices given by
`inds`"): each operation keeps `firstindex` and changes the slots exactly as documented. -/
def UserVector.Lawful {σ K : Type} (U : UserVector σ K) : Prop :=
  (∀ s x i, 0 ≤ U.offset s i → U.offset s i < (U.slots s).length →
    ∃ s', U.setAt s x i = .ok s' ∧ U.first s' = U.first s ∧
      U.slots s' = (U.slots s).set (U.offset s i).toNat (some x)) ∧
  (∀ s x, ∃ s', U.pushBack s x = .ok s' ∧ U.first s' = U.first s ∧
    U.slots s' = U.slots s ++ [some x]) ∧
  (∀ s j k, 0 ≤ U.offset s j → U.offset s j ≤ (U.slots s).length →
    U.offset s k = (U.slots s).length - 1 →
    ∃ s', U.deleteRange s j k = .ok s' ∧ U.first s' = U.first s ∧
      U.slots s' = (U.slots s).take (U.offset s j).toNat)

/-- The operations of a `UserVector`: `lastindex = firstindex + length - 1`; reading an index
outside the axes raises `BoundsError` and an unassigned slot `UndefRefError`. -/
def userVectorOps {σ K : Type} (U : UserVector σ K) : VectorOps σ K where
  firstindex := do return U.first (← get)
  lastindex := do
    let s ← get
    return JInt.wrap .i64 ((U.first s).val + (U.slots s).length - 1)
  length := do return JInt.wrap .i64 (U.slots (← get)).length
  getAt i := do
    let s ← get
    if U.offset s i < 0 then throw .bounds
    match (U.slots s)[(U.offset s i).toNat]? with
    | some (some x) => pure x
    | some none => throw .undefinedReference
    | none => throw .bounds
  setAt x i := do set (← baseLift (U.setAt (← get) x i))
  pushBack x := do set (← baseLift (U.pushBack (← get) x))
  isVector := false
  resizeTo _ := throw (.assertion "resize! is not reached for a non-Vector")
  sizehintTo _ := throw (.assertion "sizehint! is not reached for a non-Vector")
  deleteRange j k := do set (← baseLift (U.deleteRange (← get) j k))

/-- `P` holds for every `AbstractVector`: every valid `Vector` of the store with room for `extra`
more elements, and every lawful `UserVector` whose indices stay inside `Int`. `P` receives the
vector's state type, operations, slots and validity. -/
def EveryAbstractVector {K : Type} (layout : MemoryLayoutMetadata) (extra : Nat)
    (P : (σ : Type) → VectorOps σ K → (σ → List (Option K)) → (σ → Prop) → σ → Prop) : Prop :=
  (∀ (s : MutableMemory K) (h : Nat), s.validVector h →
    (∀ w slots, s.arrays[h]? = some w → s.memories[w.reference.1]? = some slots →
      slots.length + (s.contents h).length + extra + 3 < 2 ^ 62) →
    P (MutableMemory K) (storeVectorOps layout h) (fun s => s.contents h) (fun s => s.validVector h) s) ∧
  (∀ (σ : Type) (U : UserVector σ K), U.Lawful → ∀ s : σ,
    -2 ^ 62 ≤ (U.first s).val → (U.first s).val + (U.slots s).length + extra < 2 ^ 62 →
    P σ (userVectorOps U) U.slots (fun _ => True) s)

def setVecLiteralConv {K : Type} (layout : Option MemoryLayout) (isT : K → Bool) (convert : K → Except Error K) (_ : Unit)
    (test : K → SetVecM K Bool) (itr : List K) : SetVecM K Nat :=
  vectorfilter (literalFilterCollectOps (pure 0)
    (typedLiteral (fun n => StateT.lift (mutableAllocate (α := K) layout 0 n))
      (fun a x i => setindexScalar isT id (fun x => liftV (baseLift (convert x)))
        (fun a y i => StateT.lift (mutableTypedSet (α := K) a y i)) a x i) true)) () test itr

/-- The axes of a heap array, `OneTo(size(a, d))` for each dimension, given by their lengths. -/
def heapAxes {Tag : Type} (a : HeapArray Tag) : List I :=
  a.dimensions.map (fun (n : Nat) => JInt.wrap .i64 (n : Int))

abbrev AHM (α : Type) := ExceptT JuliaLean.base.abstractarray.ArrayError (VectorM α)

/-- An abstractarray.jl error as the corresponding Julia exception of this file. -/
def arrayError : JuliaLean.base.abstractarray.ArrayError → Error
  | .julia (.argumentError msg) => .argument msg
  | .julia .boundsError => .bounds
  | .dimensionMismatch msg => .dimensionMismatch msg
  | .showError error => .showError error
  | _ => .assertion "AbstractArray error"

def runAHM {α β : Type} (x : AHM α β) : VectorM α β := do
  match ← x.run with
  | .ok b => pure b
  | .error e => throw (arrayError e)

/-- `similar(A, T)` for a heap array: array.jl's vector and matrix methods (array.jl:416, 417) and,
for other dimensions, abstractarray.jl's `similar(a, T, to_shape(axes(a)))` to array.jl:419. -/
def heapSimilarType {Tag α : Type} (layout : Tag → Option MemoryLayout) (target : Tag) (a : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  match a.dimensions.length with
  | 1 => similar416 heapSize (heapVectorAllocate layout target) a
  | 2 => similar417 heapSize (fun n m => heapAllocateIntDims layout target [n, m]) a
  | _ => similar419 (heapAllocateIntDims layout target) a (heapAxes a)

/-- A fresh heap array of element type `target` and dimensions `shape` holding `values`, appended to
`heap`. -/
def freshHeapArray {Tag α : Type} (target : Tag) (shape : List Nat) (values : List (Option α))
    (heap : VectorHeap α) : HeapArray Tag × VectorHeap α :=
  (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩, heap ++ [values])

def heapIterCopy {Tag α β : Type} (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (dest : HeapArray Tag) (xs : List β) :
    VectorM α (HeapArray Tag) :=
  runAHM (JuliaLean.base.abstractarray.copytoIterable (m := AHM α)
    (fun d : HeapArray Tag => pure (intRange one (JInt.wrap .i64 (d.dimensions.prod : Int))))
    (fun inds : List I => pure (match inds with
      | [] => none
      | i :: rest => some (i, rest)))
    (fun _ st => pure (match st with
      | [] => none
      | i :: rest => some (i, rest)))
    (fun d i x => liftM (do
      let _ ← setindexScalar already asTyped (fun x => liftM (convert x))
        (fun (a : HeapArray Tag) x i => do heapSet a.handle x i; pure a) d x i
      pure ()))
    dest xs)

instance {Tag α : Type} : ForIn (AHM α) (HeapArray Tag) α where
  forIn a init f := do
    forIn (intRange one (JInt.wrap .i64 (a.dimensions.prod : Int))) init fun i b => do
      f (← liftM (heapGet (α := α) a.handle i)) b

/-- Exact `BigInt`-style operations satisfying `BigIntegerOps.Lawful`. -/
def exactIntegerOps : BigIntegerOps where
  convert t v := if t.min ≤ v ∧ v ≤ t.max then .ok (JInt.wrap t v) else .error .inexact
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  le a b := decide (a ≤ b)

theorem exactIntegerOps_lawful : exactIntegerOps.Lawful :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
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

abbrev ArrayError := JuliaLean.base.abstractarray.ArrayError

/-- A Julia exception: thrown by user code, or a Base error of array.jl, abstractarray.jl or
range.jl. -/
inductive Fault (E : Type) where
  | user (e : E)
  | base (e : Error)
  | array (e : ArrayError)
  | range (e : JuliaLean.base.range.Exc)

structure World (U α : Type) where
  heap : VectorHeap α
  memory : MutableMemory α
  user : U

abbrev UM (E U : Type) := ExceptT E (StateM U)
abbrev M (E U α : Type) := ExceptT (Fault E) (StateM (World U α))
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
section lifts
variable {E U α β : Type}

def fail (f : Fault E) : M E U α β := throwThe (Fault E) f

/-- A call into user code. -/
def liftUser (x : UM E U β) : M E U α β := do
  let w ← get
  let (r, u) := Id.run (x.run.run w.user)
  set { w with user := u }
  match r with
  | .ok b => pure b
  | .error e => fail (.user e)

instance : MonadExceptOf ArrayError (M E U α) where
  throw e := fail (.array e)
  tryCatch x h := tryCatchThe (Fault E) x fun
    | .array e => h e
    | f => fail f

instance : MonadExceptOf Error (M E U α) where
  throw e := fail (.base e)
  tryCatch x h := tryCatchThe (Fault E) x fun
    | .base e => h e
    | f => fail f
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
section iteration
variable {E U α β St : Type}

/-- Julia's `for x in itr` over a user iterator (array.lean `FiniteIterator`): the body runs on
`x`, then `iterate(itr, st)` gives the next element. -/
def iterFrom (it : FiniteIterator (UM E U) β St) {σ : Type}
    (f : β → σ → M E U α (ForInStep σ)) : β → (st : St) → σ → M E U α σ
  | x, st, b => do
    match ← f x b with
    | .done b => pure b
    | .yield b =>
      match ← liftUser (it.next st) with
      | none => pure b
      | some (x', ⟨st', _⟩) => iterFrom it f x' st' b
termination_by _ st _ => it.rank st
decreasing_by
  all_goals
    try simp_wf
    assumption

instance : ForIn (M E U α) (FiniteIterator (UM E U) β St) β where
  forIn it init f := do
    match ← liftUser it.first with
    | none => pure init
    | some (x, st) => iterFrom it f x st init
end iteration
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

/-- The field reads and `convert(T, x::T) = x` (essentials.jl) that range.jl's
`last(r::OrdinalRange{T}) = convert(T, r.stop)` uses for a `OneTo` of any Integer type. -/
instance : JuliaLean.base.range.JEltype (OneTo IntegerValue) IntegerValue := ⟨⟩
instance : JuliaLean.base.range.JFieldStop (OneTo IntegerValue) IntegerValue := ⟨OneTo.stop⟩
instance : JuliaLean.base.range.JConvert IntegerValue IntegerValue :=
  ⟨fun x => .ok (JuliaLean.base.essentials.convertTypeIdentity x)⟩
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
/-- Only Integer types without an installed model use the supplied conversion. -/
def convertInteger (ops : BigIntegerOps) (t : IntTy) : IntegerValue → Except Error (JInt t)
  | .bit _ x => (JuliaLean.base.int.convert t x).mapError (fun _ => .inexact)
  | .bool b => .ok (JuliaLean.base.int.ofBool t b)
  | .big v => ops.convert t v
end JuliaLean.Proofs.base.array.round8
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

/-- Only Integer types without an installed model use the supplied conversion. -/
def convertInteger (ops : BigIntegerOps) (t : IntTy) : IntegerValue → Except Error (JInt t)
  | .bit _ x => (JuliaLean.base.int.convert t x).mapError (fun _ => .inexact)
  | .bool b => .ok (JuliaLean.base.int.ofBool t b)
  | .big v => ops.convert t v

def integerToInt (ops : BigIntegerOps) (x : IntegerValue) : MutationM α I :=
  StateT.lift (convertInteger ops .i64 x)
end JuliaLean.Proofs.base.array.round9
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

abbrev ArrayError := JuliaLean.base.abstractarray.ArrayError

/-- A Julia exception: thrown by user code, or a Base error of array.jl, abstractarray.jl or
range.jl. -/
inductive Fault (E : Type) where
  | user (e : E)
  | base (e : Error)
  | array (e : ArrayError)
  | range (e : JuliaLean.base.range.Exc)

structure World (U α : Type) where
  heap : VectorHeap α
  memory : MutableMemory α
  user : U

abbrev UM (E U : Type) := ExceptT E (StateM U)
abbrev M (E U α : Type) := ExceptT (Fault E) (StateM (World U α))
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
section lifts
variable {E U α β : Type}

def fail (f : Fault E) : M E U α β := throwThe (Fault E) f

/-- A call into user code. -/
def liftUser (x : UM E U β) : M E U α β := do
  let w ← get
  let (r, u) := Id.run (x.run.run w.user)
  set { w with user := u }
  match r with
  | .ok b => pure b
  | .error e => fail (.user e)

def liftRange (x : JuliaLean.base.range.JlX β) : M E U α β :=
  match x with
  | .ok b => pure b
  | .error e => fail (.range e)

instance : MonadExceptOf ArrayError (M E U α) where
  throw e := fail (.array e)
  tryCatch x h := tryCatchThe (Fault E) x fun
    | .array e => h e
    | f => fail f

instance : MonadExceptOf Error (M E U α) where
  throw e := fail (.base e)
  tryCatch x h := tryCatchThe (Fault E) x fun
    | .base e => h e
    | f => fail f
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
section iteration
variable {E U α β St : Type}

/-- Julia's `for x in itr` over a user iterator (array.lean `FiniteIterator`): the body runs on
`x`, then `iterate(itr, st)` gives the next element. -/
def iterFrom (it : FiniteIterator (UM E U) β St) {σ : Type}
    (f : β → σ → M E U α (ForInStep σ)) : β → (st : St) → σ → M E U α σ
  | x, st, b => do
    match ← f x b with
    | .done b => pure b
    | .yield b =>
      match ← liftUser (it.next st) with
      | none => pure b
      | some (x', ⟨st', _⟩) => iterFrom it f x' st' b
termination_by _ st _ => it.rank st
decreasing_by
  all_goals
    try simp_wf
    assumption

instance : ForIn (M E U α) (FiniteIterator (UM E U) β St) β where
  forIn it init f := do
    match ← liftUser it.first with
    | none => pure init
    | some (x, st) => iterFrom it f x st init
end iteration
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

/-- The field reads and `convert(T, x::T) = x` (essentials.jl) that range.jl's
`last(r::OrdinalRange{T}) = convert(T, r.stop)` uses for a `OneTo` of any Integer type. -/
instance : JuliaLean.base.range.JEltype (OneTo IntegerValue) IntegerValue := ⟨⟩
instance : JuliaLean.base.range.JFieldStop (OneTo IntegerValue) IntegerValue := ⟨OneTo.stop⟩
instance : JuliaLean.base.range.JConvert IntegerValue IntegerValue :=
  ⟨fun x => .ok (JuliaLean.base.essentials.convertTypeIdentity x)⟩
end JuliaLean.Proofs.base.array.round6dcollect3
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round6b
open JuliaLean JuliaLean.base.array

inductive IntegerArgument where
  | bit (t : IntTy) (x : JInt t)
  | boolean (b : Bool)
  | opaque (value : Int)

def IntegerArgument.value : IntegerArgument → Int
  | .bit _ x => x.val
  | .boolean b => if b then 1 else 0
  | .opaque v => v

/-- Operations of an Integer type without an installed model. -/
structure OpaqueIntegerOps where
  convert : (t : IntTy) → Int → Except Error (JInt t)
  multiply : Int → Int → Int
  less : Int → Int → Bool

def OpaqueIntegerOps.ConversionLaw (ops : OpaqueIntegerOps) : Prop :=
  ∀ t v, ops.convert t v =
    if t.min ≤ v ∧ v ≤ t.max then .ok (JInt.wrap t v) else .error .inexact

def convertInteger (ops : OpaqueIntegerOps) (t : IntTy) :
    IntegerArgument → Except Error (JInt t)
  | .bit _ x => (JuliaLean.base.int.convert t x).mapError (fun _ => .inexact)
  | .boolean b => .ok (JuliaLean.base.int.ofBool t b)
  | .opaque v => ops.convert t v

abbrev ByteM := StateT JuliaLean.base.pointer.ByteHeap (Except Error)

def bytePointer (address : Nat) : JuliaLean.base.pointer.Ptr Unit :=
  ⟨JInt.wrap .u64 address⟩

def byteCall (call : JuliaLean.base.pointer.ByteHeap →
    Jl (JuliaLean.base.pointer.ByteHeap × α)) : ByteM α := do
  match call (← get) with
  | .ok (heap, x) => set heap; pure x
  | .error _ => throw .inexact
end round6b
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section IndexGets


theorem promote_i64_range (t : IntTy) :
    (IntTy.i64.promote t).min ≤ 0 ∧ 9223372036854775807 ≤ (IntTy.i64.promote t).max := by
  cases t <;> decide

/-- `getindex(A, i)` on the shared heap for one `Int` index: outside `1:length(A)` it raises
`BoundsError`, on an unassigned slot `UndefRefError`, and otherwise returns the element; the heap
is unchanged. -/
theorem heapGet_run {α : Type} (heap : VectorHeap α) (handle : Nat) (slots : List (Option α))
    (hs : heap[handle]? = some slots) (i : I) :
    (heapGet handle i).run heap =
      if 1 ≤ i.val ∧ i.val ≤ (slots.length : Int) then
        match slots[(i.val - 1).toNat]? with
        | some (some x) => .ok (x, heap)
        | _ => .error .undefinedReference
      else .error .bounds := by
  simp only [heapGet, vector_bind_run, heapSlots_run, hs, vector_lift_run, vectorGet]
  by_cases h : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int)
  · have hlt : (i.val - 1).toNat < slots.length := by omega
    rw [if_pos h, if_pos h, List.getElem?_eq_getElem hlt]
    cases slots[(i.val - 1).toNat] <;> rfl
  · rw [if_neg h, if_neg h]
    rfl
end IndexGets
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

/-- Base nextind on an Int index, through its installed constructor and addition model. -/
def nextIntIndex (i : I) : Except Error I :=
  (JuliaLean.base.abstractarray.nextind
    (fun i : I => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 i))
    () i).mapError arrayError
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
variable {α : Type}

theorem extra_val (P N : Nat) (hP : P ≤ 2 ^ 55) (hN : N < 2 ^ 63) (q : I)
    (hq : q.val = ((N / 8 : Nat) : Int)) :
    (JInt.wrap .i64 (P : Int) * JInt.wrap .i64 3 + q).val = (P : Int) * 3 + ((N / 8 : Nat) : Int) := by
  have hsh : (JInt.wrap .i64 (P : Int)).val = P := ival_wrap _ (by omega)
  have h3 : (JInt.wrap .i64 3).val = 3 := ival_wrap 3 (by decide)
  have hx3 : (JInt.wrap .i64 (P : Int) * JInt.wrap .i64 3).val = (P : Int) * 3 := by
    rw [show JInt.wrap .i64 (P : Int) * JInt.wrap .i64 3 =
      JInt.wrap .i64 ((JInt.wrap .i64 (P : Int)).val * (JInt.wrap .i64 3).val) from rfl, hsh, h3]
    exact ival_wrap _ (by omega)
  rw [ival_add _ _ (by rw [hx3, hq]; omega), hx3, hq]

theorem ovl_final (x : I) (N P : Nat) (hxv : x.val = (N : Int)) (hN : N < 2 ^ 63)
    (hP : P ≤ 2 ^ 55) (E : I) (hE : E.val = (P : Int) * 3 + ((N / 8 : Nat) : Int)) :
    (if x > JInt.typemax .i64 - E then JInt.typemax .i64 else x + E).val =
      ((if typemaxNat - (P * 3 + N / 8) < N then typemaxNat else N + (P * 3 + N / 8) : Nat) : Int) := by
  have hmax : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
  have hsub : (JInt.typemax .i64 - E).val = 9223372036854775807 - ((P : Int) * 3 + ((N / 8 : Nat) : Int)) := by
    rw [ival_sub _ _ (by rw [hmax, hE]; omega), hmax, hE]
  by_cases hgt : typemaxNat - (P * 3 + N / 8) < N
  · have hlt : JInt.typemax .i64 - E < x := by
      rw [jlt_iff, hsub, hxv]; unfold typemaxNat at hgt; omega
    rw [if_pos hlt, hmax, if_pos hgt]
    rfl
  · have hlt : ¬ JInt.typemax .i64 - E < x := by
      rw [jlt_iff, hsub, hxv]; unfold typemaxNat at hgt; omega
    rw [if_neg hlt, if_neg hgt, ival_add _ _ (by rw [hxv, hE]; unfold typemaxNat at hgt; omega),
      hxv, hE]
    push_cast
    omega

theorem ms_overallocation_val {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x : I)
    (hx : 0 ≤ x.val) :
    ∃ c : I, ((mutableStorage layout).overallocation x).run s = (.ok c, s) ∧
      c.val = (overallocationNat x.val.toNat : Int) := by
  simp only [mutableStorage, overallocation, stateExcept_bind, stateExcept_pure]
  refine ⟨_, rfl, ?_⟩
  have hb := ival_bounds x
  have hn : x.val.toNat < 2 ^ 63 := by omega
  have hxv : x.val = (x.val.toNat : Int) := by omega
  generalize hN : x.val.toNat = N at hn hxv
  have h64 : (JInt.wrap .i64 64).val = 64 := ival_wrap 64 (by decide)
  have h7 : (JInt.wrap .i64 7).val = 7 := ival_wrap 7 (by decide)
  have h8 : (JInt.wrap .i64 8).val = 8 := ival_wrap 8 (by decide)
  have h3 : (JInt.wrap .i64 3).val = 3 := ival_wrap 3 (by decide)
  have hmax : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
  -- the bit length `exp2`
  have hE : ∃ E : Nat, E ≤ 63 ∧ (if N = 0 then 0 else N.log2 + 1) = E ∧
      (JInt.wrap .i64 64 - JInt.wrap .i64 (if x.val = 0 then 64 else 63 - (N.log2 : Int))).val =
        (E : Int) := by
    by_cases h0 : N = 0
    · refine ⟨0, by omega, by simp [h0], ?_⟩
      have hx0 : x.val = 0 := by omega
      rw [if_pos hx0, ival_sub _ _ (by rw [h64]; decide), h64]; rfl
    · have hlg : N.log2 < 63 := (Nat.log2_lt h0).mpr hn
      refine ⟨N.log2 + 1, by omega, by simp [h0], ?_⟩
      have hx0 : ¬ x.val = 0 := by omega
      have hc : (JInt.wrap .i64 (63 - (N.log2 : Int))).val = 63 - (N.log2 : Int) :=
        ival_wrap _ (by omega)
      rw [if_neg hx0, ival_sub _ _ (by rw [h64, hc]; omega), h64, hc]
      push_cast
      omega
  obtain ⟨E, hE63, hEdef, hEv⟩ := hE
  have hm : ((JInt.wrap .i64 64 - JInt.wrap .i64 (if x.val = 0 then 64 else 63 - (N.log2 : Int))) *
      JInt.wrap .i64 7).val = (E : Int) * 7 := by
    change wrapInt .i64 ((JInt.wrap .i64 64 -
      JInt.wrap .i64 (if x.val = 0 then 64 else 63 - (N.log2 : Int))).val *
        (JInt.wrap .i64 7).val) = _
    rw [hEv, h7]
    exact wrapInt_of_inRange .i64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  have hq : (JInt.wrap .i64 (((JInt.wrap .i64 64 -
      JInt.wrap .i64 (if x.val = 0 then 64 else 63 - (N.log2 : Int))) *
        JInt.wrap .i64 7).val.tdiv (JInt.wrap .i64 8).val)).val.toNat = E * 7 / 8 := by
    rw [hm, h8, Int.tdiv_eq_ediv_of_nonneg (by omega), ival_wrap _ (by omega)]
    omega
  have hp1 : 1 ≤ 2 ^ (E * 7 / 8) := Nat.one_le_two_pow
  have hp2 : 2 ^ (E * 7 / 8) ≤ 2 ^ 55 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : (one.val * 2 ^ (E * 7 / 8) : Int) = ((2 ^ (E * 7 / 8) : Nat) : Int) := by
    rw [ival_one, Int.one_mul]; push_cast; rfl
  have hd8 : (JInt.wrap .i64 (x.val.tdiv (JInt.wrap .i64 8).val)).val = (N / 8 : Nat) := by
    rw [h8, Int.tdiv_eq_ediv_of_nonneg hx, ival_wrap _ (by omega)]
    omega
  rw [hq, hpow]
  simp only [overallocationNat, hEdef]
  generalize hP : 2 ^ (E * 7 / 8) = P at hp1 hp2 ⊢
  clear hP hpow hq hm hEv hEdef
  rw [ovl_final x N P hxv hn hp2 _ (extra_val P N hp2 hn _ hd8)]
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

theorem VecAt.geometry {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) :
    geometryOf s handle = ⟨slots.length, off.val.toNat, n.val.toNat⟩ := by
  simp only [geometryOf, h.1, h.2.1, Option.getD_some]

/-- `_growend!(a, delta)` with room after the last element: only the length changes. -/
theorem growend_fast {layout : MemoryLayoutMetadata} {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd : 0 ≤ delta.val) (hroom : delta.val ≤ (slots.length : Int) - (off.val - 1) - n.val) :
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) handle delta).run s =
      (.ok (), {s with arrays := s.arrays.set handle ⟨(mem, off), n + delta⟩}) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by omega)
  have hr1 : (JInt.wrap .i64 (slots.length : Int) - (off - one)).val =
      slots.length - (off.val - 1) := by
    rw [ival_sub _ _ (by rw [hL, hoff1]; omega), hL, hoff1]
  have hr2 : (JInt.wrap .i64 (slots.length : Int) - (off - one) - n).val =
      slots.length - (off.val - 1) - n.val := by
    rw [ival_sub _ _ (by rw [hr1]; omega), hr1]
  have hnlt : ¬ (JInt.wrap .i64 (slots.length : Int) - (off - one) - n < delta) := by
    rw [jlt_iff, hr2]; omega
  have hpos : delta ≥ zero := by rw [ge_iff_le, jle_iff, ival_zero]; exact hd
  have h' : VecAt s handle mem off n slots := ⟨ha, hm, ho, hn0, he, hc⟩
  simp only [growend, ms_ref, ms_length, ms_memory, ms_offset, stateExcept_bind, stateExcept_pure,
    hpos, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    mutableRef_run s handle _ ha, mutableLength_run s handle _ ha,
    mutableMemLength_run s mem slots hm, hnlt, vwSetSize_run s handle mem off n slots h']
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

theorem ms_checkedAdd_overflow {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x y : I)
    (h : ¬ (-9223372036854775808 ≤ x.val + y.val ∧ x.val + y.val ≤ 9223372036854775807)) :
    ((mutableStorage layout).checkedAdd x y).run s = (.error .overflow, s) := by
  have h' : ¬ (IntTy.i64.min ≤ x.val + y.val ∧ x.val + y.val ≤ IntTy.i64.max) := h
  change (if _ then (pure (x + y) : MutationM α I) else throw Error.overflow).run s = _
  simp only [h', ite_false, stateExcept_throw]

/-- The validity checks at the top of `_growend_internal!` pass on a valid vector. -/
theorem growendInternal_checks {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) :
    ¬ off < one ∧ ¬ JInt.wrap .i64 (slots.length : Int) < off - one ∧
      ¬ JInt.wrap .i64 (slots.length : Int) - (off - one) < n := by
  obtain ⟨_, _, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by omega)
  have hr1 : (JInt.wrap .i64 (slots.length : Int) - (off - one)).val =
      slots.length - (off.val - 1) := by
    rw [ival_sub _ _ (by rw [hL, hoff1]; omega), hL, hoff1]
  refine ⟨?_, ?_, ?_⟩
  · rw [jlt_iff, ival_one]; omega
  · rw [jlt_iff, hL, hoff1]; omega
  · rw [jlt_iff, hr1]; omega

theorem growendInternal_overflow1 {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hov : 9223372036854775807 < n.val + delta.val) :
    (growendInternal (mutableStorage layout) handle delta n).run s = (.error .overflow, s) := by
  have hadd := ms_checkedAdd_overflow (layout := layout) s n delta (by omega)
  simp only [growendInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ h.1, mutableMemLength_run s mem slots h.2.1, hadd]

theorem growendInternal_overflow2 {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val) (hov1 : n.val + delta.val ≤ 9223372036854775807)
    (hov : 9223372036854775807 < off.val - 1 + n.val + delta.val) :
    (growendInternal (mutableStorage layout) handle delta n).run s = (.error .overflow, s) := by
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hn0 := h.2.2.2.1
  have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by have := h.2.2.1; omega)
  have hadd1 := ms_checkedAdd_run (layout := layout) s n delta (by omega)
  have hadd2 := ms_checkedAdd_overflow (layout := layout) s (off - one) (n + delta)
    (by rw [hoff1, hnd]; omega)
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h
  simp only [growendInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ h.1, mutableMemLength_run s mem slots h.2.1, hadd1, hadd2,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
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

theorem imax_val (a b : I) : (max a b).val = max a.val b.val := rfl

/-- `_growend_internal!` sliding the data to the front of its own memory. -/
theorem growendInternal_slide {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val)
    (hov : off.val - 1 + n.val + delta.val ≤ 9223372036854775807)
    (hs1 : n.val + delta.val < off.val - 1)
    (hs2 : (n.val + delta.val) / 4 < off.val - 1 - (n.val + delta.val)) :
    ∃ (newoff : I) (slots' : List (Option α)),
      (growendInternal (mutableStorage layout) handle delta n).run s =
        (.ok (), { s with
          memories := s.memories.set mem slots'
          arrays := s.arrays.set handle ⟨(mem, newoff), n⟩ }) ∧
      newoff.val = (n.val + delta.val) / 8 + 1 ∧ slots'.length = slots.length ∧
      (slots'.drop (newoff.val - 1).toNat).take n.val.toNat = vwWindow slots off n := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by omega)
  have hsum1 : -9223372036854775808 ≤ n.val + delta.val ∧ n.val + delta.val ≤ 9223372036854775807 := by
    omega
  have hsum2 : -9223372036854775808 ≤ (off - one).val + (n + delta).val ∧
      (off - one).val + (n + delta).val ≤ 9223372036854775807 := by
    rw [hoff1, hnd]; omega
  have hadd1 := ms_checkedAdd_run (layout := layout) s n delta hsum1
  have hadd2 := ms_checkedAdd_run (layout := layout) s (off - one) (n + delta) hsum2
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  have hdiv4 := ms_divide_run (layout := layout) s (n + delta) (JInt.wrap .i64 4) (by rw [wval4]; decide)
  have hdiv8 := ms_divide_run (layout := layout) s (n + delta) (JInt.wrap .i64 8) (by rw [wval8]; decide)
  have hq4 : (JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 4).val)).val =
      (n.val + delta.val) / 4 := by
    rw [wval4, tdiv_nonneg_val (n + delta) 4 (by omega) (by decide) (by decide), hnd]
  have hq8 : (JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 8).val)).val =
      (n.val + delta.val) / 8 := by
    rw [wval8, tdiv_nonneg_val (n + delta) 8 (by omega) (by decide) (by decide), hnd]
  have hcond1 : n + delta < off - one := by rw [jlt_iff, hnd, hoff1]; exact hs1
  have hdiff : (off - one - (n + delta)).val = off.val - 1 - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hoff1, hnd]; omega), hoff1, hnd]
  have hcond2 : JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 4).val) < off - one - (n + delta) := by
    rw [jlt_iff, hq4, hdiff]; exact hs2
  simp only [growendInternal, ms_ref, ms_memory, ms_offset, ms_memoryref, ms_copyRef, ms_sameMem,
    ms_sameRef, ms_unsetMemory, stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1, hadd2,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    hdiv4, hcond1, hcond2, decide_true, Bool.and_self, ite_true, hdiv8, beq_self_eq_true]
  have hnewoff : (JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 8).val) + one).val =
      (n.val + delta.val) / 8 + 1 := by
    rw [ival_add_one _ (by rw [hq8]; omega), hq8]
  generalize JInt.wrap .i64 ((n + delta).val.tdiv (JInt.wrap .i64 8).val) + one = newoff at hnewoff ⊢
  have hmove := vwMemoryMove_run s mem mem newoff off n slots slots hm hm hn0
    (by rw [hnewoff]; omega) (by rw [hnewoff]; omega) ho he hc
  simp only [hmove]
  generalize hS1 : slots.take (newoff.val - 1).toNat ++ (slots.drop (off.val - 1).toNat).take n.val.toNat ++
      slots.drop (newoff.val - 1 + n.val).toNat = S1
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have hS1len : S1.length = slots.length := by
    simp only [← hS1, List.length_append, List.length_take, List.length_drop]
    rw [hnewoff]
    omega
  have hjs : ∀ j ∈ intRange (max off (newoff + n)) (off + n - one),
      1 ≤ j.val ∧ j.val ≤ (S1.length : Int) := by
    intro j hj
    have hr := intRange_mem _ _ j hj
    have hnn : (newoff + n).val = newoff.val + n.val := ival_add _ _ (by rw [hnewoff]; omega)
    have hhi : (off + n - one).val = off.val + n.val - 1 := ival_add_sub_one _ _ (by omega)
    rw [imax_val, hnn, hhi, hnewoff] at hr
    rw [hS1len]
    omega
  have hloop := vwClearLoop_run (unsetRuntime := layout.runtime) mem (intRange (max off (newoff + n)) (off + n - one))
    { s with memories := s.memories.set mem S1 } S1 (List.getElem?_set_self hlt) hjs
  simp only [hloop, List.set_set]
  generalize hS2 : vwClear (unsetRuntime := layout.runtime) S1 (intRange (max off (newoff + n)) (off + n - one)) = S2
  have href2 : (mutableRef handle).run { s with memories := s.memories.set mem S2 } =
      (.ok (mem, off), { s with memories := s.memories.set mem S2 }) :=
    mutableRef_run { s with memories := s.memories.set mem S2 } handle _ ha
  have hset := ms_setRef_run (layout := layout)
    { s with memories := s.memories.set mem S2 } handle ⟨(mem, off), n⟩ ha (mem, newoff)
  simp only [href2, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false, hset]
  refine ⟨newoff, S2, rfl, hnewoff, by rw [← hS2, vwClear_length, hS1len], ?_⟩
  have hk : ∀ j ∈ intRange (max off (newoff + n)) (off + n - one),
      (newoff.val - 1).toNat + n.val.toNat ≤ (j.val - 1).toNat := by
    intro j hj
    have hr := intRange_mem _ _ j hj
    have hnn : (newoff + n).val = newoff.val + n.val := ival_add _ _ (by rw [hnewoff]; omega)
    rw [imax_val, hnn] at hr
    omega
  have htake := vwClear_take (unsetRuntime := layout.runtime) S1 _ _ hk
  have hA : (slots.take (newoff.val - 1).toNat).length = (newoff.val - 1).toNat := by
    rw [List.length_take]; rw [hnewoff]; omega
  have hW : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  have key : ∀ l : List (Option α), (l.drop (newoff.val - 1).toNat).take n.val.toNat =
      (l.take ((newoff.val - 1).toNat + n.val.toNat)).drop (newoff.val - 1).toNat := by
    intro l; rw [List.drop_take]; congr 1; omega
  rw [key S2, ← hS2, htake, ← key S1, ← hS1, take_three hA hW]
  rfl
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

/-- `_growend_internal!` moving the data to a new memory of
`max(overallocation(memlen), offset - 1 + len + delta)` slots. -/
theorem growendInternal_alloc (l : DictLayout) {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val)
    (hov : off.val - 1 + n.val + delta.val ≤ 9223372036854775807)
    (hns : ¬ (n.val + delta.val < off.val - 1 ∧
      (n.val + delta.val) / 4 < off.val - 1 - (n.val + delta.val))) :
    let k : Nat := max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat
    (¬ memoryFits l k → (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
      (.error (.argument genericMemorySizeMessage), s)) ∧
    (memoryFits l k → ∃ D : List (Option α),
      (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
        (.ok (), { s with
          memories := (s.memories ++ [List.replicate k none]).set s.memories.length D
          arrays := s.arrays.set handle ⟨(s.memories.length, off), n⟩ }) ∧
      D.length = k ∧ (D.drop (off.val - 1).toNat).take n.val.toNat = vwWindow slots off n) := by
  intro k
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
  refine ⟨fun hnf => ?_, fun hfit => ?_⟩
  · have hE : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c (off - one + (n + delta)))).run s =
        (.error (.argument genericMemorySizeMessage), s) := hA.2.1 hK0 hnf
    simp only [hE]
  · have hOk : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c (off - one + (n + delta)))).run s =
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
    have hA' : ((List.replicate k (none : Option α)).take (off.val - 1).toNat).length = (off.val - 1).toNat := by
      rw [List.length_take, List.length_replicate]; omega
    have hW : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
      simp only [List.length_take, List.length_drop]; omega
    refine ⟨D, rfl, ?_, ?_⟩
    · rw [← hD]
      simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
      omega
    · rw [← hD, take_three hA' hW]
      rfl
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

/-- `_growend!` when the spare room is too small: `_growend_internal!`, then the new length. -/
theorem growend_slow_run {layout : MemoryLayoutMetadata} {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd : 0 ≤ delta.val) (hslow : (slots.length : Int) - (off.val - 1) - n.val < delta.val)
    (r : Except Error Unit) (st : MutableMemory α)
    (hint : (growendInternal (mutableStorage layout) handle delta n).run s = (r, st)) :
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) handle delta).run s =
      (match r with
        | .error e => (.error e, st)
        | .ok _ => ((mutableStorage layout).setSize handle (n + delta)).run st) := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by omega)
  have hr1 : (JInt.wrap .i64 (slots.length : Int) - (off - one)).val =
      slots.length - (off.val - 1) := by
    rw [ival_sub _ _ (by rw [hL, hoff1]; omega), hL, hoff1]
  have hr2 : (JInt.wrap .i64 (slots.length : Int) - (off - one) - n).val =
      slots.length - (off.val - 1) - n.val := by
    rw [ival_sub _ _ (by rw [hr1]; omega), hr1]
  have hlt : JInt.wrap .i64 (slots.length : Int) - (off - one) - n < delta := by
    rw [jlt_iff, hr2]; exact hslow
  have hpos : delta ≥ zero := by rw [ge_iff_le, jle_iff, ival_zero]; exact hd
  simp only [growend, ms_ref, ms_length, ms_memory, ms_offset, stateExcept_bind, stateExcept_pure,
    hpos, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    mutableRef_run s handle _ ha, mutableLength_run s handle _ ha,
    mutableMemLength_run s mem slots hm, hlt, ite_true, hint]
  cases r <;> rfl

theorem setSize_after {layout : MemoryLayoutMetadata} (s : MutableMemory α)
    (mems : List (List (Option α))) (handle : Nat) (v : MutableVector)
    (halt : handle < s.arrays.length) (n' : I) :
    ((mutableStorage layout).setSize handle n').run { s with memories := mems, arrays := s.arrays.set handle v } =
      (.ok (), { s with memories := mems, arrays := s.arrays.set handle ⟨v.reference, n'⟩ }) := by
  rw [ms_setSize_run _ handle v (List.getElem?_set_self halt)]
  simp only [List.set_set]

/-- `_growend!(a, delta)` on a valid vector follows `growendPlan`: the plan's error with `a`
untouched, or `a` lengthened by `delta` with its old elements as prefix and the planned
geometry; other array headers and other memories are untouched. -/
theorem growend_plan (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I) (hd : 0 ≤ delta.val) :
    (∀ e, growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .error e →
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
        handle delta).run s = (.error e, s)) ∧
    (∀ g', growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .ok g' →
      ∃ next mem' off' slots',
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
          handle delta).run s = (.ok (), next) ∧
        VecAt next handle mem' off' (n + delta) slots' ∧
        next.arrays = s.arrays.set handle ⟨(mem', off'), n + delta⟩ ∧
        (n + delta).val = n.val + delta.val ∧
        (vwWindow slots' off' (n + delta)).take n.val.toNat = vwWindow slots off n ∧
        geometryOf next handle = g' ∧
        s.memories.length ≤ next.memories.length ∧
        (∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) ∧
        (mem' = mem ∨ mem' = s.memories.length)) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hwin : ∀ (sl : List (Option α)) (o : I) (n' : I), n.val ≤ n'.val →
      (vwWindow sl o n').take n.val.toNat = (sl.drop (o.val - 1).toNat).take n.val.toNat := by
    intro sl o n' hle
    simp only [vwWindow, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  by_cases hfast : delta.val ≤ (slots.length : Int) - (off.val - 1) - n.val
  · have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
    have hplan : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
        .ok ⟨slots.length, off.val.toNat, n.val.toNat + delta.val.toNat⟩ := by
      simp only [growendPlan]
      rw [if_pos (by omega)]
    have hrun := growend_fast (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hfast
    refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' hg' => ?_⟩
    rw [hplan] at hg'
    cases hg'
    have hv : VecAt { s with arrays := s.arrays.set handle ⟨(mem, off), n + delta⟩ } handle mem off
        (n + delta) slots :=
      ⟨List.getElem?_set_self halt, hm, ho, by omega, by omega, hc⟩
    refine ⟨_, mem, off, slots, hrun, hv, rfl, hnd, ?_, ?_, Nat.le_refl _, fun _ _ _ => rfl,
      Or.inl rfl⟩
    · rw [hwin slots off (n + delta) (by omega)]; rfl
    · rw [VecAt.geometry hv, hnd]
      simp only [VectorGeometry.mk.injEq, true_and]
      omega
  · have hslow : (slots.length : Int) - (off.val - 1) - n.val < delta.val := by omega
    have hslowN : ¬ (delta.val.toNat ≤ slots.length - (off.val.toNat - 1) - n.val.toNat) := by omega
    by_cases hov1 : n.val + delta.val ≤ 9223372036854775807
    · by_cases hov : off.val - 1 + n.val + delta.val ≤ 9223372036854775807
      · have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
        have hovN : ¬ (typemaxNat < off.val.toNat - 1 + (n.val.toNat + delta.val.toNat)) := by
          unfold typemaxNat; omega
        by_cases hs : n.val + delta.val < off.val - 1 ∧
            (n.val + delta.val) / 4 < off.val - 1 - (n.val + delta.val)
        · obtain ⟨newoff, slots', hint, hnewoff, hlen, hwin'⟩ :=
            growendInternal_slide (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hov hs.1 hs.2
          have hsN : n.val.toNat + delta.val.toNat < off.val.toNat - 1 ∧
              (n.val.toNat + delta.val.toNat) / 4 <
                off.val.toNat - 1 - (n.val.toNat + delta.val.toNat) := by omega
          have hplan : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
              .ok ⟨slots.length, (n.val.toNat + delta.val.toNat) / 8 + 1,
                n.val.toNat + delta.val.toNat⟩ := by
            simp only [growendPlan, growendInternalPlan, hslowN, hovN, hsN, ite_false, ite_true,
              and_self]
            rfl
          have hrun := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hslow _ _ hint
          rw [setSize_after s _ handle _ halt] at hrun
          refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' hg' => ?_⟩
          rw [hplan] at hg'
          cases hg'
          have hv : VecAt { s with
              memories := s.memories.set mem slots'
              arrays := s.arrays.set handle ⟨(mem, newoff), n + delta⟩ } handle mem newoff
              (n + delta) slots' :=
            ⟨List.getElem?_set_self halt, List.getElem?_set_self hlt, by omega, by omega,
              by rw [hlen, hnewoff, hnd]; omega, by rw [hlen]; exact hc⟩
          refine ⟨_, mem, newoff, slots', hrun, hv, rfl, hnd, ?_, ?_, by simp, ?_, Or.inl rfl⟩
          · rw [hwin slots' newoff (n + delta) (by omega)]; exact hwin'
          · rw [VecAt.geometry hv, hnd, hlen, hnewoff]
            simp only [VectorGeometry.mk.injEq, true_and]
            omega
          · intro m _ hne
            exact List.getElem?_set_ne (fun he => hne he.symm)
        · obtain ⟨hnf, hok⟩ := growendInternal_alloc l h' delta hd hov hs
          have hsN : ¬ (n.val.toNat + delta.val.toNat < off.val.toNat - 1 ∧
              (n.val.toNat + delta.val.toNat) / 4 <
                off.val.toNat - 1 - (n.val.toNat + delta.val.toNat)) := by omega
          have hkN : max (overallocationNat slots.length)
              (off.val.toNat - 1 + (n.val.toNat + delta.val.toNat)) =
              max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat := by
            congr 1; omega
          have hplan : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
              (allocationPlan l (max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat)
                ⟨max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat,
                  off.val.toNat, n.val.toNat⟩).map fun g' => { g' with length := n.val.toNat + delta.val.toNat } := by
            simp only [growendPlan, growendInternalPlan, hslowN, hovN, hsN, ite_false, hkN]
          by_cases hfit : memoryFits l (max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat)
          · obtain ⟨D, hint, hDlen, hDwin⟩ := hok hfit
            have hk63 : max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat < 2 ^ 63 := by
              have := hfit.1; unfold maxIntVal at this; omega
            have hkge : (off.val - 1 + n.val + delta.val).toNat ≤
                max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat :=
              Nat.le_max_right _ _
            have hplan' : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
                .ok ⟨max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat,
                  off.val.toNat, n.val.toNat + delta.val.toNat⟩ := by
              rw [hplan]; simp only [allocationPlan, hfit, ite_true]; rfl
            have hrun := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hslow _ _ hint
            rw [setSize_after s _ handle _ halt] at hrun
            refine ⟨fun e he => (by rw [hplan'] at he; cases he), fun g' hg' => ?_⟩
            rw [hplan'] at hg'
            cases hg'
            have hMlt : s.memories.length < (s.memories ++ [List.replicate
                (max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat) none]).length := by
              simp
            have hv : VecAt { s with
                memories := (s.memories ++ [List.replicate
                  (max (overallocationNat slots.length) (off.val - 1 + n.val + delta.val).toNat) none]).set
                    s.memories.length D
                arrays := s.arrays.set handle ⟨(s.memories.length, off), n + delta⟩ } handle
                s.memories.length off (n + delta) D :=
              ⟨List.getElem?_set_self halt, List.getElem?_set_self hMlt, ho, by omega,
                by rw [hDlen, hnd]; omega, by rw [hDlen]; exact hk63⟩
            refine ⟨_, s.memories.length, off, D, hrun, hv, rfl, hnd, ?_, ?_, by simp, ?_, Or.inr rfl⟩
            · rw [hwin D off (n + delta) (by omega)]; exact hDwin
            · rw [VecAt.geometry hv, hnd, hDlen]
              simp only [VectorGeometry.mk.injEq, true_and]
              omega
            · intro m hm' _
              rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hm']
          · have hplan' : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
                .error (.argument genericMemorySizeMessage) := by
              rw [hplan]; simp only [allocationPlan, hfit, ite_false]; rfl
            have hrun := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hslow _ _ (hnf hfit)
            refine ⟨fun e he => ?_, fun g' hg' => by rw [hplan'] at hg'; cases hg'⟩
            rw [hplan'] at he
            cases he
            exact hrun
      · have hplan : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
            .error .overflow := by
          have hovN : typemaxNat < off.val.toNat - 1 + (n.val.toNat + delta.val.toNat) := by
            unfold typemaxNat; omega
          simp only [growendPlan, growendInternalPlan, hslowN, hovN, ite_false, ite_true]
          rfl
        have hrun := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hslow _ _
          (growendInternal_overflow2 h' delta hd hov1 (by omega))
        refine ⟨fun e he => ?_, fun g' hg' => by rw [hplan] at hg'; cases hg'⟩
        rw [hplan] at he
        cases he
        exact hrun
    · have hplan : growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
          .error .overflow := by
        have hovN : typemaxNat < off.val.toNat - 1 + (n.val.toNat + delta.val.toNat) := by
          unfold typemaxNat; omega
        simp only [growendPlan, growendInternalPlan, hslowN, hovN, ite_false, ite_true]
        rfl
      have hrun := growend_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hslow _ _
        (growendInternal_overflow1 h' delta (by omega))
      refine ⟨fun e he => ?_, fun g' hg' => by rw [hplan] at hg'; cases hg'⟩
      rw [hplan] at he
      cases he
      exact hrun
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

/-- `_push!(a, x)` (`_growend!(a, 1)`, then `a[length(a)] = x`) on a valid vector follows
`growendPlan l g 1`. -/
theorem push_plan (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (x : α) :
    (∀ e, growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ 1 = .error e →
      (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength mutableSet handle x).run s = (.error e, s)) ∧
    (∀ g', growendPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ 1 = .ok g' →
      ∃ next mem' off' slots',
        (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
          mutableLength mutableSet handle x).run s = (.ok handle, next) ∧
        VecAt next handle mem' off' (n + one) slots' ∧
        next.arrays = s.arrays.set handle ⟨(mem', off'), n + one⟩ ∧
        (n + one).val = n.val + 1 ∧
        vwWindow slots' off' (n + one) = vwWindow slots off n ++ [some x] ∧
        geometryOf next handle = g' ∧
        s.memories.length ≤ next.memories.length ∧
        (∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) ∧
        (mem' = mem ∨ mem' = s.memories.length)) := by
  obtain ⟨herr, hok⟩ := growend_plan l h one (by rw [ival_one]; decide)
  rw [show one.val.toNat = 1 from rfl] at herr hok
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · simp only [push1361, stateExcept_bind, herr e he]
  · obtain ⟨next, mem', off', slots', hrun, hv, harr, hnd, hwin, hgeo, hlen, hframe, hmem'⟩ :=
      hok g' hg'
    rw [ival_one] at hnd
    have hn0 := h.2.2.2.1
    have hset := vwSet_run next handle mem' off' (n + one) slots' hv (n + one) ⟨by omega, Int.le_refl _⟩ x
    refine ⟨_, mem', off', _, ?_, hv.set (off'.val - 1 + (n + one).val - 1).toNat (some x), harr, hnd,
      ?_, ?_, ?_, ?_, hmem'⟩
    · simp only [push1361, stateExcept_bind, hrun, mutableLength_run next handle _ hv.1, hset,
        stateExcept_pure]
    · rw [vwWindow_set _ _ _ _ _ hv.2.2.1 (by omega)]
      have hk : ((n + one).val - 1).toNat = n.val.toNat := by rw [hnd]; omega
      rw [hk]
      exact list_set_last _ _ _ _ (by rw [vwWindow_length hv, hnd]; omega) hwin
    · rw [VecAt.geometry (hv.set _ _), List.length_set, ← VecAt.geometry hv, hgeo]
    · simpa using hlen
    · intro m hm hne
      have hne' : m ≠ mem' := by
        rcases hmem' with rfl | rfl
        · exact hne
        · omega
      show (next.memories.set mem' _)[m]? = _
      rw [List.getElem?_set_ne (fun he => hne' he.symm)]
      exact hframe m hm hne
end
end opusGrowth
end JuliaLean.Proofs.base.array

